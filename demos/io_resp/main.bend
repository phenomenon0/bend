# A Redis-protocol server, to find out whether a real client agrees
# that resp.bend reads and writes RESP. It answers PING, ECHO, SET,
# GET, COMMAND and QUIT, and its store is per connection, which is
# enough for redis-cli and redis-benchmark to exercise the protocol and
# is not enough to be a database. The protocol is the point.
#
# The server is bend-wire's (wire/): the connection loop, its budgets
# and the accept loop, with a connection limit and SIGTERM, are the
# library's, proven there for every protocol; what is RESP's is the
# planner at the end of this file, from a read's bytes to the replies
# they earn. LAWS.bend states the loop's laws at its hooks.
import Base
import ../../wire/reader.bend as Wr
import ../../wire/loop.bend as L
import ../../wire/effects.bend as Fx
import ./resp.bend as R

# The store
# =========

type Kv is Data:
  Kv{k: List<&2, U32>, v: List<&2, U32>}

# The store, looked in and written to. Each is one self-recursive def
# with the rest of the search handed in as an argument, which is how
# the base library writes List.find and the only shape Bend takes: a
# helper that called back would be mutual recursion.
def find.pick(
  v: List<&2, U32>, rest: Maybe<&2, List<&2, U32>>, hit: Bool
) -> Maybe<&2, List<&2, U32>>:
  match hit:
    case True{}:
      Some{v}
    case False{}:
      rest

def find.put(
  e: Kv, +key: List<&2, U32>, rest: Maybe<&2, List<&2, U32>>
) -> Maybe<&2, List<&2, U32>>:
  match e:
    case Kv{k, v}:
      find.pick(v, rest, Wr.beq(k, key, True{}))

def find(kv: List<&2, Kv>, +key: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match kv:
    case Nil{}:
      None{}
    case Con{e, t}:
      find.put(e, key, find(t, key))

# a new value shadows an old one, and the old one is dropped so a
# connection that writes one key a million times does not grow
def drop.pick(e: Kv, rest: List<&2, Kv>, hit: Bool) -> List<&2, Kv>:
  match hit:
    case True{}:
      rest
    case False{}:
      Con{e, rest}

def drop.put(e: Kv, +key: List<&2, U32>, rest: List<&2, Kv>) -> List<&2, Kv>:
  match e:
    case Kv{+k, v}:
      drop.pick(Kv{k, v}, rest, Wr.beq(k, key, True{}))

def drop(kv: List<&2, Kv>, +key: List<&2, U32>) -> List<&2, Kv>:
  match kv:
    case Nil{}:
      Nil{}
    case Con{e, t}:
      drop.put(e, key, drop(t, key))

# Commands
# ========

# a command is an array of bulk strings; the name is matched without
# case, as every Redis client expects
def upper.one(+c: U32, low: Bool) -> U32:
  match low:
    case True{}:
      (c - 32 : U32)
    case False{}:
      c

def upper(bs: List<&2, U32>) -> List<&2, U32>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{+c, t}:
      Con{upper.one(c, U32.is_le(97, c) && U32.is_le(c, 122)), upper(t)}

# the bytes of a value, when it is a bulk string; anything else in a
# command is refused
def bulk.of(v: R.Val) -> Maybe<&2, List<&2, U32>>:
  match v:
    case R.VBulk{bs}:
      Some{bs}
    case R.VStr{bs}:
      Some{bs}
    case R.VErr{bs}:
      None{}
    case R.VInt{bs}:
      None{}
    case R.VNil{}:
      None{}
    case R.VArr{xs}:
      None{}

def arg(xs: List<&2, R.Val>, i: Nat) -> Maybe<&2, List<&2, U32>>:
  match xs i:
    case Nil{} 0n:
      None{}
    case Con{h, t} 0n:
      bulk.of(h)
    case Nil{} 1n+j:
      None{}
    case Con{h, t} 1n+j:
      arg(t, j)

# What answering one command produced: the bytes to write back, the
# store as it now is, and whether the connection ends after it.
type Ans is Data:
  Ans{out: List<&2, U32>, kv: List<&2, Kv>, close: Bool}

def err.args() -> List<&2, U32>:
  R.error("ERR wrong number of arguments")

def cmd.ping(kv: List<&2, Kv>, m: Maybe<&2, List<&2, U32>>) -> Ans:
  match m:
    case None{}:
      Ans{R.simple("PONG"), kv, False{}}
    case Some{bs}:
      Ans{R.bulk(bs), kv, False{}}

def cmd.echo(kv: List<&2, Kv>, m: Maybe<&2, List<&2, U32>>) -> Ans:
  match m:
    case None{}:
      Ans{err.args(), kv, False{}}
    case Some{bs}:
      Ans{R.bulk(bs), kv, False{}}

def cmd.get.on(kv: List<&2, Kv>, m: Maybe<&2, List<&2, U32>>) -> Ans:
  match m:
    case None{}:
      Ans{R.nil(), kv, False{}}
    case Some{bs}:
      Ans{R.bulk(bs), kv, False{}}

def cmd.get(+kv: List<&2, Kv>, m: Maybe<&2, List<&2, U32>>) -> Ans:
  match m:
    case None{}:
      Ans{err.args(), kv, False{}}
    case Some{key}:
      cmd.get.on(kv, find(kv, key))

def cmd.set.on(
  kv: List<&2, Kv>, key: List<&2, U32>, m: Maybe<&2, List<&2, U32>>
) -> Ans:
  match m:
    case None{}:
      Ans{err.args(), kv, False{}}
    case Some{val}:
      Ans{R.simple("OK"), Con{Kv{key, val}, kv}, False{}}

def cmd.set(
  kv: List<&2, Kv>, +xs: List<&2, R.Val>, m: Maybe<&2, List<&2, U32>>
) -> Ans:
  match m:
    case None{}:
      Ans{err.args(), kv, False{}}
    case Some{+key}:
      cmd.set.on(drop(kv, key), key, arg(xs, 2n))

# COMMAND DOCS is what redis-cli asks for as it connects; an empty
# array is a true answer to it and the client goes on
def run(
  kv: List<&2, Kv>, +xs: List<&2, R.Val>, name: List<&2, U32>,
  ping: Bool, echo: Bool, set: Bool, get: Bool, cmd: Bool, quit: Bool
) -> Ans:
  match ping echo set get cmd quit:
    case True{} _ _ _ _ _:
      cmd.ping(kv, arg(xs, 1n))
    case False{} True{} _ _ _ _:
      cmd.echo(kv, arg(xs, 1n))
    case False{} False{} True{} _ _ _:
      cmd.set(kv, xs, arg(xs, 1n))
    case False{} False{} False{} True{} _ _:
      cmd.get(kv, arg(xs, 1n))
    case False{} False{} False{} False{} True{} _:
      Ans{R.array(Nil{}), kv, False{}}
    case False{} False{} False{} False{} False{} True{}:
      Ans{R.simple("OK"), kv, True{}}
    case False{} False{} False{} False{} False{} False{}:
      Ans{R.error("ERR unknown command"), kv, False{}}

def dispatch(kv: List<&2, Kv>, +xs: List<&2, R.Val>, +name: List<&2, U32>) -> Ans:
  run(kv, xs, name,
    Wr.beq(name, Wr.bytes("PING"), True{}), Wr.beq(name, Wr.bytes("ECHO"), True{}),
    Wr.beq(name, Wr.bytes("SET"), True{}), Wr.beq(name, Wr.bytes("GET"), True{}),
    Wr.beq(name, Wr.bytes("COMMAND"), True{}), Wr.beq(name, Wr.bytes("QUIT"), True{}))

def named(
  kv: List<&2, Kv>, +xs: List<&2, R.Val>, m: Maybe<&2, List<&2, U32>>
) -> Ans:
  match m:
    case None{}:
      Ans{R.error("ERR bad command"), kv, False{}}
    case Some{bs}:
      dispatch(kv, xs, upper(bs))

# an inline command (redis-cli sends none, but a telnet does) is a
# simple string; anything else at the top level is not a command
def one(kv: List<&2, Kv>, v: R.Val) -> Ans:
  match v:
    case R.VArr{+xs}:
      named(kv, xs, arg(xs, 0n))
    case R.VStr{bs}:
      dispatch(kv, Nil{}, upper(bs))
    case R.VBulk{bs}:
      dispatch(kv, Nil{}, upper(bs))
    case R.VErr{bs}:
      Ans{R.error("ERR bad command"), kv, False{}}
    case R.VInt{bs}:
      Ans{R.error("ERR bad command"), kv, False{}}
    case R.VNil{}:
      Ans{R.error("ERR bad command"), kv, False{}}

# Every command in one chunk, answered in order, the store threaded
# through and a QUIT ending the batch. The running answer is a
# parameter rather than something a helper hands back, which is what
# lets this be one self-recursive def over the values.
def answer.cat(out: List<&2, U32>, a: Ans) -> Ans:
  match a:
    case Ans{more, kv, close}:
      Ans{Wr.cat(out, more), kv, close}

def answer(vs: List<&2, R.Val>, a: Ans) -> Ans:
  match vs:
    case Nil{}:
      a
    case Con{v, t}:
      match a:
        case Ans{out, kv, close}:
          match close:
            case True{}:
              Ans{out, kv, True{}}
            case False{}:
              answer(t, answer.cat(out, one(kv, v)))

def answer.all(kv: List<&2, Kv>, vs: List<&2, R.Val>) -> Ans:
  answer(vs, Ans{Nil{}, kv, False{}})

# The server
# ==========

# What serving needs: the idle time (ms), the grace time on SIGTERM
# (ms) and the most connections at once.
type Cfg is Data:
  Cfg{idle: U32, grace: U32, conns: U32}

# A connection's state between reads: its reader and its store.
type Conn is Data:
  Conn{r: R.Rd, kv: List<&2, Kv>}

def conn.new() -> Conn:
  Conn{R.new(), Nil{}}

def Plan() -> Data:
  L.Plan<Conn, Unit>

# what a read's values earn: their replies and read on, or after a QUIT
# the replies and the close; nothing yet (a value still arriving) reads
# on without a write
def plan.fin(close: Bool, out: List<&2, U32>, r: R.Rd, kv: List<&2, Kv>) -> Plan():
  match close out:
    case True{} _:
      L.End{[L.Raw{Bytes.from_list(out)}]}
    case False{} Nil{}:
      L.Wait{Conn{r, kv}}
    case False{} Con{h, t}:
      L.Go{[L.Raw{Bytes.from_list(Con{h, t})}], Conn{r, kv}}

def plan.ans(a: Ans, r: R.Rd) -> Plan():
  match a:
    case Ans{out, kv, close}:
      plan.fin(close, out, r, kv)

def ans.out(a: Ans) -> List<&2, U32>:
  match a:
    case Ans{out, kv, close}:
      out

# a refused stream is answered with the replies its values earned
# before the refusal, then the error, and the connection ends
def plan.bad(bad: Bool, a: Ans, r: R.Rd) -> Plan():
  match bad:
    case True{}:
      L.End{[L.Raw{Bytes.from_list(Wr.cat(ans.out(a), R.error("ERR protocol error")))}]}
    case False{}:
      plan.ans(a, r)

def plan.dead(kv: List<&2, Kv>, vs: List<&2, R.Val>, d: R.Rd & Bool) -> Plan():
  (r, bad) = d
  plan.bad(bad, answer.all(kv, vs), r)

def plan.took(kv: List<&2, Kv>, t: R.Rd & List<&2, R.Val>) -> Plan():
  (r, vs) = t
  plan.dead(kv, vs, R.dead(r))

# The hooks (wire/loop.bend names each): the planner, and the budgets
# out of Cfg. RESP has no head to budget, no upgrade, no stream, no
# files and no access log, so the rest are the loop's defaults (L.no.*).
def plan(cfg: Cfg, buf: Bytes(), c: Conn) -> Plan():
  match c:
    case Conn{r, kv}:
      plan.took(kv, R.take(R.feed_buf(buf, r)))

def idle(c: Cfg) -> U32:
  match c:
    case Cfg{idle, grace, conns}:
      idle

def grace(c: Cfg) -> U32:
  match c:
    case Cfg{idle, grace, conns}:
      grace

def conns(c: Cfg) -> U32:
  match c:
    case Cfg{idle, grace, conns}:
      conns

# one connection, with the real effects
def go(+cfg: Cfg, s: Socket) -> IO(Socket):
  Fx.serve(~Cfg, ~Conn, ~Unit, ~idle, ~idle, ~plan, ~L.no.mid(~Conn), ~L.no.big(),
    ~L.no.uplan(~Conn, ~Unit), ~L.no.gap(), ~L.no.event, ~L.no.shut, ~L.no.fhead, ~L.no.miss,
    ~L.no.lnote, ~L.no.lsize, cfg, conn.new(), s)

# bend-resp [PORT], 6380 by default
def port(xs: List<String>) -> U32:
  match xs:
    case Nil{}:
      6380
    case Con{a, t}:
      Maybe.default(&2, U32, U32.read(a), 6380)

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    +n : U32 = port(xs)
    l : Listener <- IO.try(Listener, TCP.listen(n))
    IO.print("bend-resp on redis://127.0.0.1:" ++ U32.show(n))
    Fx.run(~Cfg, ~go, ~grace, ~conns, "bend-resp", Cfg{300000, 3000, 1024}, l)
