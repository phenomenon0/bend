# A Redis-protocol server, to find out whether a real client agrees
# that resp.bend reads and writes RESP. It answers PING, ECHO, SET,
# GET, COMMAND and QUIT, and its store is per connection, which is
# enough for redis-cli and redis-benchmark to exercise the protocol and
# is not enough to be a database. The protocol is the point.
#
# The connection loop is the HTTP engine's, with the parser swapped:
# fuel rather than @unsafe, a timed read so a silent peer is dropped,
# an empty chunk ending the connection, and the accept loop the one
# unsafe def.
import Base
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
      find.pick(v, rest, R.beq(k, key, True{}))

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
      drop.pick(Kv{k, v}, rest, R.beq(k, key, True{}))

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
    R.beq(name, R.bytes("PING"), True{}), R.beq(name, R.bytes("ECHO"), True{}),
    R.beq(name, R.bytes("SET"), True{}), R.beq(name, R.bytes("GET"), True{}),
    R.beq(name, R.bytes("COMMAND"), True{}), R.beq(name, R.bytes("QUIT"), True{}))

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
      Ans{R.cat(out, more), kv, close}

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

def chunk() -> U32:
  16384

def idle() -> U32:
  300000

def fuel() -> Nat:
  U32.to_nat(1048576)

# what the connection does next
type Plan is Data:
  Send{out: List<&2, U32>, r: R.Rd, kv: List<&2, Kv>}
  Last{out: List<&2, U32>}
  Stop{}

def plan.fin(
  out: List<&2, U32>, r: R.Rd, kv: List<&2, Kv>, close: Bool
) -> Plan:
  match close:
    case True{}:
      Last{out}
    case False{}:
      Send{out, r, kv}

def plan.ans(a: Ans, r: R.Rd) -> Plan:
  match a:
    case Ans{out, kv, close}:
      plan.fin(out, r, kv, close)

def plan.bad(a: Ans, r: R.Rd, bad: Bool) -> Plan:
  match bad:
    case True{}:
      Last{R.error("ERR protocol error")}
    case False{}:
      plan.ans(a, r)

def plan.dead(kv: List<&2, Kv>, vs: List<&2, R.Val>, d: R.Rd & Bool) -> Plan:
  (r, bad) = d
  plan.bad(answer.all(kv, vs), r, bad)

def plan.took(kv: List<&2, Kv>, t: R.Rd & List<&2, R.Val>) -> Plan:
  (r, vs) = t
  plan.dead(kv, vs, R.dead(r))

def plan.chunk(kv: List<&2, Kv>, bs: List<&2, U32>, r: R.Rd) -> Plan:
  match bs:
    case Nil{}:
      Stop{}
    case Con{c, t}:
      plan.took(kv, R.take(R.feed(Con{c, t}, r)))

def plan.may(
  s: Socket, kv: List<&2, Kv>, m: Maybe<&1, List<&2, U32>>, r: R.Rd
) -> Socket & Plan:
  match m:
    case None{}:
      (s, Stop{})
    case Some{bs}:
      (s, plan.chunk(kv, bs, r))

def plan.res(
  s: Socket, kv: List<&2, Kv>,
  res: Result<&1, &1, U32 & String, Maybe<&1, List<&2, U32>>>, r: R.Rd
) -> Socket & Plan:
  match res:
    case Done{m}:
      plan.may(s, kv, m, r)
    case Fail{e}:
      (s, Stop{})

def plan.read(
  kv: List<&2, Kv>,
  m: Socket & Result<&1, &1, U32 & String, Maybe<&1, List<&2, U32>>>, r: R.Rd
) -> Socket & Plan:
  (s, res) = m
  plan.res(s, kv, res, r)

def turn(kv: List<&2, Kv>, s: Socket, r: R.Rd) -> IO(Socket & Plan):
  do IO<Socket & Plan>:
    m : Socket & Result<&1, &1, U32 & String, Maybe<&1, List<&2, U32>>> <-
      TCP.poll_bytes(s, chunk(), idle())
    return plan.read(kv, m, r)

def sent(m: Socket & Result<&1, &1, U32 & String, Unit>) -> IO(Unit):
  (s, r) = m
  Socket.close(s)

def turn.sent(
  kv: List<&2, Kv>, m: Socket & Result<&1, &1, U32 & String, Unit>, r: R.Rd
) -> IO(Socket & Plan):
  (s, res) = m
  turn(kv, s, r)

def conn(f: Nat, sp: Socket & Plan) -> IO(Unit):
  match f:
    case 0n:
      (s, pl) = sp
      Socket.close(s)
    case 1n+g:
      (s, pl) = sp
      match pl:
        case Stop{}:
          Socket.close(s)
        case Last{out}:
          do IO<Unit>:
            m : Socket & Result<&1, &1, U32 & String, Unit> <-
              TCP.send_bytes(s, out)
            sent(m)
        case Send{out, r, kv}:
          do IO<Unit>:
            m   : Socket & Result<&1, &1, U32 & String, Unit> <-
              TCP.send_bytes(s, out)
            sp2 : Socket & Plan <- turn.sent(kv, m, r)
            conn(g, sp2)

def start(s: Socket) -> IO(Unit):
  do IO<Unit>:
    sp : Socket & Plan <- turn(Nil{}, s, R.new())
    conn(fuel(), sp)

def accept.one(m: Listener & Result<&1, &1, U32 & String, Socket>) ->
  IO(Listener):
  (l, r) = m
  do IO<Listener>:
    s : Socket <- IO.pass(Socket, r)
    IO.spawn(Unit, start(s))
    return l

@unsafe
def accept(l: Listener) -> IO(Unit):
  do IO<Unit>:
    m  : Listener & Result<&1, &1, U32 & String, Socket> <- TCP.accept(l)
    l2 : Listener <- accept.one(m)
    accept(l2)

def port() -> U32:
  6380

def main() -> IO(Unit):
  do IO<Unit>:
    l : Listener <- IO.try(Listener, TCP.listen(port()))
    IO.print("bend-resp on redis://127.0.0.1:6380")
    accept(l)
