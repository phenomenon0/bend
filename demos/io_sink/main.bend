# An upload sink on bend-wire's body stream: a POST to /sink sends a
# body of any size, which is taken as it arrives (wire/stream.bend),
# under a 256 KiB window, and counted; the count goes back. It is the
# fixture that measures the stream on the server's side: a 100 MB
# upload costs the window and one read, not the body.
#
# The body is framed by wire/http1's reader entered at it (R.body.len,
# R.body.chunked): the same states, grammar and budget that resp_sim
# holds to RFC 9112, and drain_reads says the chunks the consumer is
# handed are that body, byte for byte. The head is read as little as a
# sink needs, and no more is claimed for it: a head of at most 16 KiB,
# its target, and Content-Length or Transfer-Encoding: chunked -- both
# at once, or a length that is not all digits, is answered 400 and the
# connection closed. It is not an HTTP server; the engine is.
#
#   bend demos/io_sink/main.bend -o sink
#   ./sink 20050 &
#   curl -T big.bin http://127.0.0.1:20050/sink
import Base
import ../../wire/loop.bend as L
import ../../wire/effects.bend as Fx
import ../../wire/stream.bend as Bs
import ../../wire/http1/resp.bend as R

# What serving needs: the idle time (ms), the grace time on SIGTERM (ms)
# and the most connections at once.
type Cfg is Data:
  Cfg{idle: U32, grace: U32, conns: U32}

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

# the stream's window, and the body's cap (the reader's largest)
def window() -> Nat:
  U32.to_nat(262144)

def ask() -> R.Ask:
  R.ask.new(False{}, 268435455)

# The head
# ========

def low(b: Bytes()) -> Bytes():
  match b:
    case SNil{}:
      SNil{}
    case SCon{Chr{c}, t}:
      SCon{Chr{R.lower(c)}, low(t)}

def spaces(b: Bytes()) -> Bytes():
  match b:
    case SNil{}:
      SNil{}
    case SCon{Chr{+c}, +t}:
      Bool.pick(Bytes(), U32.is_eq(c, 32), spaces(t), SCon{Chr{c}, t})

# the number a field's value is: digits, then its line's end
def num.pick(dg: Bool, cr: Bool, any: Bool, +acc: Nat, next: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match dg cr:
    case True{} _:
      next
    case False{} True{}:
      Bool.pick(Maybe<&2, Nat>, any, Some{acc}, None{})
    case False{} False{}:
      None{}

# the next digit taken, the number held under 2^32 (a longer one is no
# length a sink takes, and every byte of the head is walked)
def num.next(dg: Bool, +acc: Nat, +c: U32) -> Nat:
  match dg:
    case True{}:
      Nat.min(Nat.add(Nat.mul(acc, 10n), U32.to_nat((c - 48 : U32))), 4294967295n)
    case False{}:
      acc

def num(b: Bytes(), +acc: Nat, any: Bool) -> Maybe<&2, Nat>:
  match b:
    case SNil{}:
      None{}
    case SCon{Chr{+c}, t}:
      num.pick(R.digit(c), U32.is_eq(c, 13), any, acc,
        num(t, num.next(R.digit(c), acc, c), True{}))

# how the body is framed: a length, chunked, none, or two ways (refused)
type Fr is Data:
  FLen{n: Nat}
  FChunk{}
  FNone{}
  FBad{}

def frame.len(m: Maybe<&2, Nat>) -> Fr:
  match m:
    case Some{n}:
      FLen{n}
    case None{}:
      FBad{}

def frame.of(cl: Maybe<&2, Maybe<&2, Nat>>, chunked: Bool) -> Fr:
  match cl chunked:
    case None{} False{}:
      FNone{}
    case None{} True{}:
      FChunk{}
    case Some{m} False{}:
      frame.len(m)
    case Some{m} True{}:
      FBad{}

def cl.at(+lo: Bytes(), m: Maybe<&2, Nat>) -> Maybe<&2, Maybe<&2, Nat>>:
  match m:
    case None{}:
      None{}
    case Some{+i}:
      Some{num(spaces(String.drop(lo, Nat.add(i, 17n))), 0n, False{})}

def frame(+head: Bytes()) -> Fr:
  +lo = low(head)
  frame.of(cl.at(lo, Bytes.find(lo, "\r\ncontent-length:")),
    Maybe.is_some(&2, Nat, Bytes.find(lo, "\r\ntransfer-encoding: chunked\r\n")))

def entry(f: Fr) -> R.P:
  match f:
    case FLen{n}:
      R.body.len(U32.from_nat(n))
    case FChunk{}:
      R.body.chunked(268435455)
    case FNone{}:
      R.body.len(0)
    case FBad{}:
      R.body.len(0)

def bad(f: Fr) -> Bool:
  match f:
    case FBad{}:
      True{}
    case _:
      False{}

# The body
# ========
#
# The framer is the response reader entered at the body; the consumer
# counts what it is handed and takes all of it.
def feed(e: R.Ask, bs: Bytes(), p: R.P) -> R.P:
  R.feed_buf(e, bs, p)

def stage.end(end: R.End) -> Bs.Stage:
  match end:
    case R.Open{}:
      Bs.Going{}
    case R.Refused{}:
      Bs.Refused{}
    case R.Final{r, rest}:
      Bs.Ended{}
    case R.Closing{r}:
      Bs.Closing{}

def look.of(lk: R.Look) -> Bs.Stage:
  match lk:
    case R.Look{i, end}:
      stage.end(end)

def look(p: R.P) -> Bs.Stage:
  look.of(R.look(p))

def count.go(k: Nat, +bs: Bytes()) -> IO(Nat & Nat):
  IO.pure(Nat & Nat, (Nat.add(k, Bytes.len(bs)), Bytes.len(bs)))

def count(k: Nat, bs: Bytes()) -> IO(Nat & Nat):
  count.go(k, bs)

def fin(k: Nat) -> IO(Nat):
  IO.pure(Nat, k)

def rest.of(end: R.End) -> Bytes():
  match end:
    case R.Final{r, rest}:
      rest
    case _:
      ""

def rest.look(lk: R.Look) -> Bytes():
  match lk:
    case R.Look{i, end}:
      rest.of(end)

def rest(p: R.P) -> Bytes():
  rest.look(R.look(p))

def reply(status: Bytes(), +text: Bytes()) -> Bytes():
  Bytes.concat(["HTTP/1.1 ", status, "\r\ncontent-length: ", Nat.show(Bytes.len(text)),
    "\r\n\r\n", text])

# The connection
# ==============

# after a body: its count, or the connection's end
def sent(m: Socket & Result<&1, &1, U32 & String, Unit>, rest: Bytes(),
  again: Socket -> Bytes() -> IO(Socket)) -> IO(Socket):
  (s, r) = m
  match r:
    case Done{u}:
      again(s, rest)
    case Fail{e}:
      IO.pure(Socket, s)

def answered.at(
  +cfg: Cfg, +sink: Bool, w: Bs.Why, s: Socket, p: R.P, +k: Nat,
  again: Socket -> Bytes() -> IO(Socket)
) -> IO(Socket):
  match w:
    case Bs.BDone{}:
      do IO<Socket>:
        m : Socket & Result<&1, &1, U32 & String, Unit> <- TCP.send_buf_poll(s,
          Bool.pick(Bytes(), sink, reply("200 OK", Nat.show(k) ++ "\n"),
            reply("404 Not Found", "no route\n")), idle(cfg))
        sent(m, rest(p), again)
    case _:
      IO.pure(Socket, s)

def answered(
  +cfg: Cfg, +sink: Bool, q: Bs.Bq<Socket, R.P, Nat> & Bs.Why,
  again: Socket -> Bytes() -> IO(Socket)
) -> IO(Socket):
  (bq, w) = q
  match bq:
    case Bs.Bq{s, p, +k, held, eof}:
      answered.at(cfg, sink, w, s, p, k, again)

def body.go(+cfg: Cfg, +sink: Bool, q: R.P & Bytes(), s: Socket,
  again: Socket -> Bytes() -> IO(Socket)) -> IO(Socket):
  (p, x) = q
  do IO<Socket>:
    out : Bs.Bq<Socket, R.P, Nat> & Bs.Why <- Bs.run(~(A => IO(A)), ~IO.pure, ~IO.bind, ~Socket,
      ~TCP.poll_buf, ~R.Ask, ~R.P, ~feed, ~R.take, ~look, ~Nat, ~count, ~fin, ask(), window(),
      idle(cfg), U32.to_nat(16777216), Bs.Bq{s, p, 0n, x, False{}})
    answered(cfg, sink, out, again)

# a head: its body streamed to the counter, from the bytes that came
# after the head in the same read; a client that asked to be told to go
# on (Expect: 100-continue, as curl asks for a large upload) is told
def body.at(+cfg: Cfg, refused: Bool, f: Fr, +sink: Bool, +cont: Bool, +more: Bytes(), s: Socket,
  again: Socket -> Bytes() -> IO(Socket)) -> IO(Socket):
  match refused:
    case True{}:
      do IO<Socket>:
        m : Socket & Result<&1, &1, U32 & String, Unit> <- TCP.send_buf_poll(s,
          reply("400 Bad Request", "framed two ways, or not at all\n"), idle(cfg))
        IO.pure(Socket, Pair.fst(Socket, Result<&1, &1, U32 & String, Unit>, m))
    case False{}:
      do IO<Socket>:
        m : Socket & Result<&1, &1, U32 & String, Unit> <- TCP.send_buf_poll(s,
          Bool.pick(Bytes(), cont, "HTTP/1.1 100 Continue\r\n\r\n", ""), idle(cfg))
        body.go(cfg, sink, R.take(feed(ask(), more, entry(f))),
          Pair.fst(Socket, Result<&1, &1, U32 & String, Unit>, m), again)

def body(+cfg: Cfg, +head: Bytes(), +more: Bytes(), s: Socket, again: Socket -> Bytes() -> IO(Socket))
  -> IO(Socket):
  +f = frame(head)
  body.at(cfg, bad(f), f, Bytes.starts_with(head, "POST /sink ") || Bytes.starts_with(head, "PUT /sink "),
    Maybe.is_some(&2, Nat, Bytes.find(low(head), "\r\nexpect: 100-continue\r\n")), more, s, again)

# a head is read until its blank line, at most 16 KiB of it
def head.more(fin: Bool, acc: Bytes(), s: Socket, bs: Bytes(),
  more: Socket -> Bytes() -> IO(Socket)) -> IO(Socket):
  match fin:
    case True{}:
      IO.pure(Socket, s)
    case False{}:
      more(s, Bytes.append(acc, bs))

def head.may(acc: Bytes(), s: Socket, m: Maybe<&1, Bytes()>,
  more: Socket -> Bytes() -> IO(Socket)) -> IO(Socket):
  match m:
    case Some{+bs}:
      head.more(String.is_empty(bs), acc, s, bs, more)
    case None{}:
      IO.pure(Socket, s)

def head.got(acc: Bytes(), g: L.Got(Socket), more: Socket -> Bytes() -> IO(Socket)) -> IO(Socket):
  (s, r) = g
  match r:
    case Done{m}:
      head.may(acc, s, m, more)
    case Fail{e}:
      IO.pure(Socket, s)

def head.read(+cfg: Cfg, acc: Bytes(), long: Bool, s: Socket,
  more: Socket -> Bytes() -> IO(Socket)) -> IO(Socket):
  match long:
    case True{}:
      IO.pure(Socket, s)
    case False{}:
      IO.bind(L.Got(Socket), Socket, TCP.poll_buf(s, 65536, idle(cfg)), g =>
        head.got(acc, g, more))

def head.at(+cfg: Cfg, +acc: Bytes(), at: Maybe<&2, Nat>, s: Socket,
  again: Socket -> Bytes() -> IO(Socket), more: Socket -> Bytes() -> IO(Socket))
  -> IO(Socket):
  match at:
    case Some{+i}:
      body(cfg, String.take(acc, Nat.add(i, 4n)), String.drop(acc, Nat.add(i, 4n)), s, again)
    case None{}:
      head.read(cfg, acc, Nat.is_lt(16384n, Bytes.len(acc)), s, more)

# n bounds the reads and requests of one connection
def head(+cfg: Cfg, n: Nat, s: Socket, +acc: Bytes()) -> IO(Socket):
  match n:
    case 0n:
      IO.pure(Socket, s)
    case 1n+(+m):
      head.at(cfg, acc, Bytes.find(acc, "\r\n\r\n"), s,
        s2 => rest => head(cfg, m, s2, rest),
        s2 => acc2 => head(cfg, m, s2, acc2))

def go(+cfg: Cfg, s: Socket) -> IO(Socket):
  head(cfg, U32.to_nat(16777216), s, "")

# sink [PORT], 20050 by default
def port(xs: List<String>) -> U32:
  match xs:
    case Nil{}:
      20050
    case Con{a, t}:
      Maybe.default(&2, U32, U32.read(a), 20050)

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    +n : U32 = port(xs)
    l : Listener <- IO.try(Listener, TCP.listen(n))
    IO.print("bend-sink on http://127.0.0.1:" ++ U32.show(n))
    Fx.run(~Cfg, ~go, ~grace, ~conns, "bend-sink", Cfg{30000, 3000, 1024}, l)
