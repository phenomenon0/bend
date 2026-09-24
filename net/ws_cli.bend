# A WebSocket client on the command line, on net/ws.bend: connect, then
# run the steps given, printing a line for each; and an echo client for
# the Autobahn test suite.
#
#   bend net/ws_cli.bend -o wsc
#   ./wsc ws://127.0.0.1:8080/ws t:hello r b:70000 r p:hi c:1000
#   ./wsc wss://localhost:8443/ws --ca cert.pem t:hello r
#   ./wsc ws://127.0.0.1:9001 --autobahn bend    # every case, then the report
#
# Steps: t:TEXT sends a text message, b:N N bytes of binary (i % 251),
# p:TEXT a ping, r receives one message and prints it, echo sends back
# every message until the server closes, c:CODE closes with the code
# (the answer: the server's close code). With no c: step the connection
# is closed with 1000 at the end. --proto P offers the subprotocol P
# (repeatable), --ca FILE trusts FILE, --max N caps a message at N
# bytes, --recv-ms N waits N ms for a message.
import Base
import ./ws.bend as Ws
import ./ws_frame.bend as F

# The options
# ===========

type Cli is Data:
  Cli{url: String, ca: String, protos: List<&2, String>, max: U32, recv: U32, ab: String,
    steps: List<&2, String>, next: String}

def cli.new() -> Cli:
  Cli{"", "", [], 67108864, 30000, "", [], ""}

def u32.or(s: String, +d: U32) -> U32:
  Maybe.default(&2, U32, U32.read(s), d)

def cli.val(c: Cli, +x: String) -> Cli:
  match c:
    case Cli{url, +ca, +protos, +max, +recv, +ab, steps, +next}:
      Cli{url, Bool.pick(String, String.eq(next, "--ca"), x, ca),
        Bool.pick(List<&2, String>, String.eq(next, "--proto"), List.append(&2, String, protos, [x]), protos),
        Bool.pick(U32, String.eq(next, "--max"), u32.or(x, max), max),
        Bool.pick(U32, String.eq(next, "--recv-ms"), u32.or(x, recv), recv),
        Bool.pick(String, String.eq(next, "--autobahn"), x, ab), steps, ""}

def cli.pos(c: Cli, +x: String) -> Cli:
  match c:
    case Cli{+url, +ca, +protos, +max, +recv, +ab, +steps, next}:
      Bool.pick(Cli, String.is_empty(url), Cli{x, ca, protos, max, recv, ab, steps, ""},
        Cli{url, ca, protos, max, recv, ab, List.append(&2, String, steps, [x]), ""})

def cli.flag(c: Cli, +x: String) -> Cli:
  match c:
    case Cli{url, ca, protos, max, recv, ab, steps, next}:
      Cli{url, ca, protos, max, recv, ab, steps, x}

def cli.next(c: Cli) -> String:
  match c:
    case Cli{url, ca, protos, max, recv, ab, steps, next}:
      next

def cli.arg(+c: Cli, +x: String) -> Cli:
  Bool.pick(Cli, Bool.not(String.is_empty(cli.next(c))), cli.val(c, x),
    Bool.pick(Cli, String.starts_with(x, "--"), cli.flag(c, x), cli.pos(c, x)))

def cli.args(xs: List<String>, c: Cli) -> Cli:
  match xs:
    case Nil{}:
      c
    case Con{+x, t}:
      cli.args(t, cli.arg(c, x))

def cli.opts(c: Cli) -> Ws.Opts:
  match c:
    case Cli{url, ca, protos, max, +recv, ab, steps, next}:
      Ws.opts.max_msg(Ws.opts.timeouts(Ws.opts.ca(Ws.opts.protocols(Ws.opts(), protos), ca), 10000, recv, 5000),
        max)

# Printing
# ========

def show.text(+t: String) -> String:
  +n = String.length(t)
  "text " ++ Nat.show(n) ++ " " ++ String.take(t, 60n) ++ Bool.pick(String, Nat.is_lt(60n, n), "...", "")

def show.sum(b: Bytes(), acc: U32) -> U32:
  match b:
    case SNil{}:
      acc
    case SCon{Chr{c}, t}:
      show.sum(t, ((acc * 31 : U32) + c : U32))

def show.msg(m: F.Msg) -> String:
  match m:
    case F.Text{t}:
      show.text(t)
    case F.Binary{+b}:
      "binary " ++ Nat.show(Bytes.len(b)) ++ " sum " ++ U32.show(show.sum(b, 7))
    case F.Closed{code, reason}:
      "closed " ++ U32.show(code) ++ " " ++ reason

# a binary payload of n bytes, i % 251 each
def pattern.go(k: Nat, +i: U32, acc: Bytes()) -> Bytes():
  match k:
    case 0n:
      String.reverse(acc)
    case 1n+j:
      pattern.go(j, (i + 1 : U32), SCon{Chr{(i % 251 : U32)}, acc})

def pattern(n: U32) -> Bytes():
  pattern.go(U32.to_nat(n), 0, SNil{})

# The steps
# =========

def R() -> Type:
  IO(Maybe<&1, Ws.Conn>)

# a send's answer: on, or the error said and the connection dropped
def sent(what: String, g: Ws.Out(Unit)) -> R():
  (c, r) = g
  match r:
    case Done{u}:
      do IO<Maybe<&1, Ws.Conn>>:
        IO.print("sent " ++ what)
        return Some{c}
    case Fail{e}:
      do IO<Maybe<&1, Ws.Conn>>:
        IO.print("error " ++ Ws.err.show(e))
        Ws.drop(c)
        return None{}

# a recv that timed out leaves the connection as it was, and the steps
# go on
def got.err(c: Ws.Conn, e: Ws.Err) -> R():
  match e:
    case Ws.ETime{}:
      do IO<Maybe<&1, Ws.Conn>>:
        IO.print("error timed out")
        return Some{c}
    case _:
      do IO<Maybe<&1, Ws.Conn>>:
        IO.print("error " ++ Ws.err.show(e))
        Ws.drop(c)
        return None{}

def got(g: Ws.Out(F.Msg)) -> R():
  (c, r) = g
  match r:
    case Done{m}:
      do IO<Maybe<&1, Ws.Conn>>:
        IO.print(show.msg(m))
        return Some{c}
    case Fail{e}:
      got.err(c, e)

def closed(r: Result<&2, &2, Ws.Err, U32>) -> R():
  match r:
    case Done{code}:
      do IO<Maybe<&1, Ws.Conn>>:
        IO.print("close answered " ++ U32.show(code))
        return None{}
    case Fail{e}:
      do IO<Maybe<&1, Ws.Conn>>:
        IO.print("close error " ++ Ws.err.show(e))
        return None{}

# the echo: every message back as it came, until the server closes or
# the connection fails
def echo.sent(g: Ws.Out(Unit), again: Ws.Conn -> R()) -> R():
  (c, r) = g
  match r:
    case Done{u}:
      again(c)
    case Fail{e}:
      do IO<Maybe<&1, Ws.Conn>>:
        IO.print("echo error " ++ Ws.err.show(e))
        Ws.drop(c)
        return None{}

def echo.got(+n: Nat, g: Ws.Out(F.Msg), again: Ws.Conn -> R()) -> R():
  (c, r) = g
  match r:
    case Fail{e}:
      do IO<Maybe<&1, Ws.Conn>>:
        IO.print("echo error after " ++ Nat.show(n) ++ ": " ++ Ws.err.show(e))
        Ws.drop(c)
        return None{}
    case Done{m}:
      match m:
        case F.Text{t}:
          IO.bind(Ws.Out(Unit), Maybe<&1, Ws.Conn>, Ws.send_text(c, t), x => echo.sent(x, again))
        case F.Binary{b}:
          IO.bind(Ws.Out(Unit), Maybe<&1, Ws.Conn>, Ws.send_bytes(c, b), x => echo.sent(x, again))
        case F.Closed{code, reason}:
          do IO<Maybe<&1, Ws.Conn>>:
            IO.print("echoed " ++ Nat.show(n) ++ ", closed " ++ U32.show(code))
            Ws.drop(c)
            return None{}

def echo(k: Nat, +n: Nat, c: Ws.Conn) -> R():
  match k:
    case 0n:
      IO.pure(Maybe<&1, Ws.Conn>, Some{c})
    case 1n+j:
      IO.bind(Ws.Out(F.Msg), Maybe<&1, Ws.Conn>, Ws.recv(c), g => echo.got(n, g, x => echo(j, 1n+n, x)))

def step.go(+s: String, c: Ws.Conn, t: Bool, b: Bool, p: Bool, r: Bool, e: Bool, x: Bool) -> R():
  match t b p r e x:
    case True{} _ _ _ _ _:
      IO.bind(Ws.Out(Unit), Maybe<&1, Ws.Conn>, Ws.send_text(c, String.drop(s, 2n)), g => sent("text", g))
    case False{} True{} _ _ _ _:
      IO.bind(Ws.Out(Unit), Maybe<&1, Ws.Conn>, Ws.send_bytes(c, pattern(u32.or(String.drop(s, 2n), 0))),
        g => sent("binary", g))
    case False{} False{} True{} _ _ _:
      IO.bind(Ws.Out(Unit), Maybe<&1, Ws.Conn>, Ws.ping(c, String.drop(s, 2n)), g => sent("ping", g))
    case False{} False{} False{} True{} _ _:
      IO.bind(Ws.Out(F.Msg), Maybe<&1, Ws.Conn>, Ws.recv(c), got)
    case False{} False{} False{} False{} True{} _:
      echo(Ws.big(), 0n, c)
    case False{} False{} False{} False{} False{} True{}:
      IO.bind(Result<&2, &2, Ws.Err, U32>, Maybe<&1, Ws.Conn>, Ws.close(c, u32.or(String.drop(s, 2n), 1000), "bye"),
        closed)
    case False{} False{} False{} False{} False{} False{}:
      do IO<Maybe<&1, Ws.Conn>>:
        IO.print("unknown step " ++ s)
        return Some{c}

def step(+s: String, c: Ws.Conn) -> R():
  step.go(s, c, String.starts_with(s, "t:"), String.starts_with(s, "b:"), String.starts_with(s, "p:"),
    String.eq(s, "r"), String.eq(s, "echo"), String.starts_with(s, "c:"))

def steps.next(may: Maybe<&1, Ws.Conn>, again: Ws.Conn -> IO(Unit)) -> IO(Unit):
  match may:
    case None{}:
      IO.pure(Unit, Unit{})
    case Some{c}:
      again(c)

def steps(xs: List<&2, String>, c: Ws.Conn) -> IO(Unit):
  match xs:
    case Nil{}:
      IO.bind(Result<&2, &2, Ws.Err, U32>, Unit, Ws.close(c, 1000, ""),
        r => IO.bind(Maybe<&1, Ws.Conn>, Unit, closed(r), m => IO.pure(Unit, Unit{})))
    case Con{s, t}:
      IO.bind(Maybe<&1, Ws.Conn>, Unit, step(s, c), may => steps.next(may, cc => steps(t, cc)))

def opened(steps0: List<&2, String>, r: Result<&2, &1, Ws.Err, Ws.Conn>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.die(Unit, 1, "error " ++ Ws.err.show(e))
    case Done{c}:
      do IO<Unit>:
        IO.print("open")
        steps(steps0, c)

# Autobahn
# ========
#
# The fuzzing server's client protocol: getCaseCount answers the number
# of cases as text; runCase?case=i&agent=A is case i, the client echoing
# every message until the server closes; updateReports?agent=A writes
# the report.

def ab.count.got(g: Ws.Out(F.Msg)) -> IO(U32):
  (c, r) = g
  match r:
    case Done{m}:
      match m:
        case F.Text{t}:
          do IO<U32>:
            Ws.drop(c)
            return u32.or(t, 0)
        case F.Binary{b}:
          do IO<U32>:
            Ws.drop(c)
            return 0
        case F.Closed{code, reason}:
          do IO<U32>:
            Ws.drop(c)
            return 0
    case Fail{e}:
      do IO<U32>:
        Ws.drop(c)
        return 0

def ab.count(r: Result<&2, &1, Ws.Err, Ws.Conn>) -> IO(U32):
  match r:
    case Fail{e}:
      IO.die(U32, 1, "getCaseCount: " ++ Ws.err.show(e))
    case Done{c}:
      IO.bind(Ws.Out(F.Msg), U32, Ws.recv(c), ab.count.got)

def ab.left(m: Maybe<&1, Ws.Conn>) -> IO(Unit):
  match m:
    case None{}:
      IO.pure(Unit, Unit{})
    case Some{c}:
      Ws.drop(c)

def ab.case.opened(+i: U32, r: Result<&2, &1, Ws.Err, Ws.Conn>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("case " ++ U32.show(i) ++ ": " ++ Ws.err.show(e))
    case Done{c}:
      IO.bind(Maybe<&1, Ws.Conn>, Unit, echo(Ws.big(), 0n, c), m => ab.left(m))

def ab.cases(k: Nat, +i: U32, +base: String, +agent: String, +o: Ws.Opts) -> IO(Unit):
  match k:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+j:
      do IO<Unit>:
        IO.print_err("case " ++ U32.show(i))
        r : Result<&2, &1, Ws.Err, Ws.Conn> <- Ws.connect(base ++ "/runCase?case=" ++ U32.show(i) ++ "&agent=" ++ agent, o)
        ab.case.opened(i, r)
        ab.cases(j, (i + 1 : U32), base, agent, o)

def ab.report(r: Result<&2, &1, Ws.Err, Ws.Conn>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("updateReports: " ++ Ws.err.show(e))
    case Done{c}:
      IO.bind(Result<&2, &2, Ws.Err, U32>, Unit, Ws.close(c, 1000, ""), x => IO.print("report updated"))

def autobahn(+base: String, +agent: String, +o: Ws.Opts) -> IO(Unit):
  do IO<Unit>:
    r : Result<&2, &1, Ws.Err, Ws.Conn> <- Ws.connect(base ++ "/getCaseCount", o)
    +n : U32 <- ab.count(r)
    IO.print("cases " ++ U32.show(n))
    ab.cases(U32.to_nat(n), 1, base, agent, o)
    q : Result<&2, &1, Ws.Err, Ws.Conn> <- Ws.connect(base ++ "/updateReports?agent=" ++ agent, o)
    ab.report(q)

# Main
# ====

def run(+c: Cli, ab: Bool) -> IO(Unit):
  match c:
    case Cli{+url, ca, protos, max, recv, +ab2, steps0, next}:
      match ab:
        case True{}:
          autobahn(url, ab2, cli.opts(c))
        case False{}:
          IO.bind(Result<&2, &1, Ws.Err, Ws.Conn>, Unit, Ws.connect(url, cli.opts(c)), r => opened(steps0, r))

def cli.ab(c: Cli) -> String:
  match c:
    case Cli{url, ca, protos, max, recv, ab, steps, next}:
      ab

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    +c : Cli = cli.args(xs, cli.new())
    run(c, Bool.not(String.is_empty(cli.ab(c))))
