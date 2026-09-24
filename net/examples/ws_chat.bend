# A WebSocket chat client: join a room, say each message given, print
# every message heard until the room is quiet for --wait-ms, then leave
# with a clean close (1000).
#
#   bend net/examples/ws_chat.bend -o chat
#   ./chat ws://127.0.0.1:8765/room ada "hello" "anyone here?"
#   ./chat wss://chat.example/room bob "hi" --ca cert.pem --wait-ms 5000
#
# Each message goes out as a text frame "NAME: MESSAGE". A ping from the
# server is answered by the library as it comes. An error is said as the
# HTTP client's NetError (net/ws_net.bend), so a program that speaks
# both keeps one error type.
import Base
import ../ws.bend as Ws
import ../ws_frame.bend as F
import ../ws_net.bend as WsNet
import ../client.bend as Client

# The command line
# ================

type Cli is Data:
  Cli{url: String, name: String, says: List<&2, String>, ca: String, wait: U32, prev: String}

def num(+s: String, d: U32) -> U32:
  Maybe.default(&2, U32, U32.read(s), d)

# a value after a flag, a flag, or a word: the URL, the name, then messages
def word(+prev: String, +x: String, c: Cli) -> Cli:
  match c:
    case Cli{+u, +n, +ss, +ca, +w, p}:
      Bool.pick(Cli, String.eq(prev, "--ca"), Cli{u, n, ss, x, w, ""},
      Bool.pick(Cli, String.eq(prev, "--wait-ms"), Cli{u, n, ss, ca, num(x, w), ""},
      Bool.pick(Cli, String.starts_with(x, "--"), Cli{u, n, ss, ca, w, x},
      Bool.pick(Cli, String.is_empty(u), Cli{x, n, ss, ca, w, ""},
      Bool.pick(Cli, String.is_empty(n), Cli{u, x, ss, ca, w, ""},
        Cli{u, n, List.append(&2, String, ss, [x]), ca, w, ""})))))

def cli.prev(c: Cli) -> String:
  match c:
    case Cli{u, n, ss, ca, w, p}:
      p

def cli(xs: List<String>, c: Cli) -> Cli:
  match xs:
    case Nil{}:
      c
    case Con{+x, t}:
      +c2 : Cli = c
      cli(t, word(cli.prev(c2), x, c2))

# Talking
# =======

def R() -> Type:
  IO(Maybe<&1, Ws.Conn>)

# an error, said as a NetError; the connection let go
def lost(c: Ws.Conn, e: Ws.Err) -> R():
  do IO<Maybe<&1, Ws.Conn>>:
    IO.print_err("chat: " ++ Client.error.show(WsNet.of(e)))
    Ws.drop(c)
    return None{}

def then(m: Maybe<&1, Ws.Conn>, go: Ws.Conn -> R()) -> R():
  match m:
    case Some{c}:
      go(c)
    case None{}:
      IO.pure(Maybe<&1, Ws.Conn>, None{})

def said(g: Ws.Out(Unit)) -> R():
  (c, r) = g
  match r:
    case Done{u}:
      IO.pure(Maybe<&1, Ws.Conn>, Some{c})
    case Fail{e}:
      lost(c, e)

# each message, in order
def say(xs: List<&2, String>, +name: String, c: Ws.Conn) -> R():
  match xs:
    case Nil{}:
      IO.pure(Maybe<&1, Ws.Conn>, Some{c})
    case Con{x, t}:
      IO.bind(Maybe<&1, Ws.Conn>, Maybe<&1, Ws.Conn>,
        IO.bind(Ws.Out(Unit), Maybe<&1, Ws.Conn>, Ws.send_text(c, name ++ ": " ++ x), said),
        m => then(m, cc => say(t, name, cc)))

# one message heard; a quiet --wait-ms (the recv's timeout) ends the
# listening with the connection as it was
def heard(g: Ws.Out(F.Msg), again: Ws.Conn -> R()) -> R():
  (c, r) = g
  match r:
    case Done{m}:
      match m:
        case F.Text{t}:
          do IO<Maybe<&1, Ws.Conn>>:
            IO.print("< " ++ t)
            again(c)
        case F.Binary{b}:
          do IO<Maybe<&1, Ws.Conn>>:
            IO.print("< (" ++ Nat.show(Bytes.len(b)) ++ " bytes)")
            again(c)
        case F.Closed{code, reason}:
          do IO<Maybe<&1, Ws.Conn>>:
            IO.print("the server closed the room: " ++ U32.show(code) ++ " " ++ reason)
            Ws.drop(c)
            return None{}
    case Fail{e}:
      match e:
        case Ws.ETime{}:
          IO.pure(Maybe<&1, Ws.Conn>, Some{c})
        case _:
          lost(c, e)

# at most k messages (the fuel a loop on the outside world counts down)
def listen(k: Nat, +ms: U32, c: Ws.Conn) -> R():
  match k:
    case 0n:
      IO.pure(Maybe<&1, Ws.Conn>, Some{c})
    case 1n+j:
      IO.bind(Ws.Out(F.Msg), Maybe<&1, Ws.Conn>, Ws.recv_for(c, ms), g => heard(g, cc => listen(j, ms, cc)))

def left(r: Result<&2, &2, Ws.Err, U32>) -> IO(Unit):
  match r:
    case Done{code}:
      IO.print("left the room (" ++ U32.show(code) ++ ")")
    case Fail{e}:
      IO.print_err("chat: " ++ Client.error.show(WsNet.of(e)))

def leave(m: Maybe<&1, Ws.Conn>) -> IO(Unit):
  match m:
    case Some{c}:
      IO.bind(Result<&2, &2, Ws.Err, U32>, Unit, Ws.close(c, 1000, "bye"), left)
    case None{}:
      IO.pure(Unit, Unit{})

def talk(says: List<&2, String>, +name: String, +wait: U32, c: Ws.Conn) -> IO(Unit):
  do IO<Unit>:
    m : Maybe<&1, Ws.Conn> <- say(says, name, c)
    h : Maybe<&1, Ws.Conn> <- then(m, cc => listen(Ws.big(), wait, cc))
    leave(h)

def joined(says: List<&2, String>, +name: String, +wait: U32, r: Result<&2, &1, Ws.Err, Ws.Conn>) -> IO(Unit):
  match r:
    case Done{c}:
      talk(says, name, wait, c)
    case Fail{e}:
      IO.die(Unit, 1, "chat: " ++ Client.error.show(WsNet.of(e)))

def run(c: Cli) -> IO(Unit):
  match c:
    case Cli{u, +n, ss, ca, +w, p}:
      IO.bind(Result<&2, &1, Ws.Err, Ws.Conn>, Unit, Ws.connect(u, Ws.opts.ca(Ws.opts(), ca)),
        r => joined(ss, Bool.pick(String, String.is_empty(n), "anon", n), w, r))

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    run(cli(xs, Cli{"", "", [], "", 2000, ""}))
