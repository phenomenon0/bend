# A WebSocket echo server: every message comes back as it came, text as
# text and bytes as bytes, until the client closes.
#
#   bend net/examples/ws_echo.bend -o echo && ./echo --port 9002
#   ./wsc ws://127.0.0.1:9002/echo t:hello r      # net/ws_cli.bend
#
# --max-msg N caps a message (1 MiB by default; 1009 past it), --ping-ms
# and --pong-ms set the keepalive (0 for no pings), --origin O lets a
# browser in only from O, and a subprotocol "echo" is chosen when the
# client offers it. The Autobahn test suite's
# fuzzing client runs against it (net/ws_check.py --server).
import Base
import ../http.bend as Http
import ../server.bend as Server
import ../ws.bend as Ws
import ../ws_frame.bend as F
import ../ws_server.bend as WsServer

# each message back, until the client's close or a failure
def back(g: Ws.Out(Unit), go: Ws.Conn -> IO(Ws.Conn)) -> IO(Ws.Conn):
  (c, r) = g
  match r:
    case Done{u}:
      go(c)
    case Fail{e}:
      IO.pure(Ws.Conn, c)

def heard(g: Ws.Out(F.Msg), go: Ws.Conn -> IO(Ws.Conn)) -> IO(Ws.Conn):
  (c, r) = g
  match r:
    case Done{m}:
      match m:
        case F.Text{t}:
          IO.bind(Ws.Out(Unit), Ws.Conn, Ws.send_text(c, t), s => back(s, go))
        case F.Binary{b}:
          IO.bind(Ws.Out(Unit), Ws.Conn, Ws.send_bytes(c, b), s => back(s, go))
        case F.Closed{code, reason}:
          IO.pure(Ws.Conn, c)
    case Fail{e}:
      match e:
        case Ws.ETime{}:
          go(c)
        case _:
          IO.pure(Ws.Conn, c)

def echo(k: Nat, c: Ws.Conn) -> IO(Ws.Conn):
  match k:
    case 0n:
      IO.pure(Ws.Conn, c)
    case 1n+j:
      IO.bind(Ws.Out(F.Msg), Ws.Conn, Ws.recv(c), g => heard(g, cc => echo(j, cc)))

def open(r: Http.Request) -> IO(WsServer.Take):
  WsServer.accept(WsServer.choose(r, ["echo"]), c => echo(Ws.big(), c))

def page(r: Http.Request) -> IO(Http.Response):
  Http.reply(Http.text(200, "a WebSocket echo is at /echo\n"))

def num(+xs: List<&2, String>, +name: String, d: U32) -> U32:
  Maybe.default(&2, U32, U32.read(Server.flag.go(xs, name, "")), d)

def origins(+o: String) -> List<&2, Bytes()>:
  Bool.pick(List<&2, Bytes()>, String.is_empty(o), [], [o])

def wopts(xs: List<String>) -> WsServer.Opts:
  +ys : List<&2, String> = Server.strs(xs)
  WsServer.opts.origins(WsServer.opts.keepalive(WsServer.opts.max_msg(WsServer.opts(), num(ys, "--max-msg", 1048576)),
    num(ys, "--ping-ms", 20000), num(ys, "--pong-ms", 20000)), origins(Server.flag.go(ys, "--origin", "")))

def routes(+o: WsServer.Opts) -> List<&1, Server.Route>:
  [Server.get("/", page), WsServer.ws.with(o, "/echo", open)]

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    ys : List<String> <- IO.args()
    WsServer.serve.with(~WsServer.Opts, ~routes, wopts(xs), Server.args(ys, Server.config(9002)))
