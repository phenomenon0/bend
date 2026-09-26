# A WebSocket chat room: every text a client sends goes to every client
# in the room, the sender too. examples/ws_chat.bend is its client; a
# browser gets a page at / that joins the room.
#
#   bend net/examples/chat_server.bend -o room && ./room --port 8765
#   ./chat ws://127.0.0.1:8765/room ada "hello"        # examples/ws_chat.bend
#
# The room is a WsServer.Hub: each connection joins it, publishes what
# its client says, and between waits of 50 ms for the client takes what
# came for it from the others and sends it on. A client that offers the
# subprotocol "chat" gets it.
import Base
import ../http.bend as Http
import ../server.bend as Server
import ../ws.bend as Ws
import ../ws_frame.bend as F
import ../ws_server.bend as WsServer

# one turn: a message heard is published; either way, what came for
# this member goes out; the client's close or a failure ends the talk
def heard(+hub: WsServer.Hub, +me: WsServer.Member, g: Ws.Out(F.Msg), again: Ws.Conn -> IO(Ws.Conn)) -> IO(Ws.Conn):
  (c, r) = g
  match r:
    case Done{m}:
      match m:
        case F.Text{t}:
          do IO<Ws.Conn>:
            WsServer.publish(hub, F.Text{t})
            g2 : Ws.Out(Unit) <- WsServer.relay(me, c)
            WsServer.next(g2, again)
        case F.Binary{b}:
          do IO<Ws.Conn>:
            g2 : Ws.Out(Unit) <- WsServer.relay(me, c)
            WsServer.next(g2, again)
        case F.Closed{code, reason}:
          IO.pure(Ws.Conn, c)
    case Fail{e}:
      match e:
        case Ws.ETime{}:
          do IO<Ws.Conn>:
            g2 : Ws.Out(Unit) <- WsServer.relay(me, c)
            WsServer.next(g2, again)
        case _:
          IO.pure(Ws.Conn, c)

def talk(k: Nat, +hub: WsServer.Hub, +me: WsServer.Member, c: Ws.Conn) -> IO(Ws.Conn):
  match k:
    case 0n:
      IO.pure(Ws.Conn, c)
    case 1n+j:
      IO.bind(Ws.Out(F.Msg), Ws.Conn, Ws.recv_for(c, 50), g => heard(hub, me, g, cc => talk(j, hub, me, cc)))

# a client in the room: joined, talked with, and gone
def member(+hub: WsServer.Hub, c: Ws.Conn) -> IO(Ws.Conn):
  do IO<Ws.Conn>:
    +me : WsServer.Member <- WsServer.join(hub)
    c2 : Ws.Conn <- talk(Ws.big(), hub, me, c)
    WsServer.leave(hub, me)
    return c2

def enter(+hub: WsServer.Hub, r: Http.Request) -> IO(WsServer.Take):
  WsServer.accept(WsServer.choose(r, ["chat"]), c => member(hub, c))

def page(r: Http.Request) -> IO(Http.Response):
  Http.reply(Http.html(200, "<!doctype html><meta charset=utf-8><title>room</title><pre id=log></pre><input id=say autofocus><script>let w=new WebSocket((location.protocol=='https:'?'wss://':'ws://')+location.host+'/room');w.onmessage=e=>log.textContent+=e.data+'\\n';say.onkeydown=e=>{if(e.key=='Enter'){w.send(say.value);say.value=''}}</script>\n"))

# the page and the room, each request logged (the room's as its 101)
def routes(+hub: WsServer.Hub) -> List<&1, Server.Route>:
  Server.wrap(~Server.logged.around, [Server.get("/", page), WsServer.ws("/room", r => enter(hub, r))])

def main() -> IO(Unit):
  do IO<Unit>:
    +hub : WsServer.Hub <- WsServer.hub.new()
    +xs : List<&2, String> <- Server.argv([])
    WsServer.serve.with(~WsServer.Hub, ~routes, hub, Server.args(xs, Server.config(8765)))
