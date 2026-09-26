# WebSockets

`net/ws.bend` is a WebSocket connection, either end (RFC 6455), over TCP or
TLS; `net/ws_server.bend` adds WebSocket routes to the server. The tour is
`bend guide networking`.

## A Client

`Ws.connect(url, Ws.opts())` answers the connection or a `Ws.Err`, as
`Result<&2, &1, Ws.Err, Ws.Conn>`. A connection is affine: every call hands it
back beside its result, and `Ws.close` or `Ws.drop` lets it go.

```python
# each message, in order
def say(xs: List<&2, String>, +name: String, c: Ws.Conn) -> R():
  match xs:
    case Nil{}:
      IO.pure(Maybe<&1, Ws.Conn>, Some{c})
    case Con{x, t}:
      IO.bind(Maybe<&1, Ws.Conn>, Maybe<&1, Ws.Conn>,
        IO.bind(Ws.Out(Unit), Maybe<&1, Ws.Conn>, Ws.send_text(c, name ++ ": " ++ x), said),
        m => then(m, cc => say(t, name, cc)))
```

`Ws.send_text(c, s)` and `Ws.send_bytes(c, b)` answer `Ws.Out(Unit)`, the
connection beside a `Result`. `Ws.recv(c)` and `Ws.recv_for(c, ms)` answer
`Ws.Out(F.Msg)`, where a message is `F.Text{t}`, `F.Binary{b}` or
`F.Closed{code, reason}` (`F` is `net/ws_frame.bend`). A recv that times out
answers `ETime` and leaves the connection as it was:

```python
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
```

`Ws.close(c, 1000, "bye")` runs the closing handshake and answers the server's
code. The library answers a ping as it comes, and every frame it sends is
masked. A frame the RFC forbids fails the connection with 1002, text that is
not UTF-8 with 1007, and a message past the cap with 1009. `WsNet.of(e)`
(`net/ws_net.bend`) turns a `Ws.Err` into a `NetError`, so a program that
speaks both keeps one error type. `Ws.opts.protocols`, `Ws.opts.ca`,
`Ws.opts.timeouts(o, connect, recv, close)` and `Ws.opts.max_msg` change the
options. The whole program is `net/examples/ws_chat.bend`.

## A Server

`WsServer.ws(pat, h)` is a route like `Server.get`, and it sits in the same
list. `h` gets the request (its path and params, its query, its headers and
cookies: authenticate there, and pick a subprotocol) and answers
`WsServer.accept(proto, run)` or `WsServer.refuse(response)`. `run` gets a
`Ws.Conn`, the client's own type, with the same verbs and messages. It hands
the connection back when it is done; one handed back open is closed with 1000,
and `Ws.end(c, code, reason)` closes it with a code of your own first. Serve
the routes with `WsServer.serve.with(~E, ~routes, env, cfg)`, which makes them
from `env` for each request; `Server.wrap` puts middleware around them all:

```python
# the page and the room, each request logged (the room's as its 101)
def routes(+hub: WsServer.Hub) -> List<&1, Server.Route>:
  Server.wrap(~Server.logged.around, [Server.get("/", page), WsServer.ws("/room", r => enter(hub, r))])

def main() -> IO(Unit):
  do IO<Unit>:
    +hub : WsServer.Hub <- WsServer.hub.new()
    +xs : List<&2, String> <- Server.argv([])
    WsServer.serve.with(~WsServer.Hub, ~routes, hub, Server.args(xs, Server.config(8765)))
```

`WsServer.choose(r, ["chat"])` is the first of your subprotocols the client
offered (`""` for none), and the answer never names one it did not offer.

## Rooms and Feeds

A `Hub` is a room: `WsServer.join(hub)` makes a member with an inbox,
`WsServer.publish(hub, msg)` puts a message in every member's inbox, and
`WsServer.relay(me, c)` sends a member what came for it. A connection waits for
its client in slices (`Ws.recv_for(c, 50)`) and relays between them, so the
room reaches it within 50 ms:

```python
def talk(k: Nat, +hub: WsServer.Hub, +me: WsServer.Member, c: Ws.Conn) -> IO(Ws.Conn):
  match k:
    case 0n:
      IO.pure(Ws.Conn, c)
    case 1n+j:
      IO.bind(Ws.Out(F.Msg), Ws.Conn, Ws.recv_for(c, 50), g => heard(hub, me, g, cc => talk(j, hub, me, cc)))
```

A client that only listens (a dashboard's live feed) needs none of that:
`WsServer.accept("", c => WsServer.broadcast(hub, c))` joins it to the room,
sends it what the room publishes, and leaves when it closes or goes. Nothing
yet parks on a socket and a channel at once, so `broadcast` waits in the same
50 ms slices.

## The Handshake and After

The server answers the opening handshake as RFC 6455 4.2.2 says: a GET that
asked to upgrade with a good key gets the 101 and the Accept its key earns; a
request that did not ask gets a 426 naming version 13 (so does one whose
`Sec-WebSocket-Version` is not 13, or missing), and one that asked broken (any
method but GET, a key that is not sixteen bytes in base64) a 400. No extension
is ever agreed: `permessage-deflate`, offered, is declined. Then every frame
the client sends must be masked (1002), a message is at most `max_msg` (1009),
text must be UTF-8 (1007), a ping is answered as it comes, and the client's
close is answered once. A client quiet for `ping` ms is pinged, and dropped
with 1011 when `pong` ms more bring nothing. On SIGTERM, a `recv` sends 1001
(going away) and hands over the client's answer as `Closed`.
`WsServer.ws.with(o, pat, h)` takes options: `WsServer.opts()` changed by
`opts.max_msg`, `opts.keepalive(o, ping, pong)`, `opts.timeouts(o, recv,
close, send)` and `opts.origins(o, [...])`, the `Origin` values a browser's
request may carry (none named: any; a request with no `Origin` is not from a
browser and passes; any other is a 403 before `h` is asked). The whole program
is `net/examples/chat_server.bend`, and `net/examples/ws_echo.bend` is the echo
the Autobahn suite runs against.
