# bend-net: WebSockets on the server (RFC 6455).
#
#   def routes(+hub: WsServer.Hub) -> List<&1, Server.Route>:
#     [Server.get("/", page), WsServer.ws("/room", r => join(hub, r))]
#
#   def join(+hub: WsServer.Hub, r: Http.Request) -> IO(WsServer.Take):
#     WsServer.accept(WsServer.choose(r, ["chat"]), c => talk(hub, c))
#
#   Server.serve.routes(~WsServer.Hub, ~routes, hub, Server.config(8080))
#
# ws(pat, h) is a route: a GET at pat that asks to become a WebSocket is
# handed to h, which sees the request (its path and params, its query,
# its headers, cookies and all: authenticate there) and answers
# accept(proto, run) -- the subprotocol it chose ("" for none) and what
# runs on the connection -- or refuse(response). run gets a Ws.Conn, the
# client's own type (net/ws.bend), with the same verbs: Ws.recv and
# Ws.recv_for (Text{s}, Binary{b}, or Closed{code, reason}),
# Ws.send_text, Ws.send_bytes, Ws.ping, Ws.protocol; and it hands the
# connection back when it is done, closing it first with Ws.end(c,
# code, reason) if it likes. One it hands back open is closed with 1000.
#
# The opening handshake is ws_hs.bend's s.answer (ws_laws.bend's
# srv_hs_*): a request that did not ask -- no Upgrade, or a
# Sec-WebSocket-Version that is not 13, or none (RFC 6455 4.4) -- is a
# 426 naming version 13 (it may ask again on the same connection); one
# that asked broken -- any method but GET (the router hands a ws route
# every method of a request that asked: RFC 6455 4.2.1 and 4.2.2 make
# the handshake a GET and a request that does not match it a 400, so a
# POST is refused as a HEAD is, not with the router's 405), a key that
# is not sixteen bytes in base64 -- is a 400; one that asked well gets
# the 101 with the Accept its key earns and the subprotocol chosen, when
# the client offered it. A request at a ws route that did not ask and is
# not a GET or HEAD is the router's 405. No extension is ever agreed: permessage-deflate,
# offered, is declined by not naming it (RFC 7692 5), and a frame with
# a reserved bit then fails the connection (1002). The engine's reader
# checks the rest of the request (HTTP/1.1, the Host, Upgrade,
# Connection, Sec-WebSocket-Version: 13).
#
# Then every frame the client sends must be masked (1002 if not), a
# message is at most max_msg (1 MiB; 1009 past it, before its bytes are
# held), text must be UTF-8 (1007), pings are answered as they come, the
# client's close is answered once, and a quiet client is pinged after
# ping ms and dropped with 1011 when pong ms more bring nothing (the
# keepalive runs while run waits in a recv). On SIGTERM a recv sends
# 1001 (going away) and hands over the client's answer as Closed; the
# server ends once the connections have, or after its grace.
#
# Options (opts(), then opts.*): max_msg; keepalive(ping, pong), 0 for
# no pings; timeouts(recv, close, send), recv the most a Ws.recv waits,
# close the closing handshake's, send a send's; origins, the Origin
# values a browser's request may carry (none named: every origin; a
# request with no Origin is not from a browser and passes) -- a request
# from another is a 403 before h is asked. h is the hook for anything
# else: it sees every header.
#
# A Hub is a room: members join, anyone publishes a message to all of
# them, and each member takes what came for it (inbox) when it likes --
# between recv_for slices, as examples/chat_server.bend does.
import Base
import ./http.bend as Http
import ./server.bend as Server
import ./ws.bend as Ws
import ./ws_frame.bend as F
import ./ws_hs.bend as H

# The options
# ===========

type Opts is Data:
  Opts{max_msg: U32, ping: U32, pong: U32, recv: U32, close: U32, send: U32, origins: List<&2, Bytes()>}

# 1 MiB messages; a ping after 20 s of quiet, dropped 20 s later; a
# recv waits up to 60 s, a close 5 s, a send 10 s; every origin
def opts() -> Opts:
  Opts{1048576, 20000, 20000, 60000, 5000, 10000, []}

def opts.max_msg(o: Opts, n: U32) -> Opts:
  match o:
    case Opts{mm, pi, po, rc, cl, se, og}:
      Opts{n, pi, po, rc, cl, se, og}

def opts.keepalive(o: Opts, ping: U32, pong: U32) -> Opts:
  match o:
    case Opts{mm, pi, po, rc, cl, se, og}:
      Opts{mm, ping, pong, rc, cl, se, og}

def opts.timeouts(o: Opts, recv: U32, close: U32, send: U32) -> Opts:
  match o:
    case Opts{mm, pi, po, rc, cl, se, og}:
      Opts{mm, pi, po, recv, close, send, og}

def opts.origins(o: Opts, xs: List<&2, Bytes()>) -> Opts:
  match o:
    case Opts{mm, pi, po, rc, cl, se, og}:
      Opts{mm, pi, po, rc, cl, se, xs}

def o.origins(o: Opts) -> List<&2, Bytes()>:
  match o:
    case Opts{mm, pi, po, rc, cl, se, og}:
      og

# the connection's options, as net/ws.bend holds them
def o.ws(o: Opts) -> Ws.Opts:
  match o:
    case Opts{mm, pi, po, rc, cl, se, og}:
      Ws.Opts{[], "", se, rc, cl, mm, 16384}

# The handler's answer
# ====================

# accept, with the subprotocol chosen ("" for none) and what runs on the
# connection; or refuse, with the response that says why
type Take is Type:
  Accept{proto: Bytes(), run: Ws.Conn -> IO(Ws.Conn)}
  Refuse{resp: Http.Response}

def accept(proto: Bytes(), run: Ws.Conn -> IO(Ws.Conn)) -> IO(Take):
  IO.pure(Take, Accept{proto, run})

def refuse(resp: Http.Response) -> IO(Take):
  IO.pure(Take, Refuse{resp})

def vals.put(hit: Bool, v: Bytes(), rest: List<&2, Bytes()>) -> List<&2, Bytes()>:
  match hit:
    case True{}:
      Con{v, rest}
    case False{}:
      rest

# the subprotocols the request offered, in order
def vals(hs: List<&2, Http.Header>) -> List<&2, Bytes()>:
  match hs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      match h:
        case Http.Header{+n, v}:
          vals.put(String.eq(n, "sec-websocket-protocol"), v, vals(t))

def offered(r: Http.Request) -> List<&2, Bytes()>:
  H.s.offered(vals(Http.headers(r)))

def first(ours: List<&2, Bytes()>, +theirs: List<&2, Bytes()>) -> Bytes():
  match ours:
    case Nil{}:
      ""
    case Con{+x, t}:
      Bool.pick(Bytes(), H.has(theirs, x), x, first(t, theirs))

# the first of ours the request offered, or "" for none
def choose(r: Http.Request, ours: List<&2, Bytes()>) -> Bytes():
  first(ours, offered(r))

# The route
# =========

def refusal(+code: U32) -> Http.Response:
  Http.with.header(Http.with.header(Http.plain(code), "sec-websocket-version", "13"), "upgrade", "websocket")

# an Origin named, when the options name some
def origin.in(xs: List<&2, Bytes()>, +v: Bytes()) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, t}:
      String.eq(x, v) || origin.in(t, v)

def origin.at(+xs: List<&2, Bytes()>, m: Maybe<&2, Bytes()>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{+v}:
      List.is_empty(&2, Bytes(), xs) || origin.in(xs, v)

def origin.ok(+o: Opts, +r: Http.Request) -> Bool:
  origin.at(o.origins(o), Http.header(r, "origin"))

def answer(resp: Http.Response) -> IO(Server.Reply):
  IO.pure(Server.Reply, Server.Answer{resp})

# the connection ends: closed with 1000 if run handed it back open, and
# its socket handed back to the server's loop
def finish(g: Ws.Conn & Result<&2, &2, Ws.Err, U32>) -> IO(Socket):
  (c, r) = g
  IO.pure(Socket, Ws.socket(c))

def ran(c: Ws.Conn) -> IO(Socket):
  IO.bind(Ws.Conn & Result<&2, &2, Ws.Err, U32>, Socket, Ws.end(c, 1000, ""), finish)

def session(+o: Opts, +proto: Bytes(), run: Ws.Conn -> IO(Ws.Conn), s: Socket, rest: Bytes(), +now: Nat) -> IO(Socket):
  match o:
    case Opts{mm, +pi, +po, rc, cl, +se, og}:
      IO.bind(Ws.Conn, Socket, run(Ws.served(s, rest, o.ws(o), proto, pi, po, se, now)), ran)

def switched(+o: Opts, +proto: Bytes(), run: Ws.Conn -> IO(Ws.Conn), s: Socket, rest: Bytes()) -> IO(Socket):
  IO.bind(Nat, Socket, IO.now(), +now => session(o, proto, run, s, rest, now))

# the handler's answer: its refusal, or the 101 and the session
def taken.v(+o: Opts, v: H.Sv, +proto: Bytes(), run: Ws.Conn -> IO(Ws.Conn)) -> IO(Server.Reply):
  match v:
    case H.SOk{head}:
      IO.pure(Server.Reply, Server.Switch{head, s => rest => switched(o, proto, run, s, rest)})
    case H.SNo{+c}:
      answer(refusal(c))

def taken(+o: Opts, +key: Bytes(), +offered: List<&2, Bytes()>, t: Take) -> IO(Server.Reply):
  match t:
    case Refuse{resp}:
      answer(resp)
    case Accept{+proto, run}:
      +p = H.s.chosen(proto, offered)
      taken.v(o, H.s.answer(True{}, True{}, key, offered, proto), p, run)

def asked(+o: Opts, h: Http.Request -> IO(Take), +key: Bytes(), +r: Http.Request, ok: Bool) -> IO(Server.Reply):
  match ok:
    case False{}:
      answer(Http.plain(403))
    case True{}:
      IO.bind(Take, Server.Reply, h(r), t => taken(o, key, offered(r), t))

def checked(+o: Opts, h: Http.Request -> IO(Take), +key: Bytes(), +r: Http.Request, no: Maybe<&2, U32>) ->
  IO(Server.Reply):
  match no:
    case Some{+c}:
      answer(refusal(c))
    case None{}:
      asked(o, h, key, r, origin.ok(o, r))

def dispatch(+o: Opts, h: Http.Request -> IO(Take), a: Server.Ask, +r: Http.Request) -> IO(Server.Reply):
  match a:
    case Server.Ask{+up, +key}:
      checked(o, h, key, r, H.s.check(String.eq(Http.method(r), "GET"), up, key))

# a WebSocket route at pat, with the options o
def ws.with(+o: Opts, pat: Bytes(), h: Http.Request -> IO(Take)) -> Server.Route:
  Server.Sock{pat, a => r => dispatch(o, h, a, r)}

# a WebSocket route at pat
def ws(pat: Bytes(), h: Http.Request -> IO(Take)) -> Server.Route:
  ws.with(opts(), pat, h)

# The hub
# =======
#
# A room of members, each with an inbox. The room and each inbox are a
# channel of one used as a lock: taken, changed, put back. publish takes
# the room, then each inbox in turn; a member takes only its own inbox,
# so no two locks are ever waited on in the other order. An inbox holds
# at most box.cap() messages: past it the newest are dropped for that
# member (a client that does not read cannot make the server hold its
# room's traffic without end).

type Member is Data:
  Member{id: U32, box: Chan(List<&2, F.Msg>)}

type Room is Data:
  Room{next: U32, members: List<&2, Member>}

type Hub is Data:
  Hub{room: Chan(Room)}

def box.cap() -> Nat:
  1024n

def hub.made(+room: Chan(Room), ok: Bool) -> IO(Hub):
  IO.pure(Hub, Hub{room})

def hub.new() -> IO(Hub):
  do IO<Hub>:
    +room : Chan(Room) <- Chan.new(Room, 1)
    ok : Bool <- Chan.send(Room, room, Room{0, []})
    hub.made(room, ok)

def hub.room(h: Hub) -> Chan(Room):
  match h:
    case Hub{room}:
      room

def joined.put(+room: Chan(Room), +box: Chan(List<&2, F.Msg>), m: Maybe<&1, Room>) -> IO(Member):
  match m:
    case Some{rm}:
      match rm:
        case Room{+n, ms}:
          do IO<Member>:
            ok : Bool <- Chan.send(Room, room, Room{(n + 1 : U32), Con{Member{n, box}, ms}})
            return Member{n, box}
    case None{}:
      IO.pure(Member, Member{4294967295, box})

# a new member of the room, with an empty inbox
def join(+h: Hub) -> IO(Member):
  do IO<Member>:
    +box : Chan(List<&2, F.Msg>) <- Chan.new(List<&2, F.Msg>, 1)
    ok : Bool <- Chan.send(List<&2, F.Msg>, box, [])
    m : Maybe<&1, Room> <- Chan.recv(Room, hub.room(h))
    joined.put(hub.room(h), box, m)

def member.id(m: Member) -> U32:
  match m:
    case Member{id, box}:
      id

def member.box(m: Member) -> Chan(List<&2, F.Msg>):
  match m:
    case Member{id, box}:
      box

def without.put(drop: Bool, m: Member, rest: List<&2, Member>) -> List<&2, Member>:
  match drop:
    case True{}:
      rest
    case False{}:
      Con{m, rest}

def without(ms: List<&2, Member>, +id: U32) -> List<&2, Member>:
  match ms:
    case Nil{}:
      Nil{}
    case Con{+m, t}:
      without.put(U32.is_eq(member.id(m), id), m, without(t, id))

def left.put(+room: Chan(Room), +id: U32, m: Maybe<&1, Room>) -> IO(Unit):
  match m:
    case Some{rm}:
      match rm:
        case Room{n, ms}:
          IO.bind(Bool, Unit, Chan.send(Room, room, Room{n, without(ms, id)}), ok => IO.pure(Unit, Unit{}))
    case None{}:
      IO.pure(Unit, Unit{})

# the member leaves the room
def leave(+h: Hub, +me: Member) -> IO(Unit):
  IO.bind(Maybe<&1, Room>, Unit, Chan.recv(Room, hub.room(h)), m => left.put(hub.room(h), member.id(me), m))

def box.put(+box: Chan(List<&2, F.Msg>), +x: F.Msg, m: Maybe<&1, List<&2, F.Msg>>) -> IO(Unit):
  match m:
    case Some{+xs}:
      IO.bind(Bool, Unit,
        Chan.send(List<&2, F.Msg>, box,
          Bool.pick(List<&2, F.Msg>, Nat.is_lt(List.length(&2, F.Msg, xs), box.cap()), List.append(&2, F.Msg, xs, [x]), xs)),
        ok => IO.pure(Unit, Unit{}))
    case None{}:
      IO.pure(Unit, Unit{})

def box.add(+x: F.Msg, +m: Member) -> IO(Unit):
  IO.bind(Maybe<&1, List<&2, F.Msg>>, Unit, Chan.recv(List<&2, F.Msg>, member.box(m)), got => box.put(member.box(m), x, got))

def each(ms: List<&2, Member>, +x: F.Msg) -> IO(Unit):
  match ms:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{+m, t}:
      IO.bind(Unit, Unit, box.add(x, m), u => each(t, x))

def published(+room: Chan(Room), +x: F.Msg, m: Maybe<&1, Room>) -> IO(Unit):
  match m:
    case Some{rm}:
      match rm:
        case Room{n, +ms}:
          do IO<Unit>:
            each(ms, x)
            ok : Bool <- Chan.send(Room, room, Room{n, ms})
            return Unit{}
    case None{}:
      IO.pure(Unit, Unit{})

# a message to every member of the room, the sender too
def publish(+h: Hub, +x: F.Msg) -> IO(Unit):
  IO.bind(Maybe<&1, Room>, Unit, Chan.recv(Room, hub.room(h)), m => published(hub.room(h), x, m))

def taken.box(+box: Chan(List<&2, F.Msg>), m: Maybe<&1, List<&2, F.Msg>>) -> IO(List<&2, F.Msg>):
  match m:
    case Some{xs}:
      IO.bind(Bool, List<&2, F.Msg>, Chan.send(List<&2, F.Msg>, box, []), ok => IO.pure(List<&2, F.Msg>, xs))
    case None{}:
      IO.pure(List<&2, F.Msg>, [])

# what came for the member since it last looked, oldest first
def inbox(+me: Member) -> IO(List<&2, F.Msg>):
  IO.bind(Maybe<&1, List<&2, F.Msg>>, List<&2, F.Msg>, Chan.recv(List<&2, F.Msg>, member.box(me)),
    m => taken.box(member.box(me), m))

# each message sent to the connection, in order; the first send that
# fails stops it
def send.one(+x: F.Msg, c: Ws.Conn) -> IO(Ws.Out(Unit)):
  match x:
    case F.Text{t}:
      Ws.send_text(c, t)
    case F.Binary{b}:
      Ws.send_bytes(c, b)
    case F.Closed{code, reason}:
      IO.pure(Ws.Out(Unit), (c, Done{Unit{}}))

def sent.then(g: Ws.Out(Unit), go: Ws.Conn -> IO(Ws.Out(Unit))) -> IO(Ws.Out(Unit)):
  (c, r) = g
  match r:
    case Done{u}:
      go(c)
    case Fail{e}:
      IO.pure(Ws.Out(Unit), (c, Fail{e}))

def send.all(xs: List<&2, F.Msg>, c: Ws.Conn) -> IO(Ws.Out(Unit)):
  match xs:
    case Nil{}:
      IO.pure(Ws.Out(Unit), (c, Done{Unit{}}))
    case Con{+x, t}:
      IO.bind(Ws.Out(Unit), Ws.Out(Unit), send.one(x, c), g => sent.then(g, cc => send.all(t, cc)))

# what came for the member since it last looked, sent to its connection
def relay(+me: Member, c: Ws.Conn) -> IO(Ws.Out(Unit)):
  IO.bind(List<&2, F.Msg>, Ws.Out(Unit), inbox(me), xs => send.all(xs, c))

# after a send: go on, or (it failed) hand the connection back
def next(g: Ws.Out(Unit), go: Ws.Conn -> IO(Ws.Conn)) -> IO(Ws.Conn):
  (c, r) = g
  match r:
    case Done{u}:
      go(c)
    case Fail{e}:
      IO.pure(Ws.Conn, c)

# A listener
# ----------
#
# broadcast(hub, c) is a run for accept whose client only listens: the
# connection joins the room, is sent what the room publishes, and leaves
# when its client closes or goes (SIGTERM's 1001 answered, too); what
# the client sends is dropped. It waits for the client in slices of 50
# ms and relays between them, as a member that talks does: nothing yet
# parks on a socket and a channel at once, so a message reaches it
# within a slice.

def listen.relay(+me: Member, c: Ws.Conn, again: Ws.Conn -> IO(Ws.Conn)) -> IO(Ws.Conn):
  IO.bind(Ws.Out(Unit), Ws.Conn, relay(me, c), g => next(g, again))

def listen.heard(+me: Member, g: Ws.Out(F.Msg), again: Ws.Conn -> IO(Ws.Conn)) -> IO(Ws.Conn):
  (c, r) = g
  match r:
    case Done{m}:
      match m:
        case F.Closed{code, reason}:
          IO.pure(Ws.Conn, c)
        case _:
          listen.relay(me, c, again)
    case Fail{e}:
      match e:
        case Ws.ETime{}:
          listen.relay(me, c, again)
        case _:
          IO.pure(Ws.Conn, c)

def listen.go(k: Nat, +me: Member, c: Ws.Conn) -> IO(Ws.Conn):
  match k:
    case 0n:
      IO.pure(Ws.Conn, c)
    case 1n+j:
      IO.bind(Ws.Out(F.Msg), Ws.Conn, Ws.recv_for(c, 50), g => listen.heard(me, g, cc => listen.go(j, me, cc)))

# the room's messages sent to c until its client leaves
def broadcast(+hub: Hub, c: Ws.Conn) -> IO(Ws.Conn):
  do IO<Ws.Conn>:
    +me : Member <- join(hub)
    c2 : Ws.Conn <- listen.go(Ws.big(), me, c)
    leave(hub, me)
    return c2

# Serving
# =======

def unit.routes(~rs: List<&1, Server.Route>, +u: Unit) -> List<&1, Server.Route>:
  rs

# serve routes (Server's and ws's together) with cfg, until SIGTERM
def serve(~rs: List<&1, Server.Route>, +cfg: Server.Cfg) -> IO(Unit):
  Server.serve.routes(~Unit, ~unit.routes(~rs), Unit{}, cfg)

# the same, the routes made from env (a hub, a store) for each request
def serve.with(~E: Data, ~rs: @+env: E -> List<&1, Server.Route>, +env: E, +cfg: Server.Cfg) -> IO(Unit):
  Server.serve.routes(~E, ~rs, env, cfg)
