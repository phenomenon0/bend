# The JSON API, the live feed and the dashboard's files.
#
#   GET    /api/monitors                    every monitor: its spec, state, last probe, uptime over 24 h
#   GET    /api/monitors/:name/history      its probes, newest first (?limit=1..500, 50)
#   POST   /api/monitors                    a monitor added (400 with every reason, 409 when the name is taken)
#   DELETE /api/monitors/:name              removed (204, or 404)
#   GET    /live                            a WebSocket: each probe as it lands, as JSON text
#   GET    /*                               the dashboard (--web)
#
# The routes are served by WsServer.serve.with, which has no place for
# middleware around the whole table, so each HTTP route is wrapped by
# hand: logged, secured, recovered (a handler answers Fail when the store
# is gone: a plain 500).
import Base
import ../../net/http.bend as Http
import ../../net/server.bend as Server
import ../../net/json.bend as Json
import ../../net/ws.bend as Ws
import ../../net/ws_frame.bend as F
import ../../net/ws_server.bend as WsServer
import ../../power/json_value.bend as J
import ./clock.bend as Time
import ./model.bend as M
import ./env.bend as E
import ./probe.bend as P

def Res() -> Data:
  Result<&2, &2, Bytes(), Http.Response>

def gone() -> Res():
  Fail{"the store's channel is closed"}

def answer(+status: U32, j: J.Json) -> Res():
  Done{Json.respond(status, j)}

def error(+status: U32, why: Bytes()) -> Res():
  answer(status, Json.obj([Json.kv("error", Json.str(why))]))

# List.map takes a List<&1, A>: a List<&2, ...> needs its own map
def strs(xs: List<&2, Bytes()>) -> List<&2, J.Json>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{Json.str(x), strs(t)}

def errors(+status: U32, whys: List<&2, Bytes()>) -> Res():
  answer(status, Json.obj([Json.kv("errors", Json.arr(strs(whys)))]))

# GET /api/monitors
def list(+e: E.Env, r: Http.Request) -> IO(Res()):
  do IO<Res()>:
    +now : Nat <- Time.Clock.wall()
    E.peek(Res(), e, st => answer(200, Json.arr(M.mons.json(M.store.mons(st), Nat.div(now, 3600000n)))), gone())

# GET /api/monitors/:name/history?limit=
def history.of(+limit: Nat, +name: Bytes(), m: Maybe<&2, M.Mon>) -> Res():
  match m:
    case Some{mon}:
      answer(200, Json.obj([Json.kv("name", Json.str(name)),
        Json.kv("history", Json.arr(M.probes.json(List.take(&2, M.Probe, M.mon.hist(mon), limit))))]))
    case None{}:
      error(404, "no monitor named " ++ name)

def history.at(+e: E.Env, +name: Bytes(), l: Maybe<&2, U32>) -> IO(Res()):
  match l:
    case Some{+n}:
      E.peek(Res(), e, st => history.of(U32.to_nat(n), name, M.find(M.store.mons(st), name)), gone())
    case None{}:
      IO.pure(Res(), error(400, "limit must be a whole number from 1 to 500"))

def limit.ok(m: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match m:
    case Some{+n}:
      Bool.pick(Maybe<&2, U32>, (n >= 1 : U32) && (n <= 500 : U32), Some{n}, None{})
    case None{}:
      None{}

def limit.of(q: Maybe<&2, Bytes()>) -> Maybe<&2, U32>:
  match q:
    case Some{s}:
      limit.ok(U32.read(s))
    case None{}:
      Some{50}

def history(+e: E.Env, +r: Http.Request) -> IO(Res()):
  history.at(e, Http.param(r, "name"), limit.of(Http.query.get(r, "limit")))

# POST /api/monitors
def added(+e: E.Env, +s: M.Spec, m: Maybe<&2, U32>) -> IO(Res()):
  match m:
    case Some{+id}:
      do IO<Res()>:
        E.append(E.ops(e), Json.text(Json.obj(Con{Json.kv("op", Json.str("add")), M.spec.kvs(s)})))
        P.start(e, s, id)
        return Done{Http.with.header(Json.respond(201, M.spec.json(s)), "location",
          "/api/monitors/" ++ M.spec.name(s) ++ "/history")}
    case None{}:
      IO.pure(Res(), errors(409, ["a monitor named " ++ M.spec.name(s) ++ " exists"]))

def add.checked(+e: E.Env, +c: M.Checked) -> IO(Res()):
  +s = M.checked.spec(c)
  Bool.pick(IO(Res()), List.is_empty(&2, Bytes(), M.checked.errs(c)),
    IO.bind(Maybe<&2, U32>, Res(), E.locked(Maybe<&2, U32>, e, st => M.add(st, s), None{}), m => added(e, s, m)),
    IO.pure(Res(), errors(400, M.checked.errs(c))))

def add.body(+e: E.Env, r: Result<&2, &2, J.Why, J.Json>) -> IO(Res()):
  match r:
    case Done{+j}:
      add.checked(e, M.check(j))
    case Fail{w}:
      IO.pure(Res(), errors(400, ["the body is not JSON: " ++ Json.why.show(w)]))

def add(+e: E.Env, r: Http.Request) -> IO(Res()):
  add.body(e, Json.body(r, 65536))

# DELETE /api/monitors/:name
def deleted(+e: E.Env, +name: Bytes(), had: Bool) -> IO(Res()):
  match had:
    case True{}:
      do IO<Res()>:
        E.append(E.ops(e), Json.text(Json.obj([Json.kv("op", Json.str("del")), Json.kv("name", Json.str(name))])))
        return Done{Http.Response{204, Nil{}, Http.BBody{""}}}
    case False{}:
      IO.pure(Res(), error(404, "no monitor named " ++ name))

def del(+e: E.Env, r: Http.Request) -> IO(Res()):
  +name = Http.param(r, "name")
  IO.bind(Bool, Res(), E.locked(Bool, e, st => M.del(st, name), False{}), had => deleted(e, name, had))

def health(r: Http.Request) -> IO(Res()):
  IO.pure(Res(), answer(200, Json.obj([Json.kv("ok", Json.yes())])))

# GET /live: a member of the hub; what the client says is ignored, what
# the probes publish is relayed between waits of 100 ms
def heard(+me: WsServer.Member, g: Ws.Out(F.Msg), again: Ws.Conn -> IO(Ws.Conn)) -> IO(Ws.Conn):
  (c, r) = g
  match r:
    case Done{m}:
      match m:
        case F.Closed{code, reason}:
          IO.pure(Ws.Conn, c)
        case _:
          IO.bind(Ws.Out(Unit), Ws.Conn, WsServer.relay(me, c), g2 => WsServer.next(g2, again))
    case Fail{e}:
      match e:
        case Ws.ETime{}:
          IO.bind(Ws.Out(Unit), Ws.Conn, WsServer.relay(me, c), g2 => WsServer.next(g2, again))
        case _:
          IO.pure(Ws.Conn, c)

def talk(k: Nat, +me: WsServer.Member, c: Ws.Conn) -> IO(Ws.Conn):
  match k:
    case 0n:
      IO.pure(Ws.Conn, c)
    case 1n+j:
      IO.bind(Ws.Out(F.Msg), Ws.Conn, Ws.recv_for(c, 100), g => heard(me, g, cc => talk(j, me, cc)))

def member(+hub: WsServer.Hub, c: Ws.Conn) -> IO(Ws.Conn):
  do IO<Ws.Conn>:
    +me : WsServer.Member <- WsServer.join(hub)
    c2 : Ws.Conn <- talk(Ws.big(), me, c)
    WsServer.leave(hub, me)
    return c2

def live(+e: E.Env, r: Http.Request) -> IO(WsServer.Take):
  WsServer.accept("", c => member(E.hub(e), c))

# the middleware, by hand, around one route
def mw(+r: Http.Request, io: IO(Res())) -> IO(Http.Response):
  Server.logged.around(r, Server.secured.around(Server.recovered.around(io)))

def files(+r: Http.Request, io: IO(Http.Response)) -> IO(Http.Response):
  Server.logged.around(r, Server.secured.around(io))

def routes(+e: E.Env) -> List<&1, Server.Route>:
  [Server.get("/health", +r => mw(r, health(r))),
   Server.get("/api/monitors", +r => mw(r, list(e, r))),
   Server.post("/api/monitors", +r => mw(r, add(e, r))),
   Server.get("/api/monitors/:name/history", +r => mw(r, history(e, r))),
   Server.delete("/api/monitors/:name", +r => mw(r, del(e, r))),
   WsServer.ws("/live", r => live(e, r)),
   Server.get("/*", +r => files(r, Server.static.at(E.web(e), r)))]
