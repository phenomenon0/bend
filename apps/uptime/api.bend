# The JSON API, the live feed and the dashboard's files.
#
#   GET    /api/monitors                    every monitor: its spec, state, last probe, uptime over 24 h
#   GET    /api/monitors/:name/history      its probes, newest first (?limit=1..500, 50)
#   POST   /api/monitors                    a monitor added (400 with every reason, 409 when the name is taken)
#   DELETE /api/monitors/:name              removed (204, or 404)
#   GET    /live                            a WebSocket: each probe as it lands, as JSON text
#   GET    /*                               the dashboard (--web)
#
# Every route, the dashboard's files and the WebSocket too, is logged
# and gets the browser's headers (Server.wrap).
import Base
import ../../net/http.bend as Http
import ../../net/server.bend as Server
import ../../net/json.bend as Json
import ../../net/ws_server.bend as WsServer
import ../../power/json_value.bend as J
import ./model.bend as M
import ./env.bend as E
import ./probe.bend as P

# the store's channel closed: nothing can be answered
def gone() -> Http.Response:
  Json.errors(500, ["the store is gone"])

def error(+status: U32, why: Bytes()) -> Http.Response:
  Json.respond(status, Json.obj([Json.kv("error", Json.str(why))]))

# GET /api/monitors
def list(+e: E.Env, r: Http.Request) -> IO(Http.Response):
  do IO<Http.Response>:
    +now : Nat <- IO.wall()
    E.peek(Http.Response, e, st => Json.respond(200, Json.arr(M.mons.json(M.store.mons(st), Nat.div(now, 3600000n)))),
      gone())

# GET /api/monitors/:name/history?limit=
def history.of(+limit: Nat, +name: Bytes(), m: Maybe<&2, M.Mon>) -> Http.Response:
  match m:
    case Some{mon}:
      Json.respond(200, Json.obj([Json.kv("name", Json.str(name)),
        Json.kv("history", Json.arr(M.probes.json(List.take(&2, M.Probe, M.mon.hist(mon), limit))))]))
    case None{}:
      error(404, "no monitor named " ++ name)

def history.at(+e: E.Env, +name: Bytes(), l: Maybe<&2, U32>) -> IO(Http.Response):
  match l:
    case Some{+n}:
      E.peek(Http.Response, e, st => history.of(U32.to_nat(n), name, M.find(M.store.mons(st), name)), gone())
    case None{}:
      Http.reply(error(400, "limit must be a whole number from 1 to 500"))

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

def history(+e: E.Env, +r: Http.Request) -> IO(Http.Response):
  history.at(e, Http.param(r, "name"), limit.of(Http.query.get(r, "limit")))

# POST /api/monitors
def added(+e: E.Env, +s: M.Spec, m: Maybe<&2, U32>) -> IO(Http.Response):
  match m:
    case Some{+id}:
      do IO<Http.Response>:
        E.append(E.ops(e), Json.text(Json.obj(Con{Json.kv("op", Json.str("add")), M.spec.kvs(s)})))
        P.start(e, s, id)
        return Http.with.header(Json.respond(201, M.spec.json(s)), "location",
          "/api/monitors/" ++ M.spec.name(s) ++ "/history")
    case None{}:
      Http.reply(Json.errors(409, ["a monitor named " ++ M.spec.name(s) ++ " exists"]))

def add.checked(+e: E.Env, +c: M.Checked) -> IO(Http.Response):
  +s = M.checked.spec(c)
  Bool.pick(IO(Http.Response), List.is_empty(&2, Bytes(), M.checked.errs(c)),
    IO.bind(Maybe<&2, U32>, Http.Response, E.locked(Maybe<&2, U32>, e, st => M.add(st, s), None{}), m => added(e, s, m)),
    Http.reply(Json.errors(400, M.checked.errs(c))))

def add.body(+e: E.Env, r: Result<&2, &2, J.Why, J.Json>) -> IO(Http.Response):
  match r:
    case Done{+j}:
      add.checked(e, M.check(j))
    case Fail{w}:
      Http.reply(Json.errors(400, ["the body is not JSON: " ++ Json.why.show(w)]))

def add(+e: E.Env, r: Http.Request) -> IO(Http.Response):
  add.body(e, Json.body(r, 65536))

# DELETE /api/monitors/:name
def deleted(+e: E.Env, +name: Bytes(), had: Bool) -> IO(Http.Response):
  match had:
    case True{}:
      do IO<Http.Response>:
        E.append(E.ops(e), Json.text(Json.obj([Json.kv("op", Json.str("del")), Json.kv("name", Json.str(name))])))
        return Http.Response{204, Nil{}, Http.BBody{""}}
    case False{}:
      Http.reply(error(404, "no monitor named " ++ name))

def del(+e: E.Env, r: Http.Request) -> IO(Http.Response):
  +name = Http.param(r, "name")
  IO.bind(Bool, Http.Response, E.locked(Bool, e, st => M.del(st, name), False{}), had => deleted(e, name, had))

def health(r: Http.Request) -> IO(Http.Response):
  Http.reply(Json.respond(200, Json.obj([Json.kv("ok", Json.yes())])))

# GET /live: what the probes publish, as it comes; the client only listens
def live(+e: E.Env, r: Http.Request) -> IO(WsServer.Take):
  WsServer.accept("", c => WsServer.broadcast(E.hub(e), c))

def mw(+r: Http.Request, io: IO(Http.Response)) -> IO(Http.Response):
  Server.logged.around(r, Server.secured.around(io))

def routes(+e: E.Env) -> List<&1, Server.Route>:
  Server.wrap(~mw,
    [Server.get("/health", health),
     Server.get("/api/monitors", r => list(e, r)),
     Server.post("/api/monitors", r => add(e, r)),
     Server.get("/api/monitors/:name/history", r => history(e, r)),
     Server.delete("/api/monitors/:name", r => del(e, r)),
     WsServer.ws("/live", r => live(e, r)),
     Server.static("", E.web(e))])
