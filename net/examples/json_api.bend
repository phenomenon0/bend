# A JSON API: notes kept in memory, behind a router.
#
#   bend net/examples/json_api.bend -o notes && ./notes --port 8080
#   curl -s localhost:8080/notes -d '{"text":"hello"}'     201, {"id":"1","text":"hello"}
#   curl -s localhost:8080/notes                            [{"id":"1","text":"hello"}]
#   curl -s localhost:8080/notes/1                          {"id":"1","text":"hello"}
#   curl -s -X DELETE localhost:8080/notes/1                204
#
# The store is a channel of one holding the notes: a handler takes it,
# changes it and puts it back, so two requests never see half a change.
# The handler gets it as serve.with's environment.
import Base
import ../http.bend as Http
import ../server.bend as Server
import ../json.bend as Json
import ../../power/json_value.bend as J

type Store is Data:
  Store{next: U32, notes: Map<&2, Bytes()>}

# the store, taken, changed by f, and put back; what f answers
def locked.put(+db: Chan(Store), r: Store & Http.Response) -> IO(Http.Response):
  (st, resp) = r
  do IO<Http.Response>:
    ok : Bool <- Chan.send(Store, db, st)
    return resp

def locked.at(+db: Chan(Store), f: Store -> Store & Http.Response, m: Maybe<&1, Store>) -> IO(Http.Response):
  match m:
    case Some{st}:
      locked.put(db, f(st))
    case None{}:
      Http.reply(Http.plain(503))

def locked(+db: Chan(Store), f: Store -> Store & Http.Response) -> IO(Http.Response):
  IO.bind(Maybe<&1, Store>, Http.Response, Chan.recv(Store, db), m => locked.at(db, f, m))

def note(id: Bytes(), text: Bytes()) -> J.Json:
  Json.obj([Json.kv("id", Json.str(id)), Json.kv("text", Json.str(text))])

def notes.json(kvs: List<&2, Sigma<&2, &2, String, _ => Bytes()>>) -> List<&2, J.Json>:
  match kvs:
    case Nil{}:
      Nil{}
    case Con{kv, t}:
      match kv:
        case Tuple{k, v}:
          Con{note(k, v), notes.json(t)}

# GET /notes
def list.of(st: Store) -> Store & Http.Response:
  match st:
    case Store{n, +ns}:
      (Store{n, ns}, Json.respond(200, Json.arr(notes.json(Map.to_list(&2, Bytes(), ns)))))

def list(+db: Chan(Store), r: Http.Request) -> IO(Http.Response):
  locked(db, list.of)

# POST /notes, {"text": ...}
def add.of(+text: Bytes(), st: Store) -> Store & Http.Response:
  match st:
    case Store{+n, ns}:
      +id = U32.show(n)
      (Store{(n + 1 : U32), Map.set(&2, Bytes(), ns, id, text)},
        Http.with.header(Json.respond(201, note(id, text)), "location", Bytes.append("/notes/", id)))

def add.text(+db: Chan(Store), m: Maybe<&2, Bytes()>) -> IO(Http.Response):
  match m:
    case Some{+text}:
      locked(db, st => add.of(text, st))
    case None{}:
      Http.reply(Json.respond(422, Json.obj([Json.kv("error", Json.str("a note needs a text"))])))

def add.body(+db: Chan(Store), r: Result<&2, &2, J.Why, J.Json>) -> IO(Http.Response):
  match r:
    case Done{j}:
      add.text(db, Json.get.str(j, "text"))
    case Fail{w}:
      Http.reply(Json.refused(w))

def add(+db: Chan(Store), r: Http.Request) -> IO(Http.Response):
  add.body(db, Json.body(r, 65536))

# GET /notes/:id
def one.at(+id: Bytes(), got: Map<&2, Bytes()> & Bytes(), +n: U32) -> Store & Http.Response:
  (ns, +text) = got
  (Store{n, ns}, Bool.pick(Http.Response, String.is_empty(text), Http.plain(404), Json.respond(200, note(id, text))))

def one.of(+id: Bytes(), st: Store) -> Store & Http.Response:
  match st:
    case Store{+n, ns}:
      one.at(id, Map.get(Bytes(), "", ns, id), n)

def one(+db: Chan(Store), r: Http.Request) -> IO(Http.Response):
  +id = Http.param(r, "id")
  locked(db, st => one.of(id, st))

# DELETE /notes/:id
def del.at(+id: Bytes(), got: Map<&2, Bytes()> & Bool, +n: U32) -> Store & Http.Response:
  (ns, had) = got
  match had:
    case True{}:
      (Store{n, Map.del(&2, Bytes(), ns, id)}, Http.Response{204, Nil{}, Http.BBody{""}})
    case False{}:
      (Store{n, ns}, Http.plain(404))

def del.of(+id: Bytes(), st: Store) -> Store & Http.Response:
  match st:
    case Store{+n, ns}:
      del.at(id, Map.has(&2, Bytes(), ns, id), n)

def del(+db: Chan(Store), r: Http.Request) -> IO(Http.Response):
  +id = Http.param(r, "id")
  locked(db, st => del.of(id, st))

def health(r: Http.Request) -> IO(Http.Response):
  Http.reply(Json.respond(200, Json.obj([Json.kv("ok", Json.yes())])))

def routes(+db: Chan(Store)) -> List<Server.Route>:
  [Server.get("/health", health),
   Server.get("/notes", r => list(db, r)),
   Server.post("/notes", r => add(db, r)),
   Server.get("/notes/:id", r => one(db, r)),
   Server.delete("/notes/:id", r => del(db, r))]

# the routes, each request logged, the browser's headers added
def app.go(+db: Chan(Store), +r: Http.Request) -> IO(Http.Response):
  Server.log.around(r, Server.secure.around(Server.route(routes(db), r)))

def app(+db: Chan(Store), r: Http.Request) -> IO(Http.Response):
  app.go(db, r)

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<&2, String> <- Server.argv()
    +db : Chan(Store) <- Chan.new(Store, 1)
    ok : Bool <- Chan.send(Store, db, Store{1, Map.new(&2, Bytes())})
    Server.serve.with(~Chan(Store), ~app, db, Server.args(xs, Server.config(8080)))
