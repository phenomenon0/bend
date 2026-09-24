# Fetch, parse, serve: a small API in front of another one. GET
# /users/:id fetches the upstream's /users/:id, reads its JSON, and
# answers the fields it keeps; every way the fetch can fail is its own
# answer (a 504 for a timeout, a 502 for the rest).
#
#   bend net/examples/relay.bend -o relay
#   ./relay --port 8080 --upstream http://127.0.0.1:9000
#   curl -s localhost:8080/users/1      {"id":"1","name":"Ada","via":"http://127.0.0.1:9000"}
#
# The session is made once and handed to every call as serve.with's
# environment, so requests to the upstream share pooled connections.
import Base
import ../http.bend as Http
import ../server.bend as Server
import ../client.bend as Client
import ../json.bend as Json
import ../../power/json_value.bend as J

# what every handler is handed: the client's session and the upstream
type Env is Data:
  Env{s: Client.Session, up: Bytes()}

def env.s(e: Env) -> Client.Session:
  match e:
    case Env{s, up}:
      s

def env.up(e: Env) -> Bytes():
  match e:
    case Env{s, up}:
      up

def failed(status: U32, why: Bytes()) -> Http.Response:
  Json.respond(status, Json.obj([Json.kv("error", Json.str(why))]))

# the upstream's JSON, cut to the fields this API promises
def kept(+id: Bytes(), +up: Bytes(), name: Maybe<&2, Bytes()>) -> Http.Response:
  match name:
    case Some{n}:
      Json.respond(200, Json.obj([Json.kv("id", Json.str(id)), Json.kv("name", Json.str(n)),
        Json.kv("via", Json.str(up))]))
    case None{}:
      failed(502, "the upstream's answer has no name")

def parsed(+id: Bytes(), +up: Bytes(), r: Result<&2, &2, J.Why, J.Json>) -> Http.Response:
  match r:
    case Done{j}:
      kept(id, up, Json.get.str(j, "name"))
    case Fail{w}:
      failed(502, Bytes.append("the upstream's JSON: ", Json.why.show(w)))

def answered(+id: Bytes(), +up: Bytes(), +resp: Http.Response) -> Http.Response:
  Bool.pick(Http.Response, U32.is_eq(Http.status(resp), 200), parsed(id, up, Json.of(resp, 65536)),
    failed(502, Bytes.append("the upstream answered ", U32.show(Http.status(resp)))))

# a timeout is the upstream being slow: 504; anything else, 502
def fetched(+id: Bytes(), +up: Bytes(), r: Client.Res()) -> IO(Http.Response):
  match r:
    case Done{resp}:
      Http.reply(answered(id, up, resp))
    case Fail{e}:
      match e:
        case Client.Timeout{}:
          Http.reply(failed(504, "the upstream did not answer in time"))
        case _:
          Http.reply(failed(502, Client.error.show(e)))

# GET /users/:id
def user(+env: Env, r: Http.Request) -> IO(Http.Response):
  +id = Http.param(r, "id")
  +up = env.up(env)
  +url = Bytes.concat([up, "/users/", Http.pct.encode(id)])
  do IO<Http.Response>:
    res : Client.Res() <- Client.fetch(env.s(env), Client.req("GET", url))
    fetched(id, up, res)

def health(r: Http.Request) -> IO(Http.Response):
  Http.reply(Http.text(200, "ok\n"))

def routes(+env: Env) -> List<Server.Route>:
  [Server.get("/health", health), Server.get("/users/:id", r => user(env, r))]

def app.go(+env: Env, +r: Http.Request) -> IO(Http.Response):
  Server.logged.around(r, Server.route(routes(env), r))

def app(+env: Env, r: Http.Request) -> IO(Http.Response):
  app.go(env, r)

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    ys : List<String> <- IO.args()
    +s : Client.Session <- Client.session(Client.with.timeout(Client.opts(), 5000))
    +env : Env = Env{s, Server.flag(xs, "--upstream", "http://127.0.0.1:9000")}
    Server.serve.with(~Env, ~app, env, Server.args(ys, Server.config(8080)))
