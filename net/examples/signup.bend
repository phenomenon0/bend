# A JSON API that checks what it is sent: each field typed, a default for
# the ones that may be left out, and a 400 that lists every problem at
# once.
#
#   bend net/examples/signup.bend -o signup && ./signup --port 8080
#   curl -s localhost:8080/signup -d '{"name":"Ada","age":36,"email":"ada@x.org","tags":["math"]}'
#       201, {"name":"Ada","age":36,"email":"ada@x.org","tags":1,"newsletter":false}
#   curl -s localhost:8080/signup -d '{"name":7,"age":-1}'
#       400, {"errors":["name must be a string","age must be a whole number from 0 to 4294967295",
#                       "email is required"]}
import Base
import ../http.bend as Http
import ../server.bend as Server
import ../json.bend as Json
import ../../power/json_value.bend as J

# an age a person may have
def age.ok(r: Json.Got(U32)) -> Json.Got(U32):
  match r:
    case Done{+n}:
      Bool.pick(Json.Got(U32), (n <= 150 : U32), Done{n}, Fail{"age must be at most 150"})
    case Fail{why}:
      Fail{why}

# every field read, every reason kept: a 201 with what was read, or a 400
def checked(+name: Json.Got(Bytes()), +age: Json.Got(U32), +email: Json.Got(Bytes()),
  +tags: Json.Got(List<&2, J.Json>), +news: Json.Got(Bool)) -> Http.Response:
  +whys = Json.fails(Bytes(), name, Json.fails(U32, age, Json.fails(Bytes(), email,
    Json.fails(List<&2, J.Json>, tags, Json.fails(Bool, news, [])))))
  Bool.pick(Http.Response, List.is_empty(&2, Bytes(), whys),
    Json.respond(201, Json.obj([Json.kv("name", Json.str(Result.default(&2, &2, Bytes(), Bytes(), name, ""))),
      Json.kv("age", Json.num(Result.default(&2, &2, Bytes(), U32, age, 0))),
      Json.kv("email", Json.str(Result.default(&2, &2, Bytes(), Bytes(), email, ""))),
      Json.kv("tags", Json.nat(List.length(&2, J.Json, Result.default(&2, &2, Bytes(), List<&2, J.Json>, tags, [])))),
      Json.kv("newsletter", Json.flag(Result.default(&2, &2, Bytes(), Bool, news, False{})))])),
    Json.errors(400, whys))

def signup.of(+j: J.Json) -> Http.Response:
  checked(Json.get.str(j, "name"), age.ok(Json.get.u32(j, "age")), Json.get.str(j, "email"),
    Json.or(List<&2, J.Json>, j, "tags", [], Json.get.arr), Json.or(Bool, j, "newsletter", False{}, Json.get.bool))

def signup.body(r: Result<&2, &2, J.Why, J.Json>) -> IO(Http.Response):
  match r:
    case Done{+j}:
      Http.reply(signup.of(j))
    case Fail{w}:
      Http.reply(Json.refused(w))

# POST /signup
def signup(r: Http.Request) -> IO(Http.Response):
  signup.body(Json.body(r, 65536))

# each request logged
def table(+u: Unit) -> List<&1, Server.Route>:
  Server.wrap(~Server.logged.around, [Server.post("/signup", signup)])

def main() -> IO(Unit):
  do IO<Unit>:
    +xs : List<&2, String> <- Server.argv([])
    Server.serve.routes(~Unit, ~table, Unit{}, Server.args(xs, Server.config(8080)))
