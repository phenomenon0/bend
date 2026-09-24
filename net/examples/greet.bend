# A query string, a handler that can fail, middleware as templates, and
# a configuration set in code (the command line may still change it).
#
#   bend net/examples/greet.bend -o greet && ./greet --port 8080
#   curl 'localhost:8080/greet?name=Ada'     Hello, Ada!
#   curl 'localhost:8080/greet'              Hello, stranger!
#   curl localhost:8080/add/2/3              5
#   curl -i localhost:8080/add/2/x           500; "handler failed: ..." on stderr
import Base
import ../http.bend as Http
import ../server.bend as Server

# GET /greet?name=...: the query's value, percent-decoded, or a default
def greet(r: Http.Request) -> IO(Http.Response):
  +name = Maybe.default(&2, Bytes(), Http.query.get(r, "name"), "stranger")
  Http.reply(Http.text(200, Bytes.concat(["Hello, ", name, "!\n"])))

# GET /add/:a/:b: a handler that answers Done{response} or Fail{why};
# Server.recover.around turns a Fail into a plain 500
def sum(a: Maybe<&2, U32>, b: Maybe<&2, U32>) -> Result<&2, &2, Bytes(), Http.Response>:
  match a b:
    case Some{x} Some{y}:
      Done{Http.text(200, Bytes.append(U32.show((x + y : U32)), "\n"))}
    case _ _:
      Fail{"/add wants two numbers"}

def add(+r: Http.Request) -> IO(Result<&2, &2, Bytes(), Http.Response>):
  IO.pure(Result<&2, &2, Bytes(), Http.Response>, sum(U32.read(Http.param(r, "a")), U32.read(Http.param(r, "b"))))

def routes() -> List<Server.Route>:
  [Server.get("/greet", greet), Server.get("/add/:a/:b", r => Server.recover.around(add(r)))]

# a line per request on stderr (the around form: it reads r twice, so r
# is reusable here and app hands it over)
def app.go(+r: Http.Request) -> IO(Http.Response):
  Server.log.around(r, Server.route(routes(), r))

def app(r: Http.Request) -> IO(Http.Response):
  app.go(r)

# 2 s of idle, bodies of at most 64 KiB, at most 256 connections
def config() -> Server.Cfg:
  Server.set.conns(Server.set.max_body(Server.set.idle(Server.config(8080), 2000), 65536), 256)

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<&2, String> <- Server.argv()
    Server.serve(~Server.secured(~app), Server.args(xs, config()))
