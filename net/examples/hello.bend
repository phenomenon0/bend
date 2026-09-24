# The smallest server: one handler for every request.
#
#   bend net/examples/hello.bend -o hello && ./hello --port 8080
#   curl -i http://127.0.0.1:8080/
import Base
import ../http.bend as Http
import ../server.bend as Server

def hello(req: Http.Request) -> IO(Http.Response):
  Http.reply(Http.text(200, "Hello, world!\n"))

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    Server.serve(~hello, Server.args(xs, Server.config(8080)))
