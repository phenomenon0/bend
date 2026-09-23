# A static file server: the files under a directory, by the engine's
# page path (normalised, no climb out of the root, no dotfile, no link
# followed, sent by the kernel's sendfile), with the browser's headers.
#
#   bend net/examples/file_server.bend -o files && ./files --port 8080 --root www
#   curl -i localhost:8080/            www/index.html
#   curl -i localhost:8080/a/b.css     www/a/b.css
#   curl -i localhost:8080/../etc/passwd                 404
import Base
import ../http.bend as Http
import ../server.bend as Server

def health(r: Http.Request) -> IO(Http.Response):
  Http.reply(Http.text(200, "ok\n"))

def routes(+root: Bytes()) -> List<Server.Route>:
  [Server.get("/health", health), Server.static("", root)]

def app.go(+root: Bytes(), +r: Http.Request) -> IO(Http.Response):
  Server.log.around(r, Server.secure.around(Server.route(routes(root), r)))

def app(+root: Bytes(), r: Http.Request) -> IO(Http.Response):
  app.go(root, r)

def main() -> IO(Unit):
  do IO<Unit>:
    +xs : List<&2, String> <- Server.argv()
    Server.serve.with(~Bytes(), ~app, Server.flag(xs, "--root", "www"), Server.args(xs, Server.config(8080)))
