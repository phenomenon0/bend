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

# each request logged, the browser's headers added
def mw(+r: Http.Request, io: IO(Http.Response)) -> IO(Http.Response):
  Server.logged.around(r, Server.secured.around(io))

def routes(+root: Bytes()) -> List<&1, Server.Route>:
  Server.wrap(~mw, [Server.get("/health", health), Server.static("", root)])

def main() -> IO(Unit):
  do IO<Unit>:
    +xs : List<&2, String> <- Server.argv(["--root DIR"])
    Server.serve.routes(~Bytes(), ~routes, Server.flag(xs, "--root", "www"), Server.args(xs, Server.config(8080)))
