# A server over TLS: the certificate and key are PEM files, set in the
# configuration; TLS 1.2 or later, ALPN http/1.1. Every other default
# (the timeouts, the limits) is the same as over plain TCP.
#
#   openssl req -x509 -newkey rsa:2048 -nodes -days 30 -subj /CN=localhost \
#     -keyout key.pem -out cert.pem
#   bend net/examples/tls_server.bend -o tls && ./tls --port 8443 --tls-cert cert.pem --tls-key key.pem
#   curl --cacert cert.pem https://localhost:8443/
#
# The pages carry the browser's headers (Server.secure.around) and a
# Strict-Transport-Security field, which tells a browser to use https
# for this host from then on.
import Base
import ../http.bend as Http
import ../server.bend as Server

def hello(r: Http.Request) -> IO(Http.Response):
  Http.reply(Http.text(200, Bytes.concat(["Hello over TLS, ", Http.remote(r), "\n"])))

def hsts(resp: Http.Response) -> Http.Response:
  Http.with.header(resp, "strict-transport-security", "max-age=31536000")

def app(r: Http.Request) -> IO(Http.Response):
  IO.bind(Http.Response, Http.Response, Server.secure.around(Server.route([Server.get("/", hello)], r)),
    resp => Http.reply(hsts(resp)))

def main() -> IO(Unit):
  do IO<Unit>:
    +xs : List<&2, String> <- Server.argv()
    +cert : String = Server.flag(xs, "--tls-cert", "cert.pem")
    +key : String = Server.flag(xs, "--tls-key", "key.pem")
    Server.serve(~app, Server.set.tls(Server.args(xs, Server.config(8443)), cert, key))
