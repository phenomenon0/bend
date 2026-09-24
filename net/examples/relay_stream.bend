# A relay that streams: a body fetched upstream passed on as it comes,
# never held whole, end to end.
#
#   bend net/examples/relay_stream.bend -o relay_stream
#   ./relay_stream --port 8081 --upstream http://127.0.0.1:8080
#   curl -s 'http://127.0.0.1:8081/relay?path=/bytes%3Fn%3D100000000' | wc -c
#
# GET /relay?path=P fetches the upstream's P (Client.stream) and writes
# each piece of its body into the response (Stream.pour, chunked) as it
# arrives: the upstream is read only as fast as the client takes the
# response, so the relay holds a window, whatever the size. The head goes
# out before the upstream answers, so an upstream that fails, or answers
# other than 2xx, cuts the response short (Stream.abort): the client sees
# no last chunk, and the relay says why on stderr.
import Base
import ../http.bend as Http
import ../server.bend as Server
import ../client.bend as Client
import ../stream.bend as Stream

# the consumer: each piece written to the response; a write that failed
# (the client left) takes nothing, which stops the upstream
def gave(w: Stream.Wrote(), +n: Nat) -> IO(Stream.Sink & Nat):
  (k, r) = w
  match r:
    case Done{u}:
      IO.pure(Stream.Sink & Nat, (k, n))
    case Fail{e}:
      IO.pure(Stream.Sink & Nat, (k, 0n))

def give.go(k: Stream.Sink, +x: Bytes()) -> IO(Stream.Sink & Nat):
  IO.bind(Stream.Wrote(), Stream.Sink & Nat, Stream.write(k, x), w => gave(w, Bytes.len(x)))

def give(k: Stream.Sink, x: Bytes()) -> IO(Stream.Sink & Nat):
  give.go(k, x)

def fin(k: Stream.Sink) -> IO(Stream.Sink):
  IO.pure(Stream.Sink, k)

def cut(+why: Bytes(), k: Stream.Sink) -> IO(Stream.Sink):
  do IO<Stream.Sink>:
    IO.print_err(Bytes.append("relay: cut short: ", why))
    return Stream.abort(k)

def ok2xx(+code: U32) -> Bool:
  U32.is_le(200, code) && U32.is_lt(code, 300)

def status.at(ok: Bool, +code: U32, k: Stream.Sink) -> IO(Stream.Sink):
  match ok:
    case True{}:
      IO.pure(Stream.Sink, k)
    case False{}:
      cut(Bytes.append("the upstream answered ", U32.show(code)), k)

# the upstream's answer, once its body is through
def relayed(q: Stream.Sink & Client.Res()) -> IO(Stream.Sink):
  (k, r) = q
  match r:
    case Done{+resp}:
      status.at(ok2xx(Http.status(resp)), Http.status(resp), k)
    case Fail{e}:
      cut(Client.error.show(e), k)

def path.of(m: Maybe<&2, Bytes()>) -> Bytes():
  match m:
    case Some{p}:
      Http.pct.decode(p)
    case None{}:
      "/"

# GET /relay?path=P
def relay(+up: Bytes(), r: Http.Request) -> IO(Stream.Reply):
  +url = Bytes.append(up, path.of(Http.query.get(r, "path")))
  IO.pure(Stream.Reply, Stream.pour(200, [Http.Header{"content-type", "application/octet-stream"}],
    k => IO.bind(Stream.Sink & Client.Res(), Stream.Sink,
      Client.stream(~Stream.Sink, ~give, ~fin, url, Client.opts(), k), relayed)))

def routes(+up: Bytes()) -> List<Server.Route>:
  [Stream.get("/relay", r => relay(up, r))]

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    ys : List<String> <- IO.args()
    +up : Bytes() = Server.flag(xs, "--upstream", "http://127.0.0.1:8080")
    Server.serve.routes(~Bytes(), ~routes, up, Server.args(ys, Server.config(8081)))
