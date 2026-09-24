# Server-sent events from a route: an event stream, with keepalives.
#
#   bend net/examples/events.bend -o events && ./events --port 8080
#   curl -N 'http://127.0.0.1:8080/ticks?n=5&ms=1000'
#
# GET /ticks?n=N&ms=MS is an event stream (Stream.events): N events named
# tick, one every MS ms (N of 0: until the client leaves), each with its
# number as its data and id; when --keepalive-ms (15000) passes with no
# event, a comment goes out instead, which keeps a proxy from timing the
# stream out and finds a client that left. The stream ends after the
# N-th event, when the client leaves, or at SIGTERM. GET / is the page
# that listens to it (EventSource). &delay=MS has the handler wait MS ms
# before it answers: past the server's handler time (--handler-ms, 30 s)
# that is a 503, while a stream once begun runs as long as it likes
# (each of its sends has the send time).
import Base
import ../http.bend as Http
import ../server.bend as Server
import ../stream.bend as Stream

# the source: the events sent, those left, when the next is due (ms), and
# the time between them
type Tk is Data:
  Tk{n: Nat, left: Nat, due: Nat, every: Nat}

def tick(t: Tk) -> Tk & Stream.Ev:
  match t:
    case Tk{+n, +left, +due, +every}:
      (Tk{1n+n, Nat.sub(left, 1n), Nat.add(due, every), every}, Stream.Event{"tick", Nat.show(n), Nat.show(n)})

def slept(u: Unit, t: Tk) -> IO(Tk & Stream.Ev):
  IO.pure(Tk & Stream.Ev, tick(t))

def waited(u: Unit, t: Tk) -> IO(Tk & Stream.Ev):
  IO.pure(Tk & Stream.Ev, (t, Stream.idle()))

# the next event, within wait ms: due now, due within wait (slept to),
# or not yet (a keepalive, after wait)
def next.at(over: Bool, now.due: Bool, soon: Bool, +d: Nat, +wait: U32, t: Tk) -> IO(Tk & Stream.Ev):
  match over now.due soon:
    case True{} _ _:
      IO.pure(Tk & Stream.Ev, (t, Stream.over()))
    case False{} True{} _:
      IO.pure(Tk & Stream.Ev, tick(t))
    case False{} False{} True{}:
      IO.bind(Unit, Tk & Stream.Ev, IO.sleep(U32.from_nat(d)), u => slept(u, t))
    case False{} False{} False{}:
      IO.bind(Unit, Tk & Stream.Ev, IO.sleep(wait), u => waited(u, t))

def next.now(t: Tk, +now: Nat, +wait: U32) -> IO(Tk & Stream.Ev):
  match t:
    case Tk{+n, +left, +due, +every}:
      next.at(Nat.is_eq(left, 0n), Nat.is_le(due, now), Nat.is_le(Nat.sub(due, now), U32.to_nat(wait)), Nat.sub(due, now),
        wait, Tk{n, left, due, every})

def next.go(t: Tk, +wait: U32) -> IO(Tk & Stream.Ev):
  IO.bind(Nat, Tk & Stream.Ev, IO.now(), now => next.now(t, now, wait))

def next(t: Tk, wait: U32) -> IO(Tk & Stream.Ev):
  next.go(t, wait)

def num.of(m: Maybe<&2, Bytes()>, +d: Nat) -> Nat:
  match m:
    case None{}:
      d
    case Some{v}:
      Maybe.default(&2, Nat, Maybe.map(&2, U32, Nat, U32.to_nat, U32.read(v)), d)

def num(r: Http.Request, +k: Bytes(), +d: Nat) -> Nat:
  num.of(Http.query.get(r, k), d)

def started(+keep: U32, +n: Nat, +ms: Nat, +now: Nat) -> IO(Stream.Reply):
  +left = Bool.pick(Nat, Nat.is_eq(n, 0n), U32.to_nat(4294967295), n)
  IO.pure(Stream.Reply, Stream.events(~Tk, ~next, Tk{0n, left, now, ms}, keep, []))

def delayed(+keep: U32, +n: Nat, +ms: Nat, u: Unit) -> IO(Stream.Reply):
  IO.bind(Nat, Stream.Reply, IO.now(), now => started(keep, n, ms, now))

def ticks.go(+keep: U32, +r: Http.Request) -> IO(Stream.Reply):
  +n = num(r, "n", 0n)
  +ms = num(r, "ms", 1000n)
  IO.bind(Unit, Stream.Reply, IO.sleep(U32.from_nat(num(r, "delay", 0n))), u => delayed(keep, n, ms, u))

# GET /ticks
def ticks(+keep: U32, r: Http.Request) -> IO(Stream.Reply):
  ticks.go(keep, r)

def page() -> Bytes():
  "<!doctype html><title>ticks</title><pre id=o></pre><script>
new EventSource('/ticks?ms=1000').addEventListener('tick', e => { o.textContent += 'tick ' + e.data + '\\n' })
</script>
"

def index(r: Http.Request) -> IO(Http.Response):
  Http.reply(Http.html(200, page()))

def routes(+keep: U32) -> List<Server.Route>:
  [Server.get("/", index), Stream.get("/ticks", r => ticks(keep, r))]

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    ys : List<String> <- IO.args()
    +keep : U32 = Server.arg.num(Server.flag(xs, "--keepalive-ms", "15000"), 15000)
    Server.serve.routes(~U32, ~routes, keep, Server.args(ys, Server.config(8080)))
