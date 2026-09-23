# An HTTP/1.1 client on bend-wire: fetch a URL over http or https and
# print the status and the body's length (and, asked, the body). The
# name is resolved (DNS.resolve), the connection made under a deadline
# (TCP.connect_poll, or TLS.connect with SNI, ALPN http/1.1 and the
# certificate verified against the system's store or a pinned CA), and
# the exchange run by wire/client.bend: the response read through the
# reader resp_sim holds to RFC 9112, under a head cap, a body cap and a
# deadline, and refused rather than guessed at when it is framed two
# ways.
#
#   bend demos/io_http_client/main.bend -o hc
#   ./hc http://127.0.0.1:8080/health
#   ./hc https://localhost:8443/ --ca cert.pem --body
#   ./hc http://127.0.0.1:8080/ --head --twice
#
# It prints one line per response: the status, the body's length, the
# interim statuses before it, and whether the connection could carry
# another request. --twice gives the connection back to a pool
# (wire/pool.bend) and sends a second request on what the pool hands
# out: the same connection when it was fit to keep and nothing waits
# unread on it, a new one otherwise. It exits 1 when there is no
# response, with why.
import Base
import ../../wire/client.bend as C
import ../../wire/http1/resp.bend as R
import ../../wire/pool.bend as P

# The URL
# =======

type Url is Data:
  Url{tls: Bool, host: String, port: U32, path: String}

# s cut at its first c: what is before it, and what is after it if it is there
def cut.pick(hit: Bool, x: U32, t: String, r: String & Maybe<&2, String>) -> String & Maybe<&2, String>:
  match hit:
    case True{}:
      ("", Some{t})
    case False{}:
      (a, b) = r
      (SCon{Chr{x}, a}, b)

def cut(s: String, +c: U32) -> String & Maybe<&2, String>:
  match s:
    case SNil{}:
      ("", None{})
    case SCon{Chr{+x}, +t}:
      cut.pick(U32.is_eq(x, c), x, t, cut(t, c))

def url.port(tls: Bool, may: Maybe<&2, String>) -> Maybe<&2, U32>:
  match may:
    case None{}:
      Some{Bool.pick(U32, tls, 443, 80)}
    case Some{p}:
      U32.read(p)

def url.make(+tls: Bool, host: String, path: String, port: Maybe<&2, U32>) -> Maybe<&2, Url>:
  match port:
    case None{}:
      None{}
    case Some{n}:
      Some{Url{tls, host, n, path}}

def url.host(+tls: Bool, auth: String & Maybe<&2, String>, path: String) -> Maybe<&2, Url>:
  (host, port) = auth
  url.make(tls, host, path, url.port(tls, port))

def url.rest(+tls: Bool, r: String & Maybe<&2, String>) -> Maybe<&2, Url>:
  (auth, path) = r
  url.host(tls, cut(auth, 58), "/" ++ Maybe.default(&2, String, path, ""))

def url.scheme(https: Bool, http: Bool, +s: String) -> Maybe<&2, Url>:
  match https http:
    case True{} _:
      url.rest(True{}, cut(String.drop(s, 8n), 47))
    case False{} True{}:
      url.rest(False{}, cut(String.drop(s, 7n), 47))
    case False{} False{}:
      None{}

def url.parse(+s: String) -> Maybe<&2, Url>:
  url.scheme(String.starts_with(s, "https://"), String.starts_with(s, "http://"), s)

# The options
# ===========

# the URL; --head: HEAD rather than GET; --body: print the body;
# --twice: a second request on the connection, when it may carry one;
# --ca FILE: trust only the certificates in FILE (ca says the next
# argument is that file)
type Opt is Data:
  Opt{url: String, head: Bool, body: Bool, twice: Bool, ca: String, next: Bool}

def opt.take(+x: String, o: Opt) -> Opt:
  match o:
    case Opt{url, head, body, twice, ca, next}:
      match next:
        case True{}:
          Opt{url, head, body, twice, x, False{}}
        case False{}:
          Opt{Bool.pick(String, String.starts_with(x, "--"), url, x), head || String.eq(x, "--head"),
            body || String.eq(x, "--body"), twice || String.eq(x, "--twice"), ca, String.eq(x, "--ca")}

def opt.url(o: Opt) -> String:
  match o:
    case Opt{url, head, body, twice, ca, next}:
      url

def opts(xs: List<String>, o: Opt) -> Opt:
  match xs:
    case Nil{}:
      o
    case Con{+x, rest}:
      opts(rest, opt.take(x, o))

# The exchange
# ============

# a body cap of 16 MiB, and 64 KiB of head, 30 s for an exchange and
# 10 s for any one read or send
def ask.of(head: Bool) -> R.Ask:
  R.ask.new(head, 16777216)

def budget() -> C.Budget:
  C.Budget{65536, 30000, 10000}

def host.of(u: Url) -> String:
  match u:
    case Url{tls, +host, +port, path}:
      Bool.pick(String, U32.is_eq(port, Bool.pick(U32, tls, 443, 80)), host, host ++ ":" ++ U32.show(port))

def req.of(+head: Bool, +u: Url) -> Bytes():
  match u:
    case Url{tls, host, port, path}:
      C.request(Bool.pick(String, head, "HEAD", "GET"), path, host.of(u),
        "User-Agent: bend-wire\r\nAccept: */*\r\n", "")

def interim.show(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, t}:
      " " ++ U32.show(x) ++ interim.show(t)

def got.line(g: C.Got) -> String:
  match g:
    case C.Got{i, r, reuse}:
      match r:
        case R.Resp{code, v10, close, +body}:
          "status " ++ U32.show(code) ++ ", body " ++ Nat.show(Bytes.len(body)) ++ " bytes, interim ["
            ++ interim.show(i) ++ " ], " ++ Bool.pick(String, reuse, "reusable", "not reusable")

def got.body(g: C.Got) -> String:
  match g:
    case C.Got{i, r, reuse}:
      match r:
        case R.Resp{code, v10, close, body}:
          body

def got.reuse(g: C.Got) -> Bool:
  match g:
    case C.Got{i, r, reuse}:
      reuse

def said.body(show: Bool, g: C.Got) -> IO(Unit):
  match show:
    case True{}:
      IO.write(got.body(g))
    case False{}:
      IO.pure(Unit, Unit{})

def said(+show: Bool, +g: C.Got) -> IO(Unit):
  do IO<Unit>:
    IO.print(got.line(g))
    said.body(show, g)

# an exchange's answer: printed, and the socket back with whether it may
# carry another request; no response ends the program, with why
def answered(+show: Bool, m: C.Out(Socket)) -> IO(Socket & Bool):
  (s, r) = m
  match r:
    case Fail{w}:
      do IO<Socket & Bool>:
        Socket.close(s)
        IO.die(Socket & Bool, 1, "no response: " ++ C.why.show(w))
    case Done{+g}:
      do IO<Socket & Bool>:
        said(show, g)
        return (s, got.reuse(g))

# The connection
# ==============

def plain(r: Result<&1, &1, U32 & String, Socket>) -> IO(Socket):
  IO.pass(Socket, r)

def secure(r: Result<&1, &1, U32 & String, Socket & String>) -> IO(Socket):
  match r:
    case Done{sp}:
      (s, proto) = sp
      IO.pure(Socket, s)
    case Fail{e}:
      (code, msg) = e
      IO.die(Socket, 1, "TLS: " ++ msg ++ " (" ++ U32.show(code) ++ ")")

def dial(+o: Opt, +u: Url, addr: String) -> IO(Socket):
  match o u:
    case Opt{url, head, body, twice, ca, next} Url{tls, host, +port, path}:
      match tls:
        case True{}:
          IO.bind(Result<&1, &1, U32 & String, Socket & String>, Socket,
            TLS.connect(addr, port, host, "http/1.1", ca, 10000), secure)
        case False{}:
          IO.bind(Result<&1, &1, U32 & String, Socket>, Socket, TCP.connect_poll(addr, port, 10000), plain)

# one exchange on a socket
def exchange(+o: Opt, +u: Url, s: Socket) -> IO(Socket & Bool):
  match o:
    case Opt{url, +head, +body, twice, ca, next}:
      IO.bind(C.Out(Socket), Socket & Bool, C.fetch(ask.of(head), budget(), req.of(head, u), s), m => answered(body, m))

# The pool
# ========
#
# The first connection goes back to a pool (wire/pool.bend) with whether
# its exchange left it fit; --twice takes from the pool, which hands it
# out only if it was kept, is fresh, and has nothing unread on it --
# else the second request dials a new one.

def keep(+now: Nat, +born: Nat, sb: Socket & Bool) -> IO(P.Pool<&1, Socket>):
  (s, ok) = sb
  P.give.io(P.pool.new(&1, Socket, 4n, 60000n, 5000n), s, born, now, ok)

def second.on(+o: Opt, +u: Url, +addr: String, may: Maybe<&1, P.Slot<&1, Socket>>) -> IO(Socket & Bool):
  match may:
    case Some{sl}:
      match sl:
        case P.Slot{s, born, last}:
          do IO<Socket & Bool>:
            IO.print("again, on the same connection:")
            exchange(o, u, s)
    case None{}:
      do IO<Socket & Bool>:
        IO.print("again, on a new connection (the first was not fit to keep):")
        s : Socket <- dial(o, u, addr)
        exchange(o, u, s)

def second(+o: Opt, +u: Url, +addr: String, pm: P.Pool<&1, Socket> & Maybe<&1, P.Slot<&1, Socket>>) -> IO(Unit):
  (pool, may) = pm
  do IO<Unit>:
    sb : Socket & Bool <- second.on(o, u, addr, may)
    Socket.close(Pair.fst(Socket, Bool, sb))
    P.close.all(~(A => IO(A)), ~IO.pure, ~IO.bind, ~&1, ~Socket, ~Socket.close, P.pool.xs(&1, Socket, pool))

def done(+o: Opt, +u: Url, +addr: String, pool: P.Pool<&1, Socket>) -> IO(Unit):
  match o:
    case Opt{url, head, body, twice, ca, next}:
      match twice:
        case False{}:
          P.close.all(~(A => IO(A)), ~IO.pure, ~IO.bind, ~&1, ~Socket, ~Socket.close, P.pool.xs(&1, Socket, pool))
        case True{}:
          do IO<Unit>:
            now : Nat <- IO.now()
            pm : P.Pool<&1, Socket> & Maybe<&1, P.Slot<&1, Socket>> <- P.take.io(pool, now)
            second(o, u, addr, pm)

def run(+o: Opt, +u: Url) -> IO(Unit):
  match u:
    case Url{tls, host, port, path}:
      do IO<Unit>:
        +addr : String <- IO.try(String, DNS.resolve(host))
        +t0 : Nat <- IO.now()
        s : Socket <- dial(o, u, addr)
        sb : Socket & Bool <- exchange(o, u, s)
        +t1 : Nat <- IO.now()
        pool : P.Pool<&1, Socket> <- keep(t1, t0, sb)
        done(o, u, addr, pool)

def start(+o: Opt, may: Maybe<&2, Url>) -> IO(Unit):
  match may:
    case None{}:
      IO.die(Unit, 2, "usage: hc http[s]://host[:port][/path] [--head] [--body] [--twice] [--ca FILE]")
    case Some{+u}:
      run(o, u)

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    +o : Opt = opts(xs, Opt{"", False{}, False{}, False{}, "", False{}})
    start(o, url.parse(opt.url(o)))
