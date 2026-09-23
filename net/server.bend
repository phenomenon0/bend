# bend-net: the server.
#
#   Server.serve(~app, Server.config(8080))
#
# app is a handler, Http.Request -> IO(Http.Response), passed as a
# template: it compiles into the connection loop as a direct call.
# Middleware is a template from handler to handler (logged, recover,
# secured below), so ~Server.logged(~Server.secured(~app)) is one.
#
# Each connection is read by the HTTP engine's reader
# (demos/io_http_engine, held to RFC 9112 by frame_sim) through
# bend-proxy's scan (demos/io_proxy/core.bend, held to the engine's
# spec for any cut of the stream by scan_is_spec): every read goes
# through it whole, and the requests it completes are handed to the
# handler in order, adapted by Http.req.of (net/LAWS.bend's
# handler_framed). Each response is written by Http.encode.bytes
# (respond_framed) or, for a file, by the engine's page path, and a
# read's responses go out in one send. Everything is bounded and timed:
#
#   idle      a connection with no request in progress waits this long
#             for one (5 s), and every send waits at most send (10 s)
#             for progress
#   head      a request's head must arrive within head (10 s) of its
#             first byte, and be at most max_head (16 KiB) past the
#             read it began in: 408, 431
#   body      a request, head and body, within body (30 s): 408; a body
#             announced past max_body (1 MiB, the engine's cap) is
#             refused before a byte of it is read: 413
#   target    at most 8 KiB (the engine's): 414
#   conns     at most conns connections at once (1024); a SIGTERM closes
#             the listener, lets idle connections go at once, and ends
#             the process when the rest are done or grace (5 s) is up
#
# A broken request (the reader refuses it) is a 400 that closes; nothing
# after it on the connection is read. One connection's failure is its
# own: each is its own computation, with its own socket and deadlines.
import Base
import ../wire/reader.bend as Wr
import ../wire/loop.bend as L
import ../wire/effects.bend as Fx
import ../demos/io_http_engine/main.bend as Eng
import ../demos/io_proxy/core.bend as X
import ./http.bend as Http

# The peer's address (bend-proxy's effect)
def Peer.addr(s: Socket) -> IO(Socket & String):
  import "../demos/io_proxy/peer.c"
  import "../demos/io_proxy/peer.js"

# Configuration
# =============

type Cfg is Data:
  Cfg{port: U32, idle: U32, head: U32, body: U32, send: U32, max_head: U32, max_body: U32,
    conns: U32, grace: U32, cert: String, key: String, shared: Bool}

# the defaults: every one a bound
def config(port: U32) -> Cfg:
  Cfg{port, 5000, 10000, 30000, 10000, 16384, 1048576, 1024, 5000, "", "", False{}}

def cfg.port(c: Cfg) -> U32:
  match c:
    case Cfg{port, idle, head, body, send, mh, mb, conns, grace, cert, key, shared}:
      port

def cfg.idle(c: Cfg) -> U32:
  match c:
    case Cfg{port, idle, head, body, send, mh, mb, conns, grace, cert, key, shared}:
      idle

def cfg.head(c: Cfg) -> U32:
  match c:
    case Cfg{port, idle, head, body, send, mh, mb, conns, grace, cert, key, shared}:
      head

def cfg.body(c: Cfg) -> U32:
  match c:
    case Cfg{port, idle, head, body, send, mh, mb, conns, grace, cert, key, shared}:
      body

def cfg.send(c: Cfg) -> U32:
  match c:
    case Cfg{port, idle, head, body, send, mh, mb, conns, grace, cert, key, shared}:
      send

def cfg.max_head(c: Cfg) -> U32:
  match c:
    case Cfg{port, idle, head, body, send, mh, mb, conns, grace, cert, key, shared}:
      mh

def cfg.max_body(c: Cfg) -> U32:
  match c:
    case Cfg{port, idle, head, body, send, mh, mb, conns, grace, cert, key, shared}:
      mb

def cfg.conns(c: Cfg) -> U32:
  match c:
    case Cfg{port, idle, head, body, send, mh, mb, conns, grace, cert, key, shared}:
      conns

def cfg.grace(c: Cfg) -> U32:
  match c:
    case Cfg{port, idle, head, body, send, mh, mb, conns, grace, cert, key, shared}:
      grace

def cfg.cert(c: Cfg) -> String:
  match c:
    case Cfg{port, idle, head, body, send, mh, mb, conns, grace, cert, key, shared}:
      cert

def cfg.key(c: Cfg) -> String:
  match c:
    case Cfg{port, idle, head, body, send, mh, mb, conns, grace, cert, key, shared}:
      key

def cfg.shared(c: Cfg) -> Bool:
  match c:
    case Cfg{port, idle, head, body, send, mh, mb, conns, grace, cert, key, shared}:
      shared

def set.idle(c: Cfg, ms: U32) -> Cfg:
  match c:
    case Cfg{port, idle, head, body, send, mh, mb, conns, grace, cert, key, shared}:
      Cfg{port, ms, head, body, send, mh, mb, conns, grace, cert, key, shared}

def set.head(c: Cfg, ms: U32) -> Cfg:
  match c:
    case Cfg{port, idle, head, body, send, mh, mb, conns, grace, cert, key, shared}:
      Cfg{port, idle, ms, body, send, mh, mb, conns, grace, cert, key, shared}

def set.body(c: Cfg, ms: U32) -> Cfg:
  match c:
    case Cfg{port, idle, head, body, send, mh, mb, conns, grace, cert, key, shared}:
      Cfg{port, idle, head, ms, send, mh, mb, conns, grace, cert, key, shared}

def set.send(c: Cfg, ms: U32) -> Cfg:
  match c:
    case Cfg{port, idle, head, body, send, mh, mb, conns, grace, cert, key, shared}:
      Cfg{port, idle, head, body, ms, mh, mb, conns, grace, cert, key, shared}

def set.max_head(c: Cfg, n: U32) -> Cfg:
  match c:
    case Cfg{port, idle, head, body, send, mh, mb, conns, grace, cert, key, shared}:
      Cfg{port, idle, head, body, send, n, mb, conns, grace, cert, key, shared}

# at most the engine's cap, 1 MiB
def set.max_body(c: Cfg, n: U32) -> Cfg:
  match c:
    case Cfg{port, idle, head, body, send, mh, mb, conns, grace, cert, key, shared}:
      Cfg{port, idle, head, body, send, mh, U32.min(n, 1048576), conns, grace, cert, key, shared}

def set.conns(c: Cfg, n: U32) -> Cfg:
  match c:
    case Cfg{port, idle, head, body, send, mh, mb, conns, grace, cert, key, shared}:
      Cfg{port, idle, head, body, send, mh, mb, n, grace, cert, key, shared}

def set.grace(c: Cfg, ms: U32) -> Cfg:
  match c:
    case Cfg{port, idle, head, body, send, mh, mb, conns, grace, cert, key, shared}:
      Cfg{port, idle, head, body, send, mh, mb, conns, ms, cert, key, shared}

# serve TLS (1.2+, ALPN http/1.1) with the PEM files at these paths
def set.tls(c: Cfg, crt: String, k: String) -> Cfg:
  match c:
    case Cfg{port, idle, head, body, send, mh, mb, conns, grace, cert, key, shared}:
      Cfg{port, idle, head, body, send, mh, mb, conns, grace, crt, k, shared}

# share the port with other copies (SO_REUSEPORT; the runtime's
# --workers N forks them)
def set.shared(c: Cfg) -> Cfg:
  match c:
    case Cfg{port, idle, head, body, send, mh, mb, conns, grace, cert, key, shared}:
      Cfg{port, idle, head, body, send, mh, mb, conns, grace, cert, key, True{}}

# a configuration from the command line: --port N, --idle-ms N,
# --head-ms N, --body-ms N, --max-body N, --max-conns N, --grace-ms N,
# --tls-cert F --tls-key F, --shared; anything else is left alone
def arg.num(+s: String, d: U32) -> U32:
  Maybe.default(&2, U32, U32.read(s), d)

def args.one(+prev: String, +x: String, +c: Cfg) -> Cfg:
  match c:
    case Cfg{port, idle, head, body, send, mh, mb, conns, grace, cert, key, shared}:
      Cfg{Bool.pick(U32, String.eq(prev, "--port"), arg.num(x, port), port),
        Bool.pick(U32, String.eq(prev, "--idle-ms"), arg.num(x, idle), idle),
        Bool.pick(U32, String.eq(prev, "--head-ms"), arg.num(x, head), head),
        Bool.pick(U32, String.eq(prev, "--body-ms"), arg.num(x, body), body), send,
        Bool.pick(U32, String.eq(prev, "--max-head"), arg.num(x, mh), mh),
        Bool.pick(U32, String.eq(prev, "--max-body"), U32.min(arg.num(x, mb), 1048576), mb),
        Bool.pick(U32, String.eq(prev, "--max-conns"), arg.num(x, conns), conns),
        Bool.pick(U32, String.eq(prev, "--grace-ms"), arg.num(x, grace), grace),
        Bool.pick(String, String.eq(prev, "--tls-cert"), x, cert),
        Bool.pick(String, String.eq(prev, "--tls-key"), x, key), shared || String.eq(x, "--shared")}

def args.go(xs: List<&2, String>, +prev: String, c: Cfg) -> Cfg:
  match xs:
    case Nil{}:
      c
    case Con{+x, t}:
      args.go(t, x, args.one(prev, x, c))

def args(xs: List<&2, String>, c: Cfg) -> Cfg:
  args.go(xs, "", c)

def strs(xs: List<String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{x, strs(t)}

# the command line, as a list every flag reader may read
def argv() -> IO(List<&2, String>):
  IO.bind(List<String>, List<&2, String>, IO.args(), xs => IO.pure(List<&2, String>, strs(xs)))

def head.or(xs: List<&2, String>, d: String) -> String:
  match xs:
    case Nil{}:
      d
    case Con{v, t}:
      v

# a flag's value (the argument after it), or d
def flag(xs: List<&2, String>, +name: String, +d: String) -> String:
  match xs:
    case Nil{}:
      d
    case Con{+x, +t}:
      Bool.pick(String, String.eq(x, name), head.or(t, d), flag(t, name, d))

# The router
# ==========
#
# A route is the methods it answers, a pattern, and a handler. A
# pattern is a path cut at '/': a literal segment matches itself, :name
# matches any one non-empty segment and binds it (percent-decoded) as
# the param name, and a last * matches the rest, empty or not (bound
# raw as the param "*"). The first route whose pattern matches the path
# and whose methods hold the request's answers it; when patterns match
# but none holds the method, the answer is a 405 whose Allow lists every
# method those routes hold, each once, in order; when none matches, a
# 404. (LAWS.bend: route_first, against a reference spelled out there.)

type Route is Type:
  Route{methods: List<&2, Bytes()>, pat: Bytes(), h: Http.Request -> IO(Http.Response)}

# what the choice reads of a route
type Pat is Data:
  Pat{methods: List<&2, Bytes()>, pat: Bytes()}

def on(methods: List<&2, Bytes()>, pat: Bytes(), h: Http.Request -> IO(Http.Response)) -> Route:
  Route{methods, pat, h}

# GET answers HEAD too (the body is dropped when it is written)
def get(pat: Bytes(), h: Http.Request -> IO(Http.Response)) -> Route:
  Route{["GET", "HEAD"], pat, h}

def post(pat: Bytes(), h: Http.Request -> IO(Http.Response)) -> Route:
  Route{["POST"], pat, h}

def put(pat: Bytes(), h: Http.Request -> IO(Http.Response)) -> Route:
  Route{["PUT"], pat, h}

def patch(pat: Bytes(), h: Http.Request -> IO(Http.Response)) -> Route:
  Route{["PATCH"], pat, h}

def delete(pat: Bytes(), h: Http.Request -> IO(Http.Response)) -> Route:
  Route{["DELETE"], pat, h}

# the files under root, at prefix/...: the rest of the path names the
# file as the engine names one (normalised, no climb out of root, no
# dotfile, no link followed; / is index.html)
def static.at(+root: Bytes(), r: Http.Request) -> IO(Http.Response):
  Http.reply(Http.file(root, Bytes.append("/", Http.param(r, "*"))))

def static(prefix: Bytes(), root: Bytes()) -> Route:
  Route{["GET", "HEAD"], Bytes.append(prefix, "/*"), r => static.at(root, r)}

# a handler given an environment (serve.with)
def Hx(E: Data) -> Type:
  @+env: E -> Http.Request -> IO(Http.Response)

# what the loop does after a read's replies: go on with the socket, the
# scan, the start of the message in progress (None between messages),
# whether a 100 Continue went out for it, and the idle time left
def More() -> Type:
  Socket -> X.Scan -> Maybe<&2, Nat> -> Bool -> U32 -> IO(Socket)

# Between messages the wait is cut in slices of a second at most, so a
# SIGTERM lets an idle connection go within one; what is left of the
# idle time rides along (il).
def slice() -> U32:
  1000

# the server's own answers: a status and its reason, closing
def own(+head: Bool, +v10: Bool, +code: U32) -> Bytes():
  Http.encode.bytes(head, True{}, v10, code, [Http.Header{"content-type", "text/plain; charset=utf-8"}],
    Bytes.append(Bytes.append(U32.show(code), Bytes.append(" ", Http.reason(code))), "\n"))

# the segments waiting, newest first, written in order
def rev.onto(xs: List<&2, L.Seg>, acc: List<&2, L.Seg>) -> List<&2, L.Seg>:
  match xs:
    case Nil{}:
      acc
    case Con{x, t}:
      rev.onto(t, Con{x, acc})

# a file that could not be opened: a 404 that says keep-alive, so a
# Shut before it can make it say close
def miss(head: Bool) -> Bytes():
  Http.encode.bytes(head, False{}, True{}, 404, [Http.Header{"content-type", "text/plain; charset=utf-8"}],
    "404 Not Found\n")

def fhead(pre: Bytes(), n: U32) -> Bytes():
  Bytes.concat([pre, U32.show(n), "\r\nconnection: keep-alive\r\n\r\n"])

def sent.ok(m: L.Put(Socket)) -> Socket & Bool:
  (s, r) = m
  (s, Result.is_done(&1, &1, U32 & String, Unit, r))

def flush.segs(s: Socket, segs: List<&2, L.Seg>, +ms: U32) -> IO(Socket & Bool):
  match segs:
    case Nil{}:
      IO.pure(Socket & Bool, (s, True{}))
    case Con{g, t}:
      match g t:
        case L.Raw{bs} Nil{}:
          IO.bind(L.Put(Socket), Socket & Bool, TCP.send_buf_poll(s, bs, ms), m => IO.pure(Socket & Bool, sent.ok(m)))
        case _ _:
          IO.bind(L.Put(Socket), Socket & Bool,
            L.send.segs(~(A => IO(A)), ~IO.pure, ~IO.bind, ~Socket, ~Fx.Fh, ~TCP.send_buf_poll, ~IO.print_err,
              ~Fx.net.open, ~Fx.fh.size, ~Fx.fh.read, ~Fx.fh.send, ~Fx.fh.close, ~Eng.h.shut, ~fhead, ~miss,
              ~L.no.lnote, ~L.no.lsize, s, Con{g, t}, ms),
            m => IO.pure(Socket & Bool, sent.ok(m)))

# write what waits (newest first), then close
def fin(+cfg: Cfg, acc: List<&2, L.Seg>, s: Socket) -> IO(Socket):
  IO.bind(Socket & Bool, Socket, flush.segs(s, rev.onto(acc, Nil{}), cfg.send(cfg)),
    sb => IO.pure(Socket, Pair.fst(Socket, Bool, sb)))

# a message in progress whose clock ran out: 408, and the connection ends
def late(+cfg: Cfg, s: Socket) -> IO(Socket):
  fin(cfg, [L.Raw{own(False{}, False{}, 408)}], s)

def quiet(+cfg: Cfg, sc: X.Scan, cont: Bool, +il: U32, s: Socket, stop: Bool, more: More()) -> IO(Socket):
  match stop:
    case True{}:
      IO.pure(Socket, s)
    case False{}:
      more(s, sc, None{}, cont, (il - U32.min(il, slice()) : U32))

def got.none(+cfg: Cfg, sc: X.Scan, t0: Maybe<&2, Nat>, cont: Bool, +il: U32, s: Socket, last: Bool,
  more: More()) -> IO(Socket):
  match t0:
    case Some{t}:
      late(cfg, s)
    case None{}:
      match last:
        case True{}:
          IO.pure(Socket, s)
        case False{}:
          IO.bind(Bool, Socket, IO.signal_pending(15), stop => quiet(cfg, sc, cont, il, s, stop, more))

# the body a message in progress will bring, as far as it is known: a
# length's whole, or a chunked body's so far
def body.need(p: Eng.P) -> Nat:
  match p:
    case Eng.P{st, pd, out}:
      match st:
        case Eng.Bod{r, b}:
          Nat.add(r, Bytes.len(b))
        case Eng.Chd{r, b, left}:
          Nat.add(r, Bytes.len(b))
        case Eng.Chk{pos, n, b, left}:
          Bytes.len(b)
        case _:
          0n

# a message whose head is whole and whose body is coming, asking to be
# told to send it (RFC 9110 10.1.1)
def expects.low(xs: List<&2, Bytes()>) -> List<&2, Bytes()>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{Eng.lows(X.trim(x)), expects.low(t)}

def expects(+p: Eng.P) -> Bool:
  X.in.names("100-continue", expects.low(X.values("expect", Eng.p.fields(p))))

# write what waits, then go on unless the send failed
def next(sb: Socket & Bool, go: Socket -> IO(Socket)) -> IO(Socket):
  (s, ok) = sb
  match ok:
    case True{}:
      go(s)
    case False{}:
      IO.pure(Socket, s)

# the clock of a message in progress: kept from the read it began in,
# started now for one this read began
def tail.clock(+cfg: Cfg, mid: Bool, fresh: Bool, t0: Maybe<&2, Nat>, cont: Bool, s: Socket, sc: X.Scan,
  more: More()) -> IO(Socket):
  match mid:
    case False{}:
      more(s, sc, None{}, False{}, cfg.idle(cfg))
    case True{}:
      match fresh t0:
        case False{} Some{t}:
          more(s, sc, Some{t}, cont, cfg.idle(cfg))
        case _ _:
          IO.bind(Nat, Socket, IO.now(), now => more(s, sc, Some{now}, cont, cfg.idle(cfg)))

def tail.cont(ask: Bool, acc: List<&2, L.Seg>) -> List<&2, L.Seg>:
  match ask:
    case True{}:
      Con{L.Raw{"HTTP/1.1 100 Continue\r\n\r\n"}, acc}
    case False{}:
      acc

def tail.go(+cfg: Cfg, big: Bool, over: Bool, +ask: Bool, fresh: Bool, t0: Maybe<&2, Nat>, cont: Bool,
  acc: List<&2, L.Seg>, s: Socket, +p: Eng.P, +n: Nat, more: More()) -> IO(Socket):
  match big over:
    case True{} _:
      fin(cfg, Con{L.Raw{own(False{}, False{}, 431)}, acc}, s)
    case False{} True{}:
      fin(cfg, Con{L.Raw{own(False{}, False{}, 413)}, acc}, s)
    case False{} False{}:
      +mid = Eng.p.head(p) || Eng.p.body(p)
      IO.bind(Socket & Bool, Socket,
        flush.segs(s, rev.onto(tail.cont(ask, acc), Nil{}), cfg.send(cfg)),
        sb => next(sb, s2 => tail.clock(cfg, mid, fresh, t0, cont || ask, s2, X.Scan{p, n}, more)))

# After a read's requests: a tail refused is a 400; after an upgrade
# request (answered, and closing) nothing; waiting, a head past its cap
# is a 431, a body announced past its cap a 413, and a body asked to be
# sent is told to (once); then the replies go out, and the next read
# waits under the message's clock if one is in progress.
def tail.wait(+cfg: Cfg, fresh: Bool, t0: Maybe<&2, Nat>, +cont: Bool, acc: List<&2, L.Seg>, s: Socket, +p: Eng.P,
  +n: Nat, more: More()) -> IO(Socket):
  +big = Eng.p.head(p) && Nat.is_lt(U32.to_nat(cfg.max_head(cfg)), n)
  +over = Nat.is_lt(U32.to_nat(cfg.max_body(cfg)), body.need(p))
  +ask = Eng.p.body(p) && Bool.not(cont) && expects(p)
  tail.go(cfg, big, over, ask, fresh, t0, cont, acc, s, p, n, more)

def tail(+cfg: Cfg, t: X.Tail, fresh: Bool, t0: Maybe<&2, Nat>, cont: Bool, acc: List<&2, L.Seg>, s: Socket,
  more: More()) -> IO(Socket):
  match t:
    case X.TBad{}:
      fin(cfg, Con{L.Raw{own(False{}, False{}, 400)}, acc}, s)
    case X.TUp{}:
      fin(cfg, acc, s)
    case X.TWait{sc}:
      match sc:
        case X.Scan{+p, +n}:
          tail.wait(cfg, fresh, t0, cont, acc, s, p, n, more)

def hd.v10(h: Eng.Hd) -> Bool:
  match h:
    case Eng.Hd{m, v10, fs, cn}:
      v10

def hd.head(h: Eng.Hd) -> Bool:
  match h:
    case Eng.Hd{m, v10, fs, cn}:
      String.eq(m, "HEAD")

# A response as the writer's segments, in order: bytes, or a file by
# the engine's page (its name as the engine reads a path, its type by
# the extension), the handler's fields put in its head, a Shut before it
# when the connection ends after it
def file.shut(closing: Bool, g: L.Seg) -> List<&2, L.Seg>:
  match closing:
    case True{}:
      [L.Shut{}, g]
    case False{}:
      [g]

def file.segs(+head: Bool, +closing: Bool, +v10: Bool, hs: List<&2, Http.Header>, g: L.Seg) -> List<&2, L.Seg>:
  match g:
    case L.Page{root, path, ct, h}:
      file.shut(closing, L.Page{root, path, Http.fhead.pre(ct, hs), h})
    case _:
      [L.Raw{Http.encode.bytes(head, closing, v10, 404, [Http.Header{"content-type", "text/plain; charset=utf-8"}],
        "404 Not Found\n")}]

def segs.of(+head: Bool, +closing: Bool, +v10: Bool, r: Http.Response) -> List<&2, L.Seg>:
  match r:
    case Http.Response{code, hs, b}:
      match b:
        case Http.BBody{bs}:
          [L.Raw{Http.encode.bytes(head, closing, v10, code, hs, bs)}]
        case Http.BFile{root, path}:
          file.segs(head, closing, v10, hs, Eng.page(root, path, head))

# One request: the handler's response, written after what waits; a
# request that closes (it asked to, it is HTTP/1.0 without keep-alive,
# or it asked to upgrade, which this server does not) is the last, and
# a target past 8 KiB is a 414 that closes. The rest of the read's
# requests follow through go.
def one.then(+cfg: Cfg, closing: Bool, out: List<&2, L.Seg>, s: Socket, go: List<&2, L.Seg> -> Socket -> IO(Socket)) ->
  IO(Socket):
  match closing:
    case True{}:
      fin(cfg, out, s)
    case False{}:
      go(out, s)

def one.done(+cfg: Cfg, +head: Bool, +closing: Bool, +v10: Bool, resp: Http.Response, acc: List<&2, L.Seg>,
  s: Socket, go: List<&2, L.Seg> -> Socket -> IO(Socket)) -> IO(Socket):
  one.then(cfg, closing, rev.onto(segs.of(head, closing, v10, resp), acc), s, go)

def one.at(~E: Data, ~app: Hx(E), +cfg: Cfg, +ip: Bytes(), +env: E, +r: Eng.Req, +head: Bool, +v10: Bool, far: Bool,
  acc: List<&2, L.Seg>, s: Socket, go: List<&2, L.Seg> -> Socket -> IO(Socket)) -> IO(Socket):
  match far:
    case True{}:
      fin(cfg, Con{L.Raw{own(head, v10, 414)}, acc}, s)
    case False{}:
      IO.bind(Http.Response, Socket, app(env, Http.req.of(ip, r)),
        resp => one.done(cfg, head, Eng.req.close(r) || Eng.req.ws(r), v10, resp, acc, s, go))

def one(~E: Data, ~app: Hx(E), +cfg: Cfg, +ip: Bytes(), +env: E, +r: Eng.Req, acc: List<&2, L.Seg>, s: Socket,
  go: List<&2, L.Seg> -> Socket -> IO(Socket)) -> IO(Socket):
  match r:
    case Eng.Req{meth, +path, body, close, ws, key, hd}:
      one.at(~E, ~app, cfg, ip, env, r, hd.head(hd), hd.v10(hd), Eng.long(Eng.target.cap(), path), acc, s, go)

# a read's requests, oldest first, each answered in turn
def took(~E: Data, ~app: Hx(E), +cfg: Cfg, +ip: Bytes(), +env: E, ts: List<&2, Eng.Req>, t: X.Tail, fresh: Bool,
  t0: Maybe<&2, Nat>, cont: Bool, acc: List<&2, L.Seg>, s: Socket, more: More()) -> IO(Socket):
  match ts:
    case Nil{}:
      tail(cfg, t, fresh, t0, cont, acc, s, more)
    case Con{+r, rest}:
      one(~E, ~app, cfg, ip, env, r, acc, s, acc2 => s2 => took(~E, ~app, cfg, ip, env, rest, t, True{}, None{}, False{}, acc2, s2, more))

def scanned(~E: Data, ~app: Hx(E), +cfg: Cfg, +ip: Bytes(), +env: E, sd: X.Scanned, t0: Maybe<&2, Nat>, cont: Bool, s: Socket,
  more: More()) -> IO(Socket):
  match sd:
    case X.Scanned{ts, t}:
      took(~E, ~app, cfg, ip, env, ts, t, False{}, t0, cont, Nil{}, s, more)

def got.bytes(~E: Data, ~app: Hx(E), +cfg: Cfg, +ip: Bytes(), +env: E, sc: X.Scan, t0: Maybe<&2, Nat>, cont: Bool, s: Socket,
  empty: Bool, +bs: Bytes(), more: More()) -> IO(Socket):
  match empty:
    case True{}:
      IO.pure(Socket, s)
    case False{}:
      scanned(~E, ~app, cfg, ip, env, X.scan(bs, sc), t0, cont, s, more)

# what a read gave: a failure ends the connection, as does the peer's
# FIN; silence ends it between messages when the idle time is spent or
# a stop was asked, and within a message with a 408; bytes go through
# the scan
def got(~E: Data, ~app: Hx(E), +cfg: Cfg, +ip: Bytes(), +env: E, sc: X.Scan, t0: Maybe<&2, Nat>, cont: Bool, +il: U32,
  g: L.Got(Socket), more: More()) -> IO(Socket):
  (s, r) = g
  match r:
    case Fail{e}:
      IO.pure(Socket, s)
    case Done{m}:
      match m:
        case None{}:
          got.none(cfg, sc, t0, cont, il, s, U32.is_le(il, slice()), more)
        case Some{+bs}:
          got.bytes(~E, ~app, cfg, ip, env, sc, t0, cont, s, String.is_empty(bs), bs, more)

# the most one read takes: as the engine's, so a head's cap is counted
# a read at a time (every head under max_head is read, none past twice it)
def chunk() -> U32:
  16384

def wait.lim(~E: Data, ~app: Hx(E), +cfg: Cfg, +ip: Bytes(), +env: E, +p: Eng.P, +n: Nat, +t: Nat, cont: Bool, +il: U32,
  +now: Nat, +lim: Nat, s: Socket, live: Bool, more: More()) -> IO(Socket):
  match live:
    case True{}:
      IO.bind(L.Got(Socket), Socket,
        TCP.poll_buf(s, chunk(), U32.min(cfg.idle(cfg), U32.from_nat(Nat.sub(lim, now)))),
        g => got(~E, ~app, cfg, ip, env, X.Scan{p, n}, Some{t}, cont, il, g, more))
    case False{}:
      late(cfg, s)

# the message in progress has until its head's time from its start
# while its head is being read, and its body's time once it is
def wait.at(~E: Data, ~app: Hx(E), +cfg: Cfg, +ip: Bytes(), +env: E, sc: X.Scan, +t: Nat, cont: Bool, +il: U32, +now: Nat, s: Socket,
  more: More()) -> IO(Socket):
  match sc:
    case X.Scan{+p, +n}:
      +lim = Nat.add(t, U32.to_nat(Bool.pick(U32, Eng.p.head(p), cfg.head(cfg), cfg.body(cfg))))
      wait.lim(~E, ~app, cfg, ip, env, p, n, t, cont, il, now, lim, s, Nat.is_lt(now, lim), more)

def wait(~E: Data, ~app: Hx(E), +cfg: Cfg, +ip: Bytes(), +env: E, sc: X.Scan, t0: Maybe<&2, Nat>, cont: Bool, +il: U32, s: Socket,
  more: More()) -> IO(Socket):
  match t0:
    case None{}:
      IO.bind(L.Got(Socket), Socket, TCP.poll_buf(s, chunk(), U32.min(il, slice())),
        g => got(~E, ~app, cfg, ip, env, sc, None{}, cont, il, g, more))
    case Some{+t}:
      IO.bind(Nat, Socket, IO.now(), now => wait.at(~E, ~app, cfg, ip, env, sc, t, cont, il, now, s, more))

# one connection: at most k reads
def conn(~E: Data, ~app: Hx(E), +cfg: Cfg, +ip: Bytes(), +env: E, k: Nat, sc: X.Scan, t0: Maybe<&2, Nat>, cont: Bool, il: U32,
  s: Socket) -> IO(Socket):
  match k:
    case 0n:
      IO.pure(Socket, s)
    case 1n+j:
      wait(~E, ~app, cfg, ip, env, sc, t0, cont, il, s,
        s2 => sc2 => t2 => c2 => il2 => conn(~E, ~app, cfg, ip, env, j, sc2, t2, c2, il2, s2))

def go.at(~E: Data, ~app: Hx(E), +cfg: Cfg, +env: E, sa: Socket & String) -> IO(Socket):
  (s, ip) = sa
  conn(~E, ~app, cfg, ip, env, L.conn.fuel(), X.scan.new(), None{}, False{}, cfg.idle(cfg), s)

# what serving needs: the configuration, and the handler's environment
type Srv<-E: Data> is Data:
  Srv{cfg: Cfg, env: E}

def go(~E: Data, ~app: Hx(E), +srv: Srv<E>, s: Socket) -> IO(Socket):
  match srv:
    case Srv{+c, +e}:
      IO.bind(Socket & String, Socket, Peer.addr(s), sa => go.at(~E, ~app, c, e, sa))

# Serving
# =======

# a path's segments: the bytes after its leading '/', cut at every '/'
def segs.at(cut: Bool, +s: Bytes(), +i: Nat, go: Bytes() -> List<&2, Bytes()>) -> List<&2, Bytes()>:
  match cut:
    case True{}:
      Con{String.take(s, i), go(String.drop(s, 1n+i))}
    case False{}:
      [s]

def segs.go(k: Nat, +s: Bytes()) -> List<&2, Bytes()>:
  match k:
    case 0n:
      [s]
    case 1n+j:
      +i = Bytes.find_byte(s, 0n, 47)
      segs.at(Nat.is_lt(i, Bytes.len(s)), s, i, t => segs.go(j, t))

def segs(+p: Bytes()) -> List<&2, Bytes()>:
  +t = Bool.pick(Bytes(), U32.is_eq(Bytes.get(p, 0n), 47), String.drop(p, 1n), p)
  segs.go(Bytes.len(t), t)

def join.go(xs: List<&2, Bytes()>, acc: Bytes()) -> Bytes():
  match xs:
    case Nil{}:
      acc
    case Con{x, t}:
      join.go(t, Bytes.append(Bytes.append(acc, "/"), x))

# A pattern segment is a literal, a :param, or the * that takes the rest.
type Sk is Data:
  SLit{}
  SParam{}
  SStar{}

def join(xs: List<&2, Bytes()>) -> Bytes():
  match xs:
    case Nil{}:
      ""
    case Con{x, t}:
      join.go(t, x)

def seg.kind(+p: Bytes()) -> Sk:
  Bool.pick(Sk, String.eq(p, "*"), SStar{}, Bool.pick(Sk, U32.is_eq(Bytes.get(p, 0n), 58), SParam{}, SLit{}))

def seg.then(ok: Bool, xt: List<&2, Bytes()>, acc: List<&2, Http.Header>,
  go: List<&2, Bytes()> -> List<&2, Http.Header> -> Maybe<&2, List<&2, Http.Header>>) ->
  Maybe<&2, List<&2, Http.Header>>:
  match ok:
    case True{}:
      go(xt, acc)
    case False{}:
      None{}

def seg.on(k: Sk, +p: Bytes(), +x: Bytes(), xt: List<&2, Bytes()>, acc: List<&2, Http.Header>,
  go: List<&2, Bytes()> -> List<&2, Http.Header> -> Maybe<&2, List<&2, Http.Header>>) ->
  Maybe<&2, List<&2, Http.Header>>:
  match k:
    case SParam{}:
      seg.then(Bool.not(String.is_empty(x)), xt,
        List.append(&2, Http.Header, acc, [Http.Header{String.drop(p, 1n), Http.decode(x)}]), go)
    case _:
      seg.then(String.eq(p, x), xt, acc, go)

def seg.step(k: Sk, +p: Bytes(), xs: List<&2, Bytes()>, acc: List<&2, Http.Header>,
  go: List<&2, Bytes()> -> List<&2, Http.Header> -> Maybe<&2, List<&2, Http.Header>>) ->
  Maybe<&2, List<&2, Http.Header>>:
  match k:
    case SStar{}:
      Some{List.append(&2, Http.Header, acc, [Http.Header{"*", join(xs)}])}
    case _:
      match xs:
        case Nil{}:
          None{}
        case Con{+x, xt}:
          seg.on(k, p, x, xt, acc, go)

def seg.end(xs: List<&2, Bytes()>, acc: List<&2, Http.Header>) -> Maybe<&2, List<&2, Http.Header>>:
  match xs:
    case Nil{}:
      Some{acc}
    case Con{x, t}:
      None{}

# the pattern's segments against the path's: the params, when it matches
def seg.match(ps: List<&2, Bytes()>, xs: List<&2, Bytes()>, acc: List<&2, Http.Header>) ->
  Maybe<&2, List<&2, Http.Header>>:
  match ps:
    case Nil{}:
      seg.end(xs, acc)
    case Con{+p, pt}:
      seg.step(seg.kind(p), p, xs, acc, xs2 => acc2 => seg.match(pt, xs2, acc2))

def matches(+pat: Bytes(), xs: List<&2, Bytes()>) -> Maybe<&2, List<&2, Http.Header>>:
  seg.match(segs(pat), xs, Nil{})

# a method among ms
def mem(+m: Bytes(), ms: List<&2, Bytes()>) -> Bool:
  match ms:
    case Nil{}:
      False{}
    case Con{x, t}:
      String.eq(m, x) || mem(m, t)

# ms added to acc, each one not already there, in order
def union.put(has: Bool, +x: Bytes(), acc: List<&2, Bytes()>) -> List<&2, Bytes()>:
  match has:
    case True{}:
      acc
    case False{}:
      List.append(&2, Bytes(), acc, [x])

def union(ms: List<&2, Bytes()>, +acc: List<&2, Bytes()>) -> List<&2, Bytes()>:
  match ms:
    case Nil{}:
      acc
    case Con{+x, t}:
      union(t, union.put(mem(x, acc), x, acc))

# What the router chose: the i-th route with its params, a path some
# routes match but none with the method (with what they allow), or none.
type Pick is Data:
  Hit{i: Nat, params: List<&2, Http.Header>}
  NoMethod{allow: List<&2, Bytes()>}
  NoRoute{}

def pick.end(allow: List<&2, Bytes()>) -> Pick:
  match allow:
    case Nil{}:
      NoRoute{}
    case Con{a, t}:
      NoMethod{Con{a, t}}

def pick.at(m: Maybe<&2, List<&2, Http.Header>>, has: Bool, +i: Nat, +ms: List<&2, Bytes()>,
  +allow: List<&2, Bytes()>, go: List<&2, Bytes()> -> Pick) -> Pick:
  match m:
    case None{}:
      go(allow)
    case Some{ps}:
      match has:
        case True{}:
          Hit{i, ps}
        case False{}:
          go(union(ms, allow))

# one walk: the first route that matches with the method, the allowed
# methods of those that match without it gathered on the way
def pick.go(pats: List<&2, Pat>, +m: Bytes(), +xs: List<&2, Bytes()>, +i: Nat, +allow: List<&2, Bytes()>) -> Pick:
  match pats:
    case Nil{}:
      pick.end(allow)
    case Con{pt, t}:
      match pt:
        case Pat{+ms, +pat}:
          pick.at(matches(pat, xs), mem(m, ms), i, ms, allow, al => pick.go(t, m, xs, 1n+i, al))

def pick(pats: List<&2, Pat>, +m: Bytes(), +path: Bytes()) -> Pick:
  pick.go(pats, m, segs(path), 0n, Nil{})

def unzip.put(p: Pat, h: Http.Request -> IO(Http.Response),
  r: List<&2, Pat> & List<&1, Http.Request -> IO(Http.Response)>) ->
  List<&2, Pat> & List<&1, Http.Request -> IO(Http.Response)>:
  (ps, hs) = r
  (Con{p, ps}, Con{h, hs})

# the routes' patterns, and their handlers in the same order
def unzip(rs: List<&1, Route>) -> List<&2, Pat> & List<&1, Http.Request -> IO(Http.Response)>:
  match rs:
    case Nil{}:
      (Nil{}, Nil{})
    case Con{r, t}:
      match r:
        case Route{ms, pat, h}:
          unzip.put(Pat{ms, pat}, h, unzip(t))

def nth(i: Nat, hs: List<&1, Http.Request -> IO(Http.Response)>) -> Maybe<&1, Http.Request -> IO(Http.Response)>:
  match i hs:
    case _ Nil{}:
      None{}
    case 0n Con{h, t}:
      Some{h}
    case 1n+j Con{h, t}:
      nth(j, t)

def allow.go(ms: List<&2, Bytes()>, acc: Bytes()) -> Bytes():
  match ms:
    case Nil{}:
      acc
    case Con{x, t}:
      allow.go(t, Bytes.append(Bytes.append(acc, ", "), x))

def allow.text(ms: List<&2, Bytes()>) -> Bytes():
  match ms:
    case Nil{}:
      ""
    case Con{x, t}:
      allow.go(t, x)

def run.hit(m: Maybe<&1, Http.Request -> IO(Http.Response)>, r: Http.Request) -> IO(Http.Response):
  match m:
    case Some{h}:
      h(r)
    case None{}:
      Http.reply(Http.plain(500))

def run.pick(pk: Pick, hs: List<&1, Http.Request -> IO(Http.Response)>, r: Http.Request) -> IO(Http.Response):
  match pk:
    case Hit{i, ps}:
      run.hit(nth(i, hs), Http.with.params(r, ps))
    case NoMethod{allow}:
      Http.reply(Http.with.header(Http.plain(405), "allow", allow.text(allow)))
    case NoRoute{}:
      Http.reply(Http.plain(404))

def run.split(pz: List<&2, Pat> & List<&1, Http.Request -> IO(Http.Response)>, +r: Http.Request) -> IO(Http.Response):
  (pats, hs) = pz
  run.pick(pick(pats, Http.method(r), Http.path(r)), hs, r)

# the routes' answer to a request (a handler, given the routes)
def route(rs: List<&1, Route>, r: Http.Request) -> IO(Http.Response):
  run.split(unzip(rs), r)

# Middleware
# ==========
#
# Each is Handler -> Handler as a template: ~logged(~app) is a handler.
# Each is also an *.around form, over the IO a handler returns, for a
# handler that takes an environment (serve.with) and so is no template
# argument: Server.log.around(r, Server.route(routes(db), r)).

def ms.since(+t0: Nat, t1: Nat) -> Bytes():
  Nat.show(Nat.sub(t1, t0))

def logged.line(+r: Http.Request, +resp: Http.Response, +t0: Nat, t1: Nat) -> Bytes():
  Bytes.concat([Http.method(r), " ", Http.path(r), " ", U32.show(Http.status(resp)), " ",
    Nat.show(Bytes.len(Http.resp.body(resp))), " ", ms.since(t0, t1), "ms"])

def log.done(+r: Http.Request, +t0: Nat, +resp: Http.Response) -> IO(Http.Response):
  do IO<Http.Response>:
    t1 : Nat <- IO.now()
    IO.print_err(logged.line(r, resp, t0, t1))
    return resp

# a line per request on stderr: the method, the path, the status, the
# body's length and the time the handler took
def log.around(+r: Http.Request, io: IO(Http.Response)) -> IO(Http.Response):
  do IO<Http.Response>:
    +t0 : Nat <- IO.now()
    +resp : Http.Response <- io
    log.done(r, t0, resp)

def logged(~h: Http.Request -> IO(Http.Response), +r: Http.Request) -> IO(Http.Response):
  log.around(r, h(r))

def recover.at(r: Result<&2, &2, Bytes(), Http.Response>) -> IO(Http.Response):
  match r:
    case Done{resp}:
      Http.reply(resp)
    case Fail{msg}:
      do IO<Http.Response>:
        IO.print_err(Bytes.append("handler failed: ", msg))
        return Http.plain(500)

# a handler that may fail with a message, as a handler: a failure is a
# plain 500 to the client (the message goes to stderr, not to the peer)
def recover.around(io: IO(Result<&2, &2, Bytes(), Http.Response>)) -> IO(Http.Response):
  IO.bind(Result<&2, &2, Bytes(), Http.Response>, Http.Response, io, recover.at)

def recover(~h: Http.Request -> IO(Result<&2, &2, Bytes(), Http.Response>), r: Http.Request) -> IO(Http.Response):
  recover.around(h(r))

def secure.one(r: Http.Response, +n: Bytes(), v: Bytes()) -> Http.Response:
  match r:
    case Http.Response{s, +hs, b}:
      Http.Response{s, Bool.pick(List<&2, Http.Header>, Http.has(hs, n), hs, Http.add(hs, n, v)), b}

def secure.all(r: Http.Response) -> Http.Response:
  secure.one(secure.one(secure.one(secure.one(r, "x-content-type-options", "nosniff"),
    "x-frame-options", "DENY"), "referrer-policy", "no-referrer"),
    "content-security-policy", "default-src 'self'")

# the headers a browser should see, each unless the handler set it:
# nosniff, no framing, no referrer, and a CSP of 'self'
def secure.around(io: IO(Http.Response)) -> IO(Http.Response):
  IO.bind(Http.Response, Http.Response, io, resp => Http.reply(secure.all(resp)))

def secured(~h: Http.Request -> IO(Http.Response), r: Http.Request) -> IO(Http.Response):
  secure.around(h(r))

# The connection
# ==============

def Handler() -> Type:
  Http.Request -> IO(Http.Response)

def srv.grace(~E: Data, s: Srv<E>) -> U32:
  match s:
    case Srv{c, e}:
      cfg.grace(c)

def srv.conns(~E: Data, s: Srv<E>) -> U32:
  match s:
    case Srv{c, e}:
      cfg.conns(c)

def listen.at(plain: Bool, shared: Bool, +cfg: Cfg) -> IO(Result<&1, &1, U32 & String, Listener>):
  match plain shared:
    case False{} _:
      TLS.listen(cfg.port(cfg), cfg.cert(cfg), cfg.key(cfg))
    case True{} True{}:
      TCP.listen_shared(cfg.port(cfg))
    case True{} False{}:
      TCP.listen(cfg.port(cfg))

def listen(+cfg: Cfg) -> IO(Result<&1, &1, U32 & String, Listener>):
  listen.at(String.is_empty(cfg.cert(cfg)), cfg.shared(cfg), cfg)

def banner(+cfg: Cfg) -> String:
  "bend-net: listening on " ++ Bool.pick(String, String.is_empty(cfg.cert(cfg)), "http", "https") ++ "://127.0.0.1:"
    ++ U32.show(cfg.port(cfg))

# serve app with cfg, until SIGTERM; env is handed to every call of
# app (shared state: a channel, a configuration)
def serve.with(~E: Data, ~app: Hx(E), +env: E, +cfg: Cfg) -> IO(Unit):
  do IO<Unit>:
    l : Listener <- IO.try(Listener, listen(cfg))
    IO.print_err(banner(cfg))
    Fx.run(~Srv<E>, ~go(~E, ~app), ~srv.grace(~E), ~srv.conns(~E), "bend-net", Srv{cfg, env}, l)

def unit.app(~app: Handler(), +u: Unit, r: Http.Request) -> IO(Http.Response):
  app(r)

# serve app with cfg, until SIGTERM
def serve(~app: Handler(), +cfg: Cfg) -> IO(Unit):
  serve.with(~Unit, ~unit.app(~app), Unit{}, cfg)
