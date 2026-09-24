# bend-net: request bodies as streams.
#
#   Stream.serve(~app, ~uploads(), Stream.config(Server.config(8080)))
#   Stream.serve.with(~E, ~app, ~uploads, env, cfg)
#
# A server that takes uploads: app answers every request as
# Server.serve's does, its body whole, and uploads() is a table of
# stream routes (Stream.post(pat, h), Stream.put, Stream.on) whose
# handlers get the request's head and its body as a Stream.Body, read a
# chunk at a time, never held whole:
#
#   h : Http.Request -> Stream.Body -> IO(Stream.Body & Http.Response)
#
# A Body is affine, as a Ws.Conn is: Stream.read(b) answers the Body
# beside Some{chunk} (never empty), None at the body's end, or why it
# failed; Stream.to_file(b, path) writes the rest of it to a file and
# answers how many bytes. The handler hands the Body back beside its
# response, and the server takes the connection back from it.
#
# The body is read only as the handler asks: a read is one read of the
# socket (at most chunk(), 64 KiB), so a handler slower than its peer
# stops reading the socket and TCP stops the peer. A body is framed by
# wire/http1's reader entered at the body (a length counted off, or
# chunked), the reader wire/http1/LAWS.bend holds to RFC 9112's framing;
# net/LAWS.bend proves, for every body however TCP cuts it:
#
#   stream_body     the chunks a handler reads, joined, then what the
#                   reader still holds, are the body wire/http1/spec.bend's
#                   walk of RFC 9112 frames
#   stream_bounded  between reads a Body holds the chunk it hands on and
#                   the bytes that came after the body, no more than the
#                   read that brought them; the reader holds no byte of
#                   the body itself, however large the body is
#   stream_next     the connection goes on after a streamed request only
#                   once the body has ended, with exactly the bytes the
#                   framing puts after it: an undrained body's bytes are
#                   never read as the next request
#
# The bounds (Stream.Cfg): a body at most max_stream bytes (1 GiB; a
# length past it is a 413 before a byte of it is read, and a chunked
# body is cut there, and is at most 256 MiB, the reader's budget, kept
# under 2^28 so a chunk's size never wraps); each read of a body within
# progress (10 s) or a 408; the head within the server's head time and
# at most its max_head (408, 431). An Expect: 100-continue is answered
# at the handler's first read of the socket, so a handler that refuses
# without reading never asks for the body. When the handler returns, the
# server drains what is left of the body, up to drain.cap() (1 MiB),
# each read within the progress time, and the connection goes on; past
# that it answers and closes (and when a 100 Continue is still owed, the
# client sends no body: it answers and closes at once). A read that failed (the body refused, too large, too slow)
# is answered by the server itself (400, 413, 408) whatever the handler
# answered, and the connection closes.
#
# Which requests are streamed is decided by the request line, before a
# field is read: at the start of a read with no message in progress (as
# every client but a pipelining one sends), a request line whose method
# and path a stream route matches is read by this file; any other goes
# through the server's own reader. A stream route's request that comes
# pipelined behind another in one read is read by the server's reader,
# whole, under max_body, and handed to its handler as a Body over those
# bytes.
import Base
import ../wire/reader.bend as Wr
import ../wire/loop.bend as L
import ../wire/effects.bend as Fx
import ../wire/http1/resp.bend as R
import ../demos/io_http_engine/main.bend as Eng
import ../demos/io_http_engine/spec.bend as Spec
import ../demos/io_proxy/core.bend as X
import ./http.bend as Http
import ./server.bend as Server

# Configuration
# =============

# the server's configuration, the most body a stream takes, and the
# time each read of a body has to bring a byte
type Cfg is Data:
  Cfg{srv: Server.Cfg, max: U32, prog: U32}

# the defaults: bodies of at most 1 GiB, 10 s a read
def config(c: Server.Cfg) -> Cfg:
  Cfg{c, 1073741824, 10000}

def cfg.srv(c: Cfg) -> Server.Cfg:
  match c:
    case Cfg{s, m, p}:
      s

def cfg.max(c: Cfg) -> U32:
  match c:
    case Cfg{s, m, p}:
      m

def cfg.prog(c: Cfg) -> U32:
  match c:
    case Cfg{s, m, p}:
      p

def set.max_stream(c: Cfg, n: U32) -> Cfg:
  match c:
    case Cfg{s, m, p}:
      Cfg{s, n, p}

def set.progress(c: Cfg, ms: U32) -> Cfg:
  match c:
    case Cfg{s, m, p}:
      Cfg{s, m, ms}

def args.one(+prev: String, +x: String, c: Cfg) -> Cfg:
  match c:
    case Cfg{s, +m, +p}:
      Cfg{s, Bool.pick(U32, String.eq(prev, "--max-stream"), Server.arg.num(x, m), m),
        Bool.pick(U32, String.eq(prev, "--progress-ms"), Server.arg.num(x, p), p)}

def args.go(xs: List<&2, String>, +prev: String, c: Cfg) -> Cfg:
  match xs:
    case Nil{}:
      c
    case Con{+x, t}:
      args.go(t, x, args.one(prev, x, c))

def weak(xs: List<&2, String>) -> List<String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{x, weak(t)}

def args.srv(+ys: List<&2, String>, c: Cfg) -> Cfg:
  match c:
    case Cfg{s, m, p}:
      args.go(ys, "", Cfg{Server.args(weak(ys), s), m, p})

# the command line (IO.args()) over c: the server's flags (Server.args),
# and --max-stream N, --progress-ms N
def args(xs: List<String>, c: Cfg) -> Cfg:
  args.srv(Server.strs(xs), c)

# The body's reader
# =================
#
# What the laws are about: the pure steps every read of a body takes.

# how the head framed the body: a length (none is a length of 0), or
# chunked
type Frame is Data:
  FLen{n: Nat}
  FChunked{}

# the reader's context: no HEAD, and the stream's cap as the budget of a
# chunked body (kept under 2^28 by ask.new)
def ask(+max: U32) -> R.Ask:
  R.ask.new(False{}, max)

def entry.len(n: Nat) -> R.St:
  match n:
    case 0n:
      R.Fin{R.final(R.body.head(), "", False{}), ""}
    case 1n+q:
      R.Bod{R.body.head(), q, ""}

# the reader entered at the body: n bytes to count off (the count of
# the bytes after the next one), or chunked under the budget
def entry(+e: R.Ask, f: Frame) -> R.P:
  match f:
    case FLen{n}:
      R.P{entry.len(n), Nil{}}
    case FChunked{}:
      R.P{R.Chk{R.body.head(), R.ASize0{}, 0, "", R.ask.cap(e)}, Nil{}}

# a read of the body: fed to the reader, and the body bytes it brought
# taken from it
def step(+e: R.Ask, +bs: Bytes(), p: R.P) -> R.P & Bytes():
  R.take(R.feed_buf(e, bs, p))

# a body's reads, each a step, the bytes taken joined after acc
def drain(+e: R.Ask, rs: List<&2, Bytes()>, p: R.P, +acc: Bytes()) -> R.P & Bytes():
  match rs:
    case Nil{}:
      (p, acc)
    case Con{+r, t}:
      Wr.drain.on(R.P, step(e, r, p), acc, q => a => drain(e, t, q, a))

# the bytes after the body, once the reader has seen it end
def rest(p: R.P) -> Bytes():
  match p:
    case R.P{st, out}:
      match st:
        case R.Fin{r, x}:
          x
        case _:
          ""

# a step is kept only when the chunk and the bytes after the body are
# no more than the n bytes the read brought (else the read is refused)
def fits(+p: R.P, +x: Bytes(), +n: Nat) -> Bool:
  Nat.is_le(Nat.add(Bytes.len(x), Bytes.len(rest(p))), n)

def next.of(l: R.Look) -> Maybe<&2, Bytes()>:
  match l:
    case R.Look{i, end}:
      match end:
        case R.Final{r, x}:
          Some{x}
        case _:
          None{}

# what the connection goes on with after a streamed request: the bytes
# after the body, once the reader has seen it end; else nothing, and the
# connection closes
def next(p: R.P) -> Maybe<&2, Bytes()>:
  next.of(R.look(p))

# The Body
# ========

# why a read failed: no byte within the progress time; the framing
# refused the body; the body passed max_stream; the peer closed before
# it ended; the read or a file failed
type Err is Data:
  ETime{}
  EBad{}
  ELarge{}
  EClosed{}
  EIo{code: U32, msg: Bytes()}

def err.show(e: Err) -> Bytes():
  match e:
    case ETime{}:
      "the body stalled"
    case EBad{}:
      "the body is malformed"
    case ELarge{}:
      "the body is too large"
    case EClosed{}:
      "the peer closed before the body ended"
    case EIo{c, m}:
      Bytes.append("i/o error: ", m)

# what a Body knows beside the socket and the reader: the reader's
# context, the progress time, whether a 100 Continue is owed before the
# socket is read, the body bytes handed on and the most allowed, and the
# failure it ended in (every read after it answers the same)
type Lim is Data:
  Lim{e: R.Ask, ms: U32, cont: Bool, got: Nat, max: Nat, fail: Maybe<&2, Err>}

type Body is Type:
  Body{s: Socket, p: R.P, held: Bytes(), lim: Lim}

def Out(A: Data) -> Type:
  Body & Result<&2, &2, Err, A>

def lim.fail(l: Lim) -> Maybe<&2, Err>:
  match l:
    case Lim{e, ms, c, got, max, f}:
      f

def lim.cont(l: Lim) -> Bool:
  match l:
    case Lim{e, ms, c, got, max, f}:
      c

def lim.e(l: Lim) -> R.Ask:
  match l:
    case Lim{e, ms, c, got, max, f}:
      e

def lim.ms(l: Lim) -> U32:
  match l:
    case Lim{e, ms, c, got, max, f}:
      ms

def lim.failed(l: Lim, +x: Err) -> Lim:
  match l:
    case Lim{e, ms, c, got, max, f}:
      Lim{e, ms, False{}, got, max, Some{x}}

def lim.sent(l: Lim) -> Lim:
  match l:
    case Lim{e, ms, c, got, max, f}:
      Lim{e, ms, False{}, got, max, f}

def lim.took(l: Lim, +n: Nat) -> Lim:
  match l:
    case Lim{e, ms, c, got, max, f}:
      Lim{e, ms, c, Nat.add(got, n), max, f}

def lim.over(l: Lim) -> Bool:
  match l:
    case Lim{e, ms, c, got, max, f}:
      Nat.is_lt(max, got)

# the most one read of a body takes
def chunk() -> U32:
  65536

def fuel() -> Nat:
  U32.to_nat(16777216)

def failed(s: Socket, p: R.P, +lim: Lim, +x: Err) -> IO(Out(Maybe<&2, Bytes()>)):
  IO.pure(Out(Maybe<&2, Bytes()>), (Body{s, p, "", lim.failed(lim, x)}, Fail{x}))

# a chunked body the reader refused: for its budget (the same read, fed
# with the budget unspent, is not refused), or for its grammar
def rebudget(p: R.P) -> R.P:
  match p:
    case R.P{st, out}:
      match st:
        case R.Chk{h, at, n, got, left}:
          R.P{R.Chk{h, at, n, got, 268435455}, out}
        case R.Dat{h, more, got, left}:
          R.P{R.Dat{h, more, got, 268435455}, out}
        case _:
          R.P{st, out}

def refused(l: R.Look) -> Bool:
  match l:
    case R.Look{i, end}:
      match end:
        case R.Refused{}:
          True{}
        case _:
          False{}

def refused.why(+e: R.Ask, +bs: Bytes(), p0: R.P) -> Err:
  Bool.pick(Err, refused(R.look(R.feed_buf(e, bs, rebudget(p0)))), EBad{}, ELarge{})

# what a read goes on with when a socket read brought no body byte
def Again() -> Type:
  Socket -> R.P -> Lim -> IO(Out(Maybe<&2, Bytes()>))

def read.took.at(s: Socket, +p0: R.P, +bs: Bytes(), +lim: Lim, p: R.P, +x: Bytes(), +l2: Lim, bad: Bool,
  over: Bool, empty: Bool, again: Again()) -> IO(Out(Maybe<&2, Bytes()>)):
  match bad over empty:
    case True{} _ _:
      failed(s, p, lim, refused.why(lim.e(lim), bs, p0))
    case False{} True{} _:
      failed(s, p, lim, ELarge{})
    case False{} False{} True{}:
      again(s, p, l2)
    case False{} False{} False{}:
      IO.pure(Out(Maybe<&2, Bytes()>), (Body{s, p, "", l2}, Done{Some{x}}))

def read.took(s: Socket, +p0: R.P, +bs: Bytes(), +lim: Lim, +p: R.P, +x: Bytes(), again: Again()) ->
  IO(Out(Maybe<&2, Bytes()>)):
  +l2 = lim.took(lim, Bytes.len(x))
  read.took.at(s, p0, bs, lim, p, x, l2, refused(R.look(p)), lim.over(l2), String.is_empty(x), again)

def read.bytes.at(s: Socket, +p0: R.P, +lim: Lim, +bs: Bytes(), +p: R.P, +x: Bytes(), empty: Bool, ok: Bool,
  again: Again()) -> IO(Out(Maybe<&2, Bytes()>)):
  match empty ok:
    case True{} _:
      failed(s, p0, lim, EClosed{})
    case False{} False{}:
      failed(s, p0, lim, EBad{})
    case False{} True{}:
      read.took(s, p0, bs, lim, p, x, again)

def read.step(s: Socket, +p0: R.P, +lim: Lim, +bs: Bytes(), q: R.P & Bytes(), again: Again()) ->
  IO(Out(Maybe<&2, Bytes()>)):
  (+p, +x) = q
  read.bytes.at(s, p0, lim, bs, p, x, String.is_empty(bs), fits(p, x, Bytes.len(bs)), again)

# a read's bytes, one step of the reader, kept when they fit
# (LAWS.bend's stream_bounded)
def read.bytes(s: Socket, +p: R.P, +lim: Lim, +bs: Bytes(), again: Again()) -> IO(Out(Maybe<&2, Bytes()>)):
  read.step(s, p, lim, bs, step(lim.e(lim), bs, p), again)

def read.got(g: L.Got(Socket), +p: R.P, +lim: Lim, again: Again()) -> IO(Out(Maybe<&2, Bytes()>)):
  (s, r) = g
  match r:
    case Fail{(code, msg)}:
      failed(s, p, lim, EIo{code, msg})
    case Done{m}:
      match m:
        case None{}:
          failed(s, p, lim, ETime{})
        case Some{+bs}:
          read.bytes(s, p, lim, bs, again)

def read.sock(s: Socket, +p: R.P, +lim: Lim, again: Again()) -> IO(Out(Maybe<&2, Bytes()>)):
  IO.bind(L.Got(Socket), Out(Maybe<&2, Bytes()>), TCP.poll_buf(s, chunk(), lim.ms(lim)),
    g => read.got(g, p, lim, again))

def read.sent(m: L.Put(Socket), +p: R.P, +lim: Lim, again: Again()) -> IO(Out(Maybe<&2, Bytes()>)):
  (s, r) = m
  match r:
    case Fail{(code, msg)}:
      failed(s, p, lim, EIo{code, msg})
    case Done{u}:
      read.sock(s, p, lim.sent(lim), again)

# the socket read for more: a 100 Continue first when one is owed
def read.more(s: Socket, +p: R.P, +lim: Lim, cont: Bool, again: Again()) -> IO(Out(Maybe<&2, Bytes()>)):
  match cont:
    case True{}:
      IO.bind(L.Put(Socket), Out(Maybe<&2, Bytes()>),
        TCP.send_buf_poll(s, "HTTP/1.1 100 Continue\r\n\r\n", lim.ms(lim)), m => read.sent(m, p, lim, again))
    case False{}:
      read.sock(s, p, lim, again)

# where the reader is: the body over, refused, or more to read
def read.at(s: Socket, +p: R.P, +lim: Lim, end: R.End, again: Again()) -> IO(Out(Maybe<&2, Bytes()>)):
  match end:
    case R.Final{r, x}:
      IO.pure(Out(Maybe<&2, Bytes()>), (Body{s, p, "", lim}, Done{None{}}))
    case R.Open{}:
      read.more(s, p, lim, lim.cont(lim), again)
    case _:
      failed(s, p, lim, EBad{})

def read.look(s: Socket, +p: R.P, +lim: Lim, l: R.Look, again: Again()) -> IO(Out(Maybe<&2, Bytes()>)):
  match l:
    case R.Look{i, end}:
      read.at(s, p, lim, end, again)

# n bounds the reads that bring no body byte (a chunk's framing alone)
def read.go(n: Nat, s: Socket, +p: R.P, +lim: Lim) -> IO(Out(Maybe<&2, Bytes()>)):
  match n:
    case 0n:
      failed(s, p, lim, EBad{})
    case 1n+j:
      read.look(s, p, lim, R.look(p), s2 => p2 => l2 => read.go(j, s2, p2, l2))

def read.held(s: Socket, +p: R.P, +held: Bytes(), +lim: Lim, f: Maybe<&2, Err>, empty: Bool) ->
  IO(Out(Maybe<&2, Bytes()>)):
  match f empty:
    case Some{x} _:
      IO.pure(Out(Maybe<&2, Bytes()>), (Body{s, p, held, lim}, Fail{x}))
    case None{} False{}:
      IO.pure(Out(Maybe<&2, Bytes()>), (Body{s, p, "", lim}, Done{Some{held}}))
    case None{} True{}:
      read.go(fuel(), s, p, lim)

# The next chunk of the body (never empty), None at its end, or why it
# failed; a read after a failure answers the same failure
def read(b: Body) -> IO(Out(Maybe<&2, Bytes()>)):
  match b:
    case Body{s, +p, +held, +lim}:
      read.held(s, p, held, lim, lim.fail(lim), String.is_empty(held))

# To a file
# =========

def Keep() -> Type:
  Body -> File -> Nat -> IO(Out(Nat))

def file.wrote(b: Body, w: File & Result<&1, &1, U32 & String, Unit>, +n: Nat, again: Keep()) -> IO(Out(Nat)):
  (f, r) = w
  match r:
    case Fail{(code, msg)}:
      IO.bind(Unit, Out(Nat), File.close(f), u => IO.pure(Out(Nat), (b, Fail{EIo{code, msg}})))
    case Done{u}:
      again(b, f, n)

def file.got(f: File, g: Out(Maybe<&2, Bytes()>), +n: Nat, again: Keep()) -> IO(Out(Nat)):
  (b, r) = g
  match r:
    case Fail{x}:
      IO.bind(Unit, Out(Nat), File.close(f), u => IO.pure(Out(Nat), (b, Fail{x})))
    case Done{m}:
      match m:
        case None{}:
          IO.bind(Unit, Out(Nat), File.close(f), u => IO.pure(Out(Nat), (b, Done{n})))
        case Some{+x}:
          IO.bind(File & Result<&1, &1, U32 & String, Unit>, Out(Nat), File.write_buf(f, x),
            w => file.wrote(b, w, Nat.add(n, Bytes.len(x)), again))

def file.go(k: Nat, b: Body, f: File, +n: Nat) -> IO(Out(Nat)):
  match k:
    case 0n:
      IO.bind(Unit, Out(Nat), File.close(f), u => IO.pure(Out(Nat), (b, Fail{EBad{}})))
    case 1n+j:
      IO.bind(Out(Maybe<&2, Bytes()>), Out(Nat), read(b), g => file.got(f, g, n, b2 => f2 => n2 => file.go(j, b2, f2, n2)))

def file.opened(b: Body, r: Result<&1, &1, U32 & String, File>) -> IO(Out(Nat)):
  match r:
    case Fail{(code, msg)}:
      IO.pure(Out(Nat), (b, Fail{EIo{code, msg}}))
    case Done{f}:
      file.go(fuel(), b, f, 0n)

# the rest of the body written to the file at path (made, or emptied),
# a read at a time: how many bytes, or why it stopped
def to_file(b: Body, path: Bytes()) -> IO(Out(Nat)):
  IO.bind(Result<&1, &1, U32 & String, File>, Out(Nat), File.open(path, "w"), r => file.opened(b, r))

# Stream routes
# =============

def Handler() -> Type:
  Http.Request -> Body -> IO(Body & Http.Response)

# the methods a route answers, its pattern (as Server.get's), and the
# handler that takes the body as a stream
type Route is Type:
  Route{methods: List<&2, Bytes()>, pat: Bytes(), h: Handler()}

def on(methods: List<&2, Bytes()>, pat: Bytes(), h: Handler()) -> Route:
  Route{methods, pat, h}

def post(pat: Bytes(), h: Handler()) -> Route:
  Route{["POST"], pat, h}

def put(pat: Bytes(), h: Handler()) -> Route:
  Route{["PUT"], pat, h}

# a table of stream routes, given the environment (serve.with)
def Ux(E: Data) -> Type:
  @+env: E -> List<&1, Route>

def unzip.put(p: Server.Pat, h: Handler(), r: List<&2, Server.Pat> & List<&1, Handler()>) ->
  List<&2, Server.Pat> & List<&1, Handler()>:
  (ps, hs) = r
  (Con{p, ps}, Con{h, hs})

def unzip(rs: List<&1, Route>) -> List<&2, Server.Pat> & List<&1, Handler()>:
  match rs:
    case Nil{}:
      (Nil{}, Nil{})
    case Con{r, t}:
      match r:
        case Route{ms, pat, h}:
          unzip.put(Server.Pat{ms, pat}, h, unzip(t))

def nth(i: Nat, hs: List<&1, Handler()>) -> Maybe<&1, Handler()>:
  match i hs:
    case _ Nil{}:
      None{}
    case 0n Con{h, t}:
      Some{h}
    case 1n+j Con{h, t}:
      nth(j, t)

def hit(pk: Server.Pick) -> Bool:
  match pk:
    case Server.Hit{i, ps}:
      True{}
    case _:
      False{}

# whether a stream route takes the method and the path
def takes(rs: List<&1, Route>, +m: Bytes(), +path: Bytes()) -> Bool:
  hit(Server.pick(Pair.fst(List<&2, Server.Pat>, List<&1, Handler()>, unzip(rs)), m, path))

def run.hit(m: Maybe<&1, Handler()>, r: Http.Request, b: Body) -> IO(Body & Http.Response):
  match m:
    case Some{h}:
      h(r, b)
    case None{}:
      IO.pure(Body & Http.Response, (b, Http.plain(404)))

def run.pick(pk: Server.Pick, hs: List<&1, Handler()>, r: Http.Request, b: Body) -> IO(Body & Http.Response):
  match pk:
    case Server.Hit{i, ps}:
      run.hit(nth(i, hs), Http.with.params(r, ps), b)
    case _:
      IO.pure(Body & Http.Response, (b, Http.plain(404)))

def run.split(pz: List<&2, Server.Pat> & List<&1, Handler()>, +r: Http.Request, b: Body) -> IO(Body & Http.Response):
  (pats, hs) = pz
  run.pick(Server.pick(pats, Http.method(r), Http.path(r)), hs, r, b)

# the stream routes' answer to a request's head and body
def run(rs: List<&1, Route>, r: Http.Request, b: Body) -> IO(Body & Http.Response):
  run.split(unzip(rs), r, b)

# The head of a streamed request
# ==============================
#
# Read whole, through its blank line, and judged a line at a time: the
# request line by the engine's spec.bend view of one (a method, a target
# of at most 8 KiB, HTTP/1.1 or HTTP/1.0), every field line by spec.bend's
# view of it, but a Content-Length, whose digits are read here as a
# number of any size (the engine refuses one past the 1 MiB it holds).
# Refused, as the engine refuses: a line that does not read, lengths
# that disagree, a Transfer-Encoding but chunked, two of them, one beside
# a Content-Length or in HTTP/1.0, and a Host too many or too few.

# what the field lines said: the fields handed on (newest first), the
# length, the Transfer-Encodings and whether each said chunked, the
# Hosts, a Connection's close and keep-alive, 100-continue, and whether
# a line was refused
type Hs is Data:
  Hs{fs: List<&2, Http.Header>, len: Maybe<&2, Nat>, te: Nat, ch: Bool, hosts: Nat, cl: Bool, ka: Bool, co: Bool,
    bad: Bool}

def hs.new() -> Hs:
  Hs{Nil{}, None{}, 0n, True{}, 0n, False{}, False{}, False{}, False{}}

def hs.bad(h: Hs) -> Hs:
  match h:
    case Hs{fs, len, te, ch, ho, cl, ka, co, bad}:
      Hs{fs, len, te, ch, ho, cl, ka, co, True{}}

def hs.pass(h: Hs, +n: Bytes(), +v: Bytes()) -> Hs:
  match h:
    case Hs{fs, len, te, ch, ho, cl, ka, co, bad}:
      Hs{Con{Http.Header{n, v}, fs}, len, te, ch, ho, cl, ka, co, bad}

def hs.host(h: Hs, +n: Bytes(), +v: Bytes()) -> Hs:
  match h:
    case Hs{fs, len, te, ch, ho, cl, ka, co, bad}:
      Hs{Con{Http.Header{n, v}, fs}, len, te, ch, 1n+ho, cl, ka, co, bad}

def hs.expect(h: Hs, +n: Bytes(), +v: Bytes()) -> Hs:
  match h:
    case Hs{fs, len, te, ch, ho, cl, ka, co, bad}:
      Hs{Con{Http.Header{n, v}, fs}, len, te, ch, ho, cl, ka, co || String.eq(Eng.lows(v), "100-continue"), bad}

def hs.te(h: Hs, +v: Bytes()) -> Hs:
  match h:
    case Hs{fs, len, te, ch, ho, cl, ka, co, bad}:
      Hs{fs, len, 1n+te, ch && String.eq(Eng.lows(v), "chunked"), ho, cl, ka, co, bad}

def hs.conn(h: Hs, +ms: List<&2, Bytes()>) -> Hs:
  match h:
    case Hs{fs, len, te, ch, ho, cl, ka, co, bad}:
      Hs{fs, len, te, ch, ho, cl || X.in.names("close", ms), ka || X.in.names("keep-alive", ms), co, bad}

def same.len(len: Maybe<&2, Nat>, +n: Nat) -> Bool:
  match len:
    case None{}:
      True{}
    case Some{m}:
      Nat.is_eq(m, n)

def hs.len.at(h: Hs, +n: Nat) -> Hs:
  match h:
    case Hs{fs, +len, te, ch, ho, cl, ka, co, bad}:
      Hs{fs, Some{n}, te, ch, ho, cl, ka, co, bad || Bool.not(same.len(len, n))}

def hs.len(h: Hs, d: Maybe<&2, Nat>) -> Hs:
  match d:
    case None{}:
      hs.bad(h)
    case Some{+n}:
      hs.len.at(h, n)

def digit.next(+acc: Nat, +c: U32) -> Nat:
  Nat.min(Nat.add(Nat.mul(acc, 10n), U32.to_nat((c - 48 : U32))), 4294967295n)

def num.pick(dg: Bool, next: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match dg:
    case True{}:
      next
    case False{}:
      None{}

def num(b: Bytes(), +acc: Nat) -> Maybe<&2, Nat>:
  match b:
    case SNil{}:
      Some{acc}
    case SCon{Chr{+c}, t}:
      num.pick(R.digit(c), num(t, digit.next(acc, c)))

# a Content-Length's value: digits, at least one
def digits(+v: Bytes()) -> Maybe<&2, Nat>:
  Bool.pick(Maybe<&2, Nat>, String.is_empty(v), None{}, num(v, 0n))

def fline.ok(v: Spec.FLine) -> Bool:
  match v:
    case Spec.FVal{x}:
      True{}
    case _:
      False{}

def field.named(+h: Hs, +n: Bytes(), +v: Bytes()) -> Hs:
  Bool.pick(Hs, String.eq(n, "transfer-encoding"), hs.te(h, v),
  Bool.pick(Hs, String.eq(n, "connection"), hs.conn(h, X.members(v)),
  Bool.pick(Hs, String.eq(n, "upgrade"), h,
  Bool.pick(Hs, String.eq(n, "host"), hs.host(h, n, v),
  Bool.pick(Hs, String.eq(n, "expect"), hs.expect(h, n, v), hs.pass(h, n, v))))))

def field.at(+n: Bytes(), +v: Bytes(), +l: Bytes(), +h: Hs) -> Hs:
  Bool.pick(Hs, String.eq(n, "content-length"), hs.len(h, digits(v)),
    Bool.pick(Hs, fline.ok(Spec.field.view(Bytes.to_list(l))), field.named(h, n, v), hs.bad(h)))

def line.at(f: Maybe<&2, Wr.Field>, +l: Bytes(), +h: Hs) -> Hs:
  match f:
    case None{}:
      hs.bad(h)
    case Some{fl}:
      match fl:
        case Wr.Field{+n, +v}:
          field.at(n, v, l, h)

def lines(ls: List<&2, Bytes()>, h: Hs) -> Hs:
  match ls:
    case Nil{}:
      h
    case Con{+l, t}:
      lines(t, line.at(X.field.of(l), l, h))

# a head judged: the request (no body, no params yet), the body's
# framing, and whether it is HTTP/1.0, closes after, expects
# 100-continue, is a HEAD; or the status it is refused with
type Head is Data:
  HOk{req: Http.Request, f: Frame, v10: Bool, closing: Bool, cont: Bool, head: Bool}
  HNo{code: U32}

def frame.of(+te: Nat, len: Maybe<&2, Nat>) -> Frame:
  match te len:
    case 1n+k _:
      FChunked{}
    case 0n Some{n}:
      FLen{n}
    case 0n None{}:
      FLen{0n}

def hosts.ok(+v10: Bool, +ho: Nat) -> Bool:
  Bool.pick(Bool, v10, Nat.is_le(ho, 1n), Nat.is_eq(ho, 1n))

def judge.req(+m: Bytes(), pq: Bytes() & Bytes(), fs: List<&2, Http.Header>, +ip: Bytes()) -> Http.Request:
  (p, q) = pq
  Http.Request{m, p, q, List.reverse(&2, Http.Header, fs), "", ip, Nil{}}

def judge.hs(+v10: Bool, +m: Bytes(), +t: Bytes(), h: Hs, +ip: Bytes()) -> Head:
  match h:
    case Hs{fs, +len, +te, +ch, +ho, +cl, +ka, +co, +bad}:
      +two = Nat.is_lt(0n, te) && (Maybe.is_some(&2, Nat, len) || v10 || Bool.not(ch) || Nat.is_lt(1n, te))
      Bool.pick(Head, bad || two || Bool.not(hosts.ok(v10, ho)), HNo{400},
        HOk{judge.req(m, Http.target.cut(t), fs, ip), frame.of(te, len), v10, cl || (v10 && Bool.not(ka)), co,
          String.eq(m, "HEAD")})

def judge.go(ok: Bool, far: Bool, +v10: Bool, +m: Bytes(), +t: Bytes(), h: Hs, +ip: Bytes()) -> Head:
  match ok far:
    case False{} _:
      HNo{400}
    case True{} True{}:
      HNo{414}
    case True{} False{}:
      judge.hs(v10, m, t, h, ip)

def judge.ver(+m: Bytes(), +t: Bytes(), +v: Bytes(), h: Hs, +ip: Bytes()) -> Head:
  judge.go(String.eq(v, "HTTP/1.1") || String.eq(v, "HTTP/1.0"), Eng.long(Eng.target.cap(), t), String.eq(v, "HTTP/1.0"),
    m, t, h, ip)

def judge.at(rl: Spec.RLine, h: Hs, +ip: Bytes()) -> Head:
  match rl:
    case Spec.RVer{m, t, v}:
      judge.ver(Bytes.from_list(m), Bytes.from_list(t), Bytes.from_list(v), h, ip)
    case _:
      HNo{400}

# a head, up to (not with) its blank line
def judge.lines(ls: List<&2, Bytes()>, crlf: Bool, +ip: Bytes()) -> Head:
  match ls crlf:
    case _ False{}:
      HNo{400}
    case Nil{} True{}:
      HNo{400}
    case Con{+l0, t} True{}:
      judge.at(Spec.req.view(Bytes.to_list(l0)), lines(t, hs.new()), ip)

# a head's lines: cut at its CR LFs, every CR the start of one (a bare CR
# or LF is refused, as the engine refuses it)
def judge(+hb: Bytes(), +ip: Bytes()) -> Head:
  +ls = X.cut(hb, 13, 2n)
  judge.lines(ls, String.eq(String.join(ls, "\r\n"), hb), ip)

# The connection
# ==============
#
# Server.serve's loop, with one more way in: at the start of a read with
# no message in progress, the request line is read first, and a stream
# route's request is read here -- its head, then its body by the
# handler -- while every other goes through the server's own reader,
# as the same bytes (Server.scan is the proxy's scan, held to the spec
# for any cut of the stream). After a streamed request the connection
# goes on with the bytes after its body (Stream.next), read as the
# start of the next request.

# what the connection goes on with after a streamed request: the socket
# and the bytes that came after the body
def Go() -> Type:
  Socket -> Bytes() -> IO(Socket)

# the server's own answer, closing
def own.fin(+cfg: Cfg, +code: U32, s: Socket) -> IO(Socket):
  Server.fin(cfg.srv(cfg), [L.Raw{Server.own(False{}, False{}, code)}], s)

# more of a head: a read under the head's clock, which began at t
def hd.bytes(empty: Bool, s: Socket, +acc: Bytes(), +bs: Bytes(), k: Go()) -> IO(Socket):
  match empty:
    case True{}:
      IO.pure(Socket, s)
    case False{}:
      k(s, Bytes.append(acc, bs))

def hd.got(g: L.Got(Socket), +cfg: Cfg, +acc: Bytes(), k: Go()) -> IO(Socket):
  (s, r) = g
  match r:
    case Fail{e}:
      IO.pure(Socket, s)
    case Done{m}:
      match m:
        case None{}:
          Server.late(cfg.srv(cfg), s)
        case Some{+bs}:
          hd.bytes(String.is_empty(bs), s, acc, bs, k)

def hd.wait(+cfg: Cfg, +acc: Bytes(), +lim: Nat, +now: Nat, s: Socket, k: Go(), live: Bool) -> IO(Socket):
  match live:
    case True{}:
      IO.bind(L.Got(Socket), Socket, TCP.poll_buf(s, Server.chunk(), U32.from_nat(Nat.sub(lim, now))),
        g => hd.got(g, cfg, acc, k))
    case False{}:
      Server.late(cfg.srv(cfg), s)

def hd.more(+cfg: Cfg, +acc: Bytes(), +t: Nat, s: Socket, k: Go()) -> IO(Socket):
  +lim = Nat.add(t, U32.to_nat(Server.cfg.head(cfg.srv(cfg))))
  IO.bind(Nat, Socket, IO.now(), +now => hd.wait(cfg, acc, lim, now, s, k, Nat.is_lt(now, lim)))

# Draining
# --------
#
# What a handler left of the body is read and dropped, up to n bytes:
# the connection goes on only when the body then ended.

def drain.at(b: Body, over: Bool, +n: Nat, again: Body -> Nat -> IO(Body)) -> IO(Body):
  match over:
    case True{}:
      IO.pure(Body, b)
    case False{}:
      again(b, n)

def drain.got(g: Out(Maybe<&2, Bytes()>), +n: Nat, again: Body -> Nat -> IO(Body)) -> IO(Body):
  (b, r) = g
  match r:
    case Fail{x}:
      IO.pure(Body, b)
    case Done{m}:
      match m:
        case None{}:
          IO.pure(Body, b)
        case Some{+x}:
          drain.at(b, Nat.is_lt(n, Bytes.len(x)), Nat.sub(n, Bytes.len(x)), again)

def drain.go(k: Nat, b: Body, +n: Nat) -> IO(Body):
  match k:
    case 0n:
      IO.pure(Body, b)
    case 1n+j:
      IO.bind(Out(Maybe<&2, Bytes()>), Body, read(b), g => drain.got(g, n, b2 => n2 => drain.go(j, b2, n2)))

# the most of a body the server drains after its handler: past it, it
# answers and closes
def drain.cap() -> Nat:
  U32.to_nat(1048576)

# After the handler
# -----------------

# the handler's response: then the connection goes on with the bytes
# after the body when the body ended and the request did not close it;
# else it closes
def after.send(+cfg: Cfg, +head: Bool, closing: Bool, +v10: Bool, resp: Http.Response, s: Socket, +rest: Bytes(),
  nx: Go()) -> IO(Socket):
  match closing:
    case True{}:
      Server.fin(cfg.srv(cfg), Server.rev.onto(Server.segs.of(head, True{}, v10, resp), Nil{}), s)
    case False{}:
      IO.bind(Socket & Bool, Socket,
        Server.flush.segs(s, Server.segs.of(head, False{}, v10, resp), Server.cfg.send(cfg.srv(cfg))),
        sb => Server.next(sb, s2 => nx(s2, rest)))

def after.end(+cfg: Cfg, +head: Bool, +closing: Bool, +v10: Bool, resp: Http.Response, s: Socket,
  m: Maybe<&2, Bytes()>, nx: Go()) -> IO(Socket):
  match m:
    case Some{+rest}:
      after.send(cfg, head, closing, v10, resp, s, rest, nx)
    case None{}:
      Server.fin(cfg.srv(cfg), Server.rev.onto(Server.segs.of(head, True{}, v10, resp), Nil{}), s)

def after.go(+cfg: Cfg, +head: Bool, +closing: Bool, +v10: Bool, resp: Http.Response, b: Body, nx: Go()) -> IO(Socket):
  match b:
    case Body{s, +p, held, lim}:
      after.end(cfg, head, closing, v10, resp, s, next(p), nx)

# a body the handler left: drained unless its end is already read, or a
# 100 Continue is still owed (the client then sends no body: the
# connection closes after the response)
def after.drain(+cfg: Cfg, +head: Bool, +closing: Bool, +v10: Bool, resp: Http.Response, b: Body, owed: Bool,
  ended: Bool, nx: Go()) -> IO(Socket):
  match owed ended:
    case _ True{}:
      after.go(cfg, head, closing, v10, resp, b, nx)
    case True{} False{}:
      after.go(cfg, head, closing, v10, resp, b, nx)
    case False{} False{}:
      IO.bind(Body, Socket, drain.go(fuel(), b, drain.cap()), b2 => after.go(cfg, head, closing, v10, resp, b2, nx))

# a read that failed is answered by the server, whatever the handler
# said, and the connection ends: 408 slow, 400 malformed, 413 too large;
# a peer gone or a failed read, nothing
def after.err(+cfg: Cfg, x: Err, s: Socket) -> IO(Socket):
  match x:
    case ETime{}:
      own.fin(cfg, 408, s)
    case EBad{}:
      own.fin(cfg, 400, s)
    case ELarge{}:
      own.fin(cfg, 413, s)
    case _:
      IO.pure(Socket, s)

def after.fail(+cfg: Cfg, +head: Bool, +closing: Bool, +v10: Bool, resp: Http.Response, s: Socket, +p: R.P,
  held: Bytes(), +lim: Lim, f: Maybe<&2, Err>, nx: Go()) -> IO(Socket):
  match f:
    case Some{x}:
      after.err(cfg, x, s)
    case None{}:
      after.drain(cfg, head, closing, v10, resp, Body{s, p, held, lim}, lim.cont(lim), Maybe.is_some(&2, Bytes(), next(p)),
        nx)

def after(+cfg: Cfg, +head: Bool, +closing: Bool, +v10: Bool, bo: Body & Http.Response, nx: Go()) -> IO(Socket):
  (b, resp) = bo
  match b:
    case Body{s, +p, held, +lim}:
      after.fail(cfg, head, closing, v10, resp, s, p, held, lim, lim.fail(lim), nx)

# The stream
# ----------

def too.big(f: Frame, +max: U32) -> Bool:
  match f:
    case FLen{n}:
      Nat.is_lt(U32.to_nat(max), n)
    case FChunked{}:
      False{}

def lim.check(+l: Lim) -> Lim:
  Bool.pick(Lim, lim.over(l), lim.failed(l, ELarge{}), l)

def lim.new(+cfg: Cfg, +e: R.Ask, +cont: Bool, +got: Nat, f0: Maybe<&2, Err>) -> Lim:
  lim.check(Lim{e, cfg.prog(cfg), cont, got, U32.to_nat(cfg.max(cfg)), f0})

# the first read refused: for the budget, or the grammar
def first.fail(+e: R.Ask, +rest: Bytes(), +p0: R.P, bad: Bool) -> Maybe<&2, Err>:
  match bad:
    case True{}:
      Some{refused.why(e, rest, p0)}
    case False{}:
      None{}

def begin.body(~E: Data, ~ups: Ux(E), +cfg: Cfg, +env: E, +req: Http.Request, +v10: Bool, +closing: Bool, +head: Bool,
  +e: R.Ask, +cont: Bool, ok: Bool, +p: R.P, +x: Bytes(), f0: Maybe<&2, Err>, s: Socket, nx: Go()) -> IO(Socket):
  match ok:
    case False{}:
      own.fin(cfg, 400, s)
    case True{}:
      IO.bind(Body & Http.Response, Socket, run(ups(env), req, Body{s, p, x, lim.new(cfg, e, cont, Bytes.len(x), f0)}),
        bo => after(cfg, head, closing, v10, bo, nx))

def begin.step(~E: Data, ~ups: Ux(E), +cfg: Cfg, +env: E, +req: Http.Request, +v10: Bool, +closing: Bool, +head: Bool,
  +e: R.Ask, +cont: Bool, +rest: Bytes(), +p0: R.P, q: R.P & Bytes(), s: Socket, nx: Go()) -> IO(Socket):
  (+p, +x) = q
  begin.body(~E, ~ups, cfg, env, req, v10, closing, head, e, cont && String.is_empty(rest), fits(p, x, Bytes.len(rest)),
    p, x, first.fail(e, rest, p0, refused(R.look(p))), s, nx)

# a body announced past max_stream is a 413 before a byte of it is read;
# else the bytes after the head are the body's first read, and the
# handler is run on the request and the Body
def begin.at(~E: Data, ~ups: Ux(E), +cfg: Cfg, +env: E, +req: Http.Request, +f: Frame, +v10: Bool, +closing: Bool,
  +cont: Bool, +head: Bool, +rest: Bytes(), s: Socket, nx: Go(), big: Bool) -> IO(Socket):
  match big:
    case True{}:
      own.fin(cfg, 413, s)
    case False{}:
      +e = ask(cfg.max(cfg))
      begin.step(~E, ~ups, cfg, env, req, v10, closing, head, e, cont, rest, entry(e, f), step(e, rest, entry(e, f)), s, nx)

def begin(~E: Data, ~ups: Ux(E), +cfg: Cfg, +env: E, hd: Head, +rest: Bytes(), s: Socket, nx: Go()) -> IO(Socket):
  match hd:
    case HNo{code}:
      own.fin(cfg, code, s)
    case HOk{+req, +f, +v10, +closing, +cont, +head}:
      begin.at(~E, ~ups, cfg, env, req, f, v10, closing, cont, head, rest, s, nx, too.big(f, cfg.max(cfg)))

def need.big(+cfg: Cfg, big: Bool, +acc: Bytes(), +t: Nat, s: Socket, k: Go()) -> IO(Socket):
  match big:
    case True{}:
      own.fin(cfg, 431, s)
    case False{}:
      hd.more(cfg, acc, t, s, k)

# a stream route's head, read to its blank line (at most max_head)
def need(~E: Data, ~ups: Ux(E), +cfg: Cfg, +ip: Bytes(), +env: E, +t: Nat, k: Nat, fnd: Maybe<&2, Nat>, +acc: Bytes(),
  s: Socket, nx: Go()) -> IO(Socket):
  match k fnd:
    case _ Some{+i}:
      begin(~E, ~ups, cfg, env, judge(String.take(acc, i), ip), String.drop(acc, Nat.add(i, 4n)), s, nx)
    case 0n None{}:
      IO.pure(Socket, s)
    case 1n+j None{}:
      need.big(cfg, Nat.is_lt(U32.to_nat(Server.cfg.max_head(cfg.srv(cfg))), Bytes.len(acc)), acc, t, s,
        s2 => +a2 => need(~E, ~ups, cfg, ip, env, t, j, Bytes.find(a2, "\r\n\r\n"), a2, s2, nx))

# The server's own reader
# -----------------------
#
# Server.serve's, but for a stream route's request it framed whole
# (pipelined behind another in one read), run by the stream route with
# a Body over the body it holds.

def req.bare(r: Http.Request) -> Http.Request:
  match r:
    case Http.Request{m, p, q, hs, b, ip, ps}:
      Http.Request{m, p, q, hs, "", ip, ps}

def mem.body(+cfg: Cfg, s: Socket, +body: Bytes()) -> Body:
  Body{s, R.P{entry.len(0n), Nil{}}, body, Lim{ask(cfg.max(cfg)), cfg.prog(cfg), False{}, Bytes.len(body),
    U32.to_nat(cfg.max(cfg)), None{}}}

def mem.done(+cfg: Cfg, +head: Bool, +closing: Bool, +v10: Bool, bo: Body & Http.Response, acc: List<&2, L.Seg>,
  go: List<&2, L.Seg> -> Socket -> IO(Socket)) -> IO(Socket):
  (b, resp) = bo
  match b:
    case Body{s, p, held, lim}:
      Server.one.done(cfg.srv(cfg), head, closing, v10, resp, acc, s, go)

def one.run(~E: Data, ~app: Server.Hx(E), ~ups: Ux(E), +cfg: Cfg, +env: E, +req: Http.Request, +head: Bool,
  +closing: Bool, +v10: Bool, hit: Bool, acc: List<&2, L.Seg>, s: Socket,
  go: List<&2, L.Seg> -> Socket -> IO(Socket)) -> IO(Socket):
  match hit:
    case True{}:
      IO.bind(Body & Http.Response, Socket, run(ups(env), req.bare(req), mem.body(cfg, s, Http.body(req))),
        bo => mem.done(cfg, head, closing, v10, bo, acc, go))
    case False{}:
      IO.bind(Http.Response, Socket, app(env, req),
        resp => Server.one.done(cfg.srv(cfg), head, closing, v10, resp, acc, s, go))

def one.at(~E: Data, ~app: Server.Hx(E), ~ups: Ux(E), +cfg: Cfg, +ip: Bytes(), +env: E, +r: Eng.Req, +head: Bool,
  +v10: Bool, far: Bool, acc: List<&2, L.Seg>, s: Socket, go: List<&2, L.Seg> -> Socket -> IO(Socket)) -> IO(Socket):
  match far:
    case True{}:
      Server.fin(cfg.srv(cfg), Con{L.Raw{Server.own(head, v10, 414)}, acc}, s)
    case False{}:
      +req = Http.req.of(ip, r)
      one.run(~E, ~app, ~ups, cfg, env, req, head, Eng.req.close(r) || Eng.req.ws(r), v10,
        takes(ups(env), Http.method(req), Http.path(req)), acc, s, go)

def one(~E: Data, ~app: Server.Hx(E), ~ups: Ux(E), +cfg: Cfg, +ip: Bytes(), +env: E, +r: Eng.Req,
  acc: List<&2, L.Seg>, s: Socket, go: List<&2, L.Seg> -> Socket -> IO(Socket)) -> IO(Socket):
  match r:
    case Eng.Req{meth, +path, body, close, ws, key, hd}:
      one.at(~E, ~app, ~ups, cfg, ip, env, r, Server.hd.head(hd), Server.hd.v10(hd), Eng.long(Eng.target.cap(), path),
        acc, s, go)

def took(~E: Data, ~app: Server.Hx(E), ~ups: Ux(E), +cfg: Cfg, +ip: Bytes(), +env: E, ts: List<&2, Eng.Req>,
  t: X.Tail, fresh: Bool, t0: Maybe<&2, Nat>, cont: Bool, acc: List<&2, L.Seg>, s: Socket, more: Server.More()) ->
  IO(Socket):
  match ts:
    case Nil{}:
      Server.tail(cfg.srv(cfg), t, fresh, t0, cont, acc, s, more)
    case Con{+r, rest}:
      one(~E, ~app, ~ups, cfg, ip, env, r, acc, s,
        acc2 => s2 => took(~E, ~app, ~ups, cfg, ip, env, rest, t, True{}, None{}, False{}, acc2, s2, more))

def scanned(~E: Data, ~app: Server.Hx(E), ~ups: Ux(E), +cfg: Cfg, +ip: Bytes(), +env: E, sd: X.Scanned,
  t0: Maybe<&2, Nat>, cont: Bool, s: Socket, more: Server.More()) -> IO(Socket):
  match sd:
    case X.Scanned{ts, t}:
      took(~E, ~app, ~ups, cfg, ip, env, ts, t, False{}, t0, cont, Nil{}, s, more)

# The request line
# ----------------

def rl.meth(+line: Bytes()) -> Bytes():
  String.take(line, Bytes.find_byte(line, 0n, 32))

def rl.target(+line: Bytes()) -> Bytes():
  +t = String.drop(line, 1n+Bytes.find_byte(line, 0n, 32))
  String.take(t, Bytes.find_byte(t, 0n, 32))

def rl.path(+line: Bytes()) -> Bytes():
  +t = rl.target(line)
  String.take(t, Bytes.find_byte(t, 0n, 63))

# a request line past the longest the server reads is its to refuse
def rl.long(+acc: Bytes()) -> Bool:
  Nat.is_lt(Nat.add(Eng.target.cap(), 64n), Bytes.len(acc))

# no message in progress: the reader is before a request line
def fresh(sc: X.Scan) -> Bool:
  match sc:
    case X.Scan{p, n}:
      match p:
        case Eng.P{st, pd, out}:
          match st:
            case Eng.Pre{}:
              True{}
            case _:
              False{}

def bound.pick(~E: Data, ~app: Server.Hx(E), ~ups: Ux(E), +cfg: Cfg, +ip: Bytes(), +env: E, hit: Bool, +acc: Bytes(),
  t0: Maybe<&2, Nat>, +t: Nat, s: Socket, more: Server.More(), nx: Go()) -> IO(Socket):
  match hit:
    case True{}:
      need(~E, ~ups, cfg, ip, env, t, fuel(), Bytes.find(acc, "\r\n\r\n"), acc, s, nx)
    case False{}:
      scanned(~E, ~app, ~ups, cfg, ip, env, Server.scan(acc, X.scan.new()), t0, False{}, s, more)

# a read that begins a message: its request line, once it has come,
# says whose the request is
def bound(~E: Data, ~app: Server.Hx(E), ~ups: Ux(E), +cfg: Cfg, +ip: Bytes(), +env: E, +t: Nat, k: Nat,
  fnd: Maybe<&2, Nat>, lng: Bool, +acc: Bytes(), t0: Maybe<&2, Nat>, s: Socket, more: Server.More(), nx: Go()) ->
  IO(Socket):
  match k fnd lng:
    case _ Some{+i} _:
      +line = String.take(acc, i)
      bound.pick(~E, ~app, ~ups, cfg, ip, env, takes(ups(env), rl.meth(line), rl.path(line)), acc, t0, t, s, more, nx)
    case _ None{} True{}:
      scanned(~E, ~app, ~ups, cfg, ip, env, Server.scan(acc, X.scan.new()), t0, False{}, s, more)
    case 0n None{} False{}:
      IO.pure(Socket, s)
    case 1n+j None{} False{}:
      hd.more(cfg, acc, t, s, s2 => +a2 => bound(~E, ~app, ~ups, cfg, ip, env, t, j, Bytes.find(a2, "\r\n"), rl.long(a2), a2,
        Some{t}, s2, more, nx))

# The loop
# --------

def on.read(~E: Data, ~app: Server.Hx(E), ~ups: Ux(E), +cfg: Cfg, +ip: Bytes(), +env: E, at: Bool, sc: X.Scan,
  t0: Maybe<&2, Nat>, cont: Bool, s: Socket, +bs: Bytes(), more: Server.More(), nx: Go()) -> IO(Socket):
  match at:
    case True{}:
      IO.bind(Nat, Socket, IO.now(), +now => bound(~E, ~app, ~ups, cfg, ip, env, now, fuel(), Bytes.find(bs, "\r\n"),
        rl.long(bs), bs, t0, s, more, nx))
    case False{}:
      scanned(~E, ~app, ~ups, cfg, ip, env, Server.scan(bs, sc), t0, cont, s, more)

def got.bytes(~E: Data, ~app: Server.Hx(E), ~ups: Ux(E), +cfg: Cfg, +ip: Bytes(), +env: E, +sc: X.Scan,
  t0: Maybe<&2, Nat>, cont: Bool, s: Socket, empty: Bool, +bs: Bytes(), more: Server.More(), nx: Go()) -> IO(Socket):
  match empty:
    case True{}:
      IO.pure(Socket, s)
    case False{}:
      on.read(~E, ~app, ~ups, cfg, ip, env, fresh(sc), sc, t0, cont, s, bs, more, nx)

def got(~E: Data, ~app: Server.Hx(E), ~ups: Ux(E), +cfg: Cfg, +ip: Bytes(), +env: E, sc: X.Scan, t0: Maybe<&2, Nat>,
  cont: Bool, +il: U32, g: L.Got(Socket), more: Server.More(), nx: Go()) -> IO(Socket):
  (s, r) = g
  match r:
    case Fail{e}:
      IO.pure(Socket, s)
    case Done{m}:
      match m:
        case None{}:
          Server.got.none(cfg.srv(cfg), sc, t0, cont, il, s, U32.is_le(il, Server.slice()), more)
        case Some{+bs}:
          got.bytes(~E, ~app, ~ups, cfg, ip, env, sc, t0, cont, s, String.is_empty(bs), bs, more, nx)

def wait.lim(~E: Data, ~app: Server.Hx(E), ~ups: Ux(E), +cfg: Cfg, +ip: Bytes(), +env: E, +p: Eng.P, +n: Nat, +t: Nat,
  cont: Bool, +il: U32, +now: Nat, +lim: Nat, s: Socket, live: Bool, more: Server.More(), nx: Go()) -> IO(Socket):
  match live:
    case True{}:
      IO.bind(L.Got(Socket), Socket,
        TCP.poll_buf(s, Server.chunk(), U32.min(Server.cfg.idle(cfg.srv(cfg)), U32.from_nat(Nat.sub(lim, now)))),
        g => got(~E, ~app, ~ups, cfg, ip, env, X.Scan{p, n}, Some{t}, cont, il, g, more, nx))
    case False{}:
      Server.late(cfg.srv(cfg), s)

def wait.at(~E: Data, ~app: Server.Hx(E), ~ups: Ux(E), +cfg: Cfg, +ip: Bytes(), +env: E, sc: X.Scan, +t: Nat,
  cont: Bool, +il: U32, +now: Nat, s: Socket, more: Server.More(), nx: Go()) -> IO(Socket):
  match sc:
    case X.Scan{+p, +n}:
      +c = cfg.srv(cfg)
      +lim = Nat.add(t, U32.to_nat(Bool.pick(U32, Eng.p.head(p), Server.cfg.head(c), Server.cfg.body(c))))
      wait.lim(~E, ~app, ~ups, cfg, ip, env, p, n, t, cont, il, now, lim, s, Nat.is_lt(now, lim), more, nx)

def wait(~E: Data, ~app: Server.Hx(E), ~ups: Ux(E), +cfg: Cfg, +ip: Bytes(), +env: E, sc: X.Scan, t0: Maybe<&2, Nat>,
  cont: Bool, +il: U32, s: Socket, more: Server.More(), nx: Go()) -> IO(Socket):
  match t0:
    case None{}:
      IO.bind(L.Got(Socket), Socket, TCP.poll_buf(s, Server.chunk(), U32.min(il, Server.slice())),
        g => got(~E, ~app, ~ups, cfg, ip, env, sc, None{}, cont, il, g, more, nx))
    case Some{+t}:
      IO.bind(Nat, Socket, IO.now(), now => wait.at(~E, ~app, ~ups, cfg, ip, env, sc, t, cont, il, now, s, more, nx))

def conn.at(~E: Data, ~app: Server.Hx(E), ~ups: Ux(E), +cfg: Cfg, +ip: Bytes(), +env: E, empty: Bool, +pend: Bytes(),
  sc: X.Scan, t0: Maybe<&2, Nat>, cont: Bool, il: U32, s: Socket, more: Server.More(), nx: Go()) -> IO(Socket):
  match empty:
    case True{}:
      wait(~E, ~app, ~ups, cfg, ip, env, sc, t0, cont, il, s, more, nx)
    case False{}:
      got.bytes(~E, ~app, ~ups, cfg, ip, env, sc, t0, cont, s, False{}, pend, more, nx)

# one connection: at most k reads; pend, the bytes after a streamed
# body, read before the socket is
def conn(~E: Data, ~app: Server.Hx(E), ~ups: Ux(E), +cfg: Cfg, +ip: Bytes(), +env: E, k: Nat, +pend: Bytes(),
  sc: X.Scan, t0: Maybe<&2, Nat>, cont: Bool, il: U32, s: Socket) -> IO(Socket):
  match k:
    case 0n:
      IO.pure(Socket, s)
    case 1n+(+j):
      conn.at(~E, ~app, ~ups, cfg, ip, env, String.is_empty(pend), pend, sc, t0, cont, il, s,
        s2 => sc2 => t2 => c2 => il2 => conn(~E, ~app, ~ups, cfg, ip, env, j, "", sc2, t2, c2, il2, s2),
        s2 => rest => conn(~E, ~app, ~ups, cfg, ip, env, j, rest, X.scan.new(), None{}, False{},
          Server.cfg.idle(cfg.srv(cfg)), s2))

def conn.go(~E: Data, ~app: Server.Hx(E), ~ups: Ux(E), +cfg: Cfg, +env: E, sa: Socket & String) -> IO(Socket):
  (s, ip) = sa
  conn(~E, ~app, ~ups, cfg, ip, env, L.conn.fuel(), "", X.scan.new(), None{}, False{}, Server.cfg.idle(cfg.srv(cfg)), s)

# what serving needs: the configuration, and the handlers' environment
type Srv<-E: Data> is Data:
  Srv{cfg: Cfg, env: E}

def serve.conn(~E: Data, ~app: Server.Hx(E), ~ups: Ux(E), +srv: Srv<E>, s: Socket) -> IO(Socket):
  match srv:
    case Srv{+c, +e}:
      IO.bind(Socket & String, Socket, Server.Peer.addr(s), sa => conn.go(~E, ~app, ~ups, c, e, sa))

def srv.grace(~E: Data, s: Srv<E>) -> U32:
  match s:
    case Srv{c, e}:
      Server.cfg.grace(cfg.srv(c))

def srv.conns(~E: Data, s: Srv<E>) -> U32:
  match s:
    case Srv{c, e}:
      Server.cfg.conns(cfg.srv(c))

# Serving
# =======

# serve app, and the stream routes ups(env), with cfg until SIGTERM; env
# is handed to every call of both (shared state: a channel, a
# configuration)
def serve.with(~E: Data, ~app: Server.Hx(E), ~ups: Ux(E), +env: E, +cfg: Cfg) -> IO(Unit):
  +c = cfg.srv(cfg)
  do IO<Unit>:
    l : Listener <- IO.bind(Result<&1, &1, U32 & String, Listener>, Listener, Server.listen(c), r => Server.listened(c, r))
    IO.print_err(Server.banner(c))
    Fx.run(~Srv<E>, ~serve.conn(~E, ~app, ~ups), ~srv.grace(~E), ~srv.conns(~E), "bend-net", Srv{cfg, env}, l)

def unit.ups(~ups: List<&1, Route>, +u: Unit) -> List<&1, Route>:
  ups

# serve app, and the stream routes ups, with cfg until SIGTERM
def serve(~app: Server.Handler(), ~ups: List<&1, Route>, +cfg: Cfg) -> IO(Unit):
  serve.with(~Unit, ~Server.unit.app(~app), ~unit.ups(~ups), Unit{}, cfg)
