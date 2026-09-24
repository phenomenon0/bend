# bend-net: bodies as streams -- a request's read as it comes, and a
# response's written as it is made (the second half of this file).
#
#   Stream.serve(~app, ~uploads(), Stream.config(Server.config(8080)))
#   Stream.serve.with(~E, ~app, ~uploads, env, cfg)
#   Server.serve.routes(~E, ~rs, env, cfg), rs(env) with Stream.get(pat, h)
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
# and the head is the one RFC 9112 reads:
#
#   stream_head     a stream route's head is read by the engine's reader,
#                   the server's own, and what the stream takes from it
#                   at the blank line is the head spec.bend's frame()
#                   holds there, judged as the RFC judges it, however the
#                   stream was cut and whatever came before it
#
# Every request, streamed or not, goes through the one reader: a read is
# fed to it a piece at a time (Where a read stops, below), and when it
# stands at the blank line of a head a stream route takes, the read stops
# there, the requests before it are answered as Server.serve answers
# them, and the stream takes the rest. The head is the engine's; its
# body cap (the server's max_body) is left to the requests it reads
# whole, and a stream's body has the stream's.
#
# The bounds (Stream.Cfg): a body at most max_stream bytes (1 GiB; a
# length past it is a 413 before a byte of it is read -- one past
# 4294967289, more than the reader reads a length as, a 400 -- and a chunked
# body is cut there, and is at most 256 MiB, the reader's budget, kept
# under 2^28 so a chunk's size never wraps); each read of a body within
# progress (10 s) or a 408; the head within the server's head time and
# at most its max_head (408, 431), as every head. An Expect:
# 100-continue is answered at the handler's first read of the socket, so
# a handler that refuses without reading never asks for the body. When
# the handler returns, the server drains what is left of the body, up to
# drain.cap() (1 MiB), each read within the progress time, and the
# connection goes on; past that it answers and closes (and when a 100
# Continue is still owed, the client sends no body: it answers and
# closes at once). A read that failed (the body refused, too large, too
# slow) is answered by the server itself (400, 413, 408) whatever the
# handler answered, and the connection closes.
import Base
import ../wire/reader.bend as Wr
import ../wire/loop.bend as L
import ../wire/effects.bend as Fx
import ../wire/http1/resp.bend as R
import ../wire/http1/spec.bend as RS
import ../demos/io_http_engine/main.bend as Eng
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
# it ended; the read or a file failed. And why a write did (a response
# body, below): a send made no progress within the send time; the
# response could not be written as it was (the 500 went); a write past
# the length it declared; the peer is gone; the response has no body (a
# HEAD, a 204, a 304)
type Err is Data:
  ETime{}
  EBad{}
  ELarge{}
  EClosed{}
  EIo{code: U32, msg: Bytes()}
  ENone{}

def err.show(e: Err) -> Bytes():
  match e:
    case ETime{}:
      "the peer stalled"
    case EBad{}:
      "the body is malformed"
    case ELarge{}:
      "the body is too large"
    case EClosed{}:
      "the peer closed the connection"
    case EIo{c, m}:
      Bytes.append("i/o error: ", m)
    case ENone{}:
      "the response has no body"

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
# Read by the engine's reader, the one every request the server takes is
# read by (net/LAWS.bend's handler_framed, the engine's frame_sim): a
# stream route's head is the head that reader holds when it stands at
# the CR of the blank line (Eng.CrL), and its framing the engine's own
# decision there (Eng.head.frame), before the engine's body cap: the
# decision step.head applies body.fit to. Nothing here reads a byte of a
# head: net/LAWS.bend's stream_head says the view below is the one
# spec.bend's frame() reaches at the same byte, for every stream however
# cut.

# a stream route's head: the request as the server hands one on (its
# body empty), how its body is framed, and whether it is HTTP/1.0,
# closes after, is a HEAD; or refused, as the engine refuses it (a Host
# too many or too few, two framings, a Transfer-Encoding in HTTP/1.0)
type Head is Data:
  HOk{req: Http.Request, f: Frame, v10: Bool, closing: Bool, head: Bool}
  HNo{}

# the engine's framing, its body cap aside
def head.frame(ok: Bool, bd: Eng.Bd) -> Maybe<&2, Frame>:
  match ok bd:
    case False{} _:
      None{}
    case True{} Eng.BdNone{}:
      Some{FLen{0n}}
    case True{} Eng.BdLen{v}:
      Some{FLen{U32.to_nat(v)}}
    case True{} Eng.BdChunked{}:
      Some{FChunked{}}
    case True{} Eng.BdBad{}:
      None{}

def head.ok(+ip: Bytes(), r: Eng.Req, f: Frame) -> Head:
  match r:
    case Eng.Req{m, t, b, +cl, +ws, k, +hd}:
      HOk{Http.req.of(ip, Eng.Req{m, t, b, cl, ws, k, hd}), f, Server.hd.v10(hd), cl || ws, Server.hd.head(hd)}

def head.mk(+ip: Bytes(), r: Eng.Req, mf: Maybe<&2, Frame>) -> Head:
  match mf:
    case None{}:
      HNo{}
    case Some{f}:
      head.ok(ip, r, f)

def head.pair(+ip: Bytes(), r: Eng.Req, fr: Bool & Eng.Bd) -> Head:
  (ok, bd) = fr
  head.mk(ip, r, head.frame(ok, bd))

# the head the engine holds, pd, judged
def head.of(+ip: Bytes(), +pd: Eng.Pend) -> Head:
  head.pair(ip, Eng.pend.req(pd, ""), Eng.head.frame(pd))

def at.head.st(+ip: Bytes(), st: Eng.St, +pd: Eng.Pend) -> Maybe<&2, Head>:
  match st:
    case Eng.CrL{}:
      Some{head.of(ip, pd)}
    case _:
      None{}

# the reader at a head's blank line, the CR read: the head; anywhere
# else, none
def at.head(+ip: Bytes(), p: Eng.P) -> Maybe<&2, Head>:
  match p:
    case Eng.P{st, +pd, out}:
      at.head.st(ip, st, pd)

# The connection
# ==============
#
# Server.serve's loop, with one more way out of a read: the engine's
# reader stopped at a stream route's head (Where a read stops, below),
# the head judged there, and the body read by the handler. After a
# streamed request the connection goes on with the bytes after its body
# (Stream.next), read from a fresh reader as the start of the next
# request.

# what the connection goes on with after a streamed request: the socket
# and the bytes that came after the body
def Go() -> Type:
  Socket -> Bytes() -> IO(Socket)

# the server's own answer, closing
def own.fin(+cfg: Cfg, +code: U32, s: Socket) -> IO(Socket):
  Server.fin(cfg.srv(cfg), [L.Raw{Server.own(False{}, False{}, code)}], s)

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

def begin(~E: Data, ~ups: Ux(E), +cfg: Cfg, +env: E, hd: Head, +cont: Bool, +rest: Bytes(), s: Socket, nx: Go()) ->
  IO(Socket):
  match hd:
    case HNo{}:
      own.fin(cfg, 400, s)
    case HOk{+req, +f, +v10, +closing, +head}:
      begin.at(~E, ~ups, cfg, env, req, f, v10, closing, cont, head, rest, s, nx, too.big(f, cfg.max(cfg)))

def pend.of(p: Eng.P) -> Eng.Pend:
  match p:
    case Eng.P{st, pd, out}:
      pd

def target.of(p: Eng.P) -> Bytes():
  match p:
    case Eng.P{st, pd, out}:
      match pd:
        case Eng.Pend{meth, path, cl, close, host, ws, fx, hx, nx}:
          path

def begin.lf(~E: Data, ~ups: Ux(E), +cfg: Cfg, +ip: Bytes(), +env: E, +p: Eng.P, lf: Bool, far: Bool, +rest: Bytes(),
  s: Socket, nx: Go()) -> IO(Socket):
  match lf far:
    case False{} _:
      own.fin(cfg, 400, s)
    case True{} True{}:
      own.fin(cfg, 414, s)
    case True{} False{}:
      begin(~E, ~ups, cfg, env, head.of(ip, pend.of(p)), Server.expects(p), String.drop(rest, 1n), s, nx)

# a stream route's head, the reader at its blank line's CR, and rest what
# came after that CR (never empty): anything but the LF there is refused,
# as the engine refuses it; a target past 8 KiB is a 414, as the
# server's; then the head is judged (head.of) and the bytes after the LF
# are the body's first read
def begin.head(~E: Data, ~ups: Ux(E), +cfg: Cfg, +ip: Bytes(), +env: E, +p: Eng.P, +rest: Bytes(), s: Socket,
  nx: Go()) -> IO(Socket):
  begin.lf(~E, ~ups, cfg, ip, env, p, U32.is_eq(Bytes.get(rest, 0n), 10), Eng.long(Eng.target.cap(), target.of(p)), rest,
    s, nx)

# Where a read stops
# ------------------
#
# A read goes through the engine's reader as Server.serve's does (the
# proxy's scan, Server.scan), but a piece at a time: up to and with each
# CR (a body counted off by its length goes in one piece), and before
# each piece the reader is looked at. When it stands at the blank line's
# CR of a head a stream route takes (Eng.CrL, the method and path of the
# head it holds), the read stops: the requests completed before it are
# answered as the server answers them, and the rest of the read is the
# stream's. The reader reaches CrL only at a CR, and it is looked at
# after every CR and at the start of every read (a head whose CR ended
# the last one), so every stream route's head stops the read at its
# blank line, however the stream was cut and whatever came before it on
# the connection: none is read whole, and none is ever held to the
# engine's body cap.

# how a read went: through whole, as the server's scan says; or stopped
# at a stream route's head, with the requests completed before it, the
# reader at the head's CR, and the bytes after that CR
type Cut is Data:
  Whole{sd: X.Scanned}
  At{ts: List<&2, Eng.Req>, p: Eng.P, rest: Bytes()}

def stops.st(rs: List<&1, Route>, +ip: Bytes(), st: Eng.St, +pd: Eng.Pend) -> Bool:
  match st:
    case Eng.CrL{}:
      +r = Http.req.of(ip, Eng.pend.req(pd, ""))
      takes(rs, Http.method(r), Http.path(r))
    case _:
      False{}

# whether the reader stands at the blank line of a head a stream route
# takes
def stops(rs: List<&1, Route>, +ip: Bytes(), p: Eng.P) -> Bool:
  match p:
    case Eng.P{st, +pd, out}:
      stops.st(rs, ip, st, pd)

# how much of a read the next piece is: the rest of a body counted off,
# else up to and with the next CR
def piece(p: Eng.P, +bs: Bytes()) -> Nat:
  match p:
    case Eng.P{st, pd, out}:
      match st:
        case Eng.Bod{r, b}:
          1n+r
        case Eng.Chd{r, b, left}:
          1n+r
        case _:
          1n+Bytes.find_byte(bs, 0n, 13)

def scan.p(sc: X.Scan) -> Eng.P:
  match sc:
    case X.Scan{p, n}:
      p

# what a read goes on with after a piece
def Rest() -> Type:
  X.Scan -> Bytes() -> List<&2, Eng.Req> -> Cut

def cut.fed(+more: Bytes(), acc: List<&2, Eng.Req>, sd: X.Scanned, again: Rest()) -> Cut:
  match sd:
    case X.Scanned{took, t}:
      match t:
        case X.TWait{sc2}:
          again(sc2, more, List.append(&2, Eng.Req, acc, took))
        case X.TBad{}:
          Whole{X.Scanned{List.append(&2, Eng.Req, acc, took), X.TBad{}}}
        case X.TUp{}:
          Whole{X.Scanned{List.append(&2, Eng.Req, acc, took), X.TUp{}}}

def cut.at(+sc: X.Scan, +bs: Bytes(), acc: List<&2, Eng.Req>, empty: Bool, stop: Bool, again: Rest()) -> Cut:
  match empty stop:
    case True{} _:
      Whole{X.Scanned{acc, X.TWait{sc}}}
    case False{} True{}:
      At{acc, scan.p(sc), bs}
    case False{} False{}:
      +i = piece(scan.p(sc), bs)
      cut.fed(String.drop(bs, i), acc, Server.scan(String.take(bs, i), sc), again)

# a read, from where the last one left the reader: at most k pieces
# (each takes a byte at least), acc the requests completed so far
def cut.go(~E: Data, ~ups: Ux(E), +env: E, +ip: Bytes(), k: Nat, +sc: X.Scan, +bs: Bytes(), acc: List<&2, Eng.Req>) -> Cut:
  match k:
    case 0n:
      Whole{X.Scanned{acc, X.TBad{}}}
    case 1n+j:
      cut.at(sc, bs, acc, String.is_empty(bs), stops(ups(env), ip, scan.p(sc)),
        sc2 => +b2 => a2 => cut.go(~E, ~ups, env, ip, j, sc2, b2, a2))

def cut(~E: Data, ~ups: Ux(E), +env: E, +ip: Bytes(), +sc: X.Scan, +bs: Bytes()) -> Cut:
  cut.go(~E, ~ups, env, ip, Nat.add(Bytes.len(bs), 2n), sc, bs, Nil{})

# The requests before it
# ----------------------
#
# Server.serve's, for the requests a read completed: each handed to app.

def one.at(~E: Data, ~app: Server.Hx(E), +cfg: Cfg, +ip: Bytes(), +env: E, +r: Eng.Req, +head: Bool, +v10: Bool,
  far: Bool, acc: List<&2, L.Seg>, s: Socket, go: List<&2, L.Seg> -> Socket -> IO(Socket)) -> IO(Socket):
  match far:
    case True{}:
      Server.fin(cfg.srv(cfg), Con{L.Raw{Server.own(head, v10, 414)}, acc}, s)
    case False{}:
      IO.bind(Http.Response, Socket, app(env, Http.req.of(ip, r)),
        resp => Server.one.done(cfg.srv(cfg), head, Eng.req.close(r) || Eng.req.ws(r), v10, resp, acc, s, go))

def one(~E: Data, ~app: Server.Hx(E), +cfg: Cfg, +ip: Bytes(), +env: E, +r: Eng.Req, acc: List<&2, L.Seg>, s: Socket,
  go: List<&2, L.Seg> -> Socket -> IO(Socket)) -> IO(Socket):
  match r:
    case Eng.Req{meth, +path, body, close, ws, key, hd}:
      one.at(~E, ~app, cfg, ip, env, r, Server.hd.head(hd), Server.hd.v10(hd), Eng.long(Eng.target.cap(), path), acc, s,
        go)

def took(~E: Data, ~app: Server.Hx(E), +cfg: Cfg, +ip: Bytes(), +env: E, ts: List<&2, Eng.Req>, t: X.Tail, fresh: Bool,
  t0: Maybe<&2, Nat>, cont: Bool, acc: List<&2, L.Seg>, s: Socket, more: Server.More()) -> IO(Socket):
  match ts:
    case Nil{}:
      Server.tail(cfg.srv(cfg), t, fresh, t0, cont, acc, s, more)
    case Con{+r, rest}:
      one(~E, ~app, cfg, ip, env, r, acc, s,
        acc2 => s2 => took(~E, ~app, cfg, ip, env, rest, t, True{}, None{}, False{}, acc2, s2, more))

def scanned(~E: Data, ~app: Server.Hx(E), +cfg: Cfg, +ip: Bytes(), +env: E, sd: X.Scanned, t0: Maybe<&2, Nat>, cont: Bool,
  s: Socket, more: Server.More()) -> IO(Socket):
  match sd:
    case X.Scanned{ts, t}:
      took(~E, ~app, cfg, ip, env, ts, t, False{}, t0, cont, Nil{}, s, more)

# the stream, once the responses to the requests before it are sent
def stream.at(~E: Data, ~ups: Ux(E), +cfg: Cfg, +ip: Bytes(), +env: E, acc: List<&2, L.Seg>, s: Socket, +p: Eng.P,
  +rest: Bytes(), nx: Go()) -> IO(Socket):
  match acc:
    case Nil{}:
      begin.head(~E, ~ups, cfg, ip, env, p, rest, s, nx)
    case Con{a, t}:
      IO.bind(Socket & Bool, Socket,
        Server.flush.segs(s, Server.rev.onto(Con{a, t}, Nil{}), Server.cfg.send(cfg.srv(cfg))),
        sb => Server.next(sb, s2 => begin.head(~E, ~ups, cfg, ip, env, p, rest, s2, nx)))

def took.at(~E: Data, ~app: Server.Hx(E), ~ups: Ux(E), +cfg: Cfg, +ip: Bytes(), +env: E, ts: List<&2, Eng.Req>,
  acc: List<&2, L.Seg>, s: Socket, +p: Eng.P, +rest: Bytes(), nx: Go()) -> IO(Socket):
  match ts:
    case Nil{}:
      stream.at(~E, ~ups, cfg, ip, env, acc, s, p, rest, nx)
    case Con{+r, t}:
      one(~E, ~app, cfg, ip, env, r, acc, s, acc2 => s2 => took.at(~E, ~app, ~ups, cfg, ip, env, t, acc2, s2, p, rest, nx))

# The loop
# --------

def on.cut(~E: Data, ~app: Server.Hx(E), ~ups: Ux(E), +cfg: Cfg, +ip: Bytes(), +env: E, c: Cut, t0: Maybe<&2, Nat>,
  cont: Bool, s: Socket, more: Server.More(), nx: Go()) -> IO(Socket):
  match c:
    case Whole{sd}:
      scanned(~E, ~app, cfg, ip, env, sd, t0, cont, s, more)
    case At{ts, +p, +rest}:
      took.at(~E, ~app, ~ups, cfg, ip, env, ts, Nil{}, s, p, rest, nx)

def got.bytes(~E: Data, ~app: Server.Hx(E), ~ups: Ux(E), +cfg: Cfg, +ip: Bytes(), +env: E, +sc: X.Scan,
  t0: Maybe<&2, Nat>, cont: Bool, s: Socket, empty: Bool, +bs: Bytes(), more: Server.More(), nx: Go()) -> IO(Socket):
  match empty:
    case True{}:
      IO.pure(Socket, s)
    case False{}:
      on.cut(~E, ~app, ~ups, cfg, ip, env, cut(~E, ~ups, env, ip, sc, bs), t0, cont, s, more, nx)

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

# Response bodies
# ===============
#
# A response whose body the handler makes as it goes -- an export, an
# event stream, a body relayed from elsewhere -- never held whole: a
# route made by Stream.get(pat, h), h : Http.Request -> IO(Stream.Reply),
# answers Stream.pour(status, fields, run) (the length unknown: chunked)
# or Stream.pour.len(status, fields, n, run) (n bytes, a Content-Length),
# and run : Stream.Sink -> IO(Stream.Sink) is the producer. A Sink is
# affine, as a Body is: Stream.write(k, bytes) answers the Sink beside
# Done, or why it failed (Stream.Err), and the producer hands the Sink
# back when the body is over. The server writes the head before run
# begins, each write as it comes, and the end after run returns:
#
#   the framing   chunked when the length is unknown (to HTTP/1.0, the
#                 body runs to the close); a declared length is a
#                 Content-Length, and a write past it is refused whole
#                 (ELarge): nothing of it goes out, and the connection
#                 closes after the response, as it does when the
#                 producer returns short of the length
#   backpressure  a write returns once its bytes are on the socket, each
#                 send within the server's send time (10 s) or ETime: a
#                 client that stops reading stops the producer
#   the peer gone a send that fails is EClosed; after a failure every
#                 write answers the same failure and sends nothing
#   no body       to HEAD (and for a 204 or 304) the head goes out alone,
#                 and every write answers ENone
#
# net/LAWS.bend proves, of the pure writer the IO runs (Stream.emit,
# Stream.close, Stream.opening):
#
#   pour_chunked  a chunked response, read back by wire/http1's spec, is
#                 one final response, the handler's status, its body the
#                 writes joined, closing as the server said, nothing after
#   pour_length   a declared length whose writes come to it, the same
#   pour_capped   a declared length is never written past, whatever the
#                 writes
#   pour_quiet    after a failure nothing more is written, not the end
#   pour_bounded  a write goes out as itself and at most a small, fixed
#                 framing: the writer holds nothing between writes, so a
#                 connection's memory is one write, however long the body
#
# Stream.events(~S, ~next, s, every, fields) is an event stream
# (text/event-stream): next(s, every) is asked for the next event, and
# answers one (Stream.event(name, data)), Stream.idle() when nothing came
# within every ms (a comment goes out, which keeps proxies from timing
# the stream out and finds a client that left), or Stream.over().

# The writer
# ----------

# how the body is framed: chunked; a length, with what is left of it; to
# the close; none at all
type Mode is Data:
  MChunked{}
  MLen{left: Nat}
  MRaw{}
  MNone{}

# the writer between writes: its framing, and the failure it ended in
type Sent is Data:
  Sent{mode: Mode, fail: Maybe<&2, Err>}

def sent.fail(s: Sent) -> Maybe<&2, Err>:
  match s:
    case Sent{m, f}:
      f

def sent.failed(s: Sent, +e: Err) -> Sent:
  match s:
    case Sent{m, f}:
      Sent{m, Some{e}}

# A chunk is 2^j bytes, j from 0 to 14, with its size in hex: a write is
# cut into the chunks its length's bits say, the largest first, so every
# size line is one of fifteen.
def nth.size(j: Nat, ns: List<&2, Nat>) -> Nat:
  match j ns:
    case _ Nil{}:
      0n
    case 0n Con{n, t}:
      n
    case 1n+i Con{n, t}:
      nth.size(i, t)

def chunk.size(j: Nat) -> Nat:
  nth.size(j, [1n, 2n, 4n, 8n, 16n, 32n, 64n, 128n, 256n, 512n, 1024n, 2048n, 4096n, 8192n, 16384n])

def chunk.hexes() -> List<&2, Bytes()>:
  ["1", "2", "4", "8", "10", "20", "40", "80", "100", "200", "400", "800", "1000", "2000", "4000"]

def nth.hex(j: Nat, hs: List<&2, Bytes()>) -> Bytes():
  match j hs:
    case _ Nil{}:
      ""
    case 0n Con{h, t}:
      h
    case 1n+i Con{h, t}:
      nth.hex(i, t)

def chunk.hex(j: Nat) -> Bytes():
  nth.hex(j, chunk.hexes())

# the most one emit frames: Stream.write cuts longer writes into emits
# of this, each framed at once
def emit.max() -> Nat:
  16384n

def chunks.at(fit: Bool, +j: Nat, +x: Bytes(), go: Bytes() -> Bytes()) -> Bytes():
  match fit:
    case True{}:
      Bytes.append(chunk.hex(j), Bytes.append("\r\n", Bytes.append(String.take(x, chunk.size(j)),
        Bytes.append("\r\n", go(String.drop(x, chunk.size(j)))))))
    case False{}:
      go(x)

# x as chunks, a bit at a time from 2^j down: all of x when it is under
# 2^(j+1) bytes
def chunks.go(j: Nat, +x: Bytes()) -> Bytes():
  match j:
    case 0n:
      chunks.at(Nat.is_ge(Bytes.len(x), chunk.size(0n)), 0n, x, t => "")
    case 1n+(+i):
      chunks.at(Nat.is_ge(Bytes.len(x), chunk.size(1n+i)), 1n+i, x, t => chunks.go(i, t))

def chunks(+x: Bytes()) -> Bytes():
  chunks.go(14n, x)

# the body's last chunk
def chunk.last() -> Bytes():
  "0\r\n\r\n"

def emit.len(ok: Bool, +left: Nat, +x: Bytes()) -> Sent & Bytes():
  match ok:
    case True{}:
      (Sent{MLen{Nat.sub(left, Bytes.len(x))}, None{}}, x)
    case False{}:
      (Sent{MLen{left}, Some{ELarge{}}}, "")

def emit.chunked(ok: Bool, +x: Bytes()) -> Sent & Bytes():
  match ok:
    case True{}:
      (Sent{MChunked{}, None{}}, chunks(x))
    case False{}:
      (Sent{MChunked{}, Some{EBad{}}}, "")

def emit.mode(m: Mode, +x: Bytes()) -> Sent & Bytes():
  match m:
    case MChunked{}:
      emit.chunked(Nat.is_le(Bytes.len(x), emit.max()), x)
    case MLen{+left}:
      emit.len(Nat.is_le(Bytes.len(x), left), left, x)
    case MRaw{}:
      (Sent{MRaw{}, None{}}, x)
    case MNone{}:
      (Sent{MNone{}, Some{ENone{}}}, "")

# a write: the bytes that go out for it, and the writer after it. A
# writer that failed sends nothing more; a length is never written past
def emit(st: Sent, +x: Bytes()) -> Sent & Bytes():
  match st:
    case Sent{m, f}:
      match f:
        case Some{e}:
          (Sent{m, Some{e}}, "")
        case None{}:
          emit.mode(m, x)

def close.mode(m: Mode) -> Bytes() & Bool:
  match m:
    case MChunked{}:
      (chunk.last(), True{})
    case MLen{left}:
      ("", Nat.is_eq(left, 0n))
    case MRaw{}:
      ("", False{})
    case MNone{}:
      ("", True{})

def close.at(m: Mode, f: Maybe<&2, Err>) -> Bytes() & Bool:
  match f:
    case Some{e}:
      ("", False{})
    case None{}:
      close.mode(m)

def close.none(m: Mode) -> Bool:
  match m:
    case MNone{}:
      True{}
    case _:
      False{}

def close.pick(nb: Bool, m: Mode, f: Maybe<&2, Err>) -> Bytes() & Bool:
  match nb:
    case True{}:
      ("", True{})
    case False{}:
      close.at(m, f)

# the body's end: the bytes that end it, and whether the response ended
# as its framing said (else the connection closes after it). A response
# with no body ended with its head, whatever was tried after
def close(st: Sent) -> Bytes() & Bool:
  match st:
    case Sent{+m, f}:
      close.pick(close.none(m), m, f)

def emit.joined(+a: Bytes(), q: Sent & Bytes()) -> Sent & Bytes():
  (st, b) = q
  (st, Bytes.append(a, b))

def emit.join(q: Sent & Bytes(), +rest: Bytes(), again: Sent -> Bytes() -> Sent & Bytes()) -> Sent & Bytes():
  (st, a) = q
  emit.joined(a, again(st, rest))

def emit.cut(small: Bool, st: Sent, +x: Bytes(), again: Sent -> Bytes() -> Sent & Bytes()) -> Sent & Bytes():
  match small:
    case True{}:
      emit(st, x)
    case False{}:
      emit.join(emit(st, String.take(x, emit.max())), String.drop(x, emit.max()), again)

# a write of any length: emits of at most emit.max() bytes, their bytes
# joined
def emit.all(k: Nat, st: Sent, +x: Bytes()) -> Sent & Bytes():
  match k:
    case 0n:
      emit(st, x)
    case 1n+j:
      emit.cut(Nat.is_le(Bytes.len(x), emit.max()), st, x, st2 => r => emit.all(j, st2, r))

# The head
# --------

# the head as bend-proxy's rser writes one (demos/io_proxy/core.bend):
# the status line, the fields, the length (none when ""), the
# connection's fate, the blank line
def rhd.bytes(+cd: Bytes(), +why: Bytes(), fs: List<&2, Wr.Field>, clen: Bytes(), +conn: Bytes()) -> Bytes():
  Bytes.append(X.fls.put(X.rall(fs, clen, conn), Bytes.append(Bytes.append(Bytes.append(Bytes.append("HTTP/1.1 ", cd),
    " "), why), "\r\n")), "\r\n")

def te() -> List<&2, Wr.Field>:
  [Wr.Field{"transfer-encoding", "chunked"}]

# X.rok.len with the body's length for the body
def len.at.n(v: RS.FLine, +bodyless: Bool, +n: Nat) -> Bool:
  match v:
    case RS.FVal{val}:
      match val:
        case RS.VLen{+m, ws}:
          Bool.not(U32.is_lt(268435455, m)) && (bodyless ||
            (X.same(U32.is_zero(m), Nat.is_eq(n, 0n)) && Nat.is_eq(U32.to_nat(m), n)))
        case _:
          False{}
    case _:
      False{}

def len.ok(+head: Bool, +bodyless: Bool, clen: Bytes(), +n: Nat) -> Bool:
  match clen:
    case SNil{}:
      bodyless
    case SCon{c, t}:
      +d : Bytes() = SCon{c, t}
      X.rok.all(RS.TVal{}, d) && len.at.n(RS.len.view(X.rask(head), RS.span(RS.TOws{}, Con{32, Bytes.to_list(d)})),
        bodyless, n)

# what bend-proxy's rvalid asks of a head but its length: a status from
# 200 to 599, the one the line says, a reason and field values with no
# line end or control, names of token bytes none of which is the
# framing's
def rhd.ok(+cd: Bytes(), +code: U32, +why: Bytes(), fs: List<&2, Wr.Field>) -> Bool:
  X.rok.code(cd, code) && X.rok.all(RS.TVal{}, why) && X.rok.fields(fs)

# a head that failed the check: the server's 500 goes instead, and the
# writer is failed (every write answers EBad)
def opening.ok(ok: Bool, +head: Bool, +closing: Bool, +v10: Bool, +hb: Bytes(), +m: Mode) -> Bytes() & Sent:
  match ok:
    case True{}:
      (hb, Sent{m, None{}})
    case False{}:
      (X.reply(Some{X.rsp.fin(head, 500, Http.e500.head(), Http.e500.body())}, head, closing, v10),
        Sent{MNone{}, Some{EBad{}}})

def mode.body(+head: Bool, m: Mode) -> Mode:
  Bool.pick(Mode, head, MNone{}, m)

def opening.none.at(bn: Bool, bv: Bool, bh: Bool, +head: Bool, +closing: Bool, +v10: Bool, +code: U32, +cd: Bytes(),
  +why: Bytes(), +fs: List<&2, Wr.Field>) -> Bytes() & Sent:
  match bn bv bh:
    case True{} _ _:
      opening.ok(rhd.ok(cd, code, why, fs), head, closing, v10, rhd.bytes(cd, why, fs, "", X.conn.val(closing, v10)),
        MNone{})
    case False{} True{} False{}:
      opening.ok(rhd.ok(cd, code, why, fs), head, True{}, v10, rhd.bytes(cd, why, fs, "", X.conn.val(True{}, v10)),
        MRaw{})
    case False{} True{} True{}:
      opening.ok(rhd.ok(cd, code, why, fs), head, closing, v10, rhd.bytes(cd, why, fs, "", X.conn.val(closing, v10)),
        MNone{})
    case False{} False{} _:
      opening.ok(rhd.ok(cd, code, why, fs), head, closing, v10,
        rhd.bytes(cd, why, List.append(&2, Wr.Field, fs, te()), "", X.conn.val(closing, v10)), mode.body(head, MChunked{}))

# the length unknown: chunked, or to HTTP/1.0 (which reads no chunk) a
# body that runs to the close; a 204 or 304 has none
def opening.none(+head: Bool, +closing: Bool, +v10: Bool, +code: U32, +nb: Bool, h: X.RHead) -> Bytes() & Sent:
  match h:
    case X.RHead{+cd, +why, +fs, hl}:
      opening.none.at(nb, v10, head, head, closing, v10, code, cd, why, fs)

# the check of a head with a length: rhd.ok, and the length as rvalid
# reads it against a body of n bytes
def len.check(+head: Bool, +code: U32, +cd: Bytes(), +why: Bytes(), fs: List<&2, Wr.Field>, +clen: Bytes(), +n: Nat) -> Bool:
  rhd.ok(cd, code, why, fs) && len.ok(head, X.rbodyless(head, code), clen, n)

# a declared length: a Content-Length (HEAD's too, none for 204 or 304)
def opening.len(+head: Bool, +closing: Bool, +v10: Bool, +code: U32, +nb: Bool, +n: Nat, h: X.RHead) -> Bytes() & Sent:
  match h:
    case X.RHead{+cd, +why, +fs, hl}:
      +clen = Bool.pick(Bytes(), nb, "", Nat.show(n))
      opening.ok(len.check(head, code, cd, why, fs, clen, n), head, closing, v10,
        rhd.bytes(cd, why, fs, clen, X.conn.val(closing, v10)), mode.body(X.rbodyless(head, code), MLen{n}))

def opening.at(+head: Bool, +closing: Bool, +v10: Bool, +code: U32, +nb: Bool, h: X.RHead, ln: Maybe<&2, Nat>) ->
  Bytes() & Sent:
  match ln:
    case None{}:
      opening.none(head, closing, v10, code, nb, h)
    case Some{+n}:
      opening.len(head, closing, v10, code, nb, n, h)

# the head a response goes out with, and the writer its body starts in
def opening(+head: Bool, +closing: Bool, +v10: Bool, +code: U32, hs: List<&2, Http.Header>, ln: Maybe<&2, Nat>) ->
  Bytes() & Sent:
  opening.at(head, closing, v10, code, U32.is_eq(code, 204) || U32.is_eq(code, 304), Http.rhead(code, hs, ""), ln)

def emits.on(q: Sent & Bytes(), go: Sent -> Bytes()) -> Bytes():
  (st, out) = q
  Bytes.append(out, go(st))

# what the writer puts on the wire for the writes ws, the end included
def emits(ws: List<&2, Bytes()>, st: Sent) -> Bytes():
  match ws:
    case Nil{}:
      Pair.fst(Bytes(), Bool, close(st))
    case Con{+x, t}:
      emits.on(emit(st, x), s2 => emits(t, s2))

# a whole response, as the server writes it: its head, then each write's
# bytes, then the end (LAWS.bend's pour_chunked and pour_length read it)
def poured.at(q: Bytes() & Sent, ws: List<&2, Bytes()>) -> Bytes():
  (hb, st) = q
  Bytes.append(hb, emits(ws, st))

def poured(+head: Bool, +closing: Bool, +v10: Bool, +code: U32, hs: List<&2, Http.Header>, ln: Maybe<&2, Nat>,
  ws: List<&2, Bytes()>) -> Bytes():
  poured.at(opening(head, closing, v10, code, hs, ln), ws)

# The Sink
# --------

type Sink is Type:
  Sink{s: Socket, st: Sent, ms: U32}

def Wrote() -> Type:
  Sink & Result<&2, &2, Err, Unit>

# a send that failed: stalled past the send time (ETIMEDOUT), or the
# peer gone
def send.err(+code: U32) -> Err:
  Bool.pick(Err, U32.is_eq(code, 110) || U32.is_eq(code, 60), ETime{}, EClosed{})

def write.sent(m: L.Put(Socket), +st: Sent, +ms: U32) -> IO(Wrote()):
  (s, r) = m
  match r:
    case Fail{er}:
      (code, msg) = er
      +e = send.err(code)
      IO.pure(Wrote(), (Sink{s, sent.failed(st, e), ms}, Fail{e}))
    case Done{u}:
      IO.pure(Wrote(), (Sink{s, st, ms}, Done{Unit{}}))

def write.out(s: Socket, +st: Sent, +ms: U32, +out: Bytes(), f: Maybe<&2, Err>, empty: Bool) -> IO(Wrote()):
  match f empty:
    case Some{e} _:
      IO.pure(Wrote(), (Sink{s, st, ms}, Fail{e}))
    case None{} True{}:
      IO.pure(Wrote(), (Sink{s, st, ms}, Done{Unit{}}))
    case None{} False{}:
      IO.bind(L.Put(Socket), Wrote(), TCP.send_buf_poll(s, out, ms), m => write.sent(m, st, ms))

def write.emit(s: Socket, q: Sent & Bytes(), +ms: U32) -> IO(Wrote()):
  (+st, +out) = q
  write.out(s, st, ms, out, sent.fail(st), String.is_empty(out))

# Write x: its bytes go out, framed, before the write returns (each send
# within the send time); Done, or why it failed. After a failure every
# write answers the same failure and sends nothing.
def write(k: Sink, +x: Bytes()) -> IO(Wrote()):
  match k:
    case Sink{s, st, +ms}:
      write.emit(s, emit.all(Bytes.len(x), st, x), ms)

# Stop the body short: nothing more goes out, not its end, and the
# connection closes after the response, so the client sees it cut (a
# producer whose source failed, having sent a head that said 200)
def abort(k: Sink) -> Sink:
  match k:
    case Sink{s, st, ms}:
      Sink{s, sent.failed(st, EClosed{}), ms}

# The response
# ------------

# what a Stream.get handler answers: a response whole, or one whose body
# run writes (of n bytes, or of a length it does not know)
type Reply is Type:
  Plain{r: Http.Response}
  Pour{code: U32, hs: List<&2, Http.Header>, ln: Maybe<&2, Nat>, run: Sink -> IO(Sink)}

def whole(r: Http.Response) -> Reply:
  Plain{r}

# a response whose body run writes, its length unknown: chunked
def pour(code: U32, hs: List<&2, Http.Header>, run: Sink -> IO(Sink)) -> Reply:
  Pour{code, hs, None{}, run}

# a response whose body run writes, n bytes of it: a Content-Length
def pour.len(code: U32, hs: List<&2, Http.Header>, n: Nat, run: Sink -> IO(Sink)) -> Reply:
  Pour{code, hs, Some{n}, run}

def pour.ended(m: L.Put(Socket), +ok: Bool) -> IO(Socket & Bool):
  (s, r) = m
  IO.pure(Socket & Bool, (s, ok && Result.is_done(&1, &1, U32 & String, Unit, r)))

def pour.end.at(s: Socket, +eb: Bytes(), +ok: Bool, +more: Bool, +ms: U32, empty: Bool) -> IO(Socket & Bool):
  match empty:
    case True{}:
      IO.pure(Socket & Bool, (s, ok && more))
    case False{}:
      IO.bind(L.Put(Socket), Socket & Bool, TCP.send_buf_poll(s, eb, ms), m => pour.ended(m, ok && more))

def pour.end(s: Socket, q: Bytes() & Bool, +more: Bool, +ms: U32) -> IO(Socket & Bool):
  (+eb, +ok) = q
  pour.end.at(s, eb, ok, more, ms, String.is_empty(eb))

def pour.fin(k: Sink, +more: Bool) -> IO(Socket & Bool):
  match k:
    case Sink{s, st, +ms}:
      pour.end(s, close(st), more, ms)

def pour.headed(m: L.Put(Socket), +st: Sent, run: Sink -> IO(Sink), +more: Bool, +ms: U32) -> IO(Socket & Bool):
  (s, r) = m
  match r:
    case Fail{e}:
      IO.pure(Socket & Bool, (s, False{}))
    case Done{u}:
      IO.bind(Sink, Socket & Bool, run(Sink{s, st, ms}), k => pour.fin(k, more))

def pour.begun(q: Bytes() & Sent, run: Sink -> IO(Sink), +more: Bool, +ms: U32, s: Socket) -> IO(Socket & Bool):
  (hb, +st) = q
  IO.bind(L.Put(Socket), Socket & Bool, TCP.send_buf_poll(s, hb, ms), m => pour.headed(m, st, run, more, ms))

# the head, then run with the Sink, then the end: the socket, and whether
# the connection may go on
def pour.go(+code: U32, hs: List<&2, Http.Header>, ln: Maybe<&2, Nat>, run: Sink -> IO(Sink), t: Server.Terms,
  s: Socket) -> IO(Socket & Bool):
  match t:
    case Server.Terms{+head, +closing, +v10, +ms}:
      pour.begun(opening(head, closing, v10, code, hs, ln), run, Bool.not(closing), ms, s)

def reply.of(rp: Reply) -> IO(Server.Reply):
  match rp:
    case Plain{r}:
      IO.pure(Server.Reply, Server.Answer{r})
    case Pour{+code, hs, ln, run}:
      IO.pure(Server.Reply, Server.Pour{t => s => pour.go(code, hs, ln, run, t, s)})

# a GET route (HEAD too) whose handler answers a Stream.Reply, beside
# Server.get and the rest in Server.serve.routes (or WsServer.serve)
def get(pat: Bytes(), h: Http.Request -> IO(Reply)) -> Server.Route:
  Server.Sock{pat, a => r => IO.bind(Reply, Server.Reply, h(r), reply.of)}

# Server-sent events
# ------------------

# what an event stream's source answers: an event (its name, "" for a
# plain message; its data, a line a data field; its id, "" for none);
# nothing within the time it was given; or the stream's end
type Ev is Data:
  Event{name: Bytes(), data: Bytes(), id: Bytes()}
  Idle{}
  Over{}

def event(name: Bytes(), data: Bytes()) -> Ev:
  Event{name, data, ""}

def idle() -> Ev:
  Idle{}

def over() -> Ev:
  Over{}

def sse.keep(drop: Bool, +c: U32, rest: Bytes()) -> Bytes():
  match drop:
    case True{}:
      rest
    case False{}:
      SCon{Chr{c}, rest}

# a name or id, with no line end in it
def sse.clean(b: Bytes()) -> Bytes():
  match b:
    case SNil{}:
      ""
    case SCon{Chr{+c}, t}:
      sse.keep(U32.is_eq(c, 10) || U32.is_eq(c, 13), c, sse.clean(t))

def sse.field(+tag: Bytes(), +v: Bytes()) -> Bytes():
  Bool.pick(Bytes(), String.is_empty(v), "", Bytes.concat([tag, ": ", sse.clean(v), "\n"]))

# what a byte of data does: ends a line, is dropped (a CR), or is kept
type Dk is Data:
  DLf{}
  DCr{}
  DKeep{}

def sse.dk(+c: U32) -> Dk:
  Bool.pick(Dk, U32.is_eq(c, 10), DLf{}, Bool.pick(Dk, U32.is_eq(c, 13), DCr{}, DKeep{}))

def sse.line(+cur: Bytes()) -> Bytes():
  Bytes.concat(["data: ", cur, "\n"])

def sse.data.at(k: Dk, +c: U32, +cur: Bytes(), go: Bytes() -> Bytes()) -> Bytes():
  match k:
    case DLf{}:
      Bytes.append(sse.line(cur), go(""))
    case DCr{}:
      go(cur)
    case DKeep{}:
      go(Bytes.push(cur, c))

# the data, a data field a line (a CR dropped, a LF the line's end)
def sse.data.go(b: Bytes(), +cur: Bytes()) -> Bytes():
  match b:
    case SNil{}:
      sse.line(cur)
    case SCon{Chr{+c}, t}:
      sse.data.at(sse.dk(c), c, cur, cu => sse.data.go(t, cu))

# an event as it goes out (text/event-stream)
def sse.of(e: Ev) -> Bytes():
  match e:
    case Event{+name, +data, +id}:
      Bytes.concat([sse.field("event", name), sse.field("id", id), sse.data.go(data, ""), "\n"])
    case Idle{}:
      ": keepalive\n\n"
    case Over{}:
      ""

def events.fuel() -> Nat:
  U32.to_nat(4294967295)

def events.wrote(~S: Type, w: Wrote(), s: S, go: S -> Sink -> IO(Sink)) -> IO(Sink):
  (k, r) = w
  match r:
    case Done{u}:
      go(s, k)
    case Fail{e}:
      IO.pure(Sink, k)

def events.got(~S: Type, q: S & Ev, k: Sink, go: S -> Sink -> IO(Sink)) -> IO(Sink):
  (s, e) = q
  match e:
    case Over{}:
      IO.pure(Sink, k)
    case _:
      IO.bind(Wrote(), Sink, write(k, sse.of(e)), w => events.wrote(~S, w, s, go))

def events.at(~S: Type, ~next: S -> U32 -> IO(S & Ev), stop: Bool, +every: U32, s: S, k: Sink,
  go: S -> Sink -> IO(Sink)) -> IO(Sink):
  match stop:
    case True{}:
      IO.pure(Sink, k)
    case False{}:
      IO.bind(S & Ev, Sink, next(s, every), q => events.got(~S, q, k, go))

# the stream: an event, a keepalive, or the end, until the source says
# over, a write fails (the client left), or the server is stopped
def events.go(~S: Type, ~next: S -> U32 -> IO(S & Ev), n: Nat, +every: U32, s: S, k: Sink) -> IO(Sink):
  match n:
    case 0n:
      IO.pure(Sink, k)
    case 1n+j:
      IO.bind(Bool, Sink, IO.signal_seen(15),
        stop => events.at(~S, ~next, stop, every, s, k, s2 => k2 => events.go(~S, ~next, j, every, s2, k2)))

# an event stream: 200, text/event-stream, not to be cached, and the
# fields hs; next(s, every) is asked for each event
def events(~S: Type, ~next: S -> U32 -> IO(S & Ev), s: S, +every: U32, hs: List<&2, Http.Header>) -> Reply:
  pour(200, List.append(&2, Http.Header, [Http.Header{"content-type", "text/event-stream"},
    Http.Header{"cache-control", "no-cache"}], hs), k => events.go(~S, ~next, events.fuel(), every, s, k))
