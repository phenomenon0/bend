# The daemon's pure half: a request's text in, the new store and the response
# text out. Nothing here touches a socket, so every route -- including the two
# refusals -- is a test that runs in all four lanes (tests/cas/).
#
#   PUT /blob            body -> chunks -> addresses; answers with the address
#   GET /blob/<hex>/<off>/<len>   the range, one block per chunk it touches,
#                                 each block carrying its checked witness
#
# Base has no HTTP library (tests/io/http_request_roundtrip.bend pins that), so
# the parse is the four lines it has to be: cut at the blank line, split the
# request line on spaces, split the path on slashes. There is no chunked
# encoding, no keep-alive, no header beyond Content-Length: v0.
import Base
import ../../power/blake3.bend as B3
import ./cas.bend as Cas

# the chunker's target size: 1 << 12, so a chunk averages 4 KiB
def BITS() -> U32:
  12

# The head is its own def so LAWS.body_after_blank can name it: the law says
# every response is head, blank line, body, and it is only a computation away
# because the blank line is spelled once, here.
def resp.head(+code: U32, +reason: String, +len: U32) -> String:
  String.concat(["HTTP/1.1 ", U32.show(code), " ", reason,
    "\r\nContent-Type: text/plain\r\nContent-Length: ",
    U32.show(len), "\r\nConnection: close"])

def resp(+code: U32, +reason: String, +body: String) -> String:
  resp.head(code, reason, U32.from_nat(String.length(body))) ++ ("\r\n\r\n" ++ body)

# -- how much is a request ---------------------------------------------------

# A recv is one recv(2): the effs hand back whatever the socket had, so the
# reader has to know when to stop asking. These two say it, and they are pure,
# so tests/cas/ can pin the framing without a socket.

def clen.num(m: Maybe<&2, U32>) -> U32:
  match m:
    case None{}:
      0
    case Some{+n}:
      n

def clen.digits(r: String & (String & String)) -> U32:
  (num, rest) = r
  clen.num(U32.read(String.trim(num)))

def clen.after(r: String & String) -> U32:
  (sep, after) = r
  clen.digits(String.partition(after, "\r\n"))

def clen.head(r: String & (String & String)) -> U32:
  (before, rest) = r
  clen.after(rest)

# the Content-Length of a head, or 0 when it does not say. No other header is
# read: no chunked encoding, no keep-alive, no expect-continue.
def clen(+head: String) -> U32:
  clen.head(String.partition(String.to_lower(head), "content-length:"))

# The second disjunct is the socket edge again, and it is what keeps the
# daemon alive: Content-Length counts BYTES, String.length counts CHARACTERS,
# and TCP.recv hands back a UTF-8 decode -- so for a body with any byte above
# 0x7f the two never meet and the reader parks on a socket that will never
# send again. A body that is already not ASCII is one the store would refuse
# anyway, so the read stops here and route.put answers 400 instead of hanging.
def done.at(+body: String, head: String, found: Bool) -> Bool:
  match found:
    case False{}:
      False{}
    case True{}:
      Bool.or(Bool.not(String.is_ascii(body)),
        U32.is_le(clen(head), U32.from_nat(String.length(body))))

def done.on(head: String, r: String & String) -> Bool:
  (sep, body) = r
  done.at(body, head, Bool.not(String.is_empty(sep)))

def done.go(r: String & (String & String)) -> Bool:
  (head, rest) = r
  done.on(head, rest)

# a request is whole once the blank line has arrived and the bytes behind it
# are as many as the head promised
def req.done(+req: String) -> Bool:
  done.go(String.partition(req, "\r\n\r\n"))

# -- PUT ---------------------------------------------------------------------

def put.said(+b: Cas.Blob, +st: Cas.Store) -> String:
  String.concat(["stored ", B3.hex(Cas.blob.root(b)),
    "\nchunks ", U32.show(Cas.blob.n(b)),
    " size ", U32.show(Cas.blob.size(b)),
    "\nunique ", U32.show(Cas.store.kept(st)),
    " seen ", U32.show(Cas.store.seen(st)),
    " dupbytes ", U32.show(Cas.store.dupb(st)), "\n"])

def put.at(+st: Cas.Store, b: Cas.Blob) -> Cas.Store & String:
  (st, resp(201, "Created", put.said(b, st)))

def put.out(r: Cas.Store & Cas.Blob) -> Cas.Store & String:
  (st, b) = r
  put.at(st, b)

# the ASCII guard is the socket edge showing through: TCP.recv decodes UTF-8,
# so a byte above 0x7f would arrive as U+FFFD and be stored as a lie. Refusing
# is the only honest answer until the effs carry bytes.
def put.ok(st: Cas.Store, body: String, ascii: Bool) -> Cas.Store & String:
  match ascii:
    case True{}:
      put.out(Cas.put(st, body, BITS()))
    case False{}:
      (st, resp(400, "Bad Request",
        "body is not ASCII; the socket edge is UTF-8, see the lane report\n"))

def route.put(st: Cas.Store, +body: String) -> Cas.Store & String:
  put.ok(st, body, String.is_ascii(body))

# -- GET ---------------------------------------------------------------------

def get.say(r: Cas.Rsp) -> String:
  match r:
    case Cas.Ok{text}:
      resp(200, "OK", text)
    case Cas.No{why}:
      resp(409, "Conflict", "refused: " ++ (why ++ "\n"))

def get.len(+st: Cas.Store, a: String, +off: U32, ml: Maybe<&2, U32>)
    -> Cas.Store & String:
  match ml:
    case None{}:
      (st, resp(400, "Bad Request", "bad length\n"))
    case Some{+len}:
      (st, get.say(Cas.get(st, a, off, len)))

def get.off(+st: Cas.Store, a: String, mo: Maybe<&2, U32>, l: String)
    -> Cas.Store & String:
  match mo:
    case None{}:
      (st, resp(400, "Bad Request", "bad offset\n"))
    case Some{+off}:
      get.len(st, a, off, U32.read(l))

def route.get.3(st: Cas.Store, a: String, o: String, l: String)
    -> Cas.Store & String:
  get.off(st, a, U32.read(o), l)

def route.get.2(st: Cas.Store, a: String, o: String, t: List<&2, String>)
    -> Cas.Store & String:
  match t:
    case Nil{}:
      (st, resp(400, "Bad Request", "want /blob/<hex>/<off>/<len>\n"))
    case Con{l, rest}:
      route.get.3(st, a, o, l)

def route.get.1(st: Cas.Store, a: String, t: List<&2, String>)
    -> Cas.Store & String:
  match t:
    case Nil{}:
      (st, resp(400, "Bad Request", "want /blob/<hex>/<off>/<len>\n"))
    case Con{o, rest}:
      route.get.2(st, a, o, rest)

def route.get(st: Cas.Store, ps: List<&2, String>) -> Cas.Store & String:
  match ps:
    case Nil{}:
      (st, resp(400, "Bad Request", "want /blob/<hex>/<off>/<len>\n"))
    case Con{a, rest}:
      route.get.1(st, a, rest)

# -- the request -------------------------------------------------------------

def route.on(st: Cas.Store, path: String, body: String, is_put: Bool,
             is_get: Bool) -> Cas.Store & String:
  match is_put:
    case True{}:
      route.put(st, body)
    case False{}:
      match is_get:
        case True{}:
          route.get(st, String.split_on(String.drop(path, 6n), "/"))
        case False{}:
          (st, resp(404, "Not Found", "PUT /blob or GET /blob/<hex>/<off>/<len>\n"))

def route(st: Cas.Store, +method: String, +path: String, body: String)
    -> Cas.Store & String:
  route.on(st, path, body,
    Bool.and(String.eq(method, "PUT"), String.eq(path, "/blob")),
    Bool.and(String.eq(method, "GET"), String.starts_with(path, "/blob/")))

def line.on(st: Cas.Store, body: String, ws: List<&2, String>)
    -> Cas.Store & String:
  match ws:
    case Nil{}:
      (st, resp(400, "Bad Request", "empty request line\n"))
    case Con{m, t}:
      match t:
        case Nil{}:
          (st, resp(400, "Bad Request", "no path\n"))
        case Con{p, rest}:
          route(st, m, p, body)

def serve.cut(st: Cas.Store, top: String, r: String & String)
    -> Cas.Store & String:
  (sep, body) = r
  line.on(st, body, String.words(String.take(top, 200n)))

def serve.go(st: Cas.Store, r: String & (String & String))
    -> Cas.Store & String:
  (top, rest) = r
  serve.cut(st, top, rest)

# serve: the whole daemon, minus the socket. The body is everything after the
# blank line -- main.bend's job is to have read all of it before calling here.
def serve(st: Cas.Store, +req: String) -> Cas.Store & String:
  serve.go(st, String.partition(req, "\r\n\r\n"))
