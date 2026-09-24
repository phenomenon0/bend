# bend-net: the types every handler and every client speaks.
#
# A handler is Request -> IO(Response), middleware is Handler ->
# Handler, and both are templates (net/server.bend), so they compile to
# direct calls. A Request is what the HTTP engine's reader framed
# (demos/io_http_engine, held to RFC 9112 by frame_sim), adapted by
# req.of: the method's bytes, the path and the query (the target cut at
# its '?', as they came), the header fields (names lowercased, values
# trimmed, in order; the ones the framing owns -- Content-Length,
# Transfer-Encoding, Connection, Upgrade -- are the server's and are not
# passed on), the body (whole, and bounded), the peer's address, and the
# router's :params. A Response is a status, header fields and a body:
# bytes, or a file under a root that goes out by sendfile. It is written
# by write, whose every output a client reads back as exactly one
# response with that status and body (net/LAWS.bend's respond_framed).
import Base
import ../wire/reader.bend as Wr
import ../demos/io_http_engine/main.bend as Eng
import ../demos/io_proxy/core.bend as X

# Headers
# =======

# a field: its name (lowercase, as every lookup expects it) and value
type Header is Data:
  Header{name: Bytes(), value: Bytes()}

def Headers() -> Data:
  List<&2, Header>

def hdr.name(h: Header) -> Bytes():
  match h:
    case Header{n, v}:
      n

def hdr.value(h: Header) -> Bytes():
  match h:
    case Header{n, v}:
      v

# the value of the first field named n (n in any case), or None
def get.go(hs: List<&2, Header>, +n: Bytes()) -> Maybe<&2, Bytes()>:
  match hs:
    case Nil{}:
      None{}
    case Con{h, t}:
      match h:
        case Header{+k, v}:
          Bool.pick(Maybe<&2, Bytes()>, String.eq(k, n), Some{v}, get.go(t, n))

def get(hs: List<&2, Header>, n: Bytes()) -> Maybe<&2, Bytes()>:
  get.go(hs, Eng.lows(n))

def has(hs: List<&2, Header>, n: Bytes()) -> Bool:
  Maybe.is_some(&2, Bytes(), get(hs, n))

def del.put(drop: Bool, h: Header, rest: List<&2, Header>) -> List<&2, Header>:
  match drop:
    case True{}:
      rest
    case False{}:
      Con{h, rest}

# every field but those named n
def del.go(hs: List<&2, Header>, +n: Bytes()) -> List<&2, Header>:
  match hs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      match h:
        case Header{+k, v}:
          del.put(String.eq(k, n), Header{k, v}, del.go(t, n))

def del(hs: List<&2, Header>, n: Bytes()) -> List<&2, Header>:
  del.go(hs, Eng.lows(n))

# one more field, after the rest
def add(hs: List<&2, Header>, n: Bytes(), v: Bytes()) -> List<&2, Header>:
  List.append(&2, Header, hs, [Header{Eng.lows(n), v}])

# the field named n is v, and only v
def set(hs: List<&2, Header>, n: Bytes(), v: Bytes()) -> List<&2, Header>:
  +k = Eng.lows(n)
  List.append(&2, Header, del.go(hs, k), [Header{k, v}])

# Requests
# ========

type Request is Data:
  Request{method: Bytes(), path: Bytes(), query: Bytes(), headers: List<&2, Header>, body: Bytes(),
    remote: Bytes(), params: List<&2, Header>}

def path(r: Request) -> Bytes():
  match r:
    case Request{m, p, q, hs, b, ip, ps}:
      p

def query(r: Request) -> Bytes():
  match r:
    case Request{m, p, q, hs, b, ip, ps}:
      q

def headers(r: Request) -> List<&2, Header>:
  match r:
    case Request{m, p, q, hs, b, ip, ps}:
      hs

def body(r: Request) -> Bytes():
  match r:
    case Request{m, p, q, hs, b, ip, ps}:
      b

def remote(r: Request) -> Bytes():
  match r:
    case Request{m, p, q, hs, b, ip, ps}:
      ip

def params(r: Request) -> List<&2, Header>:
  match r:
    case Request{m, p, q, hs, b, ip, ps}:
      ps

def method(r: Request) -> Bytes():
  match r:
    case Request{m, p, q, hs, b, ip, ps}:
      m

# a request field's value (the name in any case)
def header(r: Request, n: Bytes()) -> Maybe<&2, Bytes()>:
  get(headers(r), n)

# a route's :name (or * for the rest), "" when the route has none
def param(r: Request, n: Bytes()) -> Bytes():
  Maybe.default(&2, Bytes(), get.go(params(r), n), "")

def with.params(r: Request, ps: List<&2, Header>) -> Request:
  match r:
    case Request{m, p, q, hs, b, ip, old}:
      Request{m, p, q, hs, b, ip, ps}

def is.method(r: Request, m: Bytes()) -> Bool:
  String.eq(method(r), m)

# The engine's request, as a handler sees it: the method's bytes, the
# target cut at its first '?', the fields the reader passed on (the
# Host, and every one it does not act on), each value trimmed of the
# whitespace at its ends (RFC 9110 5.5: none of it is the value), the
# body, and the peer's address.
def fields.of(fs: List<&2, Wr.Field>) -> List<&2, Header>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{f, t}:
      match f:
        case Wr.Field{n, v}:
          Con{Header{n, X.trim(v)}, fields.of(t)}

def target.at(+t: Bytes(), +i: Nat) -> Bytes() & Bytes():
  (String.take(t, i), String.drop(t, 1n+i))

def target.cut(+t: Bytes()) -> Bytes() & Bytes():
  target.at(t, Bytes.find_byte(t, 0n, 63))

def req.at(+ip: Bytes(), pq: Bytes() & Bytes(), hd: Eng.Hd, body: Bytes()) -> Request:
  (p, q) = pq
  match hd:
    case Eng.Hd{m, v10, fs, cn}:
      Request{m, p, q, fields.of(fs), body, ip, Nil{}}

def req.of(+ip: Bytes(), r: Eng.Req) -> Request:
  match r:
    case Eng.Req{meth, +target, body, close, ws, key, hd}:
      req.at(ip, target.cut(target), hd, body)

# Percent-encoding
# ================
#
# pct.decode is the URL standard's percent-decode: %XX (either case) is
# the byte XX, and a '%' not followed by two hex digits is itself.
# form.decode decodes '+' as a space too (application/x-www-form-
# urlencoded). pct.encode escapes every byte but the unreserved ones
# (ALPHA DIGIT - . _ ~) as %XX in capitals. LAWS.bend:
# pct.decode(pct.encode(s)) is s for every byte and for the vectors
# named there.

def hex.val(+c: U32) -> U32:
  Bool.pick(U32, U32.is_le(48, c) && U32.is_le(c, 57), (c - 48 : U32),
    Bool.pick(U32, U32.is_le(65, c) && U32.is_le(c, 70), (c - 55 : U32),
      Bool.pick(U32, U32.is_le(97, c) && U32.is_le(c, 102), (c - 87 : U32), 16)))

def hex.dig(+v: U32) -> U32:
  Bool.pick(U32, U32.is_lt(v, 10), (v + 48 : U32), (v + 55 : U32))

def pct.at(+plus: Bool, out: Bytes(), +c: U32, s: Bytes(), +h: U32, +l: U32, ok: Bool) -> Bytes() & Bytes():
  match ok:
    case True{}:
      (Bytes.push(out, ((h * 16 : U32) + l : U32)), String.drop(s, 2n))
    case False{}:
      (Bytes.push(out, c), s)

def pct.is(+plus: Bool, out: Bytes(), +c: U32, +s: Bytes(), esc: Bool) -> Bytes() & Bytes():
  match esc:
    case True{}:
      +h = hex.val(Bytes.get(s, 0n))
      +l = hex.val(Bytes.get(s, 1n))
      pct.at(plus, out, c, s, h, l, U32.is_lt(h, 16) && U32.is_lt(l, 16))
    case False{}:
      (Bytes.push(out, Bool.pick(U32, plus && U32.is_eq(c, 43), 32, c)), s)

def pct.one(+plus: Bool, out: Bytes(), +c: U32, +s: Bytes()) -> Bytes() & Bytes():
  pct.is(plus, out, c, s, U32.is_eq(c, 37))

def pct.go(k: Nat, +plus: Bool, ob: Bytes() & Bytes()) -> Bytes():
  match k:
    case 0n:
      (out, s) = ob
      out
    case 1n+j:
      (out, s) = ob
      match s:
        case SNil{}:
          out
        case SCon{Chr{+c}, t}:
          pct.go(j, plus, pct.one(plus, out, c, t))

def decode.as(+plus: Bool, +s: Bytes()) -> Bytes():
  pct.go(Bytes.len(s), plus, ("", s))

def pct.decode(s: Bytes()) -> Bytes():
  decode.as(False{}, s)

def form.decode(s: Bytes()) -> Bytes():
  decode.as(True{}, s)

def unreserved(+c: U32) -> Bool:
  (U32.is_le(65, c) && U32.is_le(c, 90)) || (U32.is_le(97, c) && U32.is_le(c, 122))
    || (U32.is_le(48, c) && U32.is_le(c, 57)) || U32.is_eq(c, 45) || U32.is_eq(c, 46)
    || U32.is_eq(c, 95) || U32.is_eq(c, 126)

def enc.one(out: Bytes(), +c: U32, keep: Bool) -> Bytes():
  match keep:
    case True{}:
      Bytes.push(out, c)
    case False{}:
      Bytes.push(Bytes.push(Bytes.push(out, 37), hex.dig(U32.shrn(c, 4n))), hex.dig(U32.and(c, 15)))

def enc.go(s: Bytes(), out: Bytes()) -> Bytes():
  match s:
    case SNil{}:
      out
    case SCon{Chr{+c}, t}:
      enc.go(t, enc.one(out, c, unreserved(c)))

def pct.encode(s: Bytes()) -> Bytes():
  enc.go(s, "")

# The query
# =========
#
# a query's pairs, in order: split at '&', each at its first '=' (a
# name alone has the value ""), both form-decoded; empty pieces dropped
def qpair(+piece: Bytes()) -> Header:
  +i = Bytes.find_byte(piece, 0n, 61)
  Header{form.decode(String.take(piece, i)), form.decode(String.drop(piece, 1n+i))}

def qput(+piece: Bytes(), +rest: List<&2, Header>) -> List<&2, Header>:
  Bool.pick(List<&2, Header>, String.is_empty(piece), rest, Con{qpair(piece), rest})

def qat(cut: Bool, +s: Bytes(), +i: Nat, go: Bytes() -> List<&2, Header>) -> List<&2, Header>:
  match cut:
    case True{}:
      qput(String.take(s, i), go(String.drop(s, 1n+i)))
    case False{}:
      qput(s, Nil{})

def qgo(k: Nat, +s: Bytes()) -> List<&2, Header>:
  match k:
    case 0n:
      Nil{}
    case 1n+j:
      +i = Bytes.find_byte(s, 0n, 38)
      qat(Nat.is_lt(i, Bytes.len(s)), s, i, t => qgo(j, t))

def query.pairs(+q: Bytes()) -> List<&2, Header>:
  qgo(Bytes.len(q), q)

# a query parameter of a request, decoded: the first one named k
def query.get(r: Request, k: Bytes()) -> Maybe<&2, Bytes()>:
  get.go(query.pairs(query(r)), k)

# Responses
# =========

# a body: bytes, or a file under a root, named by a request path (the
# engine's page: normalised, refused if it climbs out or names a
# dotfile, opened below the root with no link followed, sent by the
# kernel)
type Body is Data:
  BBody{bs: Bytes()}
  BFile{root: Bytes(), path: Bytes()}

type Response is Data:
  Response{status: U32, headers: List<&2, Header>, body: Body}

def status(r: Response) -> U32:
  match r:
    case Response{s, hs, b}:
      s

def resp.headers(r: Response) -> List<&2, Header>:
  match r:
    case Response{s, hs, b}:
      hs

# the body's bytes ("" for a file)
def resp.body(r: Response) -> Bytes():
  match r:
    case Response{s, hs, b}:
      match b:
        case BBody{bs}:
          bs
        case BFile{root, p}:
          ""

def resp.header(r: Response, n: Bytes()) -> Maybe<&2, Bytes()>:
  get(resp.headers(r), n)

# the response with the field n set to v
def with.header(r: Response, n: Bytes(), v: Bytes()) -> Response:
  match r:
    case Response{s, hs, b}:
      Response{s, set(hs, n, v), b}

def with.body(r: Response, bs: Bytes()) -> Response:
  match r:
    case Response{s, hs, b}:
      Response{s, hs, BBody{bs}}

def bytes(status: U32, ctype: Bytes(), body: Bytes()) -> Response:
  Response{status, [Header{"content-type", ctype}], BBody{body}}

def text(status: U32, body: Bytes()) -> Response:
  bytes(status, "text/plain; charset=utf-8", body)

def html(status: U32, body: Bytes()) -> Response:
  bytes(status, "text/html; charset=utf-8", body)

# a JSON text as it is (net/json.bend writes one from a value)
def json(status: U32, body: Bytes()) -> Response:
  bytes(status, "application/json", body)

def file(root: Bytes(), path: Bytes()) -> Response:
  Response{200, Nil{}, BFile{root, path}}

# The statuses a response may have without its line being computed:
# each code with its three digits and its reason, as they are written
type St is Data:
  St{code: U32, cd: Bytes(), why: Bytes()}

def statuses() -> List<&2, St>:
  [St{200, "200", "OK"}, St{201, "201", "Created"}, St{202, "202", "Accepted"}, St{204, "204", "No Content"},
   St{206, "206", "Partial Content"}, St{301, "301", "Moved Permanently"}, St{302, "302", "Found"},
   St{303, "303", "See Other"}, St{304, "304", "Not Modified"}, St{307, "307", "Temporary Redirect"},
   St{308, "308", "Permanent Redirect"}, St{400, "400", "Bad Request"}, St{401, "401", "Unauthorized"},
   St{403, "403", "Forbidden"}, St{404, "404", "Not Found"}, St{405, "405", "Method Not Allowed"},
   St{408, "408", "Request Timeout"}, St{409, "409", "Conflict"}, St{410, "410", "Gone"},
   St{411, "411", "Length Required"}, St{412, "412", "Precondition Failed"}, St{413, "413", "Content Too Large"},
   St{414, "414", "URI Too Long"}, St{415, "415", "Unsupported Media Type"}, St{416, "416", "Range Not Satisfiable"},
   St{422, "422", "Unprocessable Content"}, St{426, "426", "Upgrade Required"}, St{429, "429", "Too Many Requests"},
   St{431, "431", "Request Header Fields Too Large"}, St{500, "500", "Internal Server Error"},
   St{501, "501", "Not Implemented"}, St{502, "502", "Bad Gateway"}, St{503, "503", "Service Unavailable"},
   St{504, "504", "Gateway Timeout"}]

# (each walk stops at its hit: the rest is only asked for when needed)
def st.hit(eq: Bool, t: St, rest: Unit -> Maybe<&2, St>) -> Maybe<&2, St>:
  match eq:
    case True{}:
      Some{t}
    case False{}:
      rest(Unit{})

def st.find(ts: List<&2, St>, +c: U32) -> Maybe<&2, St>:
  match ts:
    case Nil{}:
      None{}
    case Con{t, r}:
      match t:
        case St{+k, cd, why}:
          st.hit(U32.is_eq(k, c), St{k, cd, why}, u => st.find(r, c))

# the three digits and the reason of a status
def st.of(+c: U32) -> St:
  Maybe.default(&2, St, st.find(statuses(), c), St{c, U32.show(c), "Status"})

def st.why(t: St) -> Bytes():
  match t:
    case St{k, cd, why}:
      why

def reason(+s: U32) -> Bytes():
  st.why(st.of(s))

# a status alone: its reason as a text body
def plain(+status: U32) -> Response:
  text(status, Bytes.append(Bytes.append(U32.show(status), Bytes.append(" ", reason(status))), "\n"))

# a redirect to loc: 301, 302, 303, 307 or 308
def redirect(status: U32, loc: Bytes()) -> Response:
  Response{status, [Header{"location", loc}], BBody{""}}

# a response for a handler to return
def reply(r: Response) -> IO(Response):
  IO.pure(Response, r)

# Writing a response
# ==================
#
# A response goes out as bend-proxy writes one (demos/io_proxy/core.bend's
# rsp.fin and rser): the status line, the handler's fields but the ones
# the framing owns, one Content-Length counted from the body (for HEAD
# the one GET would have sent, for 204 and 304 none), the connection's
# fate, the blank line, and the body unless the framing says none (HEAD,
# 204, 304). It is checked first (rvalid: a status from 200 to 599, field
# names of token bytes, values with no line end or control): a response
# that fails -- a value with a CR LF in it, a 1xx -- goes out as a 500,
# never as bytes a client could frame otherwise. respond_framed says a
# client reads back exactly the one response either way.

# the fields the framing owns, which a handler's are cut of (whatever
# their case; only a name of one of their lengths is lowercased to see)
def framing.low(+n: Bytes()) -> Bool:
  String.eq(n, "content-length") || String.eq(n, "transfer-encoding") || String.eq(n, "connection")

def framing.at(may: Bool, +n: Bytes()) -> Bool:
  match may:
    case True{}:
      framing.low(Eng.lows(n))
    case False{}:
      False{}

def framing(+n: Bytes()) -> Bool:
  +k = Bytes.len(n)
  framing.at(Nat.is_eq(k, 14n) || Nat.is_eq(k, 17n) || Nat.is_eq(k, 10n), n)

def wput(drop: Bool, f: Wr.Field, rest: List<&2, Wr.Field>) -> List<&2, Wr.Field>:
  match drop:
    case True{}:
      rest
    case False{}:
      Con{f, rest}

def wfields(hs: List<&2, Header>) -> List<&2, Wr.Field>:
  match hs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      match h:
        case Header{+n, v}:
          wput(framing(n), Wr.Field{n, v}, wfields(t))

# the length a HEAD answer carries: GET's, and none for 204 and 304
def hlen(+code: U32, +body: Bytes()) -> Bytes():
  Bool.pick(Bytes(), U32.is_eq(code, 204) || U32.is_eq(code, 304), "", Nat.show(Bytes.len(body)))

def rhead.st(t: St, fs: List<&2, Wr.Field>, hl: Bytes()) -> X.RHead:
  match t:
    case St{k, cd, why}:
      X.RHead{cd, why, fs, hl}

def rhead(+code: U32, hs: List<&2, Header>, +body: Bytes()) -> X.RHead:
  rhead.st(st.of(code), wfields(hs), hlen(code, body))

# The check, fast: a status line from the table, every field's name one
# the table below knows and its value of space and visible ASCII (one
# scan of it), and the length (bend-proxy's rok.len). It passes only
# where bend-proxy's rvalid passes (PROOF.bend's fast.sound), so a
# response it passes need not be checked the long way; one it does not
# is.
def known() -> List<&2, Bytes()>:
  ["content-type", "location", "cache-control", "set-cookie", "allow", "etag", "last-modified", "vary",
   "expires", "date", "server", "content-encoding", "content-disposition", "content-language",
   "accept-ranges", "link", "retry-after", "www-authenticate", "access-control-allow-origin",
   "access-control-allow-methods", "access-control-allow-headers", "x-content-type-options",
   "x-frame-options", "referrer-policy", "content-security-policy", "strict-transport-security",
   "cross-origin-opener-policy", "cross-origin-resource-policy", "x-request-id"]

def known.at(eq: Bool, rest: Unit -> Bool) -> Bool:
  match eq:
    case True{}:
      True{}
    case False{}:
      rest(Unit{})

def known.has(+n: Bytes(), ks: List<&2, Bytes()>) -> Bool:
  match ks:
    case Nil{}:
      False{}
    case Con{k, t}:
      known.at(String.eq(n, k), u => known.has(n, t))

def fields.fast(fs: List<&2, Wr.Field>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case Con{f, t}:
      match f:
        case Wr.Field{+n, +v}:
          (known.has(n, known()) && X.all.in(v, 32, 127)) && fields.fast(t)

def st.in.at(hit: Bool, +cd: Bytes(), +why: Bytes(), tc: Bytes(), tw: Bytes(), rest: Unit -> Bool) -> Bool:
  match hit:
    case True{}:
      known.at(String.eq(tc, cd) && String.eq(tw, why), rest)
    case False{}:
      rest(Unit{})

def st.in(ts: List<&2, St>, +c: U32, +cd: Bytes(), +why: Bytes()) -> Bool:
  match ts:
    case Nil{}:
      False{}
    case Con{t, r}:
      match t:
        case St{k, tc, tw}:
          st.in.at(U32.is_eq(k, c), cd, why, tc, tw, u => st.in(r, c, cd, why))

def enc.fast(+head: Bool, +code: U32, h: X.RHead, +body: Bytes()) -> Bool:
  match h:
    case X.RHead{+cd, +why, +fs, +hl}:
      st.in(statuses(), code, cd, why) && fields.fast(fs)
        && X.rok.len(head, X.rbodyless(head, code), X.rclen(head, X.rbodyless(head, code), hl, body), body)

def enc.check.at(f: Bool, +head: Bool, +code: U32, +h: X.RHead, +body: Bytes()) -> Bool:
  match f:
    case True{}:
      True{}
    case False{}:
      X.rvalid(head, code, X.rsp.fin(head, code, h, body))

# whether a response goes out as it is (else the 500 does)
def enc.check(+head: Bool, +code: U32, +h: X.RHead, +body: Bytes()) -> Bool:
  enc.check.at(enc.fast(head, code, h, body), head, code, h, body)

# the response written when a handler's cannot be
def e500.body() -> Bytes():
  "500 Internal Server Error\n"

def e500.head() -> X.RHead:
  X.RHead{"500", "Internal Server Error", [Wr.Field{"content-type", "text/plain; charset=utf-8"}], "26"}

def enc.pick(ok: Bool, +head: Bool, +code: U32, h: X.RHead, +body: Bytes(), +closing: Bool, +v10: Bool) -> Bytes():
  match ok:
    case True{}:
      X.reply(Some{X.rsp.fin(head, code, h, body)}, head, closing, v10)
    case False{}:
      X.reply(Some{X.rsp.fin(head, 500, e500.head(), e500.body())}, head, closing, v10)

def enc.of(+head: Bool, +code: U32, +h: X.RHead, +body: Bytes(), +closing: Bool, +v10: Bool) -> Bytes():
  enc.pick(enc.check(head, code, h, body), head, code, h, body, closing, v10)

# The bytes a response with a body goes out as: head says the request
# was HEAD, closing that the connection ends after it, v10 that the
# request was HTTP/1.0 (kept alive, it is told so).
def write(+head: Bool, +closing: Bool, +v10: Bool, +code: U32, hs: List<&2, Header>, +body: Bytes()) -> Bytes():
  enc.of(head, code, rhead(code, hs, body), body, closing, v10)

# A file's head: its status line and type, the handler's fields, and
# the length and the connection's fate the writer adds (wire/loop.bend's
# fhead, after fstat); the type is the engine's for the file's extension.
def fhead.fields(fs: List<&2, Wr.Field>, acc: Bytes()) -> Bytes():
  match fs:
    case Nil{}:
      acc
    case Con{f, t}:
      match f:
        case Wr.Field{n, v}:
          fhead.fields(t, Bytes.concat([acc, n, ": ", v, "\r\n"]))

def fields.names(fs: List<&2, Wr.Field>) -> List<&2, Bytes()>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{f, t}:
      match f:
        case Wr.Field{n, v}:
          Con{Eng.lows(n), fields.names(t)}

def fhead.ok(+fs: List<&2, Wr.Field>) -> Bool:
  X.rok.fields(fs) && Bool.not(X.in.names("content-type", fields.names(fs)))

# the engine's head for the file's type, "HTTP/1.1 200 OK\r\ncontent-type:
# T\r\ncontent-length: ", with the handler's fields before its length
# (only fields the check passes; any other set is dropped whole)
def fhead.pre(+pre: Bytes(), hs: List<&2, Header>) -> Bytes():
  +fs = wfields(hs)
  +n = Bytes.len(pre)
  Bool.pick(Bytes(), fhead.ok(fs),
    Bytes.concat([String.take(pre, Nat.sub(n, 16n)), fhead.fields(fs, ""), "content-length: "]), pre)
