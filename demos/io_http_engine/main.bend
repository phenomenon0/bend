# HTTP/1.1 engine: a streaming request parser, a router and a server,
# all in Bend. The parser is the point. It is one structural walk over
# whatever bytes a socket hands over, with no lookahead, no buffering
# of the head and no re-scanning: the whole reader state rides in one
# P node, so a head split across three recvs parses exactly like a head
# that arrives whole, and a chunk holding three pipelined requests
# yields three requests in that one walk.
#
# Bend's loops cannot exit early: a recursive call must shrink a matched
# argument, so a machine that stopped at the blank line would still have
# to walk the rest of the buffer rebuilding a dead state. Rather than
# fight that, the machine never stops. Completing a message emits it and
# rolls straight into the next one, which is what a pipelining parser
# should do anyway. The shape Bend forces is the shape the protocol
# wants.
#
# What it accepts is deliberately small, because a framing disagreement
# is how requests get smuggled: HTTP/1.1 only, Content-Length only, that
# length all digits, and no Transfer-Encoding at all. Everything else is
# refused, and Bad{} is never left. LAWS.bend states those as laws and
# PROOF.bend proves them.
#
# Every byte on the wire is a byte. TCP.recv and TCP.send carry String,
# and a String is decoded as UTF-8, so a body that is not text comes
# back as one U+FFFD per ill-formed byte -- three bytes out for one in,
# while Content-Length still says one. That is a framing break, not a
# cost, so this engine reads List<&2, U32> through TCP.poll_bytes and
# writes Bytes, one packed block, through TCP.send_buf: every reply is
# built as Bytes and goes out as it lies in the heap.
#
#   bend demos/io_http_engine/main.bend -o httpd && ./httpd
#   curl -i http://127.0.0.1:8080/health
import Base
import ./ws.bend as Ws

# Bytes
# =====

# The head grammar branches on four delimiters; everything else is a
# token byte, so one class per delimiter and one for the rest.
type Cls is Data:
  KSp{}
  KCr{}
  KLf{}
  KCo{}
  KCh{}

def cls.go(sp: Bool, cr: Bool, lf: Bool, co: Bool) -> Cls:
  match sp cr lf co:
    case True{} _ _ _:
      KSp{}
    case _ True{} _ _:
      KCr{}
    case _ _ True{} _:
      KLf{}
    case _ _ _ True{}:
      KCo{}
    case _ _ _ _:
      KCh{}

def cls(+c: U32) -> Cls:
  cls.go(U32.is_eq(c, 32), U32.is_eq(c, 13), U32.is_eq(c, 10), U32.is_eq(c, 58))

# Field names are case-insensitive, so they hash lowercased.
def lower.go(+c: U32, up: Bool) -> U32:
  match up:
    case True{}:
      (c + 32 : U32)
    case False{}:
      c

def lower(+c: U32) -> U32:
  lower.go(c, U32.is_le(65, c) && U32.is_le(c, 90))

def digit(+c: U32) -> Bool:
  U32.is_le(48, c) && U32.is_le(c, 57)

# The reader's unit. A byte list, one cell per byte, is what the socket
# hands over; replies go back as Bytes.
def cat(a: List<&2, U32>, b: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, a, b)

def rev(a: List<&2, U32>) -> List<&2, U32>:
  List.reverse(&2, U32, a)

# An ASCII literal as bytes. Written text stays readable in the source
# and becomes bytes here; a code point past 255 is not a byte and
# TCP.send_buf refuses it rather than re-encoding it.
def bytes(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{Chr{c}, t}:
      Con{c, bytes(t)}

# Byte-list equality, with no early exit: a route match reads every
# byte of the shorter list whatever the first one says.
def beq(a: List<&2, U32>, b: List<&2, U32>, acc: Bool) -> Bool:
  match a b:
    case Nil{} Nil{}:
      acc
    case Nil{} Con{y, u}:
      False{}
    case Con{x, t} Nil{}:
      False{}
    case Con{x, t} Con{y, u}:
      beq(t, u, acc && U32.is_eq(x, y))

# FNV-1a over a token, one byte at a time. A field name is recognised
# by its hash, so a name is never built, stored or compared as bytes.
def fnv(h: U32, c: U32) -> U32:
  (U32.xor(h, c) * 16777619 : U32)

def fnv.new() -> U32:
  2166136261

def hash.version() -> U32:
  4120326248

def hash.content_length() -> U32:
  1308181789

def hash.transfer_encoding() -> U32:
  3719590988

def hash.connection() -> U32:
  951688921

def hash.close() -> U32:
  667630371

def hash.upgrade() -> U32:
  3700935799

def hash.sec_websocket_key() -> U32:
  3400920102

def hash.websocket() -> U32:
  3470555248

def m.get() -> U32:
  2531704439

def m.head() -> U32:
  811237315

# Requests
# ========

# A parsed message: the method as a hash, the target and body as bytes,
# and whether the peer asked to close.
type Req is Data:
  Req{meth: U32, path: List<&2, U32>, body: List<&2, U32>, close: Bool,
    ws: Bool, key: List<&2, U32>}

def req.close(r: Req) -> Bool:
  match r:
    case Req{meth, path, body, close, ws, key}:
      close

# The fields of the message being read. It is rebuilt only when a token
# closes, so an ordinary byte leaves it untouched and shares it.
# What a message has said about becoming a WebSocket. Plain{} is the
# answer for every request that never names one of the three headers,
# and it carries no fields, so the ordinary path allocates nothing for
# an upgrade that is not happening.
type Up is Data:
  Plain{}
  Asks{key: List<&2, U32>, up: Bool, cu: Bool}

def up.key(u: Up, k: List<&2, U32>) -> Up:
  match u:
    case Plain{}:
      Asks{k, False{}, False{}}
    case Asks{key, up, cu}:
      Asks{k, up, cu}

def up.up(u: Up, v: Bool) -> Up:
  match u:
    case Plain{}:
      Asks{Nil{}, v, False{}}
    case Asks{key, up, cu}:
      Asks{key, v, cu}

def up.cu(u: Up, v: Bool) -> Up:
  match u:
    case Plain{}:
      Asks{Nil{}, False{}, v}
    case Asks{key, up, cu}:
      Asks{key, up, v}

def has(k: List<&2, U32>) -> Bool:
  match k:
    case Nil{}:
      False{}
    case Con{h, t}:
      True{}

# a message asks to become a WebSocket when it carried Upgrade:
# websocket, Connection: Upgrade and a key
def up.asked(u: Up) -> Bool & List<&2, U32>:
  match u:
    case Plain{}:
      (False{}, Nil{})
    case Asks{+key, up, cu}:
      (up && cu && has(key), key)

type Pend is Data:
  Pend{meth: U32, path: List<&2, U32>, clen: U32, close: Bool, te: Bool,
    ws: Up}

def pend.new() -> Pend:
  Pend{0, Nil{}, 0, False{}, False{}, Plain{}}

# a new method token starts a new message, so the rest resets with it
def pend.meth(pd: Pend, h: U32) -> Pend:
  match pd:
    case Pend{meth, path, clen, close, te, ws}:
      Pend{h, Nil{}, 0, False{}, False{}, Plain{}}

def pend.path(pd: Pend, p: List<&2, U32>) -> Pend:
  match pd:
    case Pend{meth, path, clen, close, te, ws}:
      Pend{meth, p, clen, close, te, ws}

# A closed field, applied by name hash: a length, a connection token,
# or a Transfer-Encoding, which poisons the message rather than framing
# it a second way.
def pend.set.go(
  meth: U32, path: List<&2, U32>, clen: U32, close: Bool, te: Bool, ws: Up,
  v: U32, isc: Bool, cl: Bool, isl: Bool, ist: Bool
) -> Pend:
  match isc isl ist:
    case True{} _ _:
      Pend{meth, path, clen, cl, te, ws}
    case _ True{} _:
      Pend{meth, path, v, close, te, ws}
    case _ _ True{}:
      Pend{meth, path, clen, close, True{}, ws}
    case _ _ _:
      Pend{meth, path, clen, close, te, ws}

def pend.set(pd: Pend, v: U32, isc: Bool, cl: Bool, isl: Bool, ist: Bool) -> Pend:
  match pd:
    case Pend{meth, path, clen, close, te, ws}:
      pend.set.go(meth, path, clen, close, te, ws, v, isc, cl, isl, ist)

def pend.poison(pd: Pend) -> Pend:
  match pd:
    case Pend{meth, path, clen, close, te, ws}:
      Pend{meth, path, clen, close, True{}, ws}

def pend.len(pd: Pend) -> Pend & U32:
  match pd:
    case Pend{meth, path, +clen, close, te, ws}:
      (Pend{meth, path, clen, close, te, ws}, clen)

def pend.te_if(pd: Pend, is_te: Bool) -> Pend:
  match is_te:
    case True{}:
      pend.poison(pd)
    case False{}:
      pd

def pend.te(pd: Pend) -> Pend & Bool:
  match pd:
    case Pend{meth, path, clen, close, +te, ws}:
      (Pend{meth, path, clen, close, te, ws}, te)

# the upgrade state, changed as each of its headers closes
def pend.up(pd: Pend, v: Bool) -> Pend:
  match pd:
    case Pend{meth, path, clen, close, te, ws}:
      Pend{meth, path, clen, close, te, up.up(ws, v)}

def pend.cu(pd: Pend, v: Bool) -> Pend:
  match pd:
    case Pend{meth, path, clen, close, te, ws}:
      Pend{meth, path, clen, close, te, up.cu(ws, v)}

def pend.key(pd: Pend, k: List<&2, U32>) -> Pend:
  match pd:
    case Pend{meth, path, clen, close, te, ws}:
      Pend{meth, path, clen, close, te, up.key(ws, k)}

def pend.req.go(
  meth: U32, path: List<&2, U32>, body: List<&2, U32>, close: Bool,
  asked: Bool & List<&2, U32>
) -> Req:
  (ws, key) = asked
  Req{meth, path, body, close, ws, key}

def pend.req(pd: Pend, body: List<&2, U32>) -> Req:
  match pd:
    case Pend{meth, path, clen, close, te, ws}:
      pend.req.go(meth, path, body, close, up.asked(ws))

# The reader
# ==========

# InM  the method token            Lin  at the start of a line
# InT  the target token            InN  a field name
# InV  the version token           Ows  the space after its colon
# CrM  a CR inside the head        InL  a Content-Length value
# InLc a Connection value          InLx any other value, skipped
# InLu an Upgrade value             InLk a Sec-WebSocket-Key value
# CrL  the CR of the blank line    Bod  the body, r bytes to go
# Bad  the grammar broke; absorbing, and never left
type St is Data:
  InM{h: U32}
  InT{p: List<&2, U32>}
  InV{h: U32}
  CrM{}
  Lin{}
  InN{h: U32}
  Ows{n: U32}
  InL{v: U32, d: Bool}
  InLc{g: U32}
  InLx{}
  InLu{g: U32}
  InLk{k: List<&2, U32>}
  CrL{}
  Bod{r: U32, b: List<&2, U32>}
  Bad{}

# The whole reader: where the machine is, the message it is filling,
# and the messages it has finished, newest first.
type P is Data:
  P{st: St, pd: Pend, out: List<&2, Req>}

def p.new() -> P:
  P{InM{fnv.new()}, pend.new(), Nil{}}

# a completed message rolls the machine straight into the next one
def emit(pd: Pend, body: List<&2, U32>, out: List<&2, Req>) -> P:
  P{InM{fnv.new()}, pend.new(), pend.req(pd, body) <> out}

# the version token must read exactly HTTP/1.1
def step.ver(h: U32, pd: Pend, out: List<&2, Req>, ok: Bool) -> P:
  match ok:
    case True{}:
      P{CrM{}, pd, out}
    case False{}:
      P{Bad{}, pd, out}

# a Content-Length value closes: it counts only if every byte was a
# digit, so "5x" is not a length and cannot disagree with anything
def step.clen(v: U32, d: Bool, pd: Pend, out: List<&2, Req>) -> P:
  P{CrM{}, pend.set(pd, v, False{}, False{}, d, False{}), out}

# a Connection value closes
def step.conn(+g: U32, pd: Pend, out: List<&2, Req>) -> P:
  P{CrM{}, pend.cu(pend.set(pd, 0, True{}, U32.is_eq(g, hash.close()), False{},
    False{}), U32.is_eq(g, hash.upgrade())), out}

# an Upgrade value closes: it named websocket or it did not
def step.up(g: U32, pd: Pend, out: List<&2, Req>) -> P:
  P{CrM{}, pend.up(pd, U32.is_eq(g, hash.websocket())), out}

# a Sec-WebSocket-Key value closes, kept as it came
def step.key(k: List<&2, U32>, pd: Pend, out: List<&2, Req>) -> P:
  P{CrM{}, pend.key(pd, rev(k)), out}

# the first byte of a value picks the scanner the field needs, and
# every other field gets the one that does no work per byte at all
def step.val.go(
  +c: U32, pd: Pend, out: List<&2, Req>, isl: Bool, isc: Bool, isu: Bool, isk: Bool
) -> P:
  match isl isc isu isk:
    case True{} _ _ _:
      P{InL{(c - 48 : U32), digit(c)}, pd, out}
    case _ True{} _ _:
      P{InLc{fnv(fnv.new(), lower(c))}, pd, out}
    case _ _ True{} _:
      P{InLu{fnv(fnv.new(), lower(c))}, pd, out}
    case _ _ _ True{}:
      P{InLk{[c]}, pd, out}
    case _ _ _ _:
      P{InLx{}, pd, out}

def step.val(+n: U32, +c: U32, pd: Pend, out: List<&2, Req>) -> P:
  step.val.go(c, pd, out, U32.is_eq(n, hash.content_length()),
    U32.is_eq(n, hash.connection()), U32.is_eq(n, hash.upgrade()),
    U32.is_eq(n, hash.sec_websocket_key()))

# the most body this engine will hold for one message. A head that
# announces more is refused as it completes, before a byte of the body
# is read, so an announced length is never a way to make it allocate.
def body.cap() -> U32:
  1048576

def step.head.on(pd: Pend, n: U32, out: List<&2, Req>, z: Bool, big: Bool) -> P:
  match z big:
    case True{} _:
      emit(pd, Nil{}, out)
    case False{} True{}:
      P{Bad{}, pd, out}
    case False{} False{}:
      P{Bod{n, Nil{}}, pd, out}

def step.head.len(pn: Pend & U32, out: List<&2, Req>) -> P:
  (pd, +n) = pn
  step.head.on(pd, n, out, U32.is_zero(n), U32.is_lt(body.cap(), n))

def step.head.go(pd: Pend, te: Bool, out: List<&2, Req>) -> P:
  match te:
    case True{}:
      P{Bad{}, pd, out}
    case False{}:
      step.head.len(pend.len(pd), out)

def step.head.te(pt: Pend & Bool, out: List<&2, Req>) -> P:
  (pd, te) = pt
  step.head.go(pd, te, out)

# the blank line closes the head: refuse a message that named a second
# framing, emit a bodyless one, or start counting the body down
def step.head(pd: Pend, out: List<&2, Req>) -> P:
  step.head.te(pend.te(pd), out)

def step.body.go(
  r: U32, b: List<&2, U32>, c: U32, pd: Pend, out: List<&2, Req>, last: Bool
) -> P:
  match last:
    case True{}:
      emit(pd, rev(Con{c, b}), out)
    case False{}:
      P{Bod{(r - 1 : U32), Con{c, b}}, pd, out}

# one body byte: the last one emits the message, the rest accumulate
def step.body(+r: U32, b: List<&2, U32>, c: U32, pd: Pend, out: List<&2, Req>) -> P:
  step.body.go(r, b, c, pd, out, U32.is_eq(r, 1))

# the machine: one classified byte moves it once. A token state grows
# its hash or its bytes until its delimiter arrives; the delimiter
# closes the token into the pending message and hands over.
def step.at(st: St, k: Cls, +c: U32, pd: Pend, out: List<&2, Req>) -> P:
  match st k:
    case InM{h} KSp{}:
      P{InT{Nil{}}, pend.meth(pd, h), out}
    case InM{h} _:
      P{InM{fnv(h, c)}, pd, out}
    case InT{p} KSp{}:
      P{InV{fnv.new()}, pend.path(pd, rev(p)), out}
    case InT{p} _:
      P{InT{Con{c, p}}, pd, out}
    case InV{+h} KCr{}:
      step.ver(h, pd, out, U32.is_eq(h, hash.version()))
    case InV{h} _:
      P{InV{fnv(h, c)}, pd, out}
    case CrM{} KLf{}:
      P{Lin{}, pd, out}
    case CrM{} _:
      P{Bad{}, pd, out}
    case Lin{} KCr{}:
      P{CrL{}, pd, out}
    case Lin{} _:
      P{InN{fnv(fnv.new(), lower(c))}, pd, out}
    case InN{+h} KCo{}:
      P{Ows{h}, pend.te_if(pd, U32.is_eq(h, hash.transfer_encoding())), out}
    case InN{h} _:
      P{InN{fnv(h, lower(c))}, pd, out}
    case Ows{n} KSp{}:
      P{Ows{n}, pd, out}
    case Ows{n} KCr{}:
      P{CrM{}, pd, out}
    case Ows{n} _:
      step.val(n, c, pd, out)
    case InL{v, d} KCr{}:
      step.clen(v, d, pd, out)
    case InL{v, d} _:
      P{InL{(v * 10 + (c - 48) : U32), d && digit(c)}, pd, out}
    case InLc{g} KCr{}:
      step.conn(g, pd, out)
    case InLc{g} _:
      P{InLc{fnv(g, lower(c))}, pd, out}
    case InLx{} KCr{}:
      P{CrM{}, pd, out}
    case InLx{} _:
      P{InLx{}, pd, out}
    case InLu{g} KCr{}:
      step.up(g, pd, out)
    case InLu{g} _:
      P{InLu{fnv(g, lower(c))}, pd, out}
    case InLk{k} KCr{}:
      step.key(k, pd, out)
    case InLk{k} _:
      P{InLk{Con{c, k}}, pd, out}
    case CrL{} KLf{}:
      step.head(pd, out)
    case CrL{} _:
      P{Bad{}, pd, out}
    case Bod{r, b} _:
      step.body(r, b, c, pd, out)
    case Bad{} _:
      P{Bad{}, pd, out}

def step(p: P, +c: U32) -> P:
  match p:
    case P{st, pd, out}:
      step.at(st, cls(c), c, pd, out)

# feed: one structural walk over a chunk. The reader state that comes
# out is the reader state to feed the next chunk, so a message split
# anywhere parses exactly like a message that arrived whole.
def feed(s: List<&2, U32>, p: P) -> P:
  match s:
    case Nil{}:
      p
    case Con{c, t}:
      feed(t, step(p, c))

# the finished messages, oldest first, and the reader with them cleared
def p.take(p: P) -> P & List<&2, Req>:
  match p:
    case P{st, pd, out}:
      (P{st, pd, Nil{}}, List.reverse(&2, Req, out))

def p.dead.at(st: St, pd: Pend, out: List<&2, Req>) -> P & Bool:
  match st:
    case InM{h}:
      (P{InM{h}, pd, out}, False{})
    case InT{p}:
      (P{InT{p}, pd, out}, False{})
    case InV{h}:
      (P{InV{h}, pd, out}, False{})
    case CrM{}:
      (P{CrM{}, pd, out}, False{})
    case Lin{}:
      (P{Lin{}, pd, out}, False{})
    case InN{h}:
      (P{InN{h}, pd, out}, False{})
    case Ows{n}:
      (P{Ows{n}, pd, out}, False{})
    case InL{v, d}:
      (P{InL{v, d}, pd, out}, False{})
    case InLc{g}:
      (P{InLc{g}, pd, out}, False{})
    case InLx{}:
      (P{InLx{}, pd, out}, False{})
    case InLu{g}:
      (P{InLu{g}, pd, out}, False{})
    case InLk{k}:
      (P{InLk{k}, pd, out}, False{})
    case CrL{}:
      (P{CrL{}, pd, out}, False{})
    case Bod{r, b}:
      (P{Bod{r, b}, pd, out}, False{})
    case Bad{}:
      (P{Bad{}, pd, out}, True{})

# whether the grammar broke, with the reader handed back
def p.dead(p: P) -> P & Bool:
  match p:
    case P{st, pd, out}:
      p.dead.at(st, pd, out)

# Routes
# ======

# The reply to one request: a status line, the headers this engine
# always sends, a blank line, then the body. Content-Length is always
# written, so every reply is framed by length and the connection stays
# usable. A reply is Bytes: one packed block that TCP.send_buf writes as
# it lies, where a List<&2, U32> was a cell per byte walked into a
# buffer on every send.
def reply(status: Bytes(), ctype: Bytes(), +body: Bytes()) -> Bytes():
  Bytes.concat(["HTTP/1.1 ", status, "\r\ncontent-type: ", ctype,
    "\r\ncontent-length: ", Nat.show(Bytes.len(body)),
    "\r\nconnection: keep-alive\r\n\r\n", body])

# A reply whose body is fixed has fixed bytes, so it is written out as
# a literal instead of being rebuilt per request: a literal is a static
# block, sent without a copy. LAWS.bend says each one equals reply()
# called with the arguments named beside it, and the checker refuses
# the engine if an edit ever makes that false.
def resp.health() -> Bytes():
  "HTTP/1.1 200 OK\r\ncontent-type: application/json\r\ncontent-length: 11\r\nconnection: keep-alive\r\n\r\n{\"ok\":true}"

def resp.root() -> Bytes():
  "HTTP/1.1 200 OK\r\ncontent-type: text/plain\r\ncontent-length: 10\r\nconnection: keep-alive\r\n\r\nbend-http\n"

def resp.missing() -> Bytes():
  "HTTP/1.1 404 Not Found\r\ncontent-type: text/plain\r\ncontent-length: 9\r\nconnection: keep-alive\r\n\r\nno route\n"

def resp.method() -> Bytes():
  "HTTP/1.1 405 Method Not Allowed\r\ncontent-type: text/plain\r\ncontent-length: 10\r\nallow: GET, HEAD\r\nconnection: keep-alive\r\n\r\nno method\n"

def resp.bad() -> Bytes():
  "HTTP/1.1 400 Bad Request\r\ncontent-type: text/plain\r\ncontent-length: 12\r\nconnection: keep-alive\r\n\r\nbad request\n"

# An event stream: the head goes out once, then one event at a time on
# the engine's own schedule, with nothing more read from the peer. This
# is the shape that holds a connection open -- an agent session, a token
# stream, a live feed -- and it is what this engine is actually good at.
def sse.head() -> Bytes():
  "HTTP/1.1 200 OK\r\ncontent-type: text/event-stream\r\ncache-control: no-cache\r\nconnection: keep-alive\r\n\r\n"

def sse.event(n: U32) -> Bytes():
  Bytes.concat(["event: tick\ndata: ", U32.show(n), "\n\n"])

# how many events a stream sends before it closes, and how long it
# waits between them. Both are bounds, not settings: the count is what
# makes the streaming loop terminate without @unsafe.
def sse.count() -> U32:
  1000000

def sse.gap() -> U32:
  1000

# Configuration
# =============

# The paths to a certificate and its key. They arrive one flag at a
# time, so each half waits for the other with an empty path standing
# for "not yet", and a pair still half empty when the arguments run out
# is refused rather than served in the clear.
type Pem is Data:
  Pem{cert: List<&2, U32>, key: List<&2, U32>}

def pem.cert(m: Maybe<&2, Pem>, p: List<&2, U32>) -> Maybe<&2, Pem>:
  match m:
    case None{}:
      Some{Pem{p, Nil{}}}
    case Some{pem}:
      match pem:
        case Pem{cert, key}:
          Some{Pem{p, key}}

def pem.key(m: Maybe<&2, Pem>, p: List<&2, U32>) -> Maybe<&2, Pem>:
  match m:
    case None{}:
      Some{Pem{Nil{}, p}}
    case Some{pem}:
      match pem:
        case Pem{cert, key}:
          Some{Pem{cert, p}}

# What the binary was started with: the port, the directory static
# files come from if any, and whether to log. The route table is built
# from it once, in main, and every connection shares that one table.
type Cfg is Data:
  Cfg{port: U32, root: Maybe<&2, List<&2, U32>>, log: Bool, idle: U32, conns: U32,
    grace: U32, shared: Bool, pem: Maybe<&2, Pem>}

def cfg.new() -> Cfg:
  Cfg{8080, None{}, False{}, 10000, 1024, 5000, False{}, None{}}

def cfg.port(c: Cfg) -> U32:
  match c:
    case Cfg{port, root, log, idle, conns, grace, shared, pem}:
      port

# how long a connection may be silent, in ms, before it is dropped
def cfg.idle(c: Cfg) -> U32:
  match c:
    case Cfg{port, root, log, idle, conns, grace, shared, pem}:
      idle

def cfg.root(c: Cfg) -> List<&2, U32>:
  match c:
    case Cfg{port, root, log, idle, conns, grace, shared, pem}:
      Maybe.default(&2, List<&2, U32>, root, bytes("."))

def cfg.set_port(c: Cfg, n: U32) -> Cfg:
  match c:
    case Cfg{port, root, log, idle, conns, grace, shared, pem}:
      Cfg{n, root, log, idle, conns, grace, shared, pem}

# the most connections open at once; past it, accepting waits
def cfg.conns(c: Cfg) -> U32:
  match c:
    case Cfg{port, root, log, idle, conns, grace, shared, pem}:
      conns

# how long open connections get to finish after a stop is asked, in ms
def cfg.grace(c: Cfg) -> U32:
  match c:
    case Cfg{port, root, log, idle, conns, grace, shared, pem}:
      grace

def cfg.set_conns(c: Cfg, n: U32) -> Cfg:
  match c:
    case Cfg{port, root, log, idle, conns, grace, shared, pem}:
      Cfg{port, root, log, idle, n, grace, shared, pem}

def cfg.set_grace(c: Cfg, n: U32) -> Cfg:
  match c:
    case Cfg{port, root, log, idle, conns, grace, shared, pem}:
      Cfg{port, root, log, idle, conns, n, shared, pem}

# whether the port is shared with other copies of this server
def cfg.log(c: Cfg) -> Bool:
  match c:
    case Cfg{port, root, log, idle, conns, grace, shared, pem}:
      log

# the certificate and key a TLS listener needs, if the server was given
# a pair; the half-given pair is refused when the arguments are read
def cfg.pem(c: Cfg) -> Maybe<&2, Pem>:
  match c:
    case Cfg{port, root, log, idle, conns, grace, shared, pem}:
      pem

def cfg.set_cert(c: Cfg, p: List<&2, U32>) -> Cfg:
  match c:
    case Cfg{port, root, log, idle, conns, grace, shared, pem}:
      Cfg{port, root, log, idle, conns, grace, shared, pem.cert(pem, p)}

def cfg.set_key(c: Cfg, p: List<&2, U32>) -> Cfg:
  match c:
    case Cfg{port, root, log, idle, conns, grace, shared, pem}:
      Cfg{port, root, log, idle, conns, grace, shared, pem.key(pem, p)}

def cfg.shared(c: Cfg) -> Bool:
  match c:
    case Cfg{port, root, log, idle, conns, grace, shared, pem}:
      shared

def cfg.set_shared(c: Cfg) -> Cfg:
  match c:
    case Cfg{port, root, log, idle, conns, grace, shared, pem}:
      Cfg{port, root, log, idle, conns, grace, True{}, pem}

def cfg.set_idle(c: Cfg, n: U32) -> Cfg:
  match c:
    case Cfg{port, root, log, idle, conns, grace, shared, pem}:
      Cfg{port, root, log, n, conns, grace, shared, pem}

def cfg.set_root(c: Cfg, dir: List<&2, U32>) -> Cfg:
  match c:
    case Cfg{port, root, log, idle, conns, grace, shared, pem}:
      Cfg{port, Some{dir}, log, idle, conns, grace, shared, pem}

def cfg.set_log(c: Cfg) -> Cfg:
  match c:
    case Cfg{port, root, log, idle, conns, grace, shared, pem}:
      Cfg{port, root, True{}, idle, conns, grace, shared, pem}

# a non-empty run of decimal digits
def digits.go(bs: List<&2, U32>, ok: Bool) -> Bool:
  match bs:
    case Nil{}:
      ok
    case Con{+c, t}:
      digits.go(t, ok && U32.is_le(48, c) && U32.is_le(c, 57))

def digits(bs: List<&2, U32>) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case Con{c, t}:
      digits.go(Con{c, t}, True{})

def u32.of(bs: List<&2, U32>, acc: U32) -> U32:
  match bs:
    case Nil{}:
      acc
    case Con{c, t}:
      u32.of(t, ((acc * 10 : U32) + (c - 48 : U32) : U32))

# bytes back to text, for the effects that take a String
def text(bs: List<&2, U32>) -> String:
  match bs:
    case Nil{}:
      SNil{}
    case Con{c, t}:
      SCon{Chr{c}, text(t)}

# The argument reader has the shape of the request reader: a state fed
# one argument at a time, and a step that does not recurse.
type Want is Data:
  Flag{}
  PortOf{}
  RootOf{}
  IdleOf{}
  ConnsOf{}
  GraceOf{}
  CertOf{}
  KeyOf{}
  Wrong{why: List<&2, U32>}

type Args is Data:
  Args{cfg: Cfg, want: Want}

# the flags that take a path, split out so the one match below stays
# readable rather than nine deep
def args.pem(c: Cfg, +a: List<&2, U32>, cert: Bool, key: Bool) -> Args:
  match cert key:
    case True{} _:
      Args{c, CertOf{}}
    case False{} True{}:
      Args{c, KeyOf{}}
    case False{} False{}:
      Args{c, Wrong{cat(bytes("unknown flag: "), a)}}

def args.flag(
  c: Cfg, +a: List<&2, U32>, log: Bool, port: Bool, root: Bool, idle: Bool,
  conns: Bool, grace: Bool, shared: Bool
) -> Args:
  match log port root idle conns grace shared:
    case True{} _ _ _ _ _ _:
      Args{cfg.set_log(c), Flag{}}
    case False{} True{} _ _ _ _ _:
      Args{c, PortOf{}}
    case False{} False{} True{} _ _ _ _:
      Args{c, RootOf{}}
    case False{} False{} False{} True{} _ _ _:
      Args{c, IdleOf{}}
    case False{} False{} False{} False{} True{} _ _:
      Args{c, ConnsOf{}}
    case False{} False{} False{} False{} False{} True{} _:
      Args{c, GraceOf{}}
    case False{} False{} False{} False{} False{} False{} True{}:
      Args{cfg.set_shared(c), Flag{}}
    case False{} False{} False{} False{} False{} False{} False{}:
      args.pem(c, a, beq(a, bytes("--tls-cert"), True{}),
        beq(a, bytes("--tls-key"), True{}))

def args.num(c: Cfg, a: List<&2, U32>, ok: Bool) -> Args:
  match ok:
    case True{}:
      Args{cfg.set_port(c, u32.of(a, 0)), Flag{}}
    case False{}:
      Args{c, Wrong{cat(bytes("not a port: "), a)}}

def args.ms(c: Cfg, a: List<&2, U32>, ok: Bool) -> Args:
  match ok:
    case True{}:
      Args{cfg.set_idle(c, u32.of(a, 0)), Flag{}}
    case False{}:
      Args{c, Wrong{cat(bytes("not a number of ms: "), a)}}

def args.grace(c: Cfg, a: List<&2, U32>, ok: Bool) -> Args:
  match ok:
    case True{}:
      Args{cfg.set_grace(c, u32.of(a, 0)), Flag{}}
    case False{}:
      Args{c, Wrong{cat(bytes("not a number of ms: "), a)}}

# a connection limit of zero would let nothing in, so it is refused
def args.conns(c: Cfg, a: List<&2, U32>, ok: Bool) -> Args:
  match ok:
    case True{}:
      Args{cfg.set_conns(c, u32.of(a, 0)), Flag{}}
    case False{}:
      Args{c, Wrong{cat(bytes("not a count of connections: "), a)}}

def args.feed(st: Args, +a: List<&2, U32>) -> Args:
  match st:
    case Args{c, want}:
      match want:
        case Flag{}:
          args.flag(c, a, beq(a, bytes("--log"), True{}), beq(a, bytes("--port"), True{}),
            beq(a, bytes("--root"), True{}), beq(a, bytes("--idle-ms"), True{}),
            beq(a, bytes("--max-conns"), True{}), beq(a, bytes("--grace-ms"), True{}),
            beq(a, bytes("--shared"), True{}))
        case PortOf{}:
          args.num(c, a, digits(a))
        case RootOf{}:
          Args{cfg.set_root(c, a), Flag{}}
        case IdleOf{}:
          args.ms(c, a, digits(a))
        case ConnsOf{}:
          args.conns(c, a, digits(a) && Bool.not(U32.is_zero(u32.of(a, 0))))
        case GraceOf{}:
          args.grace(c, a, digits(a))
        case CertOf{}:
          Args{cfg.set_cert(c, a), Flag{}}
        case KeyOf{}:
          Args{cfg.set_key(c, a), Flag{}}
        case Wrong{why}:
          Args{c, Wrong{why}}

def args.read(xs: List<String>, st: Args) -> Args:
  match xs:
    case Nil{}:
      st
    case Con{a, t}:
      args.read(t, args.feed(st, bytes(a)))

# A certificate without its key, or a key without its certificate, is
# refused: the one thing a server must never do with a half-given pair
# is fall back to serving in the clear.
def args.pair.go(c: Cfg, cert: Bool, key: Bool) -> IO(Cfg):
  match cert key:
    case False{} _:
      IO.die(Cfg, 2, "--tls-cert is missing")
    case True{} False{}:
      IO.die(Cfg, 2, "--tls-key is missing")
    case True{} True{}:
      do IO<Cfg>:
        return c

def args.pair(c: Cfg, m: Maybe<&2, Pem>) -> IO(Cfg):
  match m:
    case None{}:
      do IO<Cfg>:
        return c
    case Some{pem}:
      match pem:
        case Pem{+cert, +key}:
          args.pair.go(c, has(cert), has(key))

def args.done(st: Args) -> IO(Cfg):
  match st:
    case Args{+c, want}:
      match want:
        case Flag{}:
          args.pair(c, cfg.pem(c))
        case PortOf{}:
          IO.die(Cfg, 2, "--port needs a number")
        case RootOf{}:
          IO.die(Cfg, 2, "--root needs a directory")
        case IdleOf{}:
          IO.die(Cfg, 2, "--idle-ms needs a number")
        case ConnsOf{}:
          IO.die(Cfg, 2, "--max-conns needs a count")
        case GraceOf{}:
          IO.die(Cfg, 2, "--grace-ms needs a number")
        case CertOf{}:
          IO.die(Cfg, 2, "--tls-cert needs a path")
        case KeyOf{}:
          IO.die(Cfg, 2, "--tls-key needs a path")
        case Wrong{why}:
          IO.die(Cfg, 2, text(why))

# Replies by size
# ===============

# A reply head for a body of n bytes, and the reply around a body whose
# size is already known, as a file's is. reply() measures its body;
# these do not. The type is a byte list from the mime table.
def reply.n.head(status: Bytes(), ct: List<&2, U32>, n: U32) -> Bytes():
  Bytes.concat(["HTTP/1.1 ", status, "\r\ncontent-type: ", Bytes.from_list(ct),
    "\r\ncontent-length: ", U32.show(n), "\r\nconnection: keep-alive\r\n\r\n"])

def reply.n(status: Bytes(), ct: List<&2, U32>, n: U32, body: Bytes()) -> Bytes():
  Bytes.append(reply.n.head(status, ct, n), body)

# the 405 names the methods that would have worked
def reply.allow(status: Bytes(), ct: Bytes(), +body: Bytes()) -> Bytes():
  Bytes.concat(["HTTP/1.1 ", status, "\r\ncontent-type: ", ct,
    "\r\ncontent-length: ", Nat.show(Bytes.len(body)),
    "\r\nallow: GET, HEAD\r\nconnection: keep-alive\r\n\r\n", body])

# The head of a reply: its bytes through the blank line. HEAD answers
# with the head of what GET would have sent, so the two can never
# disagree about a length or a type. A reply with no blank line is all
# head.
def head.upto(+bs: Bytes(), m: Maybe<&2, Nat>) -> Bytes():
  match m:
    case None{}:
      bs
    case Some{i}:
      Bytes.slice(bs, 0n, Nat.add(i, 4n))

def head.of(+bs: Bytes()) -> Bytes():
  head.upto(bs, Bytes.find(bs, "\r\n\r\n"))

# Routes
# ======

# What a route does. The table is data, built from the configuration,
# so LAWS.bend can pin what the default table answers and that no two
# entries claim one path.
type Act is Data:
  Health{}
  Root{}
  Echo{}
  Events{}
  Live{}
  Files{}

# an entry: an exact path, or every path under it when prefix is set
type Route is Data:
  Route{path: List<&2, U32>, prefix: Bool, act: Act}

def routes.base() -> List<&2, Route>:
  [Route{bytes("/health"), False{}, Health{}},
   Route{bytes("/echo"), False{}, Echo{}},
   Route{bytes("/events"), False{}, Events{}},
   Route{bytes("/ws"), False{}, Live{}}]

# with a root directory everything the fixed routes leave is a file
# under it, "/" included; without one "/" is the banner
def routes.tail(root: Maybe<&2, List<&2, U32>>) -> List<&2, Route>:
  match root:
    case None{}:
      [Route{bytes("/"), False{}, Root{}}]
    case Some{dir}:
      [Route{bytes("/"), True{}, Files{}}]

def routes(c: Cfg) -> List<&2, Route>:
  match c:
    case Cfg{port, root, log, idle, conns, grace, shared, pem}:
      List.append(&2, Route, routes.base(), routes.tail(root))

# a is a prefix of b
def bpre(a: List<&2, U32>, b: List<&2, U32>, acc: Bool) -> Bool:
  match a b:
    case Nil{} _:
      acc
    case Con{x, t} Nil{}:
      False{}
    case Con{x, t} Con{y, u}:
      bpre(t, u, acc && U32.is_eq(x, y))

def hit(rp: List<&2, U32>, path: List<&2, U32>, prefix: Bool) -> Bool:
  match prefix:
    case True{}:
      bpre(rp, path, True{})
    case False{}:
      beq(rp, path, True{})

def route.one.go(act: Act, ok: Bool) -> Maybe<&2, Act>:
  match ok:
    case True{}:
      Some{act}
    case False{}:
      None{}

def route.one(r: Route, path: List<&2, U32>) -> Maybe<&2, Act>:
  match r:
    case Route{rp, prefix, act}:
      route.one.go(act, hit(rp, path, prefix))

# an entry is only tested while nothing earlier has matched
def route.keep(acc: Maybe<&2, Act>, r: Route, path: List<&2, U32>) -> Maybe<&2, Act>:
  match acc:
    case Some{a}:
      Some{a}
    case None{}:
      route.one(r, path)

def route.go(table: List<&2, Route>, +path: List<&2, U32>, acc: Maybe<&2, Act>) -> Maybe<&2, Act>:
  match table:
    case Nil{}:
      acc
    case Con{r, t}:
      route.go(t, path, route.keep(acc, r, path))

# the first entry that matches wins
def route(table: List<&2, Route>, +path: List<&2, U32>) -> Maybe<&2, Act>:
  route.go(table, path, None{})

# no two entries claim one path
def same(a: Route, b: Route) -> Bool:
  match a b:
    case Route{p, x, i} Route{q, y, j}:
      beq(p, q, True{})

def taken(+r: Route, rs: List<&2, Route>) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case Con{s, t}:
      same(r, s) || taken(r, t)

def distinct(rs: List<&2, Route>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{+r, +t}:
      Bool.not(taken(r, t)) && distinct(t)

# what every connection shares: the configuration and its table
type Srv is Data:
  Srv{cfg: Cfg, table: List<&2, Route>}

def srv.new(+c: Cfg) -> Srv:
  Srv{c, routes(c)}

def srv.table(s: Srv) -> List<&2, Route>:
  match s:
    case Srv{c, table}:
      table

def srv.root(s: Srv) -> List<&2, U32>:
  match s:
    case Srv{c, table}:
      cfg.root(c)

def srv.log(s: Srv) -> Bool:
  match s:
    case Srv{c, table}:
      cfg.log(c)

def srv.idle(s: Srv) -> U32:
  match s:
    case Srv{c, table}:
      cfg.idle(c)

def srv.conns(s: Srv) -> U32:
  match s:
    case Srv{c, table}:
      cfg.conns(c)

def srv.grace(s: Srv) -> U32:
  match s:
    case Srv{c, table}:
      cfg.grace(c)

# Static files
# ============

# The request path as segments, split on '/', empty ones dropped.
def segs.push(cur: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match cur:
    case Nil{}:
      acc
    case Con{c, t}:
      Con{rev(Con{c, t}), acc}

# the splitter's state: the segment being read (reversed) and the
# segments done (reversed)
type Sg is Data:
  Sg{cur: List<&2, U32>, acc: List<&2, List<&2, U32>>}

def segs.step.go(cur: List<&2, U32>, acc: List<&2, List<&2, U32>>, c: U32, slash: Bool) -> Sg:
  match slash:
    case True{}:
      Sg{Nil{}, segs.push(cur, acc)}
    case False{}:
      Sg{Con{c, cur}, acc}

def segs.step(st: Sg, +c: U32) -> Sg:
  match st:
    case Sg{cur, acc}:
      segs.step.go(cur, acc, c, U32.is_eq(c, 47))

def segs.out(st: Sg) -> List<&2, List<&2, U32>>:
  match st:
    case Sg{cur, acc}:
      segs.push(cur, acc)

def segs.go(bs: List<&2, U32>, st: Sg) -> List<&2, List<&2, U32>>:
  match bs:
    case Nil{}:
      segs.out(st)
    case Con{c, t}:
      segs.go(t, segs.step(st, c))

def segs(path: List<&2, U32>) -> List<&2, List<&2, U32>>:
  List.reverse(&2, List<&2, U32>, segs.go(path, Sg{Nil{}, Nil{}}))

# A segment is a name, ".", or "..".
type Piece is Data:
  Up{}
  Here{}
  Name{}

def piece.of(up: Bool, here: Bool) -> Piece:
  match up here:
    case True{} _:
      Up{}
    case False{} True{}:
      Here{}
    case False{} False{}:
      Name{}

def piece(+s: List<&2, U32>) -> Piece:
  piece.of(beq(s, [46, 46], True{}), beq(s, [46], True{}))

def norm.pop(st: List<&2, List<&2, U32>>) -> Maybe<&2, List<&2, List<&2, U32>>>:
  match st:
    case Nil{}:
      None{}
    case Con{h, t}:
      Some{t}

def norm.step(k: Piece, s: List<&2, U32>, st: List<&2, List<&2, U32>>) -> Maybe<&2, List<&2, List<&2, U32>>>:
  match k:
    case Up{}:
      norm.pop(st)
    case Here{}:
      Some{st}
    case Name{}:
      Some{Con{s, st}}

# ".." climbs; climbing out of the root is refused for good, not
# clamped, because a clamped path is a path someone will probe
def norm.acc(acc: Maybe<&2, List<&2, List<&2, U32>>>, +s: List<&2, U32>) -> Maybe<&2, List<&2, List<&2, U32>>>:
  match acc:
    case None{}:
      None{}
    case Some{st}:
      norm.step(piece(s), s, st)

def norm.go(ss: List<&2, List<&2, U32>>, acc: Maybe<&2, List<&2, List<&2, U32>>>) -> Maybe<&2, List<&2, List<&2, U32>>>:
  match ss:
    case Nil{}:
      acc
    case Con{s, t}:
      norm.go(t, norm.acc(acc, s))

def norm.rev(may: Maybe<&2, List<&2, List<&2, U32>>>) -> Maybe<&2, List<&2, List<&2, U32>>>:
  match may:
    case None{}:
      None{}
    case Some{st}:
      Some{List.reverse(&2, List<&2, U32>, st)}

# the segments a request may name under the root, or None when it
# tried to climb out
def norm(ss: List<&2, List<&2, U32>>) -> Maybe<&2, List<&2, List<&2, U32>>>:
  norm.rev(norm.go(ss, Some{Nil{}}))

# every byte of a file name is printable ASCII and not a backslash
def clean.go(bs: List<&2, U32>, ok: Bool) -> Bool:
  match bs:
    case Nil{}:
      ok
    case Con{+c, t}:
      clean.go(t, ok && U32.is_le(33, c) && U32.is_le(c, 126)
        && Bool.not(U32.is_eq(c, 92)))

def clean(bs: List<&2, U32>) -> Bool:
  clean.go(bs, True{})

def join.rest(ss: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{s, t}:
      Con{47, cat(s, join.rest(t))}

def join(ss: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{s, t}:
      cat(s, join.rest(t))

def last(ss: List<&2, List<&2, U32>>, acc: List<&2, U32>) -> List<&2, U32>:
  match ss:
    case Nil{}:
      acc
    case Con{s, t}:
      last(t, s)

def ext.step(cur: List<&2, U32>, c: U32, dot: Bool) -> List<&2, U32>:
  match dot:
    case True{}:
      Nil{}
    case False{}:
      Con{c, cur}

# the bytes after the last '.'
def ext.go(bs: List<&2, U32>, cur: List<&2, U32>) -> List<&2, U32>:
  match bs:
    case Nil{}:
      rev(cur)
    case Con{+c, t}:
      ext.go(t, ext.step(cur, c, U32.is_eq(c, 46)))

type Mime is Data:
  Mime{ext: List<&2, U32>, name: List<&2, U32>}

def mimes() -> List<&2, Mime>:
  [Mime{bytes("html"), bytes("text/html; charset=utf-8")},
   Mime{bytes("htm"), bytes("text/html; charset=utf-8")},
   Mime{bytes("css"), bytes("text/css; charset=utf-8")},
   Mime{bytes("js"), bytes("application/javascript; charset=utf-8")},
   Mime{bytes("json"), bytes("application/json")},
   Mime{bytes("txt"), bytes("text/plain; charset=utf-8")},
   Mime{bytes("svg"), bytes("image/svg+xml")},
   Mime{bytes("png"), bytes("image/png")},
   Mime{bytes("jpg"), bytes("image/jpeg")},
   Mime{bytes("jpeg"), bytes("image/jpeg")},
   Mime{bytes("gif"), bytes("image/gif")},
   Mime{bytes("ico"), bytes("image/x-icon")},
   Mime{bytes("wasm"), bytes("application/wasm")},
   Mime{bytes("pdf"), bytes("application/pdf")}]

def mime.one.go(name: List<&2, U32>, ok: Bool) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}:
      Some{name}
    case False{}:
      None{}

def mime.one(mi: Mime, e: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match mi:
    case Mime{x, name}:
      mime.one.go(name, beq(x, e, True{}))

def mime.keep(acc: Maybe<&2, List<&2, U32>>, mi: Mime, e: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match acc:
    case Some{n}:
      Some{n}
    case None{}:
      mime.one(mi, e)

def mime.go(ms: List<&2, Mime>, +e: List<&2, U32>, acc: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match ms:
    case Nil{}:
      acc
    case Con{mi, t}:
      mime.go(t, e, mime.keep(acc, mi, e))

def ctype(e: List<&2, U32>) -> List<&2, U32>:
  Maybe.default(&2, List<&2, U32>, mime.go(mimes(), e, None{}),
    bytes("application/octet-stream"))

# One piece of a reply: bytes as they are, or a page to read when the
# reply is written. Fixed routes stay pure; only a file route puts IO
# on the path, and only for its own request.
type Seg is Data:
  Raw{bs: Bytes()}
  Page{path: List<&2, U32>, ct: List<&2, U32>, head: Bool}
  Note{bs: List<&2, U32>}

def miss(head: Bool) -> Bytes():
  match head:
    case True{}:
      head.of(resp.missing())
    case False{}:
      resp.missing()

def page.name(root: List<&2, U32>, +ss: List<&2, List<&2, U32>>, head: Bool) -> Seg:
  Page{cat(root, Con{47, join(ss)}), ctype(ext.go(last(ss, Nil{}), Nil{})), head}

def page.of(root: List<&2, U32>, ss: List<&2, List<&2, U32>>, head: Bool) -> Seg:
  match ss:
    case Nil{}:
      Page{cat(root, bytes("/index.html")), bytes("text/html; charset=utf-8"), head}
    case Con{s, t}:
      page.name(root, Con{s, t}, head)

def page.pick(root: List<&2, U32>, may: Maybe<&2, List<&2, List<&2, U32>>>, head: Bool, ok: Bool) -> Seg:
  match may ok:
    case _ False{}:
      Raw{miss(head)}
    case None{} True{}:
      Raw{miss(head)}
    case Some{ss} True{}:
      page.of(root, ss, head)

# a file under the root, named by the request path: split, normalised,
# and gated to printable ASCII. Percent escapes are not decoded, so an
# escaped ".." is a name no file has rather than a climb.
def page(root: List<&2, U32>, +path: List<&2, U32>, head: Bool) -> Seg:
  page.pick(root, norm(segs(path)), head, clean(path))

# Reading a page: open, size, read, close. A directory opens and then
# refuses to be read, which is a miss. A file past the cap is refused
# rather than loaded, until pages are written in pieces. The body is
# read as one Bytes block, never a cell per byte.
def page.close(f: File, out: Bytes()) -> IO(Bytes()):
  do IO<Bytes()>:
    u : Unit <- File.close(f)
    return out

def page.got(got: File & Result<&1, &1, U32 & String, Bytes()>, ct: List<&2, U32>, n: U32) -> IO(Bytes()):
  (f, r) = got
  match r:
    case Fail{e}:
      page.close(f, resp.missing())
    case Done{bs}:
      page.close(f, reply.n("200 OK", ct, n, bs))

def page.peek(got: File & Result<&1, &1, U32 & String, Bytes()>, ct: List<&2, U32>, n: U32) -> IO(Bytes()):
  (f, r) = got
  match r:
    case Fail{e}:
      page.close(f, head.of(resp.missing()))
    case Done{bs}:
      page.close(f, reply.n.head("200 OK", ct, n))

def page.cap() -> U32:
  4194304

def page.body(f: File, ct: List<&2, U32>, +n: U32, head: Bool, big: Bool) -> IO(Bytes()):
  match head big:
    case True{} _:
      do IO<Bytes()>:
        got : File & Result<&1, &1, U32 & String, Bytes()> <- File.read_buf(f, 1)
        page.peek(got, ct, n)
    case False{} True{}:
      page.close(f, reply("500 Internal Server Error", "text/plain", "file too large\n"))
    case False{} False{}:
      do IO<Bytes()>:
        got : File & Result<&1, &1, U32 & String, Bytes()> <- File.read_buf(f, n)
        page.got(got, ct, n)

def page.sized(got: File & Result<&1, &1, U32 & String, U32>, ct: List<&2, U32>, head: Bool) -> IO(Bytes()):
  (f, r) = got
  match r:
    case Fail{e}:
      page.close(f, miss(head))
    case Done{+n}:
      page.body(f, ct, n, head, U32.is_lt(page.cap(), n))

def page.opened(r: Result<&1, &1, U32 & String, File>, ct: List<&2, U32>, head: Bool) -> IO(Bytes()):
  match r:
    case Fail{e}:
      do IO<Bytes()>:
        return miss(head)
    case Done{f}:
      do IO<Bytes()>:
        got : File & Result<&1, &1, U32 & String, U32> <- File.size(f)
        page.sized(got, ct, head)

def page.read(path: List<&2, U32>, ct: List<&2, U32>, head: Bool) -> IO(Bytes()):
  do IO<Bytes()>:
    r : Result<&1, &1, U32 & String, File> <- File.open(text(path), "r")
    page.opened(r, ct, head)

# the bytes to write for one chunk's answers, in order: literal ones as
# they are, pages read as they come up
# The access log: one line per request, what was asked, the status it
# got and how many bytes went back, on stderr and nowhere else, so
# whatever supervises the process is what timestamps and collects it.
# A Note carries what is known before the reply exists; the segment
# after it completes the line. --log turns it on, and it is off by
# default because a line per request is a syscall per request. The
# status is the three bytes after "HTTP/1.1 ", a view of the reply.
def log.line(+note: List<&2, U32>, +out: Bytes()) -> String:
  text(note) ++ " " ++ Bytes.slice(out, 9n, 3n) ++ " " ++ Nat.show(Bytes.len(out))

# a resolved segment, logged against the note that was waiting if there
# was one, and handed straight back: the line goes out before the
# segments after it, so the log reads in the order the requests came
def flat.note(may: Maybe<&2, List<&2, U32>>, +out: Bytes()) -> IO(Bytes()):
  match may:
    case None{}:
      do IO<Bytes()>:
        return out
    case Some{note}:
      do IO<Bytes()>:
        u : Unit <- IO.print_err(log.line(note, out))
        return out

# the segments appended onto acc in order: the first reply's block
# grows in place, so a pipelined batch is copied once
def flat.go(xs: List<&2, Seg>, may: Maybe<&2, List<&2, U32>>, acc: Bytes()) -> IO(Bytes()):
  match xs:
    case Nil{}:
      do IO<Bytes()>:
        return acc
    case Con{s, t}:
      match s:
        case Note{bs}:
          flat.go(t, Some{bs}, acc)
        case Raw{bs}:
          do IO<Bytes()>:
            out : Bytes() <- flat.note(may, bs)
            flat.go(t, None{}, Bytes.append(acc, out))
        case Page{path, ct, head}:
          do IO<Bytes()>:
            got : Bytes() <- page.read(path, ct, head)
            out : Bytes() <- flat.note(may, got)
            flat.go(t, None{}, Bytes.append(acc, out))

def flat(xs: List<&2, Seg>) -> IO(Bytes()):
  flat.go(xs, None{}, "")


# What answering a chunk produced: the bytes to write, whether the peer
# asked to close, and how many stream events to send afterwards (0 for
# an ordinary reply).
type Ans is Data:
  Ans{out: List<&2, Seg>, close: Bool, stream: U32, sock: Bool}

# Serving
# =======

# HEAD takes the head of what GET would have sent.
def fixed(+r: Bytes(), head: Bool) -> Bytes():
  match head:
    case True{}:
      head.of(r)
    case False{}:
      r

# the reply that switches the connection to frames, with the accept key
# the client's key earns
def live.head(key: List<&2, U32>) -> Bytes():
  Bytes.concat(["HTTP/1.1 101 Switching Protocols\r\nupgrade: websocket\r\nconnection: Upgrade\r\nsec-websocket-accept: ",
    Bytes.from_list(Ws.accept(key)), "\r\n\r\n"])

# /ws: a WebSocket echo, or a 426 for a request that did not ask to upgrade
def live.answer(key: List<&2, U32>, ws: Bool, head: Bool) -> Ans:
  match ws:
    case True{}:
      Ans{[Raw{live.head(key)}], False{}, 0, True{}}
    case False{}:
      Ans{[Raw{fixed(reply("426 Upgrade Required", "text/plain", "websocket only\n"), head)}],
        False{}, 0, False{}}

def act.run(
  +srv: Srv, a: Act, path: List<&2, U32>, body: List<&2, U32>, head: Bool,
  ws: Bool, key: List<&2, U32>
) -> Ans:
  match a:
    case Health{}:
      Ans{[Raw{fixed(resp.health(), head)}], False{}, 0, False{}}
    case Root{}:
      Ans{[Raw{fixed(resp.root(), head)}], False{}, 0, False{}}
    case Echo{}:
      Ans{[Raw{fixed(reply("200 OK", "application/octet-stream", Bytes.from_list(body)), head)}],
        False{}, 0, False{}}
    case Events{}:
      Ans{[Raw{sse.head()}], False{}, sse.count(), False{}}
    case Live{}:
      live.answer(key, ws, head)
    case Files{}:
      Ans{[page(srv.root(srv), path, head)], False{}, 0, False{}}

def serve.act(
  +srv: Srv, found: Maybe<&2, Act>, path: List<&2, U32>, body: List<&2, U32>,
  head: Bool, ws: Bool, key: List<&2, U32>
) -> Ans:
  match found:
    case None{}:
      Ans{[Raw{miss(head)}], False{}, 0, False{}}
    case Some{a}:
      act.run(srv, a, path, body, head, ws, key)

# A method this engine does not implement is refused before routing, so
# no route ever sees one.
def serve.go(
  +srv: Srv, +path: List<&2, U32>, body: List<&2, U32>, ok: Bool, head: Bool,
  ws: Bool, key: List<&2, U32>
) -> Ans:
  match ok:
    case True{}:
      serve.act(srv, route(srv.table(srv), path), path, body, head, ws, key)
    case False{}:
      Ans{[Raw{resp.method()}], False{}, 0, False{}}

# what a log line says was asked. The method is a hash by then, so the
# two this engine serves are named and anything else is "?".
def shown(+meth: U32, get: Bool, head: Bool) -> List<&2, U32>:
  match get head:
    case True{} _:
      bytes("GET")
    case False{} True{}:
      bytes("HEAD")
    case False{} False{}:
      bytes("?")

def noted.on(note: List<&2, U32>, a: Ans) -> Ans:
  match a:
    case Ans{out, cl, st, sk}:
      Ans{Con{Note{note}, out}, cl, st, sk}

def noted(on: Bool, note: List<&2, U32>, a: Ans) -> Ans:
  match on:
    case False{}:
      a
    case True{}:
      noted.on(note, a)

def serve.log(+srv: Srv, r: Req) -> Ans:
  match r:
    case Req{+meth, +path, body, close, ws, key}:
      noted(srv.log(srv),
        cat(shown(meth, U32.is_eq(meth, m.get()), U32.is_eq(meth, m.head())),
          cat(bytes(" "), path)),
        serve.go(srv, path, body,
          U32.is_eq(meth, m.get()) || U32.is_eq(meth, m.head()),
          U32.is_eq(meth, m.head()), ws, key))

def serve(+srv: Srv, r: Req) -> Ans:
  serve.log(srv, r)


def answer.cat(one: List<&2, Seg>, tail: List<&2, Seg>, cl: Bool, st: U32, sk: Bool) -> Ans:
  match tail:
    case Nil{}:
      Ans{one, cl, st, sk}
    case Con{h, t}:
      Ans{List.append(&2, Seg, one, Con{h, t}), cl, st, sk}

def answer.rest(a: List<&2, Seg>, c1: Bool, s1: U32, k1: Bool, rest: Ans) -> Ans:
  match rest:
    case Ans{b, c2, s2, k2}:
      answer.cat(a, b, c1 || c2, U32.max(s1, s2), k1 || k2)

def answer.go(one: Ans, rest: Ans) -> Ans:
  match one:
    case Ans{a, c1, s1, k1}:
      answer.rest(a, c1, s1, k1, rest)

# Every reply for one chunk's worth of messages, in arrival order, and
# whether any of them asked to close. The replies nest to the right, so
# each one is copied once: folding them into an accumulator instead
# would copy the accumulator per message and go quadratic in the depth
# of a pipelined batch.
def answer.one(a: Ans, cl: Bool) -> Ans:
  match a:
    case Ans{out, c, st, sk}:
      Ans{out, c || cl, st, sk}

def answer(+srv: Srv, rs: List<&2, Req>, cl: Bool) -> Ans:
  match rs:
    case Nil{}:
      Ans{Nil{}, cl, 0, False{}}
    case Con{+r, t}:
      answer.go(answer.one(serve(srv, r), req.close(r)), answer(srv, t, cl))

# The server
# ==========

# What the connection does next: write these bytes and read again,
# write them and close, write them and keep streaming without reading
# again, or close now. Feed is the one that holds a connection open.
type Plan is Data:
  Go{out: List<&2, Seg>, p2: P}
  Wait{p2: P}
  End{out: List<&2, Seg>}
  Feed{out: List<&2, Seg>, n: U32}
  Sock{out: List<&2, Seg>, wr: Ws.W}
  Hold{wr: Ws.W}
  Stop{}

def plan.pick(
  out: List<&2, Seg>, p2: P, plain: Bool, cl: Bool, st: U32, sock: Bool
) -> Plan:
  match plain cl sock:
    case _ _ True{}:
      Sock{out, Ws.new()}
    case False{} _ False{}:
      Feed{out, st}
    case True{} True{} False{}:
      End{out}
    case True{} False{} False{}:
      Go{out, p2}

# nothing to write means the chunk ended mid-message: read on without
# a write, unless the peer asked to close
def plan.quiet(p2: P, cl: Bool) -> Plan:
  match cl:
    case True{}:
      Stop{}
    case False{}:
      Wait{p2}

def plan.ans(a: Ans, p2: P) -> Plan:
  match a:
    case Ans{out, cl, +st, sock}:
      match out:
        case Nil{}:
          plan.quiet(p2, cl)
        case Con{h, t}:
          plan.pick(Con{h, t}, p2, U32.is_zero(st), cl, st, sock)

def plan.take(+srv: Srv, pr: P & List<&2, Req>) -> Plan:
  (p2, rs) = pr
  plan.ans(answer(srv, rs, False{}), p2)

def plan.go(+srv: Srv, q: P, bad: Bool) -> Plan:
  match bad:
    case True{}:
      End{[Raw{resp.bad()}]}
    case False{}:
      plan.take(srv, p.take(q))

def plan.on(+srv: Srv, pb: P & Bool) -> Plan:
  (q, bad) = pb
  plan.go(srv, q, bad)

# the plan after one chunk: parse it, then decide
# An empty chunk is the peer's FIN: nothing more will ever arrive, so
# the connection ends here rather than reading again. As first written
# the engine read again, and one peer that connected and closed without
# a byte cost most of a core in passes until the fuel ran out.
def plan.chunk(+srv: Srv, buf: List<&2, U32>, p: P) -> Plan:
  match buf:
    case Nil{}:
      Stop{}
    case Con{b, bs}:
      plan.on(srv, p.dead(feed(Con{b, bs}, p)))

# what a timed read gave: bytes to parse, the peer's silence past the
# idle time (the connection ends), or a failure (it ends)
def plan.may(
  +srv: Srv, s: Socket, may: Maybe<&1, List<&2, U32>>, p: P
) -> Socket & Plan:
  match may:
    case None{}:
      (s, Stop{})
    case Some{buf}:
      (s, plan.chunk(srv, buf, p))

def plan.polled(
  +srv: Srv, s: Socket, r: Result<&1, &1, U32 & String, Maybe<&1, List<&2, U32>>>,
  p: P
) -> Socket & Plan:
  match r:
    case Done{may}:
      plan.may(srv, s, may, p)
    case Fail{e}:
      (s, Stop{})

# the socket and the plan, out of one timed read
def plan.poll(
  +srv: Srv, m: Socket & Result<&1, &1, U32 & String, Maybe<&1, List<&2, U32>>>,
  p: P
) -> Socket & Plan:
  (s, r) = m
  plan.polled(srv, s, r, p)

def chunk() -> U32:
  16384

# read the next chunk, within the idle time, and plan from it. Splitting
# the send's socket out here is what lets the connection loop below be
# one self-recursive def.
def turn.s(+srv: Srv, s: Socket, p: P) -> IO(Socket & Plan):
  do IO<Socket & Plan>:
    m : Socket & Result<&1, &1, U32 & String, Maybe<&1, List<&2, U32>>> <-
      TCP.poll_bytes(s, chunk(), srv.idle(srv))
    return plan.poll(srv, m, p)

def turn(+srv: Srv, sent: Socket & Result<&1, &1, U32 & String, Unit>, p: P) ->
  IO(Socket & Plan):
  (s, r) = sent
  turn.s(srv, s, p)

# A WebSocket connection: what the frames one read completed earned --
# bytes to write and read on, nothing yet (read on), or the close.
def plan.rep(s: Socket, wr: Ws.W, r: Ws.Rep) -> Socket & Plan:
  match r:
    case Ws.Rep{out, close}:
      match out:
        case Nil{}:
          match close:
            case True{}:
              (s, End{Nil{}})
            case False{}:
              (s, Hold{wr})
        case Con{h, t}:
          match close:
            case True{}:
              (s, End{[Raw{Bytes.from_list(Con{h, t})}]})
            case False{}:
              (s, Sock{[Raw{Bytes.from_list(Con{h, t})}], wr})

def plan.framed(s: Socket, fs: List<&2, Ws.Frm>, dd: Ws.W & Bool) -> Socket & Plan:
  (wr, bad) = dd
  plan.rep(s, wr, Ws.reply(fs, bad))

def plan.frames(s: Socket, tk: Ws.W & List<&2, Ws.Frm>) -> Socket & Plan:
  (wr, fs) = tk
  plan.framed(s, fs, Ws.dead(wr))

def plan.wsm(s: Socket, may: Maybe<&1, List<&2, U32>>, wr: Ws.W) -> Socket & Plan:
  match may:
    case None{}:
      (s, Stop{})
    case Some{bs}:
      match bs:
        case Nil{}:
          (s, Stop{})
        case Con{b, t}:
          plan.frames(s, Ws.take(Ws.feed(Con{b, t}, wr)))

def plan.wsr(
  s: Socket, r: Result<&1, &1, U32 & String, Maybe<&1, List<&2, U32>>>, wr: Ws.W
) -> Socket & Plan:
  match r:
    case Done{may}:
      plan.wsm(s, may, wr)
    case Fail{e}:
      (s, Stop{})

def plan.ws(
  m: Socket & Result<&1, &1, U32 & String, Maybe<&1, List<&2, U32>>>, wr: Ws.W
) -> Socket & Plan:
  (s, r) = m
  plan.wsr(s, r, wr)

def turn.wr(+srv: Srv, s: Socket, wr: Ws.W) -> IO(Socket & Plan):
  do IO<Socket & Plan>:
    m : Socket & Result<&1, &1, U32 & String, Maybe<&1, List<&2, U32>>> <-
      TCP.poll_bytes(s, chunk(), srv.idle(srv))
    return plan.ws(m, wr)

def turn.ws(+srv: Srv, sent: Socket & Result<&1, &1, U32 & String, Unit>, wr: Ws.W) ->
  IO(Socket & Plan):
  (s, r) = sent
  turn.wr(srv, s, wr)

# the next event, or the end of the stream. A stream terminates because
# the count runs out, the same way a connection does: no @unsafe, and a
# peer that goes quiet still cannot hold a computation open forever.
def plan.more(s: Socket, +n: U32, done: Bool) -> Socket & Plan:
  match done:
    case True{}:
      (s, Stop{})
    case False{}:
      (s, Feed{[Raw{sse.event(n)}], (n - 1 : U32)})

def plan.next(
  s: Socket, r: Result<&1, &1, U32 & String, Unit>, +n: U32
) -> Socket & Plan:
  match r:
    case Done{u}:
      plan.more(s, n, U32.is_zero(n))
    case Fail{e}:
      (s, Stop{})

# wait, then plan the next event. The engine writes on its own clock and
# reads nothing, so the reader and the writer never contend for the one
# socket the connection owns.
def tick(sent: Socket & Result<&1, &1, U32 & String, Unit>, n: U32) ->
  IO(Socket & Plan):
  (s, r) = sent
  do IO<Socket & Plan>:
    IO.sleep(sse.gap())
    return plan.next(s, r, n)

# A connection ends by closing its socket and giving its slot back: the
# semaphore is a channel with as much room as connections allowed, a
# slot is a Unit sent into it, and accepting parks on a full one.
def fin(+sem: Chan(Unit), s: Socket) -> IO(Unit):
  do IO<Unit>:
    Socket.close(s)
    got : Maybe<&1, Unit> <- Chan.recv(Unit, sem)
    return Unit{}

def shut(+sem: Chan(Unit), m: Socket & Result<&1, &1, U32 & String, Unit>) -> IO(Unit):
  (s, r) = m
  fin(sem, s)

# One connection. fuel is the most chunks it will ever read, so the
# loop terminates by Bend's own rule rather than by @unsafe: a peer
# that dribbles bytes forever runs the fuel out and is dropped.
# the most chunks one connection may ever ask for. It is a real bound,
# not a formality: it is what stops a peer from holding a computation
# open forever, and it is why conn needs no @unsafe.
def conn.fuel() -> Nat:
  U32.to_nat(1048576)

# the most reads in a row that may finish no message. A head arrives
# in one or two chunks; one dribbled a byte at a time, each inside the
# idle time, is not a client and is dropped after this many.
def conn.waits() -> Nat:
  64n

def conn(f: Nat, +srv: Srv, +sem: Chan(Unit), sp: Socket & Plan, w: Nat) -> IO(Unit):
  match f:
    case 0n:
      (s, pl) = sp
      fin(sem, s)
    case 1n+g:
      (s, pl) = sp
      match pl:
        case Stop{}:
          fin(sem, s)
        case End{out}:
          do IO<Unit>:
            bs : Bytes() <- flat(out)
            m  : Socket & Result<&1, &1, U32 & String, Unit> <-
              TCP.send_buf(s, bs)
            shut(sem, m)
        case Wait{p2}:
          match w:
            case 0n:
              fin(sem, s)
            case 1n+v:
              do IO<Unit>:
                sp2 : Socket & Plan <- turn.s(srv, s, p2)
                conn(g, srv, sem, sp2, v)
        case Feed{out, n}:
          do IO<Unit>:
            bs  : Bytes() <- flat(out)
            m   : Socket & Result<&1, &1, U32 & String, Unit> <-
              TCP.send_buf(s, bs)
            sp2 : Socket & Plan <- tick(m, n)
            conn(g, srv, sem, sp2, conn.waits())
        case Sock{out, wr}:
          do IO<Unit>:
            bs  : Bytes() <- flat(out)
            m   : Socket & Result<&1, &1, U32 & String, Unit> <-
              TCP.send_buf(s, bs)
            sp2 : Socket & Plan <- turn.ws(srv, m, wr)
            conn(g, srv, sem, sp2, conn.waits())
        case Hold{wr}:
          match w:
            case 0n:
              fin(sem, s)
            case 1n+v:
              do IO<Unit>:
                sp2 : Socket & Plan <- turn.wr(srv, s, wr)
                conn(g, srv, sem, sp2, v)
        case Go{out, p2}:
          do IO<Unit>:
            bs  : Bytes() <- flat(out)
            m   : Socket & Result<&1, &1, U32 & String, Unit> <-
              TCP.send_buf(s, bs)
            sp2 : Socket & Plan <- turn(srv, m, p2)
            conn(g, srv, sem, sp2, conn.waits())

def start(+srv: Srv, +sem: Chan(Unit), s: Socket) -> IO(Unit):
  do IO<Unit>:
    m : Socket & Result<&1, &1, U32 & String, Maybe<&1, List<&2, U32>>> <-
      TCP.poll_bytes(s, chunk(), srv.idle(srv))
    conn(conn.fuel(), srv, sem, plan.poll(srv, m, p.new()), conn.waits())

# how often the accept loop looks up from the listener, in ms: the most
# a stop request waits before it is seen
def accept.tick() -> U32:
  250

# A connection to serve takes a slot first, so accepting parks while the
# limit is reached and the backlog holds what arrives meanwhile. Nothing
# within the tick is the moment to look for a stop request.
def accept.on(
  +srv: Srv, +sem: Chan(Unit), l: Listener, may: Maybe<&1, Socket>
) -> IO(Listener & Bool):
  match may:
    case None{}:
      do IO<Listener & Bool>:
        stop : Bool <- IO.signal_pending(15)
        return (l, Bool.not(stop))
    case Some{s}:
      do IO<Listener & Bool>:
        ok : Bool <- Chan.send(Unit, sem, Unit{})
        IO.spawn(Unit, start(srv, sem, s))
        return (l, True{})

def accept.got(
  +srv: Srv, +sem: Chan(Unit),
  m: Listener & Result<&1, &1, U32 & String, Maybe<&1, Socket>>
) -> IO(Listener & Bool):
  (l, r) = m
  match r:
    case Done{may}:
      accept.on(srv, sem, l, may)
    case Fail{e}:
      do IO<Listener & Bool>:
        return (l, False{})

def accept.one(+srv: Srv, +sem: Chan(Unit), l: Listener) -> IO(Listener & Bool):
  do IO<Listener & Bool>:
    m : Listener & Result<&1, &1, U32 & String, Maybe<&1, Socket>> <-
      TCP.accept_poll(l, accept.tick())
    accept.got(srv, sem, m)

# every slot taken back means every connection has ended
def drain(k: Nat, +sem: Chan(Unit)) -> IO(Unit):
  match k:
    case 0n:
      do IO<Unit>:
        return Unit{}
    case 1n+j:
      do IO<Unit>:
        ok : Bool <- Chan.send(Unit, sem, Unit{})
        drain(j, sem)

def grace(ms: U32) -> IO(Unit):
  do IO<Unit>:
    IO.sleep(ms)
    IO.die(Unit, 0, "bend-http: stopped with connections still open")

# Stopping, on SIGTERM: the listener closes so nothing more arrives, the
# connections open finish what they are doing, and the process ends when
# they have all ended or when the grace time is up, whichever is first.
def stopping(+srv: Srv, +sem: Chan(Unit), l: Listener) -> IO(Unit):
  do IO<Unit>:
    IO.print_err("bend-http: stopping")
    Listener.close(l)
    IO.spawn(Unit, grace(srv.grace(srv)))
    drain(U32.to_nat(srv.conns(srv)), sem)
    IO.die(Unit, 0, "bend-http: stopped")

# The accept loop is the one place that runs until it is told to stop,
# so it is the one @unsafe def in the engine.
@unsafe
def accept(+srv: Srv, +sem: Chan(Unit), lb: Listener & Bool) -> IO(Unit):
  (l, go) = lb
  match go:
    case False{}:
      stopping(srv, sem, l)
    case True{}:
      do IO<Unit>:
        lb2 : Listener & Bool <- accept.one(srv, sem, l)
        accept(srv, sem, lb2)

def scheme(m: Maybe<&2, Pem>) -> String:
  match m:
    case None{}:
      "http"
    case Some{pem}:
      "https"

def banner(+c: Cfg) -> String:
  String.append("bend-http on ", String.append(scheme(cfg.pem(c)),
    String.append("://127.0.0.1:", U32.show(cfg.port(c)))))

# a shared port: several copies of this server on one port, the kernel
# dealing the connections out; how a single-threaded server takes more
# than one core
def listen.plain(port: U32, shared: Bool) -> IO(Result<&1, &1, U32 & String, Listener>):
  match shared:
    case True{}:
      TCP.listen_shared(port)
    case False{}:
      TCP.listen(port)

# With a certificate the listener is a TLS listener, and every socket it
# accepts carries a session; nothing else in the server changes, because
# the effects that carry bytes go through the same wire either way.
def listen(port: U32, shared: Bool, m: Maybe<&2, Pem>) ->
  IO(Result<&1, &1, U32 & String, Listener>):
  match m:
    case None{}:
      listen.plain(port, shared)
    case Some{pem}:
      match pem:
        case Pem{cert, key}:
          TLS.listen(port, text(cert), text(key))

def run(+c: Cfg) -> IO(Unit):
  do IO<Unit>:
    l   : Listener <- IO.try(Listener, listen(cfg.port(c), cfg.shared(c), cfg.pem(c)))
    sem : Chan(Unit) <- Chan.new(Unit, cfg.conns(c))
    IO.print(banner(c))
    accept(srv.new(c), sem, (l, True{}))

# bend-http [--port N] [--root DIR] [--idle-ms N] [--max-conns N] [--grace-ms N]
#           [--shared] [--tls-cert PEM --tls-key PEM] [--log]
def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    c  : Cfg <- args.done(args.read(xs, Args{cfg.new(), Flag{}}))
    run(c)
