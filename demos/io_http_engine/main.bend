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
# cost, so this engine reads and writes List<&2, U32> through
# TCP.recv_bytes and TCP.send_bytes instead, the byte pair that files
# have always had.
#
#   bend demos/io_http_engine/main.bend -o httpd && ./httpd
#   curl -i http://127.0.0.1:8080/health
import Base

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

# The wire's unit. A byte list, one cell per byte, is what the socket
# hands over and what it takes back.
def cat(a: List<&2, U32>, b: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, a, b)

def rev(a: List<&2, U32>) -> List<&2, U32>:
  List.reverse(&2, U32, a)

# An ASCII literal as bytes. Written text stays readable in the source
# and becomes bytes here; a code point past 255 is not a byte and
# TCP.send_bytes refuses it rather than re-encoding it.
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

def m.get() -> U32:
  2531704439

def m.head() -> U32:
  811237315

# Requests
# ========

# A parsed message: the method as a hash, the target and body as bytes,
# and whether the peer asked to close.
type Req is Data:
  Req{meth: U32, path: List<&2, U32>, body: List<&2, U32>, close: Bool}

def req.close(r: Req) -> Bool:
  match r:
    case Req{meth, path, body, close}:
      close

# The fields of the message being read. It is rebuilt only when a token
# closes, so an ordinary byte leaves it untouched and shares it.
type Pend is Data:
  Pend{meth: U32, path: List<&2, U32>, clen: U32, close: Bool, te: Bool}

def pend.new() -> Pend:
  Pend{0, Nil{}, 0, False{}, False{}}

# a new method token starts a new message, so the rest resets with it
def pend.meth(pd: Pend, h: U32) -> Pend:
  match pd:
    case Pend{meth, path, clen, close, te}:
      Pend{h, Nil{}, 0, False{}, False{}}

def pend.path(pd: Pend, p: List<&2, U32>) -> Pend:
  match pd:
    case Pend{meth, path, clen, close, te}:
      Pend{meth, p, clen, close, te}

# A closed field, applied by name hash: a length, a connection token,
# or a Transfer-Encoding, which poisons the message rather than framing
# it a second way.
def pend.set.go(
  meth: U32, path: List<&2, U32>, clen: U32, close: Bool, te: Bool,
  v: U32, isc: Bool, cl: Bool, isl: Bool, ist: Bool
) -> Pend:
  match isc isl ist:
    case True{} _ _:
      Pend{meth, path, clen, cl, te}
    case _ True{} _:
      Pend{meth, path, v, close, te}
    case _ _ True{}:
      Pend{meth, path, clen, close, True{}}
    case _ _ _:
      Pend{meth, path, clen, close, te}

def pend.set(pd: Pend, v: U32, isc: Bool, cl: Bool, isl: Bool, ist: Bool) -> Pend:
  match pd:
    case Pend{meth, path, clen, close, te}:
      pend.set.go(meth, path, clen, close, te, v, isc, cl, isl, ist)

def pend.poison(pd: Pend) -> Pend:
  match pd:
    case Pend{meth, path, clen, close, te}:
      Pend{meth, path, clen, close, True{}}

def pend.len(pd: Pend) -> Pend & U32:
  match pd:
    case Pend{meth, path, +clen, close, te}:
      (Pend{meth, path, clen, close, te}, clen)

def pend.te_if(pd: Pend, is_te: Bool) -> Pend:
  match is_te:
    case True{}:
      pend.poison(pd)
    case False{}:
      pd

def pend.te(pd: Pend) -> Pend & Bool:
  match pd:
    case Pend{meth, path, clen, close, +te}:
      (Pend{meth, path, clen, close, te}, te)

def pend.req(pd: Pend, body: List<&2, U32>) -> Req:
  match pd:
    case Pend{meth, path, clen, close, te}:
      Req{meth, path, body, close}

# The reader
# ==========

# InM  the method token            Lin  at the start of a line
# InT  the target token            InN  a field name
# InV  the version token           Ows  the space after its colon
# CrM  a CR inside the head        InL  a Content-Length value
# InLc a Connection value          InLx any other value, skipped
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
def step.conn(g: U32, pd: Pend, out: List<&2, Req>) -> P:
  P{CrM{}, pend.set(pd, 0, True{}, U32.is_eq(g, hash.close()), False{},
    False{}), out}

# the first byte of a value picks the scanner the field needs, and
# every other field gets the one that does no work per byte at all
def step.val.go(
  +c: U32, pd: Pend, out: List<&2, Req>, isl: Bool, isc: Bool
) -> P:
  match isl isc:
    case True{} _:
      P{InL{(c - 48 : U32), digit(c)}, pd, out}
    case _ True{}:
      P{InLc{fnv(fnv.new(), lower(c))}, pd, out}
    case _ _:
      P{InLx{}, pd, out}

def step.val(+n: U32, +c: U32, pd: Pend, out: List<&2, Req>) -> P:
  step.val.go(c, pd, out, U32.is_eq(n, hash.content_length()),
    U32.is_eq(n, hash.connection()))

def step.head.on(pd: Pend, n: U32, out: List<&2, Req>, z: Bool) -> P:
  match z:
    case True{}:
      emit(pd, Nil{}, out)
    case False{}:
      P{Bod{n, Nil{}}, pd, out}

def step.head.len(pn: Pend & U32, out: List<&2, Req>) -> P:
  (pd, +n) = pn
  step.head.on(pd, n, out, U32.is_zero(n))

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
# usable.
def reply(status: String, ctype: String, +body: List<&2, U32>) -> List<&2, U32>:
  cat(bytes("HTTP/1.1 "), cat(bytes(status),
  cat(bytes("\r\ncontent-type: "), cat(bytes(ctype),
  cat(bytes("\r\ncontent-length: "),
  cat(bytes(Nat.show(List.length(&2, U32, body))),
  cat(bytes("\r\nconnection: keep-alive\r\n\r\n"), body)))))))

# A reply whose body is fixed has fixed bytes, so it is written out as
# those bytes instead of being rebuilt per request: measured here,
# building a 106-byte reply out of nine pieces cost more than parsing
# the request that asked for it. Nobody should read these numbers --
# LAWS.bend says each one equals reply() called with the arguments
# named beside it, and the checker refuses the engine if an edit ever
# makes that false, so the readable form is the specification and this
# is only its image.
def resp.health() -> List<&2, U32>:
  [
  72, 84, 84, 80, 47, 49, 46, 49, 32, 50, 48, 48, 32, 79, 75, 13, 10, 99,
  111, 110, 116, 101, 110, 116, 45, 116, 121, 112, 101, 58, 32, 97, 112,
  112, 108, 105, 99, 97, 116, 105, 111, 110, 47, 106, 115, 111, 110, 13,
  10, 99, 111, 110, 116, 101, 110, 116, 45, 108, 101, 110, 103, 116, 104,
  58, 32, 49, 49, 13, 10, 99, 111, 110, 110, 101, 99, 116, 105, 111, 110,
  58, 32, 107, 101, 101, 112, 45, 97, 108, 105, 118, 101, 13, 10, 13, 10,
  123, 34, 111, 107, 34, 58, 116, 114, 117, 101, 125]

def resp.root() -> List<&2, U32>:
  [
  72, 84, 84, 80, 47, 49, 46, 49, 32, 50, 48, 48, 32, 79, 75, 13, 10, 99,
  111, 110, 116, 101, 110, 116, 45, 116, 121, 112, 101, 58, 32, 116, 101,
  120, 116, 47, 112, 108, 97, 105, 110, 13, 10, 99, 111, 110, 116, 101,
  110, 116, 45, 108, 101, 110, 103, 116, 104, 58, 32, 49, 48, 13, 10, 99,
  111, 110, 110, 101, 99, 116, 105, 111, 110, 58, 32, 107, 101, 101, 112,
  45, 97, 108, 105, 118, 101, 13, 10, 13, 10, 98, 101, 110, 100, 45, 104,
  116, 116, 112, 10]

def resp.missing() -> List<&2, U32>:
  [
  72, 84, 84, 80, 47, 49, 46, 49, 32, 52, 48, 52, 32, 78, 111, 116, 32,
  70, 111, 117, 110, 100, 13, 10, 99, 111, 110, 116, 101, 110, 116, 45,
  116, 121, 112, 101, 58, 32, 116, 101, 120, 116, 47, 112, 108, 97, 105,
  110, 13, 10, 99, 111, 110, 116, 101, 110, 116, 45, 108, 101, 110, 103,
  116, 104, 58, 32, 57, 13, 10, 99, 111, 110, 110, 101, 99, 116, 105, 111,
  110, 58, 32, 107, 101, 101, 112, 45, 97, 108, 105, 118, 101, 13, 10, 13,
  10, 110, 111, 32, 114, 111, 117, 116, 101, 10]

def resp.method() -> List<&2, U32>:
  [
  72, 84, 84, 80, 47, 49, 46, 49, 32, 52, 48, 53, 32, 77, 101, 116, 104,
  111, 100, 32, 78, 111, 116, 32, 65, 108, 108, 111, 119, 101, 100, 13,
  10, 99, 111, 110, 116, 101, 110, 116, 45, 116, 121, 112, 101, 58, 32,
  116, 101, 120, 116, 47, 112, 108, 97, 105, 110, 13, 10, 99, 111, 110,
  116, 101, 110, 116, 45, 108, 101, 110, 103, 116, 104, 58, 32, 49, 48,
  13, 10, 99, 111, 110, 110, 101, 99, 116, 105, 111, 110, 58, 32, 107,
  101, 101, 112, 45, 97, 108, 105, 118, 101, 13, 10, 13, 10, 110, 111, 32,
  109, 101, 116, 104, 111, 100, 10]

def resp.bad() -> List<&2, U32>:
  [
  72, 84, 84, 80, 47, 49, 46, 49, 32, 52, 48, 48, 32, 66, 97, 100, 32, 82,
  101, 113, 117, 101, 115, 116, 13, 10, 99, 111, 110, 116, 101, 110, 116,
  45, 116, 121, 112, 101, 58, 32, 116, 101, 120, 116, 47, 112, 108, 97,
  105, 110, 13, 10, 99, 111, 110, 116, 101, 110, 116, 45, 108, 101, 110,
  103, 116, 104, 58, 32, 49, 50, 13, 10, 99, 111, 110, 110, 101, 99, 116,
  105, 111, 110, 58, 32, 107, 101, 101, 112, 45, 97, 108, 105, 118, 101,
  13, 10, 13, 10, 98, 97, 100, 32, 114, 101, 113, 117, 101, 115, 116, 10]

# An event stream: the head goes out once, then one event at a time on
# the engine's own schedule, with nothing more read from the peer. This
# is the shape that holds a connection open -- an agent session, a token
# stream, a live feed -- and it is what this engine is actually good at.
def sse.head() -> List<&2, U32>:
  bytes("HTTP/1.1 200 OK\r\ncontent-type: text/event-stream\r\ncache-control: no-cache\r\nconnection: keep-alive\r\n\r\n")

def sse.event(n: U32) -> List<&2, U32>:
  cat(bytes("event: tick\ndata: "), cat(bytes(U32.show(n)), bytes("\n\n")))

# how many events a stream sends before it closes, and how long it
# waits between them. Both are bounds, not settings: the count is what
# makes the streaming loop terminate without @unsafe.
def sse.count() -> U32:
  1000000

def sse.gap() -> U32:
  1000

# What answering a chunk produced: the bytes to write, whether the peer
# asked to close, and how many stream events to send afterwards (0 for
# an ordinary reply).
type Ans is Data:
  Ans{out: List<&2, U32>, close: Bool, stream: U32}

def route.go(
  path: List<&2, U32>, body: List<&2, U32>, health: Bool, echo: Bool, root: Bool
) -> List<&2, U32>:
  match health echo root:
    case True{} _ _:
      resp.health()
    case _ True{} _:
      reply("200 OK", "application/octet-stream", body)
    case _ _ True{}:
      resp.root()
    case _ _ _:
      resp.missing()

def route.ev(+path: List<&2, U32>, body: List<&2, U32>, ev: Bool) -> Ans:
  match ev:
    case True{}:
      Ans{sse.head(), False{}, sse.count()}
    case False{}:
      Ans{route.go(path, body, beq(path, bytes("/health"), True{}),
        beq(path, bytes("/echo"), True{}), beq(path, bytes("/"), True{})),
        False{}, 0}

def route(+path: List<&2, U32>, body: List<&2, U32>) -> Ans:
  route.ev(path, body, beq(path, bytes("/events"), True{}))

# A method this engine does not implement is refused before routing, so
# no route ever sees one.
def serve.go(path: List<&2, U32>, body: List<&2, U32>, ok: Bool) -> Ans:
  match ok:
    case True{}:
      route(path, body)
    case False{}:
      Ans{resp.method(), False{}, 0}

def serve(r: Req) -> Ans:
  match r:
    case Req{+meth, path, body, close}:
      serve.go(path, body,
        U32.is_eq(meth, m.get()) || U32.is_eq(meth, m.head()))

def answer.cat(one: List<&2, U32>, tail: List<&2, U32>, cl: Bool, st: U32) -> Ans:
  match tail:
    case Nil{}:
      Ans{one, cl, st}
    case Con{h, t}:
      Ans{cat(one, Con{h, t}), cl, st}

def answer.rest(a: List<&2, U32>, c1: Bool, s1: U32, rest: Ans) -> Ans:
  match rest:
    case Ans{b, c2, s2}:
      answer.cat(a, b, c1 || c2, U32.max(s1, s2))

def answer.go(one: Ans, rest: Ans) -> Ans:
  match one:
    case Ans{a, c1, s1}:
      answer.rest(a, c1, s1, rest)

# Every reply for one chunk's worth of messages, in arrival order, and
# whether any of them asked to close. The replies nest to the right, so
# each one is copied once: folding them into an accumulator instead
# would copy the accumulator per message and go quadratic in the depth
# of a pipelined batch.
def answer.one(a: Ans, cl: Bool) -> Ans:
  match a:
    case Ans{out, c, st}:
      Ans{out, c || cl, st}

def answer(rs: List<&2, Req>, cl: Bool) -> Ans:
  match rs:
    case Nil{}:
      Ans{Nil{}, cl, 0}
    case Con{+r, t}:
      answer.go(answer.one(serve(r), req.close(r)), answer(t, cl))

# The server
# ==========

# What the connection does next: write these bytes and read again,
# write them and close, write them and keep streaming without reading
# again, or close now. Feed is the one that holds a connection open.
type Plan is Data:
  Go{out: List<&2, U32>, p2: P}
  End{out: List<&2, U32>}
  Feed{out: List<&2, U32>, n: U32}
  Stop{}

def plan.pick(
  out: List<&2, U32>, p2: P, plain: Bool, cl: Bool, st: U32
) -> Plan:
  match plain cl:
    case False{} _:
      Feed{out, st}
    case True{} True{}:
      End{out}
    case True{} False{}:
      Go{out, p2}

def plan.ans(a: Ans, p2: P) -> Plan:
  match a:
    case Ans{out, cl, +st}:
      plan.pick(out, p2, U32.is_zero(st), cl, st)

def plan.take(pr: P & List<&2, Req>) -> Plan:
  (p2, rs) = pr
  plan.ans(answer(rs, False{}), p2)

def plan.go(q: P, bad: Bool) -> Plan:
  match bad:
    case True{}:
      End{resp.bad()}
    case False{}:
      plan.take(p.take(q))

def plan.on(pb: P & Bool) -> Plan:
  (q, bad) = pb
  plan.go(q, bad)

# the plan after one chunk: parse it, then decide
# An empty chunk is the peer's FIN: nothing more will ever arrive, so
# the connection ends here rather than reading again. As first written
# the engine read again, and one peer that connected and closed without
# a byte cost most of a core in passes until the fuel ran out.
def plan.chunk(buf: List<&2, U32>, p: P) -> Plan:
  match buf:
    case Nil{}:
      Stop{}
    case Con{b, bs}:
      plan.on(p.dead(feed(Con{b, bs}, p)))

def plan.read(
  s: Socket, r: Result<&1, &1, U32 & String, List<&2, U32>>, p: P
) -> Socket & Plan:
  match r:
    case Done{buf}:
      (s, plan.chunk(buf, p))
    case Fail{e}:
      (s, Stop{})

# the socket and the plan, out of one recv
def plan.recv(
  m: Socket & Result<&1, &1, U32 & String, List<&2, U32>>, p: P
) -> Socket & Plan:
  (s, r) = m
  plan.read(s, r, p)

def chunk() -> U32:
  16384

# read the next chunk and plan from it. Splitting the send's socket out
# here is what lets the connection loop below be one self-recursive def.
def turn(sent: Socket & Result<&1, &1, U32 & String, Unit>, p: P) ->
  IO(Socket & Plan):
  (s, r) = sent
  do IO<Socket & Plan>:
    m : Socket & Result<&1, &1, U32 & String, List<&2, U32>> <-
      TCP.recv_bytes(s, chunk())
    return plan.recv(m, p)

# the next event, or the end of the stream. A stream terminates because
# the count runs out, the same way a connection does: no @unsafe, and a
# peer that goes quiet still cannot hold a computation open forever.
def plan.more(s: Socket, +n: U32, done: Bool) -> Socket & Plan:
  match done:
    case True{}:
      (s, Stop{})
    case False{}:
      (s, Feed{sse.event(n), (n - 1 : U32)})

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

def shut(m: Socket & Result<&1, &1, U32 & String, Unit>) -> IO(Unit):
  (s, r) = m
  Socket.close(s)

# One connection. fuel is the most chunks it will ever read, so the
# loop terminates by Bend's own rule rather than by @unsafe: a peer
# that dribbles bytes forever runs the fuel out and is dropped.
def conn(f: Nat, sp: Socket & Plan) -> IO(Unit):
  match f:
    case 0n:
      (s, pl) = sp
      Socket.close(s)
    case 1n+g:
      (s, pl) = sp
      match pl:
        case Stop{}:
          Socket.close(s)
        case End{out}:
          do IO<Unit>:
            m : Socket & Result<&1, &1, U32 & String, Unit> <-
              TCP.send_bytes(s, out)
            shut(m)
        case Feed{out, n}:
          do IO<Unit>:
            m   : Socket & Result<&1, &1, U32 & String, Unit> <-
              TCP.send_bytes(s, out)
            sp2 : Socket & Plan <- tick(m, n)
            conn(g, sp2)
        case Go{out, p2}:
          do IO<Unit>:
            m   : Socket & Result<&1, &1, U32 & String, Unit> <-
              TCP.send_bytes(s, out)
            sp2 : Socket & Plan <- turn(m, p2)
            conn(g, sp2)

# the most chunks one connection may ever ask for. It is a real bound,
# not a formality: it is what stops a peer from holding a computation
# open forever, and it is why conn needs no @unsafe.
def conn.fuel() -> Nat:
  U32.to_nat(1048576)

def start(s: Socket) -> IO(Unit):
  do IO<Unit>:
    m : Socket & Result<&1, &1, U32 & String, List<&2, U32>> <-
      TCP.recv_bytes(s, chunk())
    conn(conn.fuel(), plan.recv(m, p.new()))

def accept.one(m: Listener & Result<&1, &1, U32 & String, Socket>) ->
  IO(Listener):
  (l, r) = m
  do IO<Listener>:
    s : Socket <- IO.pass(Socket, r)
    IO.spawn(Unit, start(s))
    return l

# The accept loop is the one place that runs until the process is
# killed, so it is the one @unsafe def in the engine.
@unsafe
def accept(l: Listener) -> IO(Unit):
  do IO<Unit>:
    m  : Listener & Result<&1, &1, U32 & String, Socket> <- TCP.accept(l)
    l2 : Listener <- accept.one(m)
    accept(l2)

def port() -> U32:
  8080

def main() -> IO(Unit):
  do IO<Unit>:
    l : Listener <- IO.try(Listener, TCP.listen(port()))
    IO.print("bend-http on http://127.0.0.1:8080")
    accept(l)
