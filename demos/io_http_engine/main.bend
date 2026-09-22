# HTTP/1.1 engine: a streaming request parser, a router and a server,
# all in Bend. The parser is the point. It is one walk over whatever
# bytes a socket hands over, with no lookahead, no buffering of the head
# and no re-scanning: the whole reader state rides in one P node, so a
# head split across three recvs parses exactly like a head that arrives
# whole, and a chunk holding three pipelined requests yields three
# requests in that one walk.
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
# is how requests get smuggled: HTTP/1.1 only, exactly one Host,
# Content-Length only, that length all digits and the same wherever it
# is repeated, no Transfer-Encoding at all, and every field name known by
# its bytes. A space before a colon, a folded line, a bare LF, a control
# byte are each refused, and Bad{} is never left. LAWS.bend states those
# as laws and PROOF.bend proves them.
#
# Every byte on the wire is a byte. TCP.recv and TCP.send carry String,
# and a String is decoded as UTF-8, so a body that is not text comes
# back as one U+FFFD per ill-formed byte -- three bytes out for one in,
# while Content-Length still says one. That is a framing break, not a
# cost, so this engine reads Bytes through TCP.poll_buf and writes Bytes
# through TCP.send_buf: a read is one packed block, walked where it lies,
# and the target, the body and the key a request carries are views of
# it; every reply is built as Bytes and goes out as it lies in the heap.
#
#   bend demos/io_http_engine/main.bend -o httpd && ./httpd
#   curl -i http://127.0.0.1:8080/health
import Base
import ./ws.bend as Ws

# Bytes
# =====

# What a byte is to the head grammar (RFC 9110 5.6.2, RFC 9112 5): a
# space, a tab, the two line ends, the colon, the comma that separates
# list members, a digit, any other token character, any other visible
# byte (or obs-text), and a control, which no part of a head may carry.
# Every state below branches on these ten classes and nothing finer.
type Cls is Data:
  KSp{}
  KHt{}
  KCr{}
  KLf{}
  KCo{}
  KCm{}
  KDg{}
  KTk{}
  KVc{}
  KCt{}

def cls.low(sp: Bool, ht: Bool, cr: Bool, lf: Bool) -> Cls:
  match sp ht cr lf:
    case True{} _ _ _:
      KSp{}
    case _ True{} _ _:
      KHt{}
    case _ _ True{} _:
      KCr{}
    case _ _ _ True{}:
      KLf{}
    case _ _ _ _:
      KCt{}

# 127 is DEL, a control; past it is obs-text, which a value may carry
def cls.high(del: Bool) -> Cls:
  match del:
    case True{}:
      KCt{}
    case False{}:
      KVc{}

# the token characters that are neither letters nor digits, as the
# ranges they fall in: ! #$%&' *+ -. ^_` | ~
def tsym(+c: U32) -> Bool:
  U32.is_eq(c, 33) || (U32.is_le(35, c) && U32.is_le(c, 39)) || U32.is_eq(c, 42)
    || U32.is_eq(c, 43) || U32.is_eq(c, 45) || U32.is_eq(c, 46)
    || (U32.is_le(94, c) && U32.is_le(c, 96)) || U32.is_eq(c, 124) || U32.is_eq(c, 126)

def cls.sym(co: Bool, cm: Bool, tk: Bool) -> Cls:
  match co cm tk:
    case True{} _ _:
      KCo{}
    case _ True{} _:
      KCm{}
    case _ _ True{}:
      KTk{}
    case _ _ _:
      KVc{}

def alpha(+c: U32) -> Bool:
  (U32.is_le(65, c) && U32.is_le(c, 90)) || (U32.is_le(97, c) && U32.is_le(c, 122))

def digit(+c: U32) -> Bool:
  U32.is_le(48, c) && U32.is_le(c, 57)

def cls.vis(+c: U32, al: Bool, dg: Bool) -> Cls:
  match al dg:
    case True{} _:
      KTk{}
    case False{} True{}:
      KDg{}
    case False{} False{}:
      cls.sym(U32.is_eq(c, 58), U32.is_eq(c, 44), tsym(c))

def cls.go(+c: U32, lo: Bool, hi: Bool) -> Cls:
  match lo hi:
    case True{} _:
      cls.low(U32.is_eq(c, 32), U32.is_eq(c, 9), U32.is_eq(c, 13), U32.is_eq(c, 10))
    case False{} True{}:
      cls.high(U32.is_eq(c, 127))
    case False{} False{}:
      cls.vis(c, alpha(c), digit(c))

def cls(+c: U32) -> Cls:
  cls.go(c, U32.is_lt(c, 33), U32.is_le(127, c))

# Field names and list members are case-insensitive, so they are read
# lowercased: a byte as Char.to_lower has it, which is what lows() does
# to a whole name at once.
def lower(c: U32) -> U32:
  Char.to_u32(Char.to_lower(Chr{c}))

def lows(s: Bytes()) -> Bytes():
  String.to_lower(s)

# Byte lists are what the file names and the arguments are walked as.
def cat(a: List<&2, U32>, b: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, a, b)

def rev(a: List<&2, U32>) -> List<&2, U32>:
  List.reverse(&2, U32, a)

# An ASCII literal as a byte list. Written text stays readable in the
# source and becomes bytes here; a code point past 255 is not a byte and
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

# The reader's unit is Bytes: a read is one packed block, and a token is
# a run of it. one() is a single byte, push() a token grown by one; the
# walk below takes whole runs at once, which the laws say is the same.
def one(c: U32) -> Bytes():
  SCon{Chr{c}, SNil{}}

def push(b: Bytes(), c: U32) -> Bytes():
  Bytes.append(b, one(c))

def bnil(b: Bytes()) -> Bool:
  match b:
    case SNil{}:
      True{}
    case SCon{h, t}:
      False{}

# Byte equality, as the runtime compares two blocks: what names,
# methods, the version and routes are recognised by. LAWS.bend proves it
# is the reference's byte-by-byte equality.
def bytes.eq(a: Bytes(), b: Bytes()) -> Bool:
  String.eq(a, b)

# Names
# =====

# The fields this engine acts on. A name is recognised by its bytes,
# never by a digest of them: two names that differ in one byte are two
# names, so no other field can be taken for a Content-Length.
type Fld is Data:
  FTe{}
  FCl{}
  FConn{}
  FUp{}
  FKey{}
  FHost{}
  FVer{}
  FOther{}

# a name as the reader holds it, lowercased, and the field it names
type Known is Data:
  Known{k: Bytes(), f: Fld}

# LAWS.bend proves the lookup through this table is the lookup through
# the reference's
def fld.table() -> List<&2, Known>:
  [Known{"transfer-encoding", FTe{}},
   Known{"content-length", FCl{}},
   Known{"connection", FConn{}},
   Known{"upgrade", FUp{}},
   Known{"sec-websocket-key", FKey{}},
   Known{"host", FHost{}},
   Known{"sec-websocket-version", FVer{}}]

def fld.pick(b: Bool, f: Fld, rest: Fld) -> Fld:
  match b:
    case True{}:
      f
    case False{}:
      rest

# The lookup walks the table once with the name in hand: each entry is
# compared with the name as two blocks, the name handed back, and the
# first entry spelled with exactly its bytes is the field. LAWS.bend
# proves it is the reference's lookup.
def fld.hit.at(eq: Bool, f: Fld) -> Maybe<&2, Fld>:
  match eq:
    case True{}:
      Some{f}
    case False{}:
      None{}

def fld.hit(acc: Maybe<&2, Fld>, c: Cmp, f: Fld) -> Maybe<&2, Fld>:
  match acc:
    case None{}:
      fld.hit.at(Cmp.is_eq(c), f)
    case Some{g}:
      Some{g}

def fld.got(kc: (Bytes() & Bytes()) & Cmp, f: Fld, acc: Maybe<&2, Fld>) ->
  Bytes() & Maybe<&2, Fld>:
  (kn, c) = kc
  (k, n) = kn
  (k, fld.hit(acc, c, f))

def fld.one(k: Bytes(), n: Bytes(), f: Fld, acc: Maybe<&2, Fld>) -> Bytes() & Maybe<&2, Fld>:
  fld.got(String.cmp(k, n), f, acc)

def fld.done(ka: Bytes() & Maybe<&2, Fld>) -> Fld:
  (k, acc) = ka
  match acc:
    case None{}:
      FOther{}
    case Some{f}:
      f

def fld.scan(tbl: List<&2, Known>, ka: Bytes() & Maybe<&2, Fld>) -> Fld:
  match tbl:
    case Nil{}:
      fld.done(ka)
    case Con{h, t}:
      match h:
        case Known{n, f}:
          (k, acc) = ka
          fld.scan(t, fld.one(k, n, f, acc))

def fld.of(k: Bytes()) -> Fld:
  fld.scan(fld.table(), (k, None{}))

# the method, by its bytes: GET and HEAD are served, and anything else
# is a method this engine does not implement
type Meth is Data:
  MGet{}
  MHead{}
  MOther{}

def meth.pick(get: Bool, head: Bool) -> Meth:
  match get head:
    case True{} _:
      MGet{}
    case False{} True{}:
      MHead{}
    case False{} False{}:
      MOther{}

def meth.of(+m: Bytes()) -> Meth:
  meth.pick(bytes.eq(m, "GET"), bytes.eq(m, "HEAD"))

def meth.get(m: Meth) -> Bool:
  match m:
    case MGet{}:
      True{}
    case MHead{}:
      False{}
    case MOther{}:
      False{}

def meth.head(m: Meth) -> Bool:
  match m:
    case MGet{}:
      False{}
    case MHead{}:
      True{}
    case MOther{}:
      False{}

def ver.lit() -> Bytes():
  "HTTP/1.1"

# the list members this engine acts on: close and upgrade in a
# Connection, websocket in an Upgrade
def tok.close() -> Bytes():
  "close"

def tok.upgrade() -> Bytes():
  "upgrade"

def tok.websocket() -> Bytes():
  "websocket"

# Requests
# ========

# A parsed message: the method, the target and body as bytes, whether
# the peer asked to close, and whether it asked to become a WebSocket
# and with what key. A target, a body and a key that arrived within one
# read are views of it.
type Req is Data:
  Req{meth: Meth, path: Bytes(), body: Bytes(), close: Bool,
    ws: Bool, key: Bytes()}

def req.close(r: Req) -> Bool:
  match r:
    case Req{meth, path, body, close, ws, key}:
      close

def req.ws(r: Req) -> Bool:
  match r:
    case Req{meth, path, body, close, ws, key}:
      ws

# What a message has said about becoming a WebSocket. Plain{} is the
# answer for every request that never names one of the three headers,
# and it carries no fields, so the ordinary path allocates nothing for
# an upgrade that is not happening.
# vb says a Sec-WebSocket-Version named something other than 13.
type Up is Data:
  Plain{}
  Asks{key: Bytes(), up: Bool, cu: Bool, vb: Bool}

def up.key(u: Up, k: Bytes()) -> Up:
  match u:
    case Plain{}:
      Asks{k, False{}, False{}, False{}}
    case Asks{key, up, cu, vb}:
      Asks{k, up, cu, vb}

# an Upgrade or a Connection field adds to what the earlier ones said
def up.up(u: Up, v: Bool) -> Up:
  match u v:
    case Plain{} False{}:
      Plain{}
    case Plain{} True{}:
      Asks{"", True{}, False{}, False{}}
    case Asks{key, up, cu, vb} w:
      Asks{key, up || w, cu, vb}

def up.cu(u: Up, v: Bool) -> Up:
  match u v:
    case Plain{} False{}:
      Plain{}
    case Plain{} True{}:
      Asks{"", False{}, True{}, False{}}
    case Asks{key, up, cu, vb} w:
      Asks{key, up, cu || w, vb}

# a Sec-WebSocket-Version names 13, the one version there is, or not
def up.ver(u: Up, v: Bool) -> Up:
  match u v:
    case Plain{} True{}:
      Plain{}
    case Plain{} False{}:
      Asks{"", False{}, False{}, True{}}
    case Asks{key, up, cu, vb} w:
      Asks{key, up, cu, vb || Bool.not(w)}

def has(k: List<&2, U32>) -> Bool:
  match k:
    case Nil{}:
      False{}
    case Con{h, t}:
      True{}

# a message asks to become a WebSocket when it carried Upgrade:
# websocket, Connection: Upgrade and a key, and named no version but
# 13; one that named another is answered as one that did not ask, with
# the 426 that says which version to ask for
def up.asked(u: Up) -> Bool & Bytes():
  match u:
    case Plain{}:
      (False{}, "")
    case Asks{+key, up, cu, vb}:
      (up && cu && Bool.not(bnil(key)) && Bool.not(vb), key)

# The length a message announced: none, or one value every
# Content-Length field agreed on.
type Cl is Data:
  NoCl{}
  Has{v: U32}

# how many Host fields the message carried: HTTP/1.1 requires exactly one
type Hosts is Data:
  H0{}
  H1{}
  H2{}

# The fields of the message being read. It is rebuilt only when a token
# closes, so an ordinary byte leaves it untouched and shares it.
type Pend is Data:
  Pend{meth: Meth, path: Bytes(), cl: Cl, close: Bool, host: Hosts,
    ws: Up}

def pend.new() -> Pend:
  Pend{MOther{}, "", NoCl{}, False{}, H0{}, Plain{}}

# a new method token starts a new message, so the rest resets with it
def pend.meth(pd: Pend, m: Meth) -> Pend:
  match pd:
    case Pend{meth, path, cl, close, host, ws}:
      Pend{m, "", NoCl{}, False{}, H0{}, Plain{}}

def pend.path(pd: Pend, p: Bytes()) -> Pend:
  match pd:
    case Pend{meth, path, cl, close, host, ws}:
      Pend{meth, p, cl, close, host, ws}

def hosts.more(h: Hosts) -> Hosts:
  match h:
    case H0{}:
      H1{}
    case H1{}:
      H2{}
    case H2{}:
      H2{}

def pend.host(pd: Pend) -> Pend:
  match pd:
    case Pend{meth, path, cl, close, host, ws}:
      Pend{meth, path, cl, close, hosts.more(host), ws}

# a Connection value closes: close anywhere in its list asks to close,
# upgrade anywhere asks to upgrade
def pend.conn(pd: Pend, cl: Bool, up: Bool) -> Pend:
  match pd:
    case Pend{meth, path, c, close, host, ws}:
      Pend{meth, path, c, close || cl, host, up.cu(ws, up)}

def pend.up(pd: Pend, v: Bool) -> Pend:
  match pd:
    case Pend{meth, path, cl, close, host, ws}:
      Pend{meth, path, cl, close, host, up.up(ws, v)}

def pend.key(pd: Pend, k: Bytes()) -> Pend:
  match pd:
    case Pend{meth, path, cl, close, host, ws}:
      Pend{meth, path, cl, close, host, up.key(ws, k)}

def pend.ver(pd: Pend, v: Bool) -> Pend:
  match pd:
    case Pend{meth, path, cl, close, host, ws}:
      Pend{meth, path, cl, close, host, up.ver(ws, v)}

def pend.req.go(
  meth: Meth, path: Bytes(), body: Bytes(), close: Bool, asked: Bool & Bytes()
) -> Req:
  (ws, key) = asked
  Req{meth, path, body, close, ws, key}

def pend.req(pd: Pend, body: Bytes()) -> Req:
  match pd:
    case Pend{meth, path, cl, close, host, ws}:
      pend.req.go(meth, path, body, close, up.asked(ws))

# The reader
# ==========

# Pre  before a request line        PreLf the LF of an empty line there
# InM  the method                    InT  the target
# InV  the version                   CrM  a CR inside the head
# Lin  at the start of a field line  InN  a field name, as it came
# InL0 a Content-Length, no digit    InL  its digits, v so far
# InLt the whitespace after them     InLc a Connection list: the member
#                                         being read, close and upgrade seen
# InLu an Upgrade list, websocket    InLk0/InLk a Sec-WebSocket-Key value
# InLv a Sec-WebSocket-Version value InLx any other value, skipped
# CrL  the CR of the blank line      Bod  the body so far, and r more
#                                         bytes after the next one
# Rest what follows a request that asked to upgrade, for the frame reader
# Bad  the grammar broke; absorbing, and never left
type St is Data:
  Pre{}
  PreLf{}
  InM{m: Bytes()}
  InT{p: Bytes()}
  InV{v: Bytes()}
  CrM{}
  Lin{}
  InN{n: Bytes()}
  InL0{}
  InL{v: U32}
  InLt{v: U32}
  InLc{t: Bytes(), cl: Bool, up: Bool}
  InLu{t: Bytes(), ws: Bool}
  InLk0{}
  InLk{k: Bytes()}
  InLv{v: Bytes()}
  InLx{}
  CrL{}
  Bod{r: Nat, b: Bytes()}
  Rest{bs: Bytes()}
  Bad{}

# The whole reader: where the machine is, the message it is filling,
# and the messages it has finished, newest first.
type P is Data:
  P{st: St, pd: Pend, out: List<&2, Req>}

def p.new() -> P:
  P{Pre{}, pend.new(), Nil{}}

# after a message that asked to upgrade, what follows is not HTTP: it
# is kept as it came for the frame reader
def emit.next(ws: Bool) -> St:
  match ws:
    case True{}:
      Rest{""}
    case False{}:
      Pre{}

def emit.go(r: Req, out: List<&2, Req>) -> P:
  match r:
    case Req{meth, path, body, close, +ws, key}:
      P{emit.next(ws), pend.new(), Req{meth, path, body, close, ws, key} <> out}

# a completed message rolls the machine straight into the next one
def emit(pd: Pend, body: Bytes(), out: List<&2, Req>) -> P:
  emit.go(pend.req(pd, body), out)

# the method closes at its space, and a new message starts with it
def step.meth(+m: Bytes(), pd: Pend, out: List<&2, Req>) -> P:
  P{InT{""}, pend.meth(pd, meth.of(m)), out}

# the target closes at its space; an empty one is no target
def step.target(p: Bytes(), pd: Pend, out: List<&2, Req>) -> P:
  match p:
    case SNil{}:
      P{Bad{}, pd, out}
    case SCon{c, t}:
      P{InV{""}, pend.path(pd, SCon{c, t}), out}

# the version token must read exactly HTTP/1.1
def step.ver(ok: Bool, pd: Pend, out: List<&2, Req>) -> P:
  match ok:
    case True{}:
      P{CrM{}, pd, out}
    case False{}:
      P{Bad{}, pd, out}

# a name closes at its colon. A Transfer-Encoding is refused there,
# whatever it says: this engine frames by length only, and a message
# that names a second framing is how requests get smuggled.
def step.name(f: Fld, pd: Pend, out: List<&2, Req>) -> P:
  match f:
    case FTe{}:
      P{Bad{}, pd, out}
    case FCl{}:
      P{InL0{}, pd, out}
    case FConn{}:
      P{InLc{"", False{}, False{}}, pd, out}
    case FUp{}:
      P{InLu{"", False{}}, pd, out}
    case FKey{}:
      P{InLk0{}, pd, out}
    case FHost{}:
      P{InLx{}, pend.host(pd), out}
    case FVer{}:
      P{InLv{""}, pd, out}
    case FOther{}:
      P{InLx{}, pd, out}

# the most body this engine will hold for one message. A length past it
# is refused at the digit that crosses it, so an announced length is
# never a way to make the engine allocate, and never wraps: the value
# so far is at most this, so ten times it plus a digit fits a U32.
def body.cap() -> U32:
  1048576

def step.digit.go(+n: U32, pd: Pend, out: List<&2, Req>, big: Bool) -> P:
  match big:
    case True{}:
      P{Bad{}, pd, out}
    case False{}:
      P{InL{n}, pd, out}

def step.digit.n(+n: U32, pd: Pend, out: List<&2, Req>) -> P:
  step.digit.go(n, pd, out, U32.is_lt(body.cap(), n))

def step.digit(v: U32, c: U32, pd: Pend, out: List<&2, Req>) -> P:
  step.digit.n((v * 10 + (c - 48) : U32), pd, out)

# a second Content-Length must say what the first did (RFC 9112 6.3)
def step.clen.dup(pd: Pend, out: List<&2, Req>, agree: Bool) -> P:
  match agree:
    case True{}:
      P{CrM{}, pd, out}
    case False{}:
      P{Bad{}, pd, out}

def step.clen.go(
  meth: Meth, path: Bytes(), cl: Cl, close: Bool, host: Hosts, ws: Up,
  +v: U32, out: List<&2, Req>
) -> P:
  match cl:
    case NoCl{}:
      P{CrM{}, Pend{meth, path, Has{v}, close, host, ws}, out}
    case Has{+w}:
      step.clen.dup(Pend{meth, path, Has{w}, close, host, ws}, out, U32.is_eq(v, w))

# a Content-Length value closes
def step.clen(+v: U32, pd: Pend, out: List<&2, Req>) -> P:
  match pd:
    case Pend{meth, path, cl, close, host, ws}:
      step.clen.go(meth, path, cl, close, host, ws, v, out)

# a list member closes at a comma, a space or the line's end
def step.conn(+t: Bytes(), cl: Bool, up: Bool, pd: Pend, out: List<&2, Req>) -> P:
  P{CrM{}, pend.conn(pd, cl || bytes.eq(t, tok.close()), up || bytes.eq(t, tok.upgrade())), out}

def tok.conn(+t: Bytes(), cl: Bool, up: Bool) -> St:
  InLc{"", cl || bytes.eq(t, tok.close()), up || bytes.eq(t, tok.upgrade())}

def step.upv(+t: Bytes(), ws: Bool, pd: Pend, out: List<&2, Req>) -> P:
  P{CrM{}, pend.up(pd, ws || bytes.eq(t, tok.websocket())), out}

def tok.up(+t: Bytes(), ws: Bool) -> St:
  InLu{"", ws || bytes.eq(t, tok.websocket())}

# a Sec-WebSocket-Key value closes, kept as it came
def step.key(k: Bytes(), pd: Pend, out: List<&2, Req>) -> P:
  P{CrM{}, pend.key(pd, k), out}

# a Sec-WebSocket-Version value closes: it named 13 or not
def step.wsv(+v: Bytes(), pd: Pend, out: List<&2, Req>) -> P:
  P{CrM{}, pend.ver(pd, bytes.eq(v, "13")), out}

# a body of v bytes: none emits the message now; otherwise the count is
# of the bytes after the next one, so the last byte is the one it finds
# at zero
def step.head.len(pd: Pend, +v: U32, out: List<&2, Req>, z: Bool) -> P:
  match z:
    case True{}:
      emit(pd, "", out)
    case False{}:
      P{Bod{Nat.sub(U32.to_nat(v), 1n), ""}, pd, out}

def step.head.at(pd: Pend, cl: Cl, host: Hosts, out: List<&2, Req>) -> P:
  match cl host:
    case NoCl{} H1{}:
      emit(pd, "", out)
    case Has{+v} H1{}:
      step.head.len(pd, v, out, U32.is_zero(v))
    case _ _:
      P{Bad{}, pd, out}

# the blank line closes the head: a message without exactly one Host is
# refused (RFC 9112 3.2); one without a length has no body; one with a
# length starts counting it down
def step.head(pd: Pend, out: List<&2, Req>) -> P:
  match pd:
    case Pend{meth, path, +cl, close, +host, ws}:
      step.head.at(Pend{meth, path, cl, close, host, ws}, cl, host, out)

# one body byte: the last one emits the message, the rest accumulate
def step.body(r: Nat, b: Bytes(), c: U32, pd: Pend, out: List<&2, Req>) -> P:
  match r:
    case 0n:
      emit(pd, push(b, c), out)
    case 1n+q:
      P{Bod{q, push(b, c)}, pd, out}

# The machine: one classified byte moves it once. A token state grows
# its bytes until its delimiter arrives; the delimiter closes the token
# into the pending message and hands over. Any byte a state has no row
# for breaks the grammar: a space before a colon, a line folded onto
# the one before, a bare LF, a control in a value or the target, a
# length that is not all digits.
def step.at(st: St, k: Cls, +c: U32, pd: Pend, out: List<&2, Req>) -> P:
  match st k:
    case Pre{} KCr{}:
      P{PreLf{}, pd, out}
    case Pre{} KTk{}:
      P{InM{one(c)}, pd, out}
    case Pre{} KDg{}:
      P{InM{one(c)}, pd, out}
    case Pre{} _:
      P{Bad{}, pd, out}
    case PreLf{} KLf{}:
      P{Pre{}, pd, out}
    case PreLf{} _:
      P{Bad{}, pd, out}
    case InM{m} KSp{}:
      step.meth(m, pd, out)
    case InM{m} KTk{}:
      P{InM{push(m, c)}, pd, out}
    case InM{m} KDg{}:
      P{InM{push(m, c)}, pd, out}
    case InM{m} _:
      P{Bad{}, pd, out}
    case InT{p} KSp{}:
      step.target(p, pd, out)
    case InT{p} KHt{}:
      P{Bad{}, pd, out}
    case InT{p} KCr{}:
      P{Bad{}, pd, out}
    case InT{p} KLf{}:
      P{Bad{}, pd, out}
    case InT{p} KCt{}:
      P{Bad{}, pd, out}
    case InT{p} _:
      P{InT{push(p, c)}, pd, out}
    case InV{+v} KCr{}:
      step.ver(bytes.eq(v, ver.lit()), pd, out)
    case InV{v} KTk{}:
      P{InV{push(v, c)}, pd, out}
    case InV{v} KDg{}:
      P{InV{push(v, c)}, pd, out}
    case InV{v} KVc{}:
      P{InV{push(v, c)}, pd, out}
    case InV{v} _:
      P{Bad{}, pd, out}
    case CrM{} KLf{}:
      P{Lin{}, pd, out}
    case CrM{} _:
      P{Bad{}, pd, out}
    case Lin{} KCr{}:
      P{CrL{}, pd, out}
    case Lin{} KTk{}:
      P{InN{one(c)}, pd, out}
    case Lin{} KDg{}:
      P{InN{one(c)}, pd, out}
    case Lin{} _:
      P{Bad{}, pd, out}
    case InN{n} KCo{}:
      step.name(fld.of(lows(n)), pd, out)
    case InN{n} KTk{}:
      P{InN{push(n, c)}, pd, out}
    case InN{n} KDg{}:
      P{InN{push(n, c)}, pd, out}
    case InN{n} _:
      P{Bad{}, pd, out}
    case InL0{} KSp{}:
      P{InL0{}, pd, out}
    case InL0{} KHt{}:
      P{InL0{}, pd, out}
    case InL0{} KDg{}:
      step.digit(0, c, pd, out)
    case InL0{} _:
      P{Bad{}, pd, out}
    case InL{v} KDg{}:
      step.digit(v, c, pd, out)
    case InL{v} KSp{}:
      P{InLt{v}, pd, out}
    case InL{v} KHt{}:
      P{InLt{v}, pd, out}
    case InL{v} KCr{}:
      step.clen(v, pd, out)
    case InL{v} _:
      P{Bad{}, pd, out}
    case InLt{v} KSp{}:
      P{InLt{v}, pd, out}
    case InLt{v} KHt{}:
      P{InLt{v}, pd, out}
    case InLt{v} KCr{}:
      step.clen(v, pd, out)
    case InLt{v} _:
      P{Bad{}, pd, out}
    case InLc{t, a, b} KCr{}:
      step.conn(t, a, b, pd, out)
    case InLc{t, a, b} KSp{}:
      P{tok.conn(t, a, b), pd, out}
    case InLc{t, a, b} KHt{}:
      P{tok.conn(t, a, b), pd, out}
    case InLc{t, a, b} KCm{}:
      P{tok.conn(t, a, b), pd, out}
    case InLc{t, a, b} KLf{}:
      P{Bad{}, pd, out}
    case InLc{t, a, b} KCt{}:
      P{Bad{}, pd, out}
    case InLc{t, a, b} _:
      P{InLc{push(t, lower(c)), a, b}, pd, out}
    case InLu{t, w} KCr{}:
      step.upv(t, w, pd, out)
    case InLu{t, w} KSp{}:
      P{tok.up(t, w), pd, out}
    case InLu{t, w} KHt{}:
      P{tok.up(t, w), pd, out}
    case InLu{t, w} KCm{}:
      P{tok.up(t, w), pd, out}
    case InLu{t, w} KLf{}:
      P{Bad{}, pd, out}
    case InLu{t, w} KCt{}:
      P{Bad{}, pd, out}
    case InLu{t, w} _:
      P{InLu{push(t, lower(c)), w}, pd, out}
    case InLk0{} KSp{}:
      P{InLk0{}, pd, out}
    case InLk0{} KHt{}:
      P{InLk0{}, pd, out}
    case InLk0{} KCr{}:
      step.key("", pd, out)
    case InLk0{} KLf{}:
      P{Bad{}, pd, out}
    case InLk0{} KCt{}:
      P{Bad{}, pd, out}
    case InLk0{} _:
      P{InLk{one(c)}, pd, out}
    case InLk{k} KCr{}:
      step.key(k, pd, out)
    case InLk{k} KLf{}:
      P{Bad{}, pd, out}
    case InLk{k} KCt{}:
      P{Bad{}, pd, out}
    case InLk{k} _:
      P{InLk{push(k, c)}, pd, out}
    case InLv{v} KSp{}:
      P{InLv{v}, pd, out}
    case InLv{v} KHt{}:
      P{InLv{v}, pd, out}
    case InLv{v} KCr{}:
      step.wsv(v, pd, out)
    case InLv{v} KLf{}:
      P{Bad{}, pd, out}
    case InLv{v} KCt{}:
      P{Bad{}, pd, out}
    case InLv{v} _:
      P{InLv{push(v, c)}, pd, out}
    case InLx{} KCr{}:
      P{CrM{}, pd, out}
    case InLx{} KLf{}:
      P{Bad{}, pd, out}
    case InLx{} KCt{}:
      P{Bad{}, pd, out}
    case InLx{} _:
      P{InLx{}, pd, out}
    case CrL{} KLf{}:
      step.head(pd, out)
    case CrL{} _:
      P{Bad{}, pd, out}
    case Bod{r, b} _:
      step.body(r, b, c, pd, out)
    case Rest{bs} _:
      P{Rest{push(bs, c)}, pd, out}
    case Bad{} _:
      P{Bad{}, pd, out}

def step(p: P, +c: U32) -> P:
  match p:
    case P{st, pd, out}:
      step.at(st, cls(c), c, pd, out)

# feed: the machine over a byte list, one byte at a time. The reader
# state that comes out is the reader state to feed the next chunk, so a
# message split anywhere parses exactly like a message that arrived
# whole. It is the reference the engine's own walk, feed_buf, is proved
# equal to.
def feed(s: List<&2, U32>, p: P) -> P:
  match s:
    case Nil{}:
      p
    case Con{c, t}:
      feed(t, step(p, c))

# The same walk over Bytes, a byte at a time.
def feed_buf.slow(s: Bytes(), p: P) -> P:
  match s:
    case SNil{}:
      p
    case SCon{Chr{c}, t}:
      feed_buf.slow(t, step(p, c))

# The walk the engine runs. Where a state reads a run of bytes without
# a transition -- a method, a target, a version, a name, a key, a value
# it skips, a body -- the run is found and taken whole: one cut of the
# read, so a target or a body within one read is a view of it and not a
# byte rebuilt. Every other byte is one step. LAWS.bend proves the walk
# is feed, byte for byte.
type Run is Data:
  RM{}
  RT{}
  RV{}
  RN{}
  RK{}
  RX{}

# which classes a run carries: exactly the ones step keeps it on
def run.stay(sel: Run, k: Cls) -> Bool:
  match sel k:
    case RM{} KTk{}:
      True{}
    case RM{} KDg{}:
      True{}
    case RM{} _:
      False{}
    case RT{} KSp{}:
      False{}
    case RT{} KHt{}:
      False{}
    case RT{} KCr{}:
      False{}
    case RT{} KLf{}:
      False{}
    case RT{} KCt{}:
      False{}
    case RT{} _:
      True{}
    case RV{} KTk{}:
      True{}
    case RV{} KDg{}:
      True{}
    case RV{} KVc{}:
      True{}
    case RV{} _:
      False{}
    case RN{} KTk{}:
      True{}
    case RN{} KDg{}:
      True{}
    case RN{} _:
      False{}
    case RK{} KCr{}:
      False{}
    case RK{} KLf{}:
      False{}
    case RK{} KCt{}:
      False{}
    case RK{} _:
      True{}
    case RX{} KCr{}:
      False{}
    case RX{} KLf{}:
      False{}
    case RX{} KCt{}:
      False{}
    case RX{} _:
      True{}

# the state a run is in, holding the bytes read so far
def st.put(sel: Run, acc: Bytes()) -> St:
  match sel:
    case RM{}:
      InM{acc}
    case RT{}:
      InT{acc}
    case RV{}:
      InV{acc}
    case RN{}:
      InN{acc}
    case RK{}:
      InLk{acc}
    case RX{}:
      InLx{}

def run.inc(ok: Bool, k: Nat) -> Nat:
  match ok:
    case True{}:
      1n+k
    case False{}:
      k

# how many bytes of s, from its first, the run carries. It looks one
# byte past the run and no further.
def run.len(s: Bytes(), go: Bool, +sel: Run, k: Nat) -> Nat:
  match s go:
    case SNil{} _:
      k
    case SCon{h, t} False{}:
      k
    case SCon{Chr{c}, t} True{}:
      +ok = run.stay(sel, cls(c))
      run.len(t, ok, sel, run.inc(ok, k))

# one byte, stepped
def one.step(p: P, s: Bytes()) -> P & Bytes():
  match s:
    case SNil{}:
      (p, SNil{})
    case SCon{Chr{c}, t}:
      (step(p, c), t)

# the run is cut from the read, and the byte that ended it is stepped
# at once
def run.took(+sel: Run, acc: Bytes(), pd: Pend, out: List<&2, Req>, ab: Bytes() & Bytes()) ->
  P & Bytes():
  (a, b) = ab
  one.step(P{st.put(sel, Bytes.append(acc, a)), pd, out}, b)

def run.cut(+sel: Run, acc: Bytes(), s: Bytes(), pd: Pend, out: List<&2, Req>, k: Nat) ->
  P & Bytes():
  match k:
    case 0n:
      one.step(P{st.put(sel, acc), pd, out}, s)
    case 1n+j:
      run.took(sel, acc, pd, out, String.cut(s, 1n+j))

def run.go(+sel: Run, acc: Bytes(), +s: Bytes(), pd: Pend, out: List<&2, Req>) -> P & Bytes():
  run.cut(sel, acc, s, pd, out, run.len(s, True{}, sel, 0n))

# A method starts at the first byte of a request line and a name at the
# first byte of a field line, and each is a run from that byte: the
# state before it steps that byte exactly as the run's empty state
# does, so the whole token is one cut and a view of the read.
type Ent is Data:
  EMeth{}
  EName{}

def ent.sel(e: Ent) -> Run:
  match e:
    case EMeth{}:
      RM{}
    case EName{}:
      RN{}

def ent.st(e: Ent) -> St:
  match e:
    case EMeth{}:
      Pre{}
    case EName{}:
      Lin{}

def ent.cut(+e: Ent, s: Bytes(), pd: Pend, out: List<&2, Req>, k: Nat) -> P & Bytes():
  match k:
    case 0n:
      one.step(P{ent.st(e), pd, out}, s)
    case 1n+j:
      run.took(ent.sel(e), "", pd, out, String.cut(s, 1n+j))

def ent.go(+e: Ent, +s: Bytes(), pd: Pend, out: List<&2, Req>) -> P & Bytes():
  ent.cut(e, s, pd, out, run.len(s, True{}, ent.sel(e), 0n))

# a value skipped: walked where it lies and nothing kept, and the byte
# that ends it stepped at once. go says whether c, the byte before s,
# was part of the value; the first call has none.
def skip(s: Bytes(), go: Bool, c: U32, pd: Pend, out: List<&2, Req>) -> P & Bytes():
  match s go:
    case _ False{}:
      (step(P{InLx{}, pd, out}, c), s)
    case SNil{} True{}:
      (P{InLx{}, pd, out}, SNil{})
    case SCon{Chr{+x}, t} True{}:
      skip(t, run.stay(RX{}, cls(x)), x, pd, out)

# a body: all of the read when the body goes on past it, else the r + 1
# bytes that end it, with the message emitted
def bod.took(pd: Pend, out: List<&2, Req>, b: Bytes(), xy: Bytes() & Bytes()) -> P & Bytes():
  (x, y) = xy
  (emit(pd, Bytes.append(b, x), out), y)

def bod.at(+r: Nat, b: Bytes(), +s: Bytes(), pd: Pend, out: List<&2, Req>, done: Bool) ->
  P & Bytes():
  match done:
    case False{}:
      (P{Bod{Nat.sub(r, Bytes.len(s)), Bytes.append(b, s)}, pd, out}, "")
    case True{}:
      bod.took(pd, out, b, String.cut(s, 1n+r))

def bod.go(+r: Nat, b: Bytes(), +s: Bytes(), pd: Pend, out: List<&2, Req>) -> P & Bytes():
  bod.at(r, b, s, pd, out, Nat.is_lt(r, Bytes.len(s)))

# one move of the walk: a run, a body, the rest after an upgrade, or
# one byte
def adv.at(st: St, s: Bytes(), pd: Pend, out: List<&2, Req>) -> P & Bytes():
  match st:
    case InM{m}:
      run.go(RM{}, m, s, pd, out)
    case InT{p}:
      run.go(RT{}, p, s, pd, out)
    case InV{v}:
      run.go(RV{}, v, s, pd, out)
    case InN{n}:
      run.go(RN{}, n, s, pd, out)
    case InLk{k}:
      run.go(RK{}, k, s, pd, out)
    case InLx{}:
      skip(s, True{}, 0, pd, out)
    case Bod{r, b}:
      bod.go(r, b, s, pd, out)
    case Rest{bs}:
      (P{Rest{Bytes.append(bs, s)}, pd, out}, "")
    case Pre{}:
      ent.go(EMeth{}, s, pd, out)
    case PreLf{}:
      one.step(P{PreLf{}, pd, out}, s)
    case CrM{}:
      one.step(P{CrM{}, pd, out}, s)
    case Lin{}:
      ent.go(EName{}, s, pd, out)
    case InL0{}:
      one.step(P{InL0{}, pd, out}, s)
    case InL{v}:
      one.step(P{InL{v}, pd, out}, s)
    case InLt{v}:
      one.step(P{InLt{v}, pd, out}, s)
    case InLc{t, a, b}:
      one.step(P{InLc{t, a, b}, pd, out}, s)
    case InLu{t, w}:
      one.step(P{InLu{t, w}, pd, out}, s)
    case InLk0{}:
      one.step(P{InLk0{}, pd, out}, s)
    case InLv{v}:
      one.step(P{InLv{v}, pd, out}, s)
    case CrL{}:
      one.step(P{CrL{}, pd, out}, s)
    case Bad{}:
      (P{Bad{}, pd, out}, "")

def adv(s: Bytes(), p: P) -> P & Bytes():
  match p:
    case P{st, pd, out}:
      adv.at(st, s, pd, out)

# the rest of a walk the fuel ran out on, a byte at a time
def feed_buf.last(q: P & Bytes()) -> P:
  (p, s) = q
  feed_buf.slow(s, p)

# n bounds the moves; every move takes at least one byte, so a walk
# over n bytes never runs out
def feed_buf.go(n: Nat, q: P & Bytes()) -> P:
  match n:
    case 0n:
      feed_buf.last(q)
    case 1n+m:
      (p, s) = q
      match s:
        case SNil{}:
          p
        case SCon{h, t}:
          feed_buf.go(m, adv(SCon{h, t}, p))

def feed_buf(+s: Bytes(), p: P) -> P:
  feed_buf.go(Bytes.len(s), (p, s))

# the finished messages, oldest first, and the reader with them cleared
def p.take(p: P) -> P & List<&2, Req>:
  match p:
    case P{st, pd, out}:
      (P{st, pd, Nil{}}, List.reverse(&2, Req, out))

def st.dead(st: St) -> St & Bool:
  match st:
    case Bad{}:
      (Bad{}, True{})
    case Pre{}:
      (Pre{}, False{})
    case PreLf{}:
      (PreLf{}, False{})
    case InM{m}:
      (InM{m}, False{})
    case InT{p}:
      (InT{p}, False{})
    case InV{v}:
      (InV{v}, False{})
    case CrM{}:
      (CrM{}, False{})
    case Lin{}:
      (Lin{}, False{})
    case InN{n}:
      (InN{n}, False{})
    case InL0{}:
      (InL0{}, False{})
    case InL{v}:
      (InL{v}, False{})
    case InLt{v}:
      (InLt{v}, False{})
    case InLc{t, a, b}:
      (InLc{t, a, b}, False{})
    case InLu{t, w}:
      (InLu{t, w}, False{})
    case InLk0{}:
      (InLk0{}, False{})
    case InLk{k}:
      (InLk{k}, False{})
    case InLv{v}:
      (InLv{v}, False{})
    case InLx{}:
      (InLx{}, False{})
    case CrL{}:
      (CrL{}, False{})
    case Bod{r, b}:
      (Bod{r, b}, False{})
    case Rest{bs}:
      (Rest{bs}, False{})

def p.dead.at(sd: St & Bool, pd: Pend, out: List<&2, Req>) -> P & Bool:
  (st, d) = sd
  (P{st, pd, out}, d)

# whether the grammar broke, with the reader handed back
def p.dead(p: P) -> P & Bool:
  match p:
    case P{st, pd, out}:
      p.dead.at(st.dead(st), pd, out)

# the bytes that followed a request that asked to upgrade, in order
def p.rest(p: P) -> Bytes():
  match p:
    case P{st, pd, out}:
      match st:
        case Rest{bs}:
          bs
        case _:
          ""

# A whole input, parsed from a fresh reader by the engine's own walk:
# the messages it completed, oldest first, and whether the grammar
# broke. LAWS.bend holds the reader to this on the vectors that matter.
def parse.out(pr: P & List<&2, Req>, dead: Bool) -> List<&2, Req> & Bool:
  (p, rs) = pr
  (rs, dead)

def parse.of(pb: P & Bool) -> List<&2, Req> & Bool:
  (p, dead) = pb
  parse.out(p.take(p), dead)

def parse(bs: Bytes()) -> List<&2, Req> & Bool:
  parse.of(p.dead(feed_buf(bs, p.new())))

# whether the reader is part way through a head: past the first byte of
# a request line and short of its blank line. A body is not a head.
def st.head(st: St) -> Bool:
  match st:
    case Pre{}:
      False{}
    case PreLf{}:
      False{}
    case Bod{r, b}:
      False{}
    case Rest{bs}:
      False{}
    case Bad{}:
      False{}
    case _:
      True{}

def p.head(+p: P) -> Bool:
  match p:
    case P{st, pd, out}:
      st.head(st)


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
  "HTTP/1.1 400 Bad Request\r\ncontent-type: text/plain\r\ncontent-length: 12\r\nconnection: close\r\n\r\nbad request\n"

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
    grace: U32, shared: Bool, pem: Maybe<&2, Pem>, head: U32}

def cfg.new() -> Cfg:
  Cfg{8080, None{}, False{}, 10000, 1024, 5000, False{}, None{}, 10000}

def cfg.port(c: Cfg) -> U32:
  match c:
    case Cfg{port, root, log, idle, conns, grace, shared, pem, head}:
      port

# how long a connection may be silent, in ms, before it is dropped
def cfg.idle(c: Cfg) -> U32:
  match c:
    case Cfg{port, root, log, idle, conns, grace, shared, pem, head}:
      idle

def cfg.root(c: Cfg) -> List<&2, U32>:
  match c:
    case Cfg{port, root, log, idle, conns, grace, shared, pem, head}:
      Maybe.default(&2, List<&2, U32>, root, bytes("."))

def cfg.set_port(c: Cfg, n: U32) -> Cfg:
  match c:
    case Cfg{port, root, log, idle, conns, grace, shared, pem, head}:
      Cfg{n, root, log, idle, conns, grace, shared, pem, head}

# the most connections open at once; past it, accepting waits
def cfg.conns(c: Cfg) -> U32:
  match c:
    case Cfg{port, root, log, idle, conns, grace, shared, pem, head}:
      conns

# how long open connections get to finish after a stop is asked, in ms
def cfg.grace(c: Cfg) -> U32:
  match c:
    case Cfg{port, root, log, idle, conns, grace, shared, pem, head}:
      grace

def cfg.set_conns(c: Cfg, n: U32) -> Cfg:
  match c:
    case Cfg{port, root, log, idle, conns, grace, shared, pem, head}:
      Cfg{port, root, log, idle, n, grace, shared, pem, head}

def cfg.set_grace(c: Cfg, n: U32) -> Cfg:
  match c:
    case Cfg{port, root, log, idle, conns, grace, shared, pem, head}:
      Cfg{port, root, log, idle, conns, n, shared, pem, head}

# whether the port is shared with other copies of this server
def cfg.log(c: Cfg) -> Bool:
  match c:
    case Cfg{port, root, log, idle, conns, grace, shared, pem, head}:
      log

# the certificate and key a TLS listener needs, if the server was given
# a pair; the half-given pair is refused when the arguments are read
def cfg.pem(c: Cfg) -> Maybe<&2, Pem>:
  match c:
    case Cfg{port, root, log, idle, conns, grace, shared, pem, head}:
      pem

def cfg.set_cert(c: Cfg, p: List<&2, U32>) -> Cfg:
  match c:
    case Cfg{port, root, log, idle, conns, grace, shared, pem, head}:
      Cfg{port, root, log, idle, conns, grace, shared, pem.cert(pem, p), head}

def cfg.set_key(c: Cfg, p: List<&2, U32>) -> Cfg:
  match c:
    case Cfg{port, root, log, idle, conns, grace, shared, pem, head}:
      Cfg{port, root, log, idle, conns, grace, shared, pem.key(pem, p), head}

def cfg.shared(c: Cfg) -> Bool:
  match c:
    case Cfg{port, root, log, idle, conns, grace, shared, pem, head}:
      shared

def cfg.set_shared(c: Cfg) -> Cfg:
  match c:
    case Cfg{port, root, log, idle, conns, grace, shared, pem, head}:
      Cfg{port, root, log, idle, conns, grace, True{}, pem, head}

def cfg.set_idle(c: Cfg, n: U32) -> Cfg:
  match c:
    case Cfg{port, root, log, idle, conns, grace, shared, pem, head}:
      Cfg{port, root, log, n, conns, grace, shared, pem, head}

def cfg.set_root(c: Cfg, dir: List<&2, U32>) -> Cfg:
  match c:
    case Cfg{port, root, log, idle, conns, grace, shared, pem, head}:
      Cfg{port, Some{dir}, log, idle, conns, grace, shared, pem, head}

# how long a request head may take to arrive, in ms, however it is
# spread over reads: the idle time bounds each wait, this bounds them all
def cfg.head(c: Cfg) -> U32:
  match c:
    case Cfg{port, root, log, idle, conns, grace, shared, pem, head}:
      head

def cfg.set_head(c: Cfg, n: U32) -> Cfg:
  match c:
    case Cfg{port, root, log, idle, conns, grace, shared, pem, head}:
      Cfg{port, root, log, idle, conns, grace, shared, pem, n}

def cfg.set_log(c: Cfg) -> Cfg:
  match c:
    case Cfg{port, root, log, idle, conns, grace, shared, pem, head}:
      Cfg{port, root, True{}, idle, conns, grace, shared, pem, head}

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
  HeadOf{}
  Wrong{why: List<&2, U32>}

type Args is Data:
  Args{cfg: Cfg, want: Want}

# the flags that take a path, and the head budget, split out so the one
# match below stays readable rather than nine deep
def args.pem(c: Cfg, +a: List<&2, U32>, cert: Bool, key: Bool, head: Bool) -> Args:
  match cert key head:
    case True{} _ _:
      Args{c, CertOf{}}
    case False{} True{} _:
      Args{c, KeyOf{}}
    case False{} False{} True{}:
      Args{c, HeadOf{}}
    case False{} False{} False{}:
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
        beq(a, bytes("--tls-key"), True{}), beq(a, bytes("--head-ms"), True{}))

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

# a head budget of zero would refuse every head that takes two reads
def args.head(c: Cfg, a: List<&2, U32>, ok: Bool) -> Args:
  match ok:
    case True{}:
      Args{cfg.set_head(c, u32.of(a, 0)), Flag{}}
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
        case HeadOf{}:
          args.head(c, a, digits(a) && Bool.not(U32.is_zero(u32.of(a, 0))))
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
        case HeadOf{}:
          IO.die(Cfg, 2, "--head-ms needs a number")
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

# The same reply, saying it is the last on its connection. Every head
# this engine writes ends "connection: keep-alive" and a blank line;
# those fourteen bytes become "close" and the blank line, and the body
# follows as it was. A reply that ends its connection says so (RFC 9112
# 9.6), and only that one reply per connection pays for the rewrite.
def closing.at(+bs: Bytes(), m: Maybe<&2, Nat>) -> Bytes():
  match m:
    case None{}:
      bs
    case Some{+i}:
      Bytes.concat([Bytes.slice(bs, 0n, i), "close\r\n\r\n", Bytes.drop(bs, Nat.add(i, 14n))])

def closing(+bs: Bytes()) -> Bytes():
  closing.at(bs, Bytes.find(bs, "keep-alive\r\n\r\n"))

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
  Route{path: Bytes(), prefix: Bool, act: Act}

def routes.base() -> List<&2, Route>:
  [Route{"/health", False{}, Health{}},
   Route{"/echo", False{}, Echo{}},
   Route{"/events", False{}, Events{}},
   Route{"/ws", False{}, Live{}}]

# with a root directory everything the fixed routes leave is a file
# under it, "/" included; without one "/" is the banner
def routes.tail(root: Maybe<&2, List<&2, U32>>) -> List<&2, Route>:
  match root:
    case None{}:
      [Route{"/", False{}, Root{}}]
    case Some{dir}:
      [Route{"/", True{}, Files{}}]

def routes(c: Cfg) -> List<&2, Route>:
  match c:
    case Cfg{port, root, log, idle, conns, grace, shared, pem, head}:
      List.append(&2, Route, routes.base(), routes.tail(root))

def hit(rp: Bytes(), path: Bytes(), prefix: Bool) -> Bool:
  match prefix:
    case True{}:
      Bytes.starts_with(path, rp)
    case False{}:
      bytes.eq(rp, path)

def route.one.go(act: Act, ok: Bool) -> Maybe<&2, Act>:
  match ok:
    case True{}:
      Some{act}
    case False{}:
      None{}

def route.one(r: Route, path: Bytes()) -> Maybe<&2, Act>:
  match r:
    case Route{rp, prefix, act}:
      route.one.go(act, hit(rp, path, prefix))

# an entry is only tested while nothing earlier has matched
def route.keep(acc: Maybe<&2, Act>, r: Route, path: Bytes()) -> Maybe<&2, Act>:
  match acc:
    case Some{a}:
      Some{a}
    case None{}:
      route.one(r, path)

def route.go(table: List<&2, Route>, +path: Bytes(), acc: Maybe<&2, Act>) -> Maybe<&2, Act>:
  match table:
    case Nil{}:
      acc
    case Con{r, t}:
      route.go(t, path, route.keep(acc, r, path))

# the first entry that matches wins
def route(table: List<&2, Route>, +path: Bytes()) -> Maybe<&2, Act>:
  route.go(table, path, None{})

# no two entries claim one path
def same(a: Route, b: Route) -> Bool:
  match a b:
    case Route{p, x, i} Route{q, y, j}:
      bytes.eq(p, q)

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

def srv.head(s: Srv) -> U32:
  match s:
    case Srv{c, table}:
      cfg.head(c)

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

# a control byte: below 32, or DEL
def ctl(+c: U32) -> Bool:
  U32.is_lt(c, 32) || U32.is_eq(c, 127)

# a byte of a request target a file may be named by: printable ASCII
# and not a backslash, so never a control byte
def clean.pick(bad: Bool, +c: U32) -> Bool:
  match bad:
    case True{}:
      False{}
    case False{}:
      U32.is_le(33, c) && U32.is_le(c, 126) && Bool.not(U32.is_eq(c, 92))

def clean.go(bs: List<&2, U32>, ok: Bool) -> Bool:
  match bs:
    case Nil{}:
      ok
    case Con{+c, t}:
      clean.go(t, ok && clean.pick(ctl(c), c))

def clean(bs: List<&2, U32>) -> Bool:
  clean.go(bs, True{})

# What a file under the root may be named by, segment by segment: some
# bytes, all printable ASCII other than '/' and '\', and not a dotfile
# (a first byte of '.') unless dot says dotfiles are served, in which
# case still never "." or "..". LAWS.bend states the same rule on its
# own and proves every path page() opens keeps it.
def fname.byte(+c: U32) -> Bool:
  U32.is_le(33, c) && U32.is_le(c, 126) && Bool.not(U32.is_eq(c, 47))
    && Bool.not(U32.is_eq(c, 92))

def fname.bytes(bs: List<&2, U32>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{+c, t}:
      fname.byte(c) && fname.bytes(t)

def fname.lead(dot: Bool, +c: U32, +s: List<&2, U32>) -> Bool:
  match dot:
    case True{}:
      Bool.not(beq(s, [46], True{}) || beq(s, [46, 46], True{}))
    case False{}:
      Bool.not(U32.is_eq(c, 46))

def fname.ok(dot: Bool, s: List<&2, U32>) -> Bool:
  match s:
    case Nil{}:
      False{}
    case Con{+c, +t}:
      fname.lead(dot, c, Con{c, t}) && fname.bytes(Con{c, t})

def fnames.ok(+dot: Bool, ss: List<&2, List<&2, U32>>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case Con{s, t}:
      fname.ok(dot, s) && fnames.ok(dot, t)

def fnames.keep(ss: List<&2, List<&2, U32>>, ok: Bool) -> Maybe<&2, List<&2, List<&2, U32>>>:
  match ok:
    case True{}:
      Some{ss}
    case False{}:
      None{}

def fnames.guard(+dot: Bool, may: Maybe<&2, List<&2, List<&2, U32>>>) ->
  Maybe<&2, List<&2, List<&2, U32>>>:
  match may:
    case None{}:
      None{}
    case Some{+ss}:
      fnames.keep(ss, fnames.ok(dot, ss))

def fnames.gate(ok: Bool, may: Maybe<&2, List<&2, List<&2, U32>>>) ->
  Maybe<&2, List<&2, List<&2, U32>>>:
  match ok:
    case True{}:
      may
    case False{}:
      None{}

# the segments a request target names under the root: its bytes clean,
# split, normalised, and every segment a name by the rule above; None
# is a 404
def fnames.of(+dot: Bool, +t: List<&2, U32>) -> Maybe<&2, List<&2, List<&2, U32>>>:
  fnames.gate(clean(t), fnames.guard(dot, norm(segs(t))))

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

# One piece of a reply: bytes as they are, or a file to write when the
# reply is written: the root, the path under it, the type, and whether
# only the head is wanted. Fixed routes stay pure; only a file route
# puts IO on the path, and only for its own request.
type Seg is Data:
  Raw{bs: Bytes()}
  Page{root: List<&2, U32>, path: List<&2, U32>, ct: List<&2, U32>, head: Bool}
  Note{bs: Bytes()}
  Shut{}

def miss(head: Bool) -> Bytes():
  match head:
    case True{}:
      head.of(resp.missing())
    case False{}:
      resp.missing()

def page.name(root: List<&2, U32>, +ss: List<&2, List<&2, U32>>, head: Bool) -> Seg:
  Page{root, join(ss), ctype(ext.go(last(ss, Nil{}), Nil{})), head}

def page.of(root: List<&2, U32>, ss: List<&2, List<&2, U32>>, head: Bool) -> Seg:
  match ss:
    case Nil{}:
      Page{root, bytes("index.html"), bytes("text/html; charset=utf-8"), head}
    case Con{s, t}:
      page.name(root, Con{s, t}, head)

def page.pick(root: List<&2, U32>, may: Maybe<&2, List<&2, List<&2, U32>>>, head: Bool) -> Seg:
  match may:
    case None{}:
      Raw{miss(head)}
    case Some{ss}:
      page.of(root, ss, head)

# a file under the root, named by the request path (fnames.of): split,
# normalised, gated to printable ASCII, dotfiles refused. Percent
# escapes are not decoded, so an escaped ".." is a name no file has
# rather than a climb. The name is opened by File.open_under, which
# follows no symbolic link and opens nothing but a regular file.
def page(root: List<&2, U32>, +path: List<&2, U32>, head: Bool) -> Seg:
  page.pick(root, fnames.of(False{}, path), head)

# The access log: one line per request, what was asked, the status it
# got and how many bytes went back, on stderr and nowhere else, so
# whatever supervises the process is what timestamps and collects it.
# A Note carries what is known before the reply exists; the segment
# after it completes the line. --log turns it on, and it is off by
# default because a line per request is a syscall per request. The
# status is the three bytes after "HTTP/1.1 ", a view of the reply.
def log.line(note: Bytes(), +out: Bytes()) -> String:
  note ++ " " ++ Bytes.slice(out, 9n, 3n) ++ " " ++ Nat.show(Bytes.len(out))

# a reply that ends its connection says so: a Shut before it marks it
def flat.shut(sh: Bool, +bs: Bytes()) -> Bytes():
  match sh:
    case True{}:
      closing(bs)
    case False{}:
      bs

# The world the connection runs in
# ================================
#
# Everything below that touches a socket or a file is written once, over
# an effect interface, and instantiated twice: with the real effects
# (IO, Socket, File, TCP.poll_buf ...) to serve, and with the pure model
# of world.bend (the identity monad, a scripted peer for the socket, a
# list of files) to prove what the loop does to every peer. The
# interface is a set of template parameters, so the real instance is the
# code it was before, compiled on its own and called directly: nothing
# is passed at runtime and nothing is looked up.
#
#   ~M, ~pure, ~bind   the monad: IO, or Id in the model
#   ~S, ~F             the socket and the file handle
#   ~rx                read: TCP.poll_buf(s, max, ms)
#   ~tx                write: TCP.send_buf_poll(s, bytes, ms)
#   ~clk               the clock, in ms, beside the socket (IO.now)
#   ~nap               sleep, beside the socket (IO.sleep)
#   ~say               a log line (IO.print_err)
#   ~fopen             File.open_under, beside the socket
#   ~fsize ~fread ~fclose   File.size, File.read_buf, File.close
#
# Each effect's contract -- what the model assumes of it and what
# conform.c checks the real one does -- is written beside it in
# bend2/base.bend and, as a relation, in world.bend.

# what a timed read answers, and what a send answers, beside the socket
law Got:
  for -S: Type
  Type

def Got(S):
  S & Result<&1, &1, U32 & String, Maybe<&1, Bytes()>>

law Put:
  for -S: Type
  Type

def Put(S):
  S & Result<&1, &1, U32 & String, Unit>

# a resolved segment, logged against the note that was waiting if there
# was one, and handed straight back: the line goes out before the
# segments after it, so the log reads in the order the requests came
def flat.note(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~say: String -> M(Unit),
  may: Maybe<&2, Bytes()>, +out: Bytes()
) -> M(Bytes()):
  match may:
    case None{}:
      pure(Bytes(), out)
    case Some{note}:
      bind(Unit, Bytes(), say(log.line(note, out)), u => pure(Bytes(), out))

# Writing a reply
# ===============
#
# The segments of one chunk's answers are written in order as they are
# produced. Fixed replies wait on one block and go out in one send with
# whatever comes next. A file goes out as its head, taken from fstat of
# the descriptor that was opened, then as blocks of at most page.chunk()
# bytes, each read only after the socket took the one before; so a file
# costs one block of memory however large it is, and a pipelined batch
# of files costs the same. The body is exactly the length its head
# promised: a read that comes back short is read on, and one that ends
# early (the file shrank) ends the connection, since nothing after it
# could be framed.

def page.chunk() -> U32:
  65536

# The batch budget. Fixed replies wait in one block, and once the block
# reaches send.cap() bytes it goes out before the next reply is taken:
# a pipelined read's replies come to what the peer sent and a head per
# request, and this bounds even that. Every send has the idle time as
# its deadline, so a peer that stops reading is let go rather than
# holding its slot.
def send.cap() -> U32:
  1048576

# what stays waiting after a reply brings the block to k bytes: all of
# it below the cap, none of it (it has gone out) at or past it
def batch.keep(c: Cmp, k: U32) -> U32:
  match c:
    case LT{}:
      k
    case EQ{}:
      0
    case GT{}:
      0

# the writer: the socket, the bytes waiting, and whether everything
# promised so far has gone out. Once it has not, nothing more is written.
type Em<-S: Type> is Type:
  Em{s: S, acc: Bytes(), ok: Bool}

# a file being written: its descriptor, the bytes still owed, the
# socket, and what waits to go out in front of the next block
type Pump<-S: Type, -F: Type> is Type:
  Going{f: F, left: U32, s: S, pre: Bytes()}
  Over{em: Em<S>}

def send.flushed(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type, m: Put(S)
) -> M(Em<S>):
  (s, r) = m
  match r:
    case Done{u}:
      pure(Em<S>, Em{s, "", True{}})
    case Fail{e}:
      pure(Em<S>, Em{s, "", False{}})

def send.held(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~tx: S -> Bytes() -> U32 -> M(Put(S)), +ms: U32, s: S, acc: Bytes(), c: Cmp
) -> M(Em<S>):
  match c:
    case LT{}:
      pure(Em<S>, Em{s, acc, True{}})
    case EQ{}:
      bind(Put(S), Em<S>, tx(s, acc, ms), m => send.flushed(~M, ~pure, ~bind, ~S, m))
    case GT{}:
      bind(Put(S), Em<S>, tx(s, acc, ms), m => send.flushed(~M, ~pure, ~bind, ~S, m))

# a reply joins the waiting block, and a block at the cap goes out
def send.hold(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~tx: S -> Bytes() -> U32 -> M(Put(S)), +ms: U32, s: S, +acc: Bytes()
) -> M(Em<S>):
  send.held(~M, ~pure, ~bind, ~S, ~tx, ms, s, acc, U32.cmp(U32.from_nat(Bytes.len(acc)),
      send.cap()))

# a file whose bytes are all out leaves what waits in front of the next
# block (its head, when it was empty) to the batch, under the batch's
# cap. As first written it was left waiting without the cap's test, so
# a pipelined read of empty files grew the batch by a head each.
def pump.left(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type, ~F: Type,
  ~tx: S -> Bytes() -> U32 -> M(Put(S)), ~fclose: F -> M(Unit), +ms: U32, f: F,
  left: U32, s: S, pre: Bytes(), done: Bool
) -> M(Pump<S, F>):
  match done:
    case True{}:
      bind(Unit, Pump<S, F>, fclose(f), u =>
        bind(Em<S>, Pump<S, F>, send.hold(~M, ~pure, ~bind, ~S, ~tx, ms, s, pre), em =>
          pure(Pump<S, F>, Over{em})))
    case False{}:
      pure(Pump<S, F>, Going{f, left, s, pre})

def pump.fail(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type, ~F: Type,
  ~fclose: F -> M(Unit), f: F, s: S, pre: Bytes()
) -> M(Pump<S, F>):
  bind(Unit, Pump<S, F>, fclose(f), u => pure(Pump<S, F>, Over{Em{s, pre, False{}}}))

def pump.sent(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type, ~F: Type,
  ~tx: S -> Bytes() -> U32 -> M(Put(S)), ~fclose: F -> M(Unit), +ms: U32, m: Put(S),
  f: F, +left: U32
) -> M(Pump<S, F>):
  (s, r) = m
  match r:
    case Fail{e}:
      pump.fail(~M, ~pure, ~bind, ~S, ~F, ~fclose, f, s, "")
    case Done{u}:
      pump.left(~M, ~pure, ~bind, ~S, ~F, ~tx, ~fclose, ms, f, left, s, "", U32.is_zero(left))

def pump.block(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type, ~F: Type,
  ~tx: S -> Bytes() -> U32 -> M(Put(S)), ~fclose: F -> M(Unit), +ms: U32, f: F,
  +left: U32, s: S, pre: Bytes(), bs: Bytes(), +n: U32, empty: Bool
) -> M(Pump<S, F>):
  match empty:
    case True{}:
      pump.fail(~M, ~pure, ~bind, ~S, ~F, ~fclose, f, s, pre)
    case False{}:
      bind(Put(S), Pump<S, F>, tx(s, Bytes.append(pre, bs), ms), m =>
        pump.sent(~M, ~pure, ~bind, ~S, ~F, ~tx, ~fclose, ms, m, f, (left - n : U32)))

def pump.got(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type, ~F: Type,
  ~tx: S -> Bytes() -> U32 -> M(Put(S)), ~fclose: F -> M(Unit), +ms: U32,
  got: F & Result<&1, &1, U32 & String, Bytes()>, left: U32, s: S, pre: Bytes()
) -> M(Pump<S, F>):
  (f, r) = got
  match r:
    case Fail{e}:
      pump.fail(~M, ~pure, ~bind, ~S, ~F, ~fclose, f, s, pre)
    case Done{+bs}:
      pump.block(~M, ~pure, ~bind, ~S, ~F, ~tx, ~fclose, ms, f, left, s, pre, bs,
        U32.from_nat(Bytes.len(bs)), U32.is_zero(U32.from_nat(Bytes.len(bs))))

def pump.out(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type, ~F: Type,
  ~fclose: F -> M(Unit), p: Pump<S, F>
) -> M(Em<S>):
  match p:
    case Over{em}:
      pure(Em<S>, em)
    case Going{f, left, s, pre}:
      bind(Unit, Em<S>, fclose(f), u => pure(Em<S>, Em{s, pre, False{}}))

# k bounds the reads: a block's worth each, and 64 short ones besides
def pump(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type, ~F: Type,
  ~tx: S -> Bytes() -> U32 -> M(Put(S)),
  ~fread: F -> U32 -> M(F & Result<&1, &1, U32 & String, Bytes()>),
  ~fclose: F -> M(Unit), k: Nat, +ms: U32, p: Pump<S, F>
) -> M(Em<S>):
  match k:
    case 0n:
      pump.out(~M, ~pure, ~bind, ~S, ~F, ~fclose, p)
    case 1n+j:
      match p:
        case Over{em}:
          pure(Em<S>, em)
        case Going{f, +left, s, pre}:
          bind(F & Result<&1, &1, U32 & String, Bytes()>, Em<S>,
            fread(f, U32.min(page.chunk(), left)), got =>
            bind(Pump<S, F>, Em<S>, pump.got(~M, ~pure, ~bind, ~S, ~F, ~tx, ~fclose, ms, got,
                left, s, pre),
              p2 => pump(~M, ~pure, ~bind, ~S, ~F, ~tx, ~fread, ~fclose, j, ms, p2)))

# a file's log line: its head's status, and the bytes its reply holds
def log.sized(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~say: String -> M(Unit),
  may: Maybe<&2, Bytes()>, +hd: Bytes(), n: U32
) -> M(Unit):
  match may:
    case None{}:
      pure(Unit, Unit{})
    case Some{note}:
      say(note ++ " " ++ Bytes.slice(hd, 9n, 3n) ++ " "
        ++ U32.show((U32.from_nat(Bytes.len(hd)) + n : U32)))

def page.miss(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~tx: S -> Bytes() -> U32 -> M(Put(S)), ~say: String -> M(Unit), +ms: U32, head: Bool,
  may: Maybe<&2, Bytes()>, sh: Bool, s: S, acc: Bytes()
) -> M(Em<S>):
  bind(Bytes(), Em<S>, flat.note(~M, ~pure, ~bind, ~say, may, flat.shut(sh, miss(head))), out =>
    send.hold(~M, ~pure, ~bind, ~S, ~tx, ms, s, Bytes.append(acc, out)))

def page.start(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type, ~F: Type,
  ~tx: S -> Bytes() -> U32 -> M(Put(S)), ~say: String -> M(Unit),
  ~fread: F -> U32 -> M(F & Result<&1, &1, U32 & String, Bytes()>),
  ~fclose: F -> M(Unit), +ms: U32, f: F, +n: U32, +hd: Bytes(), head: Bool,
  may: Maybe<&2, Bytes()>, s: S, acc: Bytes()
) -> M(Em<S>):
  match head:
    case True{}:
      bind(Unit, Em<S>, log.sized(~M, ~pure, ~bind, ~say, may, hd, 0), u =>
        bind(Unit, Em<S>, fclose(f), u2 =>
          send.hold(~M, ~pure, ~bind, ~S, ~tx, ms, s, Bytes.append(acc, hd))))
    case False{}:
      bind(Unit, Em<S>, log.sized(~M, ~pure, ~bind, ~say, may, hd, n), u =>
        bind(Pump<S, F>, Em<S>,
          pump.left(~M, ~pure, ~bind, ~S, ~F, ~tx, ~fclose, ms, f, n, s, Bytes.append(acc, hd),
              U32.is_zero(n)),
          p => pump(~M, ~pure, ~bind, ~S, ~F, ~tx, ~fread, ~fclose,
              U32.to_nat((n / page.chunk() + 64 : U32)), ms, p)))

def page.sized(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type, ~F: Type,
  ~tx: S -> Bytes() -> U32 -> M(Put(S)), ~say: String -> M(Unit),
  ~fread: F -> U32 -> M(F & Result<&1, &1, U32 & String, Bytes()>),
  ~fclose: F -> M(Unit), +ms: U32, got: F & Result<&1, &1, U32 & String, U32>,
  ct: List<&2, U32>, head: Bool, may: Maybe<&2, Bytes()>, sh: Bool, s: S, acc: Bytes()
) -> M(Em<S>):
  (f, r) = got
  match r:
    case Fail{e}:
      bind(Unit, Em<S>, fclose(f), u =>
        page.miss(~M, ~pure, ~bind, ~S, ~tx, ~say, ms, head, may, sh, s, acc))
    case Done{+n}:
      page.start(~M, ~pure, ~bind, ~S, ~F, ~tx, ~say, ~fread, ~fclose, ms, f, n,
        flat.shut(sh, reply.n.head("200 OK", ct, n)), head, may, s, acc)

def page.opened(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type, ~F: Type,
  ~tx: S -> Bytes() -> U32 -> M(Put(S)), ~say: String -> M(Unit),
  ~fsize: F -> M(F & Result<&1, &1, U32 & String, U32>),
  ~fread: F -> U32 -> M(F & Result<&1, &1, U32 & String, Bytes()>),
  ~fclose: F -> M(Unit), +ms: U32, m: S & Result<&1, &1, U32 & String, F>,
  ct: List<&2, U32>, head: Bool, may: Maybe<&2, Bytes()>, sh: Bool, acc: Bytes()
) -> M(Em<S>):
  (s, r) = m
  match r:
    case Fail{e}:
      page.miss(~M, ~pure, ~bind, ~S, ~tx, ~say, ms, head, may, sh, s, acc)
    case Done{f}:
      bind(F & Result<&1, &1, U32 & String, U32>, Em<S>, fsize(f), got =>
        page.sized(~M, ~pure, ~bind, ~S, ~F, ~tx, ~say, ~fread, ~fclose, ms, got, ct, head,
            may, sh, s, acc))

def send.page(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type, ~F: Type,
  ~tx: S -> Bytes() -> U32 -> M(Put(S)), ~say: String -> M(Unit),
  ~fopen: S -> String -> String -> M(S & Result<&1, &1, U32 & String, F>),
  ~fsize: F -> M(F & Result<&1, &1, U32 & String, U32>),
  ~fread: F -> U32 -> M(F & Result<&1, &1, U32 & String, Bytes()>),
  ~fclose: F -> M(Unit), +ms: U32, root: List<&2, U32>, path: List<&2, U32>,
  ct: List<&2, U32>, head: Bool, may: Maybe<&2, Bytes()>, sh: Bool, st: Em<S>
) -> M(Em<S>):
  match st:
    case Em{s, acc, ok}:
      match ok:
        case False{}:
          pure(Em<S>, Em{s, acc, False{}})
        case True{}:
          bind(S & Result<&1, &1, U32 & String, F>, Em<S>, fopen(s, text(root), text(path)), m =>
            page.opened(~M, ~pure, ~bind, ~S, ~F, ~tx, ~say, ~fsize, ~fread, ~fclose, ms, m,
                ct, head, may, sh, acc))

def send.raw(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~tx: S -> Bytes() -> U32 -> M(Put(S)), ~say: String -> M(Unit), +ms: U32,
  may: Maybe<&2, Bytes()>, bs: Bytes(), st: Em<S>
) -> M(Em<S>):
  match st:
    case Em{s, acc, ok}:
      match ok:
        case False{}:
          pure(Em<S>, Em{s, acc, False{}})
        case True{}:
          bind(Bytes(), Em<S>, flat.note(~M, ~pure, ~bind, ~say, may, bs), out =>
            send.hold(~M, ~pure, ~bind, ~S, ~tx, ms, s, Bytes.append(acc, out)))

def send.fin(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type, m: Put(S),
  ok: Bool
) -> M(Put(S)):
  (s, r) = m
  match ok:
    case True{}:
      pure(Put(S), (s, r))
    case False{}:
      pure(Put(S), (s, Fail{(5, "a file ended before the length its head promised")}))

def send.end(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~tx: S -> Bytes() -> U32 -> M(Put(S)), +ms: U32, st: Em<S>
) -> M(Put(S)):
  match st:
    case Em{s, acc, ok}:
      bind(Put(S), Put(S), tx(s, acc, ms), m => send.fin(~M, ~pure, ~bind, ~S, m, ok))

# a Shut before a reply marks the one that ends its connection
def send.go(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type, ~F: Type,
  ~tx: S -> Bytes() -> U32 -> M(Put(S)), ~say: String -> M(Unit),
  ~fopen: S -> String -> String -> M(S & Result<&1, &1, U32 & String, F>),
  ~fsize: F -> M(F & Result<&1, &1, U32 & String, U32>),
  ~fread: F -> U32 -> M(F & Result<&1, &1, U32 & String, Bytes()>),
  ~fclose: F -> M(Unit), xs: List<&2, Seg>, +ms: U32, may: Maybe<&2, Bytes()>, sh: Bool,
  st: Em<S>
) -> M(Put(S)):
  match xs:
    case Nil{}:
      send.end(~M, ~pure, ~bind, ~S, ~tx, ms, st)
    case Con{g, t}:
      match g:
        case Note{bs}:
          send.go(~M, ~pure, ~bind, ~S, ~F, ~tx, ~say, ~fopen, ~fsize, ~fread, ~fclose, t, ms,
              Some{bs}, sh, st)
        case Shut{}:
          send.go(~M, ~pure, ~bind, ~S, ~F, ~tx, ~say, ~fopen, ~fsize, ~fread, ~fclose, t, ms,
              may, True{}, st)
        case Raw{bs}:
          bind(Em<S>, Put(S), send.raw(~M, ~pure, ~bind, ~S, ~tx, ~say, ms, may, flat.shut(sh,
              bs), st), st2 =>
            send.go(~M, ~pure, ~bind, ~S, ~F, ~tx, ~say, ~fopen, ~fsize, ~fread, ~fclose, t,
                ms, None{}, False{}, st2))
        case Page{root, path, ct, head}:
          bind(Em<S>, Put(S),
            send.page(~M, ~pure, ~bind, ~S, ~F, ~tx, ~say, ~fopen, ~fsize, ~fread, ~fclose, ms,
                root, path, ct, head, may, sh, st), st2 =>
            send.go(~M, ~pure, ~bind, ~S, ~F, ~tx, ~say, ~fopen, ~fsize, ~fread, ~fclose, t,
                ms, None{}, False{}, st2))

# The one hook the connection loop calls: write a plan's segments to the
# socket, in order, streaming files, each send within ms of progress;
# the result fails when the socket failed, stalled, or a file came up
# short, and the connection then ends.
def send.segs(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type, ~F: Type,
  ~tx: S -> Bytes() -> U32 -> M(Put(S)), ~say: String -> M(Unit),
  ~fopen: S -> String -> String -> M(S & Result<&1, &1, U32 & String, F>),
  ~fsize: F -> M(F & Result<&1, &1, U32 & String, U32>),
  ~fread: F -> U32 -> M(F & Result<&1, &1, U32 & String, Bytes()>),
  ~fclose: F -> M(Unit), s: S, xs: List<&2, Seg>, +ms: U32
) -> M(Put(S)):
  send.go(~M, ~pure, ~bind, ~S, ~F, ~tx, ~say, ~fopen, ~fsize, ~fread, ~fclose, xs, ms, None{},
      False{}, Em{s, "", True{}})


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
# A key is sixteen random bytes in base64: 22 characters of the
# alphabet and "==", 24 in all (RFC 6455 4.1). Anything else is refused
# before it is hashed, so a key is never a way to make the engine spend.
def key.b64(+c: U32) -> Bool:
  (U32.is_le(65, c) && U32.is_le(c, 90)) || (U32.is_le(97, c) && U32.is_le(c, 122))
    || (U32.is_le(48, c) && U32.is_le(c, 57)) || U32.is_eq(c, 43) || U32.is_eq(c, 47)

def key.at(+i: U32, +c: U32) -> Bool:
  (U32.is_lt(i, 22) && key.b64(c)) || (U32.is_le(22, i) && U32.is_eq(c, 61))

def key.ok(bs: List<&2, U32>, +i: U32, ok: Bool) -> Bool:
  match bs:
    case Nil{}:
      ok && U32.is_eq(i, 24)
    case Con{+c, t}:
      key.ok(t, (i + 1 : U32), ok && key.at(i, c))

# the 426 names the version it would have spoken
def reply.v13(status: Bytes(), ct: Bytes(), +body: Bytes()) -> Bytes():
  Bytes.concat(["HTTP/1.1 ", status, "\r\ncontent-type: ", ct,
    "\r\ncontent-length: ", Nat.show(Bytes.len(body)),
    "\r\nsec-websocket-version: 13\r\nconnection: keep-alive\r\n\r\n", body])

def live.keyed(key: List<&2, U32>, ok: Bool) -> Ans:
  match ok:
    case True{}:
      Ans{[Raw{live.head(key)}], False{}, 0, True{}}
    case False{}:
      Ans{[Raw{resp.bad()}], True{}, 0, False{}}

# the key is checked and hashed as the byte list sha1.bend reads; it is
# at most one read of a head, and only an upgrade pays for it
def live.list(+key: List<&2, U32>) -> Ans:
  live.keyed(key, key.ok(key, 0, True{}))

def live.answer(key: Bytes(), ws: Bool, head: Bool) -> Ans:
  match ws:
    case True{}:
      live.list(Bytes.to_list(key))
    case False{}:
      Ans{[Raw{fixed(reply.v13("426 Upgrade Required", "text/plain", "websocket only\n"), head)}],
        False{}, 0, False{}}

# /events: the stream's head, then the events; a HEAD gets the head
# and no stream, since a HEAD reply carries no body
def events(head: Bool) -> Ans:
  match head:
    case True{}:
      Ans{[Raw{sse.head()}], False{}, 0, False{}}
    case False{}:
      Ans{[Raw{sse.head()}], False{}, sse.count(), False{}}

# the echo's body goes back as it arrived: within one read it is a view
# of that read, and the reply is the only copy made of it. A file's path
# is walked as the byte list the normaliser and its laws speak of.
def act.run(
  +srv: Srv, a: Act, path: Bytes(), body: Bytes(), head: Bool, ws: Bool, key: Bytes()
) -> Ans:
  match a:
    case Health{}:
      Ans{[Raw{fixed(resp.health(), head)}], False{}, 0, False{}}
    case Root{}:
      Ans{[Raw{fixed(resp.root(), head)}], False{}, 0, False{}}
    case Echo{}:
      Ans{[Raw{fixed(reply("200 OK", "application/octet-stream", body), head)}],
        False{}, 0, False{}}
    case Events{}:
      events(head)
    case Live{}:
      live.answer(key, ws, head)
    case Files{}:
      Ans{[page(srv.root(srv), Bytes.to_list(path), head)], False{}, 0, False{}}

def serve.act(
  +srv: Srv, found: Maybe<&2, Act>, path: Bytes(), body: Bytes(), head: Bool, ws: Bool,
  key: Bytes()
) -> Ans:
  match found:
    case None{}:
      Ans{[Raw{miss(head)}], False{}, 0, False{}}
    case Some{a}:
      act.run(srv, a, path, body, head, ws, key)

# the longest request target served; a longer one is a 414. The head's
# own budget bounds what a target can cost before it gets here.
def target.cap() -> Nat:
  8192n

# whether bs has more than k bytes
def long(k: Nat, bs: Bytes()) -> Bool:
  Nat.is_lt(k, Bytes.len(bs))

def resp.long() -> Bytes():
  reply("414 URI Too Long", "text/plain", "target too long\n")

# A method this engine does not implement is refused before routing, so
# no route ever sees one.
def serve.go(
  +srv: Srv, +path: Bytes(), body: Bytes(), ok: Bool, head: Bool, ws: Bool, key: Bytes()
) -> Ans:
  match ok:
    case True{}:
      serve.act(srv, route(srv.table(srv), path), path, body, head, ws, key)
    case False{}:
      Ans{[Raw{resp.method()}], False{}, 0, False{}}

# what a log line says was asked: the two methods this engine serves
# are named, and anything else is "?", so a log line never carries a
# method's bytes
def shown(m: Meth) -> Bytes():
  match m:
    case MGet{}:
      "GET"
    case MHead{}:
      "HEAD"
    case MOther{}:
      "?"

def noted.on(note: Bytes(), a: Ans) -> Ans:
  match a:
    case Ans{out, cl, st, sk}:
      Ans{Con{Note{note}, out}, cl, st, sk}

# the note is only built when the log is on
def noted(on: Bool, m: Meth, path: Bytes(), a: Ans) -> Ans:
  match on:
    case False{}:
      a
    case True{}:
      noted.on(Bytes.concat([shown(m), " ", path]), a)

def path.cut(+p: Bytes(), q: Maybe<&2, Nat>) -> Bytes():
  match q:
    case None{}:
      p
    case Some{i}:
      Bytes.slice(p, 0n, i)

# the path a target names is its bytes before any '?': the query says
# nothing about which resource is asked for, so /health?x=1 is /health.
# It is a view of the target.
def path.of(+p: Bytes()) -> Bytes():
  path.cut(p, Bytes.find(p, "?"))

def serve.fit(
  +srv: Srv, +path: Bytes(), body: Bytes(), ok: Bool, head: Bool, ws: Bool, key: Bytes(),
  far: Bool
) -> Ans:
  match far:
    case True{}:
      Ans{[Raw{fixed(resp.long(), head)}], False{}, 0, False{}}
    case False{}:
      serve.go(srv, path, body, ok, head, ws, key)

def serve.log(+srv: Srv, r: Req) -> Ans:
  match r:
    case Req{+meth, +path, body, close, ws, key}:
      noted(srv.log(srv), meth, path,
        serve.fit(srv, path.of(path), body, meth.get(meth) || meth.head(meth),
          meth.head(meth), ws, key, long(target.cap(), path)))

def serve(+srv: Srv, r: Req) -> Ans:
  serve.log(srv, r)

def ans.out(a: Ans) -> List<&2, Seg>:
  match a:
    case Ans{out, cl, st, sk}:
      out

def ans.close(a: Ans) -> Bool:
  match a:
    case Ans{out, cl, st, sk}:
      cl

def ans.stream(a: Ans) -> U32:
  match a:
    case Ans{out, cl, st, sk}:
      st

def ans.sock(a: Ans) -> Bool:
  match a:
    case Ans{out, cl, st, sk}:
      sk

# the replies so far, newest first, joined oldest first: each is
# copied once, so a pipelined batch costs what its replies do
def answer.flat(acc: List<&2, List<&2, Seg>>, tail: List<&2, Seg>) -> List<&2, Seg>:
  match acc:
    case Nil{}:
      tail
    case Con{a, t}:
      answer.flat(t, List.append(&2, Seg, a, tail))

# the reply to a request that ends the connection says so
def answer.shut(out: List<&2, Seg>, last: Bool) -> List<&2, Seg>:
  match last:
    case True{}:
      Con{Shut{}, out}
    case False{}:
      out

# the end of a chunk's requests: a grammar that broke after them is
# answered with a 400 after their replies, and the connection ends
def answer.end(acc: List<&2, List<&2, Seg>>, bad: Bool) -> Ans:
  match bad:
    case True{}:
      Ans{answer.flat(acc, [Raw{resp.bad()}]), True{}, 0, False{}}
    case False{}:
      Ans{answer.flat(acc, Nil{}), False{}, 0, False{}}

# Every reply for one chunk's worth of messages, in arrival order. A
# reply that ends what this connection reads -- one that closes, one
# that starts a stream, one that switches to frames -- is the last: the
# requests after it are not served, and a broken grammar after it is
# not answered. go is whether the replies so far have ended nothing.
# A request that asked to upgrade and was not switched ends the
# connection, since what followed it was never read as requests.
def answer.go(
  +srv: Srv, rs: List<&2, Req>, bad: Bool, go: Bool, cl: Bool, st: U32, sk: Bool,
  acc: List<&2, List<&2, Seg>>
) -> Ans:
  match rs go:
    case _ False{}:
      Ans{answer.flat(acc, Nil{}), cl, st, sk}
    case Nil{} True{}:
      answer.end(acc, bad)
    case Con{+r, t} True{}:
      +a = serve(srv, r)
      +k = ans.sock(a)
      +s = ans.stream(a)
      +c = ans.close(a) || req.close(r) || (req.ws(r) && Bool.not(k))
      answer.go(srv, t, bad, Bool.not(c || k || Bool.not(U32.is_zero(s))), c, s, k,
        Con{answer.shut(ans.out(a), c && U32.is_zero(s) && Bool.not(k)), acc})

def answer(+srv: Srv, rs: List<&2, Req>, bad: Bool) -> Ans:
  answer.go(srv, rs, bad, True{}, False{}, 0, False{}, Nil{})

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

# After a 101 the bytes that followed the upgrade in the same read are
# frames, and go to the frame reader rather than being dropped; the
# replies they earned go out with the 101.
def plan.up.rep(out: List<&2, Seg>, wr: Ws.W, r: Ws.Rep) -> Plan:
  match r:
    case Ws.Rep{o, close}:
      match close:
        case True{}:
          End{List.append(&2, Seg, out, [Raw{o}])}
        case False{}:
          Sock{List.append(&2, Seg, out, [Raw{o}]), wr}

def plan.up.dead(out: List<&2, Seg>, fs: List<&2, Ws.Frm>, dd: Ws.W & Bool) -> Plan:
  (wr, bad) = dd
  plan.up.rep(out, wr, Ws.reply(fs, bad))

def plan.up.take(out: List<&2, Seg>, tk: Ws.W & List<&2, Ws.Frm>) -> Plan:
  (wr, fs) = tk
  plan.up.dead(out, fs, Ws.dead(wr))

def plan.up(out: List<&2, Seg>, rest: Bytes()) -> Plan:
  plan.up.take(out, Ws.take(Ws.feed_buf(rest, Ws.new())))

def plan.pick(
  out: List<&2, Seg>, p2: P, plain: Bool, cl: Bool, st: U32, sock: Bool
) -> Plan:
  match plain cl sock:
    case _ _ True{}:
      plan.up(out, p.rest(p2))
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

# a grammar that broke is answered with a 400, after the replies owed
# to the requests the same read completed before it
def plan.take(+srv: Srv, pr: P & List<&2, Req>, bad: Bool) -> Plan:
  (p2, rs) = pr
  plan.ans(answer(srv, rs, bad), p2)

def plan.go(+srv: Srv, q: P, bad: Bool) -> Plan:
  plan.take(srv, p.take(q), bad)

def plan.on(+srv: Srv, pb: P & Bool) -> Plan:
  (q, bad) = pb
  plan.go(srv, q, bad)

# the plan after one chunk: parse it, then decide
# An empty chunk is the peer's FIN: nothing more will ever arrive, so
# the connection ends here rather than reading again. As first written
# the engine read again, and one peer that connected and closed without
# a byte cost most of a core in passes until the fuel ran out.
def plan.chunk(+srv: Srv, buf: Bytes(), p: P) -> Plan:
  match buf:
    case SNil{}:
      Stop{}
    case SCon{b, bs}:
      plan.on(srv, p.dead(feed_buf(SCon{b, bs}, p)))

# what a timed read gave: bytes to parse, the peer's silence past the
# idle time (the connection ends), or a failure (it ends)
def plan.may(
  -S: Type, +srv: Srv, s: S, may: Maybe<&1, Bytes()>, p: P
) -> S & Plan:
  match may:
    case None{}:
      (s, Stop{})
    case Some{buf}:
      (s, plan.chunk(srv, buf, p))

def plan.polled(
  -S: Type, +srv: Srv, s: S, r: Result<&1, &1, U32 & String, Maybe<&1, Bytes()>>,
  p: P
) -> S & Plan:
  match r:
    case Done{may}:
      plan.may(S, srv, s, may, p)
    case Fail{e}:
      (s, Stop{})

# the socket and the plan, out of one timed read
def plan.poll(-S: Type, +srv: Srv, m: Got(S), p: P) -> S & Plan:
  (s, r) = m
  plan.polled(S, srv, s, r, p)

def chunk() -> U32:
  16384

# The head being read, for its budget. NoHead{} is no head in progress
# (or a body, which the idle time alone bounds); Begun{} is a head the
# last read began, whose clock starts now; Since{t0, n} is one that began
# at t0 (the clock, ms) and has had n bytes since the read it began in.
type Hw is Data:
  NoHead{}
  Begun{}
  Since{t0: Nat, n: U32}

# read the next chunk, within the idle time, and plan from it. Splitting
# the send's socket out here is what lets the connection loop below be
# one self-recursive def.
def turn.s(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~rx: S -> U32 -> U32 -> M(Got(S)), +srv: Srv, s: S, p: P
) -> M((S & Plan) & Hw):
  bind(Got(S), (S & Plan) & Hw, rx(s, chunk(), srv.idle(srv)), m =>
    pure((S & Plan) & Hw, (plan.poll(S, srv, m, p), NoHead{})))

# the watch after a read that finished no message: a head still in
# progress keeps its clock, one just begun gets one
def hw.next(mid: Bool, hw: Hw) -> Hw:
  match mid:
    case False{}:
      NoHead{}
    case True{}:
      match hw:
        case NoHead{}:
          Begun{}
        case Begun{}:
          Begun{}
        case Since{t0, n}:
          Since{t0, n}

# the most bytes a head may take after the read it began in. A read is
# at most chunk() bytes, so every head under 16 KiB is read whole and
# none past 32 KiB ever is; past it, the answer is a 431 and a close.
def head.cap() -> U32:
  16384

def resp.big() -> Bytes():
  reply("431 Request Header Fields Too Large", "text/plain", "head too large\n")

def plan.sized(
  -S: Type, +srv: Srv, s: S, buf: Bytes(), p: P, t0: Nat, n: U32, big: Bool
) -> (S & Plan) & Hw:
  match big:
    case True{}:
      ((s, End{[Shut{}, Raw{resp.big()}]}), NoHead{})
    case False{}:
      ((s, plan.chunk(srv, buf, p)), Since{t0, n})

def plan.counted(
  -S: Type, +srv: Srv, s: S, may: Maybe<&1, Bytes()>, p: P, t0: Nat, n: U32
) -> (S & Plan) & Hw:
  match may:
    case None{}:
      ((s, Stop{}), NoHead{})
    case Some{+buf}:
      +k = (n + U32.from_nat(Bytes.len(buf)) : U32)
      plan.sized(S, srv, s, buf, p, t0, k, U32.is_lt(head.cap(), k))

def plan.headed(-S: Type, +srv: Srv, m: Got(S), p: P, t0: Nat, n: U32) -> (S & Plan) & Hw:
  (s, r) = m
  match r:
    case Done{may}:
      plan.counted(S, srv, s, may, p, t0, n)
    case Fail{e}:
      ((s, Stop{}), NoHead{})

# a read that continues a head waits for the idle time or for what is
# left of the head's time, whichever is less; a head out of time is
# dropped, as a silent peer is
def turn.left(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~rx: S -> U32 -> U32 -> M(Got(S)), +srv: Srv, s: S, p: P, t0: Nat, n: U32, +el: Nat,
  ok: Bool
) -> M((S & Plan) & Hw):
  match ok:
    case False{}:
      pure((S & Plan) & Hw, ((s, Stop{}), NoHead{}))
    case True{}:
      bind(Got(S), (S & Plan) & Hw,
        rx(s, chunk(),
          U32.min(srv.idle(srv), U32.from_nat(Nat.sub(U32.to_nat(srv.head(srv)), el)))),
        m => pure((S & Plan) & Hw, plan.headed(S, srv, m, p, t0, n)))

def turn.at(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~rx: S -> U32 -> U32 -> M(Got(S)), +srv: Srv, s: S, p: P, +t0: Nat, n: U32, now: Nat
) -> M((S & Plan) & Hw):
  +el = Nat.sub(now, t0)
  turn.left(~M, ~pure, ~bind, ~S, ~rx, srv, s, p, t0, n, el, Nat.is_lt(el,
      U32.to_nat(srv.head(srv))))

# the clock read at a head's first read starts its time
def turn.fresh.at(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~rx: S -> U32 -> U32 -> M(Got(S)), +srv: Srv, s: S, p: P, +now: Nat
) -> M((S & Plan) & Hw):
  turn.at(~M, ~pure, ~bind, ~S, ~rx, srv, s, p, now, 0, now)

def turn.fresh(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~rx: S -> U32 -> U32 -> M(Got(S)), +srv: Srv, sn: S & Nat, p: P
) -> M((S & Plan) & Hw):
  (s, now) = sn
  turn.fresh.at(~M, ~pure, ~bind, ~S, ~rx, srv, s, p, now)

def turn.since(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~rx: S -> U32 -> U32 -> M(Got(S)), +srv: Srv, sn: S & Nat, p: P, t0: Nat, n: U32
) -> M((S & Plan) & Hw):
  (s, now) = sn
  turn.at(~M, ~pure, ~bind, ~S, ~rx, srv, s, p, t0, n, now)

# read the next chunk for the request reader, under the head's budget
# when a head is in progress
def turn.h(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~rx: S -> U32 -> U32 -> M(Got(S)), ~clk: S -> M(S & Nat), +srv: Srv, s: S, p: P, hw: Hw
) -> M((S & Plan) & Hw):
  match hw:
    case NoHead{}:
      turn.s(~M, ~pure, ~bind, ~S, ~rx, srv, s, p)
    case Begun{}:
      bind(S & Nat, (S & Plan) & Hw, clk(s), sn => turn.fresh(~M, ~pure, ~bind, ~S, ~rx, srv,
          sn, p))
    case Since{t0, n}:
      bind(S & Nat, (S & Plan) & Hw, clk(s), sn => turn.since(~M, ~pure, ~bind, ~S, ~rx, srv,
          sn, p, t0, n))

def turn(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~rx: S -> U32 -> U32 -> M(Got(S)), ~clk: S -> M(S & Nat), +srv: Srv, sent: Put(S),
  p: P, hw: Hw
) -> M((S & Plan) & Hw):
  (s, r) = sent
  match r:
    case Fail{e}:
      pure((S & Plan) & Hw, ((s, Stop{}), NoHead{}))
    case Done{u}:
      turn.h(~M, ~pure, ~bind, ~S, ~rx, ~clk, srv, s, p, hw)

# A WebSocket connection: what the frames one read completed earned --
# bytes to write and read on, nothing yet (read on), or the close.
def plan.rep(-S: Type, s: S, wr: Ws.W, r: Ws.Rep) -> S & Plan:
  match r:
    case Ws.Rep{out, close}:
      match out:
        case SNil{}:
          match close:
            case True{}:
              (s, End{Nil{}})
            case False{}:
              (s, Hold{wr})
        case SCon{h, t}:
          match close:
            case True{}:
              (s, End{[Raw{SCon{h, t}}]})
            case False{}:
              (s, Sock{[Raw{SCon{h, t}}], wr})

def plan.framed(-S: Type, s: S, fs: List<&2, Ws.Frm>, dd: Ws.W & Bool) -> S & Plan:
  (wr, bad) = dd
  plan.rep(S, s, wr, Ws.reply(fs, bad))

def plan.frames(-S: Type, s: S, tk: Ws.W & List<&2, Ws.Frm>) -> S & Plan:
  (wr, fs) = tk
  plan.framed(S, s, fs, Ws.dead(wr))

def plan.wsm(-S: Type, s: S, may: Maybe<&1, Bytes()>, wr: Ws.W) -> S & Plan:
  match may:
    case None{}:
      (s, Stop{})
    case Some{bs}:
      match bs:
        case SNil{}:
          (s, Stop{})
        case SCon{b, t}:
          plan.frames(S, s, Ws.take(Ws.feed_buf(SCon{b, t}, wr)))

def plan.wsr(
  -S: Type, s: S, r: Result<&1, &1, U32 & String, Maybe<&1, Bytes()>>, wr: Ws.W
) -> S & Plan:
  match r:
    case Done{may}:
      plan.wsm(S, s, may, wr)
    case Fail{e}:
      (s, Stop{})

def plan.ws(-S: Type, m: Got(S), wr: Ws.W) -> S & Plan:
  (s, r) = m
  plan.wsr(S, s, r, wr)

def turn.wr(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~rx: S -> U32 -> U32 -> M(Got(S)), +srv: Srv, s: S, wr: Ws.W
) -> M(S & Plan):
  bind(Got(S), S & Plan, rx(s, chunk(), srv.idle(srv)), m => pure(S & Plan, plan.ws(S, m, wr)))

# after the frames' replies: a send that failed or stalled ends the
# connection, as it does for requests. As first written this read on
# whatever the send said, so a peer that sent pings and never read
# held its connection for as many sends as the fuel allowed, each one
# waiting out the idle time.
def turn.ws(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~rx: S -> U32 -> U32 -> M(Got(S)), +srv: Srv, sent: Put(S), wr: Ws.W
) -> M(S & Plan):
  (s, r) = sent
  match r:
    case Fail{e}:
      pure(S & Plan, (s, Stop{}))
    case Done{u}:
      turn.wr(~M, ~pure, ~bind, ~S, ~rx, srv, s, wr)

# the next event, or the end of the stream. A stream terminates because
# the count runs out, the same way a connection does: no @unsafe, and a
# peer that goes quiet still cannot hold a computation open forever.
def plan.more(-S: Type, s: S, +n: U32, done: Bool) -> S & Plan:
  match done:
    case True{}:
      (s, Stop{})
    case False{}:
      (s, Feed{[Raw{sse.event(n)}], (n - 1 : U32)})

def plan.next(
  -S: Type, s: S, r: Result<&1, &1, U32 & String, Unit>, +n: U32
) -> S & Plan:
  match r:
    case Done{u}:
      plan.more(S, s, n, U32.is_zero(n))
    case Fail{e}:
      (s, Stop{})

# wait, then plan the next event. The engine writes on its own clock and
# reads nothing, so the reader and the writer never contend for the one
# socket the connection owns.
def tick(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~nap: S -> U32 -> M(S), sent: Put(S), n: U32
) -> M(S & Plan):
  (s, r) = sent
  bind(S, S & Plan, nap(s, sse.gap()), s2 => pure(S & Plan, plan.next(S, s2, r, n)))

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

# The socket, out of what its last send answered.
def put.s(-S: Type, m: Put(S)) -> S:
  (s, r) = m
  s

# The loop answers the socket when the connection is over; the caller
# closes it. The watch rides beside the plan: a read that finishes no
# message keeps the head's clock and count, and one that finishes one
# starts them over for whatever head it left begun.
def conn(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type, ~F: Type,
  ~rx: S -> U32 -> U32 -> M(Got(S)), ~tx: S -> Bytes() -> U32 -> M(Put(S)),
  ~clk: S -> M(S & Nat), ~nap: S -> U32 -> M(S), ~say: String -> M(Unit),
  ~fopen: S -> String -> String -> M(S & Result<&1, &1, U32 & String, F>),
  ~fsize: F -> M(F & Result<&1, &1, U32 & String, U32>),
  ~fread: F -> U32 -> M(F & Result<&1, &1, U32 & String, Bytes()>),
  ~fclose: F -> M(Unit), f: Nat, +srv: Srv, sph: (S & Plan) & Hw, w: Nat
) -> M(S):
  match f:
    case 0n:
      ((s, pl), hw) = sph
      pure(S, s)
    case 1n+g:
      ((s, pl), hw) = sph
      match pl:
        case Stop{}:
          pure(S, s)
        case End{out}:
          bind(Put(S), S, send.segs(~M, ~pure, ~bind, ~S, ~F, ~tx, ~say, ~fopen, ~fsize,
              ~fread, ~fclose, s, out, srv.idle(srv)), m => pure(S, put.s(S, m)))
        case Wait{+p2}:
          match w:
            case 0n:
              pure(S, s)
            case 1n+v:
              bind((S & Plan) & Hw, S, turn.h(~M, ~pure, ~bind, ~S, ~rx, ~clk, srv, s, p2,
                  hw.next(p.head(p2), hw)),
                sp2 => conn(~M, ~pure, ~bind, ~S, ~F, ~rx, ~tx, ~clk, ~nap, ~say, ~fopen,
                    ~fsize, ~fread, ~fclose, g, srv, sp2, v))
        case Feed{out, n}:
          bind(Put(S), S, send.segs(~M, ~pure, ~bind, ~S, ~F, ~tx, ~say, ~fopen, ~fsize,
              ~fread, ~fclose, s, out, srv.idle(srv)), m =>
            bind(S & Plan, S, tick(~M, ~pure, ~bind, ~S, ~nap, m, n), sp2 =>
              conn(~M, ~pure, ~bind, ~S, ~F, ~rx, ~tx, ~clk, ~nap, ~say, ~fopen, ~fsize,
                  ~fread, ~fclose, g, srv, (sp2, NoHead{}), conn.waits())))
        case Sock{out, wr}:
          bind(Put(S), S, send.segs(~M, ~pure, ~bind, ~S, ~F, ~tx, ~say, ~fopen, ~fsize,
              ~fread, ~fclose, s, out, srv.idle(srv)), m =>
            bind(S & Plan, S, turn.ws(~M, ~pure, ~bind, ~S, ~rx, srv, m, wr), sp2 =>
              conn(~M, ~pure, ~bind, ~S, ~F, ~rx, ~tx, ~clk, ~nap, ~say, ~fopen, ~fsize,
                  ~fread, ~fclose, g, srv, (sp2, NoHead{}), conn.waits())))
        case Hold{wr}:
          match w:
            case 0n:
              pure(S, s)
            case 1n+v:
              bind(S & Plan, S, turn.wr(~M, ~pure, ~bind, ~S, ~rx, srv, s, wr), sp2 =>
                conn(~M, ~pure, ~bind, ~S, ~F, ~rx, ~tx, ~clk, ~nap, ~say, ~fopen, ~fsize,
                    ~fread, ~fclose, g, srv, (sp2, NoHead{}), v))
        case Go{out, +p2}:
          bind(Put(S), S, send.segs(~M, ~pure, ~bind, ~S, ~F, ~tx, ~say, ~fopen, ~fsize,
              ~fread, ~fclose, s, out, srv.idle(srv)), m =>
            bind((S & Plan) & Hw, S, turn(~M, ~pure, ~bind, ~S, ~rx, ~clk, srv, m, p2,
                hw.next(p.head(p2), NoHead{})),
              sp2 => conn(~M, ~pure, ~bind, ~S, ~F, ~rx, ~tx, ~clk, ~nap, ~say, ~fopen, ~fsize,
                  ~fread, ~fclose, g, srv, sp2, conn.waits())))

# A connection from its first read to the socket it leaves to be closed.
def conn.start(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type, ~F: Type,
  ~rx: S -> U32 -> U32 -> M(Got(S)), ~tx: S -> Bytes() -> U32 -> M(Put(S)),
  ~clk: S -> M(S & Nat), ~nap: S -> U32 -> M(S), ~say: String -> M(Unit),
  ~fopen: S -> String -> String -> M(S & Result<&1, &1, U32 & String, F>),
  ~fsize: F -> M(F & Result<&1, &1, U32 & String, U32>),
  ~fread: F -> U32 -> M(F & Result<&1, &1, U32 & String, Bytes()>),
  ~fclose: F -> M(Unit), +srv: Srv, s: S
) -> M(S):
  bind(Got(S), S, rx(s, chunk(), srv.idle(srv)), m =>
    conn(~M, ~pure, ~bind, ~S, ~F, ~rx, ~tx, ~clk, ~nap, ~say, ~fopen, ~fsize, ~fread, ~fclose,
        conn.fuel(), srv, (plan.poll(S, srv, m, p.new()), NoHead{}), conn.waits()))

# The accept loop
# ===============
#
# Written over its own interface, as the connection is: ~L the
# listener, ~C what it accepts, ~E what serving needs, ~lsn one timed
# accept (TCP.accept_poll), ~sig whether a stop was asked (SIGTERM),
# ~hand the hand-off of an accepted connection. A turn ends the loop
# only for a stop request or for a listener that is no longer one; an
# accept that failed for one connection, or for a passing shortage, is
# a turn like any other.

# why the loop ended: it spent its turns, a stop was asked, or the
# listener died with this code
type Why is Data:
  Spent{}
  Asked{}
  Dead{code: U32}

# The errors accept(2) answers for one connection or for the moment
# (tcp_accept_poll.c's passing set, and EAGAIN), by their numbers on
# Linux and on macOS. The effect answers them itself, so none should
# arrive here; if one does, it is one more turn and not the end.
def accept.soft.codes() -> List<&2, U32>:
  [1, 4, 11, 12, 23, 24, 35, 42, 45, 50, 51, 53, 55, 64, 65, 71, 92, 95, 100, 101,
   102, 103, 105, 112, 113]

def accept.soft.in(+code: U32, cs: List<&2, U32>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Con{+c, t}:
      U32.is_eq(code, c) || accept.soft.in(code, t)

def accept.soft(+code: U32) -> Bool:
  accept.soft.in(code, accept.soft.codes())

# after a turn: a stop request ends the loop, anything else goes on
def accept.asked(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~L: Type, lb: L & Bool
) -> M(L & Maybe<&2, Why>):
  (l, stop) = lb
  match stop:
    case True{}:
      pure(L & Maybe<&2, Why>, (l, Some{Asked{}}))
    case False{}:
      pure(L & Maybe<&2, Why>, (l, None{}))

# A connection to serve takes a slot first, so accepting parks while the
# limit is reached and the backlog holds what arrives meanwhile. A stop
# request is looked for on every turn, an arrival or not: asked only
# when nothing arrived, it went unseen for as long as arrivals kept
# coming. The ask is a flag read, not a syscall.
def accept.on(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~L: Type, ~C: Type,
  ~E: Data, ~sig: L -> M(L & Bool), ~hand: @+env: E -> L -> C -> M(L), +env: E, l: L,
  may: Maybe<&1, C>
) -> M(L & Maybe<&2, Why>):
  match may:
    case None{}:
      bind(L & Bool, L & Maybe<&2, Why>, sig(l), lb => accept.asked(~M, ~pure, ~bind, ~L, lb))
    case Some{c}:
      bind(L, L & Maybe<&2, Why>, hand(env, l, c), l2 =>
        bind(L & Bool, L & Maybe<&2, Why>, sig(l2), lb => accept.asked(~M, ~pure, ~bind, ~L,
            lb)))

# a failure ends the loop only when the listener is no longer one
def accept.dead(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~L: Type,
  ~sig: L -> M(L & Bool), l: L, +code: U32, soft: Bool
) -> M(L & Maybe<&2, Why>):
  match soft:
    case True{}:
      bind(L & Bool, L & Maybe<&2, Why>, sig(l), lb => accept.asked(~M, ~pure, ~bind, ~L, lb))
    case False{}:
      pure(L & Maybe<&2, Why>, (l, Some{Dead{code}}))

def accept.fail.at(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~L: Type,
  ~sig: L -> M(L & Bool), l: L, +code: U32
) -> M(L & Maybe<&2, Why>):
  accept.dead(~M, ~pure, ~bind, ~L, ~sig, l, code, accept.soft(code))

def accept.fail(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~L: Type,
  ~sig: L -> M(L & Bool), l: L, e: U32 & String
) -> M(L & Maybe<&2, Why>):
  (code, msg) = e
  accept.fail.at(~M, ~pure, ~bind, ~L, ~sig, l, code)

def accept.got(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~L: Type, ~C: Type,
  ~E: Data, ~sig: L -> M(L & Bool), ~hand: @+env: E -> L -> C -> M(L), +env: E,
  m: L & Result<&1, &1, U32 & String, Maybe<&1, C>>
) -> M(L & Maybe<&2, Why>):
  (l, r) = m
  match r:
    case Done{may}:
      accept.on(~M, ~pure, ~bind, ~L, ~C, ~E, ~sig, ~hand, env, l, may)
    case Fail{e}:
      accept.fail(~M, ~pure, ~bind, ~L, ~sig, l, e)

# how often the accept loop looks up from the listener, in ms: the most
# a stop request waits before it is seen
def accept.tick() -> U32:
  250

def accept.why(w: Maybe<&2, Why>) -> Why:
  match w:
    case None{}:
      Spent{}
    case Some{why}:
      why

# k turns of the loop, or fewer if it ends: one timed accept each, and
# the hand-off of what arrived
def accept.run(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~L: Type, ~C: Type,
  ~E: Data, ~lsn: L -> U32 -> M(L & Result<&1, &1, U32 & String, Maybe<&1, C>>),
  ~sig: L -> M(L & Bool), ~hand: @+env: E -> L -> C -> M(L), k: Nat, +env: E,
  lw: L & Maybe<&2, Why>
) -> M(L & Why):
  match k:
    case 0n:
      (l, w) = lw
      pure(L & Why, (l, accept.why(w)))
    case 1n+j:
      (l, w) = lw
      match w:
        case Some{why}:
          pure(L & Why, (l, why))
        case None{}:
          bind(L & Result<&1, &1, U32 & String, Maybe<&1, C>>, L & Why, lsn(l, accept.tick()), m =>
            bind(L & Maybe<&2, Why>, L & Why, accept.got(~M, ~pure, ~bind, ~L, ~C, ~E, ~sig,
                ~hand, env, m), lw2 =>
              accept.run(~M, ~pure, ~bind, ~L, ~C, ~E, ~lsn, ~sig, ~hand, j, env, lw2)))

# The real world
# ==============
#
# The interface's IO instance: the effects themselves, and the three
# that answer beside the handle they were given.
def net.now(s: Socket) -> IO(Socket & Nat):
  IO.bind(Nat, Socket & Nat, IO.now(), t => IO.pure(Socket & Nat, (s, t)))

def net.nap(s: Socket, ms: U32) -> IO(Socket):
  IO.bind(Unit, Socket, IO.sleep(ms), u => IO.pure(Socket, s))

def net.open(s: Socket, root: String, path: String) ->
  IO(Socket & Result<&1, &1, U32 & String, File>):
  IO.bind(Result<&1, &1, U32 & String, File>, Socket & Result<&1, &1, U32 & String, File>,
    File.open_under(root, path), r => IO.pure(Socket & Result<&1, &1, U32 & String, File>, (s, r)))

def net.sig(l: Listener) -> IO(Listener & Bool):
  IO.bind(Bool, Listener & Bool, IO.signal_pending(15), b => IO.pure(Listener & Bool, (l, b)))

# A connection ends by closing its socket and giving its slot back: the
# semaphore is a channel with as much room as connections allowed, a
# slot is a Unit sent into it, and accepting parks on a full one.
def fin(+sem: Chan(Unit), s: Socket) -> IO(Unit):
  do IO<Unit>:
    Socket.close(s)
    got : Maybe<&1, Unit> <- Chan.recv(Unit, sem)
    return Unit{}

def start(+srv: Srv, +sem: Chan(Unit), s: Socket) -> IO(Unit):
  do IO<Unit>:
    s2 : Socket <- conn.start(~(A => IO(A)), ~IO.pure, ~IO.bind, ~Socket, ~File, ~TCP.poll_buf,
      ~TCP.send_buf_poll, ~net.now, ~net.nap, ~IO.print_err, ~net.open, ~File.size,
          ~File.read_buf,
      ~File.close, srv, s)
    fin(sem, s2)

# what serving needs: the server, and the slots
type Env is Data:
  Env{srv: Srv, sem: Chan(Unit)}

def net.hand(+env: Env, l: Listener, s: Socket) -> IO(Listener):
  match env:
    case Env{srv, sem}:
      do IO<Listener>:
        ok : Bool <- Chan.send(Unit, sem, Unit{})
        IO.spawn(Unit, start(srv, sem, s))
        return l

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

# the turns one run of the loop takes before it is started again
def accept.fuel() -> Nat:
  U32.to_nat(1048576)

# The accept loop is the one place that runs until it is told to stop,
# so it is the one @unsafe def in the engine, and all it does is start
# accept.run again when its turns are spent. It stops for a stop
# request and for a listener that is no longer one.
@unsafe
def accept(+srv: Srv, +sem: Chan(Unit), lw: Listener & Why) -> IO(Unit):
  (l, why) = lw
  match why:
    case Spent{}:
      do IO<Unit>:
        lw2 : Listener & Why <- accept.run(~(A => IO(A)), ~IO.pure, ~IO.bind, ~Listener,
            ~Socket, ~Env, ~TCP.accept_poll,
          ~net.sig, ~net.hand, accept.fuel(), Env{srv, sem}, (l, None{}))
        accept(srv, sem, lw2)
    case Asked{}:
      stopping(srv, sem, l)
    case Dead{code}:
      stopping(srv, sem, l)

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

def early(stop: Bool) -> Why:
  match stop:
    case True{}:
      Asked{}
    case False{}:
      Spent{}

def run(+c: Cfg) -> IO(Unit):
  do IO<Unit>:
    l   : Listener <- IO.try(Listener, listen(cfg.port(c), cfg.shared(c), cfg.pem(c)))
    sem : Chan(Unit) <- Chan.new(Unit, cfg.conns(c))
    IO.print(banner(c))
    stop : Bool <- IO.signal_pending(15)
    accept(srv.new(c), sem, (l, early(stop)))

# bend-http [--port N] [--root DIR] [--idle-ms N] [--head-ms N] [--max-conns N]
#           [--grace-ms N] [--shared] [--tls-cert PEM --tls-key PEM] [--log]
def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    c  : Cfg <- args.done(args.read(xs, Args{cfg.new(), Flag{}}))
    run(c)
