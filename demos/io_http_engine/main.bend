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

def any(+c: U32, xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, t}:
      U32.is_eq(c, x) || any(c, t)

# the token characters that are neither letters nor digits
def tsym(+c: U32) -> Bool:
  any(c, [45, 46, 95, 33, 35, 36, 37, 38, 39, 42, 43, 94, 96, 124, 126])

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

# Field names are case-insensitive, so they are read lowercased.
def lower.go(+c: U32, up: Bool) -> U32:
  match up:
    case True{}:
      (c + 32 : U32)
    case False{}:
      c

def lower(+c: U32) -> U32:
  lower.go(c, U32.is_le(65, c) && U32.is_le(c, 90))

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

# Byte-list equality, structurally: what names, methods and the version
# are recognised by. LAWS.bend proves it is the reference's equality.
def bytes.eq(a: List<&2, U32>, b: List<&2, U32>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{y, u}:
      False{}
    case Con{x, t} Nil{}:
      False{}
    case Con{x, t} Con{y, u}:
      U32.is_eq(x, y) && bytes.eq(t, u)

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
  FOther{}

# a name as the reader holds it, lowercased and backwards, and the field
# it names
type Known is Data:
  Known{k: List<&2, U32>, f: Fld}

# transfer-encoding, content-length, connection, upgrade,
# sec-websocket-key and host, each backwards; LAWS.bend proves the
# lookup through this table is the lookup through the readable one
def fld.table() -> List<&2, Known>:
  [Known{[103, 110, 105, 100, 111, 99, 110, 101, 45, 114, 101, 102, 115, 110, 97, 114, 116], FTe{}},
   Known{[104, 116, 103, 110, 101, 108, 45, 116, 110, 101, 116, 110, 111, 99], FCl{}},
   Known{[110, 111, 105, 116, 99, 101, 110, 110, 111, 99], FConn{}},
   Known{[101, 100, 97, 114, 103, 112, 117], FUp{}},
   Known{[121, 101, 107, 45, 116, 101, 107, 99, 111, 115, 98, 101, 119, 45, 99, 101, 115], FKey{}},
   Known{[116, 115, 111, 104], FHost{}}]

def fld.pick(b: Bool, f: Fld, rest: Fld) -> Fld:
  match b:
    case True{}:
      f
    case False{}:
      rest

def fld.find(+k: List<&2, U32>, tbl: List<&2, Known>) -> Fld:
  match tbl:
    case Nil{}:
      FOther{}
    case Con{h, t}:
      match h:
        case Known{n, f}:
          fld.pick(bytes.eq(k, n), f, fld.find(k, t))

def fld.of(+k: List<&2, U32>) -> Fld:
  fld.find(k, fld.table())

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

# the method as read, backwards
def meth.of(+m: List<&2, U32>) -> Meth:
  meth.pick(bytes.eq(m, [84, 69, 71]), bytes.eq(m, [68, 65, 69, 72]))

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

# HTTP/1.1, backwards
def ver.lit() -> List<&2, U32>:
  [49, 46, 49, 47, 80, 84, 84, 72]

# the list members this engine acts on, backwards: close and upgrade in
# a Connection, websocket in an Upgrade
def tok.close() -> List<&2, U32>:
  [101, 115, 111, 108, 99]

def tok.upgrade() -> List<&2, U32>:
  [101, 100, 97, 114, 103, 112, 117]

def tok.websocket() -> List<&2, U32>:
  [116, 101, 107, 99, 111, 115, 98, 101, 119]

# Requests
# ========

# A parsed message: the method, the target and body as bytes, whether
# the peer asked to close, and whether it asked to become a WebSocket
# and with what key.
type Req is Data:
  Req{meth: Meth, path: List<&2, U32>, body: List<&2, U32>, close: Bool,
    ws: Bool, key: List<&2, U32>}

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
type Up is Data:
  Plain{}
  Asks{key: List<&2, U32>, up: Bool, cu: Bool}

def up.key(u: Up, k: List<&2, U32>) -> Up:
  match u:
    case Plain{}:
      Asks{k, False{}, False{}}
    case Asks{key, up, cu}:
      Asks{k, up, cu}

# an Upgrade or a Connection field adds to what the earlier ones said
def up.up(u: Up, v: Bool) -> Up:
  match u v:
    case Plain{} False{}:
      Plain{}
    case Plain{} True{}:
      Asks{Nil{}, True{}, False{}}
    case Asks{key, up, cu} w:
      Asks{key, up || w, cu}

def up.cu(u: Up, v: Bool) -> Up:
  match u v:
    case Plain{} False{}:
      Plain{}
    case Plain{} True{}:
      Asks{Nil{}, False{}, True{}}
    case Asks{key, up, cu} w:
      Asks{key, up, cu || w}

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
  Pend{meth: Meth, path: List<&2, U32>, cl: Cl, close: Bool, host: Hosts,
    ws: Up}

def pend.new() -> Pend:
  Pend{MOther{}, Nil{}, NoCl{}, False{}, H0{}, Plain{}}

# a new method token starts a new message, so the rest resets with it
def pend.meth(pd: Pend, m: Meth) -> Pend:
  match pd:
    case Pend{meth, path, cl, close, host, ws}:
      Pend{m, Nil{}, NoCl{}, False{}, H0{}, Plain{}}

def pend.path(pd: Pend, p: List<&2, U32>) -> Pend:
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

def pend.key(pd: Pend, k: List<&2, U32>) -> Pend:
  match pd:
    case Pend{meth, path, cl, close, host, ws}:
      Pend{meth, path, cl, close, host, up.key(ws, k)}

def pend.req.go(
  meth: Meth, path: List<&2, U32>, body: List<&2, U32>, close: Bool,
  asked: Bool & List<&2, U32>
) -> Req:
  (ws, key) = asked
  Req{meth, path, body, close, ws, key}

def pend.req(pd: Pend, body: List<&2, U32>) -> Req:
  match pd:
    case Pend{meth, path, cl, close, host, ws}:
      pend.req.go(meth, path, body, close, up.asked(ws))

# The reader
# ==========

# Pre  before a request line        PreLf the LF of an empty line there
# InM  the method, backwards         InT  the target, backwards
# InV  the version, backwards        CrM  a CR inside the head
# Lin  at the start of a field line  InN  a field name, lowercased, backwards
# InL0 a Content-Length, no digit    InL  its digits, v so far
# InLt the whitespace after them     InLc a Connection list: the member
#                                         being read, close and upgrade seen
# InLu an Upgrade list, websocket    InLk0/InLk a Sec-WebSocket-Key value
# InLx any other value, skipped      CrL  the CR of the blank line
# Bod  the body, r bytes to go       Rest what follows a request that
#                                         asked to upgrade, for the frame reader
# Bad  the grammar broke; absorbing, and never left
type St is Data:
  Pre{}
  PreLf{}
  InM{m: List<&2, U32>}
  InT{p: List<&2, U32>}
  InV{v: List<&2, U32>}
  CrM{}
  Lin{}
  InN{n: List<&2, U32>}
  InL0{}
  InL{v: U32}
  InLt{v: U32}
  InLc{t: List<&2, U32>, cl: Bool, up: Bool}
  InLu{t: List<&2, U32>, ws: Bool}
  InLk0{}
  InLk{k: List<&2, U32>}
  InLx{}
  CrL{}
  Bod{r: U32, b: List<&2, U32>}
  Rest{bs: List<&2, U32>}
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
      Rest{Nil{}}
    case False{}:
      Pre{}

def emit.go(r: Req, out: List<&2, Req>) -> P:
  match r:
    case Req{meth, path, body, close, +ws, key}:
      P{emit.next(ws), pend.new(), Req{meth, path, body, close, ws, key} <> out}

# a completed message rolls the machine straight into the next one
def emit(pd: Pend, body: List<&2, U32>, out: List<&2, Req>) -> P:
  emit.go(pend.req(pd, body), out)

# the method closes at its space, and a new message starts with it
def step.meth(+m: List<&2, U32>, pd: Pend, out: List<&2, Req>) -> P:
  P{InT{Nil{}}, pend.meth(pd, meth.of(m)), out}

# the target closes at its space; an empty one is no target
def step.target(p: List<&2, U32>, pd: Pend, out: List<&2, Req>) -> P:
  match p:
    case Nil{}:
      P{Bad{}, pd, out}
    case Con{c, t}:
      P{InV{Nil{}}, pend.path(pd, rev(Con{c, t})), out}

# the version token must read exactly HTTP/1.1
def step.ver(ok: Bool, pd: Pend, out: List<&2, Req>) -> P:
  match ok:
    case True{}:
      P{CrM{}, pd, out}
    case False{}:
      P{Bad{}, pd, out}

# where a value starts, by the field it belongs to
def val.init(f: Fld) -> St:
  match f:
    case FTe{}:
      Bad{}
    case FCl{}:
      InL0{}
    case FConn{}:
      InLc{Nil{}, False{}, False{}}
    case FUp{}:
      InLu{Nil{}, False{}}
    case FKey{}:
      InLk0{}
    case FHost{}:
      InLx{}
    case FOther{}:
      InLx{}

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
      P{InLc{Nil{}, False{}, False{}}, pd, out}
    case FUp{}:
      P{InLu{Nil{}, False{}}, pd, out}
    case FKey{}:
      P{InLk0{}, pd, out}
    case FHost{}:
      P{InLx{}, pend.host(pd), out}
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
  meth: Meth, path: List<&2, U32>, cl: Cl, close: Bool, host: Hosts, ws: Up,
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
def step.conn(+t: List<&2, U32>, cl: Bool, up: Bool, pd: Pend, out: List<&2, Req>) -> P:
  P{CrM{}, pend.conn(pd, cl || bytes.eq(t, tok.close()), up || bytes.eq(t, tok.upgrade())), out}

def tok.conn(+t: List<&2, U32>, cl: Bool, up: Bool) -> St:
  InLc{Nil{}, cl || bytes.eq(t, tok.close()), up || bytes.eq(t, tok.upgrade())}

def step.upv(+t: List<&2, U32>, ws: Bool, pd: Pend, out: List<&2, Req>) -> P:
  P{CrM{}, pend.up(pd, ws || bytes.eq(t, tok.websocket())), out}

def tok.up(+t: List<&2, U32>, ws: Bool) -> St:
  InLu{Nil{}, ws || bytes.eq(t, tok.websocket())}

# a Sec-WebSocket-Key value closes, kept as it came
def step.key(k: List<&2, U32>, pd: Pend, out: List<&2, Req>) -> P:
  P{CrM{}, pend.key(pd, rev(k)), out}

def step.head.len(pd: Pend, +v: U32, out: List<&2, Req>, z: Bool) -> P:
  match z:
    case True{}:
      emit(pd, Nil{}, out)
    case False{}:
      P{Bod{v, Nil{}}, pd, out}

def step.head.at(pd: Pend, cl: Cl, host: Hosts, out: List<&2, Req>) -> P:
  match cl host:
    case NoCl{} H1{}:
      emit(pd, Nil{}, out)
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
      P{InM{[c]}, pd, out}
    case Pre{} KDg{}:
      P{InM{[c]}, pd, out}
    case Pre{} _:
      P{Bad{}, pd, out}
    case PreLf{} KLf{}:
      P{Pre{}, pd, out}
    case PreLf{} _:
      P{Bad{}, pd, out}
    case InM{m} KSp{}:
      step.meth(m, pd, out)
    case InM{m} KTk{}:
      P{InM{Con{c, m}}, pd, out}
    case InM{m} KDg{}:
      P{InM{Con{c, m}}, pd, out}
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
      P{InT{Con{c, p}}, pd, out}
    case InV{+v} KCr{}:
      step.ver(bytes.eq(v, ver.lit()), pd, out)
    case InV{v} KTk{}:
      P{InV{Con{c, v}}, pd, out}
    case InV{v} KDg{}:
      P{InV{Con{c, v}}, pd, out}
    case InV{v} KVc{}:
      P{InV{Con{c, v}}, pd, out}
    case InV{v} _:
      P{Bad{}, pd, out}
    case CrM{} KLf{}:
      P{Lin{}, pd, out}
    case CrM{} _:
      P{Bad{}, pd, out}
    case Lin{} KCr{}:
      P{CrL{}, pd, out}
    case Lin{} KTk{}:
      P{InN{[lower(c)]}, pd, out}
    case Lin{} KDg{}:
      P{InN{[c]}, pd, out}
    case Lin{} _:
      P{Bad{}, pd, out}
    case InN{+n} KCo{}:
      step.name(fld.of(n), pd, out)
    case InN{n} KTk{}:
      P{InN{Con{lower(c), n}}, pd, out}
    case InN{n} KDg{}:
      P{InN{Con{c, n}}, pd, out}
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
      P{InLc{Con{lower(c), t}, a, b}, pd, out}
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
      P{InLu{Con{lower(c), t}, w}, pd, out}
    case InLk0{} KSp{}:
      P{InLk0{}, pd, out}
    case InLk0{} KHt{}:
      P{InLk0{}, pd, out}
    case InLk0{} KCr{}:
      step.key(Nil{}, pd, out)
    case InLk0{} KLf{}:
      P{Bad{}, pd, out}
    case InLk0{} KCt{}:
      P{Bad{}, pd, out}
    case InLk0{} _:
      P{InLk{[c]}, pd, out}
    case InLk{k} KCr{}:
      step.key(k, pd, out)
    case InLk{k} KLf{}:
      P{Bad{}, pd, out}
    case InLk{k} KCt{}:
      P{Bad{}, pd, out}
    case InLk{k} _:
      P{InLk{Con{c, k}}, pd, out}
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
      P{Rest{Con{c, bs}}, pd, out}
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
def p.rest(p: P) -> List<&2, U32>:
  match p:
    case P{st, pd, out}:
      match st:
        case Rest{bs}:
          rev(bs)
        case _:
          Nil{}

# A whole input, parsed from a fresh reader: the messages it completed,
# oldest first, and whether the grammar broke. LAWS.bend holds the
# reader to this on the vectors that matter.
def parse.out(pr: P & List<&2, Req>, dead: Bool) -> List<&2, Req> & Bool:
  (p, rs) = pr
  (rs, dead)

def parse.of(pb: P & Bool) -> List<&2, Req> & Bool:
  (p, dead) = pb
  parse.out(p.take(p), dead)

def parse(bs: List<&2, U32>) -> List<&2, Req> & Bool:
  parse.of(p.dead(feed(bs, p.new())))

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
  Note{bs: List<&2, U32>}
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
def log.line(+note: List<&2, U32>, +out: Bytes()) -> String:
  text(note) ++ " " ++ Bytes.slice(out, 9n, 3n) ++ " " ++ Nat.show(Bytes.len(out))

# a reply that ends its connection says so: a Shut before it marks it
def flat.shut(sh: Bool, +bs: Bytes()) -> Bytes():
  match sh:
    case True{}:
      closing(bs)
    case False{}:
      bs

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

# the writer: the socket, the bytes waiting, and whether everything
# promised so far has gone out. Once it has not, nothing more is written.
type Em is Type:
  Em{s: Socket, acc: Bytes(), ok: Bool}

# a file being written: its descriptor, the bytes still owed, the
# socket, and what waits to go out in front of the next block
type Pump is Type:
  Going{f: File, left: U32, s: Socket, pre: Bytes()}
  Over{em: Em}

def pump.left(f: File, left: U32, s: Socket, pre: Bytes(), done: Bool) -> IO(Pump):
  match done:
    case True{}:
      do IO<Pump>:
        File.close(f)
        return Over{Em{s, pre, True{}}}
    case False{}:
      do IO<Pump>:
        return Going{f, left, s, pre}

def pump.fail(f: File, s: Socket, pre: Bytes()) -> IO(Pump):
  do IO<Pump>:
    File.close(f)
    return Over{Em{s, pre, False{}}}

def pump.sent(m: Socket & Result<&1, &1, U32 & String, Unit>, f: File, +left: U32) -> IO(Pump):
  (s, r) = m
  match r:
    case Fail{e}:
      pump.fail(f, s, "")
    case Done{u}:
      pump.left(f, left, s, "", U32.is_zero(left))

def pump.block(
  f: File, +left: U32, s: Socket, pre: Bytes(), bs: Bytes(), +n: U32, empty: Bool
) -> IO(Pump):
  match empty:
    case True{}:
      pump.fail(f, s, pre)
    case False{}:
      do IO<Pump>:
        m : Socket & Result<&1, &1, U32 & String, Unit> <-
          TCP.send_buf(s, Bytes.append(pre, bs))
        pump.sent(m, f, (left - n : U32))

def pump.got(
  got: File & Result<&1, &1, U32 & String, Bytes()>, left: U32, s: Socket, pre: Bytes()
) -> IO(Pump):
  (f, r) = got
  match r:
    case Fail{e}:
      pump.fail(f, s, pre)
    case Done{+bs}:
      pump.block(f, left, s, pre, bs, U32.from_nat(Bytes.len(bs)), U32.is_zero(U32.from_nat(Bytes.len(bs))))

def pump.out(p: Pump) -> IO(Em):
  match p:
    case Over{em}:
      do IO<Em>:
        return em
    case Going{f, left, s, pre}:
      do IO<Em>:
        File.close(f)
        return Em{s, pre, False{}}

# k bounds the reads: a block's worth each, and 64 short ones besides
def pump(k: Nat, p: Pump) -> IO(Em):
  match k:
    case 0n:
      pump.out(p)
    case 1n+j:
      match p:
        case Over{em}:
          do IO<Em>:
            return em
        case Going{f, +left, s, pre}:
          do IO<Em>:
            got : File & Result<&1, &1, U32 & String, Bytes()> <-
              File.read_buf(f, U32.min(page.chunk(), left))
            p2 : Pump <- pump.got(got, left, s, pre)
            pump(j, p2)

# a file's log line: its head's status, and the bytes its reply holds
def log.sized(may: Maybe<&2, List<&2, U32>>, +hd: Bytes(), n: U32) -> IO(Unit):
  match may:
    case None{}:
      do IO<Unit>:
        return Unit{}
    case Some{note}:
      IO.print_err(text(note) ++ " " ++ Bytes.slice(hd, 9n, 3n) ++ " "
        ++ U32.show((U32.from_nat(Bytes.len(hd)) + n : U32)))

def page.miss(head: Bool, may: Maybe<&2, List<&2, U32>>, sh: Bool, s: Socket, acc: Bytes()) -> IO(Em):
  do IO<Em>:
    out : Bytes() <- flat.note(may, flat.shut(sh, miss(head)))
    return Em{s, Bytes.append(acc, out), True{}}

def page.start(
  f: File, +n: U32, +hd: Bytes(), head: Bool, may: Maybe<&2, List<&2, U32>>, s: Socket,
  acc: Bytes()
) -> IO(Em):
  match head:
    case True{}:
      do IO<Em>:
        log.sized(may, hd, 0)
        File.close(f)
        return Em{s, Bytes.append(acc, hd), True{}}
    case False{}:
      do IO<Em>:
        log.sized(may, hd, n)
        p : Pump <- pump.left(f, n, s, Bytes.append(acc, hd), U32.is_zero(n))
        pump(U32.to_nat((n / page.chunk() + 64 : U32)), p)

def page.sized(
  got: File & Result<&1, &1, U32 & String, U32>, ct: List<&2, U32>, head: Bool,
  may: Maybe<&2, List<&2, U32>>, sh: Bool, s: Socket, acc: Bytes()
) -> IO(Em):
  (f, r) = got
  match r:
    case Fail{e}:
      do IO<Em>:
        File.close(f)
        page.miss(head, may, sh, s, acc)
    case Done{+n}:
      page.start(f, n, flat.shut(sh, reply.n.head("200 OK", ct, n)), head, may, s, acc)

def page.opened(
  r: Result<&1, &1, U32 & String, File>, ct: List<&2, U32>, head: Bool,
  may: Maybe<&2, List<&2, U32>>, sh: Bool, s: Socket, acc: Bytes()
) -> IO(Em):
  match r:
    case Fail{e}:
      page.miss(head, may, sh, s, acc)
    case Done{f}:
      do IO<Em>:
        got : File & Result<&1, &1, U32 & String, U32> <- File.size(f)
        page.sized(got, ct, head, may, sh, s, acc)

def send.page(
  root: List<&2, U32>, path: List<&2, U32>, ct: List<&2, U32>, head: Bool,
  may: Maybe<&2, List<&2, U32>>, sh: Bool, st: Em
) -> IO(Em):
  match st:
    case Em{s, acc, ok}:
      match ok:
        case False{}:
          do IO<Em>:
            return Em{s, acc, False{}}
        case True{}:
          do IO<Em>:
            r : Result<&1, &1, U32 & String, File> <- File.open_under(text(root), text(path))
            page.opened(r, ct, head, may, sh, s, acc)

def send.raw(may: Maybe<&2, List<&2, U32>>, bs: Bytes(), st: Em) -> IO(Em):
  match st:
    case Em{s, acc, ok}:
      match ok:
        case False{}:
          do IO<Em>:
            return Em{s, acc, False{}}
        case True{}:
          do IO<Em>:
            out : Bytes() <- flat.note(may, bs)
            return Em{s, Bytes.append(acc, out), True{}}

def send.fin(m: Socket & Result<&1, &1, U32 & String, Unit>, ok: Bool) ->
  IO(Socket & Result<&1, &1, U32 & String, Unit>):
  (s, r) = m
  match ok:
    case True{}:
      do IO<Socket & Result<&1, &1, U32 & String, Unit>>:
        return (s, r)
    case False{}:
      do IO<Socket & Result<&1, &1, U32 & String, Unit>>:
        return (s, Fail{(5, "a file ended before the length its head promised")})

def send.end(st: Em) -> IO(Socket & Result<&1, &1, U32 & String, Unit>):
  match st:
    case Em{s, acc, ok}:
      do IO<Socket & Result<&1, &1, U32 & String, Unit>>:
        m : Socket & Result<&1, &1, U32 & String, Unit> <- TCP.send_buf(s, acc)
        send.fin(m, ok)

# a Shut before a reply marks the one that ends its connection
def send.go(xs: List<&2, Seg>, may: Maybe<&2, List<&2, U32>>, sh: Bool, st: Em) ->
  IO(Socket & Result<&1, &1, U32 & String, Unit>):
  match xs:
    case Nil{}:
      send.end(st)
    case Con{g, t}:
      match g:
        case Note{bs}:
          send.go(t, Some{bs}, sh, st)
        case Shut{}:
          send.go(t, may, True{}, st)
        case Raw{bs}:
          do IO<Socket & Result<&1, &1, U32 & String, Unit>>:
            st2 : Em <- send.raw(may, flat.shut(sh, bs), st)
            send.go(t, None{}, False{}, st2)
        case Page{root, path, ct, head}:
          do IO<Socket & Result<&1, &1, U32 & String, Unit>>:
            st2 : Em <- send.page(root, path, ct, head, may, sh, st)
            send.go(t, None{}, False{}, st2)

# The one hook the connection loop calls: write a plan's segments to the
# socket, in order, streaming files; the result fails when the socket
# failed or a file came up short, and the connection then ends.
def send.segs(s: Socket, xs: List<&2, Seg>) -> IO(Socket & Result<&1, &1, U32 & String, Unit>):
  send.go(xs, None{}, False{}, Em{s, "", True{}})


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

# /events: the stream's head, then the events; a HEAD gets the head
# and no stream, since a HEAD reply carries no body
def events(head: Bool) -> Ans:
  match head:
    case True{}:
      Ans{[Raw{sse.head()}], False{}, 0, False{}}
    case False{}:
      Ans{[Raw{sse.head()}], False{}, sse.count(), False{}}

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
      events(head)
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

# what a log line says was asked: the two methods this engine serves
# are named, and anything else is "?", so a log line never carries a
# method's bytes
def shown(m: Meth) -> List<&2, U32>:
  match m:
    case MGet{}:
      bytes("GET")
    case MHead{}:
      bytes("HEAD")
    case MOther{}:
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

def path.keep(acc: List<&2, U32>, c: U32, stop: Bool) -> List<&2, U32>:
  match stop:
    case True{}:
      acc
    case False{}:
      Con{c, acc}

def path.go(p: List<&2, U32>, stop: Bool, acc: List<&2, U32>) -> List<&2, U32>:
  match p stop:
    case Nil{} _:
      rev(acc)
    case Con{c, t} True{}:
      path.go(t, True{}, acc)
    case Con{+c, t} False{}:
      path.go(t, U32.is_eq(c, 63), path.keep(acc, c, U32.is_eq(c, 63)))

# the path a target names is its bytes before any '?': the query says
# nothing about which resource is asked for, so /health?x=1 is /health
def path.of(p: List<&2, U32>) -> List<&2, U32>:
  path.go(p, False{}, Nil{})

def serve.log(+srv: Srv, r: Req) -> Ans:
  match r:
    case Req{+meth, +path, body, close, ws, key}:
      noted(srv.log(srv), cat(shown(meth), cat(bytes(" "), path)),
        serve.go(srv, path.of(path), body, meth.get(meth) || meth.head(meth),
          meth.head(meth), ws, key))

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
          End{List.append(&2, Seg, out, [Raw{Bytes.from_list(o)}])}
        case False{}:
          Sock{List.append(&2, Seg, out, [Raw{Bytes.from_list(o)}]), wr}

def plan.up.dead(out: List<&2, Seg>, fs: List<&2, Ws.Frm>, dd: Ws.W & Bool) -> Plan:
  (wr, bad) = dd
  plan.up.rep(out, wr, Ws.reply(fs, bad))

def plan.up.take(out: List<&2, Seg>, tk: Ws.W & List<&2, Ws.Frm>) -> Plan:
  (wr, fs) = tk
  plan.up.dead(out, fs, Ws.dead(wr))

def plan.up(out: List<&2, Seg>, rest: List<&2, U32>) -> Plan:
  plan.up.take(out, Ws.take(Ws.feed(rest, Ws.new())))

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
  match r:
    case Fail{e}:
      do IO<Socket & Plan>:
        return (s, Stop{})
    case Done{u}:
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
            m : Socket & Result<&1, &1, U32 & String, Unit> <- send.segs(s, out)
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
            m   : Socket & Result<&1, &1, U32 & String, Unit> <- send.segs(s, out)
            sp2 : Socket & Plan <- tick(m, n)
            conn(g, srv, sem, sp2, conn.waits())
        case Sock{out, wr}:
          do IO<Unit>:
            m   : Socket & Result<&1, &1, U32 & String, Unit> <- send.segs(s, out)
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
            m   : Socket & Result<&1, &1, U32 & String, Unit> <- send.segs(s, out)
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
