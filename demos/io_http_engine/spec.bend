# The reference the reader is held to: the head grammar of RFC 9110 5.6
# and RFC 9112 2-7 -- HTTP/1.1 and HTTP/1.0 request heads, a body framed
# by Content-Length or by the chunked coding (RFC 9112 7.1) -- written
# for whoever checks it rather than for the clock. Every def here is
# the obvious one -- a class is membership in
# the RFC's own character sets, an equality is a walk, a field is the
# table entry spelled with exactly its bytes -- so that LAWS.bend can
# say "the engine agrees with this" and a reader can believe the claim
# by reading one short file instead of main.bend's state machine.
import Base
import ./main.bend as Eng

# Bytes
# =====

# two byte strings are equal when they are the same bytes, in order
def eq(a: Bytes(), b: Bytes()) -> Bool:
  match a b:
    case SNil{} SNil{}:
      True{}
    case SNil{} SCon{Chr{y}, u}:
      False{}
    case SCon{Chr{x}, t} SNil{}:
      False{}
    case SCon{Chr{x}, t} SCon{Chr{y}, u}:
      U32.is_eq(x, y) && eq(t, u)

def mem(+c: U32, xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, t}:
      U32.is_eq(c, x) || mem(c, t)

# every byte, 0 to 255
def all.go(n: Nat, +c: U32) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{c, all.go(p, (c + 1 : U32))}

def all() -> List<&2, U32>:
  all.go(256n, 0)

# Bytes
# =====

def digits() -> List<&2, U32>:
  Eng.bytes("0123456789")

def upper() -> List<&2, U32>:
  Eng.bytes("ABCDEFGHIJKLMNOPQRSTUVWXYZ")

def lowers() -> List<&2, U32>:
  Eng.bytes("abcdefghijklmnopqrstuvwxyz")

# tchar (RFC 9110 5.6.2): ALPHA, DIGIT, and these fifteen
def tchar(+c: U32) -> Bool:
  mem(c, Eng.bytes("!#$%&'*+-.^_`|~")) || mem(c, digits()) || mem(c, upper())
    || mem(c, lowers())

# CTL (RFC 5234): 0 to 31, and 127
def ctl(+c: U32) -> Bool:
  U32.is_lt(c, 32) || U32.is_eq(c, 127)

def cls.pick(b: Bool, k: Eng.Cls, rest: Eng.Cls) -> Eng.Cls:
  match b:
    case True{}:
      k
    case False{}:
      rest

# what a byte is to the head grammar, first match wins: SP, HTAB, CR,
# LF, ":", ",", a DIGIT, any other tchar, any other CTL, and the rest
# (the visible bytes that are not tchar, and obs-text)
def cls(+c: U32) -> Eng.Cls:
  cls.pick(U32.is_eq(c, 32), Eng.KSp{},
  cls.pick(U32.is_eq(c, 9), Eng.KHt{},
  cls.pick(U32.is_eq(c, 13), Eng.KCr{},
  cls.pick(U32.is_eq(c, 10), Eng.KLf{},
  cls.pick(U32.is_eq(c, 58), Eng.KCo{},
  cls.pick(U32.is_eq(c, 44), Eng.KCm{},
  cls.pick(mem(c, digits()), Eng.KDg{},
  cls.pick(tchar(c), Eng.KTk{},
  cls.pick(ctl(c), Eng.KCt{}, Eng.KVc{})))))))))

def u32.pick(b: Bool, x: U32, y: U32) -> U32:
  match b:
    case True{}:
      x
    case False{}:
      y

# an uppercase letter's lowercase, and every other byte as it is
def lower.at(+c: U32, us: List<&2, U32>, ls: List<&2, U32>) -> U32:
  match us ls:
    case Con{u, ut} Con{l, lt}:
      u32.pick(U32.is_eq(c, u), l, lower.at(c, ut, lt))
    case _ _:
      c

def lower(+c: U32) -> U32:
  lower.at(c, upper(), lowers())

# the engine's classes and lowercasing of every byte, beside the
# reference's: LAWS.bend says the two lists are equal
def cls.eng(xs: List<&2, U32>) -> List<&2, Eng.Cls>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{c, t}:
      Con{Eng.cls(c), cls.eng(t)}

def cls.ref(xs: List<&2, U32>) -> List<&2, Eng.Cls>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{c, t}:
      Con{cls(c), cls.ref(t)}

def lower.eng(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{c, t}:
      Con{Eng.lower(c), lower.eng(t)}

def lower.ref(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{c, t}:
      Con{lower(c), lower.ref(t)}

# which classes each part of a head may carry: a field name its token
# bytes and the colon that ends it; the start of a field line a token
# byte or the CR of the blank line; a Content-Length digits, then
# whitespace, then its CR; the target anything but a control, a tab or
# a line end; a value anything but a bare LF or a control
def in.name(k: Eng.Cls) -> Bool:
  match k:
    case Eng.KTk{}:
      True{}
    case Eng.KDg{}:
      True{}
    case Eng.KCo{}:
      True{}
    case _:
      False{}

def in.line(k: Eng.Cls) -> Bool:
  match k:
    case Eng.KTk{}:
      True{}
    case Eng.KDg{}:
      True{}
    case Eng.KCr{}:
      True{}
    case _:
      False{}

def in.clen(k: Eng.Cls) -> Bool:
  match k:
    case Eng.KDg{}:
      True{}
    case Eng.KSp{}:
      True{}
    case Eng.KHt{}:
      True{}
    case Eng.KCr{}:
      True{}
    case _:
      False{}

def in.target(k: Eng.Cls) -> Bool:
  match k:
    case Eng.KHt{}:
      False{}
    case Eng.KCr{}:
      False{}
    case Eng.KLf{}:
      False{}
    case Eng.KCt{}:
      False{}
    case _:
      True{}

def in.value(k: Eng.Cls) -> Bool:
  match k:
    case Eng.KLf{}:
      False{}
    case Eng.KCt{}:
      False{}
    case _:
      True{}

# Names
# =====

# a name as the reader looks it up: its bytes, lowercased
def name(s: String) -> Bytes():
  s

# a name lowercased, byte by byte, as lower() above does it
def lows(s: Bytes()) -> Bytes():
  match s:
    case SNil{}:
      SNil{}
    case SCon{Chr{c}, t}:
      SCon{Chr{lower(c)}, lows(t)}

def fields.rest() -> List<&2, Eng.Known>:
  [Eng.Known{name("content-length"), Eng.FCl{}},
   Eng.Known{name("connection"), Eng.FConn{}},
   Eng.Known{name("upgrade"), Eng.FUp{}},
   Eng.Known{name("sec-websocket-key"), Eng.FKey{}},
   Eng.Known{name("host"), Eng.FHost{}},
   Eng.Known{name("sec-websocket-version"), Eng.FVer{}}]

# the fields the engine acts on, spelled as RFC 9110 and RFC 6455 spell
# them. The names are distinct, so the order of the table is no part
# of what it says.
def fields() -> List<&2, Eng.Known>:
  Con{Eng.Known{name("transfer-encoding"), Eng.FTe{}}, fields.rest()}

# the field a name is: the entry spelled with exactly its bytes, and
# no field when there is none
def find(+k: Bytes(), tbl: List<&2, Eng.Known>) -> Eng.Fld:
  match tbl:
    case Nil{}:
      Eng.FOther{}
    case Con{h, t}:
      match h:
        case Eng.Known{n, f}:
          Eng.fld.pick(eq(k, n), f, find(k, t))

def field(+k: Bytes()) -> Eng.Fld:
  find(k, fields())

# HTTP/1.1 asks for exactly one Host (RFC 9112 3.2)
def one(h: Eng.Hosts) -> Bool:
  match h:
    case Eng.H1{}:
      True{}
    case _:
      False{}

# HTTP/1.0 asks for at most one
def most(h: Eng.Hosts) -> Bool:
  match h:
    case Eng.H2{}:
      False{}
    case _:
      True{}

def hosts.fit(v10: Bool, h: Eng.Hosts) -> Bool:
  match v10:
    case True{}:
      most(h)
    case False{}:
      one(h)

# The framer
# ==========
#
# What the reader is held to as a whole. frame() takes every byte a
# peer sent, however TCP cut it, and says what RFC 9112 makes of it --
# for the part of HTTP/1.1 and HTTP/1.0 this engine accepts: the
# requests it holds, oldest first, and how it ends. It never steps a
# head's byte through a state machine of the engine's shape. A line is
# gathered until its CR LF and only then read, whole: a request line
# split at its spaces into a method, a target and a version (RFC 9112
# 3), a field line split at its colon into a name and a value (RFC 9110
# 5), the value read by what the name is. A head ends at its empty line
# and is judged then (its Hosts, RFC 9112 3.2; its framing, RFC 9112
# 6.1 and 6.3), and a body is counted off by its length, or read by the
# chunked coding's own grammar (RFC 9112 7.1, below), which is regular
# and is written as the table of it. A line the input stops inside is
# read the same way, as far as it goes.

# how a whole input ends: part way into a request or between two, with
# the bytes since the last complete one; refused; or after a request
# that asked to upgrade, with what followed it, which is not HTTP
type End is Data:
  Open{rest: List<&2, U32>}
  Refused{}
  Upgraded{rest: Bytes()}

type Frames is Data:
  Frames{reqs: List<&2, Eng.Req>, end: End}

def snoc(xs: List<&2, U32>, x: U32) -> List<&2, U32>:
  List.append(&2, U32, xs, [x])

# Tokens
# ------

# the runs a line is split into, and the classes of byte each may hold:
# a method and a field name are tchar (RFC 9110 5.6.2); a target is any
# visible byte or obs-text (RFC 9112 3.2); a version is read whole at
# its CR and compared with HTTP/1.1, so it may hold what that is made
# of -- tchar, digits, "/" and the other visible bytes -- but not a
# space, a control, nor the ":" and "," that separate a head's parts;
# OWS is spaces and tabs (RFC 9110 5.6.3); a field value is anything
# but CR, LF and the controls, spaces and tabs included (RFC 9110 5.5)
type Tok is Data:
  TMeth{}
  TTarget{}
  TVer{}
  TName{}
  TOws{}
  TVal{}

def allows(t: Tok, k: Eng.Cls) -> Bool:
  match t k:
    case TMeth{} Eng.KTk{}:
      True{}
    case TMeth{} Eng.KDg{}:
      True{}
    case TMeth{} _:
      False{}
    case TTarget{} Eng.KSp{}:
      False{}
    case TTarget{} Eng.KHt{}:
      False{}
    case TTarget{} Eng.KCr{}:
      False{}
    case TTarget{} Eng.KLf{}:
      False{}
    case TTarget{} Eng.KCt{}:
      False{}
    case TTarget{} _:
      True{}
    case TVer{} Eng.KTk{}:
      True{}
    case TVer{} Eng.KDg{}:
      True{}
    case TVer{} Eng.KVc{}:
      True{}
    case TVer{} _:
      False{}
    case TName{} Eng.KTk{}:
      True{}
    case TName{} Eng.KDg{}:
      True{}
    case TName{} _:
      False{}
    case TOws{} Eng.KSp{}:
      True{}
    case TOws{} Eng.KHt{}:
      True{}
    case TOws{} _:
      False{}
    case TVal{} Eng.KCr{}:
      False{}
    case TVal{} Eng.KLf{}:
      False{}
    case TVal{} Eng.KCt{}:
      False{}
    case TVal{} _:
      True{}

# the longest run of bytes a token may hold, from the first, and what
# stopped it: the end of the line, or a byte (its class, itself, and
# what follows it)
type Stop is Data:
  SEnd{}
  SAt{k: Eng.Cls, c: U32, rest: List<&2, U32>}

type Span is Data:
  Span{run: List<&2, U32>, stop: Stop}

def span.push(c: U32, sp: Span) -> Span:
  match sp:
    case Span{r, s}:
      Span{Con{c, r}, s}

def span.pick(ok: Bool, k: Eng.Cls, c: U32, rest: List<&2, U32>, more: Span) -> Span:
  match ok:
    case True{}:
      span.push(c, more)
    case False{}:
      Span{Nil{}, SAt{k, c, rest}}

def span(+t: Tok, bs: List<&2, U32>) -> Span:
  match bs:
    case Nil{}:
      Span{Nil{}, SEnd{}}
    case Con{+c, +rest}:
      +k = cls(c)
      span.pick(allows(t, k), k, c, rest, span(t, rest))

# The request line
# ----------------

# a request line, or as much of one as has come: split at its spaces,
# it is a method, then a target, then a version (RFC 9112 3); the
# method and the target may not be empty, and nothing follows the
# version but the line's end
type RLine is Data:
  RNone{}
  RMeth{m: List<&2, U32>}
  RTarget{m: List<&2, U32>, t: List<&2, U32>}
  RVer{m: List<&2, U32>, t: List<&2, U32>, v: List<&2, U32>}
  RBad{}

def req.ver(m: List<&2, U32>, t: List<&2, U32>, sp: Span) -> RLine:
  match sp:
    case Span{v, SEnd{}}:
      RVer{m, t, v}
    case Span{v, SAt{k, c, rest}}:
      RBad{}

# a target ended at a space: it may not be empty
def req.target.sp(m: List<&2, U32>, t: List<&2, U32>, rest: List<&2, U32>) -> RLine:
  match t:
    case Nil{}:
      RBad{}
    case Con{h, r}:
      req.ver(m, Con{h, r}, span(TVer{}, rest))

def req.target(m: List<&2, U32>, sp: Span) -> RLine:
  match sp:
    case Span{t, SEnd{}}:
      RTarget{m, t}
    case Span{t, SAt{Eng.KSp{}, c, rest}}:
      req.target.sp(m, t, rest)
    case Span{t, SAt{k, c, rest}}:
      RBad{}

def req.meth(sp: Span) -> RLine:
  match sp:
    case Span{Nil{}, s}:
      RBad{}
    case Span{Con{h, r}, SEnd{}}:
      RMeth{Con{h, r}}
    case Span{Con{h, r}, SAt{Eng.KSp{}, c, rest}}:
      req.target(Con{h, r}, span(TTarget{}, rest))
    case Span{m, SAt{k, c, rest}}:
      RBad{}

def req.view(x: List<&2, U32>) -> RLine:
  match x:
    case Nil{}:
      RNone{}
    case Con{c, t}:
      req.meth(span(TMeth{}, Con{c, t}))

# The field lines
# ---------------

# a field line, or as much of one as has come: a name, a colon, and a
# value read by what the name is (RFC 9110 5). The value of a field
# this engine acts on is kept as far as the line's end needs it:
#   VLen0 / VLen  Content-Length: OWS, digits read as n, then OWS; ws
#                 says whether whitespace has come after the digits
#   VConn / VUp   Connection / Upgrade: a list, split at commas and
#                 whitespace into the members done (newest first) and
#                 the one being read
#   VKey0 / VKey  Sec-WebSocket-Key: OWS, then the key as it came
#   VVer          Sec-WebSocket-Version, as it came
#   VTe0 / VTe    Transfer-Encoding: OWS, then the coding as it came
#   VHost / VSkip Host, or any other field: the value is only checked
type Val is Data:
  VLen0{}
  VLen{n: U32, ws: Bool}
  VConn{done: List<&2, List<&2, U32>>, cur: List<&2, U32>}
  VUp{done: List<&2, List<&2, U32>>, cur: List<&2, U32>}
  VKey0{}
  VKey{k: List<&2, U32>}
  VVer{v: List<&2, U32>}
  VTe0{}
  VTe{t: List<&2, U32>}
  VHost{}
  VSkip{}

type FLine is Data:
  FEmpty{}
  FName{n: List<&2, U32>}
  FVal{v: Val}
  FBad{}

# Content-Length = 1*DIGIT (RFC 9112 6.3), OWS on either side. The
# digits are read as a decimal left to right, and a length past the most
# body this engine holds is refused at the digit that passes it: no
# later digit brings it back, and the value read so far is never past
# the cap, so ten times it plus a digit never wraps.
def len.cap() -> U32:
  1048576

def len.digit(v: U32, c: U32) -> U32:
  (v * 10 + (c - 48) : U32)

type Dec is Data:
  DNum{n: U32, stop: Stop}
  DBig{}

def dec.big(big: Bool, more: Dec) -> Dec:
  match big:
    case True{}:
      DBig{}
    case False{}:
      more

def is.digit(k: Eng.Cls) -> Bool:
  match k:
    case Eng.KDg{}:
      True{}
    case _:
      False{}

def dec.pick(dg: Bool, k: Eng.Cls, +c: U32, rest: List<&2, U32>, +v: U32, more: Dec) -> Dec:
  match dg:
    case True{}:
      dec.big(U32.is_lt(len.cap(), len.digit(v, c)), more)
    case False{}:
      DNum{v, SAt{k, c, rest}}

def dec(x: List<&2, U32>, +v: U32) -> Dec:
  match x:
    case Nil{}:
      DNum{v, SEnd{}}
    case Con{+c, +rest}:
      +k = cls(c)
      dec.pick(is.digit(k), k, c, rest, v, dec(rest, len.digit(v, c)))

def len.ws(n: U32, sp: Span) -> FLine:
  match sp:
    case Span{w, SEnd{}}:
      FVal{VLen{n, True{}}}
    case Span{w, SAt{k, c, rest}}:
      FBad{}

def len.num(d: Dec) -> FLine:
  match d:
    case DBig{}:
      FBad{}
    case DNum{n, SEnd{}}:
      FVal{VLen{n, False{}}}
    case DNum{n, SAt{Eng.KSp{}, c, rest}}:
      len.ws(n, span(TOws{}, rest))
    case DNum{n, SAt{Eng.KHt{}, c, rest}}:
      len.ws(n, span(TOws{}, rest))
    case DNum{n, SAt{k, c, rest}}:
      FBad{}

def len.first(c: U32, rest: List<&2, U32>) -> FLine:
  +n = len.digit(0, c)
  len.num(dec.big(U32.is_lt(len.cap(), n), dec(rest, n)))

def len.view(sp: Span) -> FLine:
  match sp:
    case Span{w, SEnd{}}:
      FVal{VLen0{}}
    case Span{w, SAt{Eng.KDg{}, c, rest}}:
      len.first(c, rest)
    case Span{w, SAt{k, c, rest}}:
      FBad{}

# a list (RFC 9110 5.6.1): members split at commas and whitespace, empty
# ones allowed; a byte no value may hold spoils it
type Mem is Data:
  Mem{done: List<&2, List<&2, U32>>, cur: List<&2, U32>}
  LBad{}

def mem.sep(k: Eng.Cls) -> Bool:
  match k:
    case Eng.KSp{}:
      True{}
    case Eng.KHt{}:
      True{}
    case Eng.KCm{}:
      True{}
    case _:
      False{}

def mem.done(s: Bool, done: List<&2, List<&2, U32>>, cur: List<&2, U32>) ->
  List<&2, List<&2, U32>>:
  match s:
    case True{}:
      Con{cur, done}
    case False{}:
      done

def mem.cur(s: Bool, cur: List<&2, U32>, c: U32) -> List<&2, U32>:
  match s:
    case True{}:
      Nil{}
    case False{}:
      snoc(cur, c)

def mem.end(ok: Bool, done: List<&2, List<&2, U32>>, cur: List<&2, U32>) -> Mem:
  match ok:
    case True{}:
      Mem{done, cur}
    case False{}:
      LBad{}

def members(x: List<&2, U32>, ok: Bool, done: List<&2, List<&2, U32>>, +cur: List<&2, U32>) -> Mem:
  match x:
    case Nil{}:
      mem.end(ok, done, cur)
    case Con{+c, t}:
      +k = cls(c)
      +s = mem.sep(k)
      members(t, ok && allows(TVal{}, k), mem.done(s, done, cur), mem.cur(s, cur, c))

def list.view(conn: Bool, m: Mem) -> FLine:
  match conn m:
    case _ LBad{}:
      FBad{}
    case True{} Mem{d, c}:
      FVal{VConn{d, c}}
    case False{} Mem{d, c}:
      FVal{VUp{d, c}}

# a key: OWS, then bytes a value may hold
def key.more(c: U32, sp: Span) -> FLine:
  match sp:
    case Span{r, SEnd{}}:
      FVal{VKey{Con{c, r}}}
    case Span{r, SAt{k, d, rest}}:
      FBad{}

def key.first(ok: Bool, c: U32, rest: List<&2, U32>) -> FLine:
  match ok:
    case True{}:
      key.more(c, span(TVal{}, rest))
    case False{}:
      FBad{}

def key.view(sp: Span) -> FLine:
  match sp:
    case Span{w, SEnd{}}:
      FVal{VKey0{}}
    case Span{w, SAt{k, c, rest}}:
      key.first(allows(TVal{}, k), c, rest)

# a version, or any value only checked: bytes a value may hold
def ver.view(sp: Span) -> FLine:
  match sp:
    case Span{v, SEnd{}}:
      FVal{VVer{v}}
    case Span{v, SAt{k, c, rest}}:
      FBad{}

# a transfer coding: OWS, then bytes a value may hold, kept as they came.
# Only whitespace before it is OWS to be cut: one after it is kept, and
# "chunked " is then not chunked -- it is how the coding is dressed up
# to be read one way by one reader and another way by the next.
def te.more(c: U32, sp: Span) -> FLine:
  match sp:
    case Span{r, SEnd{}}:
      FVal{VTe{Con{c, r}}}
    case Span{r, SAt{k, d, rest}}:
      FBad{}

def te.first(ok: Bool, c: U32, rest: List<&2, U32>) -> FLine:
  match ok:
    case True{}:
      te.more(c, span(TVal{}, rest))
    case False{}:
      FBad{}

def te.view(sp: Span) -> FLine:
  match sp:
    case Span{w, SEnd{}}:
      FVal{VTe0{}}
    case Span{w, SAt{k, c, rest}}:
      te.first(allows(TVal{}, k), c, rest)

def skip.view(val: Val, sp: Span) -> FLine:
  match sp:
    case Span{v, SEnd{}}:
      FVal{val}
    case Span{v, SAt{k, c, rest}}:
      FBad{}

# a name's field, and its value read the way the name says
def field.of(f: Eng.Fld, v: List<&2, U32>) -> FLine:
  match f:
    case Eng.FTe{}:
      te.view(span(TOws{}, v))
    case Eng.FCl{}:
      len.view(span(TOws{}, v))
    case Eng.FConn{}:
      list.view(True{}, members(v, True{}, Nil{}, Nil{}))
    case Eng.FUp{}:
      list.view(False{}, members(v, True{}, Nil{}, Nil{}))
    case Eng.FKey{}:
      key.view(span(TOws{}, v))
    case Eng.FHost{}:
      skip.view(VHost{}, span(TVal{}, v))
    case Eng.FVer{}:
      ver.view(span(TVal{}, v))
    case Eng.FOther{}:
      skip.view(VSkip{}, span(TVal{}, v))

# a field line is a name and its colon: no space before the colon (RFC
# 9112 5.1), no line folded onto the one before (a line that starts
# with whitespace has no name, RFC 9112 5.2)
def field.name(sp: Span) -> FLine:
  match sp:
    case Span{Nil{}, s}:
      FBad{}
    case Span{Con{h, r}, SEnd{}}:
      FName{Con{h, r}}
    case Span{Con{h, r}, SAt{Eng.KCo{}, c, v}}:
      field.of(field(lows(Bytes.from_list(Con{h, r}))), v)
    case Span{n, SAt{k, c, v}}:
      FBad{}

def field.view(x: List<&2, U32>) -> FLine:
  match x:
    case Nil{}:
      FEmpty{}
    case Con{c, t}:
      field.name(span(TName{}, Con{c, t}))

# The head
# --------

# what the head has said so far: the method and the target, the one
# length its Content-Length fields agree on, whether a Connection asked
# to close, how many Host fields came, and for an upgrade (RFC 6455
# 4.2.1): the last Sec-WebSocket-Key, whether an Upgrade named
# websocket and a Connection named upgrade, and whether a
# Sec-WebSocket-Version named anything but 13; and fr: whether the
# request line said HTTP/1.0, whether a Connection named keep-alive,
# and whether a Transfer-Encoding said chunked
type Head is Data:
  Head{meth: Eng.Meth, target: List<&2, U32>, len: Maybe<&2, U32>, close: Bool,
    hosts: Nat, key: List<&2, U32>, up: Bool, cu: Bool, vb: Bool, fr: Eng.Fx}

def meth.pick(get: Bool, head: Bool) -> Eng.Meth:
  match get head:
    case True{} _:
      Eng.MGet{}
    case False{} True{}:
      Eng.MHead{}
    case False{} False{}:
      Eng.MOther{}

# GET and HEAD are served; any other method is one this engine does not
# implement
def method(+m: Bytes()) -> Eng.Meth:
  meth.pick(eq(m, "GET"), eq(m, "HEAD"))

def head.new(m: List<&2, U32>, t: List<&2, U32>, v10: Bool) -> Head:
  Head{method(Bytes.from_list(m)), t, None{}, False{}, 0n, Nil{}, False{}, False{}, False{},
    Eng.Fx{v10, False{}, False{}}}

# whitespace at either end of a value is no part of it (RFC 9110 5.5)
def ows(k: Eng.Cls) -> Bool:
  match k:
    case Eng.KSp{}:
      True{}
    case Eng.KHt{}:
      True{}
    case _:
      False{}

def trim.lead.pick(w: Bool, c: U32, t: List<&2, U32>, r: List<&2, U32>) -> List<&2, U32>:
  match w:
    case True{}:
      r
    case False{}:
      Con{c, t}

def trim.lead(x: List<&2, U32>) -> List<&2, U32>:
  match x:
    case Nil{}:
      Nil{}
    case Con{+c, +t}:
      trim.lead.pick(ows(cls(c)), c, t, trim.lead(t))

def trim.end.pick(w: Bool, c: U32, r: List<&2, U32>) -> List<&2, U32>:
  match w r:
    case True{} Nil{}:
      Nil{}
    case _ _:
      Con{c, r}

def trim.end(x: List<&2, U32>) -> List<&2, U32>:
  match x:
    case Nil{}:
      Nil{}
    case Con{+c, t}:
      trim.end.pick(ows(cls(c)), c, trim.end(t))

def trim(x: List<&2, U32>) -> List<&2, U32>:
  trim.end(trim.lead(x))

# whether a list names w, case aside
def named(+w: Bytes(), ms: List<&2, List<&2, U32>>) -> Bool:
  match ms:
    case Nil{}:
      False{}
    case Con{m, r}:
      named(w, r) || eq(lows(Bytes.from_list(m)), w)

def head.len.at(ok: Bool, h: Head) -> Maybe<&2, Head>:
  match ok:
    case True{}:
      Some{h}
    case False{}:
      None{}

# a length: the first says it, and each after it must say the same
# (RFC 9112 6.3)
def head.len(h: Head, +n: U32) -> Maybe<&2, Head>:
  match h:
    case Head{m, t, l, cl, hs, k, u, c, v, f}:
      match l:
        case None{}:
          Some{Head{m, t, Some{n}, cl, hs, k, u, c, v, f}}
        case Some{+w}:
          head.len.at(U32.is_eq(n, w), Head{m, t, Some{w}, cl, hs, k, u, c, v, f})

# a Connection list: close, upgrade and keep-alive, each named anywhere
# in it
def head.conn(h: Head, a: Bool, b: Bool, ka: Bool) -> Head:
  match h:
    case Head{m, t, l, cl, hs, k, u, c, v, f}:
      match f:
        case Eng.Fx{v10, ka0, te}:
          Head{m, t, l, cl || a, hs, k, u, c || b, v, Eng.Fx{v10, ka0 || ka, te}}

def head.up(h: Head, w: Bool) -> Head:
  match h:
    case Head{m, t, l, cl, hs, k, u, c, v, f}:
      Head{m, t, l, cl, hs, k, u || w, c, v, f}

def head.key(h: Head, key: List<&2, U32>) -> Head:
  match h:
    case Head{m, t, l, cl, hs, k, u, c, v, f}:
      Head{m, t, l, cl, hs, key, u, c, v, f}

def head.ver(h: Head, ok: Bool) -> Head:
  match h:
    case Head{m, t, l, cl, hs, k, u, c, v, f}:
      Head{m, t, l, cl, hs, k, u, c, v || Bool.not(ok), f}

def head.host(h: Head) -> Head:
  match h:
    case Head{m, t, l, cl, hs, k, u, c, v, f}:
      Head{m, t, l, cl, 1n+hs, k, u, c, v, f}

# a Transfer-Encoding: the one coding this engine decodes is chunked,
# alone (RFC 9112 6.1, 7): named once, and exactly, in any case. A
# second Transfer-Encoding is a second coding, and chunked may be
# applied once; any other coding, or a list, is one it does not
# implement. Each is refused where its line ends.
def head.te.at(ok: Bool, m: Eng.Meth, t: List<&2, U32>, l: Maybe<&2, U32>, cl: Bool, hs: Nat,
  k: List<&2, U32>, u: Bool, c: Bool, v: Bool, v10: Bool, ka: Bool) -> Maybe<&2, Head>:
  match ok:
    case True{}:
      Some{Head{m, t, l, cl, hs, k, u, c, v, Eng.Fx{v10, ka, True{}}}}
    case False{}:
      None{}

def head.te(h: Head, chunked: Bool) -> Maybe<&2, Head>:
  match h:
    case Head{m, t, l, cl, hs, k, u, c, v, f}:
      match f:
        case Eng.Fx{v10, ka, te}:
          head.te.at(chunked && Bool.not(te), m, t, l, cl, hs, k, u, c, v, v10, ka)

# a whole field line, at its end: what the head says after it, or none
# when the line is refused
def field.done(h: Head, val: Val) -> Maybe<&2, Head>:
  match val:
    case VLen0{}:
      None{}
    case VLen{n, ws}:
      head.len(h, n)
    case VConn{+d, +c}:
      Some{head.conn(h, named("close", Con{c, d}), named("upgrade", Con{c, d}),
        named("keep-alive", Con{c, d}))}
    case VUp{d, c}:
      Some{head.up(h, named("websocket", Con{c, d}))}
    case VKey0{}:
      Some{head.key(h, Nil{})}
    case VKey{k}:
      Some{head.key(h, trim(k))}
    case VVer{v}:
      Some{head.ver(h, eq(Bytes.from_list(trim(v)), "13"))}
    case VTe0{}:
      None{}
    case VTe{t}:
      head.te(h, eq(lows(Bytes.from_list(t)), "chunked"))
    case VHost{}:
      Some{head.host(h)}
    case VSkip{}:
      Some{h}

# a request: its method, target and body; whether it asked to close --
# a Connection named close, or it is HTTP/1.0 and no Connection named
# keep-alive (RFC 9112 9.3); and whether it asked to become a WebSocket
# -- Upgrade named websocket, Connection named upgrade, a key came and
# no version but 13 -- with its key. An Upgrade in an HTTP/1.0 request
# is not one (RFC 9110 7.8: a server MUST ignore it).
def has(k: List<&2, U32>) -> Bool:
  match k:
    case Nil{}:
      False{}
    case Con{h, t}:
      True{}

def req(h: Head, body: List<&2, U32>) -> Eng.Req:
  match h:
    case Head{m, t, l, cl, hs, +k, u, c, v, f}:
      match f:
        case Eng.Fx{+v10, ka, te}:
          Eng.Req{m, Bytes.from_list(t), Bytes.from_list(body), cl || (v10 && Bool.not(ka)),
            Bool.not(v10) && (u && c && has(k) && Bool.not(v)), Bytes.from_list(k)}

# The chunked body
# -----------------
#
# RFC 9112 7.1, the grammar a chunked body is read by:
#
#   chunked-body    = *chunk last-chunk trailer-section CRLF
#   chunk           = chunk-size [ chunk-ext ] CRLF chunk-data CRLF
#   chunk-size      = 1*HEXDIG
#   last-chunk      = 1*("0") [ chunk-ext ] CRLF
#   chunk-ext       = *( BWS ";" BWS chunk-ext-name
#                        [ BWS "=" BWS chunk-ext-val ] )
#   chunk-ext-name  = token
#   chunk-ext-val   = token / quoted-string
#   trailer-section = *( field-line CRLF )
#
# and RFC 9110 5.6 for what a token, a quoted-string and a field line
# are made of. The grammar is regular, so it is written here as what it
# is: where in it a byte arrives (At, named after the rule it is in) and
# where that byte takes it (step, one row per case the grammar names;
# a byte no row names is refused). A chunk-size is read as hexadecimal
# as it comes, and it, the extensions, and the data are bounded
# together: every byte of a chunk line before its CR, and every byte of
# the chunk's data, is taken from the body's budget (len.cap() in all),
# and a byte that would leave less than the chunk still needs is refused
# where it stands -- a digit that makes the size more than is left, an
# extension that runs on past it. The extensions are read and dropped;
# the trailer's field lines are read by the head's grammar for a field
# line (a token, a colon, a value with no control, no bare LF) and
# dropped too. Every line ends in CR LF, and a bare LF is refused.

# a byte of a chunk's framing, as the grammar tells them apart: HEXDIG
# (with its value), any other tchar, whitespace, ";" "=" DQUOTE "\" ":",
# CR, LF, any other visible byte or obs-text, and a control
def u32.may(b: Bool, x: U32, r: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match b:
    case True{}:
      Some{x}
    case False{}:
      r

def hexdig.at(+c: U32, xs: List<&2, U32>, +i: U32) -> Maybe<&2, U32>:
  match xs:
    case Nil{}:
      None{}
    case Con{x, t}:
      u32.may(U32.is_eq(c, x), i, hexdig.at(c, t, (i + 1 : U32)))

# HEXDIG (RFC 5234): 0 to 9, and a to f in either case, with its value
def hexdig(+c: U32) -> Maybe<&2, U32>:
  hexdig.at(lower(c), Eng.bytes("0123456789abcdef"), 0)

def byte.is(+c: U32, s: String) -> Bool:
  mem(c, Eng.bytes(s))

def xk.hex(m: Maybe<&2, U32>) -> Eng.XK:
  match m:
    case Some{d}:
      Eng.XHex{d}
    case None{}:
      Eng.XTok{}

def xk.vc(semi: Bool, eq: Bool, quote: Bool, back: Bool) -> Eng.XK:
  match semi eq quote back:
    case True{} _ _ _:
      Eng.XSemi{}
    case False{} True{} _ _:
      Eng.XEq{}
    case False{} False{} True{} _:
      Eng.XQuote{}
    case False{} False{} False{} True{}:
      Eng.XBack{}
    case False{} False{} False{} False{}:
      Eng.XVis{}

def xk.of(k: Eng.Cls, +c: U32) -> Eng.XK:
  match k:
    case Eng.KSp{}:
      Eng.XWs{}
    case Eng.KHt{}:
      Eng.XWs{}
    case Eng.KCr{}:
      Eng.XCr{}
    case Eng.KLf{}:
      Eng.XLf{}
    case Eng.KCo{}:
      Eng.XColon{}
    case Eng.KCm{}:
      Eng.XVis{}
    case Eng.KDg{}:
      xk.hex(hexdig(c))
    case Eng.KTk{}:
      xk.hex(hexdig(c))
    case Eng.KVc{}:
      xk.vc(byte.is(c, ";"), byte.is(c, "="), byte.is(c, "\""), byte.is(c, "\\"))
    case Eng.KCt{}:
      Eng.XCtl{}

# where in the grammar a byte arrives
#   ASize0 / ASize    chunk-size, before its first HEXDIG / in it
#   ABws              BWS before a ";"
#   AName0 / AName    after ";" and BWS / in a chunk-ext-name
#   ANameWs           BWS after a name, before "=" or ";"
#   AVal0             after "=" and BWS, before chunk-ext-val
#   AToken            in a token chunk-ext-val
#   AQuoted / AEscape in a quoted-string / after its "\" (quoted-pair)
#   AClosed           after a quoted-string's closing DQUOTE
#   ALf               the LF that ends a chunk line
#   ADataCr / ADataLf the CRLF after chunk-data
#   ATrail            the start of a trailer field line, or the last CRLF
#   ATName / ATVal    a trailer field-name / field-value
#   ATLf / AEnd       the LF of a trailer line / of the body's last CRLF
type At is Data:
  ASize0{}
  ASize{}
  ABws{}
  AName0{}
  AName{}
  ANameWs{}
  AVal0{}
  AToken{}
  AQuoted{}
  AEscape{}
  AClosed{}
  ALf{}
  ADataCr{}
  ADataLf{}
  ATrail{}
  ATName{}
  ATVal{}
  ATLf{}
  AEnd{}

# where a byte takes the body: refused; to a place in the grammar, and
# whether the byte is paid from the budget; one more HEXDIG; the end of
# a chunk line (its data next, or the trailer after the last chunk); the
# body's end
type Go is Data:
  GBad{}
  GTo{at: At, paid: Bool}
  GDigit{d: U32}
  GLine{}
  GDone{}

def chunk.step(at: At, x: Eng.XK) -> Go:
  match at x:
    # chunk-size = 1*HEXDIG
    case ASize0{} Eng.XHex{d}:
      GDigit{d}
    case ASize0{} _:
      GBad{}
    # more HEXDIG; or chunk-ext's ";" or its BWS; or the CR
    case ASize{} Eng.XHex{d}:
      GDigit{d}
    case ASize{} Eng.XSemi{}:
      GTo{AName0{}, True{}}
    case ASize{} Eng.XWs{}:
      GTo{ABws{}, True{}}
    case ASize{} Eng.XCr{}:
      GTo{ALf{}, False{}}
    case ASize{} _:
      GBad{}
    # BWS ";"
    case ABws{} Eng.XWs{}:
      GTo{ABws{}, True{}}
    case ABws{} Eng.XSemi{}:
      GTo{AName0{}, True{}}
    case ABws{} _:
      GBad{}
    # ";" BWS chunk-ext-name
    case AName0{} Eng.XWs{}:
      GTo{AName0{}, True{}}
    case AName0{} Eng.XHex{d}:
      GTo{AName{}, True{}}
    case AName0{} Eng.XTok{}:
      GTo{AName{}, True{}}
    case AName0{} _:
      GBad{}
    # a token; then BWS "=", "=", the next ";", or the CR
    case AName{} Eng.XHex{d}:
      GTo{AName{}, True{}}
    case AName{} Eng.XTok{}:
      GTo{AName{}, True{}}
    case AName{} Eng.XWs{}:
      GTo{ANameWs{}, True{}}
    case AName{} Eng.XEq{}:
      GTo{AVal0{}, True{}}
    case AName{} Eng.XSemi{}:
      GTo{AName0{}, True{}}
    case AName{} Eng.XCr{}:
      GTo{ALf{}, False{}}
    case AName{} _:
      GBad{}
    # BWS, then "=" or the next ";"
    case ANameWs{} Eng.XWs{}:
      GTo{ANameWs{}, True{}}
    case ANameWs{} Eng.XEq{}:
      GTo{AVal0{}, True{}}
    case ANameWs{} Eng.XSemi{}:
      GTo{AName0{}, True{}}
    case ANameWs{} _:
      GBad{}
    # "=" BWS, then a token or a quoted-string
    case AVal0{} Eng.XWs{}:
      GTo{AVal0{}, True{}}
    case AVal0{} Eng.XHex{d}:
      GTo{AToken{}, True{}}
    case AVal0{} Eng.XTok{}:
      GTo{AToken{}, True{}}
    case AVal0{} Eng.XQuote{}:
      GTo{AQuoted{}, True{}}
    case AVal0{} _:
      GBad{}
    # a token value; then the next ";", BWS before one, or the CR
    case AToken{} Eng.XHex{d}:
      GTo{AToken{}, True{}}
    case AToken{} Eng.XTok{}:
      GTo{AToken{}, True{}}
    case AToken{} Eng.XSemi{}:
      GTo{AName0{}, True{}}
    case AToken{} Eng.XWs{}:
      GTo{ABws{}, True{}}
    case AToken{} Eng.XCr{}:
      GTo{ALf{}, False{}}
    case AToken{} _:
      GBad{}
    # qdtext = HTAB / SP / %x21 / %x23-5B / %x5D-7E / obs-text; a "\"
    # starts a quoted-pair; DQUOTE ends it
    case AQuoted{} Eng.XBack{}:
      GTo{AEscape{}, True{}}
    case AQuoted{} Eng.XQuote{}:
      GTo{AClosed{}, True{}}
    case AQuoted{} Eng.XCr{}:
      GBad{}
    case AQuoted{} Eng.XLf{}:
      GBad{}
    case AQuoted{} Eng.XCtl{}:
      GBad{}
    case AQuoted{} _:
      GTo{AQuoted{}, True{}}
    # quoted-pair = "\" ( HTAB / SP / VCHAR / obs-text )
    case AEscape{} Eng.XCr{}:
      GBad{}
    case AEscape{} Eng.XLf{}:
      GBad{}
    case AEscape{} Eng.XCtl{}:
      GBad{}
    case AEscape{} _:
      GTo{AQuoted{}, True{}}
    # after the value: the next ";", BWS before one, or the CR
    case AClosed{} Eng.XSemi{}:
      GTo{AName0{}, True{}}
    case AClosed{} Eng.XWs{}:
      GTo{ABws{}, True{}}
    case AClosed{} Eng.XCr{}:
      GTo{ALf{}, False{}}
    case AClosed{} _:
      GBad{}
    # CRLF, nothing else
    case ALf{} Eng.XLf{}:
      GLine{}
    case ALf{} _:
      GBad{}
    case ADataCr{} Eng.XCr{}:
      GTo{ADataLf{}, False{}}
    case ADataCr{} _:
      GBad{}
    case ADataLf{} Eng.XLf{}:
      GTo{ASize0{}, False{}}
    case ADataLf{} _:
      GBad{}
    # trailer-section: a field line starts with a token byte; the CR of
    # an empty line ends it
    case ATrail{} Eng.XCr{}:
      GTo{AEnd{}, False{}}
    case ATrail{} Eng.XHex{d}:
      GTo{ATName{}, False{}}
    case ATrail{} Eng.XTok{}:
      GTo{ATName{}, False{}}
    case ATrail{} _:
      GBad{}
    # field-name = token, then ":"
    case ATName{} Eng.XHex{d}:
      GTo{ATName{}, False{}}
    case ATName{} Eng.XTok{}:
      GTo{ATName{}, False{}}
    case ATName{} Eng.XColon{}:
      GTo{ATVal{}, False{}}
    case ATName{} _:
      GBad{}
    # a value: anything but a control or a line end, up to its CR
    case ATVal{} Eng.XCr{}:
      GTo{ATLf{}, False{}}
    case ATVal{} Eng.XLf{}:
      GBad{}
    case ATVal{} Eng.XCtl{}:
      GBad{}
    case ATVal{} _:
      GTo{ATVal{}, False{}}
    case ATLf{} Eng.XLf{}:
      GTo{ATrail{}, False{}}
    case ATLf{} _:
      GBad{}
    case AEnd{} Eng.XLf{}:
      GDone{}
    case AEnd{} _:
      GBad{}

# The walk
# --------

# where the input is: in a request line (or an empty line before one);
# at the CR of such an empty line; in a field line of a head that has
# said h; at the CR that ends a line of the head, or the head's empty
# line; in a body, with what it still needs after the next byte; in a
# chunked body's framing, at a place in its grammar, with the chunk's
# size, the body so far and the budget left; in a chunk's data, with
# what it still needs after the next byte; after an upgrade; or refused
type Mode is Data:
  MReq{cur: List<&2, U32>}
  MBlank{}
  MField{h: Head, cur: List<&2, U32>}
  MEol{h: Head}
  MEoh{h: Head}
  MBody{h: Head, more: Nat, got: List<&2, U32>}
  MChunk{h: Head, at: At, n: U32, got: List<&2, U32>, left: U32}
  MData{h: Head, more: Nat, got: List<&2, U32>, left: U32}
  MUp{got: List<&2, U32>}
  MBad{}

# the walk: where it is, the requests done (newest first), and the
# bytes since the last one
type W is Data:
  W{mode: Mode, out: List<&2, Eng.Req>, since: List<&2, U32>}

def emit.mode(ws: Bool) -> Mode:
  match ws:
    case True{}:
      MUp{Nil{}}
    case False{}:
      MReq{Nil{}}

def emit.go(r: Eng.Req, out: List<&2, Eng.Req>) -> W:
  match r:
    case Eng.Req{m, p, b, cl, +ws, k}:
      W{emit.mode(ws), Con{Eng.Req{m, p, b, cl, ws, k}, out}, Nil{}}

def emit(h: Head, body: List<&2, U32>, out: List<&2, Eng.Req>) -> W:
  emit.go(req(h, body), out)

# the head's end. An HTTP/1.1 request carries exactly one Host (RFC
# 9112 3.2); an HTTP/1.0 one at most one. Then its body (RFC 9112 6.3):
# a Transfer-Encoding with a Content-Length is refused, since two
# framings are how a request is smuggled, and so is a Transfer-Encoding
# in HTTP/1.0 (RFC 9112 6.1: faulty framing); chunked is a chunked body;
# a length is a body of that length; neither is no body.
def head.one(hs: Nat) -> Bool:
  match hs:
    case 0n:
      False{}
    case 1n+p:
      match p:
        case 0n:
          True{}
        case 1n+q:
          False{}

def head.most(hs: Nat) -> Bool:
  match hs:
    case 0n:
      True{}
    case 1n+p:
      match p:
        case 0n:
          True{}
        case 1n+q:
          False{}

def hosts.ok(v10: Bool, hs: Nat) -> Bool:
  match v10:
    case True{}:
      head.most(hs)
    case False{}:
      head.one(hs)

type Body is Data:
  BNone{}
  BLen{n: U32}
  BChunked{}
  BBad{}

def body.of(te: Bool, v10: Bool, l: Maybe<&2, U32>) -> Body:
  match te v10 l:
    case False{} _ None{}:
      BNone{}
    case False{} _ Some{n}:
      BLen{n}
    case True{} True{} _:
      BBad{}
    case True{} False{} None{}:
      BChunked{}
    case True{} False{} Some{n}:
      BBad{}

def head.body(z: Bool, +n: U32, h: Head, out: List<&2, Eng.Req>, s: List<&2, U32>) -> W:
  match z:
    case True{}:
      emit(h, Nil{}, out)
    case False{}:
      W{MBody{h, Nat.sub(U32.to_nat(n), 1n), Nil{}}, out, s}

def head.at(ok: Bool, b: Body, h: Head, out: List<&2, Eng.Req>, s: List<&2, U32>) -> W:
  match ok b:
    case False{} _:
      W{MBad{}, out, s}
    case True{} BBad{}:
      W{MBad{}, out, s}
    case True{} BNone{}:
      emit(h, Nil{}, out)
    case True{} BLen{+n}:
      head.body(U32.is_zero(n), n, h, out, s)
    case True{} BChunked{}:
      W{MChunk{h, ASize0{}, 0, Nil{}, len.cap()}, out, s}

def head.done(h: Head, out: List<&2, Eng.Req>, s: List<&2, U32>) -> W:
  match h:
    case Head{m, t, +l, cl, +hs, k, u, c, v, f}:
      match f:
        case Eng.Fx{+v10, ka, +te}:
          head.at(hosts.ok(v10, hs), body.of(te, v10, l),
            Head{m, t, l, cl, hs, k, u, c, v, Eng.Fx{v10, ka, te}}, out, s)

# a chunk's framing, one byte: where the grammar takes it (step), and
# the budget. A paid byte needs the budget to hold it and the chunk's
# data still; the LF of a chunk line takes the chunk's size from it.
def chunk.paid(over: Bool, h: Head, at: At, n: U32, got: List<&2, U32>, left: U32,
  out: List<&2, Eng.Req>, s: List<&2, U32>) -> W:
  match over:
    case True{}:
      W{MBad{}, out, s}
    case False{}:
      W{MChunk{h, at, n, got, (left - 1 : U32)}, out, s}

def chunk.to(paid: Bool, h: Head, at: At, +n: U32, got: List<&2, U32>, +left: U32,
  out: List<&2, Eng.Req>, s: List<&2, U32>) -> W:
  match paid:
    case True{}:
      chunk.paid(U32.is_le(left, n), h, at, n, got, left, out, s)
    case False{}:
      W{MChunk{h, at, n, got, left}, out, s}

def chunk.line(z: Bool, h: Head, +n: U32, got: List<&2, U32>, +left: U32,
  out: List<&2, Eng.Req>, s: List<&2, U32>) -> W:
  match z:
    case True{}:
      W{MChunk{h, ATrail{}, 0, got, left}, out, s}
    case False{}:
      W{MData{h, Nat.sub(U32.to_nat(n), 1n), got, (left - n : U32)}, out, s}

def chunk.go(g: Go, h: Head, +n: U32, got: List<&2, U32>, +left: U32, out: List<&2, Eng.Req>,
  s: List<&2, U32>) -> W:
  match g:
    case GBad{}:
      W{MBad{}, out, s}
    case GTo{at, paid}:
      chunk.to(paid, h, at, n, got, left, out, s)
    case GDigit{+d}:
      +n2 = (n * 16 + d : U32)
      chunk.paid(U32.is_le(left, n2), h, ASize{}, n2, got, left, out, s)
    case GLine{}:
      chunk.line(U32.is_zero(n), h, n, got, left, out, s)
    case GDone{}:
      emit(h, got, out)

# a byte of a chunk's data: the last one leaves the chunk's CRLF to come
def data.byte(more: Nat, c: U32, h: Head, got: List<&2, U32>, left: U32,
  out: List<&2, Eng.Req>, s: List<&2, U32>) -> W:
  match more:
    case 0n:
      W{MChunk{h, ADataCr{}, 0, snoc(got, c), left}, out, s}
    case 1n+q:
      W{MData{h, q, snoc(got, c), left}, out, s}

# a request line at its CR: an empty one is skipped (RFC 9112 2.2), and
# a whole one is HTTP/1.1 or HTTP/1.0
def req.ok(v11: Bool, v10: Bool, m: List<&2, U32>, t: List<&2, U32>, out: List<&2, Eng.Req>,
  s: List<&2, U32>) -> W:
  match v11 v10:
    case True{} _:
      W{MEol{head.new(m, t, False{})}, out, s}
    case False{} True{}:
      W{MEol{head.new(m, t, True{})}, out, s}
    case False{} False{}:
      W{MBad{}, out, s}

def req.cr(v: RLine, out: List<&2, Eng.Req>, s: List<&2, U32>) -> W:
  match v:
    case RNone{}:
      W{MBlank{}, out, s}
    case RVer{m, t, +ver}:
      req.ok(eq(Bytes.from_list(ver), "HTTP/1.1"), eq(Bytes.from_list(ver), "HTTP/1.0"), m, t, out, s)
    case _:
      W{MBad{}, out, s}

def field.next(mh: Maybe<&2, Head>, out: List<&2, Eng.Req>, s: List<&2, U32>) -> W:
  match mh:
    case Some{h}:
      W{MEol{h}, out, s}
    case None{}:
      W{MBad{}, out, s}

# a field line at its CR: an empty one ends the head
def field.cr(h: Head, v: FLine, out: List<&2, Eng.Req>, s: List<&2, U32>) -> W:
  match v:
    case FEmpty{}:
      W{MEoh{h}, out, s}
    case FVal{val}:
      field.next(field.done(h, val), out, s)
    case _:
      W{MBad{}, out, s}

# a line's bytes are gathered until its CR; a LF anywhere else is a bare
# LF, and after a CR nothing but a LF may come (RFC 9112 2.2)
def req.byte(k: Eng.Cls, c: U32, cur: List<&2, U32>, out: List<&2, Eng.Req>, s: List<&2, U32>) -> W:
  match k:
    case Eng.KCr{}:
      req.cr(req.view(cur), out, s)
    case Eng.KLf{}:
      W{MBad{}, out, s}
    case _:
      W{MReq{snoc(cur, c)}, out, s}

def field.byte(k: Eng.Cls, c: U32, h: Head, cur: List<&2, U32>, out: List<&2, Eng.Req>,
  s: List<&2, U32>) -> W:
  match k:
    case Eng.KCr{}:
      field.cr(h, field.view(cur), out, s)
    case Eng.KLf{}:
      W{MBad{}, out, s}
    case _:
      W{MField{h, snoc(cur, c)}, out, s}

def blank.byte(k: Eng.Cls, out: List<&2, Eng.Req>, s: List<&2, U32>) -> W:
  match k:
    case Eng.KLf{}:
      W{MReq{Nil{}}, out, s}
    case _:
      W{MBad{}, out, s}

def eol.byte(k: Eng.Cls, h: Head, out: List<&2, Eng.Req>, s: List<&2, U32>) -> W:
  match k:
    case Eng.KLf{}:
      W{MField{h, Nil{}}, out, s}
    case _:
      W{MBad{}, out, s}

def eoh.byte(k: Eng.Cls, h: Head, out: List<&2, Eng.Req>, s: List<&2, U32>) -> W:
  match k:
    case Eng.KLf{}:
      head.done(h, out, s)
    case _:
      W{MBad{}, out, s}

# a body byte: the last one completes the request
def body.byte(more: Nat, c: U32, h: Head, got: List<&2, U32>, out: List<&2, Eng.Req>,
  s: List<&2, U32>) -> W:
  match more:
    case 0n:
      emit(h, snoc(got, c), out)
    case 1n+q:
      W{MBody{h, q, snoc(got, c)}, out, s}

def next.at(mode: Mode, k: Eng.Cls, c: U32, out: List<&2, Eng.Req>, s: List<&2, U32>) -> W:
  match mode:
    case MReq{cur}:
      req.byte(k, c, cur, out, s)
    case MBlank{}:
      blank.byte(k, out, s)
    case MField{h, cur}:
      field.byte(k, c, h, cur, out, s)
    case MEol{h}:
      eol.byte(k, h, out, s)
    case MEoh{h}:
      eoh.byte(k, h, out, s)
    case MBody{h, more, got}:
      body.byte(more, c, h, got, out, s)
    case MChunk{h, at, n, got, left}:
      chunk.go(chunk.step(at, xk.of(k, c)), h, n, got, left, out, s)
    case MData{h, more, got, left}:
      data.byte(more, c, h, got, left, out, s)
    case MUp{got}:
      W{MUp{snoc(got, c)}, out, s}
    case MBad{}:
      W{MBad{}, out, s}

def next(w: W, +c: U32) -> W:
  match w:
    case W{mode, out, since}:
      next.at(mode, cls(c), c, out, snoc(since, c))

def walk(bs: List<&2, U32>, w: W) -> W:
  match bs:
    case Nil{}:
      w
    case Con{c, t}:
      walk(t, next(w, c))

# at the input's end, a line it stopped inside is read as far as it goes
def req.end(v: RLine, s: List<&2, U32>) -> End:
  match v:
    case RBad{}:
      Refused{}
    case _:
      Open{s}

def field.end(v: FLine, s: List<&2, U32>) -> End:
  match v:
    case FBad{}:
      Refused{}
    case _:
      Open{s}

def finish.end(mode: Mode, s: List<&2, U32>) -> End:
  match mode:
    case MReq{cur}:
      req.end(req.view(cur), s)
    case MField{h, cur}:
      field.end(field.view(cur), s)
    case MUp{got}:
      Upgraded{Bytes.from_list(got)}
    case MBad{}:
      Refused{}
    case _:
      Open{s}

def finish(w: W) -> Frames:
  match w:
    case W{mode, out, since}:
      Frames{List.reverse(&2, Eng.Req, out), finish.end(mode, since)}

# a whole input, framed
def frame(bs: List<&2, U32>) -> Frames:
  finish(walk(bs, W{MReq{Nil{}}, Nil{}, Nil{}}))
