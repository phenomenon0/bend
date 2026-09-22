# The reference the reader is held to: the head grammar of RFC 9110 5.6
# and RFC 9112 2-6, written for whoever checks it rather than for the
# clock. Every def here is the obvious one -- a class is membership in
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

# The framer
# ==========
#
# What the reader is held to as a whole. frame() takes every byte a
# peer sent, however TCP cut it, and says what RFC 9112 makes of it --
# for the part of HTTP/1.1 this engine accepts: the requests it holds,
# oldest first, and how it ends. It never steps a byte through a state
# machine of the engine's shape. A line is gathered until its CR LF and
# only then read, whole: a request line split at its spaces into a
# method, a target and a version (RFC 9112 3), a field line split at its
# colon into a name and a value (RFC 9110 5), the value read by what the
# name is. A head ends at its empty line and is judged then (exactly
# one Host, RFC 9112 3.2; its length, RFC 9112 6.3), and a body is
# counted off by that length. A line the input stops inside is read the
# same way, as far as it goes.

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

def req.target(m: List<&2, U32>, sp: Span) -> RLine:
  match sp:
    case Span{t, SEnd{}}:
      RTarget{m, t}
    case Span{Nil{}, SAt{Eng.KSp{}, c, rest}}:
      RBad{}
    case Span{Con{h, r}, SAt{Eng.KSp{}, c, rest}}:
      req.ver(m, Con{h, r}, span(TVer{}, rest))
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
#   VHost / VSkip Host, or any other field: the value is only checked
type Val is Data:
  VLen0{}
  VLen{n: U32, ws: Bool}
  VConn{done: List<&2, List<&2, U32>>, cur: List<&2, U32>}
  VUp{done: List<&2, List<&2, U32>>, cur: List<&2, U32>}
  VKey0{}
  VKey{k: List<&2, U32>}
  VVer{v: List<&2, U32>}
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

def skip.view(val: Val, sp: Span) -> FLine:
  match sp:
    case Span{v, SEnd{}}:
      FVal{val}
    case Span{v, SAt{k, c, rest}}:
      FBad{}

# a name's field: Transfer-Encoding is refused whatever it says, since
# this engine frames by length alone (RFC 9112 6.1 lets a server refuse
# a coding it does not implement, and two framings are how requests
# are smuggled)
def field.of(f: Eng.Fld, v: List<&2, U32>) -> FLine:
  match f:
    case Eng.FTe{}:
      FBad{}
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
# Sec-WebSocket-Version named anything but 13
type Head is Data:
  Head{meth: Eng.Meth, target: List<&2, U32>, len: Maybe<&2, U32>, close: Bool,
    hosts: Nat, key: List<&2, U32>, up: Bool, cu: Bool, vb: Bool}

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

def head.new(m: List<&2, U32>, t: List<&2, U32>) -> Head:
  Head{method(Bytes.from_list(m)), t, None{}, False{}, 0n, Nil{}, False{}, False{}, False{}}

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
    case Head{m, t, l, cl, hs, k, u, c, v}:
      match l:
        case None{}:
          Some{Head{m, t, Some{n}, cl, hs, k, u, c, v}}
        case Some{+w}:
          head.len.at(U32.is_eq(n, w), Head{m, t, Some{w}, cl, hs, k, u, c, v})

def head.conn(h: Head, a: Bool, b: Bool) -> Head:
  match h:
    case Head{m, t, l, cl, hs, k, u, c, v}:
      Head{m, t, l, cl || a, hs, k, u, c || b, v}

def head.up(h: Head, w: Bool) -> Head:
  match h:
    case Head{m, t, l, cl, hs, k, u, c, v}:
      Head{m, t, l, cl, hs, k, u || w, c, v}

def head.key(h: Head, key: List<&2, U32>) -> Head:
  match h:
    case Head{m, t, l, cl, hs, k, u, c, v}:
      Head{m, t, l, cl, hs, key, u, c, v}

def head.ver(h: Head, ok: Bool) -> Head:
  match h:
    case Head{m, t, l, cl, hs, k, u, c, v}:
      Head{m, t, l, cl, hs, k, u, c, v || Bool.not(ok)}

def head.host(h: Head) -> Head:
  match h:
    case Head{m, t, l, cl, hs, k, u, c, v}:
      Head{m, t, l, cl, 1n+hs, k, u, c, v}

# a whole field line, at its end: what the head says after it, or none
# when the line is refused
def field.done(h: Head, val: Val) -> Maybe<&2, Head>:
  match val:
    case VLen0{}:
      None{}
    case VLen{n, ws}:
      head.len(h, n)
    case VConn{+d, +c}:
      Some{head.conn(h, named("close", Con{c, d}), named("upgrade", Con{c, d}))}
    case VUp{d, c}:
      Some{head.up(h, named("websocket", Con{c, d}))}
    case VKey0{}:
      Some{head.key(h, Nil{})}
    case VKey{k}:
      Some{head.key(h, trim(k))}
    case VVer{v}:
      Some{head.ver(h, eq(Bytes.from_list(trim(v)), "13"))}
    case VHost{}:
      Some{head.host(h)}
    case VSkip{}:
      Some{h}

# a request: its method, target and body, whether it asked to close, and
# whether it asked to become a WebSocket -- Upgrade named websocket,
# Connection named upgrade, a key came and no version but 13 -- with
# its key
def has(k: List<&2, U32>) -> Bool:
  match k:
    case Nil{}:
      False{}
    case Con{h, t}:
      True{}

def req(h: Head, body: List<&2, U32>) -> Eng.Req:
  match h:
    case Head{m, t, l, cl, hs, +k, u, c, v}:
      Eng.Req{m, Bytes.from_list(t), Bytes.from_list(body), cl,
        u && c && has(k) && Bool.not(v), Bytes.from_list(k)}

# The walk
# --------

# where the input is: in a request line (or an empty line before one);
# at the CR of such an empty line; in a field line of a head that has
# said h; at the CR that ends a line of the head, or the head's empty
# line; in a body, with what it still needs after the next byte; after
# an upgrade; or refused
type Mode is Data:
  MReq{cur: List<&2, U32>}
  MBlank{}
  MField{h: Head, cur: List<&2, U32>}
  MEol{h: Head}
  MEoh{h: Head}
  MBody{h: Head, more: Nat, got: List<&2, U32>}
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

# the head's end: exactly one Host (RFC 9112 3.2), then no body, or one
# of the length it gave (RFC 9112 6.3)
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

def head.body(z: Bool, +n: U32, h: Head, out: List<&2, Eng.Req>, s: List<&2, U32>) -> W:
  match z:
    case True{}:
      emit(h, Nil{}, out)
    case False{}:
      W{MBody{h, Nat.sub(U32.to_nat(n), 1n), Nil{}}, out, s}

def head.at(one: Bool, l: Maybe<&2, U32>, h: Head, out: List<&2, Eng.Req>, s: List<&2, U32>) -> W:
  match one l:
    case False{} _:
      W{MBad{}, out, s}
    case True{} None{}:
      emit(h, Nil{}, out)
    case True{} Some{+n}:
      head.body(U32.is_zero(n), n, h, out, s)

def head.done(h: Head, out: List<&2, Eng.Req>, s: List<&2, U32>) -> W:
  match h:
    case Head{m, t, +l, cl, +hs, k, u, c, v}:
      head.at(head.one(hs), l, Head{m, t, l, cl, hs, k, u, c, v}, out, s)

def req.ok(ok: Bool, m: List<&2, U32>, t: List<&2, U32>, out: List<&2, Eng.Req>,
  s: List<&2, U32>) -> W:
  match ok:
    case True{}:
      W{MEol{head.new(m, t)}, out, s}
    case False{}:
      W{MBad{}, out, s}

# a request line at its CR: an empty one is skipped (RFC 9112 2.2), and
# a whole one is HTTP/1.1
def req.cr(v: RLine, out: List<&2, Eng.Req>, s: List<&2, U32>) -> W:
  match v:
    case RNone{}:
      W{MBlank{}, out, s}
    case RVer{m, t, ver}:
      req.ok(eq(Bytes.from_list(ver), "HTTP/1.1"), m, t, out, s)
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
