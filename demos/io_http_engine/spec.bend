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
