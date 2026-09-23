# The reference the response reader is held to: RFC 9112's response
# framing -- the status line (4), field lines (5), the body's length
# (6.3) and the chunked coding (7.1) -- written for whoever checks it
# rather than for the clock. A line is gathered until its CR and only
# then read, whole: split at its spaces into a version, a status code
# and a reason, or at its colon into a name and a value read by what the
# name is. A head is judged at its blank line, and its body is counted
# off, decoded, or read to the close, as 6.3 says, in 6.3's order.
#
# It shares with the reader what is not framing: the ten classes a byte
# falls in (LAWS.bend pins them, and lowercasing, to the RFC's sets on
# all 256 bytes: cls_rfc, lower_rfc), the table of the chunked coding's
# grammar (pinned by vectors), and the types of what is read (Ask, Head,
# Resp, Look). Everything else is written once, here, the obvious way,
# and LAWS.bend's resp_sim says the reader agrees with it on every input.
#
# Why here and not in demos/io_http_engine/spec.bend: that spec imports
# the server, and the client (wire/client.bend, the proxy after it) must
# not; responses are the client's half of HTTP/1, and bend-wire is where
# the client lives.
import Base
import ../reader.bend as Wr
import ./resp.bend as R

# The RFC's sets
# ==============
#
# RFC 5234 and RFC 9110 5.6.2, as membership in the sets they name:
# what LAWS.bend holds the shared classes to.

def mem(+c: U32, xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, t}:
      U32.is_eq(c, x) || mem(c, t)

def all.go(n: Nat, +c: U32) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{c, all.go(p, (c + 1 : U32))}

# every byte, 0 to 255
def all() -> List<&2, U32>:
  all.go(256n, 0)

def digits() -> List<&2, U32>:
  Wr.bytes("0123456789")

def upper() -> List<&2, U32>:
  Wr.bytes("ABCDEFGHIJKLMNOPQRSTUVWXYZ")

def lowers() -> List<&2, U32>:
  Wr.bytes("abcdefghijklmnopqrstuvwxyz")

# tchar: ALPHA, DIGIT, and these fifteen
def tchar(+c: U32) -> Bool:
  mem(c, Wr.bytes("!#$%&'*+-.^_`|~")) || mem(c, digits()) || mem(c, upper()) || mem(c, lowers())

# CTL: 0 to 31, and 127
def ctl(+c: U32) -> Bool:
  U32.is_lt(c, 32) || U32.is_eq(c, 127)

def cls.pick(b: Bool, k: R.Cls, rest: R.Cls) -> R.Cls:
  match b:
    case True{}:
      k
    case False{}:
      rest

# SP, HTAB, CR, LF, ":", ",", a DIGIT, any other tchar, any other CTL,
# and the rest (the visible bytes that are not tchar, and obs-text)
def cls.rfc(+c: U32) -> R.Cls:
  cls.pick(U32.is_eq(c, 32), R.KSp{},
  cls.pick(U32.is_eq(c, 9), R.KHt{},
  cls.pick(U32.is_eq(c, 13), R.KCr{},
  cls.pick(U32.is_eq(c, 10), R.KLf{},
  cls.pick(U32.is_eq(c, 58), R.KCo{},
  cls.pick(U32.is_eq(c, 44), R.KCm{},
  cls.pick(mem(c, digits()), R.KDg{},
  cls.pick(tchar(c), R.KTk{},
  cls.pick(ctl(c), R.KCt{}, R.KVc{})))))))))

def u32.pick(b: Bool, x: U32, y: U32) -> U32:
  match b:
    case True{}:
      x
    case False{}:
      y

def lower.find(+c: U32, us: List<&2, U32>, ls: List<&2, U32>) -> U32:
  match us ls:
    case Con{u, ut} Con{l, lt}:
      u32.pick(U32.is_eq(c, u), l, lower.find(c, ut, lt))
    case _ _:
      c

# an uppercase letter's lowercase, and every other byte as it is
def lower.rfc(+c: U32) -> U32:
  lower.find(c, upper(), lowers())

def cls.ref(xs: List<&2, U32>) -> List<&2, R.Cls>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{c, t}:
      Con{cls.rfc(c), cls.ref(t)}

def cls.eng(xs: List<&2, U32>) -> List<&2, R.Cls>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{c, t}:
      Con{R.cls(c), cls.eng(t)}

def lower.ref(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{c, t}:
      Con{lower.rfc(c), lower.ref(t)}

def lower.eng(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{c, t}:
      Con{R.lower(c), lower.eng(t)}

# Byte lists
# ==========

def snoc(xs: List<&2, U32>, x: U32) -> List<&2, U32>:
  List.append(&2, U32, xs, [x])

def cnt(xs: List<&2, U32>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, t}:
      1n+cnt(t)

# two byte lists are equal when they are the same bytes, in order
def leq(a: List<&2, U32>, b: List<&2, U32>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{y, u}:
      False{}
    case Con{x, t} Nil{}:
      False{}
    case Con{x, t} Con{y, u}:
      U32.is_eq(x, y) && leq(t, u)

# a name, a coding or a list member, lowercased byte by byte
def lows(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{R.lower(x), lows(t)}

# Tokens
# ======

# the runs a line is split into, and the classes of byte each may hold:
# a version is read whole at its space and compared, so it may hold
# anything but the space that ends it (and the line's end); a status
# code is digits; a field name is tchar (RFC 9110 5.6.2); OWS is spaces
# and tabs (5.6.3); a value -- and a reason phrase, which is made of the
# same bytes (RFC 9112 4) -- is anything but CR, LF and the other
# controls, spaces and tabs included (RFC 9110 5.5)
type Tok is Data:
  TVer{}
  TDig{}
  TName{}
  TOws{}
  TVal{}

def allows(t: Tok, k: R.Cls) -> Bool:
  match t k:
    case TVer{} R.KSp{}:
      False{}
    case TVer{} R.KCr{}:
      False{}
    case TVer{} R.KLf{}:
      False{}
    case TVer{} _:
      True{}
    case TDig{} R.KDg{}:
      True{}
    case TDig{} _:
      False{}
    case TName{} R.KTk{}:
      True{}
    case TName{} R.KDg{}:
      True{}
    case TName{} _:
      False{}
    case TOws{} R.KSp{}:
      True{}
    case TOws{} R.KHt{}:
      True{}
    case TOws{} _:
      False{}
    case TVal{} R.KCr{}:
      False{}
    case TVal{} R.KLf{}:
      False{}
    case TVal{} R.KCt{}:
      False{}
    case TVal{} _:
      True{}

# the longest run of bytes a token may hold, from the first, and what
# stopped it: the end of the line, or a byte (its class, itself, and
# what follows it)
type Stop is Data:
  SEnd{}
  SAt{k: R.Cls, c: U32, rest: List<&2, U32>}

type Span is Data:
  Span{run: List<&2, U32>, stop: Stop}

def span.push(c: U32, sp: Span) -> Span:
  match sp:
    case Span{r, s}:
      Span{Con{c, r}, s}

def span.pick(ok: Bool, k: R.Cls, c: U32, rest: List<&2, U32>, more: Span) -> Span:
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
      +k = R.cls(c)
      span.pick(allows(t, k), k, c, rest, span(t, rest))

# The status line
# ===============
#
# status-line = HTTP-version SP status-code SP [ reason-phrase ]
#
# (RFC 9112 4), the last SP and the reason optional here: a line that
# ends after the code is taken. The version is HTTP/1.1 or HTTP/1.0,
# exactly; the code is three digits, and RFC 9110 15 makes one outside
# 100 to 599 invalid. As far as a line has come, it is: in its version
# (the bytes so far); in its code (the digits so far); in its reason;
# or refused.
type SView is Data:
  VVer{v: List<&2, U32>}
  VCode{v10: Bool, d: List<&2, U32>}
  VWhy{v10: Bool, code: U32}
  VBad{}

# the digits of a code, read as a decimal
def num.go(d: List<&2, U32>, acc: U32) -> U32:
  match d:
    case Nil{}:
      acc
    case Con{x, t}:
      num.go(t, (acc * 10 + (x - 48) : U32))

def num(d: List<&2, U32>) -> U32:
  num.go(d, 0)

def code.whole(+d: List<&2, U32>) -> Bool:
  +n = num(d)
  Nat.is_eq(cnt(d), 3n) && U32.is_le(100, n) && U32.is_le(n, 599)

def sv.why(v10: Bool, code: U32, sp: Span) -> SView:
  match sp:
    case Span{r, SEnd{}}:
      VWhy{v10, code}
    case Span{r, SAt{k, c, rest}}:
      VBad{}

def sv.code.sp(ok: Bool, v10: Bool, d: List<&2, U32>, rest: List<&2, U32>) -> SView:
  match ok:
    case True{}:
      sv.why(v10, num(d), span(TVal{}, rest))
    case False{}:
      VBad{}

def sv.code(v10: Bool, sp: Span) -> SView:
  match sp:
    case Span{d, SEnd{}}:
      VCode{v10, d}
    case Span{+d, SAt{R.KSp{}, c, rest}}:
      sv.code.sp(code.whole(d), v10, d, rest)
    case Span{d, SAt{k, c, rest}}:
      VBad{}

def sv.ver.sp(v11: Bool, v10: Bool, rest: List<&2, U32>) -> SView:
  match v11 v10:
    case True{} _:
      sv.code(False{}, span(TDig{}, rest))
    case False{} True{}:
      sv.code(True{}, span(TDig{}, rest))
    case False{} False{}:
      VBad{}

def sv.ver(sp: Span) -> SView:
  match sp:
    case Span{v, SEnd{}}:
      VVer{v}
    case Span{+v, SAt{R.KSp{}, c, rest}}:
      sv.ver.sp(leq(v, R.lit.v11()), leq(v, R.lit.v10()), rest)
    case Span{v, SAt{k, c, rest}}:
      VBad{}

def status.view(x: List<&2, U32>) -> SView:
  sv.ver(span(TVer{}, x))

# Field lines
# ===========
#
# field-line = field-name ":" OWS field-value OWS (RFC 9112 5): no space
# before the colon, and a line that starts with whitespace -- a line
# folded onto the one before (obs-fold, 5.2) -- has no name and is
# refused. The value is read by what the name is:
#
#   Content-Length (RFC 9112 6.3)  OWS 1*DIGIT OWS, the digits read as a
#                 decimal that stops growing once past the cap (the line
#                 is then refused at its end); never a list
#   Transfer-Encoding (6.1)  OWS, then the coding as it came: whitespace
#                 after it is part of it, and "chunked " is not chunked
#   Connection (RFC 9110 7.6.1)  a list: members split at commas and
#                 whitespace, empty ones allowed
#   any other     a value, only checked
type Val is Data:
  VLen0{}
  VLen{n: U32, ws: Bool}
  VTe0{}
  VTe{t: List<&2, U32>}
  VConn{done: List<&2, List<&2, U32>>, cur: List<&2, U32>}
  VSkip{}

type FLine is Data:
  FEmpty{}
  FName{n: List<&2, U32>}
  FVal{v: Val}
  FBad{}

# the digits of a length: past the cap, the number stops growing
def len.num.go(+e: R.Ask, d: List<&2, U32>, +acc: U32) -> U32:
  match d:
    case Nil{}:
      acc
    case Con{x, t}:
      len.num.go(e, t, Bool.pick(U32, U32.is_lt(R.ask.cap(e), acc), acc, (acc * 10 + (x - 48) : U32)))

def len.num(+e: R.Ask, d: List<&2, U32>) -> U32:
  len.num.go(e, d, 0)

def len.ws(n: U32, sp: Span) -> FLine:
  match sp:
    case Span{w, SEnd{}}:
      FVal{VLen{n, True{}}}
    case Span{w, SAt{k, c, rest}}:
      FBad{}

def len.digits(n: U32, stop: Stop) -> FLine:
  match stop:
    case SEnd{}:
      FVal{VLen{n, False{}}}
    case SAt{R.KSp{}, c, rest}:
      len.ws(n, span(TOws{}, rest))
    case SAt{R.KHt{}, c, rest}:
      len.ws(n, span(TOws{}, rest))
    case SAt{k, c, rest}:
      FBad{}

def len.run(+e: R.Ask, sp: Span) -> FLine:
  match sp:
    case Span{d, stop}:
      len.digits(len.num(e, d), stop)

def len.view(+e: R.Ask, sp: Span) -> FLine:
  match sp:
    case Span{w, SEnd{}}:
      FVal{VLen0{}}
    case Span{w, SAt{R.KDg{}, c, rest}}:
      len.run(e, span.push(c, span(TDig{}, rest)))
    case Span{w, SAt{k, c, rest}}:
      FBad{}

# a coding: OWS, then bytes a value may hold, kept as they came
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

# a list, member by member: whether every byte so far is one a value may
# hold, the members done (newest first), and the one being read
type Mem is Data:
  Mem{ok: Bool, done: List<&2, List<&2, U32>>, cur: List<&2, U32>}

def mem.sep(k: R.Cls) -> Bool:
  match k:
    case R.KSp{}:
      True{}
    case R.KHt{}:
      True{}
    case R.KCm{}:
      True{}
    case _:
      False{}

def mem.next(s: Bool, ok: Bool, done: List<&2, List<&2, U32>>, cur: List<&2, U32>, c: U32) -> Mem:
  match s:
    case True{}:
      Mem{ok, Con{cur, done}, Nil{}}
    case False{}:
      Mem{ok, done, snoc(cur, c)}

def mem.byte(m: Mem, +c: U32) -> Mem:
  match m:
    case Mem{ok, done, cur}:
      +k = R.cls(c)
      mem.next(mem.sep(k), ok && allows(TVal{}, k), done, cur, c)

def members(x: List<&2, U32>, m: Mem) -> Mem:
  match x:
    case Nil{}:
      m
    case Con{c, t}:
      members(t, mem.byte(m, c))

def list.view(m: Mem) -> FLine:
  match m:
    case Mem{ok, done, cur}:
      match ok:
        case True{}:
          FVal{VConn{done, cur}}
        case False{}:
          FBad{}

def skip.view(sp: Span) -> FLine:
  match sp:
    case Span{v, SEnd{}}:
      FVal{VSkip{}}
    case Span{v, SAt{k, c, rest}}:
      FBad{}

# the fields a response's framing reads, spelled as RFC 9110 and 9112
# spell them: the one a name is, known by exactly its bytes lowercased
type Fld is Data:
  FCl{}
  FTe{}
  FConn{}
  FOther{}

def fld.pick(b: Bool, f: Fld, rest: Fld) -> Fld:
  match b:
    case True{}:
      f
    case False{}:
      rest

def field(+n: List<&2, U32>) -> Fld:
  fld.pick(leq(n, R.lit.cl()), FCl{},
  fld.pick(leq(n, R.lit.te()), FTe{},
  fld.pick(leq(n, R.lit.co()), FConn{}, FOther{})))

def field.of(+e: R.Ask, f: Fld, v: List<&2, U32>) -> FLine:
  match f:
    case FCl{}:
      len.view(e, span(TOws{}, v))
    case FTe{}:
      te.view(span(TOws{}, v))
    case FConn{}:
      list.view(members(v, Mem{True{}, Nil{}, Nil{}}))
    case FOther{}:
      skip.view(span(TVal{}, v))

def field.name(+e: R.Ask, sp: Span) -> FLine:
  match sp:
    case Span{Nil{}, s}:
      FBad{}
    case Span{Con{h, r}, SEnd{}}:
      FName{Con{h, r}}
    case Span{Con{h, r}, SAt{R.KCo{}, c, v}}:
      field.of(e, field(lows(Con{h, r})), v)
    case Span{n, SAt{k, c, v}}:
      FBad{}

def field.view(+e: R.Ask, x: List<&2, U32>) -> FLine:
  match x:
    case Nil{}:
      FEmpty{}
    case Con{c, t}:
      field.name(e, span(TName{}, Con{c, t}))

# The head
# ========

# a length: the first says it, each after it must say the same (RFC 9112
# 6.3), and none may be past the cap
def head.len.at(ok: Bool, h: R.Head) -> Maybe<&2, R.Head>:
  match ok:
    case True{}:
      Some{h}
    case False{}:
      None{}

def head.len(h: R.Head, +n: U32) -> Maybe<&2, R.Head>:
  match h:
    case R.Head{v10, code, l, te, cl, ka}:
      match l:
        case None{}:
          Some{R.Head{v10, code, Some{n}, te, cl, ka}}
        case Some{+w}:
          head.len.at(U32.is_eq(n, w), R.Head{v10, code, Some{w}, te, cl, ka})

def head.big(big: Bool, h: R.Head, +n: U32) -> Maybe<&2, R.Head>:
  match big:
    case True{}:
      None{}
    case False{}:
      head.len(h, n)

# a coding: chunked alone, named once (RFC 9112 6.1, 7: chunked is
# applied once, and last; this reader decodes no other)
def head.te.at(ok: Bool, h: R.Head) -> Maybe<&2, R.Head>:
  match ok h:
    case True{} R.Head{v10, code, l, te, cl, ka}:
      Some{R.Head{v10, code, l, True{}, cl, ka}}
    case False{} _:
      None{}

def head.te(h: R.Head, chunked: Bool) -> Maybe<&2, R.Head>:
  match h:
    case R.Head{v10, code, l, +te, cl, ka}:
      head.te.at(chunked && Bool.not(te), R.Head{v10, code, l, te, cl, ka})

# whether a list names w, case aside
def named(+w: List<&2, U32>, ms: List<&2, List<&2, U32>>) -> Bool:
  match ms:
    case Nil{}:
      False{}
    case Con{m, r}:
      named(w, r) || leq(lows(m), w)

def head.conn(h: R.Head, a: Bool, b: Bool) -> R.Head:
  match h:
    case R.Head{v10, code, l, te, cl, ka}:
      R.Head{v10, code, l, te, cl || a, ka || b}

# a whole field line, at its end: what the head says after it, or none
# when the line is refused
def field.done(+e: R.Ask, h: R.Head, val: Val) -> Maybe<&2, R.Head>:
  match val:
    case VLen0{}:
      None{}
    case VLen{+n, ws}:
      head.big(U32.is_lt(R.ask.cap(e), n), h, n)
    case VTe0{}:
      None{}
    case VTe{t}:
      head.te(h, leq(lows(t), R.lit.chunked()))
    case VConn{+d, +c}:
      Some{head.conn(h, named(R.lit.close(), Con{c, d}), named(R.lit.ka(), Con{c, d}))}
    case VSkip{}:
      Some{h}

# The body's length (RFC 9112 6.3)
# ================================
#
# In 6.3's order, after what the head refuses outright: a
# Transfer-Encoding with a Content-Length (6.3.3: "ought to be handled as
# an error", how a message is smuggled), or in an HTTP/1.0 message (6.1:
# faulty framing).
#
#   1. a response to HEAD, any 1xx, 204 and 304 end at the blank line;
#      and a 1xx other than 101 is interim: the final response follows
#      (RFC 9110 15.2); a 101 is final, and the connection is no longer
#      HTTP's
#   3. chunked is a chunked body
#   5. a length is a body of that many bytes
#   7. anything else is a body that runs to the close
#
# (6.3's 2, a 2xx to CONNECT, is not a request this client makes; its 4,
# a coding other than chunked, the head has refused already.) A status
# below 200 is a 1xx: the status line allows none below 100.
def frame.bad(te: Bool, l: Maybe<&2, U32>, v10: Bool) -> Bool:
  match te l:
    case False{} _:
      False{}
    case True{} Some{n}:
      True{}
    case True{} None{}:
      v10

def frame.len(l: Maybe<&2, U32>) -> R.Frame:
  match l:
    case Some{n}:
      R.FLen{n}
    case None{}:
      R.FClose{}

def frame.pick(b: Bool, f: R.Frame, rest: R.Frame) -> R.Frame:
  match b:
    case True{}:
      f
    case False{}:
      rest

def framing(e: R.Ask, h: R.Head) -> R.Frame:
  match e h:
    case R.Ask{+head, cap} R.Head{+v10, +code, +l, +te, cl, ka}:
      frame.pick(frame.bad(te, l, v10), R.FBad{},
      frame.pick(U32.is_lt(code, 200) && Bool.not(U32.is_eq(code, 101)), R.FNext{},
      frame.pick(head || U32.is_lt(code, 200) || U32.is_eq(code, 204) || U32.is_eq(code, 304),
        R.FNone{},
      frame.pick(te, R.FChunked{}, frame.len(l)))))

# a final response, and whether the connection closes after it: the
# head said close, or it is HTTP/1.0 and did not say keep-alive (RFC
# 9112 9.3); it switched protocols (101); or its body ran to the close
def resp(h: R.Head, body: List<&2, U32>, delim: Bool) -> R.Resp:
  match h:
    case R.Head{+v10, +code, l, te, cl, ka}:
      R.Resp{code, v10, cl || (v10 && Bool.not(ka)) || U32.is_eq(code, 101) || delim,
        Bytes.from_list(body)}

# The walk
# ========

# where the input is: in the status line; in a field line of a head
# that has said h; at the LF after a line's CR (the head so far) or
# after the blank line's; in a body with what it still needs after the
# next byte; in a chunked body's framing, at a place in its grammar,
# with the chunk's size, the body so far and the budget; in a chunk's
# data; in a body that runs to the close, with the budget; after the
# final response, with what has come since; or refused
type Mode is Data:
  MStatus{cur: List<&2, U32>}
  MField{h: R.Head, cur: List<&2, U32>}
  MEol{h: R.Head}
  MEoh{h: R.Head}
  MBody{h: R.Head, more: Nat, got: List<&2, U32>}
  MChunk{h: R.Head, at: R.At, n: U32, got: List<&2, U32>, left: U32}
  MData{h: R.Head, more: Nat, got: List<&2, U32>, left: U32}
  MClose{h: R.Head, got: List<&2, U32>, left: Nat}
  MDone{r: R.Resp, rest: List<&2, U32>}
  MBad{}

# the walk: where it is, and the interim statuses (newest first)
type W is Data:
  W{mode: Mode, out: List<&2, U32>}

def w.new() -> W:
  W{MStatus{Nil{}}, Nil{}}

def status.cr.code(ok: Bool, v10: Bool, d: List<&2, U32>) -> Mode:
  match ok:
    case True{}:
      MEol{R.head.new(v10, num(d))}
    case False{}:
      MBad{}

# a status line at its CR: a whole one
def status.cr(v: SView) -> Mode:
  match v:
    case VVer{x}:
      MBad{}
    case VCode{v10, +d}:
      status.cr.code(code.whole(d), v10, d)
    case VWhy{v10, code}:
      MEol{R.head.new(v10, code)}
    case VBad{}:
      MBad{}

def field.next(mh: Maybe<&2, R.Head>) -> Mode:
  match mh:
    case Some{h}:
      MEol{h}
    case None{}:
      MBad{}

# a field line at its CR: the empty one ends the head
def field.cr(+e: R.Ask, h: R.Head, v: FLine) -> Mode:
  match v:
    case FEmpty{}:
      MEoh{h}
    case FVal{val}:
      field.next(field.done(e, h, val))
    case _:
      MBad{}

def head.body(z: Bool, h: R.Head, +n: U32) -> Mode:
  match z:
    case True{}:
      MDone{resp(h, Nil{}, False{}), Nil{}}
    case False{}:
      MBody{h, Nat.sub(U32.to_nat(n), 1n), Nil{}}

def head.at(e: R.Ask, f: R.Frame, +h: R.Head, out: List<&2, U32>) -> W:
  match f:
    case R.FBad{}:
      W{MBad{}, out}
    case R.FNext{}:
      match h:
        case R.Head{v10, code, l, te, cl, ka}:
          W{MStatus{Nil{}}, Con{code, out}}
    case R.FNone{}:
      W{MDone{resp(h, Nil{}, False{}), Nil{}}, out}
    case R.FLen{+n}:
      W{head.body(U32.is_zero(n), h, n), out}
    case R.FChunked{}:
      W{MChunk{h, R.ASize0{}, 0, Nil{}, R.ask.cap(e)}, out}
    case R.FClose{}:
      W{MClose{h, Nil{}, U32.to_nat(R.ask.cap(e))}, out}

def head.done(+e: R.Ask, +h: R.Head, out: List<&2, U32>) -> W:
  head.at(e, framing(e, h), h, out)

# a chunk's framing, one byte: where the grammar takes it, and the
# budget; a paid byte needs the budget to hold it and the chunk's data
# still, and the LF of a chunk line takes the chunk's size from it
def chunk.paid(over: Bool, h: R.Head, at: R.At, n: U32, got: List<&2, U32>, left: U32) -> Mode:
  match over:
    case True{}:
      MBad{}
    case False{}:
      MChunk{h, at, n, got, (left - 1 : U32)}

def chunk.to(paid: Bool, h: R.Head, at: R.At, +n: U32, got: List<&2, U32>, +left: U32) -> Mode:
  match paid:
    case True{}:
      chunk.paid(U32.is_le(left, n), h, at, n, got, left)
    case False{}:
      MChunk{h, at, n, got, left}

def chunk.line(z: Bool, h: R.Head, +n: U32, got: List<&2, U32>, +left: U32) -> Mode:
  match z:
    case True{}:
      MChunk{h, R.ATrail{}, 0, got, left}
    case False{}:
      MData{h, Nat.sub(U32.to_nat(n), 1n), got, (left - n : U32)}

def chunk.go(g: R.Go, h: R.Head, +n: U32, got: List<&2, U32>, +left: U32) -> Mode:
  match g:
    case R.GBad{}:
      MBad{}
    case R.GTo{at, paid}:
      chunk.to(paid, h, at, n, got, left)
    case R.GDigit{+d}:
      +n2 = (n * 16 + d : U32)
      chunk.paid(U32.is_le(left, n2), h, R.ASize{}, n2, got, left)
    case R.GLine{}:
      chunk.line(U32.is_zero(n), h, n, got, left)
    case R.GDone{}:
      MDone{resp(h, got, False{}), Nil{}}

def data.byte(more: Nat, c: U32, h: R.Head, got: List<&2, U32>, left: U32) -> Mode:
  match more:
    case 0n:
      MChunk{h, R.ADataCr{}, 0, snoc(got, c), left}
    case 1n+q:
      MData{h, q, snoc(got, c), left}

def body.byte(more: Nat, c: U32, h: R.Head, got: List<&2, U32>) -> Mode:
  match more:
    case 0n:
      MDone{resp(h, snoc(got, c), False{}), Nil{}}
    case 1n+q:
      MBody{h, q, snoc(got, c)}

def close.byte(left: Nat, c: U32, h: R.Head, got: List<&2, U32>) -> Mode:
  match left:
    case 0n:
      MBad{}
    case 1n+q:
      MClose{h, snoc(got, c), q}

# a line's bytes are gathered until its CR; a LF anywhere else is a bare
# LF, and after a CR nothing but a LF may come (RFC 9112 2.2)
def line.byte(k: R.Cls, c: U32, cur: List<&2, U32>, cr: Mode, more: List<&2, U32> -> Mode) -> Mode:
  match k:
    case R.KCr{}:
      cr
    case R.KLf{}:
      MBad{}
    case _:
      more(snoc(cur, c))

def next.at(+e: R.Ask, mode: Mode, k: R.Cls, +c: U32, out: List<&2, U32>) -> W:
  match mode:
    case MStatus{+cur}:
      W{line.byte(k, c, cur, status.cr(status.view(cur)), x => MStatus{x}), out}
    case MField{+h, +cur}:
      W{line.byte(k, c, cur, field.cr(e, h, field.view(e, cur)), x => MField{h, x}), out}
    case MEol{h}:
      match k:
        case R.KLf{}:
          W{MField{h, Nil{}}, out}
        case _:
          W{MBad{}, out}
    case MEoh{h}:
      match k:
        case R.KLf{}:
          head.done(e, h, out)
        case _:
          W{MBad{}, out}
    case MBody{h, more, got}:
      W{body.byte(more, c, h, got), out}
    case MChunk{h, at, n, got, left}:
      W{chunk.go(R.chunk.step(at, R.xk.of(k, c)), h, n, got, left), out}
    case MData{h, more, got, left}:
      W{data.byte(more, c, h, got, left), out}
    case MClose{h, got, left}:
      W{close.byte(left, c, h, got), out}
    case MDone{r, rest}:
      W{MDone{r, snoc(rest, c)}, out}
    case MBad{}:
      W{MBad{}, out}

def next(+e: R.Ask, w: W, +c: U32) -> W:
  match w:
    case W{mode, out}:
      next.at(e, mode, R.cls(c), c, out)

def walk(+e: R.Ask, bs: List<&2, U32>, w: W) -> W:
  match bs:
    case Nil{}:
      w
    case Con{c, t}:
      walk(e, t, next(e, w, c))

# at the input's end, a line it stopped inside is read as far as it goes
def status.end(v: SView) -> R.End:
  match v:
    case VBad{}:
      R.Refused{}
    case _:
      R.Open{}

def field.end(v: FLine) -> R.End:
  match v:
    case FBad{}:
      R.Refused{}
    case _:
      R.Open{}

def finish.end(+e: R.Ask, mode: Mode) -> R.End:
  match mode:
    case MStatus{cur}:
      status.end(status.view(cur))
    case MField{h, cur}:
      field.end(field.view(e, cur))
    case MClose{h, got, left}:
      R.Closing{resp(h, got, True{})}
    case MDone{r, rest}:
      R.Final{r, Bytes.from_list(rest)}
    case MBad{}:
      R.Refused{}
    case _:
      R.Open{}

def finish(+e: R.Ask, w: W) -> R.Look:
  match w:
    case W{mode, out}:
      R.Look{List.reverse(&2, U32, out), finish.end(e, mode)}

# A whole input, read: the interim statuses, oldest first, and how the
# response ends -- as far as the input goes, refused, a final response
# with the bytes after it, or a body running to the close.
def response(+e: R.Ask, bs: List<&2, U32>) -> R.Look:
  finish(e, walk(e, bs, w.new()))
