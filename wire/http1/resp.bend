# bend-wire: the HTTP/1.1 response reader, the client's half of HTTP/1.
#
# What a client reads back for one request it sent: zero or more interim
# (1xx) responses, then one final response and whatever follows it. The
# reader is a byte-step machine on wire/reader.bend, so chunking never
# changes what it reads and a refusal is never left (the kit's laws, one
# line each in PROOF.bend), and it is held to spec.bend, RFC 9112's
# response framing written plainly, by resp_sim: for every input and
# every way TCP cuts it, the reader reads what the spec reads.
#
# What it accepts is deliberately small, because a response framed one
# way by the proxy and another by the next hop is how a response is
# split or a request smuggled behind it:
#
#   a status line  HTTP/1.1 or HTTP/1.0, one SP, three digits from 100 to
#                  599, then SP and a reason of visible bytes, spaces and
#                  tabs -- or nothing: "HTTP/1.1 204\r\n" is taken
#   field lines    a token, a colon at once, a value of no control and no
#                  bare LF; no line folded onto the one before
#   Content-Length digits and whitespace only, never a list, every copy
#                  the same, at most the body cap
#   Transfer-Encoding  exactly "chunked", in any case, and once; never
#                  beside a Content-Length, never in HTTP/1.0
#   Connection     a list; close and keep-alive are heard anywhere in it
#
# and the body is framed by RFC 9112 6.3, in its order: a response to
# HEAD, any 1xx, 204 and 304 have none; chunked is decoded by 7.1's
# grammar, extensions and trailers read and dropped; a length is counted
# off; anything else runs to the close. Every line ends in CR LF. The
# request's method is the reader's context (Ask): whether it was HEAD,
# and the most body it will hold.
import Base
import ../reader.bend as Wr

# Bytes
# =====

# What a byte is to the head grammar (RFC 9110 5.6.2, RFC 9112 5): a
# space, a tab, the two line ends, the colon, the comma that separates
# list members, a digit, any other token character, any other visible
# byte (or obs-text), and a control. spec.bend and this reader share
# these ten classes; LAWS.bend pins them to the RFC's sets on every byte.
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

def cls.high(del: Bool) -> Cls:
  match del:
    case True{}:
      KCt{}
    case False{}:
      KVc{}

# the token characters that are neither letters nor digits, as ranges:
# ! #$%&' *+ -. ^_` | ~
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

# an uppercase ASCII letter's lowercase, and every other byte as it is:
# names, codings and list members are case-insensitive
def lower.at(+c: U32, up: Bool) -> U32:
  match up:
    case True{}:
      (c + 32 : U32)
    case False{}:
      c

def lower(+c: U32) -> U32:
  lower.at(c, U32.is_le(65, c) && U32.is_le(c, 90))

# Literals
# ========
#
# A literal the reader waits for is a candidate: the bytes of it still
# to come, or None once a byte did not match. cstep takes one byte; a
# candidate is done when nothing of it is left.

def cand.pick(ok: Bool, t: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}:
      Some{t}
    case False{}:
      None{}

def cstep(m: Maybe<&2, List<&2, U32>>, +c: U32) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}:
      None{}
    case Some{l}:
      match l:
        case Nil{}:
          None{}
        case Con{w, t}:
          cand.pick(U32.is_eq(c, w), t)

def done(m: Maybe<&2, List<&2, U32>>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{l}:
      match l:
        case Nil{}:
          True{}
        case Con{w, t}:
          False{}

def lit.v11() -> List<&2, U32>:
  Wr.bytes("HTTP/1.1")

def lit.v10() -> List<&2, U32>:
  Wr.bytes("HTTP/1.0")

def lit.cl() -> List<&2, U32>:
  Wr.bytes("content-length")

def lit.te() -> List<&2, U32>:
  Wr.bytes("transfer-encoding")

def lit.co() -> List<&2, U32>:
  Wr.bytes("connection")

def lit.chunked() -> List<&2, U32>:
  Wr.bytes("chunked")

def lit.close() -> List<&2, U32>:
  Wr.bytes("close")

def lit.ka() -> List<&2, U32>:
  Wr.bytes("keep-alive")

# The context and the result
# ==========================

# What the reader reads beside the state: whether the request was HEAD,
# and the most body it holds (a body past it is refused). The cap is
# kept below 2^28 (ask.new), so sixteen times a chunk size under it plus
# a digit never wraps, nor does ten times a length plus a digit.
type Ask is Data:
  Ask{head: Bool, cap: U32}

def ask.new(head: Bool, +cap: U32) -> Ask:
  Ask{head, Bool.pick(U32, U32.is_lt(268435455, cap), 268435455, cap)}

def ask.cap(e: Ask) -> U32:
  match e:
    case Ask{head, cap}:
      cap

# What a head has said: its version (HTTP/1.0 or not) and status, the
# one length its Content-Length fields agree on, whether it said
# chunked, and whether a Connection named close or keep-alive.
type Head is Data:
  Head{v10: Bool, code: U32, len: Maybe<&2, U32>, te: Bool, close: Bool, ka: Bool}

def head.new(v10: Bool, code: U32) -> Head:
  Head{v10, code, None{}, False{}, False{}, False{}}

# A final response: its status, its version, whether the connection must
# close after it (it said so, it is HTTP/1.0 without keep-alive, it
# switched protocols, or its body ran to the close), and its body.
type Resp is Data:
  Resp{code: U32, v10: Bool, close: Bool, body: Bytes()}

def final(h: Head, body: Bytes(), delim: Bool) -> Resp:
  match h:
    case Head{+v10, +code, len, te, close, ka}:
      Resp{code, v10, close || (v10 && Bool.not(ka)) || U32.is_eq(code, 101) || delim, body}

# The chunked coding
# ==================
#
# RFC 9112 7.1's grammar is regular, and spec.bend and the reader share
# it as the table it is: where in the grammar a byte arrives (At), what
# the byte is to it (XK) and where it goes (chunk.step). A chunk-size is
# read as hexadecimal as it comes, and every byte of a chunk line before
# its CR and every byte of data is paid from the body's budget: a byte
# that would leave less than the chunk still needs is refused where it
# stands. Extensions and the trailer's field lines are read by their
# grammar and dropped. Every line ends in CR LF.
type XK is Data:
  XHex{d: U32}
  XTok{}
  XWs{}
  XSemi{}
  XEq{}
  XQuote{}
  XBack{}
  XColon{}
  XCr{}
  XLf{}
  XVis{}
  XCtl{}

def hexdig.at(+c: U32, dg: Bool, lo: Bool, up: Bool) -> Maybe<&2, U32>:
  match dg lo up:
    case True{} _ _:
      Some{(c - 48 : U32)}
    case False{} True{} _:
      Some{(c - 87 : U32)}
    case False{} False{} True{}:
      Some{(c - 55 : U32)}
    case False{} False{} False{}:
      None{}

# HEXDIG (RFC 5234): 0 to 9, and a to f in either case, with its value
def hexdig(+c: U32) -> Maybe<&2, U32>:
  hexdig.at(c, digit(c), U32.is_le(97, c) && U32.is_le(c, 102), U32.is_le(65, c) && U32.is_le(c, 70))

def xk.hex(m: Maybe<&2, U32>) -> XK:
  match m:
    case Some{d}:
      XHex{d}
    case None{}:
      XTok{}

def xk.vc(semi: Bool, eq: Bool, quote: Bool, back: Bool) -> XK:
  match semi eq quote back:
    case True{} _ _ _:
      XSemi{}
    case False{} True{} _ _:
      XEq{}
    case False{} False{} True{} _:
      XQuote{}
    case False{} False{} False{} True{}:
      XBack{}
    case False{} False{} False{} False{}:
      XVis{}

def xk.of(k: Cls, +c: U32) -> XK:
  match k:
    case KSp{}:
      XWs{}
    case KHt{}:
      XWs{}
    case KCr{}:
      XCr{}
    case KLf{}:
      XLf{}
    case KCo{}:
      XColon{}
    case KCm{}:
      XVis{}
    case KDg{}:
      xk.hex(hexdig(c))
    case KTk{}:
      xk.hex(hexdig(c))
    case KVc{}:
      xk.vc(U32.is_eq(c, 59), U32.is_eq(c, 61), U32.is_eq(c, 34), U32.is_eq(c, 92))
    case KCt{}:
      XCtl{}

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
# a chunk line; the body's end
type Go is Data:
  GBad{}
  GTo{at: At, paid: Bool}
  GDigit{d: U32}
  GLine{}
  GDone{}

def chunk.step(at: At, x: XK) -> Go:
  match at x:
    case ASize0{} XHex{d}:
      GDigit{d}
    case ASize0{} _:
      GBad{}
    case ASize{} XHex{d}:
      GDigit{d}
    case ASize{} XSemi{}:
      GTo{AName0{}, True{}}
    case ASize{} XWs{}:
      GTo{ABws{}, True{}}
    case ASize{} XCr{}:
      GTo{ALf{}, False{}}
    case ASize{} _:
      GBad{}
    case ABws{} XWs{}:
      GTo{ABws{}, True{}}
    case ABws{} XSemi{}:
      GTo{AName0{}, True{}}
    case ABws{} _:
      GBad{}
    case AName0{} XWs{}:
      GTo{AName0{}, True{}}
    case AName0{} XHex{d}:
      GTo{AName{}, True{}}
    case AName0{} XTok{}:
      GTo{AName{}, True{}}
    case AName0{} _:
      GBad{}
    case AName{} XHex{d}:
      GTo{AName{}, True{}}
    case AName{} XTok{}:
      GTo{AName{}, True{}}
    case AName{} XWs{}:
      GTo{ANameWs{}, True{}}
    case AName{} XEq{}:
      GTo{AVal0{}, True{}}
    case AName{} XSemi{}:
      GTo{AName0{}, True{}}
    case AName{} XCr{}:
      GTo{ALf{}, False{}}
    case AName{} _:
      GBad{}
    case ANameWs{} XWs{}:
      GTo{ANameWs{}, True{}}
    case ANameWs{} XEq{}:
      GTo{AVal0{}, True{}}
    case ANameWs{} XSemi{}:
      GTo{AName0{}, True{}}
    case ANameWs{} _:
      GBad{}
    case AVal0{} XWs{}:
      GTo{AVal0{}, True{}}
    case AVal0{} XHex{d}:
      GTo{AToken{}, True{}}
    case AVal0{} XTok{}:
      GTo{AToken{}, True{}}
    case AVal0{} XQuote{}:
      GTo{AQuoted{}, True{}}
    case AVal0{} _:
      GBad{}
    case AToken{} XHex{d}:
      GTo{AToken{}, True{}}
    case AToken{} XTok{}:
      GTo{AToken{}, True{}}
    case AToken{} XSemi{}:
      GTo{AName0{}, True{}}
    case AToken{} XWs{}:
      GTo{ABws{}, True{}}
    case AToken{} XCr{}:
      GTo{ALf{}, False{}}
    case AToken{} _:
      GBad{}
    case AQuoted{} XBack{}:
      GTo{AEscape{}, True{}}
    case AQuoted{} XQuote{}:
      GTo{AClosed{}, True{}}
    case AQuoted{} XCr{}:
      GBad{}
    case AQuoted{} XLf{}:
      GBad{}
    case AQuoted{} XCtl{}:
      GBad{}
    case AQuoted{} _:
      GTo{AQuoted{}, True{}}
    case AEscape{} XCr{}:
      GBad{}
    case AEscape{} XLf{}:
      GBad{}
    case AEscape{} XCtl{}:
      GBad{}
    case AEscape{} _:
      GTo{AQuoted{}, True{}}
    case AClosed{} XSemi{}:
      GTo{AName0{}, True{}}
    case AClosed{} XWs{}:
      GTo{ABws{}, True{}}
    case AClosed{} XCr{}:
      GTo{ALf{}, False{}}
    case AClosed{} _:
      GBad{}
    case ALf{} XLf{}:
      GLine{}
    case ALf{} _:
      GBad{}
    case ADataCr{} XCr{}:
      GTo{ADataLf{}, False{}}
    case ADataCr{} _:
      GBad{}
    case ADataLf{} XLf{}:
      GTo{ASize0{}, False{}}
    case ADataLf{} _:
      GBad{}
    case ATrail{} XCr{}:
      GTo{AEnd{}, False{}}
    case ATrail{} XHex{d}:
      GTo{ATName{}, False{}}
    case ATrail{} XTok{}:
      GTo{ATName{}, False{}}
    case ATrail{} _:
      GBad{}
    case ATName{} XHex{d}:
      GTo{ATName{}, False{}}
    case ATName{} XTok{}:
      GTo{ATName{}, False{}}
    case ATName{} XColon{}:
      GTo{ATVal{}, False{}}
    case ATName{} _:
      GBad{}
    case ATVal{} XCr{}:
      GTo{ATLf{}, False{}}
    case ATVal{} XLf{}:
      GBad{}
    case ATVal{} XCtl{}:
      GBad{}
    case ATVal{} _:
      GTo{ATVal{}, False{}}
    case ATLf{} XLf{}:
      GTo{ATrail{}, False{}}
    case ATLf{} _:
      GBad{}
    case AEnd{} XLf{}:
      GDone{}
    case AEnd{} _:
      GBad{}

# The reader
# ==========
#
# Where the reader is. The status line: its version, read against the
# two it may be (SVer); its code, as a number and a count of digits
# (SCode); its reason (SWhy). A field line: its start (Lin), its name,
# read against the three names that frame a body (Nam), and its value,
# read the way its name says -- a length (Len0, Len, LenW), a coding
# (Te0, Te), a Connection list with what its members said so far and
# the member being read (Conn), or anything else (Oth). The LF after a
# line's CR (Eol) and after the blank line's (Eoh). A body: counted off
# (Bod), chunked (Chk, and Dat for a chunk's data), or to the close
# (Clo), each with the body so far and, for the last two, the budget
# left. After the final response (Fin), with the bytes that came after
# it; and refused (Bad), which is never left. P adds the interim
# statuses seen, newest first.
type St is Data:
  SVer{a: Maybe<&2, List<&2, U32>>, b: Maybe<&2, List<&2, U32>>}
  SCode{v10: Bool, n: U32, k: Nat}
  SWhy{v10: Bool, code: U32}
  Eol{h: Head}
  Lin{h: Head}
  Nam{h: Head, cl: Maybe<&2, List<&2, U32>>, te: Maybe<&2, List<&2, U32>>,
    co: Maybe<&2, List<&2, U32>>}
  Oth{h: Head}
  Len0{h: Head}
  Len{h: Head, n: U32}
  LenW{h: Head, n: U32}
  Te0{h: Head}
  Te{h: Head, m: Maybe<&2, List<&2, U32>>}
  Conn{h: Head, cl: Bool, ka: Bool, mc: Maybe<&2, List<&2, U32>>, mk: Maybe<&2, List<&2, U32>>}
  Eoh{h: Head}
  Bod{h: Head, more: Nat, got: Bytes()}
  Chk{h: Head, at: At, n: U32, got: Bytes(), left: U32}
  Dat{h: Head, more: Nat, got: Bytes(), left: U32}
  Clo{h: Head, got: Bytes(), left: Nat}
  Fin{r: Resp, rest: Bytes()}
  Bad{}

type P is Data:
  P{st: St, out: List<&2, U32>}

def st.new() -> St:
  SVer{Some{lit.v11()}, Some{lit.v10()}}

def p.new() -> P:
  P{st.new(), Nil{}}

# The status line
# ---------------

def ver.sp(v11: Bool, v10: Bool) -> St:
  match v11 v10:
    case True{} _:
      SCode{False{}, 0, 0n}
    case False{} True{}:
      SCode{True{}, 0, 0n}
    case False{} False{}:
      Bad{}

# three digits, from 100 to 599 (RFC 9110 15)
def code.ok(+n: U32, +k: Nat) -> Bool:
  Nat.is_eq(k, 3n) && U32.is_le(100, n) && U32.is_le(n, 599)

def code.sp(ok: Bool, v10: Bool, n: U32) -> St:
  match ok:
    case True{}:
      SWhy{v10, n}
    case False{}:
      Bad{}

def code.cr(ok: Bool, v10: Bool, n: U32) -> St:
  match ok:
    case True{}:
      Eol{head.new(v10, n)}
    case False{}:
      Bad{}

# Field lines
# -----------

def name.end(h: Head, cl: Bool, te: Bool, co: Bool) -> St:
  match cl te co:
    case True{} _ _:
      Len0{h}
    case False{} True{} _:
      Te0{h}
    case False{} False{} True{}:
      Conn{h, False{}, False{}, Some{lit.close()}, Some{lit.ka()}}
    case False{} False{} False{}:
      Oth{h}

# a digit of a length: past the cap the number stops growing, and the
# line is refused at its end
def len.dig(e: Ask, +n: U32, c: U32) -> U32:
  Bool.pick(U32, U32.is_lt(ask.cap(e), n), n, (n * 10 + (c - 48) : U32))

def len.at(ok: Bool, h: Head) -> St:
  match ok:
    case True{}:
      Eol{h}
    case False{}:
      Bad{}

# the first says the length, and each after it must say the same
def len.head(h: Head, +n: U32) -> St:
  match h:
    case Head{v10, code, l, te, cl, ka}:
      match l:
        case None{}:
          Eol{Head{v10, code, Some{n}, te, cl, ka}}
        case Some{+w}:
          len.at(U32.is_eq(n, w), Head{v10, code, Some{w}, te, cl, ka})

def len.big(big: Bool, h: Head, +n: U32) -> St:
  match big:
    case True{}:
      Bad{}
    case False{}:
      len.head(h, n)

def len.cr(e: Ask, h: Head, +n: U32) -> St:
  len.big(U32.is_lt(ask.cap(e), n), h, n)

def te.at(ok: Bool, h: Head) -> St:
  match ok h:
    case True{} Head{v10, code, l, te, cl, ka}:
      Eol{Head{v10, code, l, True{}, cl, ka}}
    case False{} _:
      Bad{}

# chunked, named once
def te.cr(h: Head, ok: Bool) -> St:
  match h:
    case Head{v10, code, l, +te, cl, ka}:
      te.at(ok && Bool.not(te), Head{v10, code, l, te, cl, ka})

def conn.cr(h: Head, a: Bool, b: Bool) -> St:
  match h:
    case Head{v10, code, l, te, cl, ka}:
      Eol{Head{v10, code, l, te, cl || a, ka || b}}

# The head's end
# --------------
#
# RFC 9112 6.3, in its order, after the head's own refusals: a
# Transfer-Encoding beside a Content-Length (6.3.3: how a message is
# smuggled) or in HTTP/1.0 (6.1: faulty framing) is refused. Then a 1xx
# other than 101 is interim, and the next response follows; a response
# to HEAD, a 1xx, 204 and 304 end at the blank line; chunked is a
# chunked body; a length a body of that length; and anything else runs
# to the close.
type Frame is Data:
  FBad{}
  FNext{}
  FNone{}
  FLen{n: U32}
  FChunked{}
  FClose{}

def frame.body(te: Bool, l: Maybe<&2, U32>) -> Frame:
  match te l:
    case True{} _:
      FChunked{}
    case False{} Some{n}:
      FLen{n}
    case False{} None{}:
      FClose{}

def frame.none(+head: Bool, +code: U32) -> Bool:
  head || U32.is_lt(code, 200) || U32.is_eq(code, 204) || U32.is_eq(code, 304)

def frame.at(bad: Bool, next: Bool, none: Bool, te: Bool, l: Maybe<&2, U32>) -> Frame:
  match bad next none:
    case True{} _ _:
      FBad{}
    case False{} True{} _:
      FNext{}
    case False{} False{} True{}:
      FNone{}
    case False{} False{} False{}:
      frame.body(te, l)

def frame.two(+te: Bool, l: Maybe<&2, U32>) -> Bool:
  match l:
    case None{}:
      False{}
    case Some{n}:
      te

def frame(e: Ask, h: Head) -> Frame:
  match e h:
    case Ask{+head, cap} Head{+v10, +code, +l, +te, cl, ka}:
      frame.at(frame.two(te, l) || (v10 && te),
        U32.is_lt(code, 200) && Bool.not(U32.is_eq(code, 101)),
        frame.none(head, code), te, l)

def head.len(z: Bool, h: Head, +n: U32) -> St:
  match z:
    case True{}:
      Fin{final(h, "", False{}), ""}
    case False{}:
      Bod{h, Nat.sub(U32.to_nat(n), 1n), ""}

def head.at(e: Ask, f: Frame, +h: Head, +code: U32, out: List<&2, U32>) -> P:
  match f:
    case FBad{}:
      P{Bad{}, out}
    case FNext{}:
      P{st.new(), Con{code, out}}
    case FNone{}:
      P{Fin{final(h, "", False{}), ""}, out}
    case FLen{+n}:
      P{head.len(U32.is_zero(n), h, n), out}
    case FChunked{}:
      P{Chk{h, ASize0{}, 0, "", ask.cap(e)}, out}
    case FClose{}:
      P{Clo{h, "", U32.to_nat(ask.cap(e))}, out}

def head.code(h: Head) -> U32:
  match h:
    case Head{v10, code, l, te, cl, ka}:
      code

def head.end(+e: Ask, +h: Head, out: List<&2, U32>) -> P:
  head.at(e, frame(e, h), h, head.code(h), out)

# Bodies
# ------

def body.byte(more: Nat, c: U32, h: Head, got: Bytes()) -> St:
  match more:
    case 0n:
      Fin{final(h, Bytes.push(got, c), False{}), ""}
    case 1n+q:
      Bod{h, q, Bytes.push(got, c)}

def chunk.paid(over: Bool, h: Head, at: At, n: U32, got: Bytes(), left: U32) -> St:
  match over:
    case True{}:
      Bad{}
    case False{}:
      Chk{h, at, n, got, (left - 1 : U32)}

def chunk.to(paid: Bool, h: Head, at: At, +n: U32, got: Bytes(), +left: U32) -> St:
  match paid:
    case True{}:
      chunk.paid(U32.is_le(left, n), h, at, n, got, left)
    case False{}:
      Chk{h, at, n, got, left}

def chunk.line(z: Bool, h: Head, +n: U32, got: Bytes(), +left: U32) -> St:
  match z:
    case True{}:
      Chk{h, ATrail{}, 0, got, left}
    case False{}:
      Dat{h, Nat.sub(U32.to_nat(n), 1n), got, (left - n : U32)}

def chunk.go(g: Go, h: Head, +n: U32, got: Bytes(), +left: U32) -> St:
  match g:
    case GBad{}:
      Bad{}
    case GTo{at, paid}:
      chunk.to(paid, h, at, n, got, left)
    case GDigit{+d}:
      +n2 = (n * 16 + d : U32)
      chunk.paid(U32.is_le(left, n2), h, ASize{}, n2, got, left)
    case GLine{}:
      chunk.line(U32.is_zero(n), h, n, got, left)
    case GDone{}:
      Fin{final(h, got, False{}), ""}

def data.byte(more: Nat, c: U32, h: Head, got: Bytes(), left: U32) -> St:
  match more:
    case 0n:
      Chk{h, ADataCr{}, 0, Bytes.push(got, c), left}
    case 1n+q:
      Dat{h, q, Bytes.push(got, c), left}

def close.byte(left: Nat, c: U32, h: Head, got: Bytes()) -> St:
  match left:
    case 0n:
      Bad{}
    case 1n+q:
      Clo{h, Bytes.push(got, c), q}

# The step
# --------

def step.at(+e: Ask, st: St, k: Cls, +c: U32, out: List<&2, U32>) -> P:
  match st k:
    case SVer{a, b} KSp{}:
      P{ver.sp(done(a), done(b)), out}
    case SVer{a, b} KCr{}:
      P{Bad{}, out}
    case SVer{a, b} KLf{}:
      P{Bad{}, out}
    case SVer{a, b} _:
      P{SVer{cstep(a, c), cstep(b, c)}, out}
    case SCode{v10, +n, +k} KDg{}:
      P{SCode{v10, (n * 10 + (c - 48) : U32), 1n+k}, out}
    case SCode{v10, +n, +k} KSp{}:
      P{code.sp(code.ok(n, k), v10, n), out}
    case SCode{v10, +n, +k} KCr{}:
      P{code.cr(code.ok(n, k), v10, n), out}
    case SCode{v10, n, k} _:
      P{Bad{}, out}
    case SWhy{v10, code} KCr{}:
      P{Eol{head.new(v10, code)}, out}
    case SWhy{v10, code} KLf{}:
      P{Bad{}, out}
    case SWhy{v10, code} KCt{}:
      P{Bad{}, out}
    case SWhy{v10, code} _:
      P{SWhy{v10, code}, out}
    case Eol{h} KLf{}:
      P{Lin{h}, out}
    case Eol{h} _:
      P{Bad{}, out}
    case Lin{h} KCr{}:
      P{Eoh{h}, out}
    case Lin{h} KTk{}:
      +l = lower(c)
      P{Nam{h, cstep(Some{lit.cl()}, l), cstep(Some{lit.te()}, l), cstep(Some{lit.co()}, l)}, out}
    case Lin{h} KDg{}:
      +l = lower(c)
      P{Nam{h, cstep(Some{lit.cl()}, l), cstep(Some{lit.te()}, l), cstep(Some{lit.co()}, l)}, out}
    case Lin{h} _:
      P{Bad{}, out}
    case Nam{h, a, b, d} KCo{}:
      P{name.end(h, done(a), done(b), done(d)), out}
    case Nam{h, a, b, d} KTk{}:
      +l = lower(c)
      P{Nam{h, cstep(a, l), cstep(b, l), cstep(d, l)}, out}
    case Nam{h, a, b, d} KDg{}:
      +l = lower(c)
      P{Nam{h, cstep(a, l), cstep(b, l), cstep(d, l)}, out}
    case Nam{h, a, b, d} _:
      P{Bad{}, out}
    case Oth{h} KCr{}:
      P{Eol{h}, out}
    case Oth{h} KLf{}:
      P{Bad{}, out}
    case Oth{h} KCt{}:
      P{Bad{}, out}
    case Oth{h} _:
      P{Oth{h}, out}
    case Len0{h} KSp{}:
      P{Len0{h}, out}
    case Len0{h} KHt{}:
      P{Len0{h}, out}
    case Len0{h} KDg{}:
      P{Len{h, len.dig(e, 0, c)}, out}
    case Len0{h} _:
      P{Bad{}, out}
    case Len{h, +n} KDg{}:
      P{Len{h, len.dig(e, n, c)}, out}
    case Len{h, n} KSp{}:
      P{LenW{h, n}, out}
    case Len{h, n} KHt{}:
      P{LenW{h, n}, out}
    case Len{h, +n} KCr{}:
      P{len.cr(e, h, n), out}
    case Len{h, n} _:
      P{Bad{}, out}
    case LenW{h, n} KSp{}:
      P{LenW{h, n}, out}
    case LenW{h, n} KHt{}:
      P{LenW{h, n}, out}
    case LenW{h, +n} KCr{}:
      P{len.cr(e, h, n), out}
    case LenW{h, n} _:
      P{Bad{}, out}
    case Te0{h} KSp{}:
      P{Te0{h}, out}
    case Te0{h} KHt{}:
      P{Te0{h}, out}
    case Te0{h} KCr{}:
      P{Bad{}, out}
    case Te0{h} KLf{}:
      P{Bad{}, out}
    case Te0{h} KCt{}:
      P{Bad{}, out}
    case Te0{h} _:
      P{Te{h, cstep(Some{lit.chunked()}, lower(c))}, out}
    case Te{h, m} KCr{}:
      P{te.cr(h, done(m)), out}
    case Te{h, m} KLf{}:
      P{Bad{}, out}
    case Te{h, m} KCt{}:
      P{Bad{}, out}
    case Te{h, m} _:
      P{Te{h, cstep(m, lower(c))}, out}
    case Conn{h, +cl, +ka, +mc, +mk} KSp{}:
      P{Conn{h, cl || done(mc), ka || done(mk), Some{lit.close()}, Some{lit.ka()}}, out}
    case Conn{h, +cl, +ka, +mc, +mk} KHt{}:
      P{Conn{h, cl || done(mc), ka || done(mk), Some{lit.close()}, Some{lit.ka()}}, out}
    case Conn{h, +cl, +ka, +mc, +mk} KCm{}:
      P{Conn{h, cl || done(mc), ka || done(mk), Some{lit.close()}, Some{lit.ka()}}, out}
    case Conn{h, +cl, +ka, +mc, +mk} KCr{}:
      P{conn.cr(h, cl || done(mc), ka || done(mk)), out}
    case Conn{h, cl, ka, mc, mk} KLf{}:
      P{Bad{}, out}
    case Conn{h, cl, ka, mc, mk} KCt{}:
      P{Bad{}, out}
    case Conn{h, cl, ka, mc, mk} _:
      +l = lower(c)
      P{Conn{h, cl, ka, cstep(mc, l), cstep(mk, l)}, out}
    case Eoh{h} KLf{}:
      head.end(e, h, out)
    case Eoh{h} _:
      P{Bad{}, out}
    case Bod{h, more, got} _:
      P{body.byte(more, c, h, got), out}
    case Chk{h, at, n, got, left} _:
      P{chunk.go(chunk.step(at, xk.of(k, c)), h, n, got, left), out}
    case Dat{h, more, got, left} _:
      P{data.byte(more, c, h, got, left), out}
    case Clo{h, got, left} _:
      P{close.byte(left, c, h, got), out}
    case Fin{r, rest} _:
      P{Fin{r, Bytes.push(rest, c)}, out}
    case Bad{} _:
      P{Bad{}, out}

def step(+e: Ask, p: P, +c: U32) -> P:
  match p:
    case P{st, out}:
      step.at(e, st, cls(c), c, out)

# The walk is the reader kit's, with the Ask beside the state.
def wstep(e: Ask, p: P, c: U32) -> P:
  step(e, p, c)

def feed(+e: Ask, s: List<&2, U32>, p: P) -> P:
  Wr.feed(~Ask, ~P, ~wstep, e, s, p)

# The block walk
# --------------
#
# A read is walked by moves: a body, a chunk's data, a close-delimited
# body and what follows the final response are each taken as one run,
# as far as the read or the run goes; every other state steps one byte.
# PROOF.bend proves each move lands where stepping its bytes does (the
# kit's adv_ok), so the kit's laws are the reader's.

def bod.took(h: Head, b: Bytes(), out: List<&2, U32>, xy: Bytes() & Bytes()) -> P & Bytes():
  (x, y) = xy
  (P{Fin{final(h, Bytes.append(b, x), False{}), ""}, out}, y)

def bod.at(+r: Nat, h: Head, b: Bytes(), +s: Bytes(), out: List<&2, U32>, done: Bool) ->
  P & Bytes():
  match done:
    case False{}:
      (P{Bod{h, Nat.sub(r, Bytes.len(s)), Bytes.append(b, s)}, out}, "")
    case True{}:
      bod.took(h, b, out, String.cut(s, 1n+r))

def dat.took(h: Head, b: Bytes(), left: U32, out: List<&2, U32>, xy: Bytes() & Bytes()) ->
  P & Bytes():
  (x, y) = xy
  (P{Chk{h, ADataCr{}, 0, Bytes.append(b, x), left}, out}, y)

def dat.at(+r: Nat, h: Head, b: Bytes(), +s: Bytes(), left: U32, out: List<&2, U32>,
  done: Bool) -> P & Bytes():
  match done:
    case False{}:
      (P{Dat{h, Nat.sub(r, Bytes.len(s)), Bytes.append(b, s), left}, out}, "")
    case True{}:
      dat.took(h, b, left, out, String.cut(s, 1n+r))

# a close-delimited body: all of the read while the budget holds it; a
# read past the budget is refused (its byte past the budget would be)
def clo.at(h: Head, b: Bytes(), +s: Bytes(), +left: Nat, out: List<&2, U32>, fits: Bool) ->
  P & Bytes():
  match fits:
    case True{}:
      (P{Clo{h, Bytes.append(b, s), Nat.sub(left, Bytes.len(s))}, out}, "")
    case False{}:
      (P{Bad{}, out}, "")

def one(+e: Ask, p: P, s: Bytes()) -> P & Bytes():
  match s:
    case SNil{}:
      (p, SNil{})
    case SCon{Chr{c}, t}:
      (step(e, p, c), t)

def adv.at(+e: Ask, st: St, +s: Bytes(), out: List<&2, U32>) -> P & Bytes():
  match st:
    case Bod{h, +r, b}:
      bod.at(r, h, b, s, out, Nat.is_lt(r, Bytes.len(s)))
    case Dat{h, +r, b, left}:
      dat.at(r, h, b, s, left, out, Nat.is_lt(r, Bytes.len(s)))
    case Clo{h, b, +left}:
      clo.at(h, b, s, left, out, Nat.is_le(Bytes.len(s), left))
    case Fin{r, rest}:
      (P{Fin{r, Bytes.append(rest, s)}, out}, "")
    case Bad{}:
      (P{Bad{}, out}, "")
    case SVer{a, b}:
      one(e, P{SVer{a, b}, out}, s)
    case SCode{v10, n, k}:
      one(e, P{SCode{v10, n, k}, out}, s)
    case SWhy{v10, code}:
      one(e, P{SWhy{v10, code}, out}, s)
    case Eol{h}:
      one(e, P{Eol{h}, out}, s)
    case Lin{h}:
      one(e, P{Lin{h}, out}, s)
    case Nam{h, a, b, d}:
      one(e, P{Nam{h, a, b, d}, out}, s)
    case Oth{h}:
      one(e, P{Oth{h}, out}, s)
    case Len0{h}:
      one(e, P{Len0{h}, out}, s)
    case Len{h, n}:
      one(e, P{Len{h, n}, out}, s)
    case LenW{h, n}:
      one(e, P{LenW{h, n}, out}, s)
    case Te0{h}:
      one(e, P{Te0{h}, out}, s)
    case Te{h, m}:
      one(e, P{Te{h, m}, out}, s)
    case Conn{h, cl, ka, mc, mk}:
      one(e, P{Conn{h, cl, ka, mc, mk}, out}, s)
    case Eoh{h}:
      one(e, P{Eoh{h}, out}, s)
    case Chk{h, at, n, got, left}:
      one(e, P{Chk{h, at, n, got, left}, out}, s)

def adv(+e: Ask, s: Bytes(), p: P) -> P & Bytes():
  match p:
    case P{st, out}:
      adv.at(e, st, s, out)

def wadv(e: Ask, s: Bytes(), p: P) -> P & Bytes():
  adv(e, s, p)

def feed_buf(+e: Ask, +s: Bytes(), p: P) -> P:
  Wr.feed_buf(~Ask, ~P, ~wstep, ~wadv, e, s, p)

def reads(+e: Ask, rs: List<&2, Bytes()>, p: P) -> P:
  Wr.reads(~Ask, ~P, ~wstep, ~wadv, e, rs, p)

# Taking the body as it comes
# ===========================
#
# A client that streams a body (wire/stream.bend) takes what the reader
# has gathered of it after each read, and the reader goes on holding
# none: take answers the body bytes the state holds -- a body's, a
# chunk's data's or a close-delimited body's so far, or a final
# response's -- and the state without them; give puts bytes back in
# front. A state is open once the head is behind it (a body, the final
# response, or a refusal): only an open state holds body bytes, and one
# never steps back out. PROOF.bend proves the kit's obligations of the
# three, and gets drain_reads: the chunks taken after each read, joined,
# then what the reader still holds, are the body the reader frames for
# the stream whole, however it was cut.
def st.open(st: St) -> Bool:
  match st:
    case SVer{a, b}:
      False{}
    case SCode{v10, n, k}:
      False{}
    case SWhy{v10, code}:
      False{}
    case Eol{h}:
      False{}
    case Lin{h}:
      False{}
    case Nam{h, cl, te, co}:
      False{}
    case Oth{h}:
      False{}
    case Len0{h}:
      False{}
    case Len{h, n}:
      False{}
    case LenW{h, n}:
      False{}
    case Te0{h}:
      False{}
    case Te{h, m}:
      False{}
    case Conn{h, cl, ka, mc, mk}:
      False{}
    case Eoh{h}:
      False{}
    case Bod{h, more, got}:
      True{}
    case Chk{h, at, n, got, left}:
      True{}
    case Dat{h, more, got, left}:
      True{}
    case Clo{h, got, left}:
      True{}
    case Fin{r, rest}:
      True{}
    case Bad{}:
      True{}

def open(p: P) -> Bool:
  match p:
    case P{st, out}:
      st.open(st)

def resp.give(+g: Bytes(), r: Resp) -> Resp:
  match r:
    case Resp{code, v10, close, body}:
      Resp{code, v10, close, Bytes.append(g, body)}

def st.give(+g: Bytes(), st: St) -> St:
  match st:
    case SVer{a, b}:
      SVer{a, b}
    case SCode{v10, n, k}:
      SCode{v10, n, k}
    case SWhy{v10, code}:
      SWhy{v10, code}
    case Eol{h}:
      Eol{h}
    case Lin{h}:
      Lin{h}
    case Nam{h, cl, te, co}:
      Nam{h, cl, te, co}
    case Oth{h}:
      Oth{h}
    case Len0{h}:
      Len0{h}
    case Len{h, n}:
      Len{h, n}
    case LenW{h, n}:
      LenW{h, n}
    case Te0{h}:
      Te0{h}
    case Te{h, m}:
      Te{h, m}
    case Conn{h, cl, ka, mc, mk}:
      Conn{h, cl, ka, mc, mk}
    case Eoh{h}:
      Eoh{h}
    case Bod{h, more, got}:
      Bod{h, more, Bytes.append(g, got)}
    case Chk{h, at, n, got, left}:
      Chk{h, at, n, Bytes.append(g, got), left}
    case Dat{h, more, got, left}:
      Dat{h, more, Bytes.append(g, got), left}
    case Clo{h, got, left}:
      Clo{h, Bytes.append(g, got), left}
    case Fin{r, rest}:
      Fin{resp.give(g, r), rest}
    case Bad{}:
      Bad{}

def give(+g: Bytes(), p: P) -> P:
  match p:
    case P{st, out}:
      P{st.give(g, st), out}

# give with the kit's shape
def wgive(g: Bytes(), p: P) -> P:
  give(g, p)

def resp.take(r: Resp, rest: Bytes()) -> St & Bytes():
  match r:
    case Resp{code, v10, close, body}:
      (Fin{Resp{code, v10, close, ""}, rest}, body)

def st.take(st: St) -> St & Bytes():
  match st:
    case SVer{a, b}:
      (SVer{a, b}, "")
    case SCode{v10, n, k}:
      (SCode{v10, n, k}, "")
    case SWhy{v10, code}:
      (SWhy{v10, code}, "")
    case Eol{h}:
      (Eol{h}, "")
    case Lin{h}:
      (Lin{h}, "")
    case Nam{h, cl, te, co}:
      (Nam{h, cl, te, co}, "")
    case Oth{h}:
      (Oth{h}, "")
    case Len0{h}:
      (Len0{h}, "")
    case Len{h, n}:
      (Len{h, n}, "")
    case LenW{h, n}:
      (LenW{h, n}, "")
    case Te0{h}:
      (Te0{h}, "")
    case Te{h, m}:
      (Te{h, m}, "")
    case Conn{h, cl, ka, mc, mk}:
      (Conn{h, cl, ka, mc, mk}, "")
    case Eoh{h}:
      (Eoh{h}, "")
    case Bod{h, more, got}:
      (Bod{h, more, ""}, got)
    case Chk{h, at, n, got, left}:
      (Chk{h, at, n, "", left}, got)
    case Dat{h, more, got, left}:
      (Dat{h, more, "", left}, got)
    case Clo{h, got, left}:
      (Clo{h, "", left}, got)
    case Fin{r, rest}:
      resp.take(r, rest)
    case Bad{}:
      (Bad{}, "")

def take.at(q: St & Bytes(), out: List<&2, U32>) -> P & Bytes():
  (st, x) = q
  (P{st, out}, x)

def take(p: P) -> P & Bytes():
  match p:
    case P{st, out}:
      take.at(st.take(st), out)

# whether a head is in progress: the reader is in a status line or a
# field line, or between two lines of a head (a client caps the bytes
# read while one is)
def mid(p: P) -> Bool:
  match p:
    case P{st, out}:
      match st:
        case Bod{h, more, got}:
          False{}
        case Chk{h, at, n, got, left}:
          False{}
        case Dat{h, more, got, left}:
          False{}
        case Clo{h, got, left}:
          False{}
        case Fin{r, rest}:
          False{}
        case Bad{}:
          False{}
        case _:
          True{}

# What the reader has read
# ========================
#
# The reader seen from outside, as spec.bend's framing says it: the
# interim statuses, oldest first, and how it ends -- still reading,
# refused, a final response with the bytes after it, or a body that runs
# to the close, with as much of it as has come (whole once the peer
# closes).
type End is Data:
  Open{}
  Refused{}
  Final{r: Resp, rest: Bytes()}
  Closing{r: Resp}

type Look is Data:
  Look{interim: List<&2, U32>, end: End}

def look.st(st: St) -> End:
  match st:
    case Bad{}:
      Refused{}
    case Fin{r, rest}:
      Final{r, rest}
    case Clo{h, got, left}:
      Closing{final(h, got, True{})}
    case _:
      Open{}

def look(p: P) -> Look:
  match p:
    case P{st, out}:
      Look{List.reverse(&2, U32, out), look.st(st)}
