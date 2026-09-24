# The references the server is held to. First the framing, RFC 9113 3.4 and 4.1-4.2,
# written for whoever checks it rather than for the clock. The client
# sends the 24-octet connection preface, then frames; a frame is nine
# octets of header -- Length (24 bits), Type, Flags, a reserved bit and
# the Stream Identifier (31 bits) -- followed by exactly Length octets
# of payload; and a frame whose Length exceeds SETTINGS_MAX_FRAME_SIZE
# is a FRAME_SIZE_ERROR. Here that is said with take and drop over the
# whole input, which is not how the reader goes about it: the reader
# walks a byte at a time, and LAWS.bend says the two agree for every
# input.
import Base
import ../../wire/reader.bend as Wr
import ./frame.bend as Fm
import ./conn.bend as C

# 3.4: PRI * HTTP/2.0 CRLF CRLF SM CRLF CRLF
def preface() -> List<&2, U32>:
  Wr.bytes("PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n")

# how an input begins: short of the whole preface, not with it, or with
# it and then the rest
type Pre is Data:
  PMore{}
  PBad{}
  PDone{rest: List<&2, U32>}

def pre.on(ok: Bool, r: Pre) -> Pre:
  match ok:
    case True{}:
      r
    case False{}:
      PBad{}

def pre(ps: List<&2, U32>, bs: List<&2, U32>) -> Pre:
  match ps bs:
    case Nil{} _:
      PDone{bs}
    case Con{p, pt} Nil{}:
      PMore{}
    case Con{p, pt} Con{c, t}:
      pre.on(U32.is_eq(c, p), pre(pt, t))

# the first n of bs and the rest, when bs has n
type Two is Data:
  Two{a: List<&2, U32>, b: List<&2, U32>}

def take.on(+c: U32, m: Maybe<&2, Two>) ->
  Maybe<&2, Two>:
  match m:
    case None{}:
      None{}
    case Some{ab}:
      match ab:
        case Two{a, b}:
          Some{Two{Con{c, a}, b}}

def take(n: Nat, bs: List<&2, U32>) -> Maybe<&2, Two>:
  match n bs:
    case 0n _:
      Some{Two{Nil{}, bs}}
    case 1n+m Nil{}:
      None{}
    case 1n+m Con{c, t}:
      take.on(c, take(m, t))

# 4.1: the header's fields. Length is a 24-bit unsigned integer; the
# Stream Identifier is 31 bits, the reserved bit before it ignored.
def len24(+a: U32, +b: U32, +c: U32) -> Nat:
  Nat.add(Nat.mul(U32.to_nat(a), 65536n), Nat.add(Nat.mul(U32.to_nat(b), 256n), U32.to_nat(c)))

def sid31(+a: U32, +b: U32, +c: U32, +d: U32) -> U32:
  U32.or(U32.shln(U32.and(a, 127), 24n), U32.or(U32.shln(b, 16n), U32.or(U32.shln(c, 8n), d)))

# what comes next in the input: too little for a frame yet, a frame
# past the maximum, or a frame and the input after it
type Cut is Data:
  CShort{}
  CBig{}
  CFrm{f: Fm.Frm, rest: List<&2, U32>}

def cut.pay(+ty: U32, +fl: U32, +sid: U32, m: Maybe<&2, Two>) -> Cut:
  match m:
    case None{}:
      CShort{}
    case Some{pr}:
      match pr:
        case Two{p, r}:
          CFrm{Fm.Frm{ty, fl, sid, Bytes.from_list(p)}, r}

# 4.2: a Length past SETTINGS_MAX_FRAME_SIZE is refused
def cut.len(big: Bool, +n: Nat, +ty: U32, +fl: U32, +sid: U32, rest: List<&2, U32>) -> Cut:
  match big:
    case True{}:
      CBig{}
    case False{}:
      cut.pay(ty, fl, sid, take(n, rest))

def cut.hd(+max: Nat, m: Maybe<&2, Two>) -> Cut:
  match m:
    case None{}:
      CShort{}
    case Some{hr}:
      match hr:
        case Two{h, rest}:
          match h:
            case [b0, b1, b2, b3, b4, b5, b6, b7, b8]:
              +n = len24(b0, b1, b2)
              cut.len(Nat.is_lt(max, n), n, b3, b4, sid31(b5, b6, b7, b8), rest)
            case _:
              CShort{}

def cut(+max: Nat, bs: List<&2, U32>) -> Cut:
  cut.hd(max, take(9n, bs))

# What an input is: the frames it holds, newest first, and how it ends --
# inside the preface, open (the bytes after the last whole frame), or
# refused.
type End is Data:
  Pre{rest: List<&2, U32>}
  Open{rest: List<&2, U32>}
  Refused{why: Fm.Why}

type Frames is Data:
  Frames{fs: List<&2, Fm.Frm>, end: End}

# frame after frame; each takes at least nine bytes, so the input's
# length bounds how many
def go(fuel: Nat, +max: Nat, bs: List<&2, U32>, c: Cut, out: List<&2, Fm.Frm>) -> Frames:
  match fuel c:
    case 0n _:
      Frames{out, Open{bs}}
    case 1n+f CShort{}:
      Frames{out, Open{bs}}
    case 1n+f CBig{}:
      Frames{out, Refused{Fm.WSize{}}}
    case 1n+f CFrm{fr, +rest}:
      go(f, max, rest, cut(max, rest), Con{fr, out})

def frames.pre(+max: Nat, bs: List<&2, U32>, p: Pre) -> Frames:
  match p:
    case PMore{}:
      Frames{Nil{}, Pre{bs}}
    case PBad{}:
      Frames{Nil{}, Refused{Fm.WPre{}}}
    case PDone{+rest}:
      go(List.length(&2, U32, rest), max, rest, cut(max, rest), Nil{})

# a whole input
def frames(+max: Nat, +bs: List<&2, U32>) -> Frames:
  frames.pre(max, bs, pre(preface(), bs))

# 5.1: what a frame the client sends on a stream may do, by the stream's
# state, read off the RFC's text state by state: the frames each state
# permits, and what any other earns.
#
#   idle: "Receiving any frame other than HEADERS or PRIORITY on a
#     stream in this state MUST be treated as a connection error of type
#     PROTOCOL_ERROR."
#   open: "may be used by both peers to send frames of any type"
#   half-closed (local): "An endpoint can receive any type of frame in
#     this state."
#   half-closed (remote): "If an endpoint receives additional frames,
#     other than WINDOW_UPDATE, PRIORITY, or RST_STREAM, for a stream
#     that is in this state, it MUST respond with a stream error of type
#     STREAM_CLOSED."
#   closed: WINDOW_UPDATE, PRIORITY and RST_STREAM may still arrive for a
#     short while; "An endpoint that receives any frames after receiving
#     a frame with the END_STREAM flag set MUST treat that as a
#     connection error of type STREAM_CLOSED."
#   closed by our RST_STREAM: "the endpoint MUST ignore frames that it
#     receives on closed streams after it has sent a RST_STREAM frame"
def code(t: C.Ty) -> Nat:
  match t:
    case C.TData{}:
      0n
    case C.THeaders{}:
      1n
    case C.TPrio{}:
      2n
    case C.TRst{}:
      3n
    case C.TSettings{}:
      4n
    case C.TPush{}:
      5n
    case C.TPing{}:
      6n
    case C.TGoaway{}:
      7n
    case C.TWin{}:
      8n
    case C.TCont{}:
      9n
    case C.TOther{}:
      10n

def any() -> List<&2, C.Ty>:
  [C.TData{}, C.THeaders{}, C.TPrio{}, C.TRst{}, C.TSettings{}, C.TPush{}, C.TPing{}, C.TGoaway{},
   C.TWin{}, C.TCont{}, C.TOther{}]

def permits(s: C.Ss) -> List<&2, C.Ty>:
  match s:
    case C.SIdle{}:
      [C.THeaders{}, C.TPrio{}]
    case C.SOpen{}:
      any()
    case C.SLocal{}:
      any()
    case C.SReset{}:
      any()
    case C.SHalf{}:
      [C.TWin{}, C.TPrio{}, C.TRst{}]
    case C.SClosed{}:
      [C.TWin{}, C.TPrio{}, C.TRst{}]

def otherwise(s: C.Ss) -> C.Vd:
  match s:
    case C.SIdle{}:
      C.VConn{1}
    case C.SHalf{}:
      C.VStream{5}
    case C.SClosed{}:
      C.VConn{5}
    case _:
      C.VOk{}

def has(+t: C.Ty, ts: List<&2, C.Ty>) -> Bool:
  match ts:
    case Nil{}:
      False{}
    case Con{u, rest}:
      Nat.is_eq(code(t), code(u)) || has(t, rest)

def verdict.pick(ok: Bool, s: C.Ss) -> C.Vd:
  match ok:
    case True{}:
      C.VOk{}
    case False{}:
      otherwise(s)

def verdict(+s: C.Ss, +t: C.Ty) -> C.Vd:
  verdict.pick(has(t, permits(s)), s)
