# HTTP/2 frames (RFC 9113 4), read and written.
#
# The reader is a reader in bend-wire's sense: one byte-step machine
# over whatever a read hands it, the whole state in one value, a
# refusal absorbing. It reads the client's connection preface (RFC 9113
# 3.4), then frames: a 9-octet header -- a 24-bit length, a type, the
# flags, a reserved bit and a 31-bit stream identifier -- and then
# exactly length octets of payload. A frame longer than our
# SETTINGS_MAX_FRAME_SIZE is refused at its header (4.2: a
# FRAME_SIZE_ERROR), before a byte of its payload is kept. What a
# frame's payload means is the connection's (conn.bend); the reader
# only cuts the stream into frames, and spec.bend says how, from the
# RFC, and LAWS.bend that the two agree for every input.
import Base
import ../../wire/reader.bend as Wr

# a frame: its type, flags, stream and payload
type Frm is Data:
  Frm{ty: U32, fl: U32, sid: U32, pay: Bytes()}

# why the stream was refused: the preface was wrong, or a frame was
# longer than SETTINGS_MAX_FRAME_SIZE
type Why is Data:
  WPre{}
  WSize{}

# the client connection preface (RFC 9113 3.4)
def preface() -> List<&2, U32>:
  Wr.bytes("PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n")

# The fields of a frame header (RFC 9113 4.1), from its nine octets: a
# 24-bit length, the type, the flags, and the stream identifier with
# its reserved high bit dropped.
def u24(+a: U32, +b: U32, +c: U32) -> Nat:
  Nat.add(Nat.mul(U32.to_nat(a), 65536n), Nat.add(Nat.mul(U32.to_nat(b), 256n), U32.to_nat(c)))

def u31(+a: U32, +b: U32, +c: U32, +d: U32) -> U32:
  U32.or(U32.shln(U32.and(a, 127), 24n), U32.or(U32.shln(b, 16n), U32.or(U32.shln(c, 8n), d)))

# Where the reader is:
# FPre   in the preface, these bytes of it still to come
# FHd    in a frame header: left more bytes after the next, those so far
#        newest first
# FPay   in a payload: the header's fields, left more after the next,
#        the payload so far
# FBad   refused; absorbing, never left
type Fs is Data:
  FPre{rest: List<&2, U32>}
  FHd{left: Nat, h: List<&2, U32>}
  FPay{ty: U32, fl: U32, sid: U32, left: Nat, acc: Bytes()}
  FBad{why: Why}

# the reader: where it is, our SETTINGS_MAX_FRAME_SIZE, and the frames
# completed so far, newest first
type Rd is Data:
  Rd{at: Fs, max: Nat, out: List<&2, Frm>}

def hd.start() -> Fs:
  FHd{8n, Nil{}}

def new(max: Nat) -> Rd:
  Rd{FPre{preface()}, max, Nil{}}

# the preface: each byte the one expected, and after the last, frames
def step.pre.go(ok: Bool, t: List<&2, U32>, max: Nat, out: List<&2, Frm>) -> Rd:
  match ok t:
    case False{} _:
      Rd{FBad{WPre{}}, max, out}
    case True{} Nil{}:
      Rd{hd.start(), max, out}
    case True{} Con{p, u}:
      Rd{FPre{Con{p, u}}, max, out}

def step.pre(ps: List<&2, U32>, +max: Nat, out: List<&2, Frm>, +c: U32) -> Rd:
  match ps:
    case Nil{}:
      Rd{FBad{WPre{}}, max, out}
    case Con{p, t}:
      step.pre.go(U32.is_eq(c, p), t, max, out)

# a header complete: a frame past the maximum is refused; an empty
# payload completes the frame at once
def step.len(big: Bool, n: Nat, +ty: U32, +fl: U32, +sid: U32, +max: Nat, out: List<&2, Frm>) -> Rd:
  match big n:
    case True{} _:
      Rd{FBad{WSize{}}, max, out}
    case False{} 0n:
      Rd{hd.start(), max, Con{Frm{ty, fl, sid, ""}, out}}
    case False{} 1n+m:
      Rd{FPay{ty, fl, sid, m, ""}, max, out}

def step.hd9(+h: List<&2, U32>, +max: Nat, out: List<&2, Frm>) -> Rd:
  match h:
    case Con{b8, Con{b7, Con{b6, Con{b5, Con{b4, Con{b3, Con{b2, Con{b1, Con{b0, Nil{}}}}}}}}}}:
      +n = u24(b0, b1, b2)
      step.len(Nat.is_lt(max, n), n, b3, b4, u31(b5, b6, b7, b8), max, out)
    case _:
      Rd{FBad{WSize{}}, max, out}

def step.hd(left: Nat, h: List<&2, U32>, +max: Nat, out: List<&2, Frm>, +c: U32) -> Rd:
  match left:
    case 0n:
      step.hd9(Con{c, h}, max, out)
    case 1n+l:
      Rd{FHd{l, Con{c, h}}, max, out}

# a payload byte: the last completes the frame
def step.pay(+ty: U32, +fl: U32, +sid: U32, left: Nat, acc: Bytes(), +max: Nat, out: List<&2, Frm>, c: U32) -> Rd:
  match left:
    case 0n:
      Rd{hd.start(), max, Con{Frm{ty, fl, sid, Bytes.push(acc, c)}, out}}
    case 1n+l:
      Rd{FPay{ty, fl, sid, l, Bytes.push(acc, c)}, max, out}

def step(r: Rd, +c: U32) -> Rd:
  match r:
    case Rd{at, +max, out}:
      match at:
        case FPre{ps}:
          step.pre(ps, max, out, c)
        case FHd{left, h}:
          step.hd(left, h, max, out, c)
        case FPay{ty, fl, sid, left, acc}:
          step.pay(ty, fl, sid, left, acc, max, out, c)
        case FBad{why}:
          Rd{FBad{why}, max, out}

# The walk, from the kit: nothing beside the state, one byte a move.
def wstep(u: Unit, r: Rd, c: U32) -> Rd:
  step(r, c)

def wadv(u: Unit, s: Bytes(), r: Rd) -> Rd & Bytes():
  Wr.one.step(~Unit, ~Rd, ~wstep, u, s, r)

def feed(bs: List<&2, U32>, r: Rd) -> Rd:
  Wr.feed(~Unit, ~Rd, ~wstep, Unit{}, bs, r)

def feed_buf(+s: Bytes(), r: Rd) -> Rd:
  Wr.feed_buf(~Unit, ~Rd, ~wstep, ~wadv, Unit{}, s, r)

# the frames completed so far, oldest first, and the reader emptied of
# them; and whether it has refused
def take(r: Rd) -> Rd & List<&2, Frm>:
  match r:
    case Rd{at, max, out}:
      (Rd{at, max, Nil{}}, List.reverse(&2, Frm, out))

def refused(r: Rd) -> Maybe<&2, Why>:
  match r:
    case Rd{at, max, out}:
      match at:
        case FBad{why}:
          Some{why}
        case _:
          None{}

# Writing a frame: its header, then its payload.
def put24(+n: U32) -> List<&2, U32>:
  [U32.and(U32.shrn(n, 16n), 255), U32.and(U32.shrn(n, 8n), 255), U32.and(n, 255)]

def put32(+n: U32) -> List<&2, U32>:
  [U32.and(U32.shrn(n, 24n), 255), U32.and(U32.shrn(n, 16n), 255), U32.and(U32.shrn(n, 8n), 255),
   U32.and(n, 255)]

def head(+len: U32, ty: U32, fl: U32, +sid: U32) -> Bytes():
  Bytes.from_list(List.append(&2, U32, put24(len), Con{ty, Con{fl, put32(sid)}}))

def frame(ty: U32, fl: U32, +sid: U32, +pay: Bytes()) -> Bytes():
  Bytes.append(head(U32.from_nat(Bytes.len(pay)), ty, fl, sid), pay)
