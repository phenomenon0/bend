# WebSocket (RFC 6455): the frames, in and out, and the handshake's
# accept key. The reader has the request reader's shape -- one
# structural walk over whatever bytes arrive, its whole state in one W
# node -- so a frame split across reads parses like one that arrived
# whole, and LAWS.bend pins the chunking law the same way. What it
# accepts is deliberately small: client frames are masked or the
# connection is failed, as the RFC requires; fragments and reserved
# bits are refused; a payload past the cap is refused before a byte of
# it is read. It runs the echo service: text and binary come back as
# they came, a ping is answered with a pong, a close with a close.
import Base
import ./sha1.bend as Sha1
import ./b64.bend as B64

# Handshake
# =========

def ascii(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{Chr{c}, t}:
      Con{c, ascii(t)}

def guid() -> List<&2, U32>:
  ascii("258EAFA5-E914-47DA-95CA-C5AB0DC85B11")

# the accept key: base64 of the SHA-1 of the client's key joined to
# the GUID
def accept(key: List<&2, U32>) -> List<&2, U32>:
  B64.enc(Sha1.hash(List.append(&2, U32, key, guid())))

# Frames
# ======

# a complete frame: its opcode and its unmasked payload
type Frm is Data:
  Frm{op: U32, body: List<&2, U32>}

# Op   the first byte: FIN, reserved bits, opcode
# Len  the second: the mask bit and the length, or how long the length is
# Ext  the extended length, need bytes to go, len so far
# Msk  the mask, need bytes to go, collected (reversed)
# Pay  the payload, rem bytes to go, the mask rotating, kept (reversed)
# Bad  the framing broke; absorbing, and never left
type Fs is Data:
  Op{}
  Len{op: U32}
  Ext{op: U32, need: U32, len: U32}
  Msk{op: U32, len: U32, need: U32, m: List<&2, U32>}
  Pay{op: U32, rem: U32, m: List<&2, U32>, acc: List<&2, U32>}
  Bad{}

# the whole reader: where it is, and the frames done, newest first
type W is Data:
  W{st: Fs, out: List<&2, Frm>}

def new() -> W:
  W{Op{}, Nil{}}

# the most payload one frame may carry
def cap() -> U32:
  1048576

def emit(op: U32, body: List<&2, U32>, out: List<&2, Frm>) -> W:
  W{Op{}, Con{Frm{op, body}, out}}

# the first byte: FIN set, no reserved bits, an opcode this reader knows
def known(+op: U32) -> Bool:
  U32.is_eq(op, 1) || U32.is_eq(op, 2) || U32.is_eq(op, 8) || U32.is_eq(op, 9)
    || U32.is_eq(op, 10)

def step.op.go(op: U32, ok: Bool) -> Fs:
  match ok:
    case True{}:
      Len{op}
    case False{}:
      Bad{}

def step.op(+b: U32) -> Fs:
  step.op.go(U32.and(b, 15), U32.is_eq(U32.and(b, 128), 128)
    && U32.is_zero(U32.and(b, 112)) && known(U32.and(b, 15)))

# the second byte: the mask bit is required; the low seven bits are the
# length, or 126 for two more bytes of it, or 127 for eight
def step.len.on(op: U32, n: U32, two: Bool, eight: Bool) -> Fs:
  match two eight:
    case True{} _:
      Ext{op, 2, 0}
    case False{} True{}:
      Ext{op, 8, 0}
    case False{} False{}:
      Msk{op, n, 4, Nil{}}

def step.len.go(op: U32, +n: U32, masked: Bool) -> Fs:
  match masked:
    case False{}:
      Bad{}
    case True{}:
      step.len.on(op, n, U32.is_eq(n, 126), U32.is_eq(n, 127))

def step.len(op: U32, +b: U32) -> Fs:
  step.len.go(op, U32.and(b, 127), U32.is_eq(U32.and(b, 128), 128))

# the extended length, big-endian; a length past the cap is refused as
# soon as it shows, which is before any byte of an eight-byte length
# could wrap
def step.ext.go(op: U32, left: U32, len2: U32, big: Bool, done: Bool) -> Fs:
  match big done:
    case True{} _:
      Bad{}
    case False{} True{}:
      Msk{op, len2, 4, Nil{}}
    case False{} False{}:
      Ext{op, left, len2}

def step.ext.on(op: U32, +left: U32, +len2: U32) -> Fs:
  step.ext.go(op, left, len2, U32.is_lt(cap(), len2), U32.is_zero(left))

def step.ext(op: U32, need: U32, len: U32, b: U32) -> Fs:
  step.ext.on(op, (need - 1 : U32), ((len * 256 : U32) + b : U32))

# the four mask bytes; an empty payload is a frame the moment the mask
# is in
def step.msk.on(
  op: U32, len: U32, left: U32, m2: List<&2, U32>, out: List<&2, Frm>,
  last: Bool, empty: Bool
) -> W:
  match last empty:
    case False{} _:
      W{Msk{op, len, left, m2}, out}
    case True{} True{}:
      emit(op, Nil{}, out)
    case True{} False{}:
      W{Pay{op, len, List.reverse(&2, U32, m2), Nil{}}, out}

def step.msk(
  op: U32, +len: U32, +need: U32, m: List<&2, U32>, b: U32, out: List<&2, Frm>
) -> W:
  step.msk.on(op, len, (need - 1 : U32), Con{b, m}, out, U32.is_eq(need, 1),
    U32.is_zero(len))

# the payload, unmasked byte by byte with the key rotating
def rot(m: List<&2, U32>) -> List<&2, U32>:
  match m:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      List.append(&2, U32, t, [h])

def key.of(m: List<&2, U32>) -> U32:
  match m:
    case Nil{}:
      0
    case Con{h, t}:
      h

def step.pay.on(
  op: U32, left: U32, m2: List<&2, U32>, acc2: List<&2, U32>, out: List<&2, Frm>,
  last: Bool
) -> W:
  match last:
    case True{}:
      emit(op, List.reverse(&2, U32, acc2), out)
    case False{}:
      W{Pay{op, left, m2, acc2}, out}

def step.pay(
  op: U32, +rem: U32, +m: List<&2, U32>, acc: List<&2, U32>, b: U32,
  out: List<&2, Frm>
) -> W:
  step.pay.on(op, (rem - 1 : U32), rot(m), Con{U32.xor(b, key.of(m)), acc}, out,
    U32.is_eq(rem, 1))

def step.at(st: Fs, out: List<&2, Frm>, b: U32) -> W:
  match st:
    case Op{}:
      W{step.op(b), out}
    case Len{op}:
      W{step.len(op, b), out}
    case Ext{op, need, len}:
      W{step.ext(op, need, len, b), out}
    case Msk{op, len, need, m}:
      step.msk(op, len, need, m, b, out)
    case Pay{op, rem, m, acc}:
      step.pay(op, rem, m, acc, b, out)
    case Bad{}:
      W{Bad{}, out}

def step(w: W, b: U32) -> W:
  match w:
    case W{st, out}:
      step.at(st, out, b)

# one structural walk over a chunk; the state that comes out is the
# state to feed the next chunk
def feed(bs: List<&2, U32>, w: W) -> W:
  match bs:
    case Nil{}:
      w
    case Con{b, t}:
      feed(t, step(w, b))

# the frames completed so far, oldest first, and the reader emptied
def take(w: W) -> W & List<&2, Frm>:
  match w:
    case W{st, out}:
      (W{st, Nil{}}, List.reverse(&2, Frm, out))

def dead.at(st: Fs, out: List<&2, Frm>) -> W & Bool:
  match st:
    case Op{}:
      (W{Op{}, out}, False{})
    case Len{op}:
      (W{Len{op}, out}, False{})
    case Ext{op, need, len}:
      (W{Ext{op, need, len}, out}, False{})
    case Msk{op, len, need, m}:
      (W{Msk{op, len, need, m}, out}, False{})
    case Pay{op, rem, m, acc}:
      (W{Pay{op, rem, m, acc}, out}, False{})
    case Bad{}:
      (W{Bad{}, out}, True{})

# whether the framing broke, with the reader handed back
def dead(w: W) -> W & Bool:
  match w:
    case W{st, out}:
      dead.at(st, out)

# Writing
# =======

# the length: one byte under 126, 126 and two bytes under 65536, 127
# and eight bytes past that
def len.go(+n: U32, small: Bool, mid: Bool) -> List<&2, U32>:
  match small mid:
    case True{} _:
      [n]
    case False{} True{}:
      [126, Sha1.byte(Sha1.sr(8n, n)), Sha1.byte(n)]
    case False{} False{}:
      [127, 0, 0, 0, 0, Sha1.byte(Sha1.sr(24n, n)), Sha1.byte(Sha1.sr(16n, n)),
       Sha1.byte(Sha1.sr(8n, n)), Sha1.byte(n)]

def len.bytes(+n: U32) -> List<&2, U32>:
  len.go(n, U32.is_lt(n, 126), U32.is_lt(n, 65536))

# a server frame: FIN and the opcode, the length, the payload, no mask
def frame(op: U32, +body: List<&2, U32>) -> List<&2, U32>:
  Con{U32.or(128, op),
    List.append(&2, U32, len.bytes(U32.from_nat(List.length(&2, U32, body))), body)}

def close.frame(+code: U32) -> List<&2, U32>:
  frame(8, [Sha1.byte(Sha1.sr(8n, code)), Sha1.byte(code)])

# Answering
# =========

# what to write back for the frames one read completed, and whether the
# connection ends after it
type Rep is Data:
  Rep{out: List<&2, U32>, close: Bool}

# a close is answered with the peer's status code if it sent one; a
# one-byte payload is not a code and gets 1002
def close.echo(body: List<&2, U32>) -> List<&2, U32>:
  match body:
    case Nil{}:
      close.frame(1000)
    case Con{a, t}:
      match t:
        case Nil{}:
          close.frame(1002)
        case Con{b, u}:
          frame(8, [a, b])

def rep.op(op: U32, body: List<&2, U32>, is_close: Bool, is_ping: Bool, is_pong: Bool) -> Rep:
  match is_close is_ping is_pong:
    case True{} _ _:
      Rep{close.echo(body), True{}}
    case False{} True{} _:
      Rep{frame(10, body), False{}}
    case False{} False{} True{}:
      Rep{Nil{}, False{}}
    case False{} False{} False{}:
      Rep{frame(op, body), False{}}

def rep.one(f: Frm) -> Rep:
  match f:
    case Frm{+op, body}:
      rep.op(op, body, U32.is_eq(op, 8), U32.is_eq(op, 9), U32.is_eq(op, 10))

# nothing follows a close
def rep.cat.go(o1: List<&2, U32>, c1: Bool, b: Rep) -> Rep:
  match c1:
    case True{}:
      Rep{o1, True{}}
    case False{}:
      match b:
        case Rep{o2, c2}:
          Rep{List.append(&2, U32, o1, o2), c2}

def rep.cat(a: Rep, b: Rep) -> Rep:
  match a:
    case Rep{o1, c1}:
      rep.cat.go(o1, c1, b)

def reply.go(fs: List<&2, Frm>) -> Rep:
  match fs:
    case Nil{}:
      Rep{Nil{}, False{}}
    case Con{f, t}:
      rep.cat(rep.one(f), reply.go(t))

# a broken frame ends the connection with 1002, after whatever the
# good ones before it earned
def reply.bad(bad: Bool, r: Rep) -> Rep:
  match bad:
    case False{}:
      r
    case True{}:
      match r:
        case Rep{o, c}:
          Rep{List.append(&2, U32, o, close.frame(1002)), True{}}

def reply(fs: List<&2, Frm>, bad: Bool) -> Rep:
  reply.bad(bad, reply.go(fs))
