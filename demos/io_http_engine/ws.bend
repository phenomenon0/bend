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

# a complete frame: its opcode and its unmasked payload, one block
type Frm is Data:
  Frm{op: U32, body: Bytes()}

# Op   the first byte: FIN, reserved bits, opcode
# Len  the second: the mask bit and the length, or how long the length is
# Ext  the extended length, need bytes to go, len so far, and the least
#      length its form may carry (126 or 65536): a shorter one is refused
# Msk  the mask, need bytes to go, the bytes so far big-endian in a word
# Pay  the payload, rem bytes to go, the mask turned so its top byte is
#      the next key, the bytes unmasked so far (reversed)
# Bad  the framing broke; absorbing, and never left
type Fs is Data:
  Op{}
  Len{op: U32}
  Ext{op: U32, need: U32, len: U32, min: U32}
  Msk{op: U32, len: U32, need: U32, m: U32}
  Pay{op: U32, rem: U32, m: U32, acc: Bytes()}
  Bad{}

# the whole reader: where it is, and the frames done, newest first
type W is Data:
  W{st: Fs, out: List<&2, Frm>}

def new() -> W:
  W{Op{}, Nil{}}

# the most payload one frame may carry
def cap() -> U32:
  1048576

def emit(op: U32, body: Bytes(), out: List<&2, Frm>) -> W:
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
# length, or 126 for two more bytes of it, or 127 for eight. A control
# frame (opcode 8 and up) carries at most 125, so either marker on one
# is refused here.
def step.len.on(op: U32, n: U32, two: Bool, eight: Bool) -> Fs:
  match two eight:
    case True{} _:
      Ext{op, 2, 0, 126}
    case False{} True{}:
      Ext{op, 8, 0, 65536}
    case False{} False{}:
      Msk{op, n, 4, 0}

def step.len.go(op: U32, +n: U32, masked: Bool, long_ctl: Bool) -> Fs:
  match masked long_ctl:
    case False{} _:
      Bad{}
    case True{} True{}:
      Bad{}
    case True{} False{}:
      step.len.on(op, n, U32.is_eq(n, 126), U32.is_eq(n, 127))

def step.len(+op: U32, +b: U32) -> Fs:
  step.len.go(op, U32.and(b, 127), U32.is_eq(U32.and(b, 128), 128),
    U32.is_le(8, op) && U32.is_lt(125, U32.and(b, 127)))

# the extended length, big-endian; a length past the cap is refused as
# soon as it shows, which is before any byte of an eight-byte length
# could wrap, and a length its form did not need is refused at its last
# byte (RFC 6455 5.2: the minimal number of bytes)
def step.ext.go(
  op: U32, left: U32, len2: U32, min: U32, big: Bool, done: Bool, short: Bool
) -> Fs:
  match big done short:
    case True{} _ _:
      Bad{}
    case False{} True{} True{}:
      Bad{}
    case False{} True{} False{}:
      Msk{op, len2, 4, 0}
    case False{} False{} _:
      Ext{op, left, len2, min}

def step.ext.on(op: U32, +left: U32, +len2: U32, +min: U32) -> Fs:
  step.ext.go(op, left, len2, min, U32.is_lt(cap(), len2), U32.is_zero(left),
    U32.is_lt(len2, min))

def step.ext(op: U32, need: U32, len: U32, min: U32, b: U32) -> Fs:
  step.ext.on(op, (need - 1 : U32), ((len * 256 : U32) + b : U32), min)

# the four mask bytes, gathered into one word; an empty payload is a
# frame the moment the mask is in
def step.msk.on(
  op: U32, len: U32, left: U32, m2: U32, out: List<&2, Frm>, last: Bool,
  empty: Bool
) -> W:
  match last empty:
    case False{} _:
      W{Msk{op, len, left, m2}, out}
    case True{} True{}:
      emit(op, SNil{}, out)
    case True{} False{}:
      W{Pay{op, len, m2, SNil{}}, out}

def step.msk(
  op: U32, +len: U32, +need: U32, m: U32, b: U32, out: List<&2, Frm>
) -> W:
  step.msk.on(op, len, (need - 1 : U32), ((m * 256 : U32) + b : U32), out,
    U32.is_eq(need, 1), U32.is_zero(len))

# the payload, unmasked byte by byte: the key is the mask's top byte,
# and the mask turns a byte left after each
def key.of(+m: U32) -> U32:
  (m / 16777216 : U32)

def rot(+m: U32) -> U32:
  ((m * 256 : U32) + key.of(m) : U32)

# the payload is kept reversed, so each byte is a prepend, which the
# runtime does in place into the block's front room; one reverse at the
# end lays it out
def step.pay.on(
  op: U32, left: U32, m2: U32, acc2: Bytes(), out: List<&2, Frm>, last: Bool
) -> W:
  match last:
    case True{}:
      emit(op, String.reverse(acc2), out)
    case False{}:
      W{Pay{op, left, m2, acc2}, out}

def step.pay(
  op: U32, +rem: U32, +m: U32, acc: Bytes(), b: U32, out: List<&2, Frm>
) -> W:
  step.pay.on(op, (rem - 1 : U32), rot(m), SCon{Chr{U32.xor(b, key.of(m))}, acc},
    out, U32.is_eq(rem, 1))

def step.at(st: Fs, out: List<&2, Frm>, b: U32) -> W:
  match st:
    case Op{}:
      W{step.op(b), out}
    case Len{op}:
      W{step.len(op, b), out}
    case Ext{op, need, len, min}:
      W{step.ext(op, need, len, min, b), out}
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
# state to feed the next chunk. This is the reader's spec, over a list.
def feed(bs: List<&2, U32>, w: W) -> W:
  match bs:
    case Nil{}:
      w
    case Con{b, t}:
      feed(t, step(w, b))

# the same walk over a byte buffer, the one a connection reads: it
# steps the same machine, so it is feed of the buffer's bytes (LAWS.bend,
# ws_feed_buf). An uncons of a buffer nothing else holds advances it in
# place, so the walk allocates no cell per byte.
def feed_buf(b: Bytes(), w: W) -> W:
  match b:
    case SNil{}:
      w
    case SCon{Chr{c}, t}:
      feed_buf(t, step(w, c))

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
    case Ext{op, need, len, min}:
      (W{Ext{op, need, len, min}, out}, False{})
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

# UTF-8
# =====

# A text frame's payload must be UTF-8 (RFC 3629), or the connection is
# failed with 1007. The validator is a walk with its state in one node:
# need continuation bytes to go and the next one's range lo..hi, which
# is narrower than 80..BF right after E0, ED, F0 and F4 -- that is what
# refuses an overlong form, a surrogate and a code point past 10FFFF --
# or broken.
type Ut is Data:
  Ut{need: U32, lo: U32, hi: U32}
  Utx{}

def utf8.pick(c: Bool, a: Ut, b: Ut) -> Ut:
  match c:
    case True{}:
      a
    case False{}:
      b

def utf8.multi(+b: U32) -> Ut:
  utf8.pick(U32.is_lt(b, 194), Utx{},
  utf8.pick(U32.is_lt(b, 224), Ut{1, 128, 191},
  utf8.pick(U32.is_eq(b, 224), Ut{2, 160, 191},
  utf8.pick(U32.is_eq(b, 237), Ut{2, 128, 159},
  utf8.pick(U32.is_lt(b, 240), Ut{2, 128, 191},
  utf8.pick(U32.is_eq(b, 240), Ut{3, 144, 191},
  utf8.pick(U32.is_lt(b, 244), Ut{3, 128, 191},
  utf8.pick(U32.is_eq(b, 244), Ut{3, 128, 143}, Utx{}))))))))

def utf8.lead(+b: U32, ascii: Bool) -> Ut:
  match ascii:
    case True{}:
      Ut{0, 128, 191}
    case False{}:
      utf8.multi(b)

def utf8.at(need: U32, +lo: U32, +hi: U32, +b: U32, first: Bool) -> Ut:
  match first:
    case True{}:
      utf8.lead(b, U32.is_lt(b, 128))
    case False{}:
      utf8.pick(U32.is_le(lo, b) && U32.is_le(b, hi),
        Ut{(need - 1 : U32), 128, 191}, Utx{})

def utf8.step(s: Ut, b: U32) -> Ut:
  match s:
    case Ut{+need, lo, hi}:
      utf8.at(need, lo, hi, b, U32.is_zero(need))
    case Utx{}:
      Utx{}

def utf8.go(bs: Bytes(), s: Ut) -> Ut:
  match bs:
    case SNil{}:
      s
    case SCon{Chr{c}, t}:
      utf8.go(t, utf8.step(s, c))

def utf8.end(s: Ut) -> Bool:
  match s:
    case Ut{need, lo, hi}:
      U32.is_zero(need)
    case Utx{}:
      False{}

# whether the bytes are UTF-8; a character cut short at the end is not
def utf8(bs: Bytes()) -> Bool:
  utf8.end(utf8.go(bs, Ut{0, 128, 191}))

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

# a server frame, one block: FIN and the opcode, the length, the
# payload, no mask. The head is a few bytes; the payload is copied once,
# behind it.
def frame(op: U32, +body: Bytes()) -> Bytes():
  Bytes.append(
    Bytes.from_list(Con{U32.or(128, op), len.bytes(U32.from_nat(Bytes.len(body)))}),
    body)

def close.frame(+code: U32) -> Bytes():
  frame(8, Bytes.from_list([Sha1.byte(Sha1.sr(8n, code)), Sha1.byte(code)]))

# Answering
# =========

# what to write back for the frames one read completed, and whether the
# connection ends after it
type Rep is Data:
  Rep{out: Bytes(), close: Bool}

# the status codes a peer may send (RFC 6455 7.4 and the IANA registry):
# 1000-1003, 1007-1014, and 3000-4999 for libraries and applications.
# 0-999, 1004-1006, 1015 and 1016-2999 are reserved or never sent, and
# nothing past 4999 is a code.
def close.code.ok(+c: U32) -> Bool:
  (U32.is_le(1000, c) && U32.is_le(c, 1003)) || (U32.is_le(1007, c) && U32.is_le(c, 1014))
    || (U32.is_le(3000, c) && U32.is_le(c, 4999))

def close.two(+a: U32, +b: U32, ok: Bool, text: Bool) -> Bytes():
  match ok text:
    case False{} _:
      close.frame(1002)
    case True{} False{}:
      close.frame(1007)
    case True{} True{}:
      frame(8, Bytes.from_list([a, b]))

# a close is answered with the peer's status code if it sent one a peer
# may send; a one-byte payload or any other code gets 1002, and a reason
# that is not UTF-8 gets 1007
def close.echo(body: Bytes()) -> Bytes():
  match body:
    case SNil{}:
      close.frame(1000)
    case SCon{Chr{+a}, t}:
      match t:
        case SNil{}:
          close.frame(1002)
        case SCon{Chr{+b}, u}:
          close.two(a, b, close.code.ok(((a * 256 : U32) + b : U32)), utf8(u))

# text must be UTF-8; binary is whatever it is
def data.ok(+body: Bytes(), bin: Bool) -> Bool:
  match bin:
    case True{}:
      True{}
    case False{}:
      utf8(body)

def rep.data(op: U32, +body: Bytes(), ok: Bool) -> Rep:
  match ok:
    case True{}:
      Rep{frame(op, body), False{}}
    case False{}:
      Rep{close.frame(1007), True{}}

def rep.op(
  +op: U32, +body: Bytes(), is_close: Bool, is_ping: Bool, is_pong: Bool
) -> Rep:
  match is_close is_ping is_pong:
    case True{} _ _:
      Rep{close.echo(body), True{}}
    case False{} True{} _:
      Rep{frame(10, body), False{}}
    case False{} False{} True{}:
      Rep{SNil{}, False{}}
    case False{} False{} False{}:
      rep.data(op, body, data.ok(body, U32.is_eq(op, 2)))

def rep.one(f: Frm) -> Rep:
  match f:
    case Frm{+op, body}:
      rep.op(op, body, U32.is_eq(op, 8), U32.is_eq(op, 9), U32.is_eq(op, 10))

# nothing follows a close
def rep.cat.go(o1: Bytes(), c1: Bool, b: Rep) -> Rep:
  match c1:
    case True{}:
      Rep{o1, True{}}
    case False{}:
      match b:
        case Rep{o2, c2}:
          Rep{Bytes.append(o1, o2), c2}

def rep.cat(a: Rep, b: Rep) -> Rep:
  match a:
    case Rep{o1, c1}:
      rep.cat.go(o1, c1, b)

def reply.go(fs: List<&2, Frm>) -> Rep:
  match fs:
    case Nil{}:
      Rep{SNil{}, False{}}
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
          Rep{Bytes.append(o, close.frame(1002)), True{}}

def reply(fs: List<&2, Frm>, bad: Bool) -> Rep:
  reply.bad(bad, reply.go(fs))
