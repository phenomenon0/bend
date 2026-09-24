# WebSocket (RFC 6455) frames for either end of a connection.
#
# The engine's reader (demos/io_http_engine/ws.bend) reads what a
# server reads: masked frames, final, no fragments. This is that reader
# with the end it runs at as a parameter (Role): Srv reads exactly as
# the engine's does -- ws_laws.bend's role_srv holds it to Ws.feed for
# every input and state, so the engine's laws are this reader's at Srv
# -- and Cli reads what a client reads: frames that are NOT masked (a
# masked one fails the connection with 1002), fragments and
# continuations, and a payload capped by the client's own cap, a frame
# past it marked too big (1009) before a byte of it is read. The states
# are the engine's (Ws.Fs, Ws.W, Ws.Frm), and so are the extended
# length's and the payload's steps: an unmasked payload is the masked
# walk under the mask 0.
#
# A frame the Cli reader hands out carries its opcode, plus 16 when FIN
# was clear (a fragment that more follow): 1 and 2 are whole messages,
# 17 and 18 their first fragments, 16 a continuation that more follow, 0
# the last one; 8, 9 and 10 the control frames, which are never cut.
#
# Then the client's half of the rest: its frames, every one masked with
# the key it is given (mask is its own inverse: mask_inv), UTF-8 both
# ways, and the assembler that turns frames into messages -- fragments
# joined under the cap, a ping answered, a close read and its code
# checked, text held to UTF-8 -- and says, for each, what the
# connection does next (Act).
import Base
import ../wire/reader.bend as Wr
import ../demos/io_http_engine/ws.bend as Ws
import ../demos/io_http_engine/sha1.bend as Sha1

# The reader
# ==========

# Srv: a server's end, the engine's reader. Cli: a client's, with the
# most payload a frame may carry. Serv: a server's end as net/ws_server
# runs it: every frame masked (an unmasked one breaks the framing, and
# the connection fails with 1002), fragments and continuations as Cli
# reads them, and the payload capped as Cli caps it.
type Role is Data:
  Srv{}
  Cli{cap: U32}
  Serv{cap: U32}

# the marker a Cli frame past its cap is handed out as, just before the
# reader breaks: the connection fails with 1009, not 1002
def big.op() -> U32:
  99

# a Cli frame's first byte: no reserved bit (no extension was agreed),
# an opcode RFC 6455 defines, and a control frame final
def c.known(+op: U32) -> Bool:
  U32.is_eq(op, 0) || U32.is_eq(op, 1) || U32.is_eq(op, 2) || U32.is_eq(op, 8)
    || U32.is_eq(op, 9) || U32.is_eq(op, 10)

def c.op.go(+op: U32, ok: Bool, fin: Bool) -> Ws.Fs:
  match ok fin:
    case False{} _:
      Ws.Bad{}
    case True{} True{}:
      Ws.Len{op}
    case True{} False{}:
      Bool.pick(Ws.Fs, U32.is_le(8, op), Ws.Bad{}, Ws.Len{(op + 16 : U32)})

def g.op(r: Role, +b: U32) -> Ws.Fs:
  match r:
    case Srv{}:
      Ws.step.op(b)
    case Cli{cap}:
      c.op.go(U32.and(b, 15), U32.is_zero(U32.and(b, 112)) && c.known(U32.and(b, 15)),
        U32.is_eq(U32.and(b, 128), 128))
    case Serv{cap}:
      c.op.go(U32.and(b, 15), U32.is_zero(U32.and(b, 112)) && c.known(U32.and(b, 15)),
        U32.is_eq(U32.and(b, 128), 128))

# a control frame, as the Cli reader carries opcodes
def c.ctl(+op: U32) -> Bool:
  U32.is_le(8, op) && U32.is_lt(op, 16)

# the payload of a Cli frame whose length is known: none is a frame at
# once; else the payload, unmasked, is the masked walk under the mask 0
def c.body.go(op: U32, n: U32, out: List<&2, Ws.Frm>, zero: Bool) -> Ws.W:
  match zero:
    case True{}:
      Ws.emit(op, SNil{}, out)
    case False{}:
      Ws.W{Ws.Pay{op, n, 0, SNil{}}, out}

def c.body(op: U32, +n: U32, out: List<&2, Ws.Frm>) -> Ws.W:
  c.body.go(op, n, out, U32.is_zero(n))

# a frame past the cap: marked, then broken
def c.big(out: List<&2, Ws.Frm>) -> Ws.W:
  Ws.W{Ws.Bad{}, Con{Ws.Frm{big.op(), SNil{}}, out}}

def c.fits(op: U32, +n: U32, out: List<&2, Ws.Frm>, big: Bool) -> Ws.W:
  match big:
    case True{}:
      c.big(out)
    case False{}:
      c.body(op, n, out)

def c.len.on(
  +cap: U32, op: U32, +n: U32, two: Bool, eight: Bool, out: List<&2, Ws.Frm>
) -> Ws.W:
  match two eight:
    case True{} _:
      Ws.W{Ws.Ext{op, 2, 0, 126}, out}
    case False{} True{}:
      Ws.W{Ws.Ext{op, 8, 0, 65536}, out}
    case False{} False{}:
      c.fits(op, n, out, U32.is_lt(cap, n))

# the second byte: a server's frame is never masked, and a control
# frame carries at most 125 bytes (either marker on one is refused)
def c.len.go(
  +cap: U32, op: U32, +n: U32, masked: Bool, long_ctl: Bool, out: List<&2, Ws.Frm>
) -> Ws.W:
  match masked long_ctl:
    case True{} _:
      Ws.W{Ws.Bad{}, out}
    case False{} True{}:
      Ws.W{Ws.Bad{}, out}
    case False{} False{}:
      c.len.on(cap, op, n, U32.is_eq(n, 126), U32.is_eq(n, 127), out)

# at the server's end (Serv) the payload's length is followed by the
# mask: a frame whose length is known goes on to its four mask bytes (the
# engine's Msk, which unmasks the payload as the engine's reader does),
# or is marked too big
def s.fits(op: U32, +n: U32, out: List<&2, Ws.Frm>, big: Bool) -> Ws.W:
  match big:
    case True{}:
      c.big(out)
    case False{}:
      Ws.W{Ws.Msk{op, n, 4, 0}, out}

def s.len.on(
  +cap: U32, op: U32, +n: U32, two: Bool, eight: Bool, out: List<&2, Ws.Frm>
) -> Ws.W:
  match two eight:
    case True{} _:
      Ws.W{Ws.Ext{op, 2, 0, 126}, out}
    case False{} True{}:
      Ws.W{Ws.Ext{op, 8, 0, 65536}, out}
    case False{} False{}:
      s.fits(op, n, out, U32.is_lt(cap, n))

# the second byte at the server's end: a client's frame is always
# masked (RFC 6455 5.1: an unmasked one fails the connection, 1002), and
# a control frame carries at most 125 bytes
def s.len.go(
  +cap: U32, op: U32, +n: U32, masked: Bool, long_ctl: Bool, out: List<&2, Ws.Frm>
) -> Ws.W:
  match masked long_ctl:
    case False{} _:
      Ws.W{Ws.Bad{}, out}
    case True{} True{}:
      Ws.W{Ws.Bad{}, out}
    case True{} False{}:
      s.len.on(cap, op, n, U32.is_eq(n, 126), U32.is_eq(n, 127), out)

def g.len(r: Role, +op: U32, +b: U32, out: List<&2, Ws.Frm>) -> Ws.W:
  match r:
    case Srv{}:
      Ws.W{Ws.step.len(op, b), out}
    case Cli{+cap}:
      c.len.go(cap, op, U32.and(b, 127), U32.is_eq(U32.and(b, 128), 128),
        c.ctl(op) && U32.is_lt(125, U32.and(b, 127)), out)
    case Serv{+cap}:
      s.len.go(cap, op, U32.and(b, 127), U32.is_eq(U32.and(b, 128), 128),
        c.ctl(op) && U32.is_lt(125, U32.and(b, 127)), out)

# the extended length, big-endian. A length past the cap is marked too
# big the moment it shows; one that would not fit 32 bits is past any
# cap (a length over 2^24 - 1 is refused before it is shifted), and one
# its form did not need is refused at its last byte (RFC 6455 5.2).
def c.ext.go(
  op: U32, left: U32, +len2: U32, min: U32, big: Bool, done: Bool, short: Bool,
  out: List<&2, Ws.Frm>
) -> Ws.W:
  match big done short:
    case True{} _ _:
      c.big(out)
    case False{} True{} True{}:
      Ws.W{Ws.Bad{}, out}
    case False{} True{} False{}:
      c.body(op, len2, out)
    case False{} False{} _:
      Ws.W{Ws.Ext{op, left, len2, min}, out}

def c.ext.on(
  +cap: U32, op: U32, +left: U32, +len: U32, +len2: U32, +min: U32, out: List<&2, Ws.Frm>
) -> Ws.W:
  c.ext.go(op, left, len2, min, U32.is_lt(cap, len2) || U32.is_lt(16777215, len),
    U32.is_zero(left), U32.is_lt(len2, min), out)

# the extended length at the server's end: as Cli's, then the mask
def s.ext.go(
  op: U32, left: U32, +len2: U32, min: U32, big: Bool, done: Bool, short: Bool,
  out: List<&2, Ws.Frm>
) -> Ws.W:
  match big done short:
    case True{} _ _:
      c.big(out)
    case False{} True{} True{}:
      Ws.W{Ws.Bad{}, out}
    case False{} True{} False{}:
      Ws.W{Ws.Msk{op, len2, 4, 0}, out}
    case False{} False{} _:
      Ws.W{Ws.Ext{op, left, len2, min}, out}

def s.ext.on(
  +cap: U32, op: U32, +left: U32, +len: U32, +len2: U32, +min: U32, out: List<&2, Ws.Frm>
) -> Ws.W:
  s.ext.go(op, left, len2, min, U32.is_lt(cap, len2) || U32.is_lt(16777215, len),
    U32.is_zero(left), U32.is_lt(len2, min), out)

def g.ext(
  r: Role, op: U32, need: U32, +len: U32, min: U32, b: U32, out: List<&2, Ws.Frm>
) -> Ws.W:
  match r:
    case Srv{}:
      Ws.W{Ws.step.ext(op, need, len, min, b), out}
    case Cli{+cap}:
      c.ext.on(cap, op, (need - 1 : U32), len, ((len * 256 : U32) + b : U32), min, out)
    case Serv{+cap}:
      s.ext.on(cap, op, (need - 1 : U32), len, ((len * 256 : U32) + b : U32), min, out)

def g.at(r: Role, st: Ws.Fs, out: List<&2, Ws.Frm>, b: U32) -> Ws.W:
  match st:
    case Ws.Op{}:
      Ws.W{g.op(r, b), out}
    case Ws.Len{op}:
      g.len(r, op, b, out)
    case Ws.Ext{op, need, len, min}:
      g.ext(r, op, need, len, min, b, out)
    case Ws.Msk{op, len, need, m}:
      Ws.step.msk(op, len, need, m, b, out)
    case Ws.Pay{op, rem, m, acc}:
      Ws.step.pay(op, rem, m, acc, b, out)
    case Ws.Bad{}:
      Ws.W{Ws.Bad{}, out}

# one byte, at either end
def step(r: Role, w: Ws.W, b: U32) -> Ws.W:
  match w:
    case Ws.W{st, out}:
      g.at(r, st, out, b)

# the reader kit's walk (wire/reader.bend), the role its environment
def feed(+r: Role, bs: List<&2, U32>, w: Ws.W) -> Ws.W:
  Wr.feed(~Role, ~Ws.W, ~step, r, bs, w)

def feed_buf(+r: Role, b: Bytes(), w: Ws.W) -> Ws.W:
  Wr.feed_buf.slow(~Role, ~Ws.W, ~step, r, b, w)

# Masking (RFC 6455 5.3)
# =======

# the payload under the mask m: each byte xored with the mask's top
# byte, the mask turned a byte left after each -- the walk the engine's
# reader unmasks with (Ws.key.of, Ws.rot), so a frame masked here reads
# back there
def mask(p: Bytes(), +m: U32) -> Bytes():
  match p:
    case SNil{}:
      SNil{}
    case SCon{Chr{c}, t}:
      SCon{Chr{U32.xor(c, Ws.key.of(m))}, mask(t, Ws.rot(m))}

# Writing (the client's frames)
# =======

# the length's first byte (under 126, or the marker) and the bytes that
# extend it
def len7(+n: U32) -> U32:
  Bool.pick(U32, U32.is_lt(n, 126), n, Bool.pick(U32, U32.is_lt(n, 65536), 126, 127))

def tail(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      t

def len.ext(+n: U32) -> List<&2, U32>:
  tail(Ws.len.bytes(n))

# a client frame's head: FIN and the opcode; the mask bit and the
# length; the extended length; the four bytes of the key, big-endian
def c.head(op: U32, fin: Bool, +n: U32, +m: U32) -> Bytes():
  Bytes.from_list(Con{U32.or(Bool.pick(U32, fin, 128, 0), op),
    Con{U32.or(128, len7(n)), List.append(&2, U32, len.ext(n), Sha1.unword(m))}})

# a client frame: the head, then the payload under the key. Every frame
# a client sends is masked (RFC 6455 5.1), each with a key of its own.
def c.frame(op: U32, fin: Bool, +p: Bytes(), +m: U32) -> Bytes():
  Bytes.append(c.head(op, fin, U32.from_nat(Bytes.len(p)), m), mask(p, m))

# Writing (the server's frames)
# =======

# a server frame's head: FIN and the opcode; the length, its mask bit
# clear (the low seven bits kept, and only they); the extended length
def s.head(op: U32, fin: Bool, +n: U32) -> Bytes():
  Bytes.from_list(Con{U32.or(Bool.pick(U32, fin, 128, 0), op), Con{U32.and(len7(n), 127), len.ext(n)}})

# a server frame: the head, then the payload as it is. No frame a server
# sends is masked (RFC 6455 5.1; ws_laws.bend's srv_unmasked).
def s.frame(op: U32, fin: Bool, +p: Bytes()) -> Bytes():
  Bytes.append(s.head(op, fin, U32.from_nat(Bytes.len(p))), p)

def code.bytes(+code: U32) -> Bytes():
  Bytes.from_list([Sha1.byte(Sha1.sr(8n, code)), Sha1.byte(code)])

# a close: the code and the reason, or nothing for 1005 (no status)
def close.body(+code: U32, reason: Bytes()) -> Bytes():
  Bool.pick(Bytes(), U32.is_eq(code, 1005), SNil{}, Bytes.append(code.bytes(code), reason))

# UTF-8
# =====

def cont(+c: U32, k: Nat) -> U32:
  U32.or(128, U32.and(Sha1.sr(k, c), 63))

# a code point's bytes, in front of the rest: one byte under 80, two
# under 800, three under 10000, four past that
def enc.go(+c: U32, rest: Bytes(), one: Bool, two: Bool, three: Bool) -> Bytes():
  match one two three:
    case True{} _ _:
      SCon{Chr{c}, rest}
    case False{} True{} _:
      SCon{Chr{U32.or(192, Sha1.sr(6n, c))}, SCon{Chr{cont(c, 0n)}, rest}}
    case False{} False{} True{}:
      SCon{Chr{U32.or(224, Sha1.sr(12n, c))}, SCon{Chr{cont(c, 6n)},
        SCon{Chr{cont(c, 0n)}, rest}}}
    case False{} False{} False{}:
      SCon{Chr{U32.or(240, U32.and(Sha1.sr(18n, c), 7))}, SCon{Chr{cont(c, 12n)},
        SCon{Chr{cont(c, 6n)}, SCon{Chr{cont(c, 0n)}, rest}}}}

def enc.cp(+c: U32, rest: Bytes()) -> Bytes():
  enc.go(c, rest, U32.is_lt(c, 128), U32.is_lt(c, 2048), U32.is_lt(c, 65536))

# a String's UTF-8 bytes
def utf8.enc(s: String) -> Bytes():
  match s:
    case SNil{}:
      SNil{}
    case SCon{Chr{c}, t}:
      enc.cp(c, utf8.enc(t))

# Reading: need continuation bytes to go, cp the code point so far, the
# code points so far reversed. A lead byte starts a code point (its
# bits, and how many bytes follow it); a continuation adds six bits,
# and the last one lays the code point down.
type Dcd is Data:
  Dcd{need: U32, cp: U32, acc: String}

def dec.lead(+b: U32, acc: String, ascii: Bool, two: Bool, three: Bool) -> Dcd:
  match ascii two three:
    case True{} _ _:
      Dcd{0, 0, SCon{Chr{b}, acc}}
    case False{} True{} _:
      Dcd{1, U32.and(b, 31), acc}
    case False{} False{} True{}:
      Dcd{2, U32.and(b, 15), acc}
    case False{} False{} False{}:
      Dcd{3, U32.and(b, 7), acc}

def dec.cont(+need: U32, +cp: U32, acc: String, last: Bool) -> Dcd:
  match last:
    case True{}:
      Dcd{0, 0, SCon{Chr{cp}, acc}}
    case False{}:
      Dcd{need, cp, acc}

def dec.at(+need: U32, +cp: U32, acc: String, +b: U32, lead: Bool) -> Dcd:
  match lead:
    case True{}:
      dec.lead(b, acc, U32.is_lt(b, 128), U32.is_lt(b, 224), U32.is_lt(b, 240))
    case False{}:
      dec.cont((need - 1 : U32), U32.or((cp * 64 : U32), U32.and(b, 63)), acc, U32.is_eq(need, 1))

def dec.step(d: Dcd, b: U32) -> Dcd:
  match d:
    case Dcd{+need, cp, acc}:
      dec.at(need, cp, acc, b, U32.is_zero(need))

def dec.go(bs: Bytes(), d: Dcd) -> Dcd:
  match bs:
    case SNil{}:
      d
    case SCon{Chr{b}, t}:
      dec.go(t, dec.step(d, b))

def dec.out(d: Dcd) -> String:
  match d:
    case Dcd{need, cp, acc}:
      String.reverse(acc)

# the bytes, read as UTF-8 already checked (Ws.utf8), into code points
def utf8.dec(bs: Bytes()) -> String:
  dec.out(dec.go(bs, Dcd{0, 0, SNil{}}))

# Messages
# ========

# what a client receives: text (UTF-8, checked, as code points), bytes,
# or the peer's close with its code (1005 when it gave none) and reason
type Msg is Data:
  Text{text: String}
  Binary{data: Bytes()}
  Closed{code: U32, reason: String}

# what a frame asks of the connection: hand a message over, answer a
# ping with a pong of its payload, nothing (a pong, or a fragment
# taken), the peer's close (code and reason checked: answer it and
# stop), or fail the connection with a code (1002 protocol, 1007 not
# UTF-8, 1009 too big)
type Act is Data:
  Deliver{m: Msg}
  Pong{body: Bytes()}
  Skip{}
  Bye{code: U32, reason: Bytes()}
  Refuse{code: U32}

# Idle: between messages. Frag: a message cut in fragments, its opcode
# (1 or 2), its bytes so far, how many, and the UTF-8 walk over them
# when it is text, so text that breaks fails at the fragment that
# breaks it
type Asm is Data:
  Idle{}
  Frag{op: U32, acc: Bytes(), n: U32, ut: Ws.Ut}

# the assembler after a frame, and what the frame asks
type Ax is Data:
  Ax{a: Asm, x: Act}

def ax.asm(q: Ax) -> Asm:
  match q:
    case Ax{a, x}:
      a

def ax.act(q: Ax) -> Act:
  match q:
    case Ax{a, x}:
      x

def ut.broken(s: Ws.Ut) -> Bool:
  match s:
    case Ws.Ut{need, lo, hi}:
      False{}
    case Ws.Utx{}:
      True{}

# a close's payload: none is 1005 (no status); one byte is refused; a
# code a peer may not send is refused (1002), a reason that is not
# UTF-8 too (1007)
def close.two(+code: U32, reason: Bytes(), ok: Bool, text: Bool) -> Act:
  match ok text:
    case False{} _:
      Refuse{1002}
    case True{} False{}:
      Refuse{1007}
    case True{} True{}:
      Bye{code, reason}

def close.act(body: Bytes()) -> Act:
  match body:
    case SNil{}:
      Bye{1005, SNil{}}
    case SCon{Chr{+a}, t}:
      match t:
        case SNil{}:
          Refuse{1002}
        case SCon{Chr{+b}, +u}:
          +code = ((a * 256 : U32) + b : U32)
          close.two(code, u, Ws.close.code.ok(code), Ws.utf8(u))

def ctl.act(body: Bytes(), close: Bool, ping: Bool) -> Act:
  match close ping:
    case True{} _:
      close.act(body)
    case False{} True{}:
      Pong{body}
    case False{} False{}:
      Skip{}

# a whole message: text must be UTF-8
def whole.text(+body: Bytes(), ok: Bool) -> Act:
  match ok:
    case True{}:
      Deliver{Text{utf8.dec(body)}}
    case False{}:
      Refuse{1007}

def whole(+body: Bytes(), text: Bool) -> Act:
  match text:
    case True{}:
      whole.text(body, Ws.utf8(body))
    case False{}:
      Deliver{Binary{body}}

# a first fragment: text that has broken already fails here
def first.text(op: U32, +body: Bytes(), +n: U32, ut: Ws.Ut, bad: Bool) -> Ax:
  match bad:
    case True{}:
      Ax{Idle{}, Refuse{1007}}
    case False{}:
      Ax{Frag{op, body, n, ut}, Skip{}}

def first(op: U32, +body: Bytes(), +n: U32, text: Bool) -> Ax:
  match text:
    case True{}:
      +ut = Ws.utf8.go(body, Ws.Ut{0, 128, 191})
      first.text(op, body, n, ut, ut.broken(ut))
    case False{}:
      Ax{Frag{op, body, n, Ws.Ut{0, 128, 191}}, Skip{}}

# a data frame between messages: a whole message, or the first of its
# fragments; a continuation with nothing to continue is refused
def idle.data(+op: U32, +body: Bytes(), cont: Bool, cut: Bool) -> Ax:
  match cont cut:
    case True{} _:
      Ax{Idle{}, Refuse{1002}}
    case False{} True{}:
      first((op - 16 : U32), body, U32.from_nat(Bytes.len(body)), U32.is_eq(op, 17))
    case False{} False{}:
      Ax{Idle{}, whole(body, U32.is_eq(op, 1))}

# the last fragment: the message whole; text must end on a whole
# character
def last(acc: Bytes(), ut: Ws.Ut, text: Bool) -> Act:
  match text:
    case True{}:
      whole.text(acc, Ws.utf8.end(ut))
    case False{}:
      Deliver{Binary{acc}}

def more.go(+fop: U32, acc: Bytes(), +n2: U32, ut: Ws.Ut, bad: Bool, fin: Bool) -> Ax:
  match bad fin:
    case True{} _:
      Ax{Idle{}, Refuse{1007}}
    case False{} True{}:
      Ax{Idle{}, last(acc, ut, U32.is_eq(fop, 1))}
    case False{} False{}:
      Ax{Frag{fop, acc, n2, ut}, Skip{}}

def ut.walk(body: Bytes(), ut: Ws.Ut, text: Bool) -> Ws.Ut:
  match text:
    case True{}:
      Ws.utf8.go(body, ut)
    case False{}:
      ut

# a continuation: the message so far and this fragment, under the cap
# (1009 past it); text walked on from where it was
def more(
  +cap: U32, +fop: U32, acc: Bytes(), +n2: U32, ut: Ws.Ut, +body: Bytes(), fin: Bool, over: Bool
) -> Ax:
  match over:
    case True{}:
      Ax{Idle{}, Refuse{1009}}
    case False{}:
      +ut2 = ut.walk(body, ut, U32.is_eq(fop, 1))
      more.go(fop, Bytes.append(acc, body), n2, ut2, ut.broken(ut2), fin)

# a data frame inside a fragmented message: only a continuation may come
def frag.data(
  +cap: U32, +fop: U32, acc: Bytes(), +n: U32, ut: Ws.Ut, +op: U32, +body: Bytes(), cont: Bool
) -> Ax:
  match cont:
    case False{}:
      Ax{Idle{}, Refuse{1002}}
    case True{}:
      +n2 = (n + U32.from_nat(Bytes.len(body)) : U32)
      more(cap, fop, acc, n2, ut, body, U32.is_eq(op, 0), U32.is_lt(cap, n2) || U32.is_lt(n2, n))

def asm.data(+cap: U32, a: Asm, +op: U32, +body: Bytes()) -> Ax:
  match a:
    case Idle{}:
      idle.data(op, body, U32.is_eq(op, 0) || U32.is_eq(op, 16), U32.is_le(16, op))
    case Frag{fop, acc, n, ut}:
      frag.data(cap, fop, acc, n, ut, op, body, U32.is_eq(op, 0) || U32.is_eq(op, 16))

def asm.kind(+cap: U32, a: Asm, +op: U32, +body: Bytes(), ctl: Bool, big: Bool) -> Ax:
  match ctl big:
    case True{} _:
      Ax{a, ctl.act(body, U32.is_eq(op, 8), U32.is_eq(op, 9))}
    case False{} True{}:
      Ax{a, Refuse{1009}}
    case False{} False{}:
      asm.data(cap, a, op, body)

# One frame through the assembler: what the connection does, and the
# assembler after it. Control frames may come between fragments and
# leave the message where it was.
def asm(+cap: U32, a: Asm, f: Ws.Frm) -> Ax:
  match f:
    case Ws.Frm{+op, body}:
      asm.kind(cap, a, op, body, c.ctl(op), U32.is_eq(op, big.op()))

# The session, pure
# =================

def acts.go(+cap: U32, fs: List<&2, Ws.Frm>, a: Asm) -> List<&2, Act>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{f, t}:
      +q = asm(cap, a, f)
      Con{ax.act(q), acts.go(cap, t, ax.asm(q))}

def acts.end(+cap: U32, fs: List<&2, Ws.Frm>, dd: Ws.W & Bool) -> List<&2, Act>:
  (w, bad) = dd
  List.append(&2, Act, acts.go(cap, fs, Idle{}), Bool.pick(List<&2, Act>, bad, [Refuse{1002}], []))

def acts.of(+cap: U32, tk: Ws.W & List<&2, Ws.Frm>) -> List<&2, Act>:
  (w, fs) = tk
  acts.end(cap, fs, Ws.dead(w))

# what a client does with the bytes a server sent, from the first:
# every frame's act in turn, and a 1002 at the end if the framing broke
def session(+cap: U32, bs: Bytes()) -> List<&2, Act>:
  acts.of(cap, Ws.take(feed_buf(Cli{cap}, bs, Ws.new())))

# The server's session, pure
# ==========================
#
# What a server's connection hands its handler, and what it writes back
# on its own, as functions of the bytes the client sent. The spec reads
# the input whole: the frames of all of it at the server's end (Serv),
# each through the assembler in turn, and a 1002 at the end when the
# framing broke. The connection reads it as it arrives: each read fed to
# the reader from where the last left it, the frames it completed taken
# and assembled with the assembler as the last read left it, and the
# framing checked once they are all handed over (net/ws.bend's st.feed,
# turn and empty). ws_laws.bend's srv_reads: the two are the same acts,
# however the input is cut into reads.

# the acts of frames in turn, and the assembler after them
type AR is Data:
  AR{acts: List<&2, Act>, asm: Asm}

def acts.push(x: Act, r: AR) -> AR:
  match r:
    case AR{xs, a}:
      AR{Con{x, xs}, a}

def acts.run(+cap: U32, fs: List<&2, Ws.Frm>, a: Asm) -> AR:
  match fs:
    case Nil{}:
      AR{Nil{}, a}
    case Con{f, t}:
      +q = asm(cap, a, f)
      acts.push(ax.act(q), acts.run(cap, t, ax.asm(q)))

# a 1002 when the framing broke
def s.bad(w: Ws.W) -> List<&2, Act>:
  match w:
    case Ws.W{st, out}:
      match st:
        case Ws.Bad{}:
          [Refuse{1002}]
        case _:
          []

def s.fin(r: AR, w: Ws.W) -> List<&2, Act>:
  match r:
    case AR{xs, a}:
      List.append(&2, Act, xs, s.bad(w))

# from a reader and an assembler: the frames it holds, then the rest
def s.tail(+cap: U32, tk: Ws.W & List<&2, Ws.Frm>, a: Asm) -> List<&2, Act>:
  (w, fs) = tk
  s.fin(acts.run(cap, fs, a), w)

# the spec: the input whole
def s.session(+cap: U32, bs: Bytes()) -> List<&2, Act>:
  s.tail(cap, Ws.take(feed_buf(Serv{cap}, bs, Ws.new())), Idle{})

def s.took.run(r: AR, w: Ws.W, go: Ws.W -> Asm -> List<&2, Act>) -> List<&2, Act>:
  match r:
    case AR{xs, a}:
      List.append(&2, Act, xs, go(w, a))

def s.took(+cap: U32, tk: Ws.W & List<&2, Ws.Frm>, a: Asm, go: Ws.W -> Asm -> List<&2, Act>) -> List<&2, Act>:
  (w, fs) = tk
  s.took.run(acts.run(cap, fs, a), w, go)

def s.reads.go(+cap: U32, rs: List<&2, Bytes()>, w: Ws.W, a: Asm) -> List<&2, Act>:
  match rs:
    case Nil{}:
      s.bad(w)
    case Con{r, t}:
      s.took(cap, Ws.take(feed_buf(Serv{cap}, r, w)), a, w2 => a2 => s.reads.go(cap, t, w2, a2))

# the connection: the input as the reads it came in
def s.reads(+cap: U32, rs: List<&2, Bytes()>) -> List<&2, Act>:
  s.reads.go(cap, rs, Ws.new(), Idle{})

# What a connection writes on its own for an act (s.out; net/ws.bend's
# act writes exactly it): a pong for a ping, and for the peer's close or
# a failure the close frame, with the peer's code or the failure's --
# and nothing at all once this end's close went out (the handler closed
# first, or the server's 1001 on SIGTERM): no pong after a close (RFC
# 6455 5.5.1), and the peer's close is then the answer, not a thing to
# answer. The peer's close and a failure end the connection (s.stops).
type Wr is Data:
  WPong{body: Bytes()}
  WClose{code: U32}

def s.out(+sent: Bool, x: Act) -> Maybe<&2, Wr>:
  match sent:
    case True{}:
      None{}
    case False{}:
      match x:
        case Deliver{m}:
          None{}
        case Pong{body}:
          Some{WPong{body}}
        case Skip{}:
          None{}
        case Bye{code, reason}:
          Some{WClose{code}}
        case Refuse{code}:
          Some{WClose{code}}

def s.stops(x: Act) -> Bool:
  match x:
    case Bye{code, reason}:
      True{}
    case Refuse{code}:
      True{}
    case _:
      False{}

def s.put(w: Maybe<&2, Wr>, rest: List<&2, Wr>) -> List<&2, Wr>:
  match w:
    case None{}:
      rest
    case Some{x}:
      Con{x, rest}

# what the connection writes for the acts, in turn, until one ends it;
# sent is whether this end's close went out already
def s.writes(+sent: Bool, xs: List<&2, Act>) -> List<&2, Wr>:
  match xs:
    case Nil{}:
      []
    case Con{+x, t}:
      s.put(s.out(sent, x), Bool.pick(List<&2, Wr>, s.stops(x), [], s.writes(sent, t)))

# how many close frames
def closes(ws: List<&2, Wr>) -> Nat:
  match ws:
    case Nil{}:
      0n
    case Con{w, t}:
      match w:
        case WPong{b}:
          closes(t)
        case WClose{c}:
          1n+closes(t)
