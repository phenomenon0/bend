# An HTTP/2 connection (RFC 9113 5-8), as a pure machine: the frames
# one read completed go in, in order, and what the server writes back
# comes out, with the state the next read starts from.
#
# The parts, each a pure function LAWS.bend speaks of:
#
#   ty.of, verdict   a frame's type, and what the stream's state (5.1)
#                    lets it do: accepted, a stream error, a connection
#                    error. Every stream-scoped frame goes through it
#                    before anything else looks at it.
#   Sw, Rw           the flow-control windows (6.9): what we may still
#                    send, and what the peer may still send us; an
#                    increment past 2^31-1 is a FLOW_CONTROL_ERROR.
#   req.check        a request's header list (8.2, 8.3): lowercase,
#                    pseudo-headers first, known, once, the three a
#                    request needs, no connection-specific field.
#   Bud              the budgets that bound what a peer can make the
#                    server do for nothing: resets, pings, settings,
#                    header blocks and their CONTINUATIONs.
#
# What a request earns is the planner's (main.bend): the connection
# hands it the method, path and body, and takes back a status, a type
# and a body to frame.
import Base
import ../../wire/reader.bend as Wr
import ./huff.bend as H
import ./hpack.bend as K
import ./frame.bend as Fm

# Error codes (RFC 9113 7)
# ========================

def e.no() -> U32:
  0

def e.proto() -> U32:
  1

def e.internal() -> U32:
  2

def e.flow() -> U32:
  3

def e.closed() -> U32:
  5

def e.size() -> U32:
  6

def e.refused() -> U32:
  7

def e.compress() -> U32:
  9

def e.calm() -> U32:
  11

# Frame types (RFC 9113 6)
# ========================

type Ty is Data:
  TData{}
  THeaders{}
  TPrio{}
  TRst{}
  TSettings{}
  TPush{}
  TPing{}
  TGoaway{}
  TWin{}
  TCont{}
  TOther{}

def ty.pick(b: Bool, t: Ty, rest: Ty) -> Ty:
  match b:
    case True{}:
      t
    case False{}:
      rest

def ty.of(+t: U32) -> Ty:
  ty.pick(U32.is_eq(t, 0), TData{},
  ty.pick(U32.is_eq(t, 1), THeaders{},
  ty.pick(U32.is_eq(t, 2), TPrio{},
  ty.pick(U32.is_eq(t, 3), TRst{},
  ty.pick(U32.is_eq(t, 4), TSettings{},
  ty.pick(U32.is_eq(t, 5), TPush{},
  ty.pick(U32.is_eq(t, 6), TPing{},
  ty.pick(U32.is_eq(t, 7), TGoaway{},
  ty.pick(U32.is_eq(t, 8), TWin{},
  ty.pick(U32.is_eq(t, 9), TCont{}, TOther{}))))))))))

# Stream states (RFC 9113 5.1)
# ============================

# as the server sees a stream: never used; open; half-closed (remote),
# the request whole and the response under way; half-closed (local),
# the response sent before the request ended; closed by our own
# RST_STREAM lately (its late frames are ignored); closed
type Ss is Data:
  SIdle{}
  SOpen{}
  SHalf{}
  SLocal{}
  SReset{}
  SClosed{}

# what a frame may do on a stream in a state: be taken, be refused as a
# stream error, or end the connection
type Vd is Data:
  VOk{}
  VStream{code: U32}
  VConn{code: U32}

# RFC 9113 5.1, for the frames a client sends on a stream (SETTINGS,
# PING and GOAWAY are the connection's, and PUSH_PROMISE a client never
# sends; CONTINUATION is the header block's, below):
#   idle: HEADERS opens it, PRIORITY is taken; anything else is a
#     connection error PROTOCOL_ERROR
#   open, half-closed (local): everything is taken
#   closed by our RST_STREAM: everything is taken, and ignored (frames
#     the peer sent before it saw the reset)
#   half-closed (remote): WINDOW_UPDATE, PRIORITY, RST_STREAM are
#     taken; anything else is a stream error STREAM_CLOSED
#   closed: WINDOW_UPDATE, PRIORITY, RST_STREAM are taken (they may
#     cross in flight); DATA or HEADERS is a connection error
#     STREAM_CLOSED
def verdict(s: Ss, t: Ty) -> Vd:
  match s t:
    case SIdle{} THeaders{}:
      VOk{}
    case SIdle{} TPrio{}:
      VOk{}
    case SIdle{} _:
      VConn{e.proto()}
    case SOpen{} _:
      VOk{}
    case SLocal{} _:
      VOk{}
    case SReset{} _:
      VOk{}
    case SHalf{} TWin{}:
      VOk{}
    case SHalf{} TPrio{}:
      VOk{}
    case SHalf{} TRst{}:
      VOk{}
    case SHalf{} _:
      VStream{e.closed()}
    case SClosed{} TWin{}:
      VOk{}
    case SClosed{} TPrio{}:
      VOk{}
    case SClosed{} TRst{}:
      VOk{}
    case SClosed{} _:
      VConn{e.closed()}

# Flow control (RFC 9113 5.2, 6.9)
# ================================

# the most a window may reach
def win.max() -> Nat:
  2147483647n

# What we may still send: a window can go below zero when the peer
# lowers SETTINGS_INITIAL_WINDOW_SIZE (6.9.2), so it is up minus down,
# one of them zero.
type Sw is Data:
  Sw{up: Nat, down: Nat}

# an increment: refused (None) when the window would pass 2^31-1
def sw.norm(+up: Nat, +down: Nat, ge: Bool) -> Sw:
  match ge:
    case True{}:
      Sw{Nat.sub(up, down), 0n}
    case False{}:
      Sw{0n, Nat.sub(down, up)}

def sw.fit(w: Sw, ok: Bool) -> Maybe<&2, Sw>:
  match ok:
    case True{}:
      Some{w}
    case False{}:
      None{}

def sw.up(w: Sw) -> Nat:
  match w:
    case Sw{up, down}:
      up

def sw.add(w: Sw, +n: Nat) -> Maybe<&2, Sw>:
  match w:
    case Sw{+up, +down}:
      +w2 = sw.norm(Nat.add(up, n), down, Nat.is_le(down, Nat.add(up, n)))
      sw.fit(w2, Nat.is_le(sw.up(w2), win.max()))

# a decrease (a lower initial window): it can go below zero
def sw.less(w: Sw, +n: Nat) -> Sw:
  match w:
    case Sw{+up, +down}:
      sw.norm(up, Nat.add(down, n), Nat.is_le(Nat.add(down, n), up))

# sent: n of what is open (never more than up, which pump sees to)
def sw.take(w: Sw, n: Nat) -> Sw:
  match w:
    case Sw{up, down}:
      Sw{Nat.sub(up, n), down}

def sw.new(+n: Nat) -> Sw:
  Sw{n, 0n}

# What the peer may still send us: DATA past it is a FLOW_CONTROL_ERROR
# (6.9.1); a window never goes below zero, since what would take it
# there is refused.
def rw.fit(+w: Nat, +n: Nat, ok: Bool) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      Some{Nat.sub(w, n)}
    case False{}:
      None{}

def rw.take(+w: Nat, +n: Nat) -> Maybe<&2, Nat>:
  rw.fit(w, n, Nat.is_le(n, w))

# Requests (RFC 9113 8.2, 8.3)
# ============================

# A request as the connection hands it on: its stream, its method and
# path, and its body. Anything else a client sent is checked and
# dropped.
type Req is Data:
  Req{sid: U32, meth: Bytes(), path: Bytes(), body: Bytes()}

# what a request's header list has said, as it is walked: whether it is
# still well formed, whether a regular field has come (a pseudo-header
# after one is malformed), the pseudo-headers seen, the content-length
type Chk is Data:
  Chk{ok: Bool, reg: Bool, meth: Maybe<&2, Bytes()>, scheme: Maybe<&2, Bytes()>,
    path: Maybe<&2, Bytes()>, auth: Maybe<&2, Bytes()>, clen: Maybe<&2, Nat>}

def chk.new() -> Chk:
  Chk{True{}, False{}, None{}, None{}, None{}, None{}, None{}}

def chk.bad(c: Chk) -> Chk:
  match c:
    case Chk{ok, reg, m, s, p, a, cl}:
      Chk{False{}, reg, m, s, p, a, cl}

def chk.reg(c: Chk) -> Chk:
  match c:
    case Chk{ok, reg, m, s, p, a, cl}:
      Chk{ok, True{}, m, s, p, a, cl}

def chk.and(c: Chk, ok: Bool) -> Chk:
  match ok:
    case True{}:
      c
    case False{}:
      chk.bad(c)

def chk.ok(c: Chk) -> Bool:
  match c:
    case Chk{ok, reg, m, s, p, a, cl}:
      ok

# a field name with an uppercase letter is malformed (8.2.1)
def upper.any(s: Bytes()) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{Chr{+c}, t}:
      (U32.is_le(65, c) && U32.is_le(c, 90)) || upper.any(t)

def digits.all(s: Bytes()) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{Chr{+c}, t}:
      U32.is_le(48, c) && U32.is_le(c, 57) && digits.all(t)

def beq(+a: Bytes(), +b: Bytes()) -> Bool:
  K.beq(a, b)

# the pseudo-headers a request may carry (8.3.1)
type Ps is Data:
  PsMeth{}
  PsScheme{}
  PsPath{}
  PsAuth{}
  PsNone{}

def ps.pick(b: Bool, k: Ps, rest: Ps) -> Ps:
  match b:
    case True{}:
      k
    case False{}:
      rest

def ps.of(+n: Bytes()) -> Ps:
  ps.pick(beq(n, ":method"), PsMeth{}, ps.pick(beq(n, ":scheme"), PsScheme{},
    ps.pick(beq(n, ":path"), PsPath{}, ps.pick(beq(n, ":authority"), PsAuth{}, PsNone{}))))

# a pseudo-header is set once: a second is malformed
def fresh(m: Maybe<&2, Bytes()>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      False{}

def slot(m: Maybe<&2, Bytes()>, v: Bytes()) -> Maybe<&2, Bytes()>:
  match m:
    case None{}:
      Some{v}
    case Some{x}:
      Some{x}

def chk.set(c: Chk, k: Ps, +v: Bytes()) -> Chk:
  match c:
    case Chk{ok, +reg, +m, +s, +p, +a, cl}:
      match k:
        case PsMeth{}:
          Chk{ok && fresh(m) && Bool.not(reg), reg, slot(m, v), s, p, a, cl}
        case PsScheme{}:
          Chk{ok && fresh(s) && Bool.not(reg), reg, m, slot(s, v), p, a, cl}
        case PsPath{}:
          Chk{ok && fresh(p) && Bool.not(reg) && Bool.not(String.is_empty(v)), reg, m, s, slot(p, v), a, cl}
        case PsAuth{}:
          Chk{ok && fresh(a) && Bool.not(reg), reg, m, s, p, slot(a, v), cl}
        case PsNone{}:
          Chk{False{}, reg, m, s, p, a, cl}

# a content-length: digits, and the same wherever it is repeated
def clen.fine(m: Maybe<&2, Nat>, +n: Nat) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      Nat.is_eq(x, n)

def chk.clen.go(c: Chk, +n: Nat, dg: Bool) -> Chk:
  match c:
    case Chk{ok, reg, m, s, p, a, +cl}:
      Chk{ok && dg && clen.fine(cl, n), True{}, m, s, p, a, Some{n}}

# a content-length's value: its digits, at most fourteen (below 10^14,
# which a Nat holds)
def dec.digits(s: Bytes(), +acc: Nat) -> Nat:
  match s:
    case SNil{}:
      acc
    case SCon{Chr{c}, t}:
      dec.digits(t, Nat.add(Nat.mul(acc, 10n), U32.to_nat(U32.sub(c, 48))))

def chk.clen(c: Chk, +v: Bytes()) -> Chk:
  chk.clen.go(c, dec.digits(v, 0n),
    Bool.not(String.is_empty(v)) && digits.all(v) && Nat.is_le(Bytes.len(v), 14n))

# a connection-specific field is malformed in HTTP/2 (8.2.2), and TE
# may only say "trailers"
def conn.field(+n: Bytes()) -> Bool:
  beq(n, "connection") || beq(n, "keep-alive") || beq(n, "proxy-connection")
    || beq(n, "transfer-encoding") || beq(n, "upgrade")

def chk.reg2(c: Chk, +v: Bytes(), cl: Bool, cf: Bool, te: Bool) -> Chk:
  match cl cf te:
    case True{} _ _:
      chk.clen(c, v)
    case False{} True{} _:
      chk.bad(chk.reg(c))
    case False{} False{} True{}:
      chk.and(chk.reg(c), beq(v, "trailers"))
    case False{} False{} False{}:
      chk.reg(c)

def chk.regular(c: Chk, +n: Bytes(), +v: Bytes()) -> Chk:
  chk.reg2(c, v, beq(n, "content-length"), conn.field(n), beq(n, "te"))

def chk.name(c: Chk, +n: Bytes(), +v: Bytes(), trailer: Bool, up: Bool, ps: Bool) -> Chk:
  match trailer up ps:
    case _ True{} _:
      chk.bad(c)
    case True{} False{} True{}:
      chk.bad(c)
    case False{} False{} True{}:
      chk.set(c, ps.of(n), v)
    case _ False{} False{}:
      chk.regular(c, n, v)

def chk.one(c: Chk, f: K.Fld, +trailer: Bool) -> Chk:
  match f:
    case K.Fld{+n, +v}:
      chk.name(c, n, v, trailer, upper.any(n), Bytes.starts_with(n, ":"))

def chk.all(fs: List<&2, K.Fld>, c: Chk, +trailer: Bool) -> Chk:
  match fs:
    case Nil{}:
      c
    case Con{f, t}:
      chk.all(t, chk.one(c, f, trailer), trailer)

# What a request's header list comes to: malformed, or a method, path
# and content-length. A request needs :method, :scheme and :path (only
# CONNECT, which this server does not serve, goes without the last two).
type Head is Data:
  HBad{}
  HOk{meth: Bytes(), path: Bytes(), clen: Maybe<&2, Nat>}

def head.of(c: Chk) -> Head:
  match c:
    case Chk{ok, reg, m, s, p, a, cl}:
      match ok m s p:
        case True{} Some{mv} Some{sv} Some{pv}:
          HOk{mv, pv, cl}
        case _ _ _ _:
          HBad{}

def req.check(fs: List<&2, K.Fld>) -> Head:
  head.of(chk.all(fs, chk.new(), False{}))

# trailers: no pseudo-header, and the rest as in a request
def trailers.ok(fs: List<&2, K.Fld>) -> Bool:
  chk.ok(chk.all(fs, chk.new(), True{}))

# Writing frames (RFC 9113 6)
# ===========================

def put32(+n: U32) -> Bytes():
  Bytes.from_list(Fm.put32(n))

def f.data(+sid: U32, end: Bool, +bs: Bytes()) -> Bytes():
  Fm.frame(0, Bool.to_u32(end), sid, bs)

def f.headers(+sid: U32, end: Bool, +blk: Bytes()) -> Bytes():
  Fm.frame(1, U32.or(4, Bool.to_u32(end)), sid, blk)

def f.rst(+sid: U32, +code: U32) -> Bytes():
  Fm.frame(3, 0, sid, put32(code))

def f.settings() -> Bytes():
  Fm.frame(4, 0, 0, Bytes.from_list([0, 3, 0, 0, 0, 100, 0, 6, 0, 1, 0, 0]))

def f.ack() -> Bytes():
  Fm.frame(4, 1, 0, "")

def f.pong(+pay: Bytes()) -> Bytes():
  Fm.frame(6, 1, 0, pay)

def f.goaway(+last: U32, +code: U32) -> Bytes():
  Fm.frame(7, 0, 0, Bytes.append(put32(last), put32(code)))

def f.win(+sid: U32, +n: U32) -> Bytes():
  Fm.frame(8, 0, sid, put32(n))

# Reading a payload's fields
# ==========================

def be32(+b: Bytes(), +i: Nat) -> U32:
  U32.or(U32.shln(Bytes.get(b, i), 24n), U32.or(U32.shln(Bytes.get(b, 1n+i), 16n),
    U32.or(U32.shln(Bytes.get(b, 2n+i), 8n), Bytes.get(b, 3n+i))))

def be16(+b: Bytes(), +i: Nat) -> U32:
  U32.or(U32.shln(Bytes.get(b, i), 8n), Bytes.get(b, 1n+i))

def u31(+x: U32) -> U32:
  U32.and(x, 2147483647)

def flag(+fl: U32, +m: U32) -> Bool:
  Bool.not(U32.is_zero(U32.and(fl, m)))

# Streams
# =======

# A stream the server is working on: its id and state, the request as
# far as it has come (method, path, content-length, body and how much
# of it), what the peer may still send on it, what we may still send,
# and the response bytes not yet sent (and whether END_STREAM follows
# them).
type St is Data:
  St{id: U32, ss: Ss, meth: Bytes(), path: Bytes(), clen: Maybe<&2, Nat>, body: Bytes(), got: Nat,
    rw: Nat, sw: Sw, out: Bytes(), fin: Bool}

def st.id(r: St) -> U32:
  match r:
    case St{id, ss, meth, path, clen, body, got, rw, sw, out, fin}:
      id

def st.ss(r: St) -> Ss:
  match r:
    case St{id, ss, meth, path, clen, body, got, rw, sw, out, fin}:
      ss

def st.meth(r: St) -> Bytes():
  match r:
    case St{id, ss, meth, path, clen, body, got, rw, sw, out, fin}:
      meth

def st.path(r: St) -> Bytes():
  match r:
    case St{id, ss, meth, path, clen, body, got, rw, sw, out, fin}:
      path

def st.clen(r: St) -> Maybe<&2, Nat>:
  match r:
    case St{id, ss, meth, path, clen, body, got, rw, sw, out, fin}:
      clen

def st.body(r: St) -> Bytes():
  match r:
    case St{id, ss, meth, path, clen, body, got, rw, sw, out, fin}:
      body

def st.got(r: St) -> Nat:
  match r:
    case St{id, ss, meth, path, clen, body, got, rw, sw, out, fin}:
      got

def st.rw(r: St) -> Nat:
  match r:
    case St{id, ss, meth, path, clen, body, got, rw, sw, out, fin}:
      rw

def st.sw(r: St) -> Sw:
  match r:
    case St{id, ss, meth, path, clen, body, got, rw, sw, out, fin}:
      sw

def st.out(r: St) -> Bytes():
  match r:
    case St{id, ss, meth, path, clen, body, got, rw, sw, out, fin}:
      out

def st.fin(r: St) -> Bool:
  match r:
    case St{id, ss, meth, path, clen, body, got, rw, sw, out, fin}:
      fin

def st.w.id(r: St, v: U32) -> St:
  match r:
    case St{_id, ss, meth, path, clen, body, got, rw, sw, out, fin}:
      St{v, ss, meth, path, clen, body, got, rw, sw, out, fin}

def st.w.ss(r: St, v: Ss) -> St:
  match r:
    case St{id, _ss, meth, path, clen, body, got, rw, sw, out, fin}:
      St{id, v, meth, path, clen, body, got, rw, sw, out, fin}

def st.w.meth(r: St, v: Bytes()) -> St:
  match r:
    case St{id, ss, _meth, path, clen, body, got, rw, sw, out, fin}:
      St{id, ss, v, path, clen, body, got, rw, sw, out, fin}

def st.w.path(r: St, v: Bytes()) -> St:
  match r:
    case St{id, ss, meth, _path, clen, body, got, rw, sw, out, fin}:
      St{id, ss, meth, v, clen, body, got, rw, sw, out, fin}

def st.w.clen(r: St, v: Maybe<&2, Nat>) -> St:
  match r:
    case St{id, ss, meth, path, _clen, body, got, rw, sw, out, fin}:
      St{id, ss, meth, path, v, body, got, rw, sw, out, fin}

def st.w.body(r: St, v: Bytes()) -> St:
  match r:
    case St{id, ss, meth, path, clen, _body, got, rw, sw, out, fin}:
      St{id, ss, meth, path, clen, v, got, rw, sw, out, fin}

def st.w.got(r: St, v: Nat) -> St:
  match r:
    case St{id, ss, meth, path, clen, body, _got, rw, sw, out, fin}:
      St{id, ss, meth, path, clen, body, v, rw, sw, out, fin}

def st.w.rw(r: St, v: Nat) -> St:
  match r:
    case St{id, ss, meth, path, clen, body, got, _rw, sw, out, fin}:
      St{id, ss, meth, path, clen, body, got, v, sw, out, fin}

def st.w.sw(r: St, v: Sw) -> St:
  match r:
    case St{id, ss, meth, path, clen, body, got, rw, _sw, out, fin}:
      St{id, ss, meth, path, clen, body, got, rw, v, out, fin}

def st.w.out(r: St, v: Bytes()) -> St:
  match r:
    case St{id, ss, meth, path, clen, body, got, rw, sw, _out, fin}:
      St{id, ss, meth, path, clen, body, got, rw, sw, v, fin}

def st.w.fin(r: St, v: Bool) -> St:
  match r:
    case St{id, ss, meth, path, clen, body, got, rw, sw, out, _fin}:
      St{id, ss, meth, path, clen, body, got, rw, sw, out, v}


# The stream table: the streams at work, each id once. A stream is
# taken out while a frame or an answer works on it, and put back after,
# so each is held in one place; a look at a stream's state reads it
# where it is.
#
# It is a trie on the id's low bits (a client's ids are odd, so the bits
# above the lowest): seven levels, then a bucket of the streams whose
# ids agree on those bits (two only when one lives while 128 others
# open), so a look, a take and a put walk seven nodes whatever the
# table holds; a branch left empty is pruned. The table keeps its count.

# a bucket: whether its first stream has id sid
def b.at(+b: List<&2, St>, +sid: U32) -> Bool:
  match b:
    case Nil{}:
      False{}
    case Con{+s, t}:
      U32.is_eq(st.id(s), sid)

# The walks stop at the stream they look for (hit says the head is it):
# the first is the only one, and what follows it is kept untouched.
def b.look.go(b: List<&2, St>, +sid: U32, d: Ss, hit: Bool) -> Ss:
  match b hit:
    case Nil{} _:
      d
    case Con{s, t} True{}:
      st.ss(s)
    case Con{s, +t} False{}:
      b.look.go(t, sid, d, b.at(t, sid))

def b.look(+b: List<&2, St>, +sid: U32, d: Ss) -> Ss:
  b.look.go(b, sid, d, b.at(b, sid))

# a bucket's stream sid taken out, and the bucket without it
type Bt is Data:
  Bt{m: Maybe<&2, St>, b: List<&2, St>}

def bt.cons(s: St, k: Bt) -> Bt:
  match k:
    case Bt{m, r}:
      Bt{m, Con{s, r}}

def b.take.go(b: List<&2, St>, +sid: U32, hit: Bool) -> Bt:
  match b hit:
    case Nil{} _:
      Bt{None{}, Nil{}}
    case Con{s, t} True{}:
      Bt{Some{s}, t}
    case Con{s, +t} False{}:
      bt.cons(s, b.take.go(t, sid, b.at(t, sid)))

def b.take(+b: List<&2, St>, +sid: U32) -> Bt:
  b.take.go(b, sid, b.at(b, sid))

type Tr is Data:
  TNone{}
  TLeaf{b: List<&2, St>}
  TNode{lo: Tr, hi: Tr}

def key(+sid: U32) -> U32:
  U32.shrn(sid, 1n)

def bit(+k: U32) -> Bool:
  Bool.not(U32.is_zero(U32.and(k, 1)))

def tr.look(t: Tr, +k: U32, +sid: U32, d: Ss, hi: Bool) -> Ss:
  match t hi:
    case TNone{} _:
      d
    case TLeaf{b} _:
      b.look(b, sid, d)
    case TNode{l, h} False{}:
      tr.look(l, U32.shrn(k, 1n), sid, d, bit(U32.shrn(k, 1n)))
    case TNode{l, h} True{}:
      tr.look(h, U32.shrn(k, 1n), sid, d, bit(U32.shrn(k, 1n)))

# a branch with nothing left in it is pruned
def tr.node(l: Tr, h: Tr) -> Tr:
  match l h:
    case TNone{} TNone{}:
      TNone{}
    case TNone{} TLeaf{b}:
      TNode{TNone{}, TLeaf{b}}
    case TNone{} TNode{a, c}:
      TNode{TNone{}, TNode{a, c}}
    case TLeaf{b} _:
      TNode{TLeaf{b}, h}
    case TNode{a, c} _:
      TNode{TNode{a, c}, h}

def tr.bucket(b: List<&2, St>) -> Tr:
  match b:
    case Nil{}:
      TNone{}
    case Con{s, t}:
      TLeaf{Con{s, t}}

type Tt is Data:
  Tt{m: Maybe<&2, St>, t: Tr}

def tt.b(k: Bt) -> Tt:
  match k:
    case Bt{m, b}:
      Tt{m, tr.bucket(b)}

def tt.lo(k: Tt, h: Tr) -> Tt:
  match k:
    case Tt{m, l}:
      Tt{m, tr.node(l, h)}

def tt.hi(l: Tr, k: Tt) -> Tt:
  match k:
    case Tt{m, h}:
      Tt{m, tr.node(l, h)}

def tr.take(t: Tr, +k: U32, +sid: U32, hi: Bool) -> Tt:
  match t hi:
    case TNone{} _:
      Tt{None{}, TNone{}}
    case TLeaf{b} _:
      tt.b(b.take(b, sid))
    case TNode{l, h} False{}:
      tt.lo(tr.take(l, U32.shrn(k, 1n), sid, bit(U32.shrn(k, 1n))), h)
    case TNode{l, h} True{}:
      tt.hi(l, tr.take(h, U32.shrn(k, 1n), sid, bit(U32.shrn(k, 1n))))

def tr.side(hi: Bool, c: Tr) -> Tr:
  match hi:
    case False{}:
      TNode{c, TNone{}}
    case True{}:
      TNode{TNone{}, c}

# a new branch down to s's bucket, d levels deep
def tr.path(d: Nat, +k: U32, s: St) -> Tr:
  match d:
    case 0n:
      TLeaf{Con{s, Nil{}}}
    case 1n+e:
      tr.side(bit(k), tr.path(e, U32.shrn(k, 1n), s))

def tr.ins(t: Tr, +k: U32, +d: Nat, s: St, hi: Bool) -> Tr:
  match t hi:
    case TNone{} _:
      tr.path(d, k, s)
    case TLeaf{b} _:
      TLeaf{Con{s, b}}
    case TNode{l, h} False{}:
      TNode{tr.ins(l, U32.shrn(k, 1n), Nat.sub(d, 1n), s, bit(U32.shrn(k, 1n))), h}
    case TNode{l, h} True{}:
      TNode{l, tr.ins(h, U32.shrn(k, 1n), Nat.sub(d, 1n), s, bit(U32.shrn(k, 1n)))}

def tr.depth() -> Nat:
  7n

# the table: how many streams, and the trie
type Tb is Data:
  Tb{n: Nat, t: Tr}

type Tk is Data:
  Tk{m: Maybe<&2, St>, sts: Tb}

# the state of stream sid, or d when it is not at work
def st.look(+sts: Tb, +sid: U32, d: Ss) -> Ss:
  match sts:
    case Tb{n, t}:
      tr.look(t, key(sid), sid, d, bit(key(sid)))

def tk.of(+n: Nat, k: Tt) -> Tk:
  match k:
    case Tt{m, t}:
      match m:
        case None{}:
          Tk{None{}, Tb{n, t}}
        case Some{s}:
          Tk{Some{s}, Tb{Nat.sub(n, 1n), t}}

# stream sid taken out, and the table without it
def st.take(sts: Tb, +sid: U32) -> Tk:
  match sts:
    case Tb{n, t}:
      tk.of(n, tr.take(t, key(sid), sid, bit(key(sid))))

def st.del.of(k: Tk) -> Tb:
  match k:
    case Tk{m, r}:
      r

def st.del(sts: Tb, +sid: U32) -> Tb:
  st.del.of(st.take(sts, sid))

# a stream put in that the table does not hold (a new one, or one taken)
def st.ins(sts: Tb, +s: St) -> Tb:
  match sts:
    case Tb{n, t}:
      +k = key(st.id(s))
      Tb{1n+n, tr.ins(t, k, tr.depth(), s, bit(k))}

def st.count(+sts: Tb) -> Nat:
  match sts:
    case Tb{n, t}:
      n

def st.empty() -> Tb:
  Tb{0n, TNone{}}

# stream ids, one list type of their own (a U32 is read in place)
type Ids is Data:
  INil{}
  ICon{id: U32, t: Ids}

def mem.go(xs: Ids, +x: U32, acc: Bool) -> Bool:
  match xs:
    case INil{}:
      acc
    case ICon{y, t}:
      mem.go(t, x, acc || U32.is_eq(x, y))

def mem(+xs: Ids, +x: U32) -> Bool:
  mem.go(xs, x, False{})

def ids.take(n: Nat, xs: Ids) -> Ids:
  match n xs:
    case 0n _:
      INil{}
    case 1n+k INil{}:
      INil{}
    case 1n+k ICon{x, t}:
      ICon{x, ids.take(k, t)}

# the streams we reset lately, whose late frames are ignored (5.1:
# "closed"); the newest sixteen are kept
def gone.add(xs: Ids, sid: U32) -> Ids:
  ids.take(16n, ICon{sid, xs})

# A stream's state as the server sees it (5.1), when it is not at work:
# one it reset lately is reset; one above every id seen is idle; any
# other is closed.
def state.none(reset: Bool, idle: Bool) -> Ss:
  match reset idle:
    case True{} _:
      SReset{}
    case False{} True{}:
      SIdle{}
    case False{} False{}:
      SClosed{}

# The connection
# ==============

# The budgets (RFC 9113 10.5): what a peer may make the server do for
# nothing -- answer a PING, acknowledge a SETTINGS, take a reset of a
# stream it opened -- is counted down, and a peer that spends one past
# zero is told ENHANCE_YOUR_CALM and let go. Each response the server
# completes gives one of each back, up to the cap, so an ordinary
# client never meets them and a flood (a rapid reset, CVE-2023-44487;
# a PING or SETTINGS flood) meets them within cap frames.
type Bud is Data:
  Bud{ping: Nat, set: Nat, rst: Nat}

def bud.cap() -> Nat:
  64n

def bud.new() -> Bud:
  Bud{bud.cap(), bud.cap(), bud.cap()}

def bud.up(+n: Nat) -> Nat:
  Nat.min(1n+n, bud.cap())

def bud.refill(b: Bud) -> Bud:
  match b:
    case Bud{p, s, r}:
      Bud{bud.up(p), bud.up(s), bud.up(r)}

# the most a header block may take, all its HEADERS and CONTINUATION
# fragments together (a CONTINUATION flood, CVE-2024-27316, meets it)
def blk.cap() -> Nat:
  65536n

# the most a request body may hold
def body.cap() -> Nat:
  1048576n

# the most streams open at once (our SETTINGS_MAX_CONCURRENT_STREAMS)
def streams.max() -> Nat:
  100n

# the window we give every stream and the connection, kept open: what a
# frame takes is given back as the frame is read
def win.ours() -> Nat:
  65535n

# A header block's kind: a request's first, a request's trailers, or one
# decoded only to keep the table in step and then dropped (its stream
# refused with code, or with nothing when code is 0)
type Bk is Data:
  BkReq{}
  BkTrail{}
  BkDrop{code: U32}

type Blk is Data:
  BNone{}
  BIn{sid: U32, end: Bool, k: Bk, size: Nat}

# The connection: the frame reader; the HPACK decoder, and the encoder's
# table with whether a size update is owed; the streams at work and the
# ones we reset lately; the highest stream id opened; the header block
# in progress; the connection's windows (what we may send, what the peer
# may send); the peer's SETTINGS_INITIAL_WINDOW_SIZE and
# SETTINGS_MAX_FRAME_SIZE; the budgets; whether our SETTINGS went out.
type Cn is Data:
  Cn{rd: Fm.Rd, hd: K.Dec, he: K.Tbl, hup: Bool, sts: Tb, gone: Ids,
    last: U32, blk: Blk, csw: Sw, crw: Nat, init: Nat, fmax: Nat, bud: Bud, said: Bool}

def cn.new() -> Cn:
  Cn{Fm.new(16384n), K.dec.new(4096n, 65536n), K.tbl.new(4096n), False{}, st.empty(), INil{}, 0, BNone{},
    sw.new(65535n), win.ours(), 65535n, 16384n, bud.new(), False{}}

def cn.rd(r: Cn) -> Fm.Rd:
  match r:
    case Cn{rd, hd, he, hup, sts, gone, last, blk, csw, crw, init, fmax, bud, said}:
      rd

def cn.hd(r: Cn) -> K.Dec:
  match r:
    case Cn{rd, hd, he, hup, sts, gone, last, blk, csw, crw, init, fmax, bud, said}:
      hd

def cn.he(r: Cn) -> K.Tbl:
  match r:
    case Cn{rd, hd, he, hup, sts, gone, last, blk, csw, crw, init, fmax, bud, said}:
      he

def cn.hup(r: Cn) -> Bool:
  match r:
    case Cn{rd, hd, he, hup, sts, gone, last, blk, csw, crw, init, fmax, bud, said}:
      hup

def cn.sts(r: Cn) -> Tb:
  match r:
    case Cn{rd, hd, he, hup, sts, gone, last, blk, csw, crw, init, fmax, bud, said}:
      sts

def cn.gone(r: Cn) -> Ids:
  match r:
    case Cn{rd, hd, he, hup, sts, gone, last, blk, csw, crw, init, fmax, bud, said}:
      gone

def cn.last(r: Cn) -> U32:
  match r:
    case Cn{rd, hd, he, hup, sts, gone, last, blk, csw, crw, init, fmax, bud, said}:
      last

def cn.blk(r: Cn) -> Blk:
  match r:
    case Cn{rd, hd, he, hup, sts, gone, last, blk, csw, crw, init, fmax, bud, said}:
      blk

def cn.csw(r: Cn) -> Sw:
  match r:
    case Cn{rd, hd, he, hup, sts, gone, last, blk, csw, crw, init, fmax, bud, said}:
      csw

def cn.crw(r: Cn) -> Nat:
  match r:
    case Cn{rd, hd, he, hup, sts, gone, last, blk, csw, crw, init, fmax, bud, said}:
      crw

def cn.init(r: Cn) -> Nat:
  match r:
    case Cn{rd, hd, he, hup, sts, gone, last, blk, csw, crw, init, fmax, bud, said}:
      init

def cn.fmax(r: Cn) -> Nat:
  match r:
    case Cn{rd, hd, he, hup, sts, gone, last, blk, csw, crw, init, fmax, bud, said}:
      fmax

def cn.bud(r: Cn) -> Bud:
  match r:
    case Cn{rd, hd, he, hup, sts, gone, last, blk, csw, crw, init, fmax, bud, said}:
      bud

def cn.said(r: Cn) -> Bool:
  match r:
    case Cn{rd, hd, he, hup, sts, gone, last, blk, csw, crw, init, fmax, bud, said}:
      said

def cn.w.rd(r: Cn, v: Fm.Rd) -> Cn:
  match r:
    case Cn{_rd, hd, he, hup, sts, gone, last, blk, csw, crw, init, fmax, bud, said}:
      Cn{v, hd, he, hup, sts, gone, last, blk, csw, crw, init, fmax, bud, said}

def cn.w.hd(r: Cn, v: K.Dec) -> Cn:
  match r:
    case Cn{rd, _hd, he, hup, sts, gone, last, blk, csw, crw, init, fmax, bud, said}:
      Cn{rd, v, he, hup, sts, gone, last, blk, csw, crw, init, fmax, bud, said}

def cn.w.he(r: Cn, v: K.Tbl) -> Cn:
  match r:
    case Cn{rd, hd, _he, hup, sts, gone, last, blk, csw, crw, init, fmax, bud, said}:
      Cn{rd, hd, v, hup, sts, gone, last, blk, csw, crw, init, fmax, bud, said}

def cn.w.hup(r: Cn, v: Bool) -> Cn:
  match r:
    case Cn{rd, hd, he, _hup, sts, gone, last, blk, csw, crw, init, fmax, bud, said}:
      Cn{rd, hd, he, v, sts, gone, last, blk, csw, crw, init, fmax, bud, said}

def cn.w.sts(r: Cn, v: Tb) -> Cn:
  match r:
    case Cn{rd, hd, he, hup, _sts, gone, last, blk, csw, crw, init, fmax, bud, said}:
      Cn{rd, hd, he, hup, v, gone, last, blk, csw, crw, init, fmax, bud, said}

def cn.w.gone(r: Cn, v: Ids) -> Cn:
  match r:
    case Cn{rd, hd, he, hup, sts, _gone, last, blk, csw, crw, init, fmax, bud, said}:
      Cn{rd, hd, he, hup, sts, v, last, blk, csw, crw, init, fmax, bud, said}

def cn.w.last(r: Cn, v: U32) -> Cn:
  match r:
    case Cn{rd, hd, he, hup, sts, gone, _last, blk, csw, crw, init, fmax, bud, said}:
      Cn{rd, hd, he, hup, sts, gone, v, blk, csw, crw, init, fmax, bud, said}

def cn.w.blk(r: Cn, v: Blk) -> Cn:
  match r:
    case Cn{rd, hd, he, hup, sts, gone, last, _blk, csw, crw, init, fmax, bud, said}:
      Cn{rd, hd, he, hup, sts, gone, last, v, csw, crw, init, fmax, bud, said}

def cn.w.csw(r: Cn, v: Sw) -> Cn:
  match r:
    case Cn{rd, hd, he, hup, sts, gone, last, blk, _csw, crw, init, fmax, bud, said}:
      Cn{rd, hd, he, hup, sts, gone, last, blk, v, crw, init, fmax, bud, said}

def cn.w.crw(r: Cn, v: Nat) -> Cn:
  match r:
    case Cn{rd, hd, he, hup, sts, gone, last, blk, csw, _crw, init, fmax, bud, said}:
      Cn{rd, hd, he, hup, sts, gone, last, blk, csw, v, init, fmax, bud, said}

def cn.w.init(r: Cn, v: Nat) -> Cn:
  match r:
    case Cn{rd, hd, he, hup, sts, gone, last, blk, csw, crw, _init, fmax, bud, said}:
      Cn{rd, hd, he, hup, sts, gone, last, blk, csw, crw, v, fmax, bud, said}

def cn.w.fmax(r: Cn, v: Nat) -> Cn:
  match r:
    case Cn{rd, hd, he, hup, sts, gone, last, blk, csw, crw, init, _fmax, bud, said}:
      Cn{rd, hd, he, hup, sts, gone, last, blk, csw, crw, init, v, bud, said}

def cn.w.bud(r: Cn, v: Bud) -> Cn:
  match r:
    case Cn{rd, hd, he, hup, sts, gone, last, blk, csw, crw, init, fmax, _bud, said}:
      Cn{rd, hd, he, hup, sts, gone, last, blk, csw, crw, init, fmax, v, said}

def cn.w.said(r: Cn, v: Bool) -> Cn:
  match r:
    case Cn{rd, hd, he, hup, sts, gone, last, blk, csw, crw, init, fmax, bud, _said}:
      Cn{rd, hd, he, hup, sts, gone, last, blk, csw, crw, init, fmax, bud, v}

# The connection is held once: what a frame changes is changed in one
# match, and what it only reads (a stream's state, the stream count,
# the header block in progress) is read where it is.

# a stream taken out of the connection's table
type Ct is Data:
  Ct{m: Maybe<&2, St>, c: Cn}

def cn.take.go(rd: Fm.Rd, hd: K.Dec, he: K.Tbl, hup: Bool, gone: Ids, last: U32, blk: Blk, csw: Sw,
  crw: Nat, init: Nat, fmax: Nat, bud: Bud, said: Bool, k: Tk) -> Ct:
  match k:
    case Tk{m, sts}:
      Ct{m, Cn{rd, hd, he, hup, sts, gone, last, blk, csw, crw, init, fmax, bud, said}}

def cn.take(c: Cn, +sid: U32) -> Ct:
  match c:
    case Cn{rd, hd, he, hup, sts, gone, last, blk, csw, crw, init, fmax, bud, said}:
      cn.take.go(rd, hd, he, hup, gone, last, blk, csw, crw, init, fmax, bud, said, st.take(sts, sid))

# a stream the table does not hold put in
def cn.ins(c: Cn, s: St) -> Cn:
  match c:
    case Cn{rd, hd, he, hup, sts, gone, last, blk, csw, crw, init, fmax, bud, said}:
      Cn{rd, hd, he, hup, st.ins(sts, s), gone, last, blk, csw, crw, init, fmax, bud, said}

def cn.count(c: Cn) -> Nat:
  match c:
    case Cn{rd, hd, he, hup, sts, gone, last, blk, csw, crw, init, fmax, bud, said}:
      st.count(sts)



# What reading frames produces: the connection, the bytes to write, the
# requests completed (newest first), and whether the connection is over.
type Out is Data:
  Out{c: Cn, w: Bytes(), rq: List<&2, Req>, dead: Bool}

# A connection error (5.4.1): GOAWAY with the last stream id and the
# code, and nothing more is read.
def die(+c: Cn, w: Bytes(), rq: List<&2, Req>, +code: U32) -> Out:
  Out{c, Bytes.append(w, f.goaway(cn.last(c), code)), rq, True{}}

# A stream error (5.4.2): RST_STREAM, the stream dropped and remembered
# as reset, so what the peer sent before it saw the reset is ignored.
def rst(c: Cn, w: Bytes(), rq: List<&2, Req>, +sid: U32, +code: U32) -> Out:
  match c:
    case Cn{rd, hd, he, hup, sts, gone, last, blk, csw, crw, init, fmax, bud, said}:
      Out{Cn{rd, hd, he, hup, st.del(sts, sid), gone.add(gone, sid), last, blk, csw, crw, init, fmax, bud, said},
        Bytes.append(w, f.rst(sid, code)), rq, False{}}

def ok(c: Cn, w: Bytes(), rq: List<&2, Req>) -> Out:
  Out{c, w, rq, False{}}

# a stream's state (5.1), from the connection
def state(+c: Cn, +sid: U32) -> Ss:
  match c:
    case Cn{rd, hd, he, hup, sts, gone, +last, blk, csw, crw, init, fmax, bud, said}:
      st.look(sts, sid, state.none(mem(gone, sid), U32.is_lt(last, sid)))

def on(b: Bool, +n: Nat, +m: Nat) -> Nat:
  match b:
    case True{}:
      n
    case False{}:
      m

# A WINDOW_UPDATE giving back what a frame took, when it took anything
# (an increment of 0 is itself an error).
def give(+sid: U32, +n: Nat) -> Bytes():
  match n:
    case 0n:
      ""
    case 1n+m:
      f.win(sid, U32.from_nat(1n+m))

# END_STREAM on a request: its content-length, if it gave one, must be
# what its DATA came to (8.1.1); then it is half-closed (remote) and
# goes to be answered.
# (the stream is not in the table: a new one, or one taken out; what it
# asked goes with the request, and the stream keeps what its response
# needs)
def ended.go(c: Cn, w: Bytes(), rq: List<&2, Req>, +id: U32, meth: Bytes(), path: Bytes(), cl: Maybe<&2, Nat>,
  body: Bytes(), got: Nat, rw: Nat, sw: Sw, o: Bytes(), fin: Bool, fine: Bool) -> Out:
  match fine:
    case True{}:
      ok(cn.ins(c, St{id, SHalf{}, "", "", cl, "", got, rw, sw, o, fin}), w, Con{Req{id, meth, path, body}, rq})
    case False{}:
      rst(c, w, rq, id, e.proto())

def ended(c: Cn, w: Bytes(), rq: List<&2, Req>, s: St) -> Out:
  match s:
    case St{id, ss, meth, path, +cl, body, +got, rw, sw, o, fin}:
      ended.go(c, w, rq, id, meth, path, cl, body, got, rw, sw, o, fin, clen.fine(cl, got))

# a content-length is never passed
def clen.fine.le(m: Maybe<&2, Nat>, +n: Nat) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      Nat.is_le(n, x)

def data.st.end(c: Cn, w: Bytes(), rq: List<&2, Req>, s: St, end: Bool) -> Out:
  match end:
    case True{}:
      ended(c, w, rq, s)
    case False{}:
      ok(cn.ins(c, s), w, rq)

# DATA (6.1) on a stream that is open: under both windows, under the
# body's cap and under its content-length; the windows given back.
def data.st.go(c: Cn, w: Bytes(), rq: List<&2, Req>, win: Bool, cap: Bool, cl: Bool, s: St, +fl: U32,
  +len: Nat, +data: Bytes()) -> Out:
  match win cap cl:
    case False{} _ _:
      rst(c, w, rq, st.id(s), e.flow())
    case True{} False{} _:
      rst(c, w, rq, st.id(s), e.calm())
    case True{} True{} False{}:
      rst(c, w, rq, st.id(s), e.proto())
    case True{} True{} True{}:
      match s:
        case St{+id, ss, meth, path, cl2, body, got, rw, sw, o, fin}:
          +n = Bytes.len(data)
          data.st.end(c, Bytes.append(w, give(id, on(flag(fl, 1), 0n, len))), rq,
            St{id, ss, meth, path, cl2, Bytes.append(body, data), Nat.add(got, n), rw, sw, o, fin},
            flag(fl, 1))

def data.st(ct: Ct, w: Bytes(), rq: List<&2, Req>, +fl: U32, +len: Nat, +data: Bytes()) -> Out:
  match ct:
    case Ct{None{}, c}:
      ok(c, w, rq)
    case Ct{Some{+s}, c}:
      +got = Nat.add(st.got(s), Bytes.len(data))
      data.st.go(c, w, rq, Nat.is_le(len, st.rw(s)), Nat.is_le(got, body.cap()),
        clen.fine.le(st.clen(s), got), s, fl, len, data)

# the connection's window first: DATA past it ends the connection
def data.conn(+c: Cn, w: Bytes(), rq: List<&2, Req>, +fl: U32, +sid: U32, +len: Nat, +data: Bytes(), fits: Bool) -> Out:
  match fits:
    case False{}:
      die(c, w, rq, e.flow())
    case True{}:
      data.st(cn.take(c, sid), Bytes.append(w, give(0, len)), rq, fl, len, data)

def data.vd(+c: Cn, w: Bytes(), rq: List<&2, Req>, +fl: U32, +sid: U32, +len: Nat, +data: Bytes(), v: Vd) -> Out:
  match v:
    case VConn{code}:
      die(c, w, rq, code)
    case VStream{code}:
      rst(c, Bytes.append(w, give(0, len)), rq, sid, code)
    case VOk{}:
      data.conn(c, w, rq, fl, sid, len, data, Nat.is_le(len, cn.crw(c)))

def data.padded(+c: Cn, w: Bytes(), rq: List<&2, Req>, +fl: U32, +sid: U32, +len: Nat, +data: Bytes(), bad: Bool) -> Out:
  match bad:
    case True{}:
      die(c, w, rq, e.proto())
    case False{}:
      data.vd(c, w, rq, fl, sid, len, data, verdict(state(c, sid), TData{}))

# padding (6.1): a pad length that is the payload's length or more is a
# connection error
def data.pad(+c: Cn, w: Bytes(), rq: List<&2, Req>, +fl: U32, +sid: U32, +pay: Bytes(), padded: Bool, +len: Nat) -> Out:
  match padded len:
    case False{} _:
      data.vd(c, w, rq, fl, sid, len, pay, verdict(state(c, sid), TData{}))
    case True{} 0n:
      die(c, w, rq, e.proto())
    case True{} 1n+l:
      +pl = U32.to_nat(Bytes.get(pay, 0n))
      data.padded(c, w, rq, fl, sid, 1n+l, Bytes.slice(pay, 1n, Nat.sub(l, pl)), Nat.is_le(1n+l, pl))

def h.data.go(+c: Cn, w: Bytes(), rq: List<&2, Req>, +fl: U32, +sid: U32, +pay: Bytes(), z: Bool) -> Out:
  match z:
    case True{}:
      die(c, w, rq, e.proto())
    case False{}:
      data.pad(c, w, rq, fl, sid, pay, flag(fl, 8), Bytes.len(pay))

def h.data(+c: Cn, w: Bytes(), rq: List<&2, Req>, +fl: U32, +sid: U32, +pay: Bytes()) -> Out:
  h.data.go(c, w, rq, fl, sid, pay, U32.is_zero(sid))

# Header blocks
# =============

def open.st(c: Cn, w: Bytes(), rq: List<&2, Req>, s: St, end: Bool) -> Out:
  match end:
    case True{}:
      ended(c, w, rq, s)
    case False{}:
      ok(cn.ins(c, s), w, rq)

# a new stream, its request's head whole: open, or half-closed (remote)
# at once when the HEADERS ended it
def open.head(+c: Cn, w: Bytes(), rq: List<&2, Req>, +sid: U32, +end: Bool, h: Head) -> Out:
  match h:
    case HBad{}:
      rst(c, w, rq, sid, e.proto())
    case HOk{meth, path, cl}:
      +init = cn.init(c)
      open.st(c, w, rq, St{sid, SOpen{}, meth, path, cl, "", 0n, win.ours(), sw.new(init), "", False{}}, end)

# trailers: only with END_STREAM (8.1), and no pseudo-header in them
def trail(ct: Ct, w: Bytes(), rq: List<&2, Req>, +sid: U32, fine: Bool) -> Out:
  match ct fine:
    case Ct{None{}, c} _:
      ok(c, w, rq)
    case Ct{Some{s}, c} True{}:
      ended(c, w, rq, s)
    case Ct{Some{s}, c} False{}:
      rst(c, w, rq, sid, e.proto())

def drop.blk(+c: Cn, w: Bytes(), rq: List<&2, Req>, +sid: U32, +code: U32, none: Bool) -> Out:
  match none:
    case True{}:
      ok(c, w, rq)
    case False{}:
      rst(c, w, rq, sid, code)

# a header block complete (END_HEADERS): decoded whole, or a
# COMPRESSION_ERROR (4.3); then what its kind says
def blk.kind(+c: Cn, w: Bytes(), rq: List<&2, Req>, +sid: U32, +end: Bool, k: Bk, +fs: List<&2, K.Fld>) -> Out:
  match k:
    case BkReq{}:
      open.head(c, w, rq, sid, end, req.check(fs))
    case BkTrail{}:
      trail(cn.take(c, sid), w, rq, sid, end && trailers.ok(fs))
    case BkDrop{+code}:
      drop.blk(c, w, rq, sid, code, U32.is_zero(code))

def blk.done(+c: Cn, w: Bytes(), rq: List<&2, Req>, +sid: U32, +end: Bool, k: Bk, b: K.Blk) -> Out:
  match b:
    case K.BBad{why}:
      die(c, w, rq, e.compress())
    case K.BOk{d, fs}:
      blk.kind(cn.w.hd(c, d), w, rq, sid, end, k, fs)

# the decoder fed a fragment: the block's last, which ends the block
# (the connection's decoder a placeholder until the block is whole), or
# one more, whose CONTINUATION is awaited
def blk.last(+root: H.Ht, c: Cn, w: Bytes(), rq: List<&2, Req>, +sid: U32, +end: Bool, k: Bk, +frag: Bytes()) -> Out:
  match c:
    case Cn{rd, hd, he, hup, sts, gone, last, blk, csw, crw, init, fmax, bud, said}:
      blk.done(Cn{rd, K.dec.new(0n, 0n), he, hup, sts, gone, last, BNone{}, csw, crw, init, fmax, bud, said}, w, rq,
        sid, end, k, K.dec.end(K.feed_buf(root, frag, hd)))

def blk.next(+root: H.Ht, c: Cn, +frag: Bytes(), b: Blk) -> Cn:
  match c:
    case Cn{rd, hd, he, hup, sts, gone, last, blk, csw, crw, init, fmax, bud, said}:
      Cn{rd, K.feed_buf(root, frag, hd), he, hup, sts, gone, last, b, csw, crw, init, fmax, bud, said}

# a fragment fed to the decoder: past the block's cap the connection
# ends; with END_HEADERS the block is done, else it waits for its
# CONTINUATION
def blk.more(+root: H.Ht, +c: Cn, w: Bytes(), rq: List<&2, Req>, +sid: U32, +end: Bool, k: Bk, +size: Nat,
  frag: Bytes(), big: Bool, eoh: Bool) -> Out:
  match big eoh:
    case True{} _:
      die(c, w, rq, e.calm())
    case False{} True{}:
      blk.last(root, c, w, rq, sid, end, k, frag)
    case False{} False{}:
      ok(blk.next(root, c, frag, BIn{sid, end, k, size}), w, rq)

def blk.feed(+root: H.Ht, +c: Cn, w: Bytes(), rq: List<&2, Req>, +sid: U32, +end: Bool, k: Bk, +size: Nat,
  +frag: Bytes(), eoh: Bool) -> Out:
  blk.more(root, c, w, rq, sid, end, k, size, frag, Nat.is_lt(blk.cap(), size), eoh)

def cn.begin(c: Cn) -> Cn:
  match c:
    case Cn{rd, hd, he, hup, sts, gone, last, blk, csw, crw, init, fmax, bud, said}:
      Cn{rd, K.dec.begin(hd), he, hup, sts, gone, last, blk, csw, crw, init, fmax, bud, said}

# a block's first fragment: the decoder begins a block
def blk.start(+root: H.Ht, +c: Cn, w: Bytes(), rq: List<&2, Req>, +sid: U32, +end: Bool, k: Bk, +frag: Bytes(),
  eoh: Bool) -> Out:
  blk.feed(root, cn.begin(c), w, rq, sid, end, k, Bytes.len(frag), frag, eoh)

# CONTINUATION (6.10): only on the block's stream, straight after its
# HEADERS or CONTINUATION; anything else is a PROTOCOL_ERROR
def h.cont(+root: H.Ht, +c: Cn, w: Bytes(), rq: List<&2, Req>, +fl: U32, +pay: Bytes(), b: Blk, same: Bool) -> Out:
  match b same:
    case BNone{} _:
      die(c, w, rq, e.proto())
    case BIn{sid, end, k, size} False{}:
      die(c, w, rq, e.proto())
    case BIn{sid, end, k, size} True{}:
      blk.feed(root, c, w, rq, sid, end, k, Nat.add(size, Bytes.len(pay)), pay, flag(fl, 4))

def hdr.new(room: Bool) -> Bk:
  match room:
    case True{}:
      BkReq{}
    case False{}:
      BkDrop{e.refused()}

# HEADERS (6.2) on a stream the verdict let through: an idle stream
# opens (its id odd, 5.1.1, and within SETTINGS_MAX_CONCURRENT_STREAMS,
# else refused); an open one takes trailers; a reset one's block is
# decoded and dropped. A stream that depends on itself (5.3.1) is a
# stream error.
def hdr.kind(+c: Cn, +sid: U32, s: Ss, self: Bool) -> Bk:
  match s self:
    case _ True{}:
      BkDrop{e.proto()}
    case SIdle{} False{}:
      hdr.new(Nat.is_lt(cn.count(c), streams.max()))
    case SOpen{} False{}:
      BkTrail{}
    case _ False{}:
      BkDrop{0}

def last.max(+last: U32, +sid: U32, above: Bool) -> U32:
  match above:
    case True{}:
      sid
    case False{}:
      last

def is.idle(s: Ss) -> Bool:
  match s:
    case SIdle{}:
      True{}
    case _:
      False{}

# the highest stream id opened, moved to sid when that is above it
def cn.opened(c: Cn, +sid: U32) -> Cn:
  match c:
    case Cn{rd, hd, he, hup, sts, gone, +last, blk, csw, crw, init, fmax, bud, said}:
      Cn{rd, hd, he, hup, sts, gone, last.max(last, sid, U32.is_lt(last, sid)), blk, csw, crw, init, fmax, bud, said}

def hdr.open(+root: H.Ht, +c: Cn, w: Bytes(), rq: List<&2, Req>, +fl: U32, +sid: U32, +frag: Bytes(), +self: Bool,
  +s: Ss, even: Bool) -> Out:
  match even:
    case True{}:
      die(c, w, rq, e.proto())
    case False{}:
      +k = hdr.kind(c, sid, s, self)
      blk.start(root, cn.opened(c, sid), w, rq, sid, flag(fl, 1), k, frag, flag(fl, 4))

def hdr.go(+root: H.Ht, +c: Cn, w: Bytes(), rq: List<&2, Req>, +fl: U32, +sid: U32, +frag: Bytes(), +self: Bool,
  +s: Ss, v: Vd) -> Out:
  match v:
    case VConn{code}:
      die(c, w, rq, code)
    case VStream{code}:
      blk.start(root, c, w, rq, sid, flag(fl, 1), BkDrop{code}, frag, flag(fl, 4))
    case VOk{}:
      hdr.open(root, c, w, rq, fl, sid, frag, self, s, is.idle(s) && U32.is_zero(U32.and(sid, 1)))

# the payload: a pad length (PADDED) and five bytes of priority
# (PRIORITY) before the fragment; padding past the payload is a
# connection error
def hdr.pay(+root: H.Ht, +c: Cn, w: Bytes(), rq: List<&2, Req>, +fl: U32, +sid: U32, +pay: Bytes(), +off: Nat,
  +pl: Nat, +prio: Bool, bad: Bool) -> Out:
  match bad:
    case True{}:
      die(c, w, rq, e.proto())
    case False{}:
      +s = state(c, sid)
      +self = prio && U32.is_eq(u31(be32(pay, on(flag(fl, 8), 1n, 0n))), sid)
      +n = Nat.sub(Nat.sub(Bytes.len(pay), off), pl)
      hdr.go(root, c, w, rq, fl, sid, Bytes.slice(pay, off, n), self, s, verdict(s, THeaders{}))

def h.headers.go(+root: H.Ht, +c: Cn, w: Bytes(), rq: List<&2, Req>, +fl: U32, +sid: U32, +pay: Bytes(), z: Bool) -> Out:
  match z:
    case True{}:
      die(c, w, rq, e.proto())
    case False{}:
      +padded = flag(fl, 8)
      +prio = flag(fl, 32)
      +off = Nat.add(on(padded, 1n, 0n), on(prio, 5n, 0n))
      +pl = on(padded, U32.to_nat(Bytes.get(pay, 0n)), 0n)
      hdr.pay(root, c, w, rq, fl, sid, pay, off, pl, prio, Nat.is_lt(Bytes.len(pay), Nat.add(off, pl)))

def h.headers(+root: H.Ht, +c: Cn, w: Bytes(), rq: List<&2, Req>, +fl: U32, +sid: U32, +pay: Bytes()) -> Out:
  h.headers.go(root, c, w, rq, fl, sid, pay, U32.is_zero(sid))

def prio.self(+c: Cn, w: Bytes(), rq: List<&2, Req>, +sid: U32, self: Bool) -> Out:
  match self:
    case True{}:
      rst(c, w, rq, sid, e.proto())
    case False{}:
      ok(c, w, rq)


def h.rst.pay(+c: Cn, w: Bytes(), rq: List<&2, Req>, b: Bud) -> Out:
  match b:
    case Bud{p, s, r}:
      match r:
        case 0n:
          die(c, w, rq, e.calm())
        case 1n+k:
          ok(cn.w.bud(c, Bud{p, s, k}), w, rq)

# PRIORITY (6.3): parsed and ignored; five bytes, on a stream, not on
# itself
def h.prio(+c: Cn, w: Bytes(), rq: List<&2, Req>, +sid: U32, +pay: Bytes(), z: Bool, five: Bool) -> Out:
  match z five:
    case True{} _:
      die(c, w, rq, e.proto())
    case False{} False{}:
      rst(c, w, rq, sid, e.size())
    case False{} True{}:
      prio.self(c, w, rq, sid, U32.is_eq(u31(be32(pay, 0n)), sid))
# RST_STREAM (6.4): four bytes, on a stream that is not idle. A peer's
# reset of a stream it opened is paid from its budget (a rapid reset
# meets it); the stream is then closed, and what the peer sends on it
# after is a STREAM_CLOSED.
def h.rst.st(ct: Ct, w: Bytes(), rq: List<&2, Req>) -> Out:
  match ct:
    case Ct{None{}, c}:
      ok(c, w, rq)
    case Ct{Some{s}, +c}:
      h.rst.pay(c, w, rq, cn.bud(c))

def h.rst.vd(+c: Cn, w: Bytes(), rq: List<&2, Req>, +sid: U32, v: Vd) -> Out:
  match v:
    case VConn{code}:
      die(c, w, rq, code)
    case VStream{code}:
      rst(c, w, rq, sid, code)
    case VOk{}:
      h.rst.st(cn.take(c, sid), w, rq)

def h.rst(+c: Cn, w: Bytes(), rq: List<&2, Req>, +sid: U32, z: Bool, four: Bool) -> Out:
  match z four:
    case True{} _:
      die(c, w, rq, e.proto())
    case False{} False{}:
      die(c, w, rq, e.size())
    case False{} True{}:
      h.rst.vd(c, w, rq, sid, verdict(state(c, sid), TRst{}))

# SETTINGS (6.5)
# --------------

# what the settings a frame carries do, entry by entry (6.5.2): the
# encoder's table follows SETTINGS_HEADER_TABLE_SIZE (a size update is
# owed); ENABLE_PUSH past 1 is a PROTOCOL_ERROR; INITIAL_WINDOW_SIZE past
# 2^31-1 is a FLOW_CONTROL_ERROR, and moves every stream's window by the
# change (6.9.2), one pushed past 2^31-1 a FLOW_CONTROL_ERROR too;
# MAX_FRAME_SIZE outside 2^14 to 2^24-1 is a PROTOCOL_ERROR; the rest are
# taken or ignored.
type Sets is Data:
  SetOk{he: K.Tbl, hup: Bool, sts: Tb, init: Nat, fmax: Nat}
  SetErr{code: U32}

def set.table(s: Sets, +v: Nat) -> Sets:
  match s:
    case SetOk{he, hup, sts, init, fmax}:
      SetOk{K.tbl.resize(he, Nat.min(v, 4096n)), True{}, sts, init, fmax}
    case SetErr{code}:
      SetErr{code}

def set.push(s: Sets, ok: Bool) -> Sets:
  match ok:
    case True{}:
      s
    case False{}:
      SetErr{e.proto()}

def set.fmax(ok: Bool, s: Sets, +v: Nat) -> Sets:
  match ok s:
    case False{} _:
      SetErr{e.proto()}
    case True{} SetOk{he, hup, sts, init, fmax}:
      SetOk{he, hup, sts, init, v}
    case True{} SetErr{code}:
      SetErr{code}

# every stream's window moved by the change: up by d, or down by it
def sts.move.one(s: St, m: Maybe<&2, Sw>, rest: Maybe<&2, List<&2, St>>) -> Maybe<&2, List<&2, St>>:
  match m rest:
    case Some{w2} Some{r}:
      Some{Con{st.w.sw(s, w2), r}}
    case _ _:
      None{}

def sw.move(w: Sw, up: Bool, +d: Nat) -> Maybe<&2, Sw>:
  match up:
    case True{}:
      sw.add(w, d)
    case False{}:
      Some{sw.less(w, d)}

def sts.move(sts: List<&2, St>, +up: Bool, +d: Nat) -> Maybe<&2, List<&2, St>>:
  match sts:
    case Nil{}:
      Some{Nil{}}
    case Con{+s, t}:
      sts.move.one(s, sw.move(st.sw(s), up, d), sts.move(t, up, d))

def tr.move.b(m: Maybe<&2, List<&2, St>>) -> Maybe<&2, Tr>:
  match m:
    case None{}:
      None{}
    case Some{b}:
      Some{TLeaf{b}}

def tr.move.n(ml: Maybe<&2, Tr>, mh: Maybe<&2, Tr>) -> Maybe<&2, Tr>:
  match ml mh:
    case Some{l} Some{h}:
      Some{TNode{l, h}}
    case _ _:
      None{}

def tr.move(t: Tr, +up: Bool, +d: Nat) -> Maybe<&2, Tr>:
  match t:
    case TNone{}:
      Some{TNone{}}
    case TLeaf{b}:
      tr.move.b(sts.move(b, up, d))
    case TNode{l, h}:
      tr.move.n(tr.move(l, up, d), tr.move(h, up, d))

def tb.move.of(+n: Nat, m: Maybe<&2, Tr>) -> Maybe<&2, Tb>:
  match m:
    case None{}:
      None{}
    case Some{t}:
      Some{Tb{n, t}}

def tb.move(sts: Tb, +up: Bool, +d: Nat) -> Maybe<&2, Tb>:
  match sts:
    case Tb{n, t}:
      tb.move.of(n, tr.move(t, up, d))

def set.init.go(he: K.Tbl, hup: Bool, +v: Nat, fmax: Nat, m: Maybe<&2, Tb>) -> Sets:
  match m:
    case None{}:
      SetErr{e.flow()}
    case Some{sts}:
      SetOk{he, hup, sts, v, fmax}

def set.init(ok: Bool, s: Sets, +v: Nat) -> Sets:
  match ok s:
    case False{} _:
      SetErr{e.flow()}
    case True{} SetOk{he, hup, sts, +init, fmax}:
      +up = Nat.is_le(init, v)
      set.init.go(he, hup, v, fmax, tb.move(sts, up, on(up, Nat.sub(v, init), Nat.sub(init, v))))
    case True{} SetErr{code}:
      SetErr{code}

def set.pick(s: Sets, +n: Nat, push: Bool, init: Bool, fmax: Bool) -> Sets:
  match push init fmax:
    case True{} _ _:
      set.push(s, Nat.is_le(n, 1n))
    case False{} True{} _:
      set.init(Nat.is_le(n, win.max()), s, n)
    case False{} False{} True{}:
      set.fmax(Nat.is_le(16384n, n) && Nat.is_le(n, 16777215n), s, n)
    case False{} False{} False{}:
      s

def set.two(s: Sets, +id: U32, +n: Nat) -> Sets:
  set.pick(s, n, U32.is_eq(id, 2), U32.is_eq(id, 4), U32.is_eq(id, 5))

def set.one.go(s: Sets, +id: U32, +n: Nat, one: Bool) -> Sets:
  match one:
    case True{}:
      set.table(s, n)
    case False{}:
      set.two(s, id, n)

def set.one(s: Sets, +id: U32, +v: U32) -> Sets:
  set.one.go(s, id, U32.to_nat(v), U32.is_eq(id, 1))

def set.all(k: Nat, +pay: Bytes(), +i: Nat, s: Sets) -> Sets:
  match k:
    case 0n:
      s
    case 1n+j:
      set.all(j, pay, Nat.add(i, 6n), set.one(s, be16(pay, i), be32(pay, 2n+i)))

def set.done(+c: Cn, w: Bytes(), rq: List<&2, Req>, s: Sets) -> Out:
  match s:
    case SetErr{code}:
      die(c, w, rq, code)
    case SetOk{he, hup, sts, init, fmax}:
      ok(cn.w.fmax(cn.w.init(cn.w.sts(cn.w.hup(cn.w.he(c, he), hup), sts), init), fmax),
        Bytes.append(w, f.ack()), rq)

# a SETTINGS acknowledged is paid from the budget (a SETTINGS flood
# meets it)
def set.paid(+c: Cn, w: Bytes(), rq: List<&2, Req>, +pay: Bytes(), b: Bud) -> Out:
  match b:
    case Bud{p, s, r}:
      match s:
        case 0n:
          die(c, w, rq, e.calm())
        case 1n+k:
          set.done(cn.w.bud(c, Bud{p, k, r}), w, rq,
            set.all(Nat.div(Bytes.len(pay), 6n), pay, 0n,
              SetOk{cn.he(c), cn.hup(c), cn.sts(c), cn.init(c), cn.fmax(c)}))

def set.acked(+c: Cn, w: Bytes(), rq: List<&2, Req>, empty: Bool) -> Out:
  match empty:
    case True{}:
      ok(c, w, rq)
    case False{}:
      die(c, w, rq, e.size())

def set.sixes(+c: Cn, w: Bytes(), rq: List<&2, Req>, +pay: Bytes(), fine: Bool) -> Out:
  match fine:
    case True{}:
      set.paid(c, w, rq, pay, cn.bud(c))
    case False{}:
      die(c, w, rq, e.size())

def set.ack(+c: Cn, w: Bytes(), rq: List<&2, Req>, +pay: Bytes(), ack: Bool, +len: Nat) -> Out:
  match ack:
    case True{}:
      set.acked(c, w, rq, Nat.is_eq(len, 0n))
    case False{}:
      set.sixes(c, w, rq, pay, Nat.is_eq(Nat.mod(len, 6n), 0n))

# on stream 0 only; an ACK carries nothing; otherwise six bytes an entry
def h.settings(+c: Cn, w: Bytes(), rq: List<&2, Req>, +fl: U32, +pay: Bytes(), z: Bool) -> Out:
  match z:
    case False{}:
      die(c, w, rq, e.proto())
    case True{}:
      set.ack(c, w, rq, pay, flag(fl, 1), Bytes.len(pay))

# PING (6.7): on stream 0, eight bytes; answered with the same eight
# bytes and ACK, each answer paid from the budget (a PING flood meets
# it); an ACK is not answered
def ping.paid(+c: Cn, w: Bytes(), rq: List<&2, Req>, +pay: Bytes(), b: Bud) -> Out:
  match b:
    case Bud{p, s, r}:
      match p:
        case 0n:
          die(c, w, rq, e.calm())
        case 1n+k:
          ok(cn.w.bud(c, Bud{k, s, r}), Bytes.append(w, f.pong(pay)), rq)

def ping.ack(+c: Cn, w: Bytes(), rq: List<&2, Req>, +pay: Bytes(), ack: Bool) -> Out:
  match ack:
    case True{}:
      ok(c, w, rq)
    case False{}:
      ping.paid(c, w, rq, pay, cn.bud(c))

def h.ping(+c: Cn, w: Bytes(), rq: List<&2, Req>, +fl: U32, +pay: Bytes(), z: Bool, eight: Bool) -> Out:
  match z eight:
    case False{} _:
      die(c, w, rq, e.proto())
    case True{} False{}:
      die(c, w, rq, e.size())
    case True{} True{}:
      ping.ack(c, w, rq, pay, flag(fl, 1))

# GOAWAY (6.8): on stream 0. The peer opens no more streams; the ones
# it has are still answered, and the peer closes when it is done.
def h.goaway(+c: Cn, w: Bytes(), rq: List<&2, Req>, z: Bool) -> Out:
  match z:
    case False{}:
      die(c, w, rq, e.proto())
    case True{}:
      ok(c, w, rq)

# WINDOW_UPDATE (6.9): four bytes; an increment of 0 is a
# PROTOCOL_ERROR, one that takes a window past 2^31-1 a
# FLOW_CONTROL_ERROR -- of the connection on stream 0, of the stream
# otherwise
def win.conn(+c: Cn, w: Bytes(), rq: List<&2, Req>, m: Maybe<&2, Sw>) -> Out:
  match m:
    case None{}:
      die(c, w, rq, e.flow())
    case Some{sw}:
      ok(cn.w.csw(c, sw), w, rq)

def win.st.add(c: Cn, w: Bytes(), rq: List<&2, Req>, s: St, m: Maybe<&2, Sw>) -> Out:
  match m:
    case None{}:
      rst(c, w, rq, st.id(s), e.flow())
    case Some{sw}:
      ok(cn.ins(c, st.w.sw(s, sw)), w, rq)

def win.st(inc: Nat, ct: Ct, w: Bytes(), rq: List<&2, Req>, +sid: U32) -> Out:
  match inc ct:
    case _ Ct{None{}, c}:
      ok(c, w, rq)
    case 0n Ct{Some{s}, c}:
      rst(c, w, rq, sid, e.proto())
    case 1n+i Ct{Some{+s}, c}:
      win.st.add(c, w, rq, s, sw.add(st.sw(s), 1n+i))

def win.vd(+c: Cn, w: Bytes(), rq: List<&2, Req>, +sid: U32, +inc: Nat, v: Vd) -> Out:
  match v:
    case VConn{code}:
      die(c, w, rq, code)
    case VStream{code}:
      rst(c, w, rq, sid, code)
    case VOk{}:
      win.st(inc, cn.take(c, sid), w, rq, sid)

def win.zero(+c: Cn, w: Bytes(), rq: List<&2, Req>, +inc: Nat) -> Out:
  match inc:
    case 0n:
      die(c, w, rq, e.proto())
    case 1n+i:
      win.conn(c, w, rq, sw.add(cn.csw(c), 1n+i))

def h.win(+c: Cn, w: Bytes(), rq: List<&2, Req>, +sid: U32, +pay: Bytes(), four: Bool, z: Bool) -> Out:
  match four z:
    case False{} _:
      die(c, w, rq, e.size())
    case True{} True{}:
      win.zero(c, w, rq, U32.to_nat(u31(be32(pay, 0n))))
    case True{} False{}:
      win.vd(c, w, rq, sid, U32.to_nat(u31(be32(pay, 0n))), verdict(state(c, sid), TWin{}))

# One frame
# =========

def step.ty(+root: H.Ht, +c: Cn, w: Bytes(), rq: List<&2, Req>, +z: Bool, +len: Nat, t: Ty, +fl: U32, +sid: U32,
  +pay: Bytes()) -> Out:
  match t:
    case TData{}:
      h.data(c, w, rq, fl, sid, pay)
    case THeaders{}:
      h.headers(root, c, w, rq, fl, sid, pay)
    case TPrio{}:
      h.prio(c, w, rq, sid, pay, z, Nat.is_eq(len, 5n))
    case TRst{}:
      h.rst(c, w, rq, sid, z, Nat.is_eq(len, 4n))
    case TSettings{}:
      h.settings(c, w, rq, fl, pay, z)
    case TPush{}:
      die(c, w, rq, e.proto())
    case TPing{}:
      h.ping(c, w, rq, fl, pay, z, Nat.is_eq(len, 8n))
    case TGoaway{}:
      h.goaway(c, w, rq, z)
    case TWin{}:
      h.win(c, w, rq, sid, pay, Nat.is_eq(len, 4n), z)
    case TCont{}:
      die(c, w, rq, e.proto())
    case TOther{}:
      ok(c, w, rq)

# inside a header block only its CONTINUATION may come (6.10, 5.5)
def step.blk(+root: H.Ht, +c: Cn, w: Bytes(), rq: List<&2, Req>, b: Blk, f: Fm.Frm) -> Out:
  match b f:
    case BNone{} Fm.Frm{ty, fl, +sid, +pay}:
      step.ty(root, c, w, rq, U32.is_zero(sid), Bytes.len(pay), ty.of(ty), fl, sid, pay)
    case BIn{+bsid, end, k, size} Fm.Frm{+ty, fl, +sid, pay}:
      h.cont(root, c, w, rq, fl, pay, BIn{bsid, end, k, size}, U32.is_eq(ty, 9) && U32.is_eq(sid, bsid))

def step(+root: H.Ht, o: Out, f: Fm.Frm) -> Out:
  match o:
    case Out{+c, w, rq, dead}:
      match dead:
        case True{}:
          Out{c, w, rq, True{}}
        case False{}:
          step.blk(root, c, w, rq, cn.blk(c), f)

def steps(+root: H.Ht, fs: List<&2, Fm.Frm>, o: Out) -> Out:
  match fs:
    case Nil{}:
      o
    case Con{f, t}:
      steps(root, t, step(root, o, f))

# A read
# ======

# the stream refused whole: a wrong preface is a PROTOCOL_ERROR, a frame
# past SETTINGS_MAX_FRAME_SIZE a FRAME_SIZE_ERROR (4.2)
def refusal(+c: Cn, w: Bytes(), rq: List<&2, Req>, dead: Bool, m: Maybe<&2, Fm.Why>) -> Out:
  match dead m:
    case True{} _:
      Out{c, w, rq, True{}}
    case False{} None{}:
      Out{c, w, rq, False{}}
    case False{} Some{Fm.WPre{}}:
      die(c, w, rq, e.proto())
    case False{} Some{Fm.WSize{}}:
      die(c, w, rq, e.size())

def read.end(o: Out, m: Maybe<&2, Fm.Why>) -> Out:
  match o:
    case Out{c, w, rq, dead}:
      refusal(c, w, rq, dead, m)

def hello.pre(rd: Fm.Rd) -> Bool & Bytes():
  match rd:
    case Fm.Rd{at, max, out}:
      match at:
        case Fm.FPre{ps}:
          (False{}, "")
        case Fm.FBad{why}:
          (False{}, "")
        case _:
          (True{}, f.settings())

# our SETTINGS go first, once the peer's preface is in
def hello(+said: Bool, +rd: Fm.Rd) -> Bool & Bytes():
  match said:
    case True{}:
      (True{}, "")
    case False{}:
      hello.pre(rd)

# the reader goes back into the connection before the frames are
# stepped (they never touch it), with whether it refused
def read.hi(+root: H.Ht, +rd: Fm.Rd, hd: K.Dec, he: K.Tbl, hup: Bool, sts: Tb, gone: Ids,
  last: U32, blk: Blk, csw: Sw, crw: Nat, init: Nat, fmax: Nat, bud: Bud, fs: List<&2, Fm.Frm>,
  h: Bool & Bytes()) -> Out:
  match h:
    case (said, hi):
      +m = Fm.refused(rd)
      read.end(steps(root, fs, Out{Cn{rd, hd, he, hup, sts, gone, last, blk, csw, crw, init, fmax, bud, said}, hi,
        Nil{}, False{}}), m)

def read.go(+root: H.Ht, hd: K.Dec, he: K.Tbl, hup: Bool, sts: Tb, gone: Ids, last: U32,
  blk: Blk, csw: Sw, crw: Nat, init: Nat, fmax: Nat, bud: Bud, +said: Bool, fsr: Fm.Rd & List<&2, Fm.Frm>) -> Out:
  match fsr:
    case (+rd, fs):
      read.hi(root, rd, hd, he, hup, sts, gone, last, blk, csw, crw, init, fmax, bud, fs, hello(said, rd))

# one read's bytes: framed, each frame stepped in turn
def read(+root: H.Ht, c: Cn, buf: Bytes()) -> Out:
  match c:
    case Cn{rd, hd, he, hup, sts, gone, last, blk, csw, crw, init, fmax, bud, said}:
      read.go(root, hd, he, hup, sts, gone, last, blk, csw, crw, init, fmax, bud, said,
        Fm.take(Fm.feed_buf(buf, rd)))

# Answering
# =========

# the connection and what it has to write
type CW is Data:
  CW{c: Cn, w: Bytes()}

# Sending what waits (6.9): a stream's body in DATA frames, each at
# most the peer's SETTINGS_MAX_FRAME_SIZE and within both windows,
# END_STREAM on the last; a stream whose body is all out is done.
def avail(+s: St, +csw: Sw, +fmax: Nat) -> Nat:
  Nat.min(Bytes.len(st.out(s)), Nat.min(sw.up(st.sw(s)), Nat.min(sw.up(csw), fmax)))

# a stream's turn as it goes: what may go next (avail), the stream,
# the connection's window, what is written
type Pn is Data:
  Pn{n: Nat, s: St, csw: Sw, w: Bytes()}

# n bytes of a body go in one DATA frame: all that is left (with
# END_STREAM when the response ends there), or a part
def pump.cut(+fmax: Nat, +n: Nat, +csw: Sw, w: Bytes(), +id: U32, ss: Ss, meth: Bytes(), path: Bytes(),
  cl: Maybe<&2, Nat>, body: Bytes(), got: Nat, rw: Nat, +sw: Sw, +fin: Bool, whole: Bool, +out: Bytes()) -> Pn:
  match whole:
    case True{}:
      +csw2 = sw.take(csw, n)
      +s2 = {St{id, ss, meth, path, cl, body, got, rw, sw.take(sw, n), "", fin} : St}
      Pn{avail(s2, csw2, fmax), s2, csw2, Bytes.append(w, f.data(id, fin, out))}
    case False{}:
      +csw2 = sw.take(csw, n)
      +s2 = {St{id, ss, meth, path, cl, body, got, rw, sw.take(sw, n), Bytes.drop(out, n), fin} : St}
      Pn{avail(s2, csw2, fmax), s2, csw2, Bytes.append(w, f.data(id, False{}, Bytes.slice(out, 0n, n)))}

def pump.step(+fmax: Nat, +n: Nat, +csw: Sw, w: Bytes(), s: St) -> Pn:
  match s:
    case St{id, ss, meth, path, cl, body, got, rw, sw, +out, fin}:
      pump.cut(fmax, n, csw, w, id, ss, meth, path, cl, body, got, rw, sw, fin, Nat.is_eq(n, Bytes.len(out)), out)

# the frames go while the windows let them (k bounds the turns: each
# sends a byte or more)
def pump.st(k: Nat, +fmax: Nat, q: Pn) -> Pn:
  match k:
    case 0n:
      q
    case 1n+j:
      match q:
        case Pn{n, s, csw, w}:
          match n:
            case 0n:
              Pn{0n, s, csw, w}
            case 1n+m:
              pump.st(j, fmax, pump.step(fmax, 1n+m, csw, w, s))

def pump.go(+fmax: Nat, +s: St, +csw: Sw, w: Bytes()) -> Pn:
  pump.st(1n+Bytes.len(st.out(s)), fmax, Pn{avail(s, csw, fmax), s, csw, w})

# A stream after its turn: done when its body is all out and END_STREAM
# went with it (the budgets given back one of each); else it waits in
# the table for the windows.
def st.done(+s: St) -> Bool:
  String.is_empty(st.out(s)) && st.fin(s)

def bud.on(b: Bool, x: Bud) -> Bud:
  match b:
    case True{}:
      bud.refill(x)
    case False{}:
      x

def cn.refill(c: Cn) -> Cn:
  match c:
    case Cn{rd, hd, he, hup, sts, gone, last, blk, csw, crw, init, fmax, bud, said}:
      Cn{rd, hd, he, hup, sts, gone, last, blk, csw, crw, init, fmax, bud.refill(bud), said}

def pump.done(c: Cn, w: Bytes(), s: St, done: Bool) -> CW:
  match done:
    case True{}:
      CW{c, w}
    case False{}:
      CW{cn.ins(c, s), w}

def pump.one.fin(rd: Fm.Rd, hd: K.Dec, he: K.Tbl, hup: Bool, sts: Tb, gone: Ids, last: U32,
  blk: Blk, crw: Nat, init: Nat, fmax: Nat, bud: Bud, said: Bool, p: Pn) -> CW:
  match p:
    case Pn{n, +s, csw, w}:
      +done = st.done(s)
      pump.done(Cn{rd, hd, he, hup, sts, gone, last, blk, csw, crw, init, fmax, bud.on(done, bud), said}, w, s, done)

# a stream's body sent as far as the windows let it
def pump.one(c: Cn, w: Bytes(), +s: St) -> CW:
  match c:
    case Cn{rd, hd, he, hup, sts, gone, last, blk, +csw, crw, init, +fmax, bud, said}:
      pump.one.fin(rd, hd, he, hup, sts, gone, last, blk, crw, init, fmax, bud, said, pump.go(fmax, s, csw, w))

# A response to a request: its status, type and body. Its head goes out
# at once as one HEADERS frame (a size update first when the peer's
# SETTINGS_HEADER_TABLE_SIZE moved the encoder's table), and its body
# after it, as far as the windows let it.
def resp.fields(+status: Bytes(), +ct: Bytes(), +n: Nat) -> List<&2, K.Fld>:
  [K.Fld{":status", status}, K.Fld{"content-type", ct}, K.Fld{"content-length", Nat.show(n)}]

def resp.block(hup: Bool, +max: Nat, blk: List<&2, U32>) -> Bytes():
  match hup:
    case True{}:
      Bytes.from_list(List.append(&2, U32, K.int.enc(K.P5{}, 32n, max), blk))
    case False{}:
      Bytes.from_list(blk)

def resp.put(c: Cn, w: Bytes(), s: St, body: Bytes(), empty: Bool) -> CW:
  match empty:
    case True{}:
      CW{cn.refill(c), w}
    case False{}:
      pump.one(c, w, st.w.fin(st.w.out(s, body), True{}))

def resp.enc(rd: Fm.Rd, hd: K.Dec, +hup: Bool, sts: Tb, gone: Ids, last: U32, blk: Blk, csw: Sw,
  crw: Nat, init: Nat, fmax: Nat, bud: Bud, said: Bool, w: Bytes(), +s: St, body: Bytes(), +empty: Bool,
  e: K.Enc) -> CW:
  match e:
    case K.Enc{+he, hb}:
      resp.put(Cn{rd, hd, he, False{}, sts, gone, last, blk, csw, crw, init, fmax, bud, said},
        Bytes.append(w, f.headers(st.id(s), empty, resp.block(hup, K.tbl.max(he), hb))), s, body, empty)

def answer.enc(c: Cn, w: Bytes(), +s: St, +status: Bytes(), +ct: Bytes(), +body: Bytes(), +empty: Bool) -> CW:
  match c:
    case Cn{rd, hd, he, hup, sts, gone, last, blk, csw, crw, init, fmax, bud, said}:
      resp.enc(rd, hd, hup, sts, gone, last, blk, csw, crw, init, fmax, bud, said, w, s, body, empty,
        K.encode(he, resp.fields(status, ct, Bytes.len(body)), True{}))

def answer.st(ct: Ct, w: Bytes(), +status: Bytes(), +ctype: Bytes(), +body: Bytes(), +head: Bool) -> CW:
  match ct:
    case Ct{None{}, c}:
      CW{c, w}
    case Ct{Some{s}, c}:
      answer.enc(c, w, s, status, ctype, body, head || String.is_empty(body))

# the answer to the request on stream sid (a HEAD's without its body)
def answer(c: Cn, w: Bytes(), +sid: U32, status: Bytes(), ct: Bytes(), body: Bytes(), head: Bool) -> CW:
  answer.st(cn.take(c, sid), w, status, ct, body, head)

# What waits on the windows goes when they open: every stream in the
# table pumped in turn; those done leave it, each giving the budgets
# back one of each.
type Pp is Data:
  Pp{csw: Sw, w: Bytes(), sts: Tb, n: Nat}

def pump.keep.go(csw: Sw, w: Bytes(), s: St, sts: Tb, +n: Nat, done: Bool) -> Pp:
  match done:
    case True{}:
      Pp{csw, w, sts, 1n+n}
    case False{}:
      Pp{csw, w, st.ins(sts, s), n}

def pump.keep(sts: Tb, +n: Nat, p: Pn) -> Pp:
  match p:
    case Pn{k, +s, csw, w}:
      pump.keep.go(csw, w, s, sts, n, st.done(s))

def pump.b(xs: List<&2, St>, +fmax: Nat, p: Pp) -> Pp:
  match xs:
    case Nil{}:
      p
    case Con{+s, t}:
      match p:
        case Pp{+csw, w, sts, n}:
          pump.b(t, fmax, pump.keep(sts, n, pump.go(fmax, s, csw, w)))

def pump.all(t: Tr, +fmax: Nat, p: Pp) -> Pp:
  match t:
    case TNone{}:
      p
    case TLeaf{b}:
      pump.b(b, fmax, p)
    case TNode{l, h}:
      pump.all(h, fmax, pump.all(l, fmax, p))

def pump.tb(sts: Tb, +fmax: Nat, p: Pp) -> Pp:
  match sts:
    case Tb{n, t}:
      pump.all(t, fmax, p)

def bud.times(k: Nat, b: Bud) -> Bud:
  match k:
    case 0n:
      b
    case 1n+j:
      bud.times(j, bud.refill(b))

def pump.fin(rd: Fm.Rd, hd: K.Dec, he: K.Tbl, hup: Bool, gone: Ids, last: U32, blk: Blk, crw: Nat,
  init: Nat, fmax: Nat, bud: Bud, said: Bool, p: Pp) -> CW:
  match p:
    case Pp{csw, w, sts, n}:
      CW{Cn{rd, hd, he, hup, sts, gone, last, blk, csw, crw, init, fmax, bud.times(n, bud), said}, w}

def flush(c: Cn, w: Bytes()) -> CW:
  match c:
    case Cn{rd, hd, he, hup, sts, gone, last, blk, csw, crw, init, +fmax, bud, said}:
      pump.fin(rd, hd, he, hup, gone, last, blk, crw, init, fmax, bud, said,
        pump.tb(sts, fmax, Pp{csw, w, st.empty(), 0n}))
