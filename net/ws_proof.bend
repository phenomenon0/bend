# The proofs of net/ws_laws.bend. `bend net/ws_proof.bend` prints "All
# terms check." when every law holds.
import Base
import ../wire/reader.bend as Wr
import ../demos/io_http_engine/ws.bend as Ws
import ./ws_frame.bend as F
import ./ws_hs.bend as H
import ./ws_laws.bend as Laws

# The reader, at either end
# =========================

# at Srv each state steps to what the engine's reader steps it to: the
# role only picks the engine's own step
def Laws.role_srv_step(w, b):
  match w:
    case Ws.W{st, out}:
      match st:
        case Ws.Op{}:
          {==}
        case Ws.Len{op}:
          {==}
        case Ws.Ext{op, need, len, min}:
          {==}
        case Ws.Msk{op, len, need, m}:
          {==}
        case Ws.Pay{op, rem, m, acc}:
          {==}
        case Ws.Bad{}:
          {==}

# so a walk at Srv is the engine's walk, byte by byte
def Laws.role_srv(bs, w):
  match bs:
    case Nil{}:
      {==}
    case Con{c, t}:
      %Laws.role_srv_step(w, c) : {F.feed(F.Srv{}, t, F.step(F.Srv{}, w, c)) == Ws.feed(t, _) : Ws.W}
      Laws.role_srv(t, F.step(F.Srv{}, w, c))

# and on a buffer: each side is its list walk (the kit's slow_is_feed)
def Laws.role_srv_buf(b, w):
  Equal.trans(Ws.W, F.feed_buf(F.Srv{}, b, w), F.feed(F.Srv{}, Bytes.to_list(b), w), Ws.feed_buf(b, w),
    Wr.slow_is_feed(~F.Role, ~Ws.W, ~F.step, F.Srv{}, b, w),
    Equal.trans(Ws.W, F.feed(F.Srv{}, Bytes.to_list(b), w), Ws.feed(Bytes.to_list(b), w), Ws.feed_buf(b, w),
      Laws.role_srv(Bytes.to_list(b), w),
      Equal.sym(Ws.W, Ws.feed_buf(b, w), Ws.feed(Bytes.to_list(b), w),
        Wr.slow_is_feed(~Unit, ~Ws.W, ~Ws.wstep, Unit{}, b, w))))

def Laws.feed_split(r, a, b, w):
  Wr.feed_split(~F.Role, ~Ws.W, ~F.step, r, a, b, w)

def Laws.feed_buf(r, b, w):
  Wr.slow_is_feed(~F.Role, ~Ws.W, ~F.step, r, b, w)

def Laws.feed_buf_split(r, a, b, w):
  Wr.slow_split(~F.Role, ~Ws.W, ~F.step, r, a, b, w)

def bad(out: List<&2, Ws.Frm>) -> Ws.W:
  Ws.W{Ws.Bad{}, out}

def absorbs(+r: F.Role, +out: List<&2, Ws.Frm>, +c: U32) -> {F.step(r, bad(out), c) == bad(out) : Ws.W}:
  {==}

def Laws.bad_feeds_buf(r, s, out):
  Wr.bad_feeds_slow(~F.Role, ~Ws.W, ~F.step, ~List<&2, Ws.Frm>, ~bad, ~absorbs, r, s, out)

# The client's refusals
# =====================

def Laws.masked_refused(cap, op, out, b, h):
  %Equal.sym(U32, U32.and(b, 128), 128, h) :
    {F.c.len.go(cap, op, U32.and(b, 127), U32.is_eq(_, 128),
      F.c.ctl(op) && U32.is_lt(125, U32.and(b, 127)), out) == Ws.W{Ws.Bad{}, out} : Ws.W}
  {==}

def len.long(+cap: U32, +op: U32, +n: U32, masked: Bool, +out: List<&2, Ws.Frm>) ->
  {F.c.len.go(cap, op, n, masked, True{}, out) == Ws.W{Ws.Bad{}, out} : Ws.W}:
  match masked:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.control_long_refused(cap, op, out, b, h):
  %Equal.sym(Bool, F.c.ctl(op) && U32.is_lt(125, U32.and(b, 127)), True{}, h) :
    {F.c.len.go(cap, op, U32.and(b, 127), U32.is_eq(U32.and(b, 128), 128), _, out) ==
    Ws.W{Ws.Bad{}, out} : Ws.W}
  len.long(cap, op, U32.and(b, 127), U32.is_eq(U32.and(b, 128), 128), out)

def Laws.reserved_refused(cap, out, b, h):
  %Equal.sym(Bool, U32.is_zero(U32.and(b, 112)), False{}, h) :
    {Ws.W{F.c.op.go(U32.and(b, 15), _ && F.c.known(U32.and(b, 15)), U32.is_eq(U32.and(b, 128), 128)), out} ==
    Ws.W{Ws.Bad{}, out} : Ws.W}
  {==}

def Laws.text_bad_1007(cap, body, h):
  %Equal.sym(Bool, Ws.utf8(body), False{}, h) : {F.Ax{F.Idle{}, F.whole.text(body, _)} == F.Ax{F.Idle{}, F.Refuse{1007}} : F.Ax}
  {==}

def Laws.orphan_continuation(cap, fin, body):
  match fin:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.interleaved_message(cap, fop, acc, n, ut, bin, body):
  match bin:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.too_big_1009(cap, a):
  {==}

def Laws.ping_pong(cap, a, body):
  {==}

# Masking
# =======

def bxor_inv(a: Bool, b: Bool) -> {Bool.xor(Bool.xor(a, b), b) == a : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def wxor_inv(n: Nat, a: Word(n), k: Word(n)) -> {Word.xor(n, Word.xor(n, a, k), k) == a : Word(n)}:
  match n:
    case 0n:
      match a k:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a k:
        case WCon{ab, at} WCon{kb, kt}:
          %Equal.sym(Bool, Bool.xor(Bool.xor(ab, kb), kb), ab, bxor_inv(ab, kb)) : {WCon{_, Word.xor(p, Word.xor(p, at, kt), kt)} == WCon{ab, at} : Word(1n+p)}
          %Equal.sym(Word(p), Word.xor(p, Word.xor(p, at, kt), kt), at, wxor_inv(p, at, kt)) : {WCon{ab, _} == WCon{ab, at} : Word(1n+p)}
          {==}

def xor_inv(a: U32, k: U32) -> {U32.xor(U32.xor(a, k), k) == a : U32}:
  match a k:
    case U32{x} U32{y}:
      Equal.cong(Word(32n), U32, w => U32{w}, Word.xor(32n, Word.xor(32n, x, y), y), x, wxor_inv(32n, x, y))

def Laws.mask_inv(p, m):
  match p:
    case SNil{}:
      {==}
    case SCon{Chr{c}, t}:
      %Equal.sym(U32, U32.xor(U32.xor(c, Ws.key.of(m)), Ws.key.of(m)), c, xor_inv(c, Ws.key.of(m))) : {SCon{Chr{_}, F.mask(F.mask(t, Ws.rot(m)), Ws.rot(m))} == SCon{Chr{c}, t} : Bytes()}
      %Equal.sym(Bytes(), F.mask(F.mask(t, Ws.rot(m)), Ws.rot(m)), t, Laws.mask_inv(t, Ws.rot(m))) : {SCon{Chr{c}, _} == SCon{Chr{c}, t} : Bytes()}
      {==}

def band_or(a: Bool, x: Bool) -> {Bool.and(Bool.or(a, x), a) == a : Bool}:
  match a x:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def wand_or(n: Nat, a: Word(n), x: Word(n)) -> {Word.and(n, Word.or(n, a, x), a) == a : Word(n)}:
  match n:
    case 0n:
      match a x:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a x:
        case WCon{ab, at} WCon{xb, xt}:
          %Equal.sym(Bool, Bool.and(Bool.or(ab, xb), ab), ab, band_or(ab, xb)) : {WCon{_, Word.and(p, Word.or(p, at, xt), at)} == WCon{ab, at} : Word(1n+p)}
          %Equal.sym(Word(p), Word.and(p, Word.or(p, at, xt), at), at, wand_or(p, at, xt)) : {WCon{ab, _} == WCon{ab, at} : Word(1n+p)}
          {==}

# a bit set by an or is set after it
def and_or(a: U32, x: U32) -> {U32.and(U32.or(a, x), a) == a : U32}:
  match a x:
    case U32{y} U32{z}:
      Equal.cong(Word(32n), U32, w => U32{w}, Word.and(32n, Word.or(32n, y, z), y), y, wand_or(32n, y, z))

def Laws.frame_masked(op, fin, p, m):
  and_or(128, F.len7(U32.from_nat(Bytes.len(p))))

def Laws.frame_payload(op, fin, p, m):
  {==}

def Laws.frame_rfc():
  {==}

def Laws.engine_reads_client():
  {==}

# The session
# ===========

def Laws.session_rfc():
  {==}

def Laws.session_masked():
  {==}

def Laws.session_interleaved():
  {==}

def Laws.session_refusals():
  {==}

def Laws.session_close():
  {==}

def Laws.utf8_vectors():
  {==}

# The handshake
# =============

# a single Accept decides the verdict, and nothing after it can refuse
# an answer that names no extension and no subprotocol
def acc1_ok(offered: List<&2, String>, same: Bool) -> {H.ok(H.j.acc1(offered, [], False{}, same)) == same : Bool}:
  match same:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.hs_accept(key, a, offered):
  acc1_ok(offered, String.eq(a, H.expect(key)))

def Laws.hs_rfc():
  {==}

def Laws.hs_request():
  {==}

def Laws.url_vectors():
  {==}
