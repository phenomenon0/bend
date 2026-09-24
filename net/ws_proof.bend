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

def Laws.url_v6_vectors():
  {==}

def Laws.hs_request_v6():
  {==}

# The server's end
# ================

def Laws.srv_unmasked_refused(cap, op, out, b, h):
  %Equal.sym(U32, U32.and(b, 128), 0, h) :
    {F.s.len.go(cap, op, U32.and(b, 127), U32.is_eq(_, 128),
      F.c.ctl(op) && U32.is_lt(125, U32.and(b, 127)), out) == Ws.W{Ws.Bad{}, out} : Ws.W}
  {==}

# the words under U32's literals
def wd(x: U32) -> Word(32n):
  match x:
    case U32{w}:
      w

# the word of n bits, every one clear
def wz(n: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      WCon{False{}, wz(p)}

def band_assoc(a: Bool, b: Bool, c: Bool) -> {Bool.and(Bool.and(a, b), c) == Bool.and(a, Bool.and(b, c)) : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def wand_assoc(n: Nat, a: Word(n), b: Word(n), c: Word(n)) ->
  {Word.and(n, Word.and(n, a, b), c) == Word.and(n, a, Word.and(n, b, c)) : Word(n)}:
  match n:
    case 0n:
      match a b c:
        case WNil{} WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b c:
        case WCon{ab, at} WCon{bb, bt} WCon{cb, ct}:
          %band_assoc(ab, bb, cb) : {WCon{Bool.and(Bool.and(ab, bb), cb), Word.and(p, Word.and(p, at, bt), ct)} ==
            WCon{_, Word.and(p, at, Word.and(p, bt, ct))} : Word(1n+p)}
          %wand_assoc(p, at, bt, ct) : {WCon{Bool.and(Bool.and(ab, bb), cb), Word.and(p, Word.and(p, at, bt), ct)} ==
            WCon{Bool.and(Bool.and(ab, bb), cb), _} : Word(1n+p)}
          {==}

def band_false(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def wand_z(n: Nat, a: Word(n)) -> {Word.and(n, a, wz(n)) == wz(n) : Word(n)}:
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+p:
      match a:
        case WCon{ab, at}:
          %band_false(ab) : {WCon{Bool.and(ab, False{}), Word.and(p, at, wz(p))} == WCon{_, wz(p)} : Word(1n+p)}
          %wand_z(p, at) : {WCon{Bool.and(ab, False{}), Word.and(p, at, wz(p))} == WCon{Bool.and(ab, False{}), _} : Word(1n+p)}
          {==}

# a byte's low seven bits never carry the mask bit
def and_mask(+x: U32) -> {U32.and(U32.and(x, 127), 128) == 0 : U32}:
  match x:
    case U32{+w}:
      Equal.cong(Word(32n), U32, v => U32{v}, Word.and(32n, Word.and(32n, w, wd(127)), wd(128)), wz(32n),
        Equal.trans(Word(32n), Word.and(32n, Word.and(32n, w, wd(127)), wd(128)),
          Word.and(32n, w, Word.and(32n, wd(127), wd(128))), wz(32n),
          wand_assoc(32n, w, wd(127), wd(128)), wand_z(32n, w)))

def Laws.srv_frame_unmasked(op, fin, p):
  and_mask(F.len7(U32.from_nat(Bytes.len(p))))

def Laws.srv_frame_rfc():
  {==}

def Laws.srv_session_rfc():
  {==}

# Closing
# =======

def Laws.srv_close_after(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      match x:
        case F.Deliver{m}:
          Laws.srv_close_after(t)
        case F.Pong{body}:
          Laws.srv_close_after(t)
        case F.Skip{}:
          Laws.srv_close_after(t)
        case F.Bye{code, reason}:
          {==}
        case F.Refuse{code}:
          {==}

def close_once_open(xs: List<&2, F.Act>) -> {Nat.is_le(F.closes(F.s.writes(False{}, xs)), 1n) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      match x:
        case F.Deliver{m}:
          close_once_open(t)
        case F.Pong{body}:
          close_once_open(t)
        case F.Skip{}:
          close_once_open(t)
        case F.Bye{code, reason}:
          {==}
        case F.Refuse{code}:
          {==}

def Laws.srv_close_once(sent, xs):
  match sent:
    case False{}:
      close_once_open(xs)
    case True{}:
      %Equal.sym(Nat, F.closes(F.s.writes(True{}, xs)), 0n, Laws.srv_close_after(xs)) :
        {Nat.is_le(_, 1n) == True{} : Bool}
      {==}

def Laws.srv_close_vector():
  {==}

# The handshake
# =============

def Laws.srv_hs_valid(key, offered, proto, h):
  Equal.cong(Bool, H.Sv, b => H.s.answer.at(key, offered, proto, H.s.check.at(True{}, b)), H.key.ok(key), True{}, h)

def Laws.srv_hs_proto(proto, offered, h):
  Equal.cong(Bool, Bytes(), b => Bool.pick(Bytes(), b && Bool.not(String.is_empty(proto)), proto, ""),
    H.has(offered, proto), False{}, h)

def no_refused(+asked: Bool, +key: Bytes(), +offered: List<&2, Bytes()>, +proto: Bytes()) ->
  {H.s.refused(H.s.answer.at(key, offered, proto, H.s.check.at(asked, False{}))) == True{} : Bool}:
  match asked:
    case False{}:
      {==}
    case True{}:
      {==}

def Laws.srv_hs_version(get, key, offered, proto):
  match get:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.srv_hs_refused(get, asked, key, offered, proto, h):
  Equal.trans(Bool, H.s.refused(H.s.answer(get, asked, key, offered, proto)),
    H.s.refused(H.s.answer.at(key, offered, proto, H.s.check.at(asked, False{}))), True{},
    Equal.cong(Bool, Bool, b => H.s.refused(H.s.answer.at(key, offered, proto, H.s.check.at(asked, b))),
      get && asked && H.key.ok(key), False{}, h),
    no_refused(asked, key, offered, proto))

def Laws.srv_hs_vectors():
  {==}

def Laws.srv_hs_client_reads():
  {==}

def Laws.srv_offered():
  {==}

# Reads
# =====
#
# srv_reads: the reader only ever pushes frames onto its out list, so a
# read fed a reader holding frames lands where it would have holding
# none, with those frames under what it adds (feed_app); the frames the
# connection takes read by read are then the frames of the whole, in
# order (rev_app), and the assembler run over them in pieces is the one
# run over them whole (acts_app).

def wapp(w: Ws.W, e: List<&2, Ws.Frm>) -> Ws.W:
  match w:
    case Ws.W{st, o}:
      Ws.W{st, List.append(&2, Ws.Frm, o, e)}

def fits_app(+op: U32, +n: U32, +big: Bool, +o: List<&2, Ws.Frm>, +e: List<&2, Ws.Frm>) ->
  {F.s.fits(op, n, List.append(&2, Ws.Frm, o, e), big) == wapp(F.s.fits(op, n, o, big), e) : Ws.W}:
  match big:
    case True{}:
      {==}
    case False{}:
      {==}

def len_on_app(+cap: U32, +op: U32, +n: U32, +two: Bool, +eight: Bool, +o: List<&2, Ws.Frm>, +e: List<&2, Ws.Frm>) ->
  {F.s.len.on(cap, op, n, two, eight, List.append(&2, Ws.Frm, o, e)) == wapp(F.s.len.on(cap, op, n, two, eight, o), e) : Ws.W}:
  match two eight:
    case True{} _:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      fits_app(op, n, U32.is_lt(cap, n), o, e)

def len_go_app(+cap: U32, +op: U32, +n: U32, +m: Bool, +l: Bool, +o: List<&2, Ws.Frm>, +e: List<&2, Ws.Frm>) ->
  {F.s.len.go(cap, op, n, m, l, List.append(&2, Ws.Frm, o, e)) == wapp(F.s.len.go(cap, op, n, m, l, o), e) : Ws.W}:
  match m l:
    case False{} _:
      {==}
    case True{} True{}:
      {==}
    case True{} False{}:
      len_on_app(cap, op, n, U32.is_eq(n, 126), U32.is_eq(n, 127), o, e)

def ext_go_app(+op: U32, +left: U32, +len2: U32, +min: U32, +big: Bool, +done: Bool, +short: Bool,
  +o: List<&2, Ws.Frm>, +e: List<&2, Ws.Frm>) ->
  {F.s.ext.go(op, left, len2, min, big, done, short, List.append(&2, Ws.Frm, o, e)) ==
    wapp(F.s.ext.go(op, left, len2, min, big, done, short, o), e) : Ws.W}:
  match big done short:
    case True{} _ _:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} _:
      {==}

def msk_app(+op: U32, +len: U32, +left: U32, +m2: U32, +last: Bool, +empty: Bool, +o: List<&2, Ws.Frm>,
  +e: List<&2, Ws.Frm>) ->
  {Ws.step.msk.on(op, len, left, m2, List.append(&2, Ws.Frm, o, e), last, empty) ==
    wapp(Ws.step.msk.on(op, len, left, m2, o, last, empty), e) : Ws.W}:
  match last empty:
    case False{} _:
      {==}
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}

def pay_app(+op: U32, +left: U32, +m2: U32, +acc2: Bytes(), +last: Bool, +o: List<&2, Ws.Frm>, +e: List<&2, Ws.Frm>) ->
  {Ws.step.pay.on(op, left, m2, acc2, List.append(&2, Ws.Frm, o, e), last) ==
    wapp(Ws.step.pay.on(op, left, m2, acc2, o, last), e) : Ws.W}:
  match last:
    case True{}:
      {==}
    case False{}:
      {==}

# one byte at the server's end, with frames under the out list
def step_app(+cap: U32, +st: Ws.Fs, +o: List<&2, Ws.Frm>, +e: List<&2, Ws.Frm>, +b: U32) ->
  {F.step(F.Serv{cap}, Ws.W{st, List.append(&2, Ws.Frm, o, e)}, b) == wapp(F.step(F.Serv{cap}, Ws.W{st, o}, b), e) : Ws.W}:
  match st:
    case Ws.Op{}:
      {==}
    case Ws.Len{op}:
      len_go_app(cap, op, U32.and(b, 127), U32.is_eq(U32.and(b, 128), 128),
        F.c.ctl(op) && U32.is_lt(125, U32.and(b, 127)), o, e)
    case Ws.Ext{op, need, len, min}:
      ext_go_app(op, (need - 1 : U32), ((len * 256 : U32) + b : U32), min,
        U32.is_lt(cap, ((len * 256 : U32) + b : U32)) || U32.is_lt(16777215, len),
        U32.is_zero((need - 1 : U32)), U32.is_lt(((len * 256 : U32) + b : U32), min), o, e)
    case Ws.Msk{op, len, need, m}:
      msk_app(op, len, (need - 1 : U32), ((m * 256 : U32) + b : U32), U32.is_eq(need, 1), U32.is_zero(len), o, e)
    case Ws.Pay{op, rem, m, acc}:
      pay_app(op, (rem - 1 : U32), Ws.rot(m), SCon{Chr{U32.xor(b, Ws.key.of(m))}, acc}, U32.is_eq(rem, 1), o, e)
    case Ws.Bad{}:
      {==}

def step_wapp(+cap: U32, +w: Ws.W, +e: List<&2, Ws.Frm>, +b: U32) ->
  {F.step(F.Serv{cap}, wapp(w, e), b) == wapp(F.step(F.Serv{cap}, w, b), e) : Ws.W}:
  match w:
    case Ws.W{st, o}:
      step_app(cap, st, o, e, b)

def feed_app(+cap: U32, +bs: List<&2, U32>, +w: Ws.W, +e: List<&2, Ws.Frm>) ->
  {F.feed(F.Serv{cap}, bs, wapp(w, e)) == wapp(F.feed(F.Serv{cap}, bs, w), e) : Ws.W}:
  match bs:
    case Nil{}:
      {==}
    case Con{c, t}:
      Equal.trans(Ws.W, F.feed(F.Serv{cap}, t, F.step(F.Serv{cap}, wapp(w, e), c)),
        F.feed(F.Serv{cap}, t, wapp(F.step(F.Serv{cap}, w, c), e)),
        wapp(F.feed(F.Serv{cap}, t, F.step(F.Serv{cap}, w, c)), e),
        Equal.cong(Ws.W, Ws.W, x => F.feed(F.Serv{cap}, t, x), F.step(F.Serv{cap}, wapp(w, e), c),
          wapp(F.step(F.Serv{cap}, w, c), e), step_wapp(cap, w, e, c)),
        feed_app(cap, t, F.step(F.Serv{cap}, w, c), e))

def feed_buf_app(+cap: U32, +b: Bytes(), +w: Ws.W, +e: List<&2, Ws.Frm>) ->
  {F.feed_buf(F.Serv{cap}, b, wapp(w, e)) == wapp(F.feed_buf(F.Serv{cap}, b, w), e) : Ws.W}:
  Equal.trans(Ws.W, F.feed_buf(F.Serv{cap}, b, wapp(w, e)), F.feed(F.Serv{cap}, Bytes.to_list(b), wapp(w, e)),
    wapp(F.feed_buf(F.Serv{cap}, b, w), e),
    Laws.feed_buf(F.Serv{cap}, b, wapp(w, e)),
    Equal.trans(Ws.W, F.feed(F.Serv{cap}, Bytes.to_list(b), wapp(w, e)), wapp(F.feed(F.Serv{cap}, Bytes.to_list(b), w), e),
      wapp(F.feed_buf(F.Serv{cap}, b, w), e),
      feed_app(cap, Bytes.to_list(b), w, e),
      Equal.cong(Ws.W, Ws.W, x => wapp(x, e), F.feed(F.Serv{cap}, Bytes.to_list(b), w), F.feed_buf(F.Serv{cap}, b, w),
        Equal.sym(Ws.W, F.feed_buf(F.Serv{cap}, b, w), F.feed(F.Serv{cap}, Bytes.to_list(b), w),
          Laws.feed_buf(F.Serv{cap}, b, w)))))

# Lists
# -----

def app_assoc(+a: List<&2, Ws.Frm>, +b: List<&2, Ws.Frm>, +c: List<&2, Ws.Frm>) ->
  {List.append(&2, Ws.Frm, List.append(&2, Ws.Frm, a, b), c) == List.append(&2, Ws.Frm, a, List.append(&2, Ws.Frm, b, c))
    : List<&2, Ws.Frm>}:
  match a:
    case Nil{}:
      {==}
    case Con{x, t}:
      Equal.cong(List<&2, Ws.Frm>, List<&2, Ws.Frm>, l => Con{x, l}, List.append(&2, Ws.Frm, List.append(&2, Ws.Frm, t, b), c),
        List.append(&2, Ws.Frm, t, List.append(&2, Ws.Frm, b, c)), app_assoc(t, b, c))

def acts_assoc(+a: List<&2, F.Act>, +b: List<&2, F.Act>, +c: List<&2, F.Act>) ->
  {List.append(&2, F.Act, List.append(&2, F.Act, a, b), c) == List.append(&2, F.Act, a, List.append(&2, F.Act, b, c))
    : List<&2, F.Act>}:
  match a:
    case Nil{}:
      {==}
    case Con{x, t}:
      Equal.cong(List<&2, F.Act>, List<&2, F.Act>, l => Con{x, l}, List.append(&2, F.Act, List.append(&2, F.Act, t, b), c),
        List.append(&2, F.Act, t, List.append(&2, F.Act, b, c)), acts_assoc(t, b, c))

def rg_app(+a: List<&2, Ws.Frm>, +b: List<&2, Ws.Frm>, +acc: List<&2, Ws.Frm>) ->
  {List.reverse.go(&2, Ws.Frm, List.append(&2, Ws.Frm, a, b), acc) ==
    List.reverse.go(&2, Ws.Frm, b, List.reverse.go(&2, Ws.Frm, a, acc)) : List<&2, Ws.Frm>}:
  match a:
    case Nil{}:
      {==}
    case Con{x, t}:
      rg_app(t, b, Con{x, acc})

def rg_acc(+xs: List<&2, Ws.Frm>, +acc: List<&2, Ws.Frm>) ->
  {List.reverse.go(&2, Ws.Frm, xs, acc) == List.append(&2, Ws.Frm, List.reverse.go(&2, Ws.Frm, xs, Nil{}), acc)
    : List<&2, Ws.Frm>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      Equal.trans(List<&2, Ws.Frm>, List.reverse.go(&2, Ws.Frm, t, Con{x, acc}),
        List.append(&2, Ws.Frm, List.reverse.go(&2, Ws.Frm, t, Nil{}), Con{x, acc}),
        List.append(&2, Ws.Frm, List.reverse.go(&2, Ws.Frm, t, [x]), acc),
        rg_acc(t, Con{x, acc}),
        Equal.sym(List<&2, Ws.Frm>, List.append(&2, Ws.Frm, List.reverse.go(&2, Ws.Frm, t, [x]), acc),
          List.append(&2, Ws.Frm, List.reverse.go(&2, Ws.Frm, t, Nil{}), Con{x, acc}),
          Equal.trans(List<&2, Ws.Frm>, List.append(&2, Ws.Frm, List.reverse.go(&2, Ws.Frm, t, [x]), acc),
            List.append(&2, Ws.Frm, List.append(&2, Ws.Frm, List.reverse.go(&2, Ws.Frm, t, Nil{}), [x]), acc),
            List.append(&2, Ws.Frm, List.reverse.go(&2, Ws.Frm, t, Nil{}), Con{x, acc}),
            Equal.cong(List<&2, Ws.Frm>, List<&2, Ws.Frm>, l => List.append(&2, Ws.Frm, l, acc),
              List.reverse.go(&2, Ws.Frm, t, [x]), List.append(&2, Ws.Frm, List.reverse.go(&2, Ws.Frm, t, Nil{}), [x]),
              rg_acc(t, [x])),
            app_assoc(List.reverse.go(&2, Ws.Frm, t, Nil{}), [x], acc))))

def rev_app(+o2: List<&2, Ws.Frm>, +o1: List<&2, Ws.Frm>) ->
  {List.reverse(&2, Ws.Frm, List.append(&2, Ws.Frm, o2, o1)) ==
    List.append(&2, Ws.Frm, List.reverse(&2, Ws.Frm, o1), List.reverse(&2, Ws.Frm, o2)) : List<&2, Ws.Frm>}:
  Equal.trans(List<&2, Ws.Frm>, List.reverse.go(&2, Ws.Frm, List.append(&2, Ws.Frm, o2, o1), Nil{}),
    List.reverse.go(&2, Ws.Frm, o1, List.reverse.go(&2, Ws.Frm, o2, Nil{})),
    List.append(&2, Ws.Frm, List.reverse(&2, Ws.Frm, o1), List.reverse(&2, Ws.Frm, o2)),
    rg_app(o2, o1, Nil{}), rg_acc(o1, List.reverse.go(&2, Ws.Frm, o2, Nil{})))

# The assembler over pieces
# -------------------------

def ARs() -> Type:
  F.AR

def acts.pre(l: List<&2, F.Act>, r: F.AR) -> F.AR:
  match r:
    case F.AR{l2, a}:
      F.AR{List.append(&2, F.Act, l, l2), a}

def acts.cat(+cap: U32, r: F.AR, ys: List<&2, Ws.Frm>) -> F.AR:
  match r:
    case F.AR{l, a}:
      acts.pre(l, F.acts.run(cap, ys, a))

def pre_nil(+r: F.AR) -> {acts.pre(Nil{}, r) == r : F.AR}:
  match r:
    case F.AR{l, a}:
      {==}

def push_pre(+x: F.Act, +l: List<&2, F.Act>, +r: F.AR) ->
  {F.acts.push(x, acts.pre(l, r)) == acts.pre(Con{x, l}, r) : F.AR}:
  match r:
    case F.AR{l2, a}:
      {==}

def push_cat(+cap: U32, +x: F.Act, +r: F.AR, +ys: List<&2, Ws.Frm>) ->
  {F.acts.push(x, acts.cat(cap, r, ys)) == acts.cat(cap, F.acts.push(x, r), ys) : F.AR}:
  match r:
    case F.AR{l, a}:
      push_pre(x, l, F.acts.run(cap, ys, a))

def acts_app(+cap: U32, +xs: List<&2, Ws.Frm>, +ys: List<&2, Ws.Frm>, +a: F.Asm) ->
  {F.acts.run(cap, List.append(&2, Ws.Frm, xs, ys), a) == acts.cat(cap, F.acts.run(cap, xs, a), ys)
    : F.AR}:
  match xs:
    case Nil{}:
      Equal.sym(F.AR, acts.pre(Nil{}, F.acts.run(cap, ys, a)), F.acts.run(cap, ys, a),
        pre_nil(F.acts.run(cap, ys, a)))
    case Con{f, t}:
      Equal.trans(F.AR,
        F.acts.push(F.ax.act(F.asm(cap, a, f)), F.acts.run(cap, List.append(&2, Ws.Frm, t, ys), F.ax.asm(F.asm(cap, a, f)))),
        F.acts.push(F.ax.act(F.asm(cap, a, f)), acts.cat(cap, F.acts.run(cap, t, F.ax.asm(F.asm(cap, a, f))), ys)),
        acts.cat(cap, F.acts.push(F.ax.act(F.asm(cap, a, f)), F.acts.run(cap, t, F.ax.asm(F.asm(cap, a, f)))), ys),
        Equal.cong(F.AR, F.AR, q => F.acts.push(F.ax.act(F.asm(cap, a, f)), q),
          F.acts.run(cap, List.append(&2, Ws.Frm, t, ys), F.ax.asm(F.asm(cap, a, f))),
          acts.cat(cap, F.acts.run(cap, t, F.ax.asm(F.asm(cap, a, f))), ys),
          acts_app(cap, t, ys, F.ax.asm(F.asm(cap, a, f)))),
        push_cat(cap, F.ax.act(F.asm(cap, a, f)), F.acts.run(cap, t, F.ax.asm(F.asm(cap, a, f))), ys))

# The reads
# ---------

# the second piece's acts, after the first's
def fin_pre(+xs1: List<&2, F.Act>, +r2: F.AR, +w: Ws.W) ->
  {List.append(&2, F.Act, xs1, F.s.fin(r2, w)) == F.s.fin(acts.pre(xs1, r2), w) : List<&2, F.Act>}:
  match r2:
    case F.AR{xs2, a2}:
      Equal.sym(List<&2, F.Act>, List.append(&2, F.Act, List.append(&2, F.Act, xs1, xs2), F.s.bad(w)),
        List.append(&2, F.Act, xs1, List.append(&2, F.Act, xs2, F.s.bad(w))), acts_assoc(xs1, xs2, F.s.bad(w)))

def G(cap: U32, rs: List<&2, Bytes()>, st: Ws.Fs, a: F.Asm) -> Type:
  {F.s.reads.go(cap, rs, Ws.W{st, Nil{}}, a) ==
    F.s.tail(cap, Ws.take(F.feed_buf(F.Serv{cap}, Bytes.concat(rs), Ws.W{st, Nil{}})), a) : List<&2, F.Act>}

# the first read's acts, then the rest's (by the hypothesis, the
# second piece's frames assembled from where the first left off)
def took_ih(+cap: U32, -t: List<&2, Bytes()>, +st1: Ws.Fs, +r1: F.AR, +o2: List<&2, Ws.Frm>, +w: Ws.W,
  ih2: @a1: F.Asm -> {F.s.reads.go(cap, t, Ws.W{st1, Nil{}}, a1) ==
    F.s.fin(F.acts.run(cap, List.reverse(&2, Ws.Frm, o2), a1), w) : List<&2, F.Act>}) ->
  {F.s.took.run(r1, Ws.W{st1, Nil{}}, w2 => a2 => F.s.reads.go(cap, t, w2, a2)) ==
    F.s.fin(acts.cat(cap, r1, List.reverse(&2, Ws.Frm, o2)), w) : List<&2, F.Act>}:
  match r1:
    case F.AR{xs1, a1}:
      Equal.trans(List<&2, F.Act>, List.append(&2, F.Act, xs1, F.s.reads.go(cap, t, Ws.W{st1, Nil{}}, a1)),
        List.append(&2, F.Act, xs1, F.s.fin(F.acts.run(cap, List.reverse(&2, Ws.Frm, o2), a1), w)),
        F.s.fin(acts.pre(xs1, F.acts.run(cap, List.reverse(&2, Ws.Frm, o2), a1)), w),
        Equal.cong(List<&2, F.Act>, List<&2, F.Act>, l => List.append(&2, F.Act, xs1, l),
          F.s.reads.go(cap, t, Ws.W{st1, Nil{}}, a1), F.s.fin(F.acts.run(cap, List.reverse(&2, Ws.Frm, o2), a1), w), ih2(a1)),
        fin_pre(xs1, F.acts.run(cap, List.reverse(&2, Ws.Frm, o2), a1), w))

# the reader after the rest, taken apart: the frames it pushed over the
# first read's
def con_w2(+cap: U32, -t: List<&2, Bytes()>, +st1: Ws.Fs, +o1: List<&2, Ws.Frm>, +w2: Ws.W, +a: F.Asm,
  ih2: @a1: F.Asm -> {F.s.reads.go(cap, t, Ws.W{st1, Nil{}}, a1) == F.s.tail(cap, Ws.take(w2), a1) : List<&2, F.Act>}) ->
  {F.s.took.run(F.acts.run(cap, List.reverse(&2, Ws.Frm, o1), a), Ws.W{st1, Nil{}}, w3 => a3 => F.s.reads.go(cap, t, w3, a3)) ==
    F.s.tail(cap, Ws.take(wapp(w2, o1)), a) : List<&2, F.Act>}:
  match w2:
    case Ws.W{st2, o2}:
      Equal.trans(List<&2, F.Act>,
        F.s.took.run(F.acts.run(cap, List.reverse(&2, Ws.Frm, o1), a), Ws.W{st1, Nil{}}, w3 => a3 => F.s.reads.go(cap, t, w3, a3)),
        F.s.fin(acts.cat(cap, F.acts.run(cap, List.reverse(&2, Ws.Frm, o1), a), List.reverse(&2, Ws.Frm, o2)), Ws.W{st2, Nil{}}),
        F.s.fin(F.acts.run(cap, List.reverse(&2, Ws.Frm, List.append(&2, Ws.Frm, o2, o1)), a), Ws.W{st2, Nil{}}),
        took_ih(cap, t, st1, F.acts.run(cap, List.reverse(&2, Ws.Frm, o1), a), o2, Ws.W{st2, Nil{}}, ih2),
        Equal.sym(List<&2, F.Act>,
          F.s.fin(F.acts.run(cap, List.reverse(&2, Ws.Frm, List.append(&2, Ws.Frm, o2, o1)), a), Ws.W{st2, Nil{}}),
          F.s.fin(acts.cat(cap, F.acts.run(cap, List.reverse(&2, Ws.Frm, o1), a), List.reverse(&2, Ws.Frm, o2)), Ws.W{st2, Nil{}}),
          Equal.trans(List<&2, F.Act>,
            F.s.fin(F.acts.run(cap, List.reverse(&2, Ws.Frm, List.append(&2, Ws.Frm, o2, o1)), a), Ws.W{st2, Nil{}}),
            F.s.fin(F.acts.run(cap, List.append(&2, Ws.Frm, List.reverse(&2, Ws.Frm, o1), List.reverse(&2, Ws.Frm, o2)), a),
              Ws.W{st2, Nil{}}),
            F.s.fin(acts.cat(cap, F.acts.run(cap, List.reverse(&2, Ws.Frm, o1), a), List.reverse(&2, Ws.Frm, o2)), Ws.W{st2, Nil{}}),
            Equal.cong(List<&2, Ws.Frm>, List<&2, F.Act>, l => F.s.fin(F.acts.run(cap, l, a), Ws.W{st2, Nil{}}),
              List.reverse(&2, Ws.Frm, List.append(&2, Ws.Frm, o2, o1)),
              List.append(&2, Ws.Frm, List.reverse(&2, Ws.Frm, o1), List.reverse(&2, Ws.Frm, o2)), rev_app(o2, o1)),
            Equal.cong(F.AR, List<&2, F.Act>, q => F.s.fin(q, Ws.W{st2, Nil{}}),
              F.acts.run(cap, List.append(&2, Ws.Frm, List.reverse(&2, Ws.Frm, o1), List.reverse(&2, Ws.Frm, o2)), a),
              acts.cat(cap, F.acts.run(cap, List.reverse(&2, Ws.Frm, o1), a), List.reverse(&2, Ws.Frm, o2)),
              acts_app(cap, List.reverse(&2, Ws.Frm, o1), List.reverse(&2, Ws.Frm, o2), a)))))

# the reader after the first read, taken apart
def con_w(+cap: U32, +t: List<&2, Bytes()>, +w1: Ws.W, +a: F.Asm, ih: @st2: Ws.Fs -> @a2: F.Asm -> G(cap, t, st2, a2)) ->
  {F.s.took(cap, Ws.take(w1), a, w2 => a2 => F.s.reads.go(cap, t, w2, a2)) ==
    F.s.tail(cap, Ws.take(F.feed_buf(F.Serv{cap}, Bytes.concat(t), w1)), a) : List<&2, F.Act>}:
  match w1:
    case Ws.W{st1, o1}:
      Equal.trans(List<&2, F.Act>,
        F.s.took.run(F.acts.run(cap, List.reverse(&2, Ws.Frm, o1), a), Ws.W{st1, Nil{}}, w3 => a3 => F.s.reads.go(cap, t, w3, a3)),
        F.s.tail(cap, Ws.take(wapp(F.feed_buf(F.Serv{cap}, Bytes.concat(t), Ws.W{st1, Nil{}}), o1)), a),
        F.s.tail(cap, Ws.take(F.feed_buf(F.Serv{cap}, Bytes.concat(t), Ws.W{st1, o1})), a),
        con_w2(cap, t, st1, o1, F.feed_buf(F.Serv{cap}, Bytes.concat(t), Ws.W{st1, Nil{}}), a, a1 => ih(st1, a1)),
        Equal.cong(Ws.W, List<&2, F.Act>, x => F.s.tail(cap, Ws.take(x), a),
          wapp(F.feed_buf(F.Serv{cap}, Bytes.concat(t), Ws.W{st1, Nil{}}), o1),
          F.feed_buf(F.Serv{cap}, Bytes.concat(t), Ws.W{st1, o1}),
          Equal.sym(Ws.W, F.feed_buf(F.Serv{cap}, Bytes.concat(t), Ws.W{st1, o1}),
            wapp(F.feed_buf(F.Serv{cap}, Bytes.concat(t), Ws.W{st1, Nil{}}), o1),
            feed_buf_app(cap, Bytes.concat(t), Ws.W{st1, Nil{}}, o1))))

def reads_go(+cap: U32, +rs: List<&2, Bytes()>, +st: Ws.Fs, +a: F.Asm) -> G(cap, rs, st, a):
  match rs:
    case Nil{}:
      {==}
    case Con{r, t}:
      Equal.trans(List<&2, F.Act>,
        F.s.took(cap, Ws.take(F.feed_buf(F.Serv{cap}, r, Ws.W{st, Nil{}})), a, w2 => a2 => F.s.reads.go(cap, t, w2, a2)),
        F.s.tail(cap, Ws.take(F.feed_buf(F.Serv{cap}, Bytes.concat(t), F.feed_buf(F.Serv{cap}, r, Ws.W{st, Nil{}}))), a),
        F.s.tail(cap, Ws.take(F.feed_buf(F.Serv{cap}, Bytes.append(r, Bytes.concat(t)), Ws.W{st, Nil{}})), a),
        con_w(cap, t, F.feed_buf(F.Serv{cap}, r, Ws.W{st, Nil{}}), a, s2 => a2 => reads_go(cap, t, s2, a2)),
        Equal.cong(Ws.W, List<&2, F.Act>, x => F.s.tail(cap, Ws.take(x), a),
          F.feed_buf(F.Serv{cap}, Bytes.concat(t), F.feed_buf(F.Serv{cap}, r, Ws.W{st, Nil{}})),
          F.feed_buf(F.Serv{cap}, Bytes.append(r, Bytes.concat(t)), Ws.W{st, Nil{}}),
          Equal.sym(Ws.W, F.feed_buf(F.Serv{cap}, Bytes.append(r, Bytes.concat(t)), Ws.W{st, Nil{}}),
            F.feed_buf(F.Serv{cap}, Bytes.concat(t), F.feed_buf(F.Serv{cap}, r, Ws.W{st, Nil{}})),
            Laws.feed_buf_split(F.Serv{cap}, r, Bytes.concat(t), Ws.W{st, Nil{}}))))

def Laws.srv_reads(cap, rs):
  reads_go(cap, rs, Ws.Op{}, F.Idle{})
