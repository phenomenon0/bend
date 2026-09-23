# The proofs of LAWS.bend.
import Base
import ../../wire/reader.bend as Wr
import ./huff.bend as H
import ./hpack.bend as K
import ./LAWS.bend as Laws
import ./nat.bend as N
import ./huff_proof.bend as HP
import ./frame.bend as Fm
import ./spec.bend as Sp
import ./conn.bend as C
import ./main.bend as S
import ../../wire/loop.bend as L
import ../../wire/world.bend as WW

# HPACK integers
# ==============

# acc + r m + q (128 m) = acc + (128 q + r) m
def ring(+acc: Nat, +q: Nat, +r: Nat, +m: Nat) ->
  {Nat.add(Nat.add(acc, Nat.mul(r, m)), Nat.mul(q, Nat.mul(m, 128n))) ==
    Nat.add(acc, Nat.mul(Nat.add(Nat.mul(q, 128n), r), m)) : Nat}:
  %Equal.sym(Nat, Nat.mul(Nat.add(Nat.mul(q, 128n), r), m), Nat.add(Nat.mul(Nat.mul(q, 128n), m), Nat.mul(r, m)),
      N.mul_distr(Nat.mul(q, 128n), r, m)) :
    {Nat.add(Nat.add(acc, Nat.mul(r, m)), Nat.mul(q, Nat.mul(m, 128n))) == Nat.add(acc, _) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.mul(q, 128n), m), Nat.mul(q, Nat.mul(128n, m)), N.mul_assoc(q, 128n, m)) :
    {Nat.add(Nat.add(acc, Nat.mul(r, m)), Nat.mul(q, Nat.mul(m, 128n))) == Nat.add(acc, Nat.add(_, Nat.mul(r, m))) : Nat}
  %N.mul_comm(m, 128n) :
    {Nat.add(Nat.add(acc, Nat.mul(r, m)), Nat.mul(q, Nat.mul(m, 128n))) ==
      Nat.add(acc, Nat.add(Nat.mul(q, _), Nat.mul(r, m))) : Nat}
  %N.add_comm(Nat.mul(r, m), Nat.mul(q, Nat.mul(m, 128n))) :
    {Nat.add(Nat.add(acc, Nat.mul(r, m)), Nat.mul(q, Nat.mul(m, 128n))) == Nat.add(acc, _) : Nat}
  N.add_assoc(acc, Nat.mul(r, m), Nat.mul(q, Nat.mul(m, 128n)))

def dq(+x: Nat) -> Nat:
  Nat.div(x, 128n)

def dr(+x: Nat) -> Nat:
  Nat.mod(x, 128n)

# the last digit: below 128, read as itself, and the value is done
def cont.base(+j: Nat, +r: Nat, +acc: Nat, +mul: Nat, +hr: {Nat.is_lt(r, 128n) == True{} : Bool}) ->
  {K.int.feed(K.int.cont(1n+j, (0n, r)), K.ICont{acc, mul, 1n+j}) ==
    K.IDone{Nat.add(acc, Nat.mul(r, mul))} : K.Ist}:
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(r)), r, N.byte_nat(r, N.lt_le(r, 128n, 256n, hr, {==}))) :
    {K.int.byte(acc, mul, 1n+j, _, Nat.is_le(128n, _)) == K.IDone{Nat.add(acc, Nat.mul(r, mul))} : K.Ist}
  %Equal.sym(Bool, Nat.is_le(128n, r), False{}, N.lt_nle(r, 128n, hr)) :
    {K.int.byte(acc, mul, 1n+j, r, _) == K.IDone{Nat.add(acc, Nat.mul(r, mul))} : K.Ist}
  {==}

# The continuation bytes of 128 q + r, a value of at most 1+j digits,
# from a decoder with 1+j bytes left, read back as that value:
# induction on j, a digit a step, the quotient's digits the rest.
def cont.go(+j: Nat, +q: Nat, +r: Nat, +acc: Nat, +mul: Nat, +hr: {Nat.is_lt(r, 128n) == True{} : Bool},
  +hq: {K.int.fits(j, q) == True{} : Bool}) ->
  {K.int.feed(K.int.cont(1n+j, (q, r)), K.ICont{acc, mul, 1n+j}) ==
    K.IDone{Nat.add(acc, Nat.mul(Nat.add(Nat.mul(q, 128n), r), mul))} : K.Ist}:
  match j q:
    case 0n 0n:
      cont.base(0n, r, acc, mul, hr)
    case 1n+k 0n:
      cont.base(1n+k, r, acc, mul, hr)
    case 0n 1n+p:
      N.absurd({K.int.feed(K.int.cont(1n, (1n+p, r)), K.ICont{acc, mul, 1n}) ==
        K.IDone{Nat.add(acc, Nat.mul(Nat.add(Nat.mul(1n+p, 128n), r), mul))} : K.Ist}, N.ft(hq))
    case 1n+k 1n+p:
      %Equal.sym(Nat, U32.to_nat(U32.from_nat(Nat.add(128n, r))), Nat.add(128n, r),
          N.byte_nat(Nat.add(128n, r), hr)) :
        {K.int.feed(K.int.cont(1n+k, Nat.divmod(1n+p, 128n)),
          K.int.byte(acc, mul, 2n+k, _, Nat.is_le(128n, _))) ==
          K.IDone{Nat.add(acc, Nat.mul(Nat.add(Nat.mul(1n+p, 128n), r), mul))} : K.Ist}
      %Equal.sym(Bool, Nat.is_le(0n, r), True{}, N.le0(r)) :
        {K.int.feed(K.int.cont(1n+k, Nat.divmod(1n+p, 128n)),
          K.int.byte(acc, mul, 2n+k, Nat.add(128n, r), _)) ==
          K.IDone{Nat.add(acc, Nat.mul(Nat.add(Nat.mul(1n+p, 128n), r), mul))} : K.Ist}
      %Equal.sym(Nat, Nat.sub(r, 0n), r, N.sub_0r(r)) :
        {K.int.feed(K.int.cont(1n+k, Nat.divmod(1n+p, 128n)), K.int.more(acc, mul, 2n+k, _)) ==
          K.IDone{Nat.add(acc, Nat.mul(Nat.add(Nat.mul(1n+p, 128n), r), mul))} : K.Ist}
      %ring(acc, 1n+p, r, mul) :
        {K.int.feed(K.int.cont(1n+k, Nat.divmod(1n+p, 128n)),
          K.ICont{Nat.add(acc, Nat.mul(r, mul)), Nat.mul(mul, 128n), 1n+k}) == K.IDone{_} : K.Ist}
      %Equal.sym(Nat & Nat, Nat.divmod(1n+p, 128n), (dq(1n+p), dr(1n+p)), N.eta(Nat.divmod(1n+p, 128n))) :
        {K.int.feed(K.int.cont(1n+k, _), K.ICont{Nat.add(acc, Nat.mul(r, mul)), Nat.mul(mul, 128n), 1n+k}) ==
          K.IDone{Nat.add(Nat.add(acc, Nat.mul(r, mul)), Nat.mul(1n+p, Nat.mul(mul, 128n)))} : K.Ist}
      %N.dm_eq(1n+p) :
        {K.int.feed(K.int.cont(1n+k, (dq(1n+p), dr(1n+p))),
          K.ICont{Nat.add(acc, Nat.mul(r, mul)), Nat.mul(mul, 128n), 1n+k}) ==
          K.IDone{Nat.add(Nat.add(acc, Nat.mul(r, mul)), Nat.mul(_, Nat.mul(mul, 128n)))} : K.Ist}
      cont.go(k, dq(1n+p), dr(1n+p), Nat.add(acc, Nat.mul(r, mul)), Nat.mul(mul, 128n), N.dm_lt(1n+p), hq)

# the same for x itself, x of at most 1+j digits
def cont_rt(+j: Nat, +x: Nat, +acc: Nat, +mul: Nat, +h: {K.int.fits(1n+j, x) == True{} : Bool}) ->
  {K.int.feed(K.int.cont(1n+j, Nat.divmod(x, 128n)), K.ICont{acc, mul, 1n+j}) ==
    K.IDone{Nat.add(acc, Nat.mul(x, mul))} : K.Ist}:
  %Equal.sym(Nat & Nat, Nat.divmod(x, 128n), (dq(x), dr(x)), N.eta(Nat.divmod(x, 128n))) :
    {K.int.feed(K.int.cont(1n+j, _), K.ICont{acc, mul, 1n+j}) == K.IDone{Nat.add(acc, Nat.mul(x, mul))} : K.Ist}
  %N.dm_eq(x) :
    {K.int.feed(K.int.cont(1n+j, (dq(x), dr(x))), K.ICont{acc, mul, 1n+j}) ==
      K.IDone{Nat.add(acc, Nat.mul(_, mul))} : K.Ist}
  cont.go(j, dq(x), dr(x), acc, mul, N.dm_lt(x), h)

# past the prefix: the prefix's ones, then v - max in continuation bytes
def rt.big(+max: Nat, +v: Nat, +e: {Nat.is_lt(v, max) == False{} : Bool},
  +h: {K.int.fits(K.int.cap(), Nat.sub(v, max)) == True{} : Bool}) ->
  {K.int.feed(K.int.cont(4n, Nat.divmod(Nat.sub(v, max), 128n)), K.ICont{max, 1n, 4n}) == K.IDone{v} : K.Ist}:
  %Equal.sym(K.Ist, K.int.feed(K.int.cont(4n, Nat.divmod(Nat.sub(v, max), 128n)), K.ICont{max, 1n, 4n}),
      K.IDone{Nat.add(max, Nat.mul(Nat.sub(v, max), 1n))}, cont_rt(3n, Nat.sub(v, max), max, 1n, h)) :
    {_ == K.IDone{v} : K.Ist}
  %Equal.sym(Nat, Nat.mul(Nat.sub(v, max), 1n), Nat.sub(v, max), N.mul_1r(Nat.sub(v, max))) :
    {K.IDone{Nat.add(max, _)} == K.IDone{v} : K.Ist}
  %Equal.sym(Nat, Nat.add(max, Nat.sub(v, max)), v, N.add_sub(max, v, e)) :
    {K.IDone{_} == K.IDone{v} : K.Ist}
  {==}

# within the prefix: the byte is the value
def rt.small(+max: Nat, +v: Nat, +e: {Nat.is_lt(v, max) == True{} : Bool},
  h: {Nat.is_le(max, 256n) == True{} : Bool}) ->
  {K.int.first(max, U32.to_nat(U32.from_nat(v))) == K.IDone{v} : K.Ist}:
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(v)), v, N.byte_nat(v, N.lt_le(v, max, 256n, e, h))) :
    {K.int.first(max, _) == K.IDone{v} : K.Ist}
  %Equal.sym(Bool, Nat.is_lt(v, max), True{}, e) :
    {K.int.first.go(max, v, _) == K.IDone{v} : K.Ist}
  {==}

def rt.go(p: K.Pfx, +v: Nat, lt: Bool, +e: {Nat.is_lt(v, K.pfx.max(p)) == lt : Bool},
  +h: {K.int.fits(K.int.cap(), Nat.sub(v, K.pfx.max(p))) == True{} : Bool}) ->
  {K.int.dec(p, K.int.enc.go(0n, K.pfx.max(p), v, lt)) == K.IDone{v} : K.Ist}:
  match p lt:
    case K.P4{} True{}:
      rt.small(15n, v, e, {==})
    case K.P5{} True{}:
      rt.small(31n, v, e, {==})
    case K.P6{} True{}:
      rt.small(63n, v, e, {==})
    case K.P7{} True{}:
      rt.small(127n, v, e, {==})
    case K.P4{} False{}:
      rt.big(15n, v, e, h)
    case K.P5{} False{}:
      rt.big(31n, v, e, h)
    case K.P6{} False{}:
      rt.big(63n, v, e, h)
    case K.P7{} False{}:
      rt.big(127n, v, e, h)

def Laws.int_rt(p, v, h):
  rt.go(p, v, Nat.is_lt(v, K.pfx.max(p)), {==}, h)

def Laws.int_c1_1():
  {==}

def Laws.int_c1_2():
  {==}

def Laws.int_c1_3():
  {==}

def Laws.int_over():
  {==}

# HPACK Huffman strings
# =====================

# the ones that pad bs to a whole byte, as chunk8 adds them
def padbits(bs: List<&2, Bool>) -> List<&2, Bool>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{a, Nil{}}:
      [True{}, True{}, True{}, True{}, True{}, True{}, True{}]
    case Con{a, Con{b, Nil{}}}:
      [True{}, True{}, True{}, True{}, True{}, True{}]
    case Con{a, Con{b, Con{c, Nil{}}}}:
      [True{}, True{}, True{}, True{}, True{}]
    case Con{a, Con{b, Con{c, Con{d, Nil{}}}}}:
      [True{}, True{}, True{}, True{}]
    case Con{a, Con{b, Con{c, Con{d, Con{e, Nil{}}}}}}:
      [True{}, True{}, True{}]
    case Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, Nil{}}}}}}}:
      [True{}, True{}]
    case Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, Con{g, Nil{}}}}}}}}:
      [True{}]
    case Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, Con{g, Con{h, t}}}}}}}}:
      padbits(t)

# the walk over a join is the walk over its parts
def walk_cat(+root: H.Ht, xs: List<&2, Bool>, -ys: List<&2, Bool>, h: K.Hf) ->
  {HP.walk(root, List.append(&2, Bool, xs, ys), h) == HP.walk(root, ys, HP.walk(root, xs, h)) : K.Hf}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      walk_cat(root, t, ys, K.hf.bit(root, h, x))

# the packed bytes decode as the bits they pack, padding included
def feed_chunk(+root: H.Ht, bs: List<&2, Bool>, +h: K.Hf) ->
  {K.hf.feed(root, K.chunk8(bs), h) == HP.walk(root, List.append(&2, Bool, bs, padbits(bs)), h) : K.Hf}:
  match bs:
    case Nil{}:
      {==}
    case Con{a, Nil{}}:
      HP.hf_byte(root, h, a, True{}, True{}, True{}, True{}, True{}, True{}, True{})
    case Con{a, Con{b, Nil{}}}:
      HP.hf_byte(root, h, a, b, True{}, True{}, True{}, True{}, True{}, True{})
    case Con{a, Con{b, Con{c, Nil{}}}}:
      HP.hf_byte(root, h, a, b, c, True{}, True{}, True{}, True{}, True{})
    case Con{a, Con{b, Con{c, Con{d, Nil{}}}}}:
      HP.hf_byte(root, h, a, b, c, d, True{}, True{}, True{}, True{})
    case Con{a, Con{b, Con{c, Con{d, Con{e, Nil{}}}}}}:
      HP.hf_byte(root, h, a, b, c, d, e, True{}, True{}, True{})
    case Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, Nil{}}}}}}}:
      HP.hf_byte(root, h, a, b, c, d, e, f, True{}, True{})
    case Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, Con{g, Nil{}}}}}}}}:
      HP.hf_byte(root, h, a, b, c, d, e, f, g, True{})
    case Con{+a, Con{+b, Con{+c, Con{+d, Con{+e, Con{+f, Con{+g, Con{+i, t}}}}}}}}:
      %Equal.sym(K.Hf, K.hf.byte(root, h, K.pack8(a, b, c, d, e, f, g, i)),
          HP.walk(root, [a, b, c, d, e, f, g, i], h), HP.hf_byte(root, h, a, b, c, d, e, f, g, i)) :
        {K.hf.feed(root, K.chunk8(t), _) ==
          HP.walk(root, List.append(&2, Bool, Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, Con{g, Con{i, t}}}}}}}},
            padbits(t)), h) : K.Hf}
      feed_chunk(root, t, HP.walk(root, [a, b, c, d, e, f, g, i], h))

def str_nil(s: Bytes()) -> {String.append(s, SNil{}) == s : Bytes()}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      %str_nil(t) : {SCon{c, String.append(t, SNil{})} == SCon{c, _} : Bytes()}
      {==}

def str_assoc(a: Bytes(), -b: Bytes(), -c: Bytes()) ->
  {String.append(String.append(a, b), c) == String.append(a, String.append(b, c)) : Bytes()}:
  match a:
    case SNil{}:
      {==}
    case SCon{x, t}:
      %str_assoc(t, b, c) : {SCon{x, String.append(String.append(t, b), c)} == SCon{x, _} : Bytes()}
      {==}

# every code in turn walks to its byte: the string's bits walk to the
# string
def walk_str(ws: List<&2, Word(8n)>, +acc: Bytes()) ->
  {HP.walk(H.tree(), K.huff.bits(Laws.bytes(ws)), K.HfAt{H.tree(), acc}) ==
    K.HfAt{H.tree(), String.append(acc, Laws.bytes(ws))} : K.Hf}:
  match ws:
    case Nil{}:
      %Equal.sym(Bytes(), String.append(acc, SNil{}), acc, str_nil(acc)) : {K.HfAt{H.tree(), acc} == K.HfAt{H.tree(), _} : K.Hf}
      {==}
    case Con{+w, t}:
      %Equal.sym(K.Hf, HP.walk(H.tree(), List.append(&2, Bool, K.code(Laws.byte(w)), K.huff.bits(Laws.bytes(t))),
          K.HfAt{H.tree(), acc}),
          HP.walk(H.tree(), K.huff.bits(Laws.bytes(t)), HP.walk(H.tree(), K.code(Laws.byte(w)), K.HfAt{H.tree(), acc})),
          walk_cat(H.tree(), K.code(Laws.byte(w)), K.huff.bits(Laws.bytes(t)), K.HfAt{H.tree(), acc})) :
        {_ == K.HfAt{H.tree(), String.append(acc, SCon{Chr{Laws.byte(w)}, Laws.bytes(t)})} : K.Hf}
      %Equal.sym(K.Hf, HP.walk(H.tree(), K.code(Laws.byte(w)), K.HfAt{H.tree(), acc}),
          K.HfAt{H.tree(), Bytes.push(acc, Laws.byte(w))}, HP.hf_sym(acc, w)) :
        {HP.walk(H.tree(), K.huff.bits(Laws.bytes(t)), _) ==
          K.HfAt{H.tree(), String.append(acc, SCon{Chr{Laws.byte(w)}, Laws.bytes(t)})} : K.Hf}
      %str_assoc(acc, SCon{Chr{Laws.byte(w)}, SNil{}}, Laws.bytes(t)) :
        {HP.walk(H.tree(), K.huff.bits(Laws.bytes(t)), K.HfAt{H.tree(), Bytes.push(acc, Laws.byte(w))}) ==
          K.HfAt{H.tree(), _} : K.Hf}
      walk_str(t, Bytes.push(acc, Laws.byte(w)))

# the padding ends where a string may: at most seven ones from the root
def pad_end(bs: List<&2, Bool>, +out: Bytes()) ->
  {K.hf.end(HP.walk(H.tree(), padbits(bs), K.HfAt{H.tree(), out})) == Some{out} : Maybe<&2, Bytes()>}:
  match bs:
    case Nil{}:
      {==}
    case Con{a, Nil{}}:
      {==}
    case Con{a, Con{b, Nil{}}}:
      {==}
    case Con{a, Con{b, Con{c, Nil{}}}}:
      {==}
    case Con{a, Con{b, Con{c, Con{d, Nil{}}}}}:
      {==}
    case Con{a, Con{b, Con{c, Con{d, Con{e, Nil{}}}}}}:
      {==}
    case Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, Nil{}}}}}}}:
      {==}
    case Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, Con{g, Nil{}}}}}}}}:
      {==}
    case Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, Con{g, Con{h, t}}}}}}}}:
      pad_end(t, out)

def Laws.huff_rt(ws):
  %Equal.sym(K.Hf, K.hf.feed(H.tree(), K.chunk8(K.huff.bits(Laws.bytes(ws))), K.HfAt{H.tree(), ""}),
      HP.walk(H.tree(), List.append(&2, Bool, K.huff.bits(Laws.bytes(ws)), padbits(K.huff.bits(Laws.bytes(ws)))),
        K.HfAt{H.tree(), ""}),
      feed_chunk(H.tree(), K.huff.bits(Laws.bytes(ws)), K.HfAt{H.tree(), ""})) :
    {K.hf.end(_) == Some{Laws.bytes(ws)} : Maybe<&2, Bytes()>}
  %Equal.sym(K.Hf,
      HP.walk(H.tree(), List.append(&2, Bool, K.huff.bits(Laws.bytes(ws)), padbits(K.huff.bits(Laws.bytes(ws)))),
        K.HfAt{H.tree(), ""}),
      HP.walk(H.tree(), padbits(K.huff.bits(Laws.bytes(ws))),
        HP.walk(H.tree(), K.huff.bits(Laws.bytes(ws)), K.HfAt{H.tree(), ""})),
      walk_cat(H.tree(), K.huff.bits(Laws.bytes(ws)), padbits(K.huff.bits(Laws.bytes(ws))), K.HfAt{H.tree(), ""})) :
    {K.hf.end(_) == Some{Laws.bytes(ws)} : Maybe<&2, Bytes()>}
  %Equal.sym(K.Hf, HP.walk(H.tree(), K.huff.bits(Laws.bytes(ws)), K.HfAt{H.tree(), ""}),
      K.HfAt{H.tree(), Laws.bytes(ws)}, walk_str(ws, "")) :
    {K.hf.end(HP.walk(H.tree(), padbits(K.huff.bits(Laws.bytes(ws))), _)) == Some{Laws.bytes(ws)} : Maybe<&2, Bytes()>}
  pad_end(K.huff.bits(Laws.bytes(ws)), Laws.bytes(ws))

def Laws.huff_eos():
  {==}

def Laws.huff_pad_long():
  {==}

def Laws.huff_pad_zero():
  {==}

def fit.case(e: K.Fld, -t: List<&2, K.Fld>, +b: Nat, ok: Bool,
  eq: {Nat.is_le(K.fld.size(e), b) == ok : Bool},
  ih: {Nat.is_le(K.sizes(K.fit(t, Nat.sub(b, K.fld.size(e)))), Nat.sub(b, K.fld.size(e))) == True{} : Bool}) ->
  {Nat.is_le(K.sizes(K.fit.pick(e, K.fit(t, Nat.sub(b, K.fld.size(e))), ok)), b) == True{} : Bool}:
  match ok:
    case True{}:
      N.le_add_sub(K.fld.size(e), b, K.sizes(K.fit(t, Nat.sub(b, K.fld.size(e)))), eq, ih)
    case False{}:
      N.le0(b)

def Laws.fit_le(es, b):
  match es:
    case Nil{}:
      N.le0(b)
    case Con{+e, t}:
      fit.case(e, t, b, Nat.is_le(K.fld.size(e), b), {==}, Laws.fit_le(t, Nat.sub(b, K.fld.size(e))))

def Laws.tbl_add_fits(t, f):
  match t:
    case K.Tbl{es, max}:
      Laws.fit_le(Con{f, es}, max)

def Laws.tbl_resize_fits(t, m):
  match t:
    case K.Tbl{es, max}:
      Laws.fit_le(es, m)

# HPACK: the decoder's bounds
# ===========================
#
# Every function the step goes through, with the invariant of what it
# is handed, hands back a decoder with it: only field.cap and got.size
# change what the invariant speaks of, and each checks what it must.

def dj.bad(-t: K.Tbl, -out: List<&2, K.Fld>, -sz: Nat, -any: Bool, -lim: K.Lim, -why: K.Err,
  j: Laws.J(t, out, sz, lim)) -> Laws.INV(K.bad(t, out, sz, any, lim, why)):
  j

def dj.kind(k: K.Rep, +t: K.Tbl, +f: K.Fld, h: {Laws.fits(t) == True{} : Bool}) ->
  {Laws.fits(K.field.kind(k, t, f)) == True{} : Bool}:
  match k:
    case K.KInc{}:
      Laws.tbl_add_fits(t, f)
    case K.KNot{}:
      h
    case K.KNever{}:
      h

def dj.sz(-sz: Nat, +out: List<&2, K.Fld>, +f: K.Fld, jz: {sz == K.sizes(out) : Nat}) ->
  {Nat.add(sz, K.fld.size(f)) == K.sizes(Con{f, out}) : Nat}:
  %Equal.sym(Nat, sz, K.sizes(out), jz) : {Nat.add(_, K.fld.size(f)) == Nat.add(K.fld.size(f), K.sizes(out)) : Nat}
  N.add_comm(K.sizes(out), K.fld.size(f))

def dj.cap(+k: K.Rep, +t: K.Tbl, +out: List<&2, K.Fld>, +sz: Nat, +lim: K.Lim, +f: K.Fld, ok: Bool,
  e: {Nat.is_le(Nat.add(sz, K.fld.size(f)), K.lim.l(lim)) == ok : Bool}, j: Laws.J(t, out, sz, lim)) ->
  Laws.INV(K.field.cap(k, t, out, sz, Nat.add(sz, K.fld.size(f)), lim, f, ok)):
  match ok:
    case False{}:
      j
    case True{}:
      match j:
        case (jz, jr):
          match jr:
            case (jl, jt):
              (dj.sz(sz, out, f, jz), (e, dj.kind(k, t, f, jt)))

def dj.field(+k: K.Rep, +t: K.Tbl, +out: List<&2, K.Fld>, +sz: Nat, +lim: K.Lim, +f: K.Fld,
  j: Laws.J(t, out, sz, lim)) -> Laws.INV(K.field(k, t, out, sz, lim, f)):
  dj.cap(k, t, out, sz, lim, f, Nat.is_le(Nat.add(sz, K.fld.size(f)), K.lim.l(lim)), {==}, j)

def dj.idx(+t: K.Tbl, +out: List<&2, K.Fld>, +sz: Nat, +lim: K.Lim, m: Maybe<&2, K.Fld>,
  j: Laws.J(t, out, sz, lim)) -> Laws.INV(K.got.idx(t, out, sz, lim, m)):
  match m:
    case None{}:
      j
    case Some{f}:
      dj.field(K.KNot{}, t, out, sz, lim, f, j)

def dj.name(-k: K.Rep, -t: K.Tbl, -out: List<&2, K.Fld>, -sz: Nat, -lim: K.Lim, m: Maybe<&2, K.Fld>,
  j: Laws.J(t, out, sz, lim)) -> Laws.INV(K.got.name(k, t, out, sz, lim, m)):
  match m:
    case None{}:
      j
    case Some{f}:
      match f:
        case K.Fld{n, v}:
          j

def dj.size(+t: K.Tbl, -out: List<&2, K.Fld>, -sz: Nat, -any: Bool, -lim: K.Lim, +v: Nat, ok: Bool,
  j: Laws.J(t, out, sz, lim)) -> Laws.INV(K.got.size(t, out, sz, any, lim, v, ok)):
  match ok:
    case False{}:
      j
    case True{}:
      match j:
        case (jz, jr):
          match jr:
            case (jl, jt):
              (jz, (jl, Laws.tbl_resize_fits(t, v)))

def dj.done(+fo: K.For, m: Maybe<&2, Bytes()>, +t: K.Tbl, +out: List<&2, K.Fld>, +sz: Nat, +lim: K.Lim,
  j: Laws.J(t, out, sz, lim)) -> Laws.INV(K.str.done(fo, m, t, out, sz, lim)):
  match fo m:
    case K.FName{k} None{}:
      j
    case K.FVal{k, name} None{}:
      j
    case K.FName{k} Some{s}:
      j
    case K.FVal{k, name} Some{s}:
      dj.field(k, t, out, sz, lim, K.Fld{name, s}, j)

def dj.len(+root: H.Ht, +fo: K.For, +h: Bool, +t: K.Tbl, +out: List<&2, K.Fld>, +sz: Nat, +lim: K.Lim, n: Nat,
  j: Laws.J(t, out, sz, lim)) -> Laws.INV(K.str.len(root, fo, h, t, out, sz, lim, n)):
  match n:
    case 0n:
      dj.done(fo, K.str.fin(K.str.sb(root, h)), t, out, sz, lim, j)
    case 1n+m:
      j

def dj.start(+root: H.Ht, +fo: K.For, +h: Bool, +t: K.Tbl, +out: List<&2, K.Fld>, +sz: Nat, +lim: K.Lim, +n: Nat,
  ok: Bool, j: Laws.J(t, out, sz, lim)) -> Laws.INV(K.str.start(root, fo, h, t, out, sz, lim, n, ok)):
  match ok:
    case True{}:
      dj.len(root, fo, h, t, out, sz, lim, n, j)
    case False{}:
      j

def dj.int.done(+root: H.Ht, to: K.To, +v: Nat, +t: K.Tbl, +out: List<&2, K.Fld>, +sz: Nat, +any: Bool,
  +lim: K.Lim, j: Laws.J(t, out, sz, lim)) -> Laws.INV(K.int.done(root, to, v, t, out, sz, any, lim)):
  match to:
    case K.TIdx{}:
      dj.idx(t, out, sz, lim, K.at(v, t), j)
    case K.TName{k}:
      dj.name(k, t, out, sz, lim, K.at(v, t), j)
    case K.TSize{}:
      dj.size(t, out, sz, any, lim, v, Bool.not(any) && Nat.is_le(v, K.lim.t(lim)), j)
    case K.TLen{fo, h}:
      dj.start(root, fo, h, t, out, sz, lim, v, Nat.is_le(v, K.lim.l(lim)), j)

def dj.int(+root: H.Ht, +to: K.To, i: K.Ist, +t: K.Tbl, +out: List<&2, K.Fld>, +sz: Nat, +any: Bool,
  +lim: K.Lim, j: Laws.J(t, out, sz, lim)) -> Laws.INV(K.int.at(root, to, i, t, out, sz, any, lim)):
  match i:
    case K.IDone{v}:
      dj.int.done(root, to, v, t, out, sz, any, lim, j)
    case K.ICont{acc, mul, left}:
      j
    case K.IOver{}:
      j

def dj.lit(+root: H.Ht, +k: K.Rep, +p: K.Pfx, v: Nat, +t: K.Tbl, +out: List<&2, K.Fld>, +sz: Nat,
  +lim: K.Lim, j: Laws.J(t, out, sz, lim)) -> Laws.INV(K.lit(root, k, p, v, t, out, sz, lim)):
  match v:
    case 0n:
      j
    case 1n+i:
      dj.int(root, K.TName{k}, K.int.first(K.pfx.max(p), 1n+i), t, out, sz, True{}, lim, j)

def dj.top(+root: H.Ht, +b: Nat, +t: K.Tbl, +out: List<&2, K.Fld>, +sz: Nat, +any: Bool, +lim: K.Lim,
  ix: Bool, inc: Bool, up: Bool, nev: Bool, j: Laws.J(t, out, sz, lim)) ->
  Laws.INV(K.top.go(root, b, t, out, sz, any, lim, ix, inc, up, nev)):
  match ix inc up nev:
    case True{} _ _ _:
      dj.int(root, K.TIdx{}, K.int.first(127n, Nat.sub(b, 128n)), t, out, sz, True{}, lim, j)
    case False{} True{} _ _:
      dj.lit(root, K.KInc{}, K.P6{}, Nat.sub(b, 64n), t, out, sz, lim, j)
    case False{} False{} True{} _:
      dj.int(root, K.TSize{}, K.int.first(31n, Nat.sub(b, 32n)), t, out, sz, any, lim, j)
    case False{} False{} False{} True{}:
      dj.lit(root, K.KNever{}, K.P4{}, Nat.sub(b, 16n), t, out, sz, lim, j)
    case False{} False{} False{} False{}:
      dj.lit(root, K.KNot{}, K.P4{}, b, t, out, sz, lim, j)

def dj.lengo(+root: H.Ht, +fo: K.For, +b: Nat, +t: K.Tbl, +out: List<&2, K.Fld>, +sz: Nat, +lim: K.Lim, h: Bool,
  j: Laws.J(t, out, sz, lim)) -> Laws.INV(K.len.go(root, fo, b, t, out, sz, lim, h)):
  match h:
    case True{}:
      dj.int(root, K.TLen{fo, True{}}, K.int.first(127n, Nat.sub(b, 128n)), t, out, sz, True{}, lim, j)
    case False{}:
      dj.int(root, K.TLen{fo, False{}}, K.int.first(127n, b), t, out, sz, True{}, lim, j)

def dj.byte(+fo: K.For, left: Nat, +sb: K.Sb, +t: K.Tbl, +out: List<&2, K.Fld>, +sz: Nat, +lim: K.Lim,
  j: Laws.J(t, out, sz, lim)) -> Laws.INV(K.str.byte(fo, left, sb, t, out, sz, lim)):
  match left:
    case 0n:
      dj.done(fo, K.str.fin(sb), t, out, sz, lim, j)
    case 1n+m:
      j

def dj.at(+root: H.Ht, at: K.At, +t: K.Tbl, +out: List<&2, K.Fld>, +sz: Nat, +any: Bool, +lim: K.Lim, +c: U32,
  j: Laws.J(t, out, sz, lim)) -> Laws.INV(K.step.at(root, at, t, out, sz, any, lim, c)):
  match at:
    case K.ATop{}:
      dj.top(root, U32.to_nat(c), t, out, sz, any, lim, Nat.is_le(128n, U32.to_nat(c)),
        Nat.is_le(64n, U32.to_nat(c)), Nat.is_le(32n, U32.to_nat(c)), Nat.is_le(16n, U32.to_nat(c)), j)
    case K.ALen{fo}:
      dj.lengo(root, fo, U32.to_nat(c), t, out, sz, lim, Nat.is_le(128n, U32.to_nat(c)), j)
    case K.AInt{to, i}:
      dj.int(root, to, K.int.step(i, c), t, out, sz, any, lim, j)
    case K.AStr{fo, left, sb}:
      dj.byte(fo, left, K.sb.byte(root, sb, c), t, out, sz, lim, j)
    case K.ABad{why}:
      j

def Laws.dec_step(root, d, c, h):
  match d:
    case K.Dc{at, +t, +out, +sz, +any, +lim}:
      dj.at(root, at, t, out, sz, any, lim, c, h)

def Laws.dec_feed(root, bs, d, h):
  match bs:
    case Nil{}:
      h
    case Con{+c, t}:
      Laws.dec_feed(root, t, K.step(root, d, c), Laws.dec_step(root, d, c, h))

def Laws.dec_begin(d, h):
  match d:
    case K.Dc{at, t, out, sz, any, +lim}:
      match h:
        case (jz, jr):
          match jr:
            case (jl, jt):
              ({==}, (N.le0(K.lim.l(lim)), jt))

def Laws.dec_new(tmax, lmax):
  ({==}, (N.le0(lmax), N.le0(tmax)))

def Laws.list_capped(d, h):
  match d:
    case K.Dc{at, t, out, sz, any, lim}:
      match h:
        case (jz, jr):
          match jr:
            case (jl, jt):
              %jz : {Nat.is_le(_, K.lim.l(lim)) == True{} : Bool}
              jl

def Laws.refuse_idx0():
  {==}

def Laws.refuse_idx_past():
  {==}

def Laws.refuse_name_past():
  {==}

def Laws.refuse_int():
  {==}

def Laws.refuse_huff_eos():
  {==}

def Laws.refuse_huff_pad():
  {==}

def Laws.refuse_size_big():
  {==}

def Laws.refuse_size_late():
  {==}

def Laws.size_first():
  {==}

def Laws.refuse_cut():
  {==}

def Laws.refuse_str_big():
  {==}

def Laws.refuse_bomb():
  {==}

def Laws.c2_1():
  {==}

def Laws.c2_2():
  {==}

def Laws.c2_3():
  {==}

def Laws.c2_4():
  {==}

def Laws.c3_dec():
  {==}

def Laws.c4_dec():
  {==}

def Laws.c5_dec():
  {==}

def Laws.c6_dec():
  {==}

def Laws.c3_enc():
  {==}

def Laws.c4_enc():
  {==}

def Laws.c5_enc():
  {==}

def Laws.c6_enc():
  {==}

def Laws.static_index():
  {==}

# Frames
# ======

# a refused reader absorbs every byte: the kit's obligation, and so the
# kit's bad_feeds
type Bx is Data:
  Bx{why: Fm.Why, max: Nat, out: List<&2, Fm.Frm>}

def bx(x: Bx) -> Fm.Rd:
  match x:
    case Bx{w, m, o}:
      Fm.Rd{Fm.FBad{w}, m, o}

def absorbs(+u: Unit, +x: Bx, +c: U32) -> {Fm.wstep(u, bx(x), c) == bx(x) : Fm.Rd}:
  match x:
    case Bx{w, m, o}:
      {==}

def bad_feed(+bs: List<&2, U32>, +why: Fm.Why, +max: Nat, +out: List<&2, Fm.Frm>) ->
  {Fm.feed(bs, Fm.Rd{Fm.FBad{why}, max, out}) == Fm.Rd{Fm.FBad{why}, max, out} : Fm.Rd}:
  Wr.bad_feeds(~Unit, ~Fm.Rd, ~Fm.wstep, ~Bx, ~bx, ~absorbs, Unit{}, bs, Bx{why, max, out})

def len(xs: List<&2, U32>) -> Nat:
  List.length(&2, U32, xs)

# A payload: from a reader with m more bytes to go after the next, xs
# either runs out first (still reading, nothing new completed) or holds
# the payload and then r, and the frame completes where the payload ends.
def RP(-ty: U32, -fl: U32, -sid: U32, -m: Nat, -acc: Bytes(), -max: Nat, -out: List<&2, Fm.Frm>,
  -xs: List<&2, U32>, mt: Maybe<&2, Sp.Two>) -> Type:
  match mt:
    case None{}:
      {Laws.look(Fm.feed(xs, Fm.Rd{Fm.FPay{ty, fl, sid, m, acc}, max, out})) == (out, Laws.Reading{}) :
        List<&2, Fm.Frm> & Laws.Look}
    case Some{tw}:
      match tw:
        case Sp.Two{p, r}:
          {Fm.feed(xs, Fm.Rd{Fm.FPay{ty, fl, sid, m, acc}, max, out}) ==
            Fm.feed(r, Laws.start(max, Con{Fm.Frm{ty, fl, sid, String.append(acc, Bytes.from_list(p))}, out})) :
            Fm.Rd} & {Nat.is_le(len(r), len(xs)) == True{} : Bool}

def pay.eq(+ty: U32, +fl: U32, +sid: U32, -m: Nat, +acc: Bytes(), +max: Nat, +out: List<&2, Fm.Frm>, +c: U32,
  -t: List<&2, U32>, +p: List<&2, U32>, -r: List<&2, U32>,
  e1: {Fm.feed(t, Fm.Rd{Fm.FPay{ty, fl, sid, m, Bytes.push(acc, c)}, max, out}) ==
    Fm.feed(r, Laws.start(max, Con{Fm.Frm{ty, fl, sid, String.append(Bytes.push(acc, c), Bytes.from_list(p))}, out})) :
    Fm.Rd}) ->
  {Fm.feed(t, Fm.Rd{Fm.FPay{ty, fl, sid, m, Bytes.push(acc, c)}, max, out}) ==
    Fm.feed(r, Laws.start(max, Con{Fm.Frm{ty, fl, sid, String.append(acc, Bytes.from_list(Con{c, p}))}, out})) :
    Fm.Rd}:
  %str_assoc(acc, SCon{Chr{c}, SNil{}}, Bytes.from_list(p)) :
    {Fm.feed(t, Fm.Rd{Fm.FPay{ty, fl, sid, m, Bytes.push(acc, c)}, max, out}) ==
      Fm.feed(r, Laws.start(max, Con{Fm.Frm{ty, fl, sid, _}, out})) : Fm.Rd}
  e1

def pay.step(+ty: U32, +fl: U32, +sid: U32, -m: Nat, +acc: Bytes(), +max: Nat, +out: List<&2, Fm.Frm>, +c: U32,
  +t: List<&2, U32>, mt: Maybe<&2, Sp.Two>, ih: RP(ty, fl, sid, m, Bytes.push(acc, c), max, out, t, mt)) ->
  RP(ty, fl, sid, 1n+m, acc, max, out, Con{c, t}, Sp.take.on(c, mt)):
  match mt:
    case None{}:
      ih
    case Some{tw}:
      match tw:
        case Sp.Two{p, r}:
          match ih:
            case (e1, e2):
              (pay.eq(ty, fl, sid, m, acc, max, out, c, t, p, r, e1), N.le_S(len(r), len(t), e2))

def pay(+ty: U32, +fl: U32, +sid: U32, +m: Nat, +acc: Bytes(), +max: Nat, +out: List<&2, Fm.Frm>,
  xs: List<&2, U32>) -> RP(ty, fl, sid, m, acc, max, out, xs, Sp.take(1n+m, xs)):
  match m xs:
    case 0n Nil{}:
      {==}
    case 1n+k Nil{}:
      {==}
    case 0n Con{+c, +t}:
      ({==}, N.le_S(len(t), len(t), N.le_refl(len(t))))
    case 1n+k Con{+c, +t}:
      pay.step(ty, fl, sid, k, acc, max, out, c, t, Sp.take(1n+k, t), pay(ty, fl, sid, k, Bytes.push(acc, c), max, out, t))

# What comes after a header: the relation, from the reader's side,
# between the reader after the rest of the input and what the reference
# cut from it.
def RC9(-max: Nat, -r0: Fm.Rd, -rest: List<&2, U32>, -out: List<&2, Fm.Frm>, c: Sp.Cut) -> Type:
  match c:
    case Sp.CShort{}:
      {Laws.look(Fm.feed(rest, r0)) == (out, Laws.Reading{}) : List<&2, Fm.Frm> & Laws.Look}
    case Sp.CBig{}:
      {Laws.look(Fm.feed(rest, r0)) == (out, Laws.Refusing{Fm.WSize{}}) : List<&2, Fm.Frm> & Laws.Look}
    case Sp.CFrm{fr, r}:
      {Fm.feed(rest, r0) == Fm.feed(r, Laws.start(max, Con{fr, out})) : Fm.Rd} &
        {Nat.is_le(len(r), len(rest)) == True{} : Bool}

def pay.cut(+ty: U32, +fl: U32, +sid: U32, -m: Nat, +max: Nat, +out: List<&2, Fm.Frm>, -rest: List<&2, U32>,
  mt: Maybe<&2, Sp.Two>, h: RP(ty, fl, sid, m, "", max, out, rest, mt)) ->
  RC9(max, Fm.Rd{Fm.FPay{ty, fl, sid, m, ""}, max, out}, rest, out, Sp.cut.pay(ty, fl, sid, mt)):
  match mt:
    case None{}:
      h
    case Some{tw}:
      match tw:
        case Sp.Two{p, r}:
          h

def cut.len9(+max: Nat, big: Bool, +n: Nat, +ty: U32, +fl: U32, +sid: U32, +rest: List<&2, U32>,
  +out: List<&2, Fm.Frm>) ->
  RC9(max, Fm.step.len(big, n, ty, fl, sid, max, out), rest, out, Sp.cut.len(big, n, ty, fl, sid, rest)):
  match big:
    case True{}:
      %Equal.sym(Fm.Rd, Fm.feed(rest, Fm.Rd{Fm.FBad{Fm.WSize{}}, max, out}), Fm.Rd{Fm.FBad{Fm.WSize{}}, max, out},
          bad_feed(rest, Fm.WSize{}, max, out)) :
        {Laws.look(_) == (out, Laws.Refusing{Fm.WSize{}}) : List<&2, Fm.Frm> & Laws.Look}
      {==}
    case False{}:
      match n:
        case 0n:
          ({==}, N.le_refl(len(rest)))
        case 1n+m:
          pay.cut(ty, fl, sid, m, max, out, rest, Sp.take(1n+m, rest), pay(ty, fl, sid, m, "", max, out, rest))

# the relation for a whole input from a frame's first byte
def RC(-max: Nat, -bs: List<&2, U32>, -out: List<&2, Fm.Frm>, c: Sp.Cut) -> Type:
  match c:
    case Sp.CShort{}:
      {Laws.look(Fm.feed(bs, Laws.start(max, out))) == (out, Laws.Reading{}) : List<&2, Fm.Frm> & Laws.Look}
    case Sp.CBig{}:
      {Laws.look(Fm.feed(bs, Laws.start(max, out))) == (out, Laws.Refusing{Fm.WSize{}}) :
        List<&2, Fm.Frm> & Laws.Look}
    case Sp.CFrm{fr, r}:
      {Fm.feed(bs, Laws.start(max, out)) == Fm.feed(r, Laws.start(max, Con{fr, out})) : Fm.Rd} &
        {Nat.is_le(1n+len(r), len(bs)) == True{} : Bool}

def cut.nine(+max: Nat, +b0: U32, +b1: U32, +b2: U32, +b3: U32, +b4: U32, +b5: U32, +b6: U32, +b7: U32,
  +b8: U32, +rest: List<&2, U32>, +out: List<&2, Fm.Frm>, c: Sp.Cut,
  h: RC9(max, Fm.step.hd9([b8, b7, b6, b5, b4, b3, b2, b1, b0], max, out), rest, out, c)) ->
  RC(max, Con{b0, Con{b1, Con{b2, Con{b3, Con{b4, Con{b5, Con{b6, Con{b7, Con{b8, rest}}}}}}}}}, out, c):
  match c:
    case Sp.CShort{}:
      h
    case Sp.CBig{}:
      h
    case Sp.CFrm{fr, r}:
      match h:
        case (e1, e2):
          (e1, N.le_add8(len(r), len(rest), e2))

def cut_ok(+max: Nat, +bs: List<&2, U32>, +out: List<&2, Fm.Frm>) -> RC(max, bs, out, Sp.cut(max, bs)):
  match bs:
    case Nil{}:
      {==}
    case [a]:
      {==}
    case [a, b]:
      {==}
    case [a, b, c]:
      {==}
    case [a, b, c, d]:
      {==}
    case [a, b, c, d, e]:
      {==}
    case [a, b, c, d, e, f]:
      {==}
    case [a, b, c, d, e, f, g]:
      {==}
    case [a, b, c, d, e, f, g, h]:
      {==}
    case Con{+b0, Con{+b1, Con{+b2, Con{+b3, Con{+b4, Con{+b5, Con{+b6, Con{+b7, Con{+b8, +rest}}}}}}}}}:
      cut.nine(max, b0, b1, b2, b3, b4, b5, b6, b7, b8, rest, out,
        Sp.cut.len(Nat.is_lt(max, Fm.u24(b0, b1, b2)), Fm.u24(b0, b1, b2), b3, b4, Fm.u31(b5, b6, b7, b8), rest),
        cut.len9(max, Nat.is_lt(max, Fm.u24(b0, b1, b2)), Fm.u24(b0, b1, b2), b3, b4, Fm.u31(b5, b6, b7, b8),
          rest, out))

# frame after frame: the reader from a frame's first byte agrees with
# the reference's walk, for every fuel the input's length is within
def sim(+fuel: Nat, +max: Nat, +bs: List<&2, U32>, +out: List<&2, Fm.Frm>, c: Sp.Cut, h: RC(max, bs, out, c),
  +hf: {Nat.is_le(len(bs), fuel) == True{} : Bool}) ->
  Laws.agree(Fm.feed(bs, Laws.start(max, out)), max, Sp.go(fuel, max, bs, c, out)):
  match fuel:
    case 0n:
      match bs:
        case Nil{}:
          ({==}, {==})
        case Con{x, t}:
          N.absurd(Laws.agree(Fm.feed(Con{x, t}, Laws.start(max, out)), max, Sp.go(0n, max, Con{x, t}, c, out)),
            N.ft(hf))
    case 1n+f:
      match c:
        case Sp.CShort{}:
          (h, {==})
        case Sp.CBig{}:
          h
        case Sp.CFrm{+fr, +r}:
          match h:
            case (e1, e2):
              %Equal.sym(Fm.Rd, Fm.feed(bs, Laws.start(max, out)), Fm.feed(r, Laws.start(max, Con{fr, out})), e1) :
                Laws.agree(_, max, Sp.go(f, max, r, Sp.cut(max, r), Con{fr, out}))
              sim(f, max, r, Con{fr, out}, Sp.cut(max, r), cut_ok(max, r, Con{fr, out}),
                N.le_trans(1n+len(r), len(bs), 1n+f, e2, hf))

# The preface: the reader fed the input, beside how the reference
# begins.
def RPre(-max: Nat, -fed: Fm.Rd, pr: Sp.Pre) -> Type:
  match pr:
    case Sp.PMore{}:
      {Laws.look(fed) == (Nil{}, Laws.Reading{}) : List<&2, Fm.Frm> & Laws.Look}
    case Sp.PBad{}:
      {Laws.look(fed) == (Nil{}, Laws.Refusing{Fm.WPre{}}) : List<&2, Fm.Frm> & Laws.Look}
    case Sp.PDone{rest}:
      {fed == Fm.feed(rest, Laws.start(max, Nil{})) : Fm.Rd}

def pre.bad(+max: Nat, +u: List<&2, U32>) ->
  {Laws.look(Fm.feed(u, Fm.Rd{Fm.FBad{Fm.WPre{}}, max, Nil{}})) == (Nil{}, Laws.Refusing{Fm.WPre{}}) :
    List<&2, Fm.Frm> & Laws.Look}:
  %Equal.sym(Fm.Rd, Fm.feed(u, Fm.Rd{Fm.FBad{Fm.WPre{}}, max, Nil{}}), Fm.Rd{Fm.FBad{Fm.WPre{}}, max, Nil{}},
      bad_feed(u, Fm.WPre{}, max, Nil{})) :
    {Laws.look(_) == (Nil{}, Laws.Refusing{Fm.WPre{}}) : List<&2, Fm.Frm> & Laws.Look}
  {==}

def pre.nil(+max: Nat, ok: Bool, +u: List<&2, U32>) ->
  RPre(max, Fm.feed(u, Fm.step.pre.go(ok, Nil{}, max, Nil{})), Sp.pre.on(ok, Sp.PDone{u})):
  match ok:
    case True{}:
      {==}
    case False{}:
      pre.bad(max, u)

def pre.con(+max: Nat, ok: Bool, +p: U32, +t: List<&2, U32>, +u: List<&2, U32>,
  ih: RPre(max, Fm.feed(u, Fm.Rd{Fm.FPre{Con{p, t}}, max, Nil{}}), Sp.pre(Con{p, t}, u))) ->
  RPre(max, Fm.feed(u, Fm.step.pre.go(ok, Con{p, t}, max, Nil{})), Sp.pre.on(ok, Sp.pre(Con{p, t}, u))):
  match ok:
    case True{}:
      ih
    case False{}:
      pre.bad(max, u)

def pre_ok(bs: List<&2, U32>, +max: Nat, +p: U32, +t: List<&2, U32>) ->
  RPre(max, Fm.feed(bs, Fm.Rd{Fm.FPre{Con{p, t}}, max, Nil{}}), Sp.pre(Con{p, t}, bs)):
  match bs:
    case Nil{}:
      {==}
    case Con{+c, +u}:
      match t:
        case Nil{}:
          pre.nil(max, U32.is_eq(c, p), u)
        case Con{+q, +w}:
          pre.con(max, U32.is_eq(c, p), q, w, u, pre_ok(u, max, q, w))

def frames.ok(+max: Nat, +bs: List<&2, U32>, pr: Sp.Pre, h: RPre(max, Fm.feed(bs, Fm.new(max)), pr)) ->
  Laws.agree(Fm.feed(bs, Fm.new(max)), max, Sp.frames.pre(max, bs, pr)):
  match pr:
    case Sp.PMore{}:
      h
    case Sp.PBad{}:
      h
    case Sp.PDone{+rest}:
      %Equal.sym(Fm.Rd, Fm.feed(bs, Fm.new(max)), Fm.feed(rest, Laws.start(max, Nil{})), h) :
        Laws.agree(_, max, Sp.go(List.length(&2, U32, rest), max, rest, Sp.cut(max, rest), Nil{}))
      sim(List.length(&2, U32, rest), max, rest, Nil{}, Sp.cut(max, rest), cut_ok(max, rest, Nil{}),
        N.le_refl(len(rest)))

def Laws.frame_sim(max, bs):
  frames.ok(max, bs, Sp.pre(Sp.preface(), bs), pre_ok(bs, max, 80, Wr.bytes("RI * HTTP/2.0\r\n\r\nSM\r\n\r\n")))

def feed_buf_is(+b: Bytes(), +r: Fm.Rd) -> {Fm.feed_buf(b, r) == Fm.feed(Bytes.to_list(b), r) : Fm.Rd}:
  Wr.feed_buf_is_feed(~Unit, ~Fm.Rd, ~Fm.wstep, ~Fm.wadv, ~Wr.one.step_ok(~Unit, ~Fm.Rd, ~Fm.wstep), Unit{}, b, r)

def Laws.frame_sim_buf(max, b):
  %Equal.sym(Fm.Rd, Fm.feed_buf(b, Fm.new(max)), Fm.feed(Bytes.to_list(b), Fm.new(max)), feed_buf_is(b, Fm.new(max))) :
    Laws.agree(_, max, Sp.frames(max, Bytes.to_list(b)))
  Laws.frame_sim(max, Bytes.to_list(b))

def Laws.frame_sim_reads(max, rs):
  %Equal.sym(Fm.Rd, Laws.reads(rs, Fm.new(max)), Fm.feed(Bytes.to_list(Bytes.concat(rs)), Fm.new(max)),
      Wr.reads_is(~Unit, ~Fm.Rd, ~Fm.wstep, ~Fm.wadv, ~Wr.one.step_ok(~Unit, ~Fm.Rd, ~Fm.wstep), Unit{}, rs,
        Fm.new(max))) :
    Laws.agree(_, max, Sp.frames(max, Bytes.to_list(Bytes.concat(rs))))
  Laws.frame_sim(max, Bytes.to_list(Bytes.concat(rs)))

def Laws.frame_split(a, b, r):
  Wr.feed_split(~Unit, ~Fm.Rd, ~Fm.wstep, Unit{}, a, b, r)

def Laws.frame_settings():
  {==}

def Laws.frame_bad_preface():
  {==}

def Laws.frame_too_big():
  {==}

def Laws.frame_cut():
  {==}

def Laws.frame_fields():
  {==}


# Streams, flow control, budgets, requests
# =======================================

# words compare equal to themselves; a U32 is equal to and at most itself
def cmp_refl(n: Nat, w: Word(n)) -> {Word.cmp(n, w, w) == EQ{} : Cmp}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{True{}, t}:
          %Equal.sym(Cmp, Word.cmp(p, t, t), EQ{}, cmp_refl(p, t)) : {Word.cmp.fin(True{}, True{}, _) == EQ{} : Cmp}
          {==}
        case WCon{False{}, t}:
          %Equal.sym(Cmp, Word.cmp(p, t, t), EQ{}, cmp_refl(p, t)) : {Word.cmp.fin(False{}, False{}, _) == EQ{} : Cmp}
          {==}

def u32_eq_refl(x: U32) -> {U32.is_eq(x, x) == True{} : Bool}:
  match x:
    case U32{w}:
      %Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, cmp_refl(32n, w)) : {Cmp.is_eq(_) == True{} : Bool}
      {==}

def u32_le_refl(x: U32) -> {U32.is_le(x, x) == True{} : Bool}:
  match x:
    case U32{w}:
      %Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, cmp_refl(32n, w)) : {Cmp.is_le(_) == True{} : Bool}
      {==}

def cmp_lt_le(c: Cmp, h: {Cmp.is_lt(c) == True{} : Bool}) -> {Cmp.is_le(c) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      N.absurd({Cmp.is_le(EQ{}) == True{} : Bool}, N.ft(h))
    case GT{}:
      N.absurd({Cmp.is_le(GT{}) == True{} : Bool}, N.ft(h))

def and3(-a: Bool, -b: Bool, -c: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool},
  ec: {c == True{} : Bool}) -> {a && b && c == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {_ && b && c == True{} : Bool}
  %Equal.sym(Bool, b, True{}, eb) : {True{} && _ && c == True{} : Bool}
  %Equal.sym(Bool, c, True{}, ec) : {True{} && True{} && _ == True{} : Bool}
  {==}

def and4(-a: Bool, -b: Bool, -c: Bool, -d: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool},
  ec: {c == True{} : Bool}, ed: {d == True{} : Bool}) -> {a && b && c && d == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {_ && b && c && d == True{} : Bool}
  %Equal.sym(Bool, b, True{}, eb) : {True{} && _ && c && d == True{} : Bool}
  %Equal.sym(Bool, c, True{}, ec) : {True{} && True{} && _ && d == True{} : Bool}
  %Equal.sym(Bool, d, True{}, ed) : {True{} && True{} && True{} && _ == True{} : Bool}
  {==}

def Laws.verdict_rfc(s, t):
  match s t:
    case C.SIdle{} C.TData{}:
      {==}
    case C.SIdle{} C.THeaders{}:
      {==}
    case C.SIdle{} C.TPrio{}:
      {==}
    case C.SIdle{} C.TRst{}:
      {==}
    case C.SIdle{} C.TSettings{}:
      {==}
    case C.SIdle{} C.TPush{}:
      {==}
    case C.SIdle{} C.TPing{}:
      {==}
    case C.SIdle{} C.TGoaway{}:
      {==}
    case C.SIdle{} C.TWin{}:
      {==}
    case C.SIdle{} C.TCont{}:
      {==}
    case C.SIdle{} C.TOther{}:
      {==}
    case C.SOpen{} C.TData{}:
      {==}
    case C.SOpen{} C.THeaders{}:
      {==}
    case C.SOpen{} C.TPrio{}:
      {==}
    case C.SOpen{} C.TRst{}:
      {==}
    case C.SOpen{} C.TSettings{}:
      {==}
    case C.SOpen{} C.TPush{}:
      {==}
    case C.SOpen{} C.TPing{}:
      {==}
    case C.SOpen{} C.TGoaway{}:
      {==}
    case C.SOpen{} C.TWin{}:
      {==}
    case C.SOpen{} C.TCont{}:
      {==}
    case C.SOpen{} C.TOther{}:
      {==}
    case C.SHalf{} C.TData{}:
      {==}
    case C.SHalf{} C.THeaders{}:
      {==}
    case C.SHalf{} C.TPrio{}:
      {==}
    case C.SHalf{} C.TRst{}:
      {==}
    case C.SHalf{} C.TSettings{}:
      {==}
    case C.SHalf{} C.TPush{}:
      {==}
    case C.SHalf{} C.TPing{}:
      {==}
    case C.SHalf{} C.TGoaway{}:
      {==}
    case C.SHalf{} C.TWin{}:
      {==}
    case C.SHalf{} C.TCont{}:
      {==}
    case C.SHalf{} C.TOther{}:
      {==}
    case C.SLocal{} C.TData{}:
      {==}
    case C.SLocal{} C.THeaders{}:
      {==}
    case C.SLocal{} C.TPrio{}:
      {==}
    case C.SLocal{} C.TRst{}:
      {==}
    case C.SLocal{} C.TSettings{}:
      {==}
    case C.SLocal{} C.TPush{}:
      {==}
    case C.SLocal{} C.TPing{}:
      {==}
    case C.SLocal{} C.TGoaway{}:
      {==}
    case C.SLocal{} C.TWin{}:
      {==}
    case C.SLocal{} C.TCont{}:
      {==}
    case C.SLocal{} C.TOther{}:
      {==}
    case C.SReset{} C.TData{}:
      {==}
    case C.SReset{} C.THeaders{}:
      {==}
    case C.SReset{} C.TPrio{}:
      {==}
    case C.SReset{} C.TRst{}:
      {==}
    case C.SReset{} C.TSettings{}:
      {==}
    case C.SReset{} C.TPush{}:
      {==}
    case C.SReset{} C.TPing{}:
      {==}
    case C.SReset{} C.TGoaway{}:
      {==}
    case C.SReset{} C.TWin{}:
      {==}
    case C.SReset{} C.TCont{}:
      {==}
    case C.SReset{} C.TOther{}:
      {==}
    case C.SClosed{} C.TData{}:
      {==}
    case C.SClosed{} C.THeaders{}:
      {==}
    case C.SClosed{} C.TPrio{}:
      {==}
    case C.SClosed{} C.TRst{}:
      {==}
    case C.SClosed{} C.TSettings{}:
      {==}
    case C.SClosed{} C.TPush{}:
      {==}
    case C.SClosed{} C.TPing{}:
      {==}
    case C.SClosed{} C.TGoaway{}:
      {==}
    case C.SClosed{} C.TWin{}:
      {==}
    case C.SClosed{} C.TCont{}:
      {==}
    case C.SClosed{} C.TOther{}:
      {==}

# DATA on a stream whose verdict is a connection error: whatever its
# padding, the connection ends with the verdict's code
def vd.conn(+c: C.Cn, w: Bytes(), rq: List<&2, C.Req>, +fl: U32, +sid: U32, +len: Nat, +data: Bytes(), +code: U32,
  hv: {C.verdict(C.state(c, sid), C.TData{}) == C.VConn{code} : C.Vd}) ->
  {C.data.vd(c, w, rq, fl, sid, len, data, C.verdict(C.state(c, sid), C.TData{})) == C.die(c, w, rq, code) : C.Out}:
  %Equal.sym(C.Vd, C.verdict(C.state(c, sid), C.TData{}), C.VConn{code}, hv) :
    {C.data.vd(c, w, rq, fl, sid, len, data, _) == C.die(c, w, rq, code) : C.Out}
  {==}

def padded.conn(+c: C.Cn, w: Bytes(), rq: List<&2, C.Req>, +fl: U32, +sid: U32, +len: Nat, +data: Bytes(),
  bad: Bool, +code: U32, +hp: {code == C.e.proto() : U32},
  +hv: {C.verdict(C.state(c, sid), C.TData{}) == C.VConn{code} : C.Vd}) ->
  {C.data.padded(c, w, rq, fl, sid, len, data, bad) == C.die(c, w, rq, code) : C.Out}:
  match bad:
    case True{}:
      %Equal.sym(U32, code, C.e.proto(), hp) : {C.die(c, w, rq, C.e.proto()) == C.die(c, w, rq, _) : C.Out}
      {==}
    case False{}:
      vd.conn(c, w, rq, fl, sid, len, data, code, hv)

def pad.conn(+c: C.Cn, w: Bytes(), rq: List<&2, C.Req>, +fl: U32, +sid: U32, +pay: Bytes(), padded: Bool, +len: Nat,
  +code: U32, +hp: {code == C.e.proto() : U32},
  +hv: {C.verdict(C.state(c, sid), C.TData{}) == C.VConn{code} : C.Vd}) ->
  {C.data.pad(c, w, rq, fl, sid, pay, padded, len) == C.die(c, w, rq, code) : C.Out}:
  match padded len:
    case False{} _:
      vd.conn(c, w, rq, fl, sid, len, pay, code, hv)
    case True{} 0n:
      %Equal.sym(U32, code, C.e.proto(), hp) : {C.die(c, w, rq, C.e.proto()) == C.die(c, w, rq, _) : C.Out}
      {==}
    case True{} 1n+l:
      padded.conn(c, w, rq, fl, sid, 1n+l, Bytes.slice(pay, 1n, Nat.sub(l, U32.to_nat(Bytes.get(pay, 0n)))),
        Nat.is_le(1n+l, U32.to_nat(Bytes.get(pay, 0n))), code, hp, hv)

def data.conn.law(+root: H.Ht, +c: C.Cn, w: Bytes(), rq: List<&2, C.Req>, +fl: U32, +sid: U32, +pay: Bytes(),
  +code: U32, hb: {C.cn.blk(c) == C.BNone{} : C.Blk}, hz: {U32.is_zero(sid) == False{} : Bool},
  +hp: {code == C.e.proto() : U32},
  +hv: {C.verdict(C.state(c, sid), C.TData{}) == C.VConn{code} : C.Vd}) ->
  {Laws.one(root, c, w, rq, Fm.Frm{0, fl, sid, pay}) == C.die(c, w, rq, code) : C.Out}:
  %Equal.sym(C.Blk, C.cn.blk(c), C.BNone{}, hb) :
    {C.step.blk(root, c, w, rq, _, Fm.Frm{0, fl, sid, pay}) == C.die(c, w, rq, code) : C.Out}
  %Equal.sym(Bool, U32.is_zero(sid), False{}, hz) :
    {C.h.data.go(c, w, rq, fl, sid, pay, _) == C.die(c, w, rq, code) : C.Out}
  pad.conn(c, w, rq, fl, sid, pay, C.flag(fl, 8), Bytes.len(pay), code, hp, hv)

def Laws.idle_data(root, c, w, rq, fl, sid, pay, hb, hs, hz):
  data.conn.law(root, c, w, rq, fl, sid, pay, 1, hb, hz, {==},
    Equal.cong(C.Ss, C.Vd, s => C.verdict(s, C.TData{}), C.state(c, sid), C.SIdle{}, hs))

# an unpadded DATA frame goes straight to its verdict
def unpadded(+root: H.Ht, +c: C.Cn, w: Bytes(), rq: List<&2, C.Req>, +fl: U32, +sid: U32, +pay: Bytes(),
  hb: {C.cn.blk(c) == C.BNone{} : C.Blk}, hz: {U32.is_zero(sid) == False{} : Bool},
  hp: {C.flag(fl, 8) == False{} : Bool}) ->
  {Laws.one(root, c, w, rq, Fm.Frm{0, fl, sid, pay}) ==
    C.data.vd(c, w, rq, fl, sid, Bytes.len(pay), pay, C.verdict(C.state(c, sid), C.TData{})) : C.Out}:
  %Equal.sym(C.Blk, C.cn.blk(c), C.BNone{}, hb) :
    {C.step.blk(root, c, w, rq, _, Fm.Frm{0, fl, sid, pay}) ==
      C.data.vd(c, w, rq, fl, sid, Bytes.len(pay), pay, C.verdict(C.state(c, sid), C.TData{})) : C.Out}
  %Equal.sym(Bool, U32.is_zero(sid), False{}, hz) :
    {C.h.data.go(c, w, rq, fl, sid, pay, _) ==
      C.data.vd(c, w, rq, fl, sid, Bytes.len(pay), pay, C.verdict(C.state(c, sid), C.TData{})) : C.Out}
  %Equal.sym(Bool, C.flag(fl, 8), False{}, hp) :
    {C.data.pad(c, w, rq, fl, sid, pay, _, Bytes.len(pay)) ==
      C.data.vd(c, w, rq, fl, sid, Bytes.len(pay), pay, C.verdict(C.state(c, sid), C.TData{})) : C.Out}
  {==}

def Laws.closed_data(root, c, w, rq, fl, sid, pay, hb, hs, hz, hp):
  Equal.trans(C.Out, Laws.one(root, c, w, rq, Fm.Frm{0, fl, sid, pay}),
    C.data.vd(c, w, rq, fl, sid, Bytes.len(pay), pay, C.verdict(C.state(c, sid), C.TData{})),
    C.die(c, w, rq, C.e.closed()),
    unpadded(root, c, w, rq, fl, sid, pay, hb, hz, hp),
    vd.conn(c, w, rq, fl, sid, Bytes.len(pay), pay, 5,
      Equal.cong(C.Ss, C.Vd, s => C.verdict(s, C.TData{}), C.state(c, sid), C.SClosed{}, hs)))

def Laws.half_data(root, c, w, rq, fl, sid, pay, hb, hs, hz, hp):
  %Equal.sym(C.Out, Laws.one(root, c, w, rq, Fm.Frm{0, fl, sid, pay}),
      C.data.vd(c, w, rq, fl, sid, Bytes.len(pay), pay, C.verdict(C.state(c, sid), C.TData{})),
      unpadded(root, c, w, rq, fl, sid, pay, hb, hz, hp)) :
    {_ == C.rst(c, Bytes.append(w, C.give(0, Bytes.len(pay))), rq, sid, C.e.closed()) : C.Out}
  %Equal.sym(C.Ss, C.state(c, sid), C.SHalf{}, hs) :
    {C.data.vd(c, w, rq, fl, sid, Bytes.len(pay), pay, C.verdict(_, C.TData{})) ==
      C.rst(c, Bytes.append(w, C.give(0, Bytes.len(pay))), rq, sid, C.e.closed()) : C.Out}
  {==}


















def Laws.req_ok():
  {==}

def Laws.req_upper():
  {==}

def Laws.req_unknown_pseudo():
  {==}

def Laws.req_response_pseudo():
  {==}

def Laws.req_pseudo_late():
  {==}

def Laws.req_connection():
  {==}

def Laws.req_te():
  {==}

def Laws.req_empty_path():
  {==}

def Laws.req_no_method():
  {==}

def Laws.req_no_scheme():
  {==}

def Laws.req_no_path():
  {==}

def Laws.req_twice():
  {==}

def Laws.req_clen_disagree():
  {==}

def Laws.req_clen_digits():
  {==}

def Laws.trailers_pseudo():
  {==}

def Laws.trailers_plain():
  {==}

# a HEADERS on an idle stream with an even id: past the padding check,
# its verdict takes it and the id refuses it
def even.pay(+root: H.Ht, +c: C.Cn, +w: Bytes(), +rq: List<&2, C.Req>, +fl: U32, +sid: U32, +pay: Bytes(), +off: Nat,
  +pl: Nat, +prio: Bool, bad: Bool, hs: {C.state(c, sid) == C.SIdle{} : C.Ss},
  he: {U32.is_zero(U32.and(sid, 1)) == True{} : Bool}) ->
  {Laws.dead(C.hdr.pay(root, c, w, rq, fl, sid, pay, off, pl, prio, bad)) == True{} : Bool}:
  match bad:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(C.Ss, C.state(c, sid), C.SIdle{}, hs) :
        {Laws.dead(C.hdr.go(root, c, w, rq, fl, sid, Bytes.slice(pay, off, Nat.sub(Nat.sub(Bytes.len(pay), off), pl)),
          prio && U32.is_eq(C.u31(C.be32(pay, C.on(C.flag(fl, 8), 1n, 0n))), sid), _, C.verdict(_, C.THeaders{})))
          == True{} : Bool}
      %Equal.sym(Bool, U32.is_zero(U32.and(sid, 1)), True{}, he) :
        {Laws.dead(C.hdr.open(root, c, w, rq, fl, sid, Bytes.slice(pay, off, Nat.sub(Nat.sub(Bytes.len(pay), off), pl)),
          prio && U32.is_eq(C.u31(C.be32(pay, C.on(C.flag(fl, 8), 1n, 0n))), sid), C.SIdle{}, _)) == True{} : Bool}
      {==}

def Laws.even_id(root, c, w, rq, fl, sid, pay, hb, hs, hz, he):
  %Equal.sym(C.Blk, C.cn.blk(c), C.BNone{}, hb) :
    {Laws.dead(C.step.blk(root, c, w, rq, _, Fm.Frm{1, fl, sid, pay})) == True{} : Bool}
  %Equal.sym(Bool, U32.is_zero(sid), False{}, hz) :
    {Laws.dead(C.h.headers.go(root, c, w, rq, fl, sid, pay, _)) == True{} : Bool}
  even.pay(root, c, w, rq, fl, sid, pay,
    Nat.add(C.on(C.flag(fl, 8), 1n, 0n), C.on(C.flag(fl, 32), 5n, 0n)),
    C.on(C.flag(fl, 8), U32.to_nat(Bytes.get(pay, 0n)), 0n), C.flag(fl, 32),
    Nat.is_lt(Bytes.len(pay), Nat.add(Nat.add(C.on(C.flag(fl, 8), 1n, 0n), C.on(C.flag(fl, 32), 5n, 0n)),
      C.on(C.flag(fl, 8), U32.to_nat(Bytes.get(pay, 0n)), 0n))), hs, he)

def ids.go(+last: U32, +sid: U32, b: Bool, e: {U32.is_lt(last, sid) == b : Bool}) ->
  {U32.is_le(last, C.last.max(last, sid, b)) == True{} : Bool}:
  match b:
    case True{}:
      cmp_lt_le(U32.cmp(last, sid), e)
    case False{}:
      u32_le_refl(last)

def Laws.ids_grow(last, sid):
  ids.go(last, sid, U32.is_lt(last, sid), {==})

def Laws.cont_only(root, c, w, rq, bsid, end, k, size, ty, fl, sid, pay, hb, hn):
  %Equal.sym(C.Blk, C.cn.blk(c), C.BIn{bsid, end, k, size}, hb) :
    {C.step.blk(root, c, w, rq, _, Fm.Frm{ty, fl, sid, pay}) == C.die(c, w, rq, C.e.proto()) : C.Out}
  %Equal.sym(Bool, Bool.and(U32.is_eq(ty, 9), U32.is_eq(sid, bsid)), False{}, hn) :
    {C.h.cont(root, c, w, rq, fl, pay, C.BIn{bsid, end, k, size}, _) == C.die(c, w, rq, C.e.proto()) : C.Out}
  {==}

def Laws.cont_capped(root, c, w, rq, bsid, end, k, size, fl, pay, hb, hbig):
  %Equal.sym(C.Blk, C.cn.blk(c), C.BIn{bsid, end, k, size}, hb) :
    {C.step.blk(root, c, w, rq, _, Fm.Frm{9, fl, bsid, pay}) == C.die(c, w, rq, C.e.calm()) : C.Out}
  %Equal.sym(Bool, U32.is_eq(bsid, bsid), True{}, u32_eq_refl(bsid)) :
    {C.h.cont(root, c, w, rq, fl, pay, C.BIn{bsid, end, k, size}, _) == C.die(c, w, rq, C.e.calm()) : C.Out}
  %Equal.sym(Bool, Nat.is_lt(C.blk.cap(), Nat.add(size, Bytes.len(pay))), True{}, hbig) :
    {C.blk.more(root, c, w, rq, bsid, end, k, Nat.add(size, Bytes.len(pay)), pay, _, C.flag(fl, 4)) ==
      C.die(c, w, rq, C.e.calm()) : C.Out}
  {==}

# Flow control
# ------------

def wa.fit(-up: Nat, -down: Nat, -n: Nat, w2: C.Sw, ok: Bool,
  eok: {Nat.is_le(C.sw.up(w2), C.win.max()) == ok : Bool},
  fact: {Nat.add(Laws.Sw.val.up(w2), down) == Nat.add(Nat.add(up, n), Laws.Sw.val.down(w2)) : Nat}) ->
  Laws.lands(C.sw.fit(w2, ok), C.Sw{up, down}, n):
  match w2 ok:
    case C.Sw{u2, d2} False{}:
      Unit{}
    case C.Sw{u2, d2} True{}:
      (eok, fact)

def wa(+up: Nat, +down: Nat, +n: Nat, ge: Bool, ege: {Nat.is_le(down, Nat.add(up, n)) == ge : Bool}) ->
  Laws.lands(C.sw.fit(C.sw.norm(Nat.add(up, n), down, ge),
    Nat.is_le(C.sw.up(C.sw.norm(Nat.add(up, n), down, ge)), C.win.max())), C.Sw{up, down}, n):
  match ge:
    case True{}:
      wa.fit(up, down, n, C.Sw{Nat.sub(Nat.add(up, n), down), 0n},
        Nat.is_le(Nat.sub(Nat.add(up, n), down), C.win.max()), {==},
        Equal.trans(Nat, Nat.add(Nat.sub(Nat.add(up, n), down), down), Nat.add(up, n), Nat.add(Nat.add(up, n), 0n),
          N.sub_add(Nat.add(up, n), down, ege), Equal.sym(Nat, Nat.add(Nat.add(up, n), 0n), Nat.add(up, n),
            N.add_0r(Nat.add(up, n)))))
    case False{}:
      wa.fit(up, down, n, C.Sw{0n, Nat.sub(down, Nat.add(up, n))}, Nat.is_le(0n, C.win.max()), {==},
        Equal.sym(Nat, Nat.add(Nat.add(up, n), Nat.sub(down, Nat.add(up, n))), down,
          N.add_sub(Nat.add(up, n), down, N.nle_nlt(down, Nat.add(up, n), ege))))

def Laws.win_add(w, n):
  match w:
    case C.Sw{+up, +down}:
      wa(up, down, n, Nat.is_le(down, Nat.add(up, n)), {==})

def Laws.win_over(u, n, h):
  %Equal.sym(Bool, Nat.is_le(0n, Nat.add(u, n)), True{}, N.le0(Nat.add(u, n))) :
    {C.sw.fit(C.sw.norm(Nat.add(u, n), 0n, _), Nat.is_le(C.sw.up(C.sw.norm(Nat.add(u, n), 0n, _)), C.win.max())) ==
      None{} : Maybe<&2, C.Sw>}
  %Equal.sym(Nat, Nat.sub(Nat.add(u, n), 0n), Nat.add(u, n), N.sub_0r(Nat.add(u, n))) :
    {C.sw.fit(C.Sw{_, 0n}, Nat.is_le(_, C.win.max())) == None{} : Maybe<&2, C.Sw>}
  %Equal.sym(Bool, Nat.is_le(Nat.add(u, n), C.win.max()), False{}, N.lt_nle(C.win.max(), Nat.add(u, n), h)) :
    {C.sw.fit(C.Sw{Nat.add(u, n), 0n}, _) == None{} : Maybe<&2, C.Sw>}
  {==}

def Laws.rw_take(w, n, h):
  %Equal.sym(Bool, Nat.is_le(n, w), True{}, h) : {C.rw.fit(w, n, _) == Some{Nat.sub(w, n)} : Maybe<&2, Nat>}
  {==}

def Laws.rw_refuse(w, n, h):
  %Equal.sym(Bool, Nat.is_le(n, w), False{}, h) : {C.rw.fit(w, n, _) == None{} : Maybe<&2, Nat>}
  {==}

def Laws.data_fits(s, csw, fmax):
  +a = Bytes.len(C.st.out(s))
  +b = C.sw.up(C.st.sw(s))
  +cc = C.sw.up(csw)
  +m3 = Nat.min(cc, fmax)
  +m2 = Nat.min(b, m3)
  and4(Nat.is_le(Nat.min(a, m2), b), Nat.is_le(Nat.min(a, m2), cc), Nat.is_le(Nat.min(a, m2), fmax),
    Nat.is_le(Nat.min(a, m2), a),
    N.le_trans(Nat.min(a, m2), m2, b, N.min_le_r(a, m2), N.min_le_l(b, m3)),
    N.le_trans(Nat.min(a, m2), m2, cc, N.min_le_r(a, m2), N.le_trans(m2, m3, cc, N.min_le_r(b, m3), N.min_le_l(cc, fmax))),
    N.le_trans(Nat.min(a, m2), m2, fmax, N.min_le_r(a, m2), N.le_trans(m2, m3, fmax, N.min_le_r(b, m3),
      N.min_le_r(cc, fmax))),
    N.min_le_l(a, m2))

# Budgets
# -------

def Laws.ping_through(root, c, w, rq, fl, pay, hb, h8, ha):
  %Equal.sym(C.Blk, C.cn.blk(c), C.BNone{}, hb) :
    {C.step.blk(root, c, w, rq, _, Fm.Frm{6, fl, 0, pay}) == C.ping.paid(c, w, rq, pay, C.cn.bud(c)) : C.Out}
  %Equal.sym(Bool, Nat.is_eq(Bytes.len(pay), 8n), True{}, h8) :
    {C.h.ping(c, w, rq, fl, pay, True{}, _) == C.ping.paid(c, w, rq, pay, C.cn.bud(c)) : C.Out}
  %Equal.sym(Bool, C.flag(fl, 1), False{}, ha) :
    {C.ping.ack(c, w, rq, pay, _) == C.ping.paid(c, w, rq, pay, C.cn.bud(c)) : C.Out}
  {==}

def Laws.ping_spent(c, w, rq, pay, s, r):
  {==}

def Laws.ping_pays(c, w, rq, pay, k, s, r):
  {==}

def Laws.bud_capped(b):
  match b:
    case C.Bud{+p, +s, +r}:
      and3(Nat.is_le(C.bud.up(p), C.bud.cap()), Nat.is_le(C.bud.up(s), C.bud.cap()),
        Nat.is_le(C.bud.up(r), C.bud.cap()),
        N.min_le_r(1n+p, C.bud.cap()), N.min_le_r(1n+s, C.bud.cap()), N.min_le_r(1n+r, C.bud.cap()))

# The server
# ==========

def Laws.end_is_last(srv, w, out, hw, g, v):
  WW.end_is_last(~S.Srv, ~C.Cn, ~Unit, ~S.srv.idle, ~S.srv.head, ~S.h.plan, ~L.no.mid(~C.Cn), ~L.no.big(),
    ~L.no.uplan(~C.Cn, ~Unit), ~L.no.gap(), ~L.no.event, ~L.no.shut, ~L.no.fhead, ~L.no.miss,
    ~L.no.lnote, ~L.no.lsize, srv, w, out, hw, g, v)

def Laws.stop_is_last(srv, w, hw, g, v):
  WW.stop_is_last(~S.Srv, ~C.Cn, ~Unit, ~S.srv.idle, ~S.srv.head, ~S.h.plan, ~L.no.mid(~C.Cn), ~L.no.big(),
    ~L.no.uplan(~C.Cn, ~Unit), ~L.no.gap(), ~L.no.event, ~L.no.shut, ~L.no.fhead, ~L.no.miss,
    ~L.no.lnote, ~L.no.lsize, srv, w, hw, g, v)

def Laws.go_order(srv, w, out, c, hw, g, v):
  WW.go_order(~S.Srv, ~C.Cn, ~Unit, ~S.srv.idle, ~S.srv.head, ~S.h.plan, ~L.no.mid(~C.Cn), ~L.no.big(),
    ~L.no.uplan(~C.Cn, ~Unit), ~L.no.gap(), ~L.no.event, ~L.no.shut, ~L.no.fhead, ~L.no.miss,
    ~L.no.lnote, ~L.no.lsize, srv, w, out, c, hw, g, v)

def Laws.fail_go(srv, g, v, m, c, hw, e):
  WW.fail_go(~S.Srv, ~C.Cn, ~Unit, ~S.srv.idle, ~S.srv.head, ~S.h.plan, ~L.no.mid(~C.Cn), ~L.no.big(),
    ~L.no.uplan(~C.Cn, ~Unit), ~L.no.gap(), ~L.no.event, ~L.no.shut, ~L.no.fhead, ~L.no.miss,
    ~L.no.lnote, ~L.no.lsize, srv, g, v, m, c, hw, e)

def Laws.segs_wire(xs, ms, rd, now, fs, out, e):
  WW.segs_wire(~L.no.shut, ~L.no.fhead, ~L.no.miss, ~L.no.lnote, ~L.no.lsize, xs, ms, rd, now, fs, out, e)

def Laws.stall_ends(srv, w, pl, hw, g, v):
  WW.stall_ends(~S.Srv, ~C.Cn, ~Unit, ~S.srv.idle, ~S.srv.head, ~S.h.plan, ~L.no.mid(~C.Cn), ~L.no.big(),
    ~L.no.uplan(~C.Cn, ~Unit), ~L.no.gap(), ~L.no.event, ~L.no.shut, ~L.no.fhead, ~L.no.miss,
    ~L.no.lnote, ~L.no.lsize, ~WW.no.event_ok, srv, w, pl, hw, g, v)

# a connection over plans its end, whatever its answers and its flush
def ends.cw(cw: C.CW) -> {Laws.ends(S.plan.cw(cw, True{})) == True{} : Bool}:
  match cw:
    case C.CW{c, SNil{}}:
      {==}
    case C.CW{c, SCon{h, t}}:
      {==}

def ends.flush(cw: C.CW) -> {Laws.ends(S.plan.flush(cw, True{})) == True{} : Bool}:
  match cw:
    case C.CW{+c, w}:
      ends.cw(C.flush(c, w))

def Laws.dead_ends(srv, c, w, rq):
  ends.flush(S.answer.all(srv, List.reverse(&2, C.Req, rq), C.CW{c, w}))
