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
