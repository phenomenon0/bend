# The proofs of LAWS.bend. The heart is resp_sim, a simulation between
# the reader's byte machine and the spec's line-at-a-time walk (below,
# "The reader is the framing"); the rest are the kit's laws at the
# reader's hooks, and the vectors, which compute.
import Base
import ../reader.bend as Wr
import ./resp.bend as R
import ./spec.bend as S
import ./LAWS.bend as Laws

# Tools
# =====

def BD(b: Bool, tc: Type, fc: Type) -> Type:
  match b:
    case True{}:
      tc
    case False{}:
      fc

def no(-g: Type, e: {False{} == True{} : Bool}) -> g:
  %e : BD(_, g, Unit)
  Unit{}

def no2(-g: Type, e: {True{} == False{} : Bool}) -> g:
  %e : BD(_, Unit, g)
  Unit{}

# Byte lists
# ==========

def Cand() -> Data:
  Maybe<&2, List<&2, U32>>

def keep(b: Bool, m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match b:
    case True{}:
      m
    case False{}:
      None{}

# what is left of lit once xs is cut from its front, if xs is its front
def strip(xs: List<&2, U32>, lit: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match xs lit:
    case Nil{} l:
      Some{l}
    case Con{x, t} Nil{}:
      None{}
    case Con{x, t} Con{y, u}:
      keep(U32.is_eq(x, y), strip(t, u))

def keep_pick(b: Bool, -u: List<&2, U32>) -> {keep(b, Some{u}) == R.cand.pick(b, u) : Cand()}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def keep_cstep(b: Bool, -m: Cand(), -c: U32) -> {keep(b, R.cstep(m, c)) == R.cstep(keep(b, m), c) : Cand()}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def strip_snoc(acc: List<&2, U32>, +c: U32, l: List<&2, U32>) ->
  {strip(S.snoc(acc, c), l) == R.cstep(strip(acc, l), c) : Cand()}:
  match acc l:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, u}:
      keep_pick(U32.is_eq(c, y), u)
    case Con{x, t} Nil{}:
      {==}
    case Con{+x, t} Con{+y, u}:
      Equal.trans(Cand(), keep(U32.is_eq(x, y), strip(S.snoc(t, c), u)),
        keep(U32.is_eq(x, y), R.cstep(strip(t, u), c)), R.cstep(keep(U32.is_eq(x, y), strip(t, u)), c),
        Equal.cong(Cand(), Cand(), m => keep(U32.is_eq(x, y), m), strip(S.snoc(t, c), u),
          R.cstep(strip(t, u), c), strip_snoc(t, c, u)),
        keep_cstep(U32.is_eq(x, y), strip(t, u), c))

def done_keep(b: Bool, -m: Cand(), -x: Bool, e: {R.done(m) == x : Bool}) ->
  {R.done(keep(b, m)) == (b && x) : Bool}:
  match b:
    case True{}:
      e
    case False{}:
      {==}

def done_leq(a: List<&2, U32>, l: List<&2, U32>) -> {R.done(strip(a, l)) == S.leq(a, l) : Bool}:
  match a l:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, u}:
      {==}
    case Con{x, t} Nil{}:
      {==}
    case Con{+x, t} Con{+y, u}:
      done_keep(U32.is_eq(x, y), strip(t, u), S.leq(t, u), done_leq(t, u))

def lows_snoc(xs: List<&2, U32>, -c: U32) -> {S.lows(S.snoc(xs, c)) == S.snoc(S.lows(xs), R.lower(c)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      Equal.cong(List<&2, U32>, List<&2, U32>, y => Con{R.lower(x), y}, S.lows(S.snoc(t, c)),
        S.snoc(S.lows(t), R.lower(c)), lows_snoc(t, c))

def cnt_snoc(xs: List<&2, U32>, -c: U32) -> {S.cnt(S.snoc(xs, c)) == 1n+S.cnt(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      Equal.cong(Nat, Nat, y => 1n+y, S.cnt(S.snoc(t, c)), 1n+S.cnt(t), cnt_snoc(t, c))

def num_snoc(xs: List<&2, U32>, -c: U32, a: U32) ->
  {S.num.go(S.snoc(xs, c), a) == (S.num.go(xs, a) * 10 + (c - 48) : U32) : U32}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      num_snoc(t, c, (a * 10 + (x - 48) : U32))

def len_snoc(+e: R.Ask, xs: List<&2, U32>, -c: U32, +a: U32) ->
  {S.len.num.go(e, S.snoc(xs, c), a) == R.len.dig(e, S.len.num.go(e, xs, a), c) : U32}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      len_snoc(e, t, c, Bool.pick(U32, U32.is_lt(R.ask.cap(e), a), a, (a * 10 + (x - 48) : U32)))

def app_snoc(acc: List<&2, U32>, -c: U32, -r: List<&2, U32>) ->
  {List.append(&2, U32, S.snoc(acc, c), r) == List.append(&2, U32, acc, Con{c, r}) : List<&2, U32>}:
  match acc:
    case Nil{}:
      {==}
    case Con{x, t}:
      Equal.cong(List<&2, U32>, List<&2, U32>, y => Con{x, y},
        List.append(&2, U32, S.snoc(t, c), r), List.append(&2, U32, t, Con{c, r}), app_snoc(t, c, r))

def fl_snoc(xs: List<&2, U32>, -c: U32) ->
  {Bytes.from_list(S.snoc(xs, c)) == Bytes.push(Bytes.from_list(xs), c) : Bytes()}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      Equal.cong(Bytes(), Bytes(), y => SCon{Chr{x}, y}, Bytes.from_list(S.snoc(t, c)),
        Bytes.push(Bytes.from_list(t), c), fl_snoc(t, c))

# The reader's walk
# =================

def feed_snoc(+e: R.Ask, xs: List<&2, U32>, +c: U32, p: R.P) ->
  {R.feed(e, S.snoc(xs, c), p) == R.step(e, R.feed(e, xs, p), c) : R.P}:
  Wr.feed_split(~R.Ask, ~R.P, ~R.wstep, e, xs, [c], p)

def bad_feed(+e: R.Ask, xs: List<&2, U32>, -out: List<&2, U32>) ->
  {R.feed(e, xs, R.P{R.Bad{}, out}) == R.P{R.Bad{}, out} : R.P}:
  match xs:
    case Nil{}:
      {==}
    case Con{c, t}:
      bad_feed(e, t, out)


# Lines
# =====

def notcrlf(k: R.Cls) -> Bool:
  match k:
    case R.KCr{}:
      False{}
    case R.KLf{}:
      False{}
    case _:
      True{}

# a line holds no CR and no LF: they end it
def Plain(xs: List<&2, U32>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{c, t}:
      {notcrlf(R.cls(c)) == True{} : Bool} & Plain(t)

def plain.snoc.con(-x: U32, -t: List<&2, U32>, -c: U32,
  pl: {notcrlf(R.cls(x)) == True{} : Bool} & Plain(t), ih: Plain(t) -> Plain(S.snoc(t, c))) ->
  {notcrlf(R.cls(x)) == True{} : Bool} & Plain(S.snoc(t, c)):
  (a, b) = pl
  (a, ih(b))

def plain.snoc(xs: List<&2, U32>, -c: U32, nc: {notcrlf(R.cls(c)) == True{} : Bool}) ->
  Plain(xs) -> Plain(S.snoc(xs, c)):
  match xs:
    case Nil{}:
      pl => (nc, Unit{})
    case Con{x, t}:
      pl => plain.snoc.con(x, t, c, pl, plain.snoc(t, c, nc))

def plain.dup.two(-t: List<&2, U32>, -x: Bool, +nc: {x == True{} : Bool}, ab: Plain(t) & Plain(t)) ->
  ({x == True{} : Bool} & Plain(t)) & ({x == True{} : Bool} & Plain(t)):
  (a, b) = ab
  ((nc, a), (nc, b))

def plain.dup.con(-c: U32, -t: List<&2, U32>, pl: {notcrlf(R.cls(c)) == True{} : Bool} & Plain(t),
  ih: Plain(t) -> Plain(t) & Plain(t)) ->
  ({notcrlf(R.cls(c)) == True{} : Bool} & Plain(t)) & ({notcrlf(R.cls(c)) == True{} : Bool} & Plain(t)):
  (+nc, pt) = pl
  plain.dup.two(t, notcrlf(R.cls(c)), nc, ih(pt))

def plain.dup(xs: List<&2, U32>) -> Plain(xs) -> Plain(xs) & Plain(xs):
  match xs:
    case Nil{}:
      pl => (Unit{}, Unit{})
    case Con{c, t}:
      pl => plain.dup.con(c, t, pl, plain.dup(t))

def app_nil(xs: List<&2, U32>) -> {List.append(&2, U32, xs, Nil{}) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      Equal.cong(List<&2, U32>, List<&2, U32>, y => Con{x, y}, List.append(&2, U32, t, Nil{}), t,
        app_nil(t))

def leq_done(+a: List<&2, U32>, +l: List<&2, U32>) -> {S.leq(a, l) == R.done(strip(a, l)) : Bool}:
  Equal.sym(Bool, R.done(strip(a, l)), S.leq(a, l), done_leq(a, l))

def strip_lows_snoc(+acc: List<&2, U32>, +c: U32, +l: List<&2, U32>) ->
  {strip(S.lows(S.snoc(acc, c)), l) == R.cstep(strip(S.lows(acc), l), R.lower(c)) : Cand()}:
  Equal.trans(Cand(), strip(S.lows(S.snoc(acc, c)), l), strip(S.snoc(S.lows(acc), R.lower(c)), l),
    R.cstep(strip(S.lows(acc), l), R.lower(c)),
    Equal.cong(List<&2, U32>, Cand(), x => strip(x, l), S.lows(S.snoc(acc, c)),
      S.snoc(S.lows(acc), R.lower(c)), lows_snoc(acc, c)),
    strip_snoc(S.lows(acc), R.lower(c), l))

# one byte against a literal, as the reader and as strip see it
def cand1(+c: U32, l: List<&2, U32>) -> {strip([c], l) == R.cstep(Some{l}, c) : Cand()}:
  match l:
    case Nil{}:
      {==}
    case Con{+y, u}:
      keep_pick(U32.is_eq(c, y), u)

# A token's run, stepped
# ----------------------
#
# Where the reader is inside each run a line is split into, given the
# run so far (acc): the version against its two literals, the code as a
# number and a count, a name against its three, a length as its
# digits read, a coding against chunked; the rest hold nothing of it.
type Sel is Data:
  SlVer{}
  SlCode{v10: Bool}
  SlWhy{v10: Bool, code: U32}
  SlName{h: R.Head}
  SlOth{h: R.Head}
  SlLen0{h: R.Head}
  SlLen{h: R.Head}
  SlLenW{h: R.Head, n: U32}
  SlTe0{h: R.Head}
  SlTe{h: R.Head}

def tokof(s: Sel) -> S.Tok:
  match s:
    case SlVer{}:
      S.TVer{}
    case SlCode{v10}:
      S.TDig{}
    case SlWhy{v10, code}:
      S.TVal{}
    case SlName{h}:
      S.TName{}
    case SlOth{h}:
      S.TVal{}
    case SlLen0{h}:
      S.TOws{}
    case SlLen{h}:
      S.TDig{}
    case SlLenW{h, n}:
      S.TOws{}
    case SlTe0{h}:
      S.TOws{}
    case SlTe{h}:
      S.TVal{}

def put(+e: R.Ask, s: Sel, +acc: List<&2, U32>) -> R.St:
  match s:
    case SlVer{}:
      R.SVer{strip(acc, R.lit.v11()), strip(acc, R.lit.v10())}
    case SlCode{v10}:
      R.SCode{v10, S.num(acc), S.cnt(acc)}
    case SlWhy{v10, code}:
      R.SWhy{v10, code}
    case SlName{h}:
      R.Nam{h, strip(S.lows(acc), R.lit.cl()), strip(S.lows(acc), R.lit.te()),
        strip(S.lows(acc), R.lit.co())}
    case SlOth{h}:
      R.Oth{h}
    case SlLen0{h}:
      R.Len0{h}
    case SlLen{h}:
      R.Len{h, S.len.num(e, acc)}
    case SlLenW{h, n}:
      R.LenW{h, n}
    case SlTe0{h}:
      R.Te0{h}
    case SlTe{h}:
      R.Te{h, strip(S.lows(acc), R.lit.chunked())}

# a byte a token holds is one the reader stays on, adding it
def SS(+e: R.Ask, -s: Sel, -k: R.Cls, -c: U32, -acc: List<&2, U32>, -out: List<&2, U32>) -> Type:
  {R.P{put(e, s, S.snoc(acc, c)), out} == R.step.at(e, put(e, s, acc), k, c, out) : R.P}

def stay.ver(+e: R.Ask, +acc: List<&2, U32>, +c: U32, -out: List<&2, U32>) -> SS(e, SlVer{}, R.KTk{}, c, acc, out):
  %strip_snoc(acc, c, R.lit.v11()) :
    {R.P{R.SVer{strip(S.snoc(acc, c), R.lit.v11()), strip(S.snoc(acc, c), R.lit.v10())}, out} ==
      R.P{R.SVer{_, R.cstep(strip(acc, R.lit.v10()), c)}, out} : R.P}
  %strip_snoc(acc, c, R.lit.v10()) :
    {R.P{R.SVer{strip(S.snoc(acc, c), R.lit.v11()), strip(S.snoc(acc, c), R.lit.v10())}, out} ==
      R.P{R.SVer{strip(S.snoc(acc, c), R.lit.v11()), _}, out} : R.P}
  {==}


def stay.code(+e: R.Ask, +v10: Bool, +acc: List<&2, U32>, +c: U32, -out: List<&2, U32>) ->
  SS(e, SlCode{v10}, R.KDg{}, c, acc, out):
  %num_snoc(acc, c, 0) :
    {R.P{R.SCode{v10, S.num(S.snoc(acc, c)), S.cnt(S.snoc(acc, c))}, out} ==
      R.P{R.SCode{v10, _, 1n+S.cnt(acc)}, out} : R.P}
  %cnt_snoc(acc, c) :
    {R.P{R.SCode{v10, S.num(S.snoc(acc, c)), S.cnt(S.snoc(acc, c))}, out} ==
      R.P{R.SCode{v10, S.num(S.snoc(acc, c)), _}, out} : R.P}
  {==}

def stay.name(+e: R.Ask, +h: R.Head, +acc: List<&2, U32>, +c: U32, -out: List<&2, U32>) ->
  SS(e, SlName{h}, R.KTk{}, c, acc, out):
  %strip_lows_snoc(acc, c, R.lit.cl()) :
    {R.P{R.Nam{h, strip(S.lows(S.snoc(acc, c)), R.lit.cl()), strip(S.lows(S.snoc(acc, c)), R.lit.te()),
      strip(S.lows(S.snoc(acc, c)), R.lit.co())}, out} ==
      R.P{R.Nam{h, _, R.cstep(strip(S.lows(acc), R.lit.te()), R.lower(c)),
        R.cstep(strip(S.lows(acc), R.lit.co()), R.lower(c))}, out} : R.P}
  %strip_lows_snoc(acc, c, R.lit.te()) :
    {R.P{R.Nam{h, strip(S.lows(S.snoc(acc, c)), R.lit.cl()), strip(S.lows(S.snoc(acc, c)), R.lit.te()),
      strip(S.lows(S.snoc(acc, c)), R.lit.co())}, out} ==
      R.P{R.Nam{h, strip(S.lows(S.snoc(acc, c)), R.lit.cl()), _,
        R.cstep(strip(S.lows(acc), R.lit.co()), R.lower(c))}, out} : R.P}
  %strip_lows_snoc(acc, c, R.lit.co()) :
    {R.P{R.Nam{h, strip(S.lows(S.snoc(acc, c)), R.lit.cl()), strip(S.lows(S.snoc(acc, c)), R.lit.te()),
      strip(S.lows(S.snoc(acc, c)), R.lit.co())}, out} ==
      R.P{R.Nam{h, strip(S.lows(S.snoc(acc, c)), R.lit.cl()), strip(S.lows(S.snoc(acc, c)), R.lit.te()),
        _}, out} : R.P}
  {==}

def stay.len(+e: R.Ask, +h: R.Head, +acc: List<&2, U32>, +c: U32, -out: List<&2, U32>) ->
  SS(e, SlLen{h}, R.KDg{}, c, acc, out):
  %len_snoc(e, acc, c, 0) :
    {R.P{R.Len{h, S.len.num(e, S.snoc(acc, c))}, out} == R.P{R.Len{h, _}, out} : R.P}
  {==}

def stay.te(+e: R.Ask, +h: R.Head, +acc: List<&2, U32>, +c: U32, -out: List<&2, U32>) ->
  SS(e, SlTe{h}, R.KTk{}, c, acc, out):
  %strip_lows_snoc(acc, c, R.lit.chunked()) :
    {R.P{R.Te{h, strip(S.lows(S.snoc(acc, c)), R.lit.chunked())}, out} == R.P{R.Te{h, _}, out} : R.P}
  {==}


def stay(+e: R.Ask, s: Sel, k: R.Cls, +c: U32, +acc: List<&2, U32>, +out: List<&2, U32>) ->
  {S.allows(tokof(s), k) == True{} : Bool} -> SS(e, s, k, c, acc, out):
  match s k:
    case SlVer{} R.KSp{}:
      x => no(SS(e, SlVer{}, R.KSp{}, c, acc, out), x)
    case SlVer{} R.KHt{}:
      x => stay.ver(e, acc, c, out)
    case SlVer{} R.KCr{}:
      x => no(SS(e, SlVer{}, R.KCr{}, c, acc, out), x)
    case SlVer{} R.KLf{}:
      x => no(SS(e, SlVer{}, R.KLf{}, c, acc, out), x)
    case SlVer{} R.KCo{}:
      x => stay.ver(e, acc, c, out)
    case SlVer{} R.KCm{}:
      x => stay.ver(e, acc, c, out)
    case SlVer{} R.KDg{}:
      x => stay.ver(e, acc, c, out)
    case SlVer{} R.KTk{}:
      x => stay.ver(e, acc, c, out)
    case SlVer{} R.KVc{}:
      x => stay.ver(e, acc, c, out)
    case SlVer{} R.KCt{}:
      x => stay.ver(e, acc, c, out)
    case SlCode{v10} R.KSp{}:
      x => no(SS(e, SlCode{v10}, R.KSp{}, c, acc, out), x)
    case SlCode{v10} R.KHt{}:
      x => no(SS(e, SlCode{v10}, R.KHt{}, c, acc, out), x)
    case SlCode{v10} R.KCr{}:
      x => no(SS(e, SlCode{v10}, R.KCr{}, c, acc, out), x)
    case SlCode{v10} R.KLf{}:
      x => no(SS(e, SlCode{v10}, R.KLf{}, c, acc, out), x)
    case SlCode{v10} R.KCo{}:
      x => no(SS(e, SlCode{v10}, R.KCo{}, c, acc, out), x)
    case SlCode{v10} R.KCm{}:
      x => no(SS(e, SlCode{v10}, R.KCm{}, c, acc, out), x)
    case SlCode{v10} R.KDg{}:
      x => stay.code(e, v10, acc, c, out)
    case SlCode{v10} R.KTk{}:
      x => no(SS(e, SlCode{v10}, R.KTk{}, c, acc, out), x)
    case SlCode{v10} R.KVc{}:
      x => no(SS(e, SlCode{v10}, R.KVc{}, c, acc, out), x)
    case SlCode{v10} R.KCt{}:
      x => no(SS(e, SlCode{v10}, R.KCt{}, c, acc, out), x)
    case SlWhy{v10, code} R.KSp{}:
      x => {==}
    case SlWhy{v10, code} R.KHt{}:
      x => {==}
    case SlWhy{v10, code} R.KCr{}:
      x => no(SS(e, SlWhy{v10, code}, R.KCr{}, c, acc, out), x)
    case SlWhy{v10, code} R.KLf{}:
      x => no(SS(e, SlWhy{v10, code}, R.KLf{}, c, acc, out), x)
    case SlWhy{v10, code} R.KCo{}:
      x => {==}
    case SlWhy{v10, code} R.KCm{}:
      x => {==}
    case SlWhy{v10, code} R.KDg{}:
      x => {==}
    case SlWhy{v10, code} R.KTk{}:
      x => {==}
    case SlWhy{v10, code} R.KVc{}:
      x => {==}
    case SlWhy{v10, code} R.KCt{}:
      x => no(SS(e, SlWhy{v10, code}, R.KCt{}, c, acc, out), x)
    case SlName{h} R.KSp{}:
      x => no(SS(e, SlName{h}, R.KSp{}, c, acc, out), x)
    case SlName{h} R.KHt{}:
      x => no(SS(e, SlName{h}, R.KHt{}, c, acc, out), x)
    case SlName{h} R.KCr{}:
      x => no(SS(e, SlName{h}, R.KCr{}, c, acc, out), x)
    case SlName{h} R.KLf{}:
      x => no(SS(e, SlName{h}, R.KLf{}, c, acc, out), x)
    case SlName{h} R.KCo{}:
      x => no(SS(e, SlName{h}, R.KCo{}, c, acc, out), x)
    case SlName{h} R.KCm{}:
      x => no(SS(e, SlName{h}, R.KCm{}, c, acc, out), x)
    case SlName{h} R.KDg{}:
      x => stay.name(e, h, acc, c, out)
    case SlName{h} R.KTk{}:
      x => stay.name(e, h, acc, c, out)
    case SlName{h} R.KVc{}:
      x => no(SS(e, SlName{h}, R.KVc{}, c, acc, out), x)
    case SlName{h} R.KCt{}:
      x => no(SS(e, SlName{h}, R.KCt{}, c, acc, out), x)
    case SlOth{h} R.KSp{}:
      x => {==}
    case SlOth{h} R.KHt{}:
      x => {==}
    case SlOth{h} R.KCr{}:
      x => no(SS(e, SlOth{h}, R.KCr{}, c, acc, out), x)
    case SlOth{h} R.KLf{}:
      x => no(SS(e, SlOth{h}, R.KLf{}, c, acc, out), x)
    case SlOth{h} R.KCo{}:
      x => {==}
    case SlOth{h} R.KCm{}:
      x => {==}
    case SlOth{h} R.KDg{}:
      x => {==}
    case SlOth{h} R.KTk{}:
      x => {==}
    case SlOth{h} R.KVc{}:
      x => {==}
    case SlOth{h} R.KCt{}:
      x => no(SS(e, SlOth{h}, R.KCt{}, c, acc, out), x)
    case SlLen0{h} R.KSp{}:
      x => {==}
    case SlLen0{h} R.KHt{}:
      x => {==}
    case SlLen0{h} R.KCr{}:
      x => no(SS(e, SlLen0{h}, R.KCr{}, c, acc, out), x)
    case SlLen0{h} R.KLf{}:
      x => no(SS(e, SlLen0{h}, R.KLf{}, c, acc, out), x)
    case SlLen0{h} R.KCo{}:
      x => no(SS(e, SlLen0{h}, R.KCo{}, c, acc, out), x)
    case SlLen0{h} R.KCm{}:
      x => no(SS(e, SlLen0{h}, R.KCm{}, c, acc, out), x)
    case SlLen0{h} R.KDg{}:
      x => no(SS(e, SlLen0{h}, R.KDg{}, c, acc, out), x)
    case SlLen0{h} R.KTk{}:
      x => no(SS(e, SlLen0{h}, R.KTk{}, c, acc, out), x)
    case SlLen0{h} R.KVc{}:
      x => no(SS(e, SlLen0{h}, R.KVc{}, c, acc, out), x)
    case SlLen0{h} R.KCt{}:
      x => no(SS(e, SlLen0{h}, R.KCt{}, c, acc, out), x)
    case SlLen{h} R.KSp{}:
      x => no(SS(e, SlLen{h}, R.KSp{}, c, acc, out), x)
    case SlLen{h} R.KHt{}:
      x => no(SS(e, SlLen{h}, R.KHt{}, c, acc, out), x)
    case SlLen{h} R.KCr{}:
      x => no(SS(e, SlLen{h}, R.KCr{}, c, acc, out), x)
    case SlLen{h} R.KLf{}:
      x => no(SS(e, SlLen{h}, R.KLf{}, c, acc, out), x)
    case SlLen{h} R.KCo{}:
      x => no(SS(e, SlLen{h}, R.KCo{}, c, acc, out), x)
    case SlLen{h} R.KCm{}:
      x => no(SS(e, SlLen{h}, R.KCm{}, c, acc, out), x)
    case SlLen{h} R.KDg{}:
      x => stay.len(e, h, acc, c, out)
    case SlLen{h} R.KTk{}:
      x => no(SS(e, SlLen{h}, R.KTk{}, c, acc, out), x)
    case SlLen{h} R.KVc{}:
      x => no(SS(e, SlLen{h}, R.KVc{}, c, acc, out), x)
    case SlLen{h} R.KCt{}:
      x => no(SS(e, SlLen{h}, R.KCt{}, c, acc, out), x)
    case SlLenW{h, n} R.KSp{}:
      x => {==}
    case SlLenW{h, n} R.KHt{}:
      x => {==}
    case SlLenW{h, n} R.KCr{}:
      x => no(SS(e, SlLenW{h, n}, R.KCr{}, c, acc, out), x)
    case SlLenW{h, n} R.KLf{}:
      x => no(SS(e, SlLenW{h, n}, R.KLf{}, c, acc, out), x)
    case SlLenW{h, n} R.KCo{}:
      x => no(SS(e, SlLenW{h, n}, R.KCo{}, c, acc, out), x)
    case SlLenW{h, n} R.KCm{}:
      x => no(SS(e, SlLenW{h, n}, R.KCm{}, c, acc, out), x)
    case SlLenW{h, n} R.KDg{}:
      x => no(SS(e, SlLenW{h, n}, R.KDg{}, c, acc, out), x)
    case SlLenW{h, n} R.KTk{}:
      x => no(SS(e, SlLenW{h, n}, R.KTk{}, c, acc, out), x)
    case SlLenW{h, n} R.KVc{}:
      x => no(SS(e, SlLenW{h, n}, R.KVc{}, c, acc, out), x)
    case SlLenW{h, n} R.KCt{}:
      x => no(SS(e, SlLenW{h, n}, R.KCt{}, c, acc, out), x)
    case SlTe0{h} R.KSp{}:
      x => {==}
    case SlTe0{h} R.KHt{}:
      x => {==}
    case SlTe0{h} R.KCr{}:
      x => no(SS(e, SlTe0{h}, R.KCr{}, c, acc, out), x)
    case SlTe0{h} R.KLf{}:
      x => no(SS(e, SlTe0{h}, R.KLf{}, c, acc, out), x)
    case SlTe0{h} R.KCo{}:
      x => no(SS(e, SlTe0{h}, R.KCo{}, c, acc, out), x)
    case SlTe0{h} R.KCm{}:
      x => no(SS(e, SlTe0{h}, R.KCm{}, c, acc, out), x)
    case SlTe0{h} R.KDg{}:
      x => no(SS(e, SlTe0{h}, R.KDg{}, c, acc, out), x)
    case SlTe0{h} R.KTk{}:
      x => no(SS(e, SlTe0{h}, R.KTk{}, c, acc, out), x)
    case SlTe0{h} R.KVc{}:
      x => no(SS(e, SlTe0{h}, R.KVc{}, c, acc, out), x)
    case SlTe0{h} R.KCt{}:
      x => no(SS(e, SlTe0{h}, R.KCt{}, c, acc, out), x)
    case SlTe{h} R.KSp{}:
      x => stay.te(e, h, acc, c, out)
    case SlTe{h} R.KHt{}:
      x => stay.te(e, h, acc, c, out)
    case SlTe{h} R.KCr{}:
      x => no(SS(e, SlTe{h}, R.KCr{}, c, acc, out), x)
    case SlTe{h} R.KLf{}:
      x => no(SS(e, SlTe{h}, R.KLf{}, c, acc, out), x)
    case SlTe{h} R.KCo{}:
      x => stay.te(e, h, acc, c, out)
    case SlTe{h} R.KCm{}:
      x => stay.te(e, h, acc, c, out)
    case SlTe{h} R.KDg{}:
      x => stay.te(e, h, acc, c, out)
    case SlTe{h} R.KTk{}:
      x => stay.te(e, h, acc, c, out)
    case SlTe{h} R.KVc{}:
      x => stay.te(e, h, acc, c, out)
    case SlTe{h} R.KCt{}:
      x => no(SS(e, SlTe{h}, R.KCt{}, c, acc, out), x)


# where the reader is after the run a span took: the run's state with
# the run added, and, when a byte stopped it, that byte stepped and what
# follows it walked
def RES.at(+e: R.Ask, stop: S.Stop, s: Sel, a: List<&2, U32>, out: List<&2, U32>) -> R.P:
  match stop:
    case S.SEnd{}:
      R.P{put(e, s, a), out}
    case S.SAt{k, c, rest}:
      R.feed(e, rest, R.step.at(e, put(e, s, a), k, c, out))

def RES(+e: R.Ask, sp: S.Span, s: Sel, acc: List<&2, U32>, out: List<&2, U32>) -> R.P:
  match sp:
    case S.Span{run, stop}:
      RES.at(e, stop, s, List.append(&2, U32, acc, run), out)

def respush(+e: R.Ask, -c: U32, sp: S.Span, -s: Sel, +acc: List<&2, U32>, -out: List<&2, U32>) ->
  {RES(e, sp, s, S.snoc(acc, c), out) == RES(e, S.span.push(c, sp), s, acc, out) : R.P}:
  match sp:
    case S.Span{r, st}:
      %app_snoc(acc, c, r) :
        {RES.at(e, st, s, List.append(&2, U32, S.snoc(acc, c), r), out) == RES.at(e, st, s, _, out) : R.P}
      {==}

def RSG(+e: R.Ask, -x: List<&2, U32>, -s: Sel, -acc: List<&2, U32>, -out: List<&2, U32>) -> Type:
  {RES(e, S.span(tokof(s), x), s, acc, out) == R.feed(e, x, R.P{put(e, s, acc), out}) : R.P}

def RS.ok(+e: R.Ask, +s: Sel, +k: R.Cls, +c: U32, +t: List<&2, U32>, +acc: List<&2, U32>,
  +out: List<&2, U32>, ok: Bool, ih: RSG(e, t, s, S.snoc(acc, c), out)) ->
  {S.allows(tokof(s), k) == ok : Bool} ->
  {RES(e, S.span.pick(ok, k, c, t, S.span(tokof(s), t)), s, acc, out) ==
    R.feed(e, t, R.step.at(e, put(e, s, acc), k, c, out)) : R.P}:
  match ok:
    case True{}:
      x =>
        %stay(e, s, k, c, acc, out)(x) :
          {RES(e, S.span.push(c, S.span(tokof(s), t)), s, acc, out) == R.feed(e, t, _) : R.P}
        %respush(e, c, S.span(tokof(s), t), s, acc, out) :
          {_ == R.feed(e, t, R.P{put(e, s, S.snoc(acc, c)), out}) : R.P}
        ih
    case False{}:
      x =>
        %Equal.sym(List<&2, U32>, List.append(&2, U32, acc, Nil{}), acc, app_nil(acc)) :
          {R.feed(e, t, R.step.at(e, put(e, s, _), k, c, out)) ==
            R.feed(e, t, R.step.at(e, put(e, s, acc), k, c, out)) : R.P}
        {==}

# a span, stepped: the reader walks the run a byte at a time, staying
# on it, and steps the byte that stopped it
def RS(+e: R.Ask, x: List<&2, U32>, +s: Sel, +acc: List<&2, U32>, +out: List<&2, U32>) ->
  RSG(e, x, s, acc, out):
  match x:
    case Nil{}:
      %Equal.sym(List<&2, U32>, List.append(&2, U32, acc, Nil{}), acc, app_nil(acc)) :
        {R.P{put(e, s, _), out} == R.P{put(e, s, acc), out} : R.P}
      {==}
    case Con{+c, +t}:
      RS.ok(e, s, R.cls(c), c, t, acc, out, S.allows(tokof(s), R.cls(c)),
        RS(e, t, s, S.snoc(acc, c), out))({==})

# what a span stopped at: a byte its token does not hold, and, in a
# line, no CR or LF, with the rest of the line after it
def SW.at(-t: S.Tok, stop: S.Stop) -> Type:
  match stop:
    case S.SEnd{}:
      Unit
    case S.SAt{+k, c, rest}:
      {S.allows(t, k) == False{} : Bool} & ({notcrlf(k) == True{} : Bool} & Plain(rest))

def SW(-t: S.Tok, sp: S.Span) -> Type:
  match sp:
    case S.Span{r, stop}:
      SW.at(t, stop)

def sw.push(-t: S.Tok, -c: U32, sp: S.Span) -> SW(t, sp) -> SW(t, S.span.push(c, sp)):
  match sp:
    case S.Span{r, stop}:
      h => h

def span.sw.ok(+t: S.Tok, +c: U32, +u: List<&2, U32>, ok: Bool,
  ih: Plain(u) -> SW(t, S.span(t, u))) ->
  {S.allows(t, R.cls(c)) == ok : Bool} -> {notcrlf(R.cls(c)) == True{} : Bool} -> Plain(u) ->
  SW(t, S.span.pick(ok, R.cls(c), c, u, S.span(t, u))):
  match ok:
    case True{}:
      x => nc => pu => sw.push(t, c, S.span(t, u))(ih(pu))
    case False{}:
      x => nc => pu => (x, (nc, pu))

def span.sw.con(+t: S.Tok, +c: U32, +u: List<&2, U32>,
  pl: {notcrlf(R.cls(c)) == True{} : Bool} & Plain(u), ih: Plain(u) -> SW(t, S.span(t, u))) ->
  SW(t, S.span(t, Con{c, u})):
  (nc, pu) = pl
  span.sw.ok(t, c, u, S.allows(t, R.cls(c)), ih)({==})(nc)(pu)

def span.sw(+t: S.Tok, x: List<&2, U32>) -> Plain(x) -> SW(t, S.span(t, x)):
  match x:
    case Nil{}:
      pl => Unit{}
    case Con{+c, +u}:
      pl => span.sw.con(t, c, u, pl, span.sw(t, u))


# The status line, seen
# ---------------------
#
# The reader's state after as much of a status line as has come is fixed
# by the spec's view of that much: a version against its two literals,
# a code as its number and count, a reason -- or refused.

def Rs(v: S.SView) -> R.St:
  match v:
    case S.VVer{+x}:
      R.SVer{strip(x, R.lit.v11()), strip(x, R.lit.v10())}
    case S.VCode{v10, +d}:
      R.SCode{v10, S.num(d), S.cnt(d)}
    case S.VWhy{v10, code}:
      R.SWhy{v10, code}
    case S.VBad{}:
      R.Bad{}

# the reason
def G.why(+e: R.Ask, k: R.Cls, c: U32, rest: List<&2, U32>, v10: Bool, code: U32, out: List<&2, U32>) -> Type:
  {R.feed(e, rest, R.step.at(e, R.SWhy{v10, code}, k, c, out)) == R.P{R.Bad{}, out} : R.P}

def K.why.k(+e: R.Ask, k: R.Cls, +c: U32, +rest: List<&2, U32>, +v10: Bool, +code: U32, +out: List<&2, U32>,
  mx: {S.allows(S.TVal{}, k) == False{} : Bool}, nc: {notcrlf(k) == True{} : Bool}) ->
  G.why(e, k, c, rest, v10, code, out):
  match k:
    case R.KCt{}:
      bad_feed(e, rest, out)
    case R.KCr{}:
      no(G.why(e, R.KCr{}, c, rest, v10, code, out), nc)
    case R.KLf{}:
      no(G.why(e, R.KLf{}, c, rest, v10, code, out), nc)
    case R.KSp{}:
      no2(G.why(e, R.KSp{}, c, rest, v10, code, out), mx)
    case R.KHt{}:
      no2(G.why(e, R.KHt{}, c, rest, v10, code, out), mx)
    case R.KCo{}:
      no2(G.why(e, R.KCo{}, c, rest, v10, code, out), mx)
    case R.KCm{}:
      no2(G.why(e, R.KCm{}, c, rest, v10, code, out), mx)
    case R.KDg{}:
      no2(G.why(e, R.KDg{}, c, rest, v10, code, out), mx)
    case R.KTk{}:
      no2(G.why(e, R.KTk{}, c, rest, v10, code, out), mx)
    case R.KVc{}:
      no2(G.why(e, R.KVc{}, c, rest, v10, code, out), mx)

def K.why.sat(+e: R.Ask, +k: R.Cls, +c: U32, +rest: List<&2, U32>, +v10: Bool, +code: U32, +out: List<&2, U32>,
  sw: {S.allows(S.TVal{}, k) == False{} : Bool} & ({notcrlf(k) == True{} : Bool} & Plain(rest))) ->
  G.why(e, k, c, rest, v10, code, out):
  (mx, np) = sw
  (nc, pr) = np
  K.why.k(e, k, c, rest, v10, code, out, mx, nc)

def K.why(+e: R.Ask, +v10: Bool, +code: U32, sp: S.Span, +out: List<&2, U32>) ->
  SW(S.TVal{}, sp) ->
  {RES(e, sp, SlWhy{v10, code}, Nil{}, out) == R.P{Rs(S.sv.why(v10, code, sp)), out} : R.P}:
  match sp:
    case S.Span{r, stop}:
      match stop:
        case S.SEnd{}:
          sw => {==}
        case S.SAt{k, c, rest}:
          sw => K.why.sat(e, k, c, rest, v10, code, out, sw)

# the code
def K.csp(+e: R.Ask, b: Bool, +v10: Bool, +d: List<&2, U32>, +rest: List<&2, U32>, +out: List<&2, U32>,
  pr: Plain(rest)) ->
  {R.feed(e, rest, R.P{R.code.sp(b, v10, S.num(d)), out}) == R.P{Rs(S.sv.code.sp(b, v10, d, rest)), out} : R.P}:
  match b:
    case True{}:
      %RS(e, rest, SlWhy{v10, S.num(d)}, Nil{}, out) :
        {_ == R.P{Rs(S.sv.why(v10, S.num(d), S.span(S.TVal{}, rest))), out} : R.P}
      K.why(e, v10, S.num(d), S.span(S.TVal{}, rest), out)(span.sw(S.TVal{}, rest)(pr))
    case False{}:
      bad_feed(e, rest, out)

def G.code(+e: R.Ask, k: R.Cls, c: U32, rest: List<&2, U32>, v10: Bool, d: List<&2, U32>, out: List<&2, U32>) ->
  Type:
  {R.feed(e, rest, R.step.at(e, R.SCode{v10, S.num(d), S.cnt(d)}, k, c, out)) ==
    R.P{Rs(S.sv.code(v10, S.Span{d, S.SAt{k, c, rest}})), out} : R.P}

def K.code.k(+e: R.Ask, k: R.Cls, +c: U32, +rest: List<&2, U32>, +v10: Bool, +d: List<&2, U32>,
  +out: List<&2, U32>, mx: {S.allows(S.TDig{}, k) == False{} : Bool}, nc: {notcrlf(k) == True{} : Bool},
  pr: Plain(rest)) -> G.code(e, k, c, rest, v10, d, out):
  match k:
    case R.KSp{}:
      K.csp(e, S.code.whole(d), v10, d, rest, out, pr)
    case R.KDg{}:
      no2(G.code(e, R.KDg{}, c, rest, v10, d, out), mx)
    case R.KCr{}:
      no(G.code(e, R.KCr{}, c, rest, v10, d, out), nc)
    case R.KLf{}:
      no(G.code(e, R.KLf{}, c, rest, v10, d, out), nc)
    case R.KHt{}:
      bad_feed(e, rest, out)
    case R.KCo{}:
      bad_feed(e, rest, out)
    case R.KCm{}:
      bad_feed(e, rest, out)
    case R.KTk{}:
      bad_feed(e, rest, out)
    case R.KVc{}:
      bad_feed(e, rest, out)
    case R.KCt{}:
      bad_feed(e, rest, out)

def K.code.sat(+e: R.Ask, +k: R.Cls, +c: U32, +rest: List<&2, U32>, +v10: Bool, +d: List<&2, U32>,
  +out: List<&2, U32>,
  sw: {S.allows(S.TDig{}, k) == False{} : Bool} & ({notcrlf(k) == True{} : Bool} & Plain(rest))) ->
  G.code(e, k, c, rest, v10, d, out):
  (mx, np) = sw
  (nc, pr) = np
  K.code.k(e, k, c, rest, v10, d, out, mx, nc, pr)

def K.code(+e: R.Ask, +v10: Bool, sp: S.Span, +out: List<&2, U32>) ->
  SW(S.TDig{}, sp) ->
  {RES(e, sp, SlCode{v10}, Nil{}, out) == R.P{Rs(S.sv.code(v10, sp)), out} : R.P}:
  match sp:
    case S.Span{d, stop}:
      match stop:
        case S.SEnd{}:
          sw => {==}
        case S.SAt{k, c, rest}:
          sw => K.code.sat(e, k, c, rest, v10, d, out, sw)

# the version
def K.vsp(+e: R.Ask, b11: Bool, b10: Bool, +rest: List<&2, U32>, +out: List<&2, U32>, pr: Plain(rest)) ->
  {R.feed(e, rest, R.P{R.ver.sp(b11, b10), out}) == R.P{Rs(S.sv.ver.sp(b11, b10, rest)), out} : R.P}:
  match b11 b10:
    case True{} _:
      %RS(e, rest, SlCode{False{}}, Nil{}, out) :
        {_ == R.P{Rs(S.sv.code(False{}, S.span(S.TDig{}, rest))), out} : R.P}
      K.code(e, False{}, S.span(S.TDig{}, rest), out)(span.sw(S.TDig{}, rest)(pr))
    case False{} True{}:
      %RS(e, rest, SlCode{True{}}, Nil{}, out) :
        {_ == R.P{Rs(S.sv.code(True{}, S.span(S.TDig{}, rest))), out} : R.P}
      K.code(e, True{}, S.span(S.TDig{}, rest), out)(span.sw(S.TDig{}, rest)(pr))
    case False{} False{}:
      bad_feed(e, rest, out)

def G.ver(+e: R.Ask, k: R.Cls, c: U32, rest: List<&2, U32>, +v: List<&2, U32>, out: List<&2, U32>) -> Type:
  {R.feed(e, rest, R.step.at(e, R.SVer{strip(v, R.lit.v11()), strip(v, R.lit.v10())}, k, c, out)) ==
    R.P{Rs(S.sv.ver(S.Span{v, S.SAt{k, c, rest}})), out} : R.P}

def K.ver.k(+e: R.Ask, k: R.Cls, +c: U32, +rest: List<&2, U32>, +v: List<&2, U32>, +out: List<&2, U32>,
  mx: {S.allows(S.TVer{}, k) == False{} : Bool}, nc: {notcrlf(k) == True{} : Bool}, pr: Plain(rest)) ->
  G.ver(e, k, c, rest, v, out):
  match k:
    case R.KSp{}:
      %leq_done(v, R.lit.v11()) :
        {R.feed(e, rest, R.P{R.ver.sp(_, R.done(strip(v, R.lit.v10()))), out}) ==
          R.P{Rs(S.sv.ver.sp(S.leq(v, R.lit.v11()), S.leq(v, R.lit.v10()), rest)), out} : R.P}
      %leq_done(v, R.lit.v10()) :
        {R.feed(e, rest, R.P{R.ver.sp(S.leq(v, R.lit.v11()), _), out}) ==
          R.P{Rs(S.sv.ver.sp(S.leq(v, R.lit.v11()), S.leq(v, R.lit.v10()), rest)), out} : R.P}
      K.vsp(e, S.leq(v, R.lit.v11()), S.leq(v, R.lit.v10()), rest, out, pr)
    case R.KCr{}:
      no(G.ver(e, R.KCr{}, c, rest, v, out), nc)
    case R.KLf{}:
      no(G.ver(e, R.KLf{}, c, rest, v, out), nc)
    case R.KHt{}:
      no2(G.ver(e, R.KHt{}, c, rest, v, out), mx)
    case R.KCo{}:
      no2(G.ver(e, R.KCo{}, c, rest, v, out), mx)
    case R.KCm{}:
      no2(G.ver(e, R.KCm{}, c, rest, v, out), mx)
    case R.KDg{}:
      no2(G.ver(e, R.KDg{}, c, rest, v, out), mx)
    case R.KTk{}:
      no2(G.ver(e, R.KTk{}, c, rest, v, out), mx)
    case R.KVc{}:
      no2(G.ver(e, R.KVc{}, c, rest, v, out), mx)
    case R.KCt{}:
      no2(G.ver(e, R.KCt{}, c, rest, v, out), mx)

def K.ver.sat(+e: R.Ask, +k: R.Cls, +c: U32, +rest: List<&2, U32>, +v: List<&2, U32>, +out: List<&2, U32>,
  sw: {S.allows(S.TVer{}, k) == False{} : Bool} & ({notcrlf(k) == True{} : Bool} & Plain(rest))) ->
  G.ver(e, k, c, rest, v, out):
  (mx, np) = sw
  (nc, pr) = np
  K.ver.k(e, k, c, rest, v, out, mx, nc, pr)

def K.ver(+e: R.Ask, sp: S.Span, +out: List<&2, U32>) ->
  SW(S.TVer{}, sp) -> {RES(e, sp, SlVer{}, Nil{}, out) == R.P{Rs(S.sv.ver(sp)), out} : R.P}:
  match sp:
    case S.Span{v, stop}:
      match stop:
        case S.SEnd{}:
          sw => {==}
        case S.SAt{k, c, rest}:
          sw => K.ver.sat(e, k, c, rest, v, out, sw)

# LEMMA: a status line, as far as it has come, puts the reader where the
# spec's view of it says
def line.status(+e: R.Ask, +x: List<&2, U32>, +out: List<&2, U32>) ->
  Plain(x) -> {R.feed(e, x, R.P{R.st.new(), out}) == R.P{Rs(S.status.view(x)), out} : R.P}:
  pl =>
    %RS(e, x, SlVer{}, Nil{}, out) : {_ == R.P{Rs(S.status.view(x)), out} : R.P}
    K.ver(e, S.span(S.TVer{}, x), out)(span.sw(S.TVer{}, x)(pl))


# A field line, seen
# ------------------

def Rv(+h: R.Head, v: S.Val) -> R.St:
  match v:
    case S.VLen0{}:
      R.Len0{h}
    case S.VLen{n, ws}:
      match ws:
        case False{}:
          R.Len{h, n}
        case True{}:
          R.LenW{h, n}
    case S.VTe0{}:
      R.Te0{h}
    case S.VTe{t}:
      R.Te{h, strip(S.lows(t), R.lit.chunked())}
    case S.VConn{+d, +cur}:
      R.Conn{h, S.named(R.lit.close(), d), S.named(R.lit.ka(), d), strip(S.lows(cur), R.lit.close()),
        strip(S.lows(cur), R.lit.ka())}
    case S.VSkip{}:
      R.Oth{h}

def Rf(+h: R.Head, v: S.FLine) -> R.St:
  match v:
    case S.FEmpty{}:
      R.Lin{h}
    case S.FName{+n}:
      R.Nam{h, strip(S.lows(n), R.lit.cl()), strip(S.lows(n), R.lit.te()), strip(S.lows(n), R.lit.co())}
    case S.FVal{val}:
      Rv(h, val)
    case S.FBad{}:
      R.Bad{}

# a value no field acts on
def G.oth(+e: R.Ask, k: R.Cls, c: U32, rest: List<&2, U32>, +h: R.Head, out: List<&2, U32>) -> Type:
  {R.feed(e, rest, R.step.at(e, R.Oth{h}, k, c, out)) == R.P{R.Bad{}, out} : R.P}

def K.oth.k(+e: R.Ask, k: R.Cls, +c: U32, +rest: List<&2, U32>, +h: R.Head, +out: List<&2, U32>,
  mx: {S.allows(S.TVal{}, k) == False{} : Bool}, nc: {notcrlf(k) == True{} : Bool}) ->
  G.oth(e, k, c, rest, h, out):
  match k:
    case R.KCt{}:
      bad_feed(e, rest, out)
    case R.KCr{}:
      no(G.oth(e, R.KCr{}, c, rest, h, out), nc)
    case R.KLf{}:
      no(G.oth(e, R.KLf{}, c, rest, h, out), nc)
    case R.KSp{}:
      no2(G.oth(e, R.KSp{}, c, rest, h, out), mx)
    case R.KHt{}:
      no2(G.oth(e, R.KHt{}, c, rest, h, out), mx)
    case R.KCo{}:
      no2(G.oth(e, R.KCo{}, c, rest, h, out), mx)
    case R.KCm{}:
      no2(G.oth(e, R.KCm{}, c, rest, h, out), mx)
    case R.KDg{}:
      no2(G.oth(e, R.KDg{}, c, rest, h, out), mx)
    case R.KTk{}:
      no2(G.oth(e, R.KTk{}, c, rest, h, out), mx)
    case R.KVc{}:
      no2(G.oth(e, R.KVc{}, c, rest, h, out), mx)

def K.oth.sat(+e: R.Ask, +k: R.Cls, +c: U32, +rest: List<&2, U32>, +h: R.Head, +out: List<&2, U32>,
  sw: {S.allows(S.TVal{}, k) == False{} : Bool} & ({notcrlf(k) == True{} : Bool} & Plain(rest))) ->
  G.oth(e, k, c, rest, h, out):
  (mx, np) = sw
  (nc, pr) = np
  K.oth.k(e, k, c, rest, h, out, mx, nc)

def K.oth(+e: R.Ask, +h: R.Head, sp: S.Span, +out: List<&2, U32>) ->
  SW(S.TVal{}, sp) -> {RES(e, sp, SlOth{h}, Nil{}, out) == R.P{Rf(h, S.skip.view(sp)), out} : R.P}:
  match sp:
    case S.Span{r, stop}:
      match stop:
        case S.SEnd{}:
          sw => {==}
        case S.SAt{k, c, rest}:
          sw => K.oth.sat(e, k, c, rest, h, out, sw)

# a coding
def G.te(+e: R.Ask, k: R.Cls, c: U32, rest: List<&2, U32>, +h: R.Head, m: Cand(), out: List<&2, U32>) -> Type:
  {R.feed(e, rest, R.step.at(e, R.Te{h, m}, k, c, out)) == R.P{R.Bad{}, out} : R.P}

def K.te.k(+e: R.Ask, k: R.Cls, +c: U32, +rest: List<&2, U32>, +h: R.Head, +m: Cand(), +out: List<&2, U32>,
  mx: {S.allows(S.TVal{}, k) == False{} : Bool}, nc: {notcrlf(k) == True{} : Bool}) ->
  G.te(e, k, c, rest, h, m, out):
  match k:
    case R.KCt{}:
      bad_feed(e, rest, out)
    case R.KCr{}:
      no(G.te(e, R.KCr{}, c, rest, h, m, out), nc)
    case R.KLf{}:
      no(G.te(e, R.KLf{}, c, rest, h, m, out), nc)
    case R.KSp{}:
      no2(G.te(e, R.KSp{}, c, rest, h, m, out), mx)
    case R.KHt{}:
      no2(G.te(e, R.KHt{}, c, rest, h, m, out), mx)
    case R.KCo{}:
      no2(G.te(e, R.KCo{}, c, rest, h, m, out), mx)
    case R.KCm{}:
      no2(G.te(e, R.KCm{}, c, rest, h, m, out), mx)
    case R.KDg{}:
      no2(G.te(e, R.KDg{}, c, rest, h, m, out), mx)
    case R.KTk{}:
      no2(G.te(e, R.KTk{}, c, rest, h, m, out), mx)
    case R.KVc{}:
      no2(G.te(e, R.KVc{}, c, rest, h, m, out), mx)

def K.te.sat(+e: R.Ask, +k: R.Cls, +c: U32, +rest: List<&2, U32>, +h: R.Head, +m: Cand(), +out: List<&2, U32>,
  sw: {S.allows(S.TVal{}, k) == False{} : Bool} & ({notcrlf(k) == True{} : Bool} & Plain(rest))) ->
  G.te(e, k, c, rest, h, m, out):
  (mx, np) = sw
  (nc, pr) = np
  K.te.k(e, k, c, rest, h, m, out, mx, nc)

def K.te(+e: R.Ask, +h: R.Head, +c: U32, sp: S.Span, +out: List<&2, U32>) ->
  SW(S.TVal{}, sp) -> {RES(e, sp, SlTe{h}, [c], out) == R.P{Rf(h, S.te.more(c, sp)), out} : R.P}:
  match sp:
    case S.Span{+r, stop}:
      match stop:
        case S.SEnd{}:
          sw => {==}
        case S.SAt{k, d, rest}:
          sw => K.te.sat(e, k, d, rest, h, strip(S.lows(Con{c, r}), R.lit.chunked()), out, sw)

def G.te0(+e: R.Ask, k: R.Cls, c: U32, rest: List<&2, U32>, +h: R.Head, r: List<&2, U32>, out: List<&2, U32>) -> Type:
  {R.feed(e, rest, R.step.at(e, R.Te0{h}, k, c, out)) ==
    R.P{Rf(h, S.te.view(S.Span{r, S.SAt{k, c, rest}})), out} : R.P}

# the first byte of a coding: the reader's candidate is strip's
def K.te1(+e: R.Ask, +c: U32, +rest: List<&2, U32>, +h: R.Head, +out: List<&2, U32>, pr: Plain(rest)) ->
  {R.feed(e, rest, R.P{R.Te{h, R.cstep(Some{R.lit.chunked()}, R.lower(c))}, out}) ==
    R.P{Rf(h, S.te.more(c, S.span(S.TVal{}, rest))), out} : R.P}:
  %cand1(R.lower(c), R.lit.chunked()) :
    {R.feed(e, rest, R.P{R.Te{h, _}, out}) == R.P{Rf(h, S.te.more(c, S.span(S.TVal{}, rest))), out} : R.P}
  %RS(e, rest, SlTe{h}, [c], out) : {_ == R.P{Rf(h, S.te.more(c, S.span(S.TVal{}, rest))), out} : R.P}
  K.te(e, h, c, S.span(S.TVal{}, rest), out)(span.sw(S.TVal{}, rest)(pr))

def K.te0.k(+e: R.Ask, k: R.Cls, +c: U32, +rest: List<&2, U32>, +h: R.Head, -r: List<&2, U32>, +out: List<&2, U32>,
  mx: {S.allows(S.TOws{}, k) == False{} : Bool}, nc: {notcrlf(k) == True{} : Bool}, pr: Plain(rest)) ->
  G.te0(e, k, c, rest, h, r, out):
  match k:
    case R.KCt{}:
      bad_feed(e, rest, out)
    case R.KCr{}:
      no(G.te0(e, R.KCr{}, c, rest, h, r, out), nc)
    case R.KLf{}:
      no(G.te0(e, R.KLf{}, c, rest, h, r, out), nc)
    case R.KSp{}:
      no2(G.te0(e, R.KSp{}, c, rest, h, r, out), mx)
    case R.KHt{}:
      no2(G.te0(e, R.KHt{}, c, rest, h, r, out), mx)
    case R.KCo{}:
      K.te1(e, c, rest, h, out, pr)
    case R.KCm{}:
      K.te1(e, c, rest, h, out, pr)
    case R.KDg{}:
      K.te1(e, c, rest, h, out, pr)
    case R.KTk{}:
      K.te1(e, c, rest, h, out, pr)
    case R.KVc{}:
      K.te1(e, c, rest, h, out, pr)

def K.te0.sat(+e: R.Ask, +k: R.Cls, +c: U32, +rest: List<&2, U32>, +h: R.Head, -r: List<&2, U32>, +out: List<&2, U32>,
  sw: {S.allows(S.TOws{}, k) == False{} : Bool} & ({notcrlf(k) == True{} : Bool} & Plain(rest))) ->
  G.te0(e, k, c, rest, h, r, out):
  (mx, np) = sw
  (nc, pr) = np
  K.te0.k(e, k, c, rest, h, r, out, mx, nc, pr)

def K.te0(+e: R.Ask, +h: R.Head, sp: S.Span, +out: List<&2, U32>) ->
  SW(S.TOws{}, sp) -> {RES(e, sp, SlTe0{h}, Nil{}, out) == R.P{Rf(h, S.te.view(sp)), out} : R.P}:
  match sp:
    case S.Span{r, stop}:
      match stop:
        case S.SEnd{}:
          sw => {==}
        case S.SAt{k, c, rest}:
          sw => K.te0.sat(e, k, c, rest, h, r, out, sw)

# a length: the whitespace after it
def G.lenw(+e: R.Ask, k: R.Cls, c: U32, rest: List<&2, U32>, +h: R.Head, n: U32, out: List<&2, U32>) -> Type:
  {R.feed(e, rest, R.step.at(e, R.LenW{h, n}, k, c, out)) == R.P{R.Bad{}, out} : R.P}

def K.lenw.k(+e: R.Ask, k: R.Cls, +c: U32, +rest: List<&2, U32>, +h: R.Head, +n: U32, +out: List<&2, U32>,
  mx: {S.allows(S.TOws{}, k) == False{} : Bool}, nc: {notcrlf(k) == True{} : Bool}) ->
  G.lenw(e, k, c, rest, h, n, out):
  match k:
    case R.KSp{}:
      no2(G.lenw(e, R.KSp{}, c, rest, h, n, out), mx)
    case R.KHt{}:
      no2(G.lenw(e, R.KHt{}, c, rest, h, n, out), mx)
    case R.KCr{}:
      no(G.lenw(e, R.KCr{}, c, rest, h, n, out), nc)
    case R.KLf{}:
      no(G.lenw(e, R.KLf{}, c, rest, h, n, out), nc)
    case R.KCo{}:
      bad_feed(e, rest, out)
    case R.KCm{}:
      bad_feed(e, rest, out)
    case R.KDg{}:
      bad_feed(e, rest, out)
    case R.KTk{}:
      bad_feed(e, rest, out)
    case R.KVc{}:
      bad_feed(e, rest, out)
    case R.KCt{}:
      bad_feed(e, rest, out)

def K.lenw.sat(+e: R.Ask, +k: R.Cls, +c: U32, +rest: List<&2, U32>, +h: R.Head, +n: U32, +out: List<&2, U32>,
  sw: {S.allows(S.TOws{}, k) == False{} : Bool} & ({notcrlf(k) == True{} : Bool} & Plain(rest))) ->
  G.lenw(e, k, c, rest, h, n, out):
  (mx, np) = sw
  (nc, pr) = np
  K.lenw.k(e, k, c, rest, h, n, out, mx, nc)

def K.lenw(+e: R.Ask, +h: R.Head, +n: U32, sp: S.Span, +out: List<&2, U32>) ->
  SW(S.TOws{}, sp) -> {RES(e, sp, SlLenW{h, n}, Nil{}, out) == R.P{Rf(h, S.len.ws(n, sp)), out} : R.P}:
  match sp:
    case S.Span{r, stop}:
      match stop:
        case S.SEnd{}:
          sw => {==}
        case S.SAt{k, c, rest}:
          sw => K.lenw.sat(e, k, c, rest, h, n, out, sw)

# a length: its digits
def G.len(+e: R.Ask, k: R.Cls, c: U32, rest: List<&2, U32>, +h: R.Head, +n: U32, out: List<&2, U32>) -> Type:
  {R.feed(e, rest, R.step.at(e, R.Len{h, n}, k, c, out)) ==
    R.P{Rf(h, S.len.digits(n, S.SAt{k, c, rest})), out} : R.P}

def K.len.ws(+e: R.Ask, +c: U32, +rest: List<&2, U32>, +h: R.Head, +n: U32, +out: List<&2, U32>,
  pr: Plain(rest)) ->
  {R.feed(e, rest, R.P{R.LenW{h, n}, out}) == R.P{Rf(h, S.len.ws(n, S.span(S.TOws{}, rest))), out} : R.P}:
  %RS(e, rest, SlLenW{h, n}, Nil{}, out) : {_ == R.P{Rf(h, S.len.ws(n, S.span(S.TOws{}, rest))), out} : R.P}
  K.lenw(e, h, n, S.span(S.TOws{}, rest), out)(span.sw(S.TOws{}, rest)(pr))

def K.len.k(+e: R.Ask, k: R.Cls, +c: U32, +rest: List<&2, U32>, +h: R.Head, +n: U32, +out: List<&2, U32>,
  mx: {S.allows(S.TDig{}, k) == False{} : Bool}, nc: {notcrlf(k) == True{} : Bool}, pr: Plain(rest)) ->
  G.len(e, k, c, rest, h, n, out):
  match k:
    case R.KSp{}:
      K.len.ws(e, c, rest, h, n, out, pr)
    case R.KHt{}:
      K.len.ws(e, c, rest, h, n, out, pr)
    case R.KDg{}:
      no2(G.len(e, R.KDg{}, c, rest, h, n, out), mx)
    case R.KCr{}:
      no(G.len(e, R.KCr{}, c, rest, h, n, out), nc)
    case R.KLf{}:
      no(G.len(e, R.KLf{}, c, rest, h, n, out), nc)
    case R.KCo{}:
      bad_feed(e, rest, out)
    case R.KCm{}:
      bad_feed(e, rest, out)
    case R.KTk{}:
      bad_feed(e, rest, out)
    case R.KVc{}:
      bad_feed(e, rest, out)
    case R.KCt{}:
      bad_feed(e, rest, out)

def K.len.sat(+e: R.Ask, +k: R.Cls, +c: U32, +rest: List<&2, U32>, +h: R.Head, +n: U32, +out: List<&2, U32>,
  sw: {S.allows(S.TDig{}, k) == False{} : Bool} & ({notcrlf(k) == True{} : Bool} & Plain(rest))) ->
  G.len(e, k, c, rest, h, n, out):
  (mx, np) = sw
  (nc, pr) = np
  K.len.k(e, k, c, rest, h, n, out, mx, nc, pr)

def K.len(+e: R.Ask, +h: R.Head, +c: U32, sp: S.Span, +out: List<&2, U32>) ->
  SW(S.TDig{}, sp) ->
  {RES(e, sp, SlLen{h}, [c], out) == R.P{Rf(h, S.len.run(e, S.span.push(c, sp))), out} : R.P}:
  match sp:
    case S.Span{+r, stop}:
      match stop:
        case S.SEnd{}:
          sw => {==}
        case S.SAt{k, d, rest}:
          sw => K.len.sat(e, k, d, rest, h, S.len.num(e, Con{c, r}), out, sw)

# a length: the whitespace before it
def G.len0(+e: R.Ask, k: R.Cls, c: U32, rest: List<&2, U32>, +h: R.Head, r: List<&2, U32>, out: List<&2, U32>) -> Type:
  {R.feed(e, rest, R.step.at(e, R.Len0{h}, k, c, out)) ==
    R.P{Rf(h, S.len.view(e, S.Span{r, S.SAt{k, c, rest}})), out} : R.P}

def K.len1(+e: R.Ask, +c: U32, +rest: List<&2, U32>, +h: R.Head, +out: List<&2, U32>, pr: Plain(rest)) ->
  {R.feed(e, rest, R.P{R.Len{h, R.len.dig(e, 0, c)}, out}) ==
    R.P{Rf(h, S.len.run(e, S.span.push(c, S.span(S.TDig{}, rest)))), out} : R.P}:
  %RS(e, rest, SlLen{h}, [c], out) :
    {_ == R.P{Rf(h, S.len.run(e, S.span.push(c, S.span(S.TDig{}, rest)))), out} : R.P}
  K.len(e, h, c, S.span(S.TDig{}, rest), out)(span.sw(S.TDig{}, rest)(pr))

def K.len0.k(+e: R.Ask, k: R.Cls, +c: U32, +rest: List<&2, U32>, +h: R.Head, -r: List<&2, U32>, +out: List<&2, U32>,
  mx: {S.allows(S.TOws{}, k) == False{} : Bool}, nc: {notcrlf(k) == True{} : Bool}, pr: Plain(rest)) ->
  G.len0(e, k, c, rest, h, r, out):
  match k:
    case R.KDg{}:
      K.len1(e, c, rest, h, out, pr)
    case R.KSp{}:
      no2(G.len0(e, R.KSp{}, c, rest, h, r, out), mx)
    case R.KHt{}:
      no2(G.len0(e, R.KHt{}, c, rest, h, r, out), mx)
    case R.KCr{}:
      no(G.len0(e, R.KCr{}, c, rest, h, r, out), nc)
    case R.KLf{}:
      no(G.len0(e, R.KLf{}, c, rest, h, r, out), nc)
    case R.KCo{}:
      bad_feed(e, rest, out)
    case R.KCm{}:
      bad_feed(e, rest, out)
    case R.KTk{}:
      bad_feed(e, rest, out)
    case R.KVc{}:
      bad_feed(e, rest, out)
    case R.KCt{}:
      bad_feed(e, rest, out)

def K.len0.sat(+e: R.Ask, +k: R.Cls, +c: U32, +rest: List<&2, U32>, +h: R.Head, -r: List<&2, U32>, +out: List<&2, U32>,
  sw: {S.allows(S.TOws{}, k) == False{} : Bool} & ({notcrlf(k) == True{} : Bool} & Plain(rest))) ->
  G.len0(e, k, c, rest, h, r, out):
  (mx, np) = sw
  (nc, pr) = np
  K.len0.k(e, k, c, rest, h, r, out, mx, nc, pr)

def K.len0(+e: R.Ask, +h: R.Head, sp: S.Span, +out: List<&2, U32>) ->
  SW(S.TOws{}, sp) -> {RES(e, sp, SlLen0{h}, Nil{}, out) == R.P{Rf(h, S.len.view(e, sp)), out} : R.P}:
  match sp:
    case S.Span{r, stop}:
      match stop:
        case S.SEnd{}:
          sw => {==}
        case S.SAt{k, c, rest}:
          sw => K.len0.sat(e, k, c, rest, h, r, out, sw)


# a Connection list: what its members said, and the one being read
def CE(+h: R.Head, m: S.Mem) -> R.St:
  match m:
    case S.Mem{ok, +done, +cur}:
      match ok:
        case True{}:
          R.Conn{h, S.named(R.lit.close(), done), S.named(R.lit.ka(), done), strip(S.lows(cur), R.lit.close()),
            strip(S.lows(cur), R.lit.ka())}
        case False{}:
          R.Bad{}

def ce_list(+h: R.Head, m: S.Mem) -> {CE(h, m) == Rf(h, S.list.view(m)) : R.St}:
  match m:
    case S.Mem{ok, done, cur}:
      match ok:
        case True{}:
          {==}
        case False{}:
          {==}

def ce_false(+h: R.Head, s: Bool, -done: List<&2, List<&2, U32>>, -cur: List<&2, U32>, -c: U32) ->
  {CE(h, S.mem.next(s, False{}, done, cur, c)) == R.Bad{} : R.St}:
  match s:
    case True{}:
      {==}
    case False{}:
      {==}

def G.conn(+e: R.Ask, k: R.Cls, c: U32, +h: R.Head, +done: List<&2, List<&2, U32>>, +cur: List<&2, U32>,
  out: List<&2, U32>) -> Type:
  {R.P{CE(h, S.mem.next(S.mem.sep(k), S.allows(S.TVal{}, k), done, cur, c)), out} ==
    R.step.at(e, R.Conn{h, S.named(R.lit.close(), done), S.named(R.lit.ka(), done),
      strip(S.lows(cur), R.lit.close()), strip(S.lows(cur), R.lit.ka())}, k, c, out) : R.P}

def conn.sep(+e: R.Ask, +c: U32, +h: R.Head, +done: List<&2, List<&2, U32>>, +cur: List<&2, U32>,
  +out: List<&2, U32>) -> G.conn(e, R.KSp{}, c, h, done, cur, out):
  %leq_done(S.lows(cur), R.lit.close()) :
    {R.P{CE(h, S.Mem{True{}, Con{cur, done}, Nil{}}), out} ==
      R.P{R.Conn{h, S.named(R.lit.close(), done) || _,
        S.named(R.lit.ka(), done) || R.done(strip(S.lows(cur), R.lit.ka())),
        Some{R.lit.close()}, Some{R.lit.ka()}}, out} : R.P}
  %leq_done(S.lows(cur), R.lit.ka()) :
    {R.P{CE(h, S.Mem{True{}, Con{cur, done}, Nil{}}), out} ==
      R.P{R.Conn{h, S.named(R.lit.close(), done) || S.leq(S.lows(cur), R.lit.close()),
        S.named(R.lit.ka(), done) || _, Some{R.lit.close()}, Some{R.lit.ka()}}, out} : R.P}
  {==}

def conn.byte(+e: R.Ask, +c: U32, +h: R.Head, +done: List<&2, List<&2, U32>>, +cur: List<&2, U32>,
  +out: List<&2, U32>) -> G.conn(e, R.KTk{}, c, h, done, cur, out):
  %strip_lows_snoc(cur, c, R.lit.close()) :
    {R.P{CE(h, S.Mem{True{}, done, S.snoc(cur, c)}), out} ==
      R.P{R.Conn{h, S.named(R.lit.close(), done), S.named(R.lit.ka(), done),
        _, R.cstep(strip(S.lows(cur), R.lit.ka()), R.lower(c))}, out} : R.P}
  %strip_lows_snoc(cur, c, R.lit.ka()) :
    {R.P{CE(h, S.Mem{True{}, done, S.snoc(cur, c)}), out} ==
      R.P{R.Conn{h, S.named(R.lit.close(), done), S.named(R.lit.ka(), done),
        strip(S.lows(S.snoc(cur, c)), R.lit.close()), _}, out} : R.P}
  {==}

def conn.k(+e: R.Ask, k: R.Cls, +c: U32, +h: R.Head, +done: List<&2, List<&2, U32>>, +cur: List<&2, U32>,
  +out: List<&2, U32>, nc: {notcrlf(k) == True{} : Bool}) -> G.conn(e, k, c, h, done, cur, out):
  match k:
    case R.KSp{}:
      conn.sep(e, c, h, done, cur, out)
    case R.KHt{}:
      conn.sep(e, c, h, done, cur, out)
    case R.KCm{}:
      conn.sep(e, c, h, done, cur, out)
    case R.KCt{}:
      {==}
    case R.KCr{}:
      no(G.conn(e, R.KCr{}, c, h, done, cur, out), nc)
    case R.KLf{}:
      no(G.conn(e, R.KLf{}, c, h, done, cur, out), nc)
    case R.KCo{}:
      conn.byte(e, c, h, done, cur, out)
    case R.KDg{}:
      conn.byte(e, c, h, done, cur, out)
    case R.KTk{}:
      conn.byte(e, c, h, done, cur, out)
    case R.KVc{}:
      conn.byte(e, c, h, done, cur, out)

def conn.step(+e: R.Ask, ok: Bool, +k: R.Cls, +c: U32, +h: R.Head, +done: List<&2, List<&2, U32>>,
  +cur: List<&2, U32>, +out: List<&2, U32>, nc: {notcrlf(k) == True{} : Bool}) ->
  {R.P{CE(h, S.mem.next(S.mem.sep(k), ok && S.allows(S.TVal{}, k), done, cur, c)), out} ==
    R.step.at(e, CE(h, S.Mem{ok, done, cur}), k, c, out) : R.P}:
  match ok:
    case True{}:
      conn.k(e, k, c, h, done, cur, out, nc)
    case False{}:
      Equal.cong(R.St, R.P, x => R.P{x, out}, CE(h, S.mem.next(S.mem.sep(k), False{}, done, cur, c)), R.Bad{},
        ce_false(h, S.mem.sep(k), done, cur, c))

def conn.walk.con(+e: R.Ask, +c: U32, +t: List<&2, U32>, +h: R.Head, m: S.Mem, +out: List<&2, U32>,
  pv: {notcrlf(R.cls(c)) == True{} : Bool} & Plain(t),
  ih: @+m2: S.Mem -> Plain(t) -> {R.feed(e, t, R.P{CE(h, m2), out}) == R.P{CE(h, S.members(t, m2)), out} : R.P}) ->
  {R.feed(e, Con{c, t}, R.P{CE(h, m), out}) == R.P{CE(h, S.members(Con{c, t}, m)), out} : R.P}:
  match m:
    case S.Mem{+ok, +done, +cur}:
      (nc, pt) = pv
      %conn.step(e, ok, R.cls(c), c, h, done, cur, out, nc) :
        {R.feed(e, t, _) ==
          R.P{CE(h, S.members(t, S.mem.next(S.mem.sep(R.cls(c)), ok && S.allows(S.TVal{}, R.cls(c)), done, cur, c))),
            out} : R.P}
      ih(S.mem.next(S.mem.sep(R.cls(c)), ok && S.allows(S.TVal{}, R.cls(c)), done, cur, c))(pt)

# LEMMA: a Connection list, member by member, as the spec reads it
def conn.walk(+e: R.Ask, v: List<&2, U32>, +h: R.Head, +m: S.Mem, +out: List<&2, U32>) ->
  Plain(v) -> {R.feed(e, v, R.P{CE(h, m), out}) == R.P{CE(h, S.members(v, m)), out} : R.P}:
  match v:
    case Nil{}:
      pv => {==}
    case Con{+c, +t}:
      pv => conn.walk.con(e, c, t, h, m, out, pv, m2 => conn.walk(e, t, h, m2, out))

def K.conn(+e: R.Ask, +h: R.Head, +v: List<&2, U32>, +out: List<&2, U32>, pv: Plain(v)) ->
  {R.feed(e, v, R.P{R.Conn{h, False{}, False{}, Some{R.lit.close()}, Some{R.lit.ka()}}, out}) ==
    R.P{Rf(h, S.list.view(S.members(v, S.Mem{True{}, Nil{}, Nil{}}))), out} : R.P}:
  %ce_list(h, S.members(v, S.Mem{True{}, Nil{}, Nil{}})) :
    {R.feed(e, v, R.P{R.Conn{h, False{}, False{}, Some{R.lit.close()}, Some{R.lit.ka()}}, out}) == R.P{_, out} : R.P}
  conn.walk(e, v, h, S.Mem{True{}, Nil{}, Nil{}}, out)(pv)

# a name, at its colon: the field it names, and its value read that way
def K.fld(+e: R.Ask, b1: Bool, b2: Bool, b3: Bool, +h: R.Head, +v: List<&2, U32>, +out: List<&2, U32>,
  pv: Plain(v)) ->
  {R.feed(e, v, R.P{R.name.end(h, b1, b2, b3), out}) ==
    R.P{Rf(h, S.field.of(e, S.fld.pick(b1, S.FCl{}, S.fld.pick(b2, S.FTe{}, S.fld.pick(b3, S.FConn{}, S.FOther{}))),
      v)), out} : R.P}:
  match b1 b2 b3:
    case True{} _ _:
      %RS(e, v, SlLen0{h}, Nil{}, out) : {_ == R.P{Rf(h, S.len.view(e, S.span(S.TOws{}, v))), out} : R.P}
      K.len0(e, h, S.span(S.TOws{}, v), out)(span.sw(S.TOws{}, v)(pv))
    case False{} True{} _:
      %RS(e, v, SlTe0{h}, Nil{}, out) : {_ == R.P{Rf(h, S.te.view(S.span(S.TOws{}, v))), out} : R.P}
      K.te0(e, h, S.span(S.TOws{}, v), out)(span.sw(S.TOws{}, v)(pv))
    case False{} False{} True{}:
      K.conn(e, h, v, out, pv)
    case False{} False{} False{}:
      %RS(e, v, SlOth{h}, Nil{}, out) : {_ == R.P{Rf(h, S.skip.view(S.span(S.TVal{}, v))), out} : R.P}
      K.oth(e, h, S.span(S.TVal{}, v), out)(span.sw(S.TVal{}, v)(pv))

def G.name(+e: R.Ask, k: R.Cls, d: U32, v: List<&2, U32>, +h: R.Head, +n: List<&2, U32>, out: List<&2, U32>) ->
  Type:
  {R.feed(e, v, R.step.at(e, R.Nam{h, strip(S.lows(n), R.lit.cl()), strip(S.lows(n), R.lit.te()),
    strip(S.lows(n), R.lit.co())}, k, d, out)) == R.P{Rf(h, S.field.name(e, S.Span{n, S.SAt{k, d, v}})), out} : R.P}

def K.name.co(+e: R.Ask, +d: U32, +v: List<&2, U32>, +h: R.Head, +n: List<&2, U32>, +out: List<&2, U32>,
  pv: Plain(v)) ->
  {R.feed(e, v, R.P{R.name.end(h, R.done(strip(S.lows(n), R.lit.cl())), R.done(strip(S.lows(n), R.lit.te())),
    R.done(strip(S.lows(n), R.lit.co()))), out}) ==
    R.P{Rf(h, S.field.of(e, S.field(S.lows(n)), v)), out} : R.P}:
  %leq_done(S.lows(n), R.lit.cl()) :
    {R.feed(e, v, R.P{R.name.end(h, _, R.done(strip(S.lows(n), R.lit.te())),
      R.done(strip(S.lows(n), R.lit.co()))), out}) == R.P{Rf(h, S.field.of(e, S.field(S.lows(n)), v)), out} : R.P}
  %leq_done(S.lows(n), R.lit.te()) :
    {R.feed(e, v, R.P{R.name.end(h, S.leq(S.lows(n), R.lit.cl()), _,
      R.done(strip(S.lows(n), R.lit.co()))), out}) == R.P{Rf(h, S.field.of(e, S.field(S.lows(n)), v)), out} : R.P}
  %leq_done(S.lows(n), R.lit.co()) :
    {R.feed(e, v, R.P{R.name.end(h, S.leq(S.lows(n), R.lit.cl()), S.leq(S.lows(n), R.lit.te()), _), out}) ==
      R.P{Rf(h, S.field.of(e, S.field(S.lows(n)), v)), out} : R.P}
  K.fld(e, S.leq(S.lows(n), R.lit.cl()), S.leq(S.lows(n), R.lit.te()), S.leq(S.lows(n), R.lit.co()), h, v, out, pv)

def K.name.k(+e: R.Ask, k: R.Cls, +d: U32, +v: List<&2, U32>, +h: R.Head, +c: U32, +r: List<&2, U32>,
  +out: List<&2, U32>, mx: {S.allows(S.TName{}, k) == False{} : Bool}, nc: {notcrlf(k) == True{} : Bool},
  pv: Plain(v)) -> G.name(e, k, d, v, h, Con{c, r}, out):
  match k:
    case R.KCo{}:
      K.name.co(e, d, v, h, Con{c, r}, out, pv)
    case R.KTk{}:
      no2(G.name(e, R.KTk{}, d, v, h, Con{c, r}, out), mx)
    case R.KDg{}:
      no2(G.name(e, R.KDg{}, d, v, h, Con{c, r}, out), mx)
    case R.KCr{}:
      no(G.name(e, R.KCr{}, d, v, h, Con{c, r}, out), nc)
    case R.KLf{}:
      no(G.name(e, R.KLf{}, d, v, h, Con{c, r}, out), nc)
    case R.KSp{}:
      bad_feed(e, v, out)
    case R.KHt{}:
      bad_feed(e, v, out)
    case R.KCm{}:
      bad_feed(e, v, out)
    case R.KVc{}:
      bad_feed(e, v, out)
    case R.KCt{}:
      bad_feed(e, v, out)

def K.name.sat(+e: R.Ask, +k: R.Cls, +d: U32, +v: List<&2, U32>, +h: R.Head, +c: U32, +r: List<&2, U32>,
  +out: List<&2, U32>,
  sw: {S.allows(S.TName{}, k) == False{} : Bool} & ({notcrlf(k) == True{} : Bool} & Plain(v))) ->
  G.name(e, k, d, v, h, Con{c, r}, out):
  (mx, np) = sw
  (nc, pv) = np
  K.name.k(e, k, d, v, h, c, r, out, mx, nc, pv)

def K.name(+e: R.Ask, +h: R.Head, +c: U32, sp: S.Span, +out: List<&2, U32>) ->
  SW(S.TName{}, sp) ->
  {RES(e, sp, SlName{h}, [c], out) == R.P{Rf(h, S.field.name(e, S.span.push(c, sp))), out} : R.P}:
  match sp:
    case S.Span{+r, stop}:
      match stop:
        case S.SEnd{}:
          sw => {==}
        case S.SAt{k, d, v}:
          sw => K.name.sat(e, k, d, v, h, c, r, out, sw)

def G.line(+e: R.Ask, k: R.Cls, c: U32, t: List<&2, U32>, +h: R.Head, out: List<&2, U32>) -> Type:
  {R.feed(e, t, R.step.at(e, R.Lin{h}, k, c, out)) ==
    R.P{Rf(h, S.field.name(e, S.span.pick(S.allows(S.TName{}, k), k, c, t, S.span(S.TName{}, t)))), out} : R.P}

def line.field.name(+e: R.Ask, +c: U32, +t: List<&2, U32>, +h: R.Head, +out: List<&2, U32>, pt: Plain(t)) ->
  {R.feed(e, t, R.P{R.Nam{h, R.cstep(Some{R.lit.cl()}, R.lower(c)), R.cstep(Some{R.lit.te()}, R.lower(c)),
    R.cstep(Some{R.lit.co()}, R.lower(c))}, out}) ==
    R.P{Rf(h, S.field.name(e, S.span.push(c, S.span(S.TName{}, t)))), out} : R.P}:
  %cand1(R.lower(c), R.lit.cl()) :
    {R.feed(e, t, R.P{R.Nam{h, _, R.cstep(Some{R.lit.te()}, R.lower(c)),
      R.cstep(Some{R.lit.co()}, R.lower(c))}, out}) ==
      R.P{Rf(h, S.field.name(e, S.span.push(c, S.span(S.TName{}, t)))), out} : R.P}
  %cand1(R.lower(c), R.lit.te()) :
    {R.feed(e, t, R.P{R.Nam{h, strip([R.lower(c)], R.lit.cl()), _,
      R.cstep(Some{R.lit.co()}, R.lower(c))}, out}) ==
      R.P{Rf(h, S.field.name(e, S.span.push(c, S.span(S.TName{}, t)))), out} : R.P}
  %cand1(R.lower(c), R.lit.co()) :
    {R.feed(e, t, R.P{R.Nam{h, strip([R.lower(c)], R.lit.cl()), strip([R.lower(c)], R.lit.te()), _}, out}) ==
      R.P{Rf(h, S.field.name(e, S.span.push(c, S.span(S.TName{}, t)))), out} : R.P}
  %RS(e, t, SlName{h}, [c], out) : {_ == R.P{Rf(h, S.field.name(e, S.span.push(c, S.span(S.TName{}, t)))), out} : R.P}
  K.name(e, h, c, S.span(S.TName{}, t), out)(span.sw(S.TName{}, t)(pt))

# the reader builds a literal's candidate only when the name's first
# byte starts it: the same candidate as the literal stepped
def lit1(b: Bool, +s: String) -> {R.lit.first(b, s) == R.cand.pick(b, Wr.bytes(s)) : Maybe<&2, List<&2, U32>>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def line.field.name1(+e: R.Ask, +c: U32, +t: List<&2, U32>, +h: R.Head, +out: List<&2, U32>, pt: Plain(t)) ->
  {R.feed(e, t, R.P{R.Nam{h, R.cl1(R.lower(c)), R.te1(R.lower(c)), R.co1(R.lower(c))}, out}) == R.P{Rf(h, S.field.name(e, S.span.push(c, S.span(S.TName{}, t)))), out} : R.P}:
  +l = R.lower(c)
  %Equal.sym(Maybe<&2, List<&2, U32>>, R.lit.first(U32.is_eq(l, 99), "ontent-length"),
    R.cand.pick(U32.is_eq(l, 99), Wr.bytes("ontent-length")), lit1(U32.is_eq(l, 99), "ontent-length")) :
    {R.feed(e, t, R.P{R.Nam{h, _, R.te1(l), R.co1(l)}, out}) == R.P{Rf(h, S.field.name(e, S.span.push(c, S.span(S.TName{}, t)))), out} : R.P}
  %Equal.sym(Maybe<&2, List<&2, U32>>, R.lit.first(U32.is_eq(l, 116), "ransfer-encoding"),
    R.cand.pick(U32.is_eq(l, 116), Wr.bytes("ransfer-encoding")), lit1(U32.is_eq(l, 116), "ransfer-encoding")) :
    {R.feed(e, t, R.P{R.Nam{h, R.cand.pick(U32.is_eq(l, 99), Wr.bytes("ontent-length")), _, R.co1(l)}, out}) ==
      R.P{Rf(h, S.field.name(e, S.span.push(c, S.span(S.TName{}, t)))), out} : R.P}
  %Equal.sym(Maybe<&2, List<&2, U32>>, R.lit.first(U32.is_eq(l, 99), "onnection"),
    R.cand.pick(U32.is_eq(l, 99), Wr.bytes("onnection")), lit1(U32.is_eq(l, 99), "onnection")) :
    {R.feed(e, t, R.P{R.Nam{h, R.cand.pick(U32.is_eq(l, 99), Wr.bytes("ontent-length")),
      R.cand.pick(U32.is_eq(l, 116), Wr.bytes("ransfer-encoding")), _}, out}) == R.P{Rf(h, S.field.name(e, S.span.push(c, S.span(S.TName{}, t)))), out} : R.P}
  line.field.name(e, c, t, h, out, pt)

def line.field.k(+e: R.Ask, k: R.Cls, +c: U32, +t: List<&2, U32>, +h: R.Head, +out: List<&2, U32>,
  nc: {notcrlf(k) == True{} : Bool}, pt: Plain(t)) -> G.line(e, k, c, t, h, out):
  match k:
    case R.KTk{}:
      line.field.name1(e, c, t, h, out, pt)
    case R.KDg{}:
      line.field.name1(e, c, t, h, out, pt)
    case R.KCr{}:
      no(G.line(e, R.KCr{}, c, t, h, out), nc)
    case R.KLf{}:
      no(G.line(e, R.KLf{}, c, t, h, out), nc)
    case R.KSp{}:
      bad_feed(e, t, out)
    case R.KHt{}:
      bad_feed(e, t, out)
    case R.KCo{}:
      bad_feed(e, t, out)
    case R.KCm{}:
      bad_feed(e, t, out)
    case R.KVc{}:
      bad_feed(e, t, out)
    case R.KCt{}:
      bad_feed(e, t, out)

def line.field.con(+e: R.Ask, +c: U32, +t: List<&2, U32>, +h: R.Head, +out: List<&2, U32>,
  pl: {notcrlf(R.cls(c)) == True{} : Bool} & Plain(t)) -> G.line(e, R.cls(c), c, t, h, out):
  (nc, pt) = pl
  line.field.k(e, R.cls(c), c, t, h, out, nc, pt)

# LEMMA: a field line, as far as it has come, puts the reader where the
# spec's view of it says
def line.field(+e: R.Ask, x: List<&2, U32>, +h: R.Head, +out: List<&2, U32>) ->
  Plain(x) -> {R.feed(e, x, R.P{R.Lin{h}, out}) == R.P{Rf(h, S.field.view(e, x)), out} : R.P}:
  match x:
    case Nil{}:
      pl => {==}
    case Con{+c, +t}:
      pl => line.field.con(e, c, t, h, out, pl)


# The reader is the framing
# =========================
#
# resp_sim is a simulation. The spec's walk gathers a line's bytes and
# reads the line whole at its CR; the reader steps each byte. emb says
# where the reader is for each place the walk can be -- inside a line,
# the reader from the line's start fed the line so far; anywhere else,
# the state of the same name holding the same things -- and a byte
# moves both so that emb still holds after it (STEP); at the input's
# end, emb gives the agreement (END); induction on the input does the
# rest (walk.lem). Inside a line, line.status and line.field above say
# what that reader is: the state the spec's view of the line names.

def emb.m(+e: R.Ask, mode: S.Mode, out: List<&2, U32>) -> R.P:
  match mode:
    case S.MStatus{cur}:
      R.feed(e, cur, R.P{R.st.new(), out})
    case S.MField{h, cur}:
      R.feed(e, cur, R.P{R.Lin{h}, out})
    case S.MEol{h}:
      R.P{R.Eol{h}, out}
    case S.MEoh{h}:
      R.P{R.Eoh{h}, out}
    case S.MBody{h, more, got}:
      R.P{R.Bod{h, more, Bytes.from_list(got)}, out}
    case S.MChunk{h, at, n, got, left}:
      R.P{R.Chk{h, at, n, Bytes.from_list(got), left}, out}
    case S.MData{h, more, got, left}:
      R.P{R.Dat{h, more, Bytes.from_list(got), left}, out}
    case S.MClose{h, got, left}:
      R.P{R.Clo{h, Bytes.from_list(got), left}, out}
    case S.MDone{r, rest}:
      R.P{R.Fin{r, Bytes.from_list(rest)}, out}
    case S.MBad{}:
      R.P{R.Bad{}, out}

def emb(+e: R.Ask, w: S.W) -> R.P:
  match w:
    case S.W{mode, out}:
      emb.m(e, mode, out)

def INV.m(mode: S.Mode) -> Type:
  match mode:
    case S.MStatus{cur}:
      Plain(cur)
    case S.MField{h, cur}:
      Plain(cur)
    case _:
      Unit

def INV(w: S.W) -> Type:
  match w:
    case S.W{mode, out}:
      INV.m(mode)

# a final response, as each side builds it
def final.is(h: R.Head, +xs: List<&2, U32>, +d: Bool) ->
  {S.resp(h, xs, d) == R.final(h, Bytes.from_list(xs), d) : R.Resp}:
  match h:
    case R.Head{v10, code, l, te, cl, ka}:
      {==}

def final.snoc(+h: R.Head, +xs: List<&2, U32>, +c: U32, +d: Bool) ->
  {S.resp(h, S.snoc(xs, c), d) == R.final(h, Bytes.push(Bytes.from_list(xs), c), d) : R.Resp}:
  Equal.trans(R.Resp, S.resp(h, S.snoc(xs, c), d), R.final(h, Bytes.from_list(S.snoc(xs, c)), d),
    R.final(h, Bytes.push(Bytes.from_list(xs), c), d), final.is(h, S.snoc(xs, c), d),
    Equal.cong(Bytes(), R.Resp, b => R.final(h, b, d), Bytes.from_list(S.snoc(xs, c)),
      Bytes.push(Bytes.from_list(xs), c), fl_snoc(xs, c)))

# what a byte must keep: the walk's invariant after it, and the reader
# where emb puts it
def SG(+e: R.Ask, mode: S.Mode, out: List<&2, U32>, p: R.P) -> Type:
  INV.m(mode) & {emb.m(e, mode, out) == p : R.P}

# a byte of a line that is neither CR nor LF: one more byte for the
# reader from the line's start
def line.more(+e: R.Ask, +cur: List<&2, U32>, +c: U32, -k: R.Cls, +p0: R.P, +st1: R.St, +out: List<&2, U32>,
  ek: {R.cls(c) == k : R.Cls}, eq: {R.feed(e, cur, p0) == R.P{st1, out} : R.P}) ->
  {R.feed(e, S.snoc(cur, c), p0) == R.step.at(e, st1, k, c, out) : R.P}:
  Equal.trans(R.P, R.feed(e, S.snoc(cur, c), p0), R.step(e, R.feed(e, cur, p0), c),
    R.step.at(e, st1, k, c, out), feed_snoc(e, cur, c, p0),
    Equal.trans(R.P, R.step(e, R.feed(e, cur, p0), c), R.step(e, R.P{st1, out}, c),
      R.step.at(e, st1, k, c, out),
      Equal.cong(R.P, R.P, x => R.step(e, x, c), R.feed(e, cur, p0), R.P{st1, out}, eq),
      Equal.cong(R.Cls, R.P, y => R.step.at(e, st1, y, c, out), R.cls(c), k, ek)))

def ncof(-c: U32, -k: R.Cls, ek: {R.cls(c) == k : R.Cls}, nk: {notcrlf(k) == True{} : Bool}) ->
  {notcrlf(R.cls(c)) == True{} : Bool}:
  Equal.trans(Bool, notcrlf(R.cls(c)), notcrlf(k), True{}, Equal.cong(R.Cls, Bool, notcrlf, R.cls(c), k, ek), nk)

# The status line's byte
# ----------------------

def st.cr.code(+e: R.Ask, b: Bool, +v10: Bool, +d: List<&2, U32>, +out: List<&2, U32>) ->
  SG(e, S.status.cr.code(b, v10, d), out, R.P{R.code.cr(b, v10, S.num(d)), out}):
  match b:
    case True{}:
      (Unit{}, {==})
    case False{}:
      (Unit{}, {==})

def st.cr(+e: R.Ask, v: S.SView, +c: U32, +out: List<&2, U32>) ->
  SG(e, S.status.cr(v), out, R.step.at(e, Rs(v), R.KCr{}, c, out)):
  match v:
    case S.VVer{x}:
      (Unit{}, {==})
    case S.VCode{v10, +d}:
      st.cr.code(e, S.code.whole(d), v10, d, out)
    case S.VWhy{v10, code}:
      (Unit{}, {==})
    case S.VBad{}:
      (Unit{}, {==})

def st.lf(+e: R.Ask, v: S.SView, +c: U32, +out: List<&2, U32>) ->
  {R.P{R.Bad{}, out} == R.step.at(e, Rs(v), R.KLf{}, c, out) : R.P}:
  match v:
    case S.VVer{x}:
      {==}
    case S.VCode{v10, d}:
      {==}
    case S.VWhy{v10, code}:
      {==}
    case S.VBad{}:
      {==}

def G.st(+e: R.Ask, +k: R.Cls, +c: U32, +cur: List<&2, U32>, +out: List<&2, U32>) -> Type:
  SG(e, S.line.byte(k, c, cur, S.status.cr(S.status.view(cur)), x => S.MStatus{x}), out,
    R.step.at(e, Rs(S.status.view(cur)), k, c, out))

def st.more(+e: R.Ask, -k: R.Cls, +c: U32, +cur: List<&2, U32>, +out: List<&2, U32>,
  +ek: {R.cls(c) == k : R.Cls}, nk: {notcrlf(k) == True{} : Bool}, pp: Plain(cur) & Plain(cur)) ->
  Plain(S.snoc(cur, c)) &
  {R.feed(e, S.snoc(cur, c), R.P{R.st.new(), out}) == R.step.at(e, Rs(S.status.view(cur)), k, c, out) : R.P}:
  (p1, p2) = pp
  (plain.snoc(cur, c, ncof(c, k, ek, nk))(p1),
    line.more(e, cur, c, k, R.P{R.st.new(), out}, Rs(S.status.view(cur)), out, ek, line.status(e, cur, out)(p2)))

def st.k(+e: R.Ask, k: R.Cls, +c: U32, +cur: List<&2, U32>, +out: List<&2, U32>, ek: {R.cls(c) == k : R.Cls},
  pl: Plain(cur)) -> G.st(e, k, c, cur, out):
  match k:
    case R.KCr{}:
      st.cr(e, S.status.view(cur), c, out)
    case R.KLf{}:
      (Unit{}, st.lf(e, S.status.view(cur), c, out))
    case R.KSp{}:
      st.more(e, R.KSp{}, c, cur, out, ek, {==}, plain.dup(cur)(pl))
    case R.KHt{}:
      st.more(e, R.KHt{}, c, cur, out, ek, {==}, plain.dup(cur)(pl))
    case R.KCo{}:
      st.more(e, R.KCo{}, c, cur, out, ek, {==}, plain.dup(cur)(pl))
    case R.KCm{}:
      st.more(e, R.KCm{}, c, cur, out, ek, {==}, plain.dup(cur)(pl))
    case R.KDg{}:
      st.more(e, R.KDg{}, c, cur, out, ek, {==}, plain.dup(cur)(pl))
    case R.KTk{}:
      st.more(e, R.KTk{}, c, cur, out, ek, {==}, plain.dup(cur)(pl))
    case R.KVc{}:
      st.more(e, R.KVc{}, c, cur, out, ek, {==}, plain.dup(cur)(pl))
    case R.KCt{}:
      st.more(e, R.KCt{}, c, cur, out, ek, {==}, plain.dup(cur)(pl))

def STEP.status(+e: R.Ask, +c: U32, +cur: List<&2, U32>, +out: List<&2, U32>, pp: Plain(cur) & Plain(cur)) ->
  SG(e, S.line.byte(R.cls(c), c, cur, S.status.cr(S.status.view(cur)), x => S.MStatus{x}), out,
    R.step(e, R.feed(e, cur, R.P{R.st.new(), out}), c)):
  (p1, p2) = pp
  %Equal.sym(R.P, R.feed(e, cur, R.P{R.st.new(), out}), R.P{Rs(S.status.view(cur)), out},
    line.status(e, cur, out)(p1)) :
    SG(e, S.line.byte(R.cls(c), c, cur, S.status.cr(S.status.view(cur)), x => S.MStatus{x}), out,
      R.step(e, _, c))
  st.k(e, R.cls(c), c, cur, out, {==}, p2)


# A field line's byte
# -------------------

def fl.len.at(+e: R.Ask, b: Bool, +h: R.Head, +out: List<&2, U32>) ->
  SG(e, S.field.next(S.head.len.at(b, h)), out, R.P{R.len.at(b, h), out}):
  match b:
    case True{}:
      (Unit{}, {==})
    case False{}:
      (Unit{}, {==})

def fl.len.head(+e: R.Ask, h: R.Head, +n: U32, +out: List<&2, U32>) ->
  SG(e, S.field.next(S.head.len(h, n)), out, R.P{R.len.head(h, n), out}):
  match h:
    case R.Head{v10, code, l, te, cl, ka}:
      match l:
        case None{}:
          (Unit{}, {==})
        case Some{+w}:
          fl.len.at(e, U32.is_eq(n, w), R.Head{v10, code, Some{w}, te, cl, ka}, out)

def fl.len(+e: R.Ask, b: Bool, +h: R.Head, +n: U32, +out: List<&2, U32>) ->
  SG(e, S.field.next(S.head.big(b, h, n)), out, R.P{R.len.big(b, h, n), out}):
  match b:
    case True{}:
      (Unit{}, {==})
    case False{}:
      fl.len.head(e, h, n, out)

def fl.te.at(+e: R.Ask, b: Bool, h: R.Head, +out: List<&2, U32>) ->
  SG(e, S.field.next(S.head.te.at(b, h)), out, R.P{R.te.at(b, h), out}):
  match b h:
    case True{} R.Head{v10, code, l, te, cl, ka}:
      (Unit{}, {==})
    case False{} _:
      (Unit{}, {==})

def fl.te(+e: R.Ask, b: Bool, h: R.Head, +out: List<&2, U32>) ->
  SG(e, S.field.next(S.head.te(h, b)), out, R.P{R.te.cr(h, b), out}):
  match h:
    case R.Head{v10, code, l, +te, cl, ka}:
      fl.te.at(e, b && Bool.not(te), R.Head{v10, code, l, te, cl, ka}, out)

def fl.conn(+e: R.Ask, a: Bool, b: Bool, h: R.Head, +out: List<&2, U32>) ->
  SG(e, S.MEol{S.head.conn(h, a, b)}, out, R.P{R.conn.cr(h, a, b), out}):
  match h:
    case R.Head{v10, code, l, te, cl, ka}:
      (Unit{}, {==})

def fl.cr.val(+e: R.Ask, +h: R.Head, val: S.Val, +c: U32, +out: List<&2, U32>) ->
  SG(e, S.field.next(S.field.done(e, h, val)), out, R.step.at(e, Rv(h, val), R.KCr{}, c, out)):
  match val:
    case S.VLen0{}:
      (Unit{}, {==})
    case S.VLen{+n, ws}:
      match ws:
        case False{}:
          fl.len(e, U32.is_lt(R.ask.cap(e), n), h, n, out)
        case True{}:
          fl.len(e, U32.is_lt(R.ask.cap(e), n), h, n, out)
    case S.VTe0{}:
      (Unit{}, {==})
    case S.VTe{+t}:
      %leq_done(S.lows(t), R.lit.chunked()) :
        SG(e, S.field.next(S.head.te(h, S.leq(S.lows(t), R.lit.chunked()))), out, R.P{R.te.cr(h, _), out})
      fl.te(e, S.leq(S.lows(t), R.lit.chunked()), h, out)
    case S.VConn{+d, +cur}:
      %leq_done(S.lows(cur), R.lit.close()) :
        SG(e, S.MEol{S.head.conn(h, S.named(R.lit.close(), Con{cur, d}), S.named(R.lit.ka(), Con{cur, d}))}, out,
          R.P{R.conn.cr(h, S.named(R.lit.close(), d) || _,
            S.named(R.lit.ka(), d) || R.done(strip(S.lows(cur), R.lit.ka()))), out})
      %leq_done(S.lows(cur), R.lit.ka()) :
        SG(e, S.MEol{S.head.conn(h, S.named(R.lit.close(), Con{cur, d}), S.named(R.lit.ka(), Con{cur, d}))}, out,
          R.P{R.conn.cr(h, S.named(R.lit.close(), d) || S.leq(S.lows(cur), R.lit.close()),
            S.named(R.lit.ka(), d) || _), out})
      fl.conn(e, S.named(R.lit.close(), Con{cur, d}), S.named(R.lit.ka(), Con{cur, d}), h, out)
    case S.VSkip{}:
      (Unit{}, {==})

def fl.cr(+e: R.Ask, +h: R.Head, v: S.FLine, +c: U32, +out: List<&2, U32>) ->
  SG(e, S.field.cr(e, h, v), out, R.step.at(e, Rf(h, v), R.KCr{}, c, out)):
  match v:
    case S.FEmpty{}:
      (Unit{}, {==})
    case S.FName{n}:
      (Unit{}, {==})
    case S.FVal{val}:
      fl.cr.val(e, h, val, c, out)
    case S.FBad{}:
      (Unit{}, {==})

def fl.lf(+e: R.Ask, +h: R.Head, v: S.FLine, +c: U32, +out: List<&2, U32>) ->
  {R.P{R.Bad{}, out} == R.step.at(e, Rf(h, v), R.KLf{}, c, out) : R.P}:
  match v:
    case S.FEmpty{}:
      {==}
    case S.FName{n}:
      {==}
    case S.FVal{val}:
      match val:
        case S.VLen0{}:
          {==}
        case S.VLen{n, ws}:
          match ws:
            case False{}:
              {==}
            case True{}:
              {==}
        case S.VTe0{}:
          {==}
        case S.VTe{t}:
          {==}
        case S.VConn{d, cur}:
          {==}
        case S.VSkip{}:
          {==}
    case S.FBad{}:
      {==}

def G.fl(+e: R.Ask, +k: R.Cls, +c: U32, +h: R.Head, +cur: List<&2, U32>, +out: List<&2, U32>) -> Type:
  SG(e, S.line.byte(k, c, cur, S.field.cr(e, h, S.field.view(e, cur)), x => S.MField{h, x}), out,
    R.step.at(e, Rf(h, S.field.view(e, cur)), k, c, out))

def fl.more(+e: R.Ask, -k: R.Cls, +c: U32, +h: R.Head, +cur: List<&2, U32>, +out: List<&2, U32>,
  +ek: {R.cls(c) == k : R.Cls}, nk: {notcrlf(k) == True{} : Bool}, pp: Plain(cur) & Plain(cur)) ->
  Plain(S.snoc(cur, c)) &
  {R.feed(e, S.snoc(cur, c), R.P{R.Lin{h}, out}) == R.step.at(e, Rf(h, S.field.view(e, cur)), k, c, out) : R.P}:
  (p1, p2) = pp
  (plain.snoc(cur, c, ncof(c, k, ek, nk))(p1),
    line.more(e, cur, c, k, R.P{R.Lin{h}, out}, Rf(h, S.field.view(e, cur)), out, ek, line.field(e, cur, h, out)(p2)))

def fl.k(+e: R.Ask, k: R.Cls, +c: U32, +h: R.Head, +cur: List<&2, U32>, +out: List<&2, U32>,
  +ek: {R.cls(c) == k : R.Cls}, pl: Plain(cur)) -> G.fl(e, k, c, h, cur, out):
  match k:
    case R.KCr{}:
      fl.cr(e, h, S.field.view(e, cur), c, out)
    case R.KLf{}:
      (Unit{}, fl.lf(e, h, S.field.view(e, cur), c, out))
    case R.KSp{}:
      fl.more(e, R.KSp{}, c, h, cur, out, ek, {==}, plain.dup(cur)(pl))
    case R.KHt{}:
      fl.more(e, R.KHt{}, c, h, cur, out, ek, {==}, plain.dup(cur)(pl))
    case R.KCo{}:
      fl.more(e, R.KCo{}, c, h, cur, out, ek, {==}, plain.dup(cur)(pl))
    case R.KCm{}:
      fl.more(e, R.KCm{}, c, h, cur, out, ek, {==}, plain.dup(cur)(pl))
    case R.KDg{}:
      fl.more(e, R.KDg{}, c, h, cur, out, ek, {==}, plain.dup(cur)(pl))
    case R.KTk{}:
      fl.more(e, R.KTk{}, c, h, cur, out, ek, {==}, plain.dup(cur)(pl))
    case R.KVc{}:
      fl.more(e, R.KVc{}, c, h, cur, out, ek, {==}, plain.dup(cur)(pl))
    case R.KCt{}:
      fl.more(e, R.KCt{}, c, h, cur, out, ek, {==}, plain.dup(cur)(pl))

def STEP.field(+e: R.Ask, +c: U32, +h: R.Head, +cur: List<&2, U32>, +out: List<&2, U32>,
  pp: Plain(cur) & Plain(cur)) ->
  SG(e, S.line.byte(R.cls(c), c, cur, S.field.cr(e, h, S.field.view(e, cur)), x => S.MField{h, x}), out,
    R.step(e, R.feed(e, cur, R.P{R.Lin{h}, out}), c)):
  (p1, p2) = pp
  %Equal.sym(R.P, R.feed(e, cur, R.P{R.Lin{h}, out}), R.P{Rf(h, S.field.view(e, cur)), out},
    line.field(e, cur, h, out)(p1)) :
    SG(e, S.line.byte(R.cls(c), c, cur, S.field.cr(e, h, S.field.view(e, cur)), x => S.MField{h, x}), out,
      R.step(e, _, c))
  fl.k(e, R.cls(c), c, h, cur, out, {==}, p2)

# The other places
# ----------------

def STEP.eol(+e: R.Ask, k: R.Cls, +c: U32, +h: R.Head, +out: List<&2, U32>) ->
  INV(S.next.at(e, S.MEol{h}, k, c, out)) & {emb(e, S.next.at(e, S.MEol{h}, k, c, out)) ==
    R.step.at(e, R.Eol{h}, k, c, out) : R.P}:
  match k:
    case R.KSp{}:
      (Unit{}, {==})
    case R.KHt{}:
      (Unit{}, {==})
    case R.KCr{}:
      (Unit{}, {==})
    case R.KLf{}:
      (Unit{}, {==})
    case R.KCo{}:
      (Unit{}, {==})
    case R.KCm{}:
      (Unit{}, {==})
    case R.KDg{}:
      (Unit{}, {==})
    case R.KTk{}:
      (Unit{}, {==})
    case R.KVc{}:
      (Unit{}, {==})
    case R.KCt{}:
      (Unit{}, {==})

def fr.at(te: Bool, l: Maybe<&2, U32>, v10: Bool, x: Bool, nn: Bool) ->
  {S.frame.pick(S.frame.bad(te, l, v10), R.FBad{}, S.frame.pick(x, R.FNext{}, S.frame.pick(nn, R.FNone{},
    S.frame.pick(te, R.FChunked{}, S.frame.len(l))))) ==
    R.frame.at(R.frame.two(te, l) || (v10 && te), x, nn, te, l) : R.Frame}:
  match te l v10 x nn:
    case True{} None{} True{} True{} True{}:
      {==}
    case True{} None{} True{} True{} False{}:
      {==}
    case True{} None{} True{} False{} True{}:
      {==}
    case True{} None{} True{} False{} False{}:
      {==}
    case True{} None{} False{} True{} True{}:
      {==}
    case True{} None{} False{} True{} False{}:
      {==}
    case True{} None{} False{} False{} True{}:
      {==}
    case True{} None{} False{} False{} False{}:
      {==}
    case True{} Some{+n} True{} True{} True{}:
      {==}
    case True{} Some{+n} True{} True{} False{}:
      {==}
    case True{} Some{+n} True{} False{} True{}:
      {==}
    case True{} Some{+n} True{} False{} False{}:
      {==}
    case True{} Some{+n} False{} True{} True{}:
      {==}
    case True{} Some{+n} False{} True{} False{}:
      {==}
    case True{} Some{+n} False{} False{} True{}:
      {==}
    case True{} Some{+n} False{} False{} False{}:
      {==}
    case False{} None{} True{} True{} True{}:
      {==}
    case False{} None{} True{} True{} False{}:
      {==}
    case False{} None{} True{} False{} True{}:
      {==}
    case False{} None{} True{} False{} False{}:
      {==}
    case False{} None{} False{} True{} True{}:
      {==}
    case False{} None{} False{} True{} False{}:
      {==}
    case False{} None{} False{} False{} True{}:
      {==}
    case False{} None{} False{} False{} False{}:
      {==}
    case False{} Some{+n} True{} True{} True{}:
      {==}
    case False{} Some{+n} True{} True{} False{}:
      {==}
    case False{} Some{+n} True{} False{} True{}:
      {==}
    case False{} Some{+n} True{} False{} False{}:
      {==}
    case False{} Some{+n} False{} True{} True{}:
      {==}
    case False{} Some{+n} False{} True{} False{}:
      {==}
    case False{} Some{+n} False{} False{} True{}:
      {==}
    case False{} Some{+n} False{} False{} False{}:
      {==}


# the head's end: the two framings are one
def fr(e: R.Ask, h: R.Head) -> {S.framing(e, h) == R.frame(e, h) : R.Frame}:
  match e h:
    case R.Ask{+head, cap} R.Head{+v10, +code, +l, +te, cl, ka}:
      fr.at(te, l, v10, U32.is_lt(code, 200) && Bool.not(U32.is_eq(code, 101)),
        head || U32.is_lt(code, 200) || U32.is_eq(code, 204) || U32.is_eq(code, 304))

def HG(+e: R.Ask, w: S.W, p: R.P) -> Type:
  INV(w) & {emb(e, w) == p : R.P}

def hd.len(+e: R.Ask, z: Bool, +h: R.Head, +n: U32, +out: List<&2, U32>) ->
  HG(e, S.W{S.head.body(z, h, n), out}, R.P{R.head.len(z, h, n), out}):
  match z:
    case True{}:
      (Unit{}, Equal.cong(R.Resp, R.P, r => R.P{R.Fin{r, ""}, out}, S.resp(h, Nil{}, False{}),
        R.final(h, "", False{}), final.is(h, Nil{}, False{})))
    case False{}:
      (Unit{}, {==})

def hd.at(+e: R.Ask, f: R.Frame, h: R.Head, +out: List<&2, U32>) ->
  HG(e, S.head.at(e, f, h, out), R.head.at(e, f, h, R.head.code(h), out)):
  match f:
    case R.FBad{}:
      (Unit{}, {==})
    case R.FNext{}:
      match h:
        case R.Head{v10, code, l, te, cl, ka}:
          (Unit{}, {==})
    case R.FNone{}:
      (Unit{}, Equal.cong(R.Resp, R.P, r => R.P{R.Fin{r, ""}, out}, S.resp(h, Nil{}, False{}),
        R.final(h, "", False{}), final.is(h, Nil{}, False{})))
    case R.FLen{+n}:
      hd.len(e, U32.is_zero(n), h, n, out)
    case R.FChunked{}:
      (Unit{}, {==})
    case R.FClose{}:
      (Unit{}, {==})

def STEP.eoh.lf(+e: R.Ask, +h: R.Head, +out: List<&2, U32>) ->
  HG(e, S.head.done(e, h, out), R.head.end(e, h, out)):
  %fr(e, h) :
    HG(e, S.head.done(e, h, out), R.head.at(e, _, h, R.head.code(h), out))
  hd.at(e, S.framing(e, h), h, out)

def STEP.eoh(+e: R.Ask, k: R.Cls, +c: U32, +h: R.Head, +out: List<&2, U32>) ->
  HG(e, S.next.at(e, S.MEoh{h}, k, c, out), R.step.at(e, R.Eoh{h}, k, c, out)):
  match k:
    case R.KLf{}:
      STEP.eoh.lf(e, h, out)
    case R.KSp{}:
      (Unit{}, {==})
    case R.KHt{}:
      (Unit{}, {==})
    case R.KCr{}:
      (Unit{}, {==})
    case R.KCo{}:
      (Unit{}, {==})
    case R.KCm{}:
      (Unit{}, {==})
    case R.KDg{}:
      (Unit{}, {==})
    case R.KTk{}:
      (Unit{}, {==})
    case R.KVc{}:
      (Unit{}, {==})
    case R.KCt{}:
      (Unit{}, {==})

# bodies
def STEP.body(+e: R.Ask, more: Nat, +c: U32, +h: R.Head, +got: List<&2, U32>, +out: List<&2, U32>) ->
  HG(e, S.W{S.body.byte(more, c, h, got), out}, R.P{R.body.byte(more, c, h, Bytes.from_list(got)), out}):
  match more:
    case 0n:
      (Unit{}, Equal.cong(R.Resp, R.P, r => R.P{R.Fin{r, ""}, out}, S.resp(h, S.snoc(got, c), False{}),
        R.final(h, Bytes.push(Bytes.from_list(got), c), False{}), final.snoc(h, got, c, False{})))
    case 1n+q:
      (Unit{}, Equal.cong(Bytes(), R.P, b => R.P{R.Bod{h, q, b}, out}, Bytes.from_list(S.snoc(got, c)),
        Bytes.push(Bytes.from_list(got), c), fl_snoc(got, c)))

def STEP.data(+e: R.Ask, more: Nat, +c: U32, +h: R.Head, +got: List<&2, U32>, +left: U32, +out: List<&2, U32>) ->
  HG(e, S.W{S.data.byte(more, c, h, got, left), out}, R.P{R.data.byte(more, c, h, Bytes.from_list(got), left), out}):
  match more:
    case 0n:
      (Unit{}, Equal.cong(Bytes(), R.P, b => R.P{R.Chk{h, R.ADataCr{}, 0, b, left}, out},
        Bytes.from_list(S.snoc(got, c)), Bytes.push(Bytes.from_list(got), c), fl_snoc(got, c)))
    case 1n+q:
      (Unit{}, Equal.cong(Bytes(), R.P, b => R.P{R.Dat{h, q, b, left}, out}, Bytes.from_list(S.snoc(got, c)),
        Bytes.push(Bytes.from_list(got), c), fl_snoc(got, c)))

def STEP.close(+e: R.Ask, left: Nat, +c: U32, +h: R.Head, +got: List<&2, U32>, +out: List<&2, U32>) ->
  HG(e, S.W{S.close.byte(left, c, h, got), out}, R.P{R.close.byte(left, c, h, Bytes.from_list(got)), out}):
  match left:
    case 0n:
      (Unit{}, {==})
    case 1n+q:
      (Unit{}, Equal.cong(Bytes(), R.P, b => R.P{R.Clo{h, b, q}, out}, Bytes.from_list(S.snoc(got, c)),
        Bytes.push(Bytes.from_list(got), c), fl_snoc(got, c)))

# a chunk's framing
def ck.paid(+e: R.Ask, b: Bool, +h: R.Head, +at: R.At, +n: U32, +got: List<&2, U32>, +left: U32, +out: List<&2, U32>) ->
  HG(e, S.W{S.chunk.paid(b, h, at, n, got, left), out}, R.P{R.chunk.paid(b, h, at, n, Bytes.from_list(got), left), out}):
  match b:
    case True{}:
      (Unit{}, {==})
    case False{}:
      (Unit{}, {==})

def ck.line(+e: R.Ask, z: Bool, +h: R.Head, +n: U32, +got: List<&2, U32>, +left: U32, +out: List<&2, U32>) ->
  HG(e, S.W{S.chunk.line(z, h, n, got, left), out}, R.P{R.chunk.line(z, h, n, Bytes.from_list(got), left), out}):
  match z:
    case True{}:
      (Unit{}, {==})
    case False{}:
      (Unit{}, {==})

def STEP.chunk(+e: R.Ask, g: R.Go, +h: R.Head, +n: U32, +got: List<&2, U32>, +left: U32, +out: List<&2, U32>) ->
  HG(e, S.W{S.chunk.go(g, h, n, got, left), out}, R.P{R.chunk.go(g, h, n, Bytes.from_list(got), left), out}):
  match g:
    case R.GBad{}:
      (Unit{}, {==})
    case R.GTo{+at, paid}:
      match paid:
        case True{}:
          ck.paid(e, U32.is_le(left, n), h, at, n, got, left, out)
        case False{}:
          (Unit{}, {==})
    case R.GDigit{+d}:
      ck.paid(e, U32.is_le(left, (n * 16 + d : U32)), h, R.ASize{}, (n * 16 + d : U32), got, left, out)
    case R.GLine{}:
      ck.line(e, U32.is_zero(n), h, n, got, left, out)
    case R.GDone{}:
      (Unit{}, Equal.cong(R.Resp, R.P, r => R.P{R.Fin{r, ""}, out}, S.resp(h, got, False{}),
        R.final(h, Bytes.from_list(got), False{}), final.is(h, got, False{})))

# LEMMA: a byte keeps the walk and the reader where emb says
def STEP.m(+e: R.Ask, mode: S.Mode, +c: U32, +out: List<&2, U32>) ->
  INV.m(mode) -> HG(e, S.next.at(e, mode, R.cls(c), c, out), R.step(e, emb.m(e, mode, out), c)):
  match mode:
    case S.MStatus{+cur}:
      pl => STEP.status(e, c, cur, out, plain.dup(cur)(pl))
    case S.MField{+h, +cur}:
      pl => STEP.field(e, c, h, cur, out, plain.dup(cur)(pl))
    case S.MEol{+h}:
      i => STEP.eol(e, R.cls(c), c, h, out)
    case S.MEoh{+h}:
      i => STEP.eoh(e, R.cls(c), c, h, out)
    case S.MBody{+h, more, +got}:
      i => STEP.body(e, more, c, h, got, out)
    case S.MChunk{+h, +at, +n, +got, +left}:
      i => STEP.chunk(e, R.chunk.step(at, R.xk.of(R.cls(c), c)), h, n, got, left, out)
    case S.MData{+h, more, +got, +left}:
      i => STEP.data(e, more, c, h, got, left, out)
    case S.MClose{+h, +got, left}:
      i => STEP.close(e, left, c, h, got, out)
    case S.MDone{r, +rest}:
      i => (Unit{}, Equal.cong(Bytes(), R.P, b => R.P{R.Fin{r, b}, out}, Bytes.from_list(S.snoc(rest, c)),
        Bytes.push(Bytes.from_list(rest), c), fl_snoc(rest, c)))
    case S.MBad{}:
      i => (Unit{}, {==})

def STEP(+e: R.Ask, w: S.W, +c: U32) -> INV(w) -> HG(e, S.next(e, w, c), R.step(e, emb(e, w), c)):
  match w:
    case S.W{mode, +out}:
      STEP.m(e, mode, c, out)

# LEMMA: where the walk stops, the reader agrees with it
def end.status(v: S.SView) -> {R.look.st(Rs(v)) == S.status.end(v) : R.End}:
  match v:
    case S.VVer{x}:
      {==}
    case S.VCode{v10, d}:
      {==}
    case S.VWhy{v10, code}:
      {==}
    case S.VBad{}:
      {==}

def end.field(+h: R.Head, v: S.FLine) -> {R.look.st(Rf(h, v)) == S.field.end(v) : R.End}:
  match v:
    case S.FEmpty{}:
      {==}
    case S.FName{n}:
      {==}
    case S.FVal{val}:
      match val:
        case S.VLen0{}:
          {==}
        case S.VLen{n, ws}:
          match ws:
            case False{}:
              {==}
            case True{}:
              {==}
        case S.VTe0{}:
          {==}
        case S.VTe{t}:
          {==}
        case S.VConn{d, cur}:
          {==}
        case S.VSkip{}:
          {==}
    case S.FBad{}:
      {==}

def END.m(+e: R.Ask, mode: S.Mode, +out: List<&2, U32>) ->
  INV.m(mode) -> {R.look(emb.m(e, mode, out)) == R.Look{List.reverse(&2, U32, out), S.finish.end(e, mode)} : R.Look}:
  match mode:
    case S.MStatus{+cur}:
      pl =>
        %Equal.sym(R.P, R.feed(e, cur, R.P{R.st.new(), out}), R.P{Rs(S.status.view(cur)), out},
          line.status(e, cur, out)(pl)) :
          {R.look(_) == R.Look{List.reverse(&2, U32, out), S.finish.end(e, S.MStatus{cur})} : R.Look}
        Equal.cong(R.End, R.Look, x => R.Look{List.reverse(&2, U32, out), x}, R.look.st(Rs(S.status.view(cur))),
          S.status.end(S.status.view(cur)), end.status(S.status.view(cur)))
    case S.MField{+h, +cur}:
      pl =>
        %Equal.sym(R.P, R.feed(e, cur, R.P{R.Lin{h}, out}), R.P{Rf(h, S.field.view(e, cur)), out},
          line.field(e, cur, h, out)(pl)) :
          {R.look(_) == R.Look{List.reverse(&2, U32, out), S.finish.end(e, S.MField{h, cur})} : R.Look}
        Equal.cong(R.End, R.Look, x => R.Look{List.reverse(&2, U32, out), x}, R.look.st(Rf(h, S.field.view(e, cur))),
          S.field.end(S.field.view(e, cur)), end.field(h, S.field.view(e, cur)))
    case S.MEol{h}:
      i => {==}
    case S.MEoh{h}:
      i => {==}
    case S.MBody{h, more, got}:
      i => {==}
    case S.MChunk{h, at, n, got, left}:
      i => {==}
    case S.MData{h, more, got, left}:
      i => {==}
    case S.MClose{+h, +got, left}:
      i => Equal.cong(R.Resp, R.Look, r => R.Look{List.reverse(&2, U32, out), R.Closing{r}},
        R.final(h, Bytes.from_list(got), True{}), S.resp(h, got, True{}),
        Equal.sym(R.Resp, S.resp(h, got, True{}), R.final(h, Bytes.from_list(got), True{}), final.is(h, got, True{})))
    case S.MDone{r, rest}:
      i => {==}
    case S.MBad{}:
      i => {==}

def END(+e: R.Ask, w: S.W) -> INV(w) -> {R.look(emb(e, w)) == S.finish(e, w) : R.Look}:
  match w:
    case S.W{mode, +out}:
      END.m(e, mode, out)

def walk.step(+e: R.Ask, t: List<&2, U32>, +w: S.W, +c: U32, g: HG(e, S.next(e, w, c), R.step(e, emb(e, w), c)),
  ih: @+w2: S.W -> INV(w2) -> {R.look(R.feed(e, t, emb(e, w2))) == S.finish(e, S.walk(e, t, w2)) : R.Look}) ->
  {R.look(R.feed(e, t, R.step(e, emb(e, w), c))) == S.finish(e, S.walk(e, t, S.next(e, w, c))) : R.Look}:
  (i2, eq) = g
  %eq : {R.look(R.feed(e, t, _)) == S.finish(e, S.walk(e, t, S.next(e, w, c))) : R.Look}
  ih(S.next(e, w, c))(i2)

# the walk: induction on the input, one byte at a time
def walk.lem(+e: R.Ask, bs: List<&2, U32>, +w: S.W) ->
  INV(w) -> {R.look(R.feed(e, bs, emb(e, w))) == S.finish(e, S.walk(e, bs, w)) : R.Look}:
  match bs:
    case Nil{}:
      i => END(e, w)(i)
    case Con{+c, +t}:
      i => walk.step(e, t, w, c, STEP(e, w, c)(i), w2 => walk.lem(e, t, w2))

# THEOREM: for every input, the reader reads what the spec reads
def resp.sim(+e: R.Ask, bs: List<&2, U32>) -> {R.look(R.feed(e, bs, R.p.new())) == S.response(e, bs) : R.Look}:
  walk.lem(e, bs, S.w.new())(Unit{})


# The block walk
# ==============
#
# Each move of R.adv lands where stepping its bytes one at a time does:
# a run of body, of chunk data, of a close-delimited body, or of what
# follows the final response, taken whole; every other state steps one
# byte. That is the kit's obligation (adv_ok), and with it every law of
# feed is a law of feed_buf and of a connection's reads.

def last(+e: R.Ask, q: R.P & Bytes()) -> R.P:
  Wr.feed_buf.last(~R.Ask, ~R.P, ~R.wstep, e, q)

def slow(+e: R.Ask, s: Bytes(), p: R.P) -> R.P:
  Wr.feed_buf.slow(~R.Ask, ~R.P, ~R.wstep, e, s, p)

def app_bnil(a: Bytes()) -> {Bytes.append(a, "") == a : Bytes()}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      %app_bnil(t) : {SCon{h, Bytes.append(t, "")} == SCon{h, _} : Bytes()}
      {==}

def app_assoc(a: Bytes(), -b: Bytes(), -c: Bytes()) ->
  {Bytes.append(Bytes.append(a, b), c) == Bytes.append(a, Bytes.append(b, c)) : Bytes()}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      %app_assoc(t, b, c) : {SCon{h, Bytes.append(Bytes.append(t, b), c)} == SCon{h, _} : Bytes()}
      {==}

def push_app(acc: Bytes(), -c: U32, -x: Bytes()) ->
  {Bytes.append(Bytes.push(acc, c), x) == Bytes.append(acc, SCon{Chr{c}, x}) : Bytes()}:
  app_assoc(acc, SCon{Chr{c}, SNil{}}, x)

def take0(t: Bytes()) -> {String.take(t, 0n) == "" : Bytes()}:
  match t:
    case SNil{}:
      {==}
    case SCon{h, u}:
      {==}

def drop0(t: Bytes()) -> {String.drop(t, 0n) == t : Bytes()}:
  match t:
    case SNil{}:
      {==}
    case SCon{h, u}:
      {==}

def len_shift(t: Bytes()) -> {String.length.go(t, 1n) == 1n+String.length.go(t, 0n) : Nat}:
  Bytes.len.shift(t, 0n)

def lem.one(+e: R.Ask, p: R.P, s: Bytes()) -> {last(e, R.one(e, p, s)) == slow(e, s, p) : R.P}:
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{c}, t}:
      {==}

# a body
def lem.bod.at(+e: R.Ask, +q: Nat, +h: R.Head, +b: Bytes(), +c: U32, +t: Bytes(), +out: List<&2, U32>, d: Bool) ->
  {last(e, R.bod.at(1n+q, h, b, SCon{Chr{c}, t}, out, d)) == last(e, R.bod.at(q, h, Bytes.push(b, c), t, out, d)) : R.P}:
  match d:
    case False{}:
      %Equal.sym(Nat, String.length.go(t, 1n), 1n+String.length.go(t, 0n), len_shift(t)) :
        {R.P{R.Bod{h, Nat.sub(1n+q, _), Bytes.append(b, SCon{Chr{c}, t})}, out} ==
          R.P{R.Bod{h, Nat.sub(q, String.length.go(t, 0n)), Bytes.append(Bytes.push(b, c), t)}, out} : R.P}
      %push_app(b, c, t) :
        {R.P{R.Bod{h, Nat.sub(q, String.length.go(t, 0n)), _}, out} ==
          R.P{R.Bod{h, Nat.sub(q, String.length.go(t, 0n)), Bytes.append(Bytes.push(b, c), t)}, out} : R.P}
      {==}
    case True{}:
      %push_app(b, c, String.take(t, 1n+q)) :
        {slow(e, String.drop(t, 1n+q), R.P{R.Fin{R.final(h, _, False{}), ""}, out}) ==
          slow(e, String.drop(t, 1n+q),
            R.P{R.Fin{R.final(h, Bytes.append(Bytes.push(b, c), String.take(t, 1n+q)), False{}), ""}, out}) : R.P}
      {==}

def lem.bod(+e: R.Ask, +s: Bytes(), +r: Nat, +h: R.Head, +b: Bytes(), +out: List<&2, U32>) ->
  {last(e, R.bod.at(r, h, b, s, out, Nat.is_lt(r, Bytes.len(s)))) == slow(e, s, R.P{R.Bod{h, r, b}, out}) : R.P}:
  match s r:
    case SNil{} 0n:
      %Equal.sym(Bytes(), Bytes.append(b, ""), b, app_bnil(b)) :
        {R.P{R.Bod{h, 0n, _}, out} == R.P{R.Bod{h, 0n, b}, out} : R.P}
      {==}
    case SNil{} 1n+q:
      %Equal.sym(Bytes(), Bytes.append(b, ""), b, app_bnil(b)) :
        {R.P{R.Bod{h, 1n+q, _}, out} == R.P{R.Bod{h, 1n+q, b}, out} : R.P}
      {==}
    case SCon{Chr{c}, t} 0n:
      %Equal.sym(Nat, String.length.go(t, 1n), 1n+String.length.go(t, 0n), len_shift(t)) :
        {last(e, R.bod.at(0n, h, b, SCon{Chr{c}, t}, out, Nat.is_lt(0n, _))) ==
          slow(e, t, R.P{R.Fin{R.final(h, Bytes.push(b, c), False{}), ""}, out}) : R.P}
      %Equal.sym(Bytes(), String.take(t, 0n), "", take0(t)) :
        {slow(e, String.drop(t, 0n), R.P{R.Fin{R.final(h, Bytes.append(b, SCon{Chr{c}, _}), False{}), ""}, out}) ==
          slow(e, t, R.P{R.Fin{R.final(h, Bytes.push(b, c), False{}), ""}, out}) : R.P}
      %Equal.sym(Bytes(), String.drop(t, 0n), t, drop0(t)) :
        {slow(e, _, R.P{R.Fin{R.final(h, Bytes.push(b, c), False{}), ""}, out}) ==
          slow(e, t, R.P{R.Fin{R.final(h, Bytes.push(b, c), False{}), ""}, out}) : R.P}
      {==}
    case SCon{Chr{c}, t} 1n+q:
      %Equal.sym(Nat, String.length.go(t, 1n), 1n+String.length.go(t, 0n), len_shift(t)) :
        {last(e, R.bod.at(1n+q, h, b, SCon{Chr{c}, t}, out, Nat.is_lt(1n+q, _))) ==
          slow(e, t, R.P{R.Bod{h, q, Bytes.push(b, c)}, out}) : R.P}
      Equal.trans(R.P,
        last(e, R.bod.at(1n+q, h, b, SCon{Chr{c}, t}, out, Nat.is_lt(q, String.length.go(t, 0n)))),
        last(e, R.bod.at(q, h, Bytes.push(b, c), t, out, Nat.is_lt(q, String.length.go(t, 0n)))),
        slow(e, t, R.P{R.Bod{h, q, Bytes.push(b, c)}, out}),
        lem.bod.at(e, q, h, b, c, t, out, Nat.is_lt(q, String.length.go(t, 0n))),
        lem.bod(e, t, q, h, Bytes.push(b, c), out))

# a chunk's data
def lem.dat.at(+e: R.Ask, +q: Nat, +h: R.Head, +b: Bytes(), +c: U32, +t: Bytes(), +left: U32, +out: List<&2, U32>,
  d: Bool) ->
  {last(e, R.dat.at(1n+q, h, b, SCon{Chr{c}, t}, left, out, d)) ==
    last(e, R.dat.at(q, h, Bytes.push(b, c), t, left, out, d)) : R.P}:
  match d:
    case False{}:
      %Equal.sym(Nat, String.length.go(t, 1n), 1n+String.length.go(t, 0n), len_shift(t)) :
        {R.P{R.Dat{h, Nat.sub(1n+q, _), Bytes.append(b, SCon{Chr{c}, t}), left}, out} ==
          R.P{R.Dat{h, Nat.sub(q, String.length.go(t, 0n)), Bytes.append(Bytes.push(b, c), t), left}, out} : R.P}
      %push_app(b, c, t) :
        {R.P{R.Dat{h, Nat.sub(q, String.length.go(t, 0n)), _, left}, out} ==
          R.P{R.Dat{h, Nat.sub(q, String.length.go(t, 0n)), Bytes.append(Bytes.push(b, c), t), left}, out} : R.P}
      {==}
    case True{}:
      %push_app(b, c, String.take(t, 1n+q)) :
        {slow(e, String.drop(t, 1n+q), R.P{R.Chk{h, R.ADataCr{}, 0, _, left}, out}) ==
          slow(e, String.drop(t, 1n+q),
            R.P{R.Chk{h, R.ADataCr{}, 0, Bytes.append(Bytes.push(b, c), String.take(t, 1n+q)), left}, out}) : R.P}
      {==}

def lem.dat(+e: R.Ask, +s: Bytes(), +r: Nat, +h: R.Head, +b: Bytes(), +left: U32, +out: List<&2, U32>) ->
  {last(e, R.dat.at(r, h, b, s, left, out, Nat.is_lt(r, Bytes.len(s)))) ==
    slow(e, s, R.P{R.Dat{h, r, b, left}, out}) : R.P}:
  match s r:
    case SNil{} 0n:
      %Equal.sym(Bytes(), Bytes.append(b, ""), b, app_bnil(b)) :
        {R.P{R.Dat{h, 0n, _, left}, out} == R.P{R.Dat{h, 0n, b, left}, out} : R.P}
      {==}
    case SNil{} 1n+q:
      %Equal.sym(Bytes(), Bytes.append(b, ""), b, app_bnil(b)) :
        {R.P{R.Dat{h, 1n+q, _, left}, out} == R.P{R.Dat{h, 1n+q, b, left}, out} : R.P}
      {==}
    case SCon{Chr{c}, t} 0n:
      %Equal.sym(Nat, String.length.go(t, 1n), 1n+String.length.go(t, 0n), len_shift(t)) :
        {last(e, R.dat.at(0n, h, b, SCon{Chr{c}, t}, left, out, Nat.is_lt(0n, _))) ==
          slow(e, t, R.P{R.Chk{h, R.ADataCr{}, 0, Bytes.push(b, c), left}, out}) : R.P}
      %Equal.sym(Bytes(), String.take(t, 0n), "", take0(t)) :
        {slow(e, String.drop(t, 0n), R.P{R.Chk{h, R.ADataCr{}, 0, Bytes.append(b, SCon{Chr{c}, _}), left}, out}) ==
          slow(e, t, R.P{R.Chk{h, R.ADataCr{}, 0, Bytes.push(b, c), left}, out}) : R.P}
      %Equal.sym(Bytes(), String.drop(t, 0n), t, drop0(t)) :
        {slow(e, _, R.P{R.Chk{h, R.ADataCr{}, 0, Bytes.push(b, c), left}, out}) ==
          slow(e, t, R.P{R.Chk{h, R.ADataCr{}, 0, Bytes.push(b, c), left}, out}) : R.P}
      {==}
    case SCon{Chr{c}, t} 1n+q:
      %Equal.sym(Nat, String.length.go(t, 1n), 1n+String.length.go(t, 0n), len_shift(t)) :
        {last(e, R.dat.at(1n+q, h, b, SCon{Chr{c}, t}, left, out, Nat.is_lt(1n+q, _))) ==
          slow(e, t, R.P{R.Dat{h, q, Bytes.push(b, c), left}, out}) : R.P}
      Equal.trans(R.P,
        last(e, R.dat.at(1n+q, h, b, SCon{Chr{c}, t}, left, out, Nat.is_lt(q, String.length.go(t, 0n)))),
        last(e, R.dat.at(q, h, Bytes.push(b, c), t, left, out, Nat.is_lt(q, String.length.go(t, 0n)))),
        slow(e, t, R.P{R.Dat{h, q, Bytes.push(b, c), left}, out}),
        lem.dat.at(e, q, h, b, c, t, left, out, Nat.is_lt(q, String.length.go(t, 0n))),
        lem.dat(e, t, q, h, Bytes.push(b, c), left, out))

# refused, and after the final response
def lem.bad(+e: R.Ask, s: Bytes(), -out: List<&2, U32>) -> {slow(e, s, R.P{R.Bad{}, out}) == R.P{R.Bad{}, out} : R.P}:
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{c}, t}:
      lem.bad(e, t, out)

def lem.rest(+e: R.Ask, +s: Bytes(), -r: R.Resp, +bs: Bytes(), -out: List<&2, U32>) ->
  {slow(e, s, R.P{R.Fin{r, bs}, out}) == R.P{R.Fin{r, Bytes.append(bs, s)}, out} : R.P}:
  match s:
    case SNil{}:
      %Equal.sym(Bytes(), Bytes.append(bs, ""), bs, app_bnil(bs)) :
        {R.P{R.Fin{r, bs}, out} == R.P{R.Fin{r, _}, out} : R.P}
      {==}
    case SCon{Chr{c}, t}:
      %push_app(bs, c, t) : {slow(e, t, R.P{R.Fin{r, Bytes.push(bs, c)}, out}) == R.P{R.Fin{r, _}, out} : R.P}
      lem.rest(e, t, r, Bytes.push(bs, c), out)

# a body that runs to the close
def lem.clo.at(+e: R.Ask, +q: Nat, +h: R.Head, +b: Bytes(), +c: U32, +t: Bytes(), +out: List<&2, U32>, d: Bool) ->
  {last(e, R.clo.at(h, b, SCon{Chr{c}, t}, 1n+q, out, d)) == last(e, R.clo.at(h, Bytes.push(b, c), t, q, out, d)) : R.P}:
  match d:
    case True{}:
      %Equal.sym(Nat, String.length.go(t, 1n), 1n+String.length.go(t, 0n), len_shift(t)) :
        {R.P{R.Clo{h, Bytes.append(b, SCon{Chr{c}, t}), Nat.sub(1n+q, _)}, out} ==
          R.P{R.Clo{h, Bytes.append(Bytes.push(b, c), t), Nat.sub(q, String.length.go(t, 0n))}, out} : R.P}
      %push_app(b, c, t) :
        {R.P{R.Clo{h, _, Nat.sub(q, String.length.go(t, 0n))}, out} ==
          R.P{R.Clo{h, Bytes.append(Bytes.push(b, c), t), Nat.sub(q, String.length.go(t, 0n))}, out} : R.P}
      {==}
    case False{}:
      {==}

def lem.clo(+e: R.Ask, +s: Bytes(), +h: R.Head, +b: Bytes(), +left: Nat, +out: List<&2, U32>) ->
  {last(e, R.clo.at(h, b, s, left, out, Nat.is_le(Bytes.len(s), left))) == slow(e, s, R.P{R.Clo{h, b, left}, out}) : R.P}:
  match s left:
    case SNil{} 0n:
      %Equal.sym(Bytes(), Bytes.append(b, ""), b, app_bnil(b)) :
        {R.P{R.Clo{h, _, 0n}, out} == R.P{R.Clo{h, b, 0n}, out} : R.P}
      {==}
    case SNil{} 1n+q:
      %Equal.sym(Bytes(), Bytes.append(b, ""), b, app_bnil(b)) :
        {R.P{R.Clo{h, _, 1n+q}, out} == R.P{R.Clo{h, b, 1n+q}, out} : R.P}
      {==}
    case SCon{Chr{c}, t} 0n:
      %Equal.sym(Nat, String.length.go(t, 1n), 1n+String.length.go(t, 0n), len_shift(t)) :
        {last(e, R.clo.at(h, b, SCon{Chr{c}, t}, 0n, out, Nat.is_le(_, 0n))) ==
          slow(e, t, R.P{R.Bad{}, out}) : R.P}
      Equal.sym(R.P, slow(e, t, R.P{R.Bad{}, out}), R.P{R.Bad{}, out}, lem.bad(e, t, out))
    case SCon{Chr{c}, t} 1n+q:
      %Equal.sym(Nat, String.length.go(t, 1n), 1n+String.length.go(t, 0n), len_shift(t)) :
        {last(e, R.clo.at(h, b, SCon{Chr{c}, t}, 1n+q, out, Nat.is_le(_, 1n+q))) ==
          slow(e, t, R.P{R.Clo{h, Bytes.push(b, c), q}, out}) : R.P}
      Equal.trans(R.P,
        last(e, R.clo.at(h, b, SCon{Chr{c}, t}, 1n+q, out, Nat.is_le(String.length.go(t, 0n), q))),
        last(e, R.clo.at(h, Bytes.push(b, c), t, q, out, Nat.is_le(String.length.go(t, 0n), q))),
        slow(e, t, R.P{R.Clo{h, Bytes.push(b, c), q}, out}),
        lem.clo.at(e, q, h, b, c, t, out, Nat.is_le(String.length.go(t, 0n), q)),
        lem.clo(e, t, h, Bytes.push(b, c), q, out))

# every move
def lem.adv.at(+e: R.Ask, st: R.St, +s: Bytes(), +out: List<&2, U32>) ->
  {last(e, R.adv.at(e, st, s, out)) == slow(e, s, R.P{st, out}) : R.P}:
  match st:
    case R.Bod{+h, +r, +b}:
      lem.bod(e, s, r, h, b, out)
    case R.Dat{+h, +r, +b, +left}:
      lem.dat(e, s, r, h, b, left, out)
    case R.Clo{+h, +b, +left}:
      lem.clo(e, s, h, b, left, out)
    case R.Fin{+r, +rest}:
      Equal.sym(R.P, slow(e, s, R.P{R.Fin{r, rest}, out}), R.P{R.Fin{r, Bytes.append(rest, s)}, out},
        lem.rest(e, s, r, rest, out))
    case R.Bad{}:
      Equal.sym(R.P, slow(e, s, R.P{R.Bad{}, out}), R.P{R.Bad{}, out}, lem.bad(e, s, out))
    case R.SVer{a, b}:
      lem.one(e, R.P{R.SVer{a, b}, out}, s)
    case R.SCode{v10, n, k}:
      lem.one(e, R.P{R.SCode{v10, n, k}, out}, s)
    case R.SWhy{v10, code}:
      lem.one(e, R.P{R.SWhy{v10, code}, out}, s)
    case R.Eol{h}:
      lem.one(e, R.P{R.Eol{h}, out}, s)
    case R.Lin{h}:
      lem.one(e, R.P{R.Lin{h}, out}, s)
    case R.Nam{h, a, b, d}:
      lem.one(e, R.P{R.Nam{h, a, b, d}, out}, s)
    case R.Oth{h}:
      lem.one(e, R.P{R.Oth{h}, out}, s)
    case R.Len0{h}:
      lem.one(e, R.P{R.Len0{h}, out}, s)
    case R.Len{h, n}:
      lem.one(e, R.P{R.Len{h, n}, out}, s)
    case R.LenW{h, n}:
      lem.one(e, R.P{R.LenW{h, n}, out}, s)
    case R.Te0{h}:
      lem.one(e, R.P{R.Te0{h}, out}, s)
    case R.Te{h, m}:
      lem.one(e, R.P{R.Te{h, m}, out}, s)
    case R.Conn{h, cl, ka, mc, mk}:
      lem.one(e, R.P{R.Conn{h, cl, ka, mc, mk}, out}, s)
    case R.Eoh{h}:
      lem.one(e, R.P{R.Eoh{h}, out}, s)
    case R.Chk{h, at, n, got, left}:
      lem.one(e, R.P{R.Chk{h, at, n, got, left}, out}, s)

# the kit's obligation: every move lands where stepping its bytes does
def adv_ok(+e: R.Ask, +s: Bytes(), p: R.P) ->
  {Wr.feed_buf.last(~R.Ask, ~R.P, ~R.wstep, e, R.wadv(e, s, p)) ==
    Wr.feed_buf.slow(~R.Ask, ~R.P, ~R.wstep, e, s, p) : R.P}:
  match p:
    case R.P{st, +out}:
      lem.adv.at(e, st, s, out)


# Taking the body
# ===============
#
# The kit's obligations of take, give and open (resp.bend), for
# drain_reads: only an open state holds body bytes, an open state steps
# to an open one, and a byte stepped with bytes put back in front of an
# open state's body lands with them still in front.

def t.app_nil(+a: Bytes()) -> {Bytes.append(a, "") == a : Bytes()}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.cong(Bytes(), Bytes(), x => SCon{h, x}, Bytes.append(t, ""), t, t.app_nil(t))

def t.app_assoc(+a: Bytes(), +b: Bytes(), +c: Bytes()) ->
  {Bytes.append(Bytes.append(a, b), c) == Bytes.append(a, Bytes.append(b, c)) : Bytes()}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.cong(Bytes(), Bytes(), x => SCon{h, x}, Bytes.append(Bytes.append(t, b), c),
        Bytes.append(t, Bytes.append(b, c)), t.app_assoc(t, b, c))

# a byte pushed after bytes put in front
def t.push_give(+x: Bytes(), +got: Bytes(), +c: U32) ->
  {Bytes.push(Bytes.append(x, got), c) == Bytes.append(x, Bytes.push(got, c)) : Bytes()}:
  t.app_assoc(x, got, SCon{Chr{c}, SNil{}})

def t.give_final(+x: Bytes(), h: R.Head, +b: Bytes(), +d: Bool) ->
  {R.resp.give(x, R.final(h, b, d)) == R.final(h, Bytes.append(x, b), d) : R.Resp}:
  match h:
    case R.Head{v10, code, len, te, close, ka}:
      {==}

def t.give_nil.st(st: R.St, +out: List<&2, U32>) ->
  {R.P{R.st.give("", st), out} == R.P{st, out} : R.P}:
  match st:
    case R.SVer{a, b}:
      {==}
    case R.SCode{v10, n, k}:
      {==}
    case R.SWhy{v10, code}:
      {==}
    case R.Eol{h}:
      {==}
    case R.Lin{h}:
      {==}
    case R.Nam{h, cl, te, co}:
      {==}
    case R.Oth{h}:
      {==}
    case R.Len0{h}:
      {==}
    case R.Len{h, n}:
      {==}
    case R.LenW{h, n}:
      {==}
    case R.Te0{h}:
      {==}
    case R.Te{h, m}:
      {==}
    case R.Conn{h, cl, ka, mc, mk}:
      {==}
    case R.Eoh{h}:
      {==}
    case R.Bod{h, more, got}:
      {==}
    case R.Chk{h, at, n, got, left}:
      {==}
    case R.Dat{h, more, got, left}:
      {==}
    case R.Clo{h, got, left}:
      {==}
    case R.Fin{r, rest}:
      match r:
        case R.Resp{code, v10, close, body}:
          {==}
    case R.Bad{}:
      {==}

def t.give_nil(+p: R.P) -> {R.give("", p) == p : R.P}:
  match p:
    case R.P{st, +out}:
      t.give_nil.st(st, out)

def t.give_app.st(+a: Bytes(), +b: Bytes(), st: R.St, +out: List<&2, U32>) ->
  {R.P{R.st.give(Bytes.append(a, b), st), out} == R.P{R.st.give(a, R.st.give(b, st)), out} : R.P}:
  match st:
    case R.SVer{+a, +b}:
      {==}
    case R.SCode{+v10, +n, +k}:
      {==}
    case R.SWhy{+v10, +code}:
      {==}
    case R.Eol{+h}:
      {==}
    case R.Lin{+h}:
      {==}
    case R.Nam{+h, +cl, +te, +co}:
      {==}
    case R.Oth{+h}:
      {==}
    case R.Len0{+h}:
      {==}
    case R.Len{+h, +n}:
      {==}
    case R.LenW{+h, +n}:
      {==}
    case R.Te0{+h}:
      {==}
    case R.Te{+h, +m}:
      {==}
    case R.Conn{+h, +cl, +ka, +mc, +mk}:
      {==}
    case R.Eoh{+h}:
      {==}
    case R.Bod{+h, +more, +got}:
      Equal.cong(Bytes(), R.P, y => R.P{R.Bod{h, more, y}, out},
        Bytes.append(Bytes.append(a, b), got), Bytes.append(a, Bytes.append(b, got)),
        t.app_assoc(a, b, got))
    case R.Chk{+h, +at, +n, +got, +left}:
      Equal.cong(Bytes(), R.P, y => R.P{R.Chk{h, at, n, y, left}, out},
        Bytes.append(Bytes.append(a, b), got), Bytes.append(a, Bytes.append(b, got)),
        t.app_assoc(a, b, got))
    case R.Dat{+h, +more, +got, +left}:
      Equal.cong(Bytes(), R.P, y => R.P{R.Dat{h, more, y, left}, out},
        Bytes.append(Bytes.append(a, b), got), Bytes.append(a, Bytes.append(b, got)),
        t.app_assoc(a, b, got))
    case R.Clo{+h, +got, +left}:
      Equal.cong(Bytes(), R.P, y => R.P{R.Clo{h, y, left}, out},
        Bytes.append(Bytes.append(a, b), got), Bytes.append(a, Bytes.append(b, got)),
        t.app_assoc(a, b, got))
    case R.Fin{+r, +rest}:
      match r:
        case R.Resp{code, v10, close, +body}:
          Equal.cong(Bytes(), R.P, y => R.P{R.Fin{R.Resp{code, v10, close, y}, rest}, out},
            Bytes.append(Bytes.append(a, b), body), Bytes.append(a, Bytes.append(b, body)),
            t.app_assoc(a, b, body))
    case R.Bad{}:
      {==}

def t.give_app(+a: Bytes(), +b: Bytes(), +p: R.P) ->
  {R.give(Bytes.append(a, b), p) == R.give(a, R.give(b, p)) : R.P}:
  match p:
    case R.P{st, +out}:
      t.give_app.st(a, b, st, out)

def t.give_take.st(st: R.St, +out: List<&2, U32>) ->
  {R.give(Wr.drain.b(R.P, R.take.at(R.st.take(st), out)),
    Wr.drain.s(R.P, R.take.at(R.st.take(st), out))) == R.P{st, out} : R.P}:
  match st:
    case R.SVer{+a, +b}:
      {==}
    case R.SCode{+v10, +n, +k}:
      {==}
    case R.SWhy{+v10, +code}:
      {==}
    case R.Eol{+h}:
      {==}
    case R.Lin{+h}:
      {==}
    case R.Nam{+h, +cl, +te, +co}:
      {==}
    case R.Oth{+h}:
      {==}
    case R.Len0{+h}:
      {==}
    case R.Len{+h, +n}:
      {==}
    case R.LenW{+h, +n}:
      {==}
    case R.Te0{+h}:
      {==}
    case R.Te{+h, +m}:
      {==}
    case R.Conn{+h, +cl, +ka, +mc, +mk}:
      {==}
    case R.Eoh{+h}:
      {==}
    case R.Bod{+h, +more, +got}:
      Equal.cong(Bytes(), R.P, y => R.P{R.Bod{h, more, y}, out},
        Bytes.append(got, ""), got, t.app_nil(got))
    case R.Chk{+h, +at, +n, +got, +left}:
      Equal.cong(Bytes(), R.P, y => R.P{R.Chk{h, at, n, y, left}, out},
        Bytes.append(got, ""), got, t.app_nil(got))
    case R.Dat{+h, +more, +got, +left}:
      Equal.cong(Bytes(), R.P, y => R.P{R.Dat{h, more, y, left}, out},
        Bytes.append(got, ""), got, t.app_nil(got))
    case R.Clo{+h, +got, +left}:
      Equal.cong(Bytes(), R.P, y => R.P{R.Clo{h, y, left}, out},
        Bytes.append(got, ""), got, t.app_nil(got))
    case R.Fin{+r, +rest}:
      match r:
        case R.Resp{code, v10, close, +body}:
          Equal.cong(Bytes(), R.P, y => R.P{R.Fin{R.Resp{code, v10, close, y}, rest}, out},
            Bytes.append(body, ""), body, t.app_nil(body))
    case R.Bad{}:
      {==}

def t.give_take(+p: R.P) ->
  {R.give(Wr.drain.b(R.P, R.take(p)), Wr.drain.s(R.P, R.take(p))) == p : R.P}:
  match p:
    case R.P{st, +out}:
      t.give_take.st(st, out)

def t.take_open.st(st: R.St, +out: List<&2, U32>) ->
  {R.open(Wr.drain.s(R.P, R.take.at(R.st.take(st), out))) == R.st.open(st) : Bool}:
  match st:
    case R.SVer{a, b}:
      {==}
    case R.SCode{v10, n, k}:
      {==}
    case R.SWhy{v10, code}:
      {==}
    case R.Eol{h}:
      {==}
    case R.Lin{h}:
      {==}
    case R.Nam{h, cl, te, co}:
      {==}
    case R.Oth{h}:
      {==}
    case R.Len0{h}:
      {==}
    case R.Len{h, n}:
      {==}
    case R.LenW{h, n}:
      {==}
    case R.Te0{h}:
      {==}
    case R.Te{h, m}:
      {==}
    case R.Conn{h, cl, ka, mc, mk}:
      {==}
    case R.Eoh{h}:
      {==}
    case R.Bod{h, more, got}:
      {==}
    case R.Chk{h, at, n, got, left}:
      {==}
    case R.Dat{h, more, got, left}:
      {==}
    case R.Clo{h, got, left}:
      {==}
    case R.Fin{r, rest}:
      match r:
        case R.Resp{code, v10, close, body}:
          {==}
    case R.Bad{}:
      {==}

def t.take_open(+p: R.P) -> {R.open(Wr.drain.s(R.P, R.take(p))) == R.open(p) : Bool}:
  match p:
    case R.P{st, +out}:
      t.take_open.st(st, out)

def t.shut_take.st(st: R.St, +out: List<&2, U32>, o: {R.st.open(st) == False{} : Bool}) ->
  {Wr.drain.b(R.P, R.take.at(R.st.take(st), out)) == "" : Bytes()}:
  match st:
    case R.SVer{a, b}:
      {==}
    case R.SCode{v10, n, k}:
      {==}
    case R.SWhy{v10, code}:
      {==}
    case R.Eol{h}:
      {==}
    case R.Lin{h}:
      {==}
    case R.Nam{h, cl, te, co}:
      {==}
    case R.Oth{h}:
      {==}
    case R.Len0{h}:
      {==}
    case R.Len{h, n}:
      {==}
    case R.LenW{h, n}:
      {==}
    case R.Te0{h}:
      {==}
    case R.Te{h, m}:
      {==}
    case R.Conn{h, cl, ka, mc, mk}:
      {==}
    case R.Eoh{h}:
      {==}
    case R.Bod{h, more, got}:
      no2({Wr.drain.b(R.P, R.take.at(R.st.take(R.Bod{h, more, got}), out)) == "" : Bytes()}, o)
    case R.Chk{h, at, n, got, left}:
      no2({Wr.drain.b(R.P, R.take.at(R.st.take(R.Chk{h, at, n, got, left}), out)) == "" : Bytes()}, o)
    case R.Dat{h, more, got, left}:
      no2({Wr.drain.b(R.P, R.take.at(R.st.take(R.Dat{h, more, got, left}), out)) == "" : Bytes()}, o)
    case R.Clo{h, got, left}:
      no2({Wr.drain.b(R.P, R.take.at(R.st.take(R.Clo{h, got, left}), out)) == "" : Bytes()}, o)
    case R.Fin{r, rest}:
      no2({Wr.drain.b(R.P, R.take.at(R.st.take(R.Fin{r, rest}), out)) == "" : Bytes()}, o)
    case R.Bad{}:
      no2({Wr.drain.b(R.P, R.take.at(R.st.take(R.Bad{}), out)) == "" : Bytes()}, o)

def t.shut_take(+p: R.P, o: {R.open(p) == False{} : Bool}) ->
  {Wr.drain.b(R.P, R.take(p)) == "" : Bytes()}:
  match p:
    case R.P{st, +out}:
      t.shut_take.st(st, out, o)

def t.paid_open(over: Bool, -h: R.Head, -at: R.At, -n: U32, -got: Bytes(), -left: U32) ->
  {R.st.open(R.chunk.paid(over, h, at, n, got, left)) == True{} : Bool}:
  match over:
    case True{}:
      {==}
    case False{}:
      {==}

def t.line_open(z: Bool, -h: R.Head, -n: U32, -got: Bytes(), -left: U32) ->
  {R.st.open(R.chunk.line(z, h, n, got, left)) == True{} : Bool}:
  match z:
    case True{}:
      {==}
    case False{}:
      {==}

def t.chk_open(g: R.Go, -h: R.Head, +n: U32, -got: Bytes(), +left: U32) ->
  {R.st.open(R.chunk.go(g, h, n, got, left)) == True{} : Bool}:
  match g:
    case R.GBad{}:
      {==}
    case R.GTo{at, paid}:
      match paid:
        case True{}:
          t.paid_open(U32.is_le(left, n), h, at, n, got, left)
        case False{}:
          {==}
    case R.GDigit{+d}:
      t.paid_open(U32.is_le(left, (n * 16 + d : U32)), h, R.ASize{}, (n * 16 + d : U32), got, left)
    case R.GLine{}:
      t.line_open(U32.is_zero(n), h, n, got, left)
    case R.GDone{}:
      {==}

def t.step_open.st(+e: R.Ask, st: R.St, +c: U32, +out: List<&2, U32>,
  o: {R.st.open(st) == True{} : Bool}) ->
  {R.open(R.step.at(e, st, R.cls(c), c, out)) == True{} : Bool}:
  match st:
    case R.SVer{+a, +b}:
      no({R.open(R.step.at(e, R.SVer{a, b}, R.cls(c), c, out)) == True{} : Bool}, o)
    case R.SCode{+v10, +n, +k}:
      no({R.open(R.step.at(e, R.SCode{v10, n, k}, R.cls(c), c, out)) == True{} : Bool}, o)
    case R.SWhy{+v10, +code}:
      no({R.open(R.step.at(e, R.SWhy{v10, code}, R.cls(c), c, out)) == True{} : Bool}, o)
    case R.Eol{+h}:
      no({R.open(R.step.at(e, R.Eol{h}, R.cls(c), c, out)) == True{} : Bool}, o)
    case R.Lin{+h}:
      no({R.open(R.step.at(e, R.Lin{h}, R.cls(c), c, out)) == True{} : Bool}, o)
    case R.Nam{+h, +cl, +te, +co}:
      no({R.open(R.step.at(e, R.Nam{h, cl, te, co}, R.cls(c), c, out)) == True{} : Bool}, o)
    case R.Oth{+h}:
      no({R.open(R.step.at(e, R.Oth{h}, R.cls(c), c, out)) == True{} : Bool}, o)
    case R.Len0{+h}:
      no({R.open(R.step.at(e, R.Len0{h}, R.cls(c), c, out)) == True{} : Bool}, o)
    case R.Len{+h, +n}:
      no({R.open(R.step.at(e, R.Len{h, n}, R.cls(c), c, out)) == True{} : Bool}, o)
    case R.LenW{+h, +n}:
      no({R.open(R.step.at(e, R.LenW{h, n}, R.cls(c), c, out)) == True{} : Bool}, o)
    case R.Te0{+h}:
      no({R.open(R.step.at(e, R.Te0{h}, R.cls(c), c, out)) == True{} : Bool}, o)
    case R.Te{+h, +m}:
      no({R.open(R.step.at(e, R.Te{h, m}, R.cls(c), c, out)) == True{} : Bool}, o)
    case R.Conn{+h, +cl, +ka, +mc, +mk}:
      no({R.open(R.step.at(e, R.Conn{h, cl, ka, mc, mk}, R.cls(c), c, out)) == True{} : Bool}, o)
    case R.Eoh{+h}:
      no({R.open(R.step.at(e, R.Eoh{h}, R.cls(c), c, out)) == True{} : Bool}, o)
    case R.Bod{+h, +more, +got}:
      match more:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case R.Chk{+h, +at, +n, +got, +left}:
      t.chk_open(R.chunk.step(at, R.xk.of(R.cls(c), c)), h, n, got, left)
    case R.Dat{+h, +more, +got, +left}:
      match more:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case R.Clo{+h, +got, +left}:
      match left:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case R.Fin{+r, +rest}:
      {==}
    case R.Bad{}:
      {==}

def t.step_open(+e: R.Ask, +p: R.P, +c: U32, o: {R.open(p) == True{} : Bool}) ->
  {R.open(R.wstep(e, p, c)) == True{} : Bool}:
  match p:
    case R.P{st, +out}:
      t.step_open.st(e, st, c, out, o)

def t.paid_give(over: Bool, +x: Bytes(), -h: R.Head, -at: R.At, -n: U32, -got: Bytes(),
  -left: U32, -out: List<&2, U32>) ->
  {R.P{R.chunk.paid(over, h, at, n, Bytes.append(x, got), left), out} ==
    R.P{R.st.give(x, R.chunk.paid(over, h, at, n, got, left)), out} : R.P}:
  match over:
    case True{}:
      {==}
    case False{}:
      {==}

def t.line_give(z: Bool, +x: Bytes(), -h: R.Head, +n: U32, -got: Bytes(), +left: U32,
  -out: List<&2, U32>) ->
  {R.P{R.chunk.line(z, h, n, Bytes.append(x, got), left), out} ==
    R.P{R.st.give(x, R.chunk.line(z, h, n, got, left)), out} : R.P}:
  match z:
    case True{}:
      {==}
    case False{}:
      {==}

def t.chk_give(g: R.Go, +x: Bytes(), +h: R.Head, +n: U32, +got: Bytes(), +left: U32,
  +out: List<&2, U32>) ->
  {R.P{R.chunk.go(g, h, n, Bytes.append(x, got), left), out} ==
    R.P{R.st.give(x, R.chunk.go(g, h, n, got, left)), out} : R.P}:
  match g:
    case R.GBad{}:
      {==}
    case R.GTo{at, paid}:
      match paid:
        case True{}:
          t.paid_give(U32.is_le(left, n), x, h, at, n, got, left, out)
        case False{}:
          {==}
    case R.GDigit{+d}:
      t.paid_give(U32.is_le(left, (n * 16 + d : U32)), x, h, R.ASize{}, (n * 16 + d : U32), got,
        left, out)
    case R.GLine{}:
      t.line_give(U32.is_zero(n), x, h, n, got, left, out)
    case R.GDone{}:
      Equal.cong(R.Resp, R.P, y => R.P{R.Fin{y, ""}, out}, R.final(h, Bytes.append(x, got), False{}),
        R.resp.give(x, R.final(h, got, False{})),
        Equal.sym(R.Resp, R.resp.give(x, R.final(h, got, False{})),
          R.final(h, Bytes.append(x, got), False{}), t.give_final(x, h, got, False{})))

def t.step_give.st(+e: R.Ask, +x: Bytes(), st: R.St, +c: U32, +out: List<&2, U32>,
  o: {R.st.open(st) == True{} : Bool}) ->
  {R.step.at(e, R.st.give(x, st), R.cls(c), c, out) == R.give(x, R.step.at(e, st, R.cls(c), c, out)) :
    R.P}:
  match st:
    case R.SVer{+a, +b}:
      no({R.step.at(e, R.st.give(x, R.SVer{a, b}), R.cls(c), c, out) ==
        R.give(x, R.step.at(e, R.SVer{a, b}, R.cls(c), c, out)) : R.P}, o)
    case R.SCode{+v10, +n, +k}:
      no({R.step.at(e, R.st.give(x, R.SCode{v10, n, k}), R.cls(c), c, out) ==
        R.give(x, R.step.at(e, R.SCode{v10, n, k}, R.cls(c), c, out)) : R.P}, o)
    case R.SWhy{+v10, +code}:
      no({R.step.at(e, R.st.give(x, R.SWhy{v10, code}), R.cls(c), c, out) ==
        R.give(x, R.step.at(e, R.SWhy{v10, code}, R.cls(c), c, out)) : R.P}, o)
    case R.Eol{+h}:
      no({R.step.at(e, R.st.give(x, R.Eol{h}), R.cls(c), c, out) ==
        R.give(x, R.step.at(e, R.Eol{h}, R.cls(c), c, out)) : R.P}, o)
    case R.Lin{+h}:
      no({R.step.at(e, R.st.give(x, R.Lin{h}), R.cls(c), c, out) ==
        R.give(x, R.step.at(e, R.Lin{h}, R.cls(c), c, out)) : R.P}, o)
    case R.Nam{+h, +cl, +te, +co}:
      no({R.step.at(e, R.st.give(x, R.Nam{h, cl, te, co}), R.cls(c), c, out) ==
        R.give(x, R.step.at(e, R.Nam{h, cl, te, co}, R.cls(c), c, out)) : R.P}, o)
    case R.Oth{+h}:
      no({R.step.at(e, R.st.give(x, R.Oth{h}), R.cls(c), c, out) ==
        R.give(x, R.step.at(e, R.Oth{h}, R.cls(c), c, out)) : R.P}, o)
    case R.Len0{+h}:
      no({R.step.at(e, R.st.give(x, R.Len0{h}), R.cls(c), c, out) ==
        R.give(x, R.step.at(e, R.Len0{h}, R.cls(c), c, out)) : R.P}, o)
    case R.Len{+h, +n}:
      no({R.step.at(e, R.st.give(x, R.Len{h, n}), R.cls(c), c, out) ==
        R.give(x, R.step.at(e, R.Len{h, n}, R.cls(c), c, out)) : R.P}, o)
    case R.LenW{+h, +n}:
      no({R.step.at(e, R.st.give(x, R.LenW{h, n}), R.cls(c), c, out) ==
        R.give(x, R.step.at(e, R.LenW{h, n}, R.cls(c), c, out)) : R.P}, o)
    case R.Te0{+h}:
      no({R.step.at(e, R.st.give(x, R.Te0{h}), R.cls(c), c, out) ==
        R.give(x, R.step.at(e, R.Te0{h}, R.cls(c), c, out)) : R.P}, o)
    case R.Te{+h, +m}:
      no({R.step.at(e, R.st.give(x, R.Te{h, m}), R.cls(c), c, out) ==
        R.give(x, R.step.at(e, R.Te{h, m}, R.cls(c), c, out)) : R.P}, o)
    case R.Conn{+h, +cl, +ka, +mc, +mk}:
      no({R.step.at(e, R.st.give(x, R.Conn{h, cl, ka, mc, mk}), R.cls(c), c, out) ==
        R.give(x, R.step.at(e, R.Conn{h, cl, ka, mc, mk}, R.cls(c), c, out)) : R.P}, o)
    case R.Eoh{+h}:
      no({R.step.at(e, R.st.give(x, R.Eoh{h}), R.cls(c), c, out) ==
        R.give(x, R.step.at(e, R.Eoh{h}, R.cls(c), c, out)) : R.P}, o)
    case R.Bod{+h, +more, +got}:
      match more:
        case 0n:
          Equal.trans(R.P, R.P{R.Fin{R.final(h, Bytes.push(Bytes.append(x, got), c), False{}), ""}, out},
            R.P{R.Fin{R.final(h, Bytes.append(x, Bytes.push(got, c)), False{}), ""}, out},
            R.P{R.Fin{R.resp.give(x, R.final(h, Bytes.push(got, c), False{})), ""}, out},
            Equal.cong(Bytes(), R.P, y => R.P{R.Fin{R.final(h, y, False{}), ""}, out},
              Bytes.push(Bytes.append(x, got), c), Bytes.append(x, Bytes.push(got, c)),
              t.push_give(x, got, c)),
            Equal.cong(R.Resp, R.P, y => R.P{R.Fin{y, ""}, out},
              R.final(h, Bytes.append(x, Bytes.push(got, c)), False{}),
              R.resp.give(x, R.final(h, Bytes.push(got, c), False{})),
              Equal.sym(R.Resp, R.resp.give(x, R.final(h, Bytes.push(got, c), False{})),
                R.final(h, Bytes.append(x, Bytes.push(got, c)), False{}),
                t.give_final(x, h, Bytes.push(got, c), False{}))))
        case 1n+q:
          Equal.cong(Bytes(), R.P, y => R.P{R.Bod{h, q, y}, out},
            Bytes.push(Bytes.append(x, got), c), Bytes.append(x, Bytes.push(got, c)),
            t.push_give(x, got, c))
    case R.Chk{+h, +at, +n, +got, +left}:
      t.chk_give(R.chunk.step(at, R.xk.of(R.cls(c), c)), x, h, n, got, left, out)
    case R.Dat{+h, +more, +got, +left}:
      match more:
        case 0n:
          Equal.cong(Bytes(), R.P, y => R.P{R.Chk{h, R.ADataCr{}, 0, y, left}, out},
            Bytes.push(Bytes.append(x, got), c), Bytes.append(x, Bytes.push(got, c)),
            t.push_give(x, got, c))
        case 1n+q:
          Equal.cong(Bytes(), R.P, y => R.P{R.Dat{h, q, y, left}, out},
            Bytes.push(Bytes.append(x, got), c), Bytes.append(x, Bytes.push(got, c)),
            t.push_give(x, got, c))
    case R.Clo{+h, +got, +left}:
      match left:
        case 0n:
          {==}
        case 1n+q:
          Equal.cong(Bytes(), R.P, y => R.P{R.Clo{h, y, q}, out},
            Bytes.push(Bytes.append(x, got), c), Bytes.append(x, Bytes.push(got, c)),
            t.push_give(x, got, c))
    case R.Fin{+r, +rest}:
      {==}
    case R.Bad{}:
      {==}

def t.step_give(+e: R.Ask, +x: Bytes(), +p: R.P, +c: U32, o: {R.open(p) == True{} : Bool}) ->
  {R.wstep(e, R.give(x, p), c) == R.give(x, R.wstep(e, p, c)) : R.P}:
  match p:
    case R.P{st, +out}:
      t.step_give.st(e, x, st, c, out, o)


# The laws, whole
# ===============

def Laws.feed_split(e, a, b, p):
  Wr.feed_split(~R.Ask, ~R.P, ~R.wstep, e, a, b, p)

def Laws.bad_absorbs(e, c, out):
  {==}

# a refused reader, as the kit's absorbing states
def bad(out: List<&2, U32>) -> R.P:
  R.P{R.Bad{}, out}

def absorbs(+e: R.Ask, +out: List<&2, U32>, +c: U32) -> {R.wstep(e, bad(out), c) == bad(out) : R.P}:
  {==}

def Laws.bad_feeds(e, s, out):
  Wr.bad_feeds(~R.Ask, ~R.P, ~R.wstep, ~List<&2, U32>, ~bad, ~absorbs, e, s, out)

def Laws.feed_buf_is_feed(e, b, p):
  Wr.feed_buf_is_feed(~R.Ask, ~R.P, ~R.wstep, ~R.wadv, ~adv_ok, e, b, p)

def Laws.feed_buf_split(e, a, b, p):
  Wr.feed_buf_split(~R.Ask, ~R.P, ~R.wstep, ~R.wadv, ~adv_ok, e, a, b, p)

def Laws.bad_feeds_buf(e, s, out):
  Wr.bad_feeds_buf(~R.Ask, ~R.P, ~R.wstep, ~R.wadv, ~adv_ok, ~List<&2, U32>, ~bad, ~absorbs, e, s, out)

def Laws.reads_split(e, rs, p):
  Wr.reads_split(~R.Ask, ~R.P, ~R.wstep, ~R.wadv, ~adv_ok, e, rs, p)

def Laws.drain_reads(e, rs, p):
  Wr.drain_reads(~R.Ask, ~R.P, ~R.wstep, ~R.wadv, ~adv_ok, ~R.take, ~R.wgive, ~R.open,
    ~t.step_open, ~t.step_give, ~t.take_open, ~t.shut_take, ~t.give_take, ~t.give_nil,
    ~t.give_app, e, rs, p)

def Laws.cls_rfc():
  {==}

def Laws.lower_rfc():
  {==}

def Laws.resp_sim(e, bs):
  resp.sim(e, bs)

def Laws.resp_sim_buf(e, b):
  %Equal.sym(R.P, R.feed_buf(e, b, R.p.new()), R.feed(e, Bytes.to_list(b), R.p.new()),
    Laws.feed_buf_is_feed(e, b, R.p.new())) : {R.look(_) == S.response(e, Bytes.to_list(b)) : R.Look}
  resp.sim(e, Bytes.to_list(b))

def Laws.resp_sim_reads(e, rs):
  %Equal.sym(R.P, R.reads(e, rs, R.p.new()), R.feed(e, Bytes.to_list(Bytes.concat(rs)), R.p.new()),
    Wr.reads_is(~R.Ask, ~R.P, ~R.wstep, ~R.wadv, ~adv_ok, e, rs, R.p.new())) :
    {R.look(_) == S.response(e, Bytes.to_list(Bytes.concat(rs))) : R.Look}
  resp.sim(e, Bytes.to_list(Bytes.concat(rs)))

def Laws.cuts():
  {==}

def Laws.cuts_bytes():
  {==}

def Laws.v_interim():
  {==}

def Laws.v_204_len():
  {==}

def Laws.v_304():
  {==}

def Laws.v_head():
  {==}

def Laws.v_head_chunked():
  {==}

def Laws.v_chunked():
  {==}

def Laws.v_close():
  {==}

def Laws.v_10_keepalive():
  {==}

def Laws.v_10_close():
  {==}

def Laws.v_conn_close():
  {==}

def Laws.v_101():
  {==}

def Laws.v_no_reason():
  {==}

def Laws.v_after():
  {==}

def Laws.v_close_cap():
  {==}

def Laws.v_body_len():
  {==}

def Laws.v_body_chunked():
  {==}

def Laws.v_body_drain():
  {==}

def Laws.r_cl_te():
  {==}

def Laws.r_te_cl():
  {==}

def Laws.r_te_10():
  {==}

def Laws.r_te_list():
  {==}

def Laws.r_te_space():
  {==}

def Laws.r_te_twice():
  {==}

def Laws.r_fold():
  {==}

def Laws.r_lf_status():
  {==}

def Laws.r_lf_field():
  {==}

def Laws.r_cr():
  {==}

def Laws.r_cl_list():
  {==}

def Laws.r_cl_two():
  {==}

def Laws.r_cl_sign():
  {==}

def Laws.r_cl_empty():
  {==}

def Laws.r_space_colon():
  {==}

def Laws.r_status_short():
  {==}

def Laws.r_status_long():
  {==}

def Laws.r_status_low():
  {==}

def Laws.r_status_high():
  {==}

def Laws.r_version():
  {==}

def Laws.r_version_case():
  {==}

def Laws.r_two_sp():
  {==}

def Laws.r_reason_ctl():
  {==}

def Laws.r_value_nul():
  {==}

def Laws.r_cap_len():
  {==}

def Laws.r_cap_chunk():
  {==}

def Laws.r_cap_close():
  {==}
