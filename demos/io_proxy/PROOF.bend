# The proofs of bend-proxy's laws.
#
# scan_is_spec is a simulation between two walks that never meet
# directly: the proxy steps the engine's reader, the reference steps
# spec.bend's walk. What joins them is frame_sim, the engine's law that
# its reader agrees with frame() on every input: after each byte, both
# sides are compared through frame_sim of the bytes so far -- the same
# requests, and a refusal on one exactly when the other refuses -- and
# the relation (Waits) is carried to the next byte by the reader kit's
# feed_split and the walk's own step. The rest is bookkeeping: the
# requests taken in order (reversed accumulators, reversed back), and a
# stream cut into reads is the stream whole.
import Base
import ../../wire/reader.bend as Wr
import ../io_http_engine/main.bend as Eng
import ../io_http_engine/spec.bend as Spec
import ../io_http_engine/LAWS.bend as EL
import ../io_http_engine/PROOF.bend as EP
import ./core.bend as X
import ./LAWS.bend as Laws

# Lists
# =====

def app.nil(-A: Data, xs: List<&2, A>) -> {List.append(&2, A, xs, Nil{}) == xs : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(List<&2, A>, List<&2, A>, ys => Con{h, ys}, List.append(&2, A, t, Nil{}), t, app.nil(A, t))

def app.assoc(-A: Data, xs: List<&2, A>, -ys: List<&2, A>, -zs: List<&2, A>) ->
  {List.append(&2, A, List.append(&2, A, xs, ys), zs) == List.append(&2, A, xs, List.append(&2, A, ys, zs)) :
    List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(List<&2, A>, List<&2, A>, us => Con{h, us}, List.append(&2, A, List.append(&2, A, t, ys), zs),
        List.append(&2, A, t, List.append(&2, A, ys, zs)), app.assoc(A, t, ys, zs))

# reversing onto a list is reversing, then appending it
def rev.go(-A: Data, xs: List<&2, A>, +acc: List<&2, A>) ->
  {List.reverse.go(&2, A, xs, acc) == List.append(&2, A, List.reverse(&2, A, xs), acc) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.trans(List<&2, A>, List.reverse.go(&2, A, t, Con{h, acc}),
        List.append(&2, A, List.reverse(&2, A, t), Con{h, acc}),
        List.append(&2, A, List.reverse.go(&2, A, t, Con{h, Nil{}}), acc),
        rev.go(A, t, Con{h, acc}),
        Equal.trans(List<&2, A>, List.append(&2, A, List.reverse(&2, A, t), Con{h, acc}),
          List.append(&2, A, List.append(&2, A, List.reverse(&2, A, t), Con{h, Nil{}}), acc),
          List.append(&2, A, List.reverse.go(&2, A, t, Con{h, Nil{}}), acc),
          Equal.sym(List<&2, A>, List.append(&2, A, List.append(&2, A, List.reverse(&2, A, t), Con{h, Nil{}}), acc),
            List.append(&2, A, List.reverse(&2, A, t), Con{h, acc}),
            app.assoc(A, List.reverse(&2, A, t), Con{h, Nil{}}, acc)),
          Equal.cong(List<&2, A>, List<&2, A>, us => List.append(&2, A, us, acc),
            List.append(&2, A, List.reverse(&2, A, t), Con{h, Nil{}}), List.reverse.go(&2, A, t, Con{h, Nil{}}),
            Equal.sym(List<&2, A>, List.reverse.go(&2, A, t, Con{h, Nil{}}),
              List.append(&2, A, List.reverse(&2, A, t), Con{h, Nil{}}), rev.go(A, t, Con{h, Nil{}})))))

def rev.twice.go(-A: Data, xs: List<&2, A>, a: List<&2, A>, -b: List<&2, A>) ->
  {List.reverse.go(&2, A, List.reverse.go(&2, A, xs, a), b) == List.reverse.go(&2, A, a, List.append(&2, A, xs, b)) :
    List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      rev.twice.go(A, t, Con{h, a}, b)

def rev.rev(-A: Data, +xs: List<&2, A>) -> {List.reverse(&2, A, List.reverse(&2, A, xs)) == xs : List<&2, A>}:
  Equal.trans(List<&2, A>, List.reverse(&2, A, List.reverse(&2, A, xs)), List.append(&2, A, xs, Nil{}), xs,
    rev.twice.go(A, xs, Nil{}, Nil{}), app.nil(A, xs))

def rev.inj(-A: Data, +a: List<&2, A>, +b: List<&2, A>,
  e: {List.reverse(&2, A, a) == List.reverse(&2, A, b) : List<&2, A>}) -> {a == b : List<&2, A>}:
  Equal.trans(List<&2, A>, a, List.reverse(&2, A, List.reverse(&2, A, a)), b,
    Equal.sym(List<&2, A>, List.reverse(&2, A, List.reverse(&2, A, a)), a, rev.rev(A, a)),
    Equal.trans(List<&2, A>, List.reverse(&2, A, List.reverse(&2, A, a)), List.reverse(&2, A, List.reverse(&2, A, b)), b,
      Equal.cong(List<&2, A>, List<&2, A>, xs => List.reverse(&2, A, xs), List.reverse(&2, A, a),
        List.reverse(&2, A, b), e),
      rev.rev(A, b)))

# reversing a list with one more at its head puts it at the end
def rev.con(-A: Data, +h: A, +t: List<&2, A>) ->
  {List.reverse(&2, A, Con{h, t}) == List.append(&2, A, List.reverse(&2, A, t), Con{h, Nil{}}) : List<&2, A>}:
  rev.go(A, t, Con{h, Nil{}})

# The requests taken, as the reference's
# --------------------------------------

def tooks.rev.go(ts: List<&2, X.Took>, acc: List<&2, X.Took>) ->
  {Laws.tooks.of(List.reverse.go(&2, X.Took, ts, acc)) ==
    List.reverse.go(&2, Laws.PTook, Laws.tooks.of(ts), Laws.tooks.of(acc)) : List<&2, Laws.PTook>}:
  match ts:
    case Nil{}:
      {==}
    case Con{h, t}:
      tooks.rev.go(t, Con{h, acc})

def tooks.rev(ts: List<&2, X.Took>) ->
  {Laws.tooks.of(List.reverse(&2, X.Took, ts)) == List.reverse(&2, Laws.PTook, Laws.tooks.of(ts)) :
    List<&2, Laws.PTook>}:
  tooks.rev.go(ts, Nil{})

def tooks.app(ts: List<&2, X.Took>, -us: List<&2, X.Took>) ->
  {Laws.tooks.of(List.append(&2, X.Took, ts, us)) ==
    List.append(&2, Laws.PTook, Laws.tooks.of(ts), Laws.tooks.of(us)) : List<&2, Laws.PTook>}:
  match ts:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(List<&2, Laws.PTook>, List<&2, Laws.PTook>, xs => Con{Laws.took.of(h), xs},
        Laws.tooks.of(List.append(&2, X.Took, t, us)),
        List.append(&2, Laws.PTook, Laws.tooks.of(t), Laws.tooks.of(us)), tooks.app(t, us))

# One byte
# ========

# the walk over one more byte is one more step
def walk.snoc(xs: List<&2, U32>, -c: U32, +w: Spec.W) ->
  {Spec.walk(Spec.snoc(xs, c), w) == Spec.next(Spec.walk(xs, w), c) : Spec.W}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      walk.snoc(t, c, Spec.next(w, x))

# and so is the reader's, by the kit's feed_split
def feed.snoc(+xs: List<&2, U32>, +c: U32, +p: Eng.P) ->
  {Eng.feed(Spec.snoc(xs, c), p) == Eng.step(Eng.feed(xs, p), c) : Eng.P}:
  EL.feed_split(xs, Con{c, Nil{}}, p)

# what the proxy's step and the reference's left, related: still
# reading on the same bytes (Waits), a request with the same bytes and
# the same reading, or both refused
def StpRel(a: X.Stp, b: Laws.PStp) -> Type:
  match a b:
    case X.SGo{p, rb} Laws.PGo{w, r}:
      Laws.Waits(X.Scan{p, rb}, w, r)
    case X.SMsg{rb, q} Laws.PMsg{r, q2}:
      {Bytes.to_list(rb) == r : List<&2, U32>} & {q == q2 : Eng.Req}
    case X.SUp{rb, q} Laws.PUp{r, q2}:
      {Bytes.to_list(rb) == r : List<&2, U32>} & {q == q2 : Eng.Req}
    case X.SBad{} Laws.PBad{}:
      Unit
    case _ _:
      Empty

def BD(b: Bool, tc: Type, fc: Type) -> Type:
  match b:
    case True{}:
      tc
    case False{}:
      fc

def no(-g: Type, e: {False{} == True{} : Bool}) -> g:
  %e : BD(_, g, Unit)
  Unit{}

def look.eq(l: EL.Look, m: EL.Look) -> Bool:
  match l m:
    case EL.Reading{} EL.Reading{}:
      True{}
    case EL.Refusing{} EL.Refusing{}:
      True{}
    case EL.Handing{} EL.Handing{}:
      True{}
    case _ _:
      False{}

# two different looks are never equal
def look.no(-g: Type, x: EL.Look, -y: EL.Look, e: {x == y : EL.Look}) -> BD(look.eq(x, y), Unit, g):
  match x:
    case EL.Reading{}:
      %e : BD(look.eq(EL.Reading{}, _), Unit, g)
      Unit{}
    case EL.Refusing{}:
      %e : BD(look.eq(EL.Refusing{}, _), Unit, g)
      Unit{}
    case EL.Handing{}:
      %e : BD(look.eq(EL.Handing{}, _), Unit, g)
      Unit{}

def st.of(p: Eng.P) -> Eng.St:
  match p:
    case Eng.P{st, pd, out}:
      st

def out.of(p: Eng.P) -> List<&2, Eng.Req>:
  match p:
    case Eng.P{st, pd, out}:
      out

def st.bad(st: Eng.St) -> Bool:
  match st:
    case Eng.Bad{}:
      True{}
    case _:
      False{}

def lk.fst(l: List<&2, Eng.Req> & EL.Look) -> List<&2, Eng.Req>:
  Pair.fst(List<&2, Eng.Req>, EL.Look, l)

def lk.snd(l: List<&2, Eng.Req> & EL.Look) -> EL.Look:
  Pair.snd(List<&2, Eng.Req>, EL.Look, l)

# a request completed on the byte: both sides take it
def req.rel(b: Bool, -rb: Bytes(), -r: List<&2, U32>, -q: Eng.Req, er: {Bytes.to_list(rb) == r : List<&2, U32>}) ->
  StpRel(X.stp.req(b, rb, q), Laws.px.req(b, r, q)):
  match b:
    case True{}:
      (er, {==})
    case False{}:
      (er, {==})

# none completed, the walk's framing still open: the reader is not
# refused (it reads), and both go on reading the same bytes
def nil.open(st: Eng.St, -pd: Eng.Pend, -rb: Bytes(), -r: List<&2, U32>, -mode: Spec.Mode, -since: List<&2, U32>,
  er: {Bytes.to_list(rb) == r : List<&2, U32>}, hl: {EL.look.st(st) == EL.Reading{} : EL.Look},
  hp: {Eng.P{st, pd, Nil{}} == Eng.feed(r, Eng.p.new()) : Eng.P},
  hw: {Spec.W{mode, Nil{}, since} == Spec.walk(r, Laws.w0()) : Spec.W}) ->
  StpRel(X.stp.st(st, pd, rb), Laws.PGo{Spec.W{mode, Nil{}, since}, r}):
  match st:
    case Eng.Pre{}:
      (er, (hp, hw))
    case Eng.PreLf{}:
      (er, (hp, hw))
    case Eng.InM{m0}:
      (er, (hp, hw))
    case Eng.InT{p0}:
      (er, (hp, hw))
    case Eng.InV{v0}:
      (er, (hp, hw))
    case Eng.CrM{}:
      (er, (hp, hw))
    case Eng.Lin{}:
      (er, (hp, hw))
    case Eng.InN{n0}:
      (er, (hp, hw))
    case Eng.InL0{}:
      (er, (hp, hw))
    case Eng.InL{v0}:
      (er, (hp, hw))
    case Eng.InLt{v0}:
      (er, (hp, hw))
    case Eng.InLc{t0, cl0, up0, ka0}:
      (er, (hp, hw))
    case Eng.InLu{t0, ws0}:
      (er, (hp, hw))
    case Eng.InLk0{}:
      (er, (hp, hw))
    case Eng.InLk{k0}:
      (er, (hp, hw))
    case Eng.InLv{v0}:
      (er, (hp, hw))
    case Eng.InLx{}:
      (er, (hp, hw))
    case Eng.InLe0{}:
      (er, (hp, hw))
    case Eng.InLe{v0}:
      (er, (hp, hw))
    case Eng.CrL{}:
      (er, (hp, hw))
    case Eng.Bod{r0, b0}:
      (er, (hp, hw))
    case Eng.Chk{pos0, n0, b0, left0}:
      (er, (hp, hw))
    case Eng.Chd{r0, b0, left0}:
      (er, (hp, hw))
    case Eng.Rest{bs0}:
      (er, (hp, hw))
    case Eng.Bad{}:
      look.no(Empty, EL.Refusing{}, EL.Reading{}, hl)

# none completed, the framing refused: the reader has refused too
def nil.refused(st: Eng.St, -pd: Eng.Pend, -rb: Bytes(), hl: {EL.look.st(st) == EL.Refusing{} : EL.Look}) ->
  StpRel(X.stp.st(st, pd, rb), Laws.PBad{}):
  match st:
    case Eng.Pre{}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.PreLf{}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.InM{m0}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.InT{p0}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.InV{v0}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.CrM{}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.Lin{}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.InN{n0}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.InL0{}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.InL{v0}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.InLt{v0}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.InLc{t0, cl0, up0, ka0}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.InLu{t0, ws0}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.InLk0{}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.InLk{k0}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.InLv{v0}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.InLx{}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.InLe0{}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.InLe{v0}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.CrL{}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.Bod{r0, b0}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.Chk{pos0, n0, b0, left0}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.Chd{r0, b0, left0}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.Rest{bs0}:
      look.no(Empty, EL.Handing{}, EL.Refusing{}, hl)
    case Eng.Bad{}:
      Unit{}

# none completed after an upgrade (never, but it would read on)
def nil.up(st: Eng.St, -pd: Eng.Pend, -rb: Bytes(), -r: List<&2, U32>, -mode: Spec.Mode, -since: List<&2, U32>,
  -b: Bytes(), er: {Bytes.to_list(rb) == r : List<&2, U32>}, hs: {st == Eng.Rest{b} : Eng.St},
  hp: {Eng.P{st, pd, Nil{}} == Eng.feed(r, Eng.p.new()) : Eng.P},
  hw: {Spec.W{mode, Nil{}, since} == Spec.walk(r, Laws.w0()) : Spec.W}) ->
  StpRel(X.stp.st(st, pd, rb), Laws.PGo{Spec.W{mode, Nil{}, since}, r}):
  match st:
    case Eng.Pre{}:
      (er, (hp, hw))
    case Eng.PreLf{}:
      (er, (hp, hw))
    case Eng.InM{m0}:
      (er, (hp, hw))
    case Eng.InT{p0}:
      (er, (hp, hw))
    case Eng.InV{v0}:
      (er, (hp, hw))
    case Eng.CrM{}:
      (er, (hp, hw))
    case Eng.Lin{}:
      (er, (hp, hw))
    case Eng.InN{n0}:
      (er, (hp, hw))
    case Eng.InL0{}:
      (er, (hp, hw))
    case Eng.InL{v0}:
      (er, (hp, hw))
    case Eng.InLt{v0}:
      (er, (hp, hw))
    case Eng.InLc{t0, cl0, up0, ka0}:
      (er, (hp, hw))
    case Eng.InLu{t0, ws0}:
      (er, (hp, hw))
    case Eng.InLk0{}:
      (er, (hp, hw))
    case Eng.InLk{k0}:
      (er, (hp, hw))
    case Eng.InLv{v0}:
      (er, (hp, hw))
    case Eng.InLx{}:
      (er, (hp, hw))
    case Eng.InLe0{}:
      (er, (hp, hw))
    case Eng.InLe{v0}:
      (er, (hp, hw))
    case Eng.CrL{}:
      (er, (hp, hw))
    case Eng.Bod{r0, b0}:
      (er, (hp, hw))
    case Eng.Chk{pos0, n0, b0, left0}:
      (er, (hp, hw))
    case Eng.Chd{r0, b0, left0}:
      (er, (hp, hw))
    case Eng.Rest{bs0}:
      (er, (hp, hw))
    case Eng.Bad{}:
      no(Empty, Equal.cong(Eng.St, Bool, st.bad, Eng.Rest{b}, Eng.Bad{}, Equal.sym(Eng.St, Eng.Bad{}, Eng.Rest{b}, hs)))

def fin.open(out: List<&2, Eng.Req>, st: Eng.St, +pd: Eng.Pend, -rb: Bytes(), -r: List<&2, U32>, +mode: Spec.Mode,
  +since: List<&2, U32>, -rest: List<&2, U32>, he: {Spec.finish.end(mode, since) == Spec.Open{rest} : Spec.End},
  er: {Bytes.to_list(rb) == r : List<&2, U32>}, hl: {EL.look.st(st) == EL.Reading{} : EL.Look},
  hp: {Eng.P{st, pd, out} == Eng.feed(r, Eng.p.new()) : Eng.P},
  hw: {Spec.W{mode, out, since} == Spec.walk(r, Laws.w0()) : Spec.W}) ->
  StpRel(X.stp.out(st, pd, out, rb), Laws.px.out(mode, out, since, r)):
  match out:
    case Con{+q, t}:
      req.rel(Eng.req.ws(q), rb, r, q, er)
    case Nil{}:
      %Equal.sym(Spec.End, Spec.finish.end(mode, since), Spec.Open{rest}, he) :
        StpRel(X.stp.st(st, pd, rb), Laws.px.end(_, Spec.W{mode, Nil{}, since}, r))
      nil.open(st, pd, rb, r, mode, since, er, hl, hp, hw)

def fin.refused(out: List<&2, Eng.Req>, st: Eng.St, +pd: Eng.Pend, -rb: Bytes(), -r: List<&2, U32>, +mode: Spec.Mode,
  +since: List<&2, U32>, he: {Spec.finish.end(mode, since) == Spec.Refused{} : Spec.End},
  er: {Bytes.to_list(rb) == r : List<&2, U32>}, hl: {EL.look.st(st) == EL.Refusing{} : EL.Look}) ->
  StpRel(X.stp.out(st, pd, out, rb), Laws.px.out(mode, out, since, r)):
  match out:
    case Con{+q, t}:
      req.rel(Eng.req.ws(q), rb, r, q, er)
    case Nil{}:
      %Equal.sym(Spec.End, Spec.finish.end(mode, since), Spec.Refused{}, he) :
        StpRel(X.stp.st(st, pd, rb), Laws.px.end(_, Spec.W{mode, Nil{}, since}, r))
      nil.refused(st, pd, rb, hl)

def fin.up(out: List<&2, Eng.Req>, st: Eng.St, +pd: Eng.Pend, -rb: Bytes(), -r: List<&2, U32>, +mode: Spec.Mode,
  +since: List<&2, U32>, -b: Bytes(), he: {Spec.finish.end(mode, since) == Spec.Upgraded{b} : Spec.End},
  er: {Bytes.to_list(rb) == r : List<&2, U32>}, hs: {st == Eng.Rest{b} : Eng.St},
  hp: {Eng.P{st, pd, out} == Eng.feed(r, Eng.p.new()) : Eng.P},
  hw: {Spec.W{mode, out, since} == Spec.walk(r, Laws.w0()) : Spec.W}) ->
  StpRel(X.stp.out(st, pd, out, rb), Laws.px.out(mode, out, since, r)):
  match out:
    case Con{+q, t}:
      req.rel(Eng.req.ws(q), rb, r, q, er)
    case Nil{}:
      %Equal.sym(Spec.End, Spec.finish.end(mode, since), Spec.Upgraded{b}, he) :
        StpRel(X.stp.st(st, pd, rb), Laws.px.end(_, Spec.W{mode, Nil{}, since}, r))
      nil.up(st, pd, rb, r, mode, since, b, er, hs, hp, hw)

# one equality between pairs is two, and one between readers two more
def pair.eqs(-a: List<&2, Eng.Req>, -b: EL.Look, -c: List<&2, Eng.Req>, -d: EL.Look,
  e: {(a, b) == (c, d) : List<&2, Eng.Req> & EL.Look}) -> {a == c : List<&2, Eng.Req>} & {b == d : EL.Look}:
  %Equal.sym(List<&2, Eng.Req> & EL.Look, (a, b), (c, d), e) : {lk.fst(_) == c : List<&2, Eng.Req>} & {lk.snd(_) == d : EL.Look}
  ({==}, {==})

def p.eqs(-st: Eng.St, -pd: Eng.Pend, -out: List<&2, Eng.Req>, -st2: Eng.St, -pd2: Eng.Pend,
  -out2: List<&2, Eng.Req>, e: {Eng.P{st, pd, out} == Eng.P{st2, pd2, out2} : Eng.P}) ->
  {st == st2 : Eng.St} & {out == out2 : List<&2, Eng.Req>}:
  %Equal.sym(Eng.P, Eng.P{st, pd, out}, Eng.P{st2, pd2, out2}, e) : {st.of(_) == st2 : Eng.St} & {out.of(_) == out2 : List<&2, Eng.Req>}
  ({==}, {==})

def e.open(+st: Eng.St, +pd: Eng.Pend, +out: List<&2, Eng.Req>, +mode: Spec.Mode, +o2: List<&2, Eng.Req>,
  +since: List<&2, U32>, -rest: List<&2, U32>, he: {Spec.finish.end(mode, since) == Spec.Open{rest} : Spec.End},
  -rb: Bytes(), -r: List<&2, U32>, er: {Bytes.to_list(rb) == r : List<&2, U32>},
  l2: {List.reverse(&2, Eng.Req, out) == List.reverse(&2, Eng.Req, o2) : List<&2, Eng.Req>} &
    {EL.look.st(st) == EL.Reading{} : EL.Look},
  hp: {Eng.P{st, pd, out} == Eng.feed(r, Eng.p.new()) : Eng.P},
  hw: {Spec.W{mode, o2, since} == Spec.walk(r, Laws.w0()) : Spec.W}) ->
  StpRel(X.stp.out(st, pd, out, rb), Laws.px.out(mode, o2, since, r)):
  (lr, ls) = l2
  +eq = rev.inj(Eng.Req, out, o2, lr)
  %eq : StpRel(X.stp.out(st, pd, out, rb), Laws.px.out(mode, _, since, r))
  fin.open(out, st, pd, rb, r, mode, since, rest, he, er, ls, hp,
    Equal.trans(Spec.W, Spec.W{mode, out, since}, Spec.W{mode, o2, since}, Spec.walk(r, Laws.w0()),
      Equal.cong(List<&2, Eng.Req>, Spec.W, x => Spec.W{mode, x, since}, out, o2, eq), hw))

def e.refused(+st: Eng.St, +pd: Eng.Pend, +out: List<&2, Eng.Req>, +mode: Spec.Mode, +o2: List<&2, Eng.Req>,
  +since: List<&2, U32>, he: {Spec.finish.end(mode, since) == Spec.Refused{} : Spec.End},
  -rb: Bytes(), -r: List<&2, U32>, er: {Bytes.to_list(rb) == r : List<&2, U32>},
  l2: {List.reverse(&2, Eng.Req, out) == List.reverse(&2, Eng.Req, o2) : List<&2, Eng.Req>} &
    {EL.look.st(st) == EL.Refusing{} : EL.Look}) ->
  StpRel(X.stp.out(st, pd, out, rb), Laws.px.out(mode, o2, since, r)):
  (lr, ls) = l2
  +eq = rev.inj(Eng.Req, out, o2, lr)
  %eq : StpRel(X.stp.out(st, pd, out, rb), Laws.px.out(mode, _, since, r))
  fin.refused(out, st, pd, rb, r, mode, since, he, er, ls)

def e.up(+st: Eng.St, +pd: Eng.Pend, +out: List<&2, Eng.Req>, +mode: Spec.Mode, +o2: List<&2, Eng.Req>,
  +since: List<&2, U32>, -b: Bytes(), he: {Spec.finish.end(mode, since) == Spec.Upgraded{b} : Spec.End},
  -rb: Bytes(), -r: List<&2, U32>, er: {Bytes.to_list(rb) == r : List<&2, U32>},
  p2: {st == Eng.Rest{b} : Eng.St} &
    {out == List.reverse(&2, Eng.Req, List.reverse(&2, Eng.Req, o2)) : List<&2, Eng.Req>},
  hp: {Eng.P{st, pd, out} == Eng.feed(r, Eng.p.new()) : Eng.P},
  hw: {Spec.W{mode, o2, since} == Spec.walk(r, Laws.w0()) : Spec.W}) ->
  StpRel(X.stp.out(st, pd, out, rb), Laws.px.out(mode, o2, since, r)):
  (es, eo) = p2
  +eq = Equal.trans(List<&2, Eng.Req>, out, List.reverse(&2, Eng.Req, List.reverse(&2, Eng.Req, o2)), o2, eo,
    rev.rev(Eng.Req, o2))
  %eq : StpRel(X.stp.out(st, pd, out, rb), Laws.px.out(mode, _, since, r))
  fin.up(out, st, pd, rb, r, mode, since, b, he, er, es, hp,
    Equal.trans(Spec.W, Spec.W{mode, out, since}, Spec.W{mode, o2, since}, Spec.walk(r, Laws.w0()),
      Equal.cong(List<&2, Eng.Req>, Spec.W, x => Spec.W{mode, x, since}, out, o2, eq), hw))

# the walk's step and the reader's, compared through frame_sim's
# agreement at the byte, whichever way the framing ends there
def stp.end(+st: Eng.St, +pd: Eng.Pend, +out: List<&2, Eng.Req>, +mode: Spec.Mode, +o2: List<&2, Eng.Req>,
  +since: List<&2, U32>, e: Spec.End, he: {Spec.finish.end(mode, since) == e : Spec.End}, -rb: Bytes(),
  -r: List<&2, U32>, er: {Bytes.to_list(rb) == r : List<&2, U32>},
  ag: EL.agree.end(Eng.P{st, pd, out}, List.reverse(&2, Eng.Req, o2), e),
  hp: {Eng.P{st, pd, out} == Eng.feed(r, Eng.p.new()) : Eng.P},
  hw: {Spec.W{mode, o2, since} == Spec.walk(r, Laws.w0()) : Spec.W}) ->
  StpRel(X.stp.out(st, pd, out, rb), Laws.px.out(mode, o2, since, r)):
  match e:
    case Spec.Open{rest}:
      (l, q) = ag
      e.open(st, pd, out, mode, o2, since, rest, he, rb, r, er,
        pair.eqs(List.reverse(&2, Eng.Req, out), EL.look.st(st), List.reverse(&2, Eng.Req, o2), EL.Reading{}, l), hp, hw)
    case Spec.Refused{}:
      e.refused(st, pd, out, mode, o2, since, he, rb, r, er,
        pair.eqs(List.reverse(&2, Eng.Req, out), EL.look.st(st), List.reverse(&2, Eng.Req, o2), EL.Refusing{}, ag))
    case Spec.Upgraded{b}:
      e.up(st, pd, out, mode, o2, since, b, he, rb, r, er,
        p.eqs(st, pd, out, Eng.Rest{b}, Eng.pend.new(), List.reverse(&2, Eng.Req, List.reverse(&2, Eng.Req, o2)), ag),
        hp, hw)

def stp.at(+pp: Eng.P, +ww: Spec.W, -rb: Bytes(), -r: List<&2, U32>, er: {Bytes.to_list(rb) == r : List<&2, U32>},
  ag: EL.agree(pp, Spec.finish(ww)), hp: {pp == Eng.feed(r, Eng.p.new()) : Eng.P},
  hw: {ww == Spec.walk(r, Laws.w0()) : Spec.W}) ->
  StpRel(X.stp.of(pp, rb), Laws.px.of(ww, r)):
  match pp ww:
    case Eng.P{+st, +pd, +out} Spec.W{+mode, +o2, +since}:
      stp.end(st, pd, out, mode, o2, since, Spec.finish.end(mode, since), {==}, rb, r, er, ag, hp, hw)


# frame_sim at the bytes so far, one more byte in
def ag.at(-p: Eng.P, -w: Spec.W, +r: List<&2, U32>, +c: U32,
  hp: {Eng.step(p, c) == Eng.feed(Spec.snoc(r, c), Eng.p.new()) : Eng.P},
  hw: {Spec.next(w, c) == Spec.walk(Spec.snoc(r, c), Laws.w0()) : Spec.W}) ->
  EL.agree(Eng.step(p, c), Spec.finish(Spec.next(w, c))):
  %Equal.sym(Eng.P, Eng.step(p, c), Eng.feed(Spec.snoc(r, c), Eng.p.new()), hp) :
    EL.agree(_, Spec.finish(Spec.next(w, c)))
  %Equal.sym(Spec.W, Spec.next(w, c), Spec.walk(Spec.snoc(r, c), Laws.w0()), hw) :
    EL.agree(Eng.feed(Spec.snoc(r, c), Eng.p.new()), Spec.finish(_))
  EL.frame_sim(Spec.snoc(r, c))

# LEMMA: one byte. The proxy's step and the reference's, from scans that
# agree, leave results that agree.
def stp.is(+p: Eng.P, +rb: Bytes(), +w: Spec.W, +r: List<&2, U32>, +c: U32, rel: Laws.Waits(X.Scan{p, rb}, w, r)) ->
  StpRel(X.stp(p, c, rb), Laws.px.stp(w, c, r)):
  (e1, e23) = rel
  (e2, e3) = e23
  +hp = Equal.trans(Eng.P, Eng.step(p, c), Eng.step(Eng.feed(r, Eng.p.new()), c),
    Eng.feed(Spec.snoc(r, c), Eng.p.new()),
    Equal.cong(Eng.P, Eng.P, x => Eng.step(x, c), p, Eng.feed(r, Eng.p.new()), e2),
    Equal.sym(Eng.P, Eng.feed(Spec.snoc(r, c), Eng.p.new()), Eng.step(Eng.feed(r, Eng.p.new()), c),
      feed.snoc(r, c, Eng.p.new())))
  +hw = Equal.trans(Spec.W, Spec.next(w, c), Spec.next(Spec.walk(r, Laws.w0()), c),
    Spec.walk(Spec.snoc(r, c), Laws.w0()),
    Equal.cong(Spec.W, Spec.W, x => Spec.next(x, c), w, Spec.walk(r, Laws.w0()), e3),
    Equal.sym(Spec.W, Spec.walk(Spec.snoc(r, c), Laws.w0()), Spec.next(Spec.walk(r, Laws.w0()), c),
      walk.snoc(r, c, Laws.w0())))
  stp.at(Eng.step(p, c), Spec.next(w, c), Bytes.push(rb, c), Spec.snoc(r, c),
    Equal.trans(List<&2, U32>, Bytes.to_list(Bytes.push(rb, c)),
      List.append(&2, U32, Bytes.to_list(rb), Con{c, Nil{}}), Spec.snoc(r, c),
      Bytes.push_list(rb, c),
      Equal.cong(List<&2, U32>, List<&2, U32>, x => List.append(&2, U32, x, Con{c, Nil{}}), Bytes.to_list(rb), r, e1)),
    ag.at(p, w, r, c, hp, hw), hp, hw)

# a request taken on both sides, with the same bytes and reading
def took.cons(-rb: Bytes(), -q: Eng.Req, -r: List<&2, U32>, -q2: Eng.Req, +acc: List<&2, X.Took>,
  -acc2: List<&2, Laws.PTook>, rel: {Bytes.to_list(rb) == r : List<&2, U32>} & {q == q2 : Eng.Req},
  ha: {Laws.tooks.of(acc) == acc2 : List<&2, Laws.PTook>}) ->
  {Laws.tooks.of(Con{X.Took{rb, q}, acc}) == Con{Laws.PTook{r, q2}, acc2} : List<&2, Laws.PTook>}:
  (e1, e2) = rel
  %e1 :
    {Laws.tooks.of(Con{X.Took{rb, q}, acc}) == Con{Laws.PTook{_, q2}, acc2} : List<&2, Laws.PTook>}
  %e2 :
    {Laws.tooks.of(Con{X.Took{rb, q}, acc}) == Con{Laws.PTook{Bytes.to_list(rb), _}, acc2} : List<&2, Laws.PTook>}
  %ha :
    {Laws.tooks.of(Con{X.Took{rb, q}, acc}) == Con{Laws.PTook{Bytes.to_list(rb), q}, _} : List<&2, Laws.PTook>}
  {==}

# and the taken, reversed at the end, agree
def done.rel(+acc: List<&2, X.Took>, -acc2: List<&2, Laws.PTook>,
  ha: {Laws.tooks.of(acc) == acc2 : List<&2, Laws.PTook>}) ->
  {Laws.tooks.of(List.reverse(&2, X.Took, acc)) == List.reverse(&2, Laws.PTook, acc2) : List<&2, Laws.PTook>}:
  Equal.trans(List<&2, Laws.PTook>, Laws.tooks.of(List.reverse(&2, X.Took, acc)),
    List.reverse(&2, Laws.PTook, Laws.tooks.of(acc)), List.reverse(&2, Laws.PTook, acc2),
    tooks.rev(acc),
    Equal.cong(List<&2, Laws.PTook>, List<&2, Laws.PTook>, xs => List.reverse(&2, Laws.PTook, xs),
      Laws.tooks.of(acc), acc2, ha))

# LEMMA: a read. The proxy's scan of a read and the reference's walk of
# its bytes, from steps that agree, take the same requests and end the
# same way.
def go.is(s: Bytes(), a: X.Stp, b: Laws.PStp, +acc: List<&2, X.Took>, -acc2: List<&2, Laws.PTook>,
  ha: {Laws.tooks.of(acc) == acc2 : List<&2, Laws.PTook>}, rel: StpRel(a, b)) ->
  Laws.Scans(X.scan.go(s, a, acc), Laws.px.go(Bytes.to_list(s), b, acc2)):
  match s:
    case SNil{}:
      match a b:
        case X.SGo{+p, +rb} Laws.PGo{+w, +r}:
          (done.rel(acc, acc2, ha), rel)
        case X.SGo{p, rb} Laws.PMsg{r, q2}:
          match rel:
        case X.SGo{p, rb} Laws.PUp{r, q2}:
          match rel:
        case X.SGo{p, rb} Laws.PBad{}:
          match rel:
        case X.SMsg{rb, q} Laws.PGo{w, r}:
          match rel:
        case X.SMsg{rb, q} Laws.PMsg{r, q2}:
          (done.rel(Con{X.Took{rb, q}, acc}, Con{Laws.PTook{r, q2}, acc2}, took.cons(rb, q, r, q2, acc, acc2, rel, ha)), ({==}, ({==}, {==})))
        case X.SMsg{rb, q} Laws.PUp{r, q2}:
          match rel:
        case X.SMsg{rb, q} Laws.PBad{}:
          match rel:
        case X.SUp{rb, q} Laws.PGo{w, r}:
          match rel:
        case X.SUp{rb, q} Laws.PMsg{r, q2}:
          match rel:
        case X.SUp{rb, q} Laws.PUp{r, q2}:
          (done.rel(Con{X.Took{rb, q}, acc}, Con{Laws.PTook{r, q2}, acc2}, took.cons(rb, q, r, q2, acc, acc2, rel, ha)), Unit{})
        case X.SUp{rb, q} Laws.PBad{}:
          match rel:
        case X.SBad{} Laws.PGo{w, r}:
          match rel:
        case X.SBad{} Laws.PMsg{r, q2}:
          match rel:
        case X.SBad{} Laws.PUp{r, q2}:
          match rel:
        case X.SBad{} Laws.PBad{}:
          (done.rel(acc, acc2, ha), Unit{})
    case SCon{Chr{+c}, t}:
      match a b:
        case X.SGo{+p, +rb} Laws.PGo{+w, +r}:
          go.is(t, X.stp(p, c, rb), Laws.px.stp(w, c, r), acc, acc2, ha, stp.is(p, rb, w, r, c, rel))
        case X.SGo{p, rb} Laws.PMsg{r, q2}:
          match rel:
        case X.SGo{p, rb} Laws.PUp{r, q2}:
          match rel:
        case X.SGo{p, rb} Laws.PBad{}:
          match rel:
        case X.SMsg{rb, q} Laws.PGo{w, r}:
          match rel:
        case X.SMsg{rb, q} Laws.PMsg{r, q2}:
          go.is(t, X.stp(Eng.p.new(), c, ""), Laws.px.stp(Laws.w0(), c, Nil{}), Con{X.Took{rb, q}, acc}, Con{Laws.PTook{r, q2}, acc2}, took.cons(rb, q, r, q2, acc, acc2, rel, ha), stp.is(Eng.p.new(), "", Laws.w0(), Nil{}, c, ({==}, ({==}, {==}))))
        case X.SMsg{rb, q} Laws.PUp{r, q2}:
          match rel:
        case X.SMsg{rb, q} Laws.PBad{}:
          match rel:
        case X.SUp{rb, q} Laws.PGo{w, r}:
          match rel:
        case X.SUp{rb, q} Laws.PMsg{r, q2}:
          match rel:
        case X.SUp{rb, q} Laws.PUp{r, q2}:
          (done.rel(Con{X.Took{rb, q}, acc}, Con{Laws.PTook{r, q2}, acc2}, took.cons(rb, q, r, q2, acc, acc2, rel, ha)), Unit{})
        case X.SUp{rb, q} Laws.PBad{}:
          match rel:
        case X.SBad{} Laws.PGo{w, r}:
          match rel:
        case X.SBad{} Laws.PMsg{r, q2}:
          match rel:
        case X.SBad{} Laws.PUp{r, q2}:
          match rel:
        case X.SBad{} Laws.PBad{}:
          (done.rel(acc, acc2, ha), Unit{})

# A stream cut in two
# ===================

# requests taken before, put in front
def pre(xs: List<&2, Laws.PTook>, f: Laws.PScanned) -> Laws.PScanned:
  match f:
    case Laws.PScanned{us, u}:
      Laws.PScanned{List.append(&2, Laws.PTook, xs, us), u}

# the rest of a stream, walked on from where the first part ended
def then(f: Laws.PScanned, ys: List<&2, U32>) -> Laws.PScanned:
  match f:
    case Laws.PScanned{us, u}:
      match u:
        case Laws.PWait{w, raw}:
          Laws.px.go(ys, Laws.PGo{w, raw}, List.reverse(&2, Laws.PTook, us))
        case Laws.PRefused{}:
          Laws.PScanned{us, Laws.PRefused{}}
        case Laws.PUpgraded{}:
          Laws.PScanned{us, Laws.PUpgraded{}}

def pre.pre(+a: List<&2, Laws.PTook>, +b: List<&2, Laws.PTook>, f: Laws.PScanned) ->
  {pre(List.append(&2, Laws.PTook, a, b), f) == pre(a, pre(b, f)) : Laws.PScanned}:
  match f:
    case Laws.PScanned{us, u}:
      Equal.cong(List<&2, Laws.PTook>, Laws.PScanned, x => Laws.PScanned{x, u},
        List.append(&2, Laws.PTook, List.append(&2, Laws.PTook, a, b), us),
        List.append(&2, Laws.PTook, a, List.append(&2, Laws.PTook, b, us)), app.assoc(Laws.PTook, a, b, us))

def done.nil(+acc: List<&2, Laws.PTook>, u: Laws.PTail) ->
  {Laws.px.done(acc, u) == pre(List.reverse(&2, Laws.PTook, acc), Laws.px.done(Nil{}, u)) : Laws.PScanned}:
  Equal.cong(List<&2, Laws.PTook>, Laws.PScanned, x => Laws.PScanned{x, u}, List.reverse(&2, Laws.PTook, acc),
    List.append(&2, Laws.PTook, List.reverse(&2, Laws.PTook, acc), Nil{}),
    Equal.sym(List<&2, Laws.PTook>, List.append(&2, Laws.PTook, List.reverse(&2, Laws.PTook, acc), Nil{}),
      List.reverse(&2, Laws.PTook, acc), app.nil(Laws.PTook, List.reverse(&2, Laws.PTook, acc))))

def done.one(+x: Laws.PTook, +acc: List<&2, Laws.PTook>, u: Laws.PTail) ->
  {Laws.px.done(Con{x, acc}, u) == pre(List.reverse(&2, Laws.PTook, acc), Laws.px.done(Con{x, Nil{}}, u)) :
    Laws.PScanned}:
  Equal.cong(List<&2, Laws.PTook>, Laws.PScanned, y => Laws.PScanned{y, u}, List.reverse(&2, Laws.PTook, Con{x, acc}),
    List.append(&2, Laws.PTook, List.reverse(&2, Laws.PTook, acc), Con{x, Nil{}}), rev.con(Laws.PTook, x, acc))

# the requests taken before a walk are in front of what it takes
def go.acc(+bs: List<&2, U32>, st: Laws.PStp, +acc: List<&2, Laws.PTook>) ->
  {Laws.px.go(bs, st, acc) == pre(List.reverse(&2, Laws.PTook, acc), Laws.px.go(bs, st, Nil{})) : Laws.PScanned}:
  match bs st:
    case Nil{} Laws.PBad{}:
      done.nil(acc, Laws.PRefused{})
    case Nil{} Laws.PUp{raw, r}:
      done.one(Laws.PTook{raw, r}, acc, Laws.PUpgraded{})
    case Nil{} Laws.PGo{w, raw}:
      done.nil(acc, Laws.PWait{w, raw})
    case Nil{} Laws.PMsg{raw, r}:
      done.one(Laws.PTook{raw, r}, acc, Laws.PWait{Laws.w0(), Nil{}})
    case Con{c, t} Laws.PBad{}:
      done.nil(acc, Laws.PRefused{})
    case Con{c, t} Laws.PUp{raw, r}:
      done.one(Laws.PTook{raw, r}, acc, Laws.PUpgraded{})
    case Con{+c, +t} Laws.PGo{w, raw}:
      go.acc(t, Laws.px.stp(w, c, raw), acc)
    case Con{+c, +t} Laws.PMsg{+raw, +r}:
      Equal.trans(Laws.PScanned, Laws.px.go(t, Laws.px.stp(Laws.w0(), c, Nil{}), Con{Laws.PTook{raw, r}, acc}),
        pre(List.reverse(&2, Laws.PTook, Con{Laws.PTook{raw, r}, acc}), Laws.px.go(t, Laws.px.stp(Laws.w0(), c, Nil{}), Nil{})),
        pre(List.reverse(&2, Laws.PTook, acc), Laws.px.go(t, Laws.px.stp(Laws.w0(), c, Nil{}), Con{Laws.PTook{raw, r}, Nil{}})),
        go.acc(t, Laws.px.stp(Laws.w0(), c, Nil{}), Con{Laws.PTook{raw, r}, acc}),
        Equal.trans(Laws.PScanned,
          pre(List.reverse(&2, Laws.PTook, Con{Laws.PTook{raw, r}, acc}), Laws.px.go(t, Laws.px.stp(Laws.w0(), c, Nil{}), Nil{})),
          pre(List.reverse(&2, Laws.PTook, acc), pre(Con{Laws.PTook{raw, r}, Nil{}}, Laws.px.go(t, Laws.px.stp(Laws.w0(), c, Nil{}), Nil{}))),
          pre(List.reverse(&2, Laws.PTook, acc), Laws.px.go(t, Laws.px.stp(Laws.w0(), c, Nil{}), Con{Laws.PTook{raw, r}, Nil{}})),
          %Equal.sym(List<&2, Laws.PTook>, List.reverse(&2, Laws.PTook, Con{Laws.PTook{raw, r}, acc}),
            List.append(&2, Laws.PTook, List.reverse(&2, Laws.PTook, acc), Con{Laws.PTook{raw, r}, Nil{}}),
            rev.con(Laws.PTook, Laws.PTook{raw, r}, acc)) :
            {pre(_, Laws.px.go(t, Laws.px.stp(Laws.w0(), c, Nil{}), Nil{})) ==
              pre(List.reverse(&2, Laws.PTook, acc), pre(Con{Laws.PTook{raw, r}, Nil{}}, Laws.px.go(t, Laws.px.stp(Laws.w0(), c, Nil{}), Nil{}))) :
              Laws.PScanned}
          pre.pre(List.reverse(&2, Laws.PTook, acc), Con{Laws.PTook{raw, r}, Nil{}},
            Laws.px.go(t, Laws.px.stp(Laws.w0(), c, Nil{}), Nil{})),
          Equal.cong(Laws.PScanned, Laws.PScanned, f => pre(List.reverse(&2, Laws.PTook, acc), f),
            pre(Con{Laws.PTook{raw, r}, Nil{}}, Laws.px.go(t, Laws.px.stp(Laws.w0(), c, Nil{}), Nil{})),
            Laws.px.go(t, Laws.px.stp(Laws.w0(), c, Nil{}), Con{Laws.PTook{raw, r}, Nil{}}),
            Equal.sym(Laws.PScanned, Laws.px.go(t, Laws.px.stp(Laws.w0(), c, Nil{}), Con{Laws.PTook{raw, r}, Nil{}}),
              pre(Con{Laws.PTook{raw, r}, Nil{}}, Laws.px.go(t, Laws.px.stp(Laws.w0(), c, Nil{}), Nil{})),
              go.acc(t, Laws.px.stp(Laws.w0(), c, Nil{}), Con{Laws.PTook{raw, r}, Nil{}})))))

# a walk over a stream is a walk over its first part, then its rest
def go.app0(ys: List<&2, U32>, st: Laws.PStp, +acc: List<&2, Laws.PTook>) ->
  {Laws.px.go(ys, st, acc) == then(Laws.px.go(Nil{}, st, acc), ys) : Laws.PScanned}:
  match ys st:
    case Nil{} Laws.PBad{}:
      {==}
    case Con{c, t} Laws.PBad{}:
      {==}
    case Nil{} Laws.PUp{raw, r}:
      {==}
    case Con{c, t} Laws.PUp{raw, r}:
      {==}
    case Nil{} Laws.PGo{w, raw}:
      %rev.rev(Laws.PTook, acc) : {Laws.px.go(Nil{}, Laws.PGo{w, raw}, _) ==
        Laws.px.go(Nil{}, Laws.PGo{w, raw}, List.reverse(&2, Laws.PTook, List.reverse(&2, Laws.PTook, acc))) :
        Laws.PScanned}
      {==}
    case Con{c, t} Laws.PGo{w, raw}:
      %rev.rev(Laws.PTook, acc) : {Laws.px.go(Con{c, t}, Laws.PGo{w, raw}, _) ==
        Laws.px.go(Con{c, t}, Laws.PGo{w, raw}, List.reverse(&2, Laws.PTook, List.reverse(&2, Laws.PTook, acc))) :
        Laws.PScanned}
      {==}
    case Nil{} Laws.PMsg{raw, r}:
      %rev.rev(Laws.PTook, Con{Laws.PTook{raw, r}, acc}) : {Laws.px.go(Nil{}, Laws.PGo{Laws.w0(), Nil{}}, _) ==
        Laws.px.go(Nil{}, Laws.PGo{Laws.w0(), Nil{}},
          List.reverse(&2, Laws.PTook, List.reverse(&2, Laws.PTook, Con{Laws.PTook{raw, r}, acc}))) : Laws.PScanned}
      {==}
    case Con{c, t} Laws.PMsg{raw, r}:
      %rev.rev(Laws.PTook, Con{Laws.PTook{raw, r}, acc}) : {Laws.px.go(Con{c, t}, Laws.PGo{Laws.w0(), Nil{}}, _) ==
        Laws.px.go(Con{c, t}, Laws.PGo{Laws.w0(), Nil{}},
          List.reverse(&2, Laws.PTook, List.reverse(&2, Laws.PTook, Con{Laws.PTook{raw, r}, acc}))) : Laws.PScanned}
      {==}

def go.app(xs: List<&2, U32>, +ys: List<&2, U32>, st: Laws.PStp, +acc: List<&2, Laws.PTook>) ->
  {Laws.px.go(List.append(&2, U32, xs, ys), st, acc) == then(Laws.px.go(xs, st, acc), ys) : Laws.PScanned}:
  match xs st:
    case Nil{} _:
      go.app0(ys, st, acc)
    case Con{c, t} Laws.PBad{}:
      {==}
    case Con{c, t} Laws.PUp{raw, r}:
      {==}
    case Con{+c, t} Laws.PGo{w, raw}:
      go.app(t, ys, Laws.px.stp(w, c, raw), acc)
    case Con{+c, t} Laws.PMsg{raw, r}:
      go.app(t, ys, Laws.px.stp(Laws.w0(), c, Nil{}), Con{Laws.PTook{raw, r}, acc})

# The reads of a connection
# =========================

# the proxy's connection so far against the reference's walk: the
# requests the reference took before (pre) and then the connection's
def RA(pre: List<&2, Laws.PTook>, c: Laws.Conn, f: Laws.PScanned) -> Type:
  match c f:
    case Laws.Conn{ts, t} Laws.PScanned{us, u}:
      {List.append(&2, Laws.PTook, pre, Laws.tooks.of(ts)) == us : List<&2, Laws.PTook>} & Laws.Tails(t, u)

def ra.rw(-ra1: List<&2, Laws.PTook>, -ra2: List<&2, Laws.PTook>, -c: Laws.Conn, -f: Laws.PScanned,
  e: {ra1 == ra2 : List<&2, Laws.PTook>}, h: RA(ra1, c, f)) -> RA(ra2, c, f):
  %e : RA(_, c, f)
  h

def more.ra(+ts: List<&2, X.Took>, c: Laws.Conn, f: Laws.PScanned, +ra: List<&2, Laws.PTook>,
  +us: List<&2, Laws.PTook>, hts: {Laws.tooks.of(ts) == us : List<&2, Laws.PTook>},
  h: RA(List.append(&2, Laws.PTook, ra, us), c, f)) -> RA(ra, Laws.conn.more(ts, c), f):
  match c f:
    case Laws.Conn{+ts2, t2} Laws.PScanned{us2, u2}:
      (h1, h2) = h
      (Equal.trans(List<&2, Laws.PTook>, List.append(&2, Laws.PTook, ra, Laws.tooks.of(List.append(&2, X.Took, ts, ts2))),
        List.append(&2, Laws.PTook, List.append(&2, Laws.PTook, ra, us), Laws.tooks.of(ts2)), us2,
        Equal.trans(List<&2, Laws.PTook>, List.append(&2, Laws.PTook, ra, Laws.tooks.of(List.append(&2, X.Took, ts, ts2))),
          List.append(&2, Laws.PTook, ra, List.append(&2, Laws.PTook, us, Laws.tooks.of(ts2))),
          List.append(&2, Laws.PTook, List.append(&2, Laws.PTook, ra, us), Laws.tooks.of(ts2)),
          %hts : {List.append(&2, Laws.PTook, ra, Laws.tooks.of(List.append(&2, X.Took, ts, ts2))) ==
            List.append(&2, Laws.PTook, ra, List.append(&2, Laws.PTook, _, Laws.tooks.of(ts2))) : List<&2, Laws.PTook>}
          Equal.cong(List<&2, Laws.PTook>, List<&2, Laws.PTook>, x => List.append(&2, Laws.PTook, ra, x),
            Laws.tooks.of(List.append(&2, X.Took, ts, ts2)),
            List.append(&2, Laws.PTook, Laws.tooks.of(ts), Laws.tooks.of(ts2)), tooks.app(ts, ts2)),
          Equal.sym(List<&2, Laws.PTook>, List.append(&2, Laws.PTook, List.append(&2, Laws.PTook, ra, us), Laws.tooks.of(ts2)),
            List.append(&2, Laws.PTook, ra, List.append(&2, Laws.PTook, us, Laws.tooks.of(ts2))),
            app.assoc(Laws.PTook, ra, us, Laws.tooks.of(ts2)))),
        h1), h2)

def tail.wait(+ts: List<&2, X.Took>, +sc2: X.Scan, +w2: Spec.W, +raw2: List<&2, U32>, +us: List<&2, Laws.PTook>,
  hts: {Laws.tooks.of(ts) == us : List<&2, Laws.PTook>}, wt: Laws.Waits(sc2, w2, raw2), +t: List<&2, Bytes()>,
  +ra: List<&2, Laws.PTook>,
  ih: @+sc: X.Scan -> @+w: Spec.W -> @+raw: List<&2, U32> -> @+pr: List<&2, Laws.PTook> -> Laws.Waits(sc, w, raw) ->
    RA(List.reverse(&2, Laws.PTook, pr), Laws.reads.go(t, sc), Laws.px.go(Bytes.to_list(Bytes.concat(t)), Laws.PGo{w, raw}, pr))) ->
  RA(ra, Laws.conn.more(ts, Laws.reads.go(t, sc2)), Laws.px.go(Bytes.to_list(Bytes.concat(t)), Laws.PGo{w2, raw2},
    List.reverse(&2, Laws.PTook, List.append(&2, Laws.PTook, ra, us)))):
  more.ra(ts, Laws.reads.go(t, sc2), Laws.px.go(Bytes.to_list(Bytes.concat(t)), Laws.PGo{w2, raw2},
      List.reverse(&2, Laws.PTook, List.append(&2, Laws.PTook, ra, us))), ra, us, hts,
    ra.rw(List.reverse(&2, Laws.PTook, List.reverse(&2, Laws.PTook, List.append(&2, Laws.PTook, ra, us))),
      List.append(&2, Laws.PTook, ra, us), Laws.reads.go(t, sc2),
      Laws.px.go(Bytes.to_list(Bytes.concat(t)), Laws.PGo{w2, raw2},
        List.reverse(&2, Laws.PTook, List.append(&2, Laws.PTook, ra, us))),
      rev.rev(Laws.PTook, List.append(&2, Laws.PTook, ra, us)),
      ih(sc2, w2, raw2, List.reverse(&2, Laws.PTook, List.append(&2, Laws.PTook, ra, us)), wt)))

def reads.tail(+ts: List<&2, X.Took>, tl: X.Tail, +us: List<&2, Laws.PTook>, u: Laws.PTail,
  hts: {Laws.tooks.of(ts) == us : List<&2, Laws.PTook>}, ht: Laws.Tails(tl, u), +t: List<&2, Bytes()>,
  +ra: List<&2, Laws.PTook>,
  ih: @+sc: X.Scan -> @+w: Spec.W -> @+raw: List<&2, U32> -> @+pr: List<&2, Laws.PTook> -> Laws.Waits(sc, w, raw) ->
    RA(List.reverse(&2, Laws.PTook, pr), Laws.reads.go(t, sc), Laws.px.go(Bytes.to_list(Bytes.concat(t)), Laws.PGo{w, raw}, pr))) ->
  RA(ra, Laws.reads.at(X.Scanned{ts, tl}, s2 => Laws.reads.go(t, s2)),
    then(pre(ra, Laws.PScanned{us, u}), Bytes.to_list(Bytes.concat(t)))):
  match tl u:
    case X.TWait{sc2} Laws.PWait{w2, raw2}:
      tail.wait(ts, sc2, w2, raw2, us, hts, ht, t, ra, ih)
    case X.TWait{sc2} Laws.PRefused{}:
      match ht:
    case X.TWait{sc2} Laws.PUpgraded{}:
      match ht:
    case X.TBad{} Laws.PWait{w2, raw2}:
      match ht:
    case X.TBad{} Laws.PRefused{}:
      (Equal.cong(List<&2, Laws.PTook>, List<&2, Laws.PTook>, x => List.append(&2, Laws.PTook, ra, x),
        Laws.tooks.of(ts), us, hts), Unit{})
    case X.TBad{} Laws.PUpgraded{}:
      match ht:
    case X.TUp{} Laws.PWait{w2, raw2}:
      match ht:
    case X.TUp{} Laws.PRefused{}:
      match ht:
    case X.TUp{} Laws.PUpgraded{}:
      (Equal.cong(List<&2, Laws.PTook>, List<&2, Laws.PTook>, x => List.append(&2, Laws.PTook, ra, x),
        Laws.tooks.of(ts), us, hts), Unit{})

def reads.step(sd: X.Scanned, f: Laws.PScanned, hs: Laws.Scans(sd, f), +t: List<&2, Bytes()>,
  +ra: List<&2, Laws.PTook>,
  ih: @+sc: X.Scan -> @+w: Spec.W -> @+raw: List<&2, U32> -> @+pr: List<&2, Laws.PTook> -> Laws.Waits(sc, w, raw) ->
    RA(List.reverse(&2, Laws.PTook, pr), Laws.reads.go(t, sc), Laws.px.go(Bytes.to_list(Bytes.concat(t)), Laws.PGo{w, raw}, pr))) ->
  RA(ra, Laws.reads.at(sd, s2 => Laws.reads.go(t, s2)), then(pre(ra, f), Bytes.to_list(Bytes.concat(t)))):
  match sd f:
    case X.Scanned{+ts, tl} Laws.PScanned{+us, u}:
      (hts, ht) = hs
      reads.tail(ts, tl, us, u, hts, ht, t, ra, ih)

def reads.con(+r: Bytes(), +t: List<&2, Bytes()>, +sc: X.Scan, +w: Spec.W, +raw: List<&2, U32>,
  +pr: List<&2, Laws.PTook>, wt: Laws.Waits(sc, w, raw),
  ih: @+sc: X.Scan -> @+w: Spec.W -> @+raw: List<&2, U32> -> @+pr: List<&2, Laws.PTook> -> Laws.Waits(sc, w, raw) ->
    RA(List.reverse(&2, Laws.PTook, pr), Laws.reads.go(t, sc), Laws.px.go(Bytes.to_list(Bytes.concat(t)), Laws.PGo{w, raw}, pr))) ->
  RA(List.reverse(&2, Laws.PTook, pr), Laws.reads.go(Con{r, t}, sc),
    then(pre(List.reverse(&2, Laws.PTook, pr), Laws.px.go(Bytes.to_list(r), Laws.PGo{w, raw}, Nil{})),
      Bytes.to_list(Bytes.concat(t)))):
  match sc:
    case X.Scan{+p, +rb}:
      reads.step(X.scan(r, X.Scan{p, rb}), Laws.px.go(Bytes.to_list(r), Laws.PGo{w, raw}, Nil{}),
        go.is(r, X.SGo{p, rb}, Laws.PGo{w, raw}, Nil{}, Nil{}, {==}, wt), t, List.reverse(&2, Laws.PTook, pr), ih)

# LEMMA: a connection's reads. Whatever the reads, from a scan that
# agrees with a walk, the connection agrees with the walk over the reads
# joined, the requests the walk took before in front.
def reads.is(rs: List<&2, Bytes()>, +sc: X.Scan, +w: Spec.W, +raw: List<&2, U32>, +pr: List<&2, Laws.PTook>,
  wt: Laws.Waits(sc, w, raw)) ->
  RA(List.reverse(&2, Laws.PTook, pr), Laws.reads.go(rs, sc),
    Laws.px.go(Bytes.to_list(Bytes.concat(rs)), Laws.PGo{w, raw}, pr)):
  match rs:
    case Nil{}:
      (app.nil(Laws.PTook, List.reverse(&2, Laws.PTook, pr)), wt)
    case Con{+r, +t}:
      %Equal.sym(List<&2, U32>, Bytes.to_list(Bytes.append(r, Bytes.concat(t))),
        List.append(&2, U32, Bytes.to_list(r), Bytes.to_list(Bytes.concat(t))),
        Bytes.to_list_append(r, Bytes.concat(t))) :
        RA(List.reverse(&2, Laws.PTook, pr), Laws.reads.go(Con{r, t}, sc), Laws.px.go(_, Laws.PGo{w, raw}, pr))
      %Equal.sym(Laws.PScanned,
        Laws.px.go(List.append(&2, U32, Bytes.to_list(r), Bytes.to_list(Bytes.concat(t))), Laws.PGo{w, raw}, pr),
        then(Laws.px.go(Bytes.to_list(r), Laws.PGo{w, raw}, pr), Bytes.to_list(Bytes.concat(t))),
        go.app(Bytes.to_list(r), Bytes.to_list(Bytes.concat(t)), Laws.PGo{w, raw}, pr)) :
        RA(List.reverse(&2, Laws.PTook, pr), Laws.reads.go(Con{r, t}, sc), _)
      %Equal.sym(Laws.PScanned, Laws.px.go(Bytes.to_list(r), Laws.PGo{w, raw}, pr),
        pre(List.reverse(&2, Laws.PTook, pr), Laws.px.go(Bytes.to_list(r), Laws.PGo{w, raw}, Nil{})),
        go.acc(Bytes.to_list(r), Laws.PGo{w, raw}, pr)) :
        RA(List.reverse(&2, Laws.PTook, pr), Laws.reads.go(Con{r, t}, sc), then(_, Bytes.to_list(Bytes.concat(t))))
      reads.con(r, t, sc, w, raw, pr, wt,
        sc2 => w2 => raw2 => pr2 => wt2 => reads.is(t, sc2, w2, raw2, pr2, wt2))

def ra.conns(c: Laws.Conn, f: Laws.PScanned, h: RA(Nil{}, c, f)) -> Laws.Conns(c, f):
  match c f:
    case Laws.Conn{ts, t} Laws.PScanned{us, u}:
      h

def Laws.scan_is_spec(rs):
  ra.conns(Laws.reads(rs), Laws.frame(Bytes.to_list(Bytes.concat(rs))),
    reads.is(rs, X.scan.new(), Laws.w0(), Nil{}, Nil{}, ({==}, ({==}, {==}))))
