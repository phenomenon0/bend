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

# spec.bend's walk and the requests it has done
# ==============================================
#
# frames_agree: the reference framing restarts a fresh walk after each
# request, frame() walks on. The two are one walk because nothing the
# walk does looks at the requests it has done: every step only puts one
# more in front of them. shift puts a list of done requests behind a
# walk's own; each of spec.bend's step functions, given done requests o,
# is the same function given none, shifted by o.

def shift(w: Spec.W, o: List<&2, Eng.Req>) -> Spec.W:
  match w:
    case Spec.W{m, x, s}:
      Spec.W{m, List.append(&2, Eng.Req, x, o), s}

def emit.go.par(r: Eng.Req, -o: List<&2, Eng.Req>) ->
  {Spec.emit.go(r, o) == shift(Spec.emit.go(r, Nil{}), o) : Spec.W}:
  match r:
    case Eng.Req{m, p, b, cl, ws, k}:
      {==}

def emit.par(+h: Spec.Head, +body: List<&2, U32>, -o: List<&2, Eng.Req>) ->
  {Spec.emit(h, body, o) == shift(Spec.emit(h, body, Nil{}), o) : Spec.W}:
  emit.go.par(Spec.req(h, body), o)

def head.body.par(z: Bool, +n: U32, +h: Spec.Head, -o: List<&2, Eng.Req>, -s: List<&2, U32>) ->
  {Spec.head.body(z, n, h, o, s) == shift(Spec.head.body(z, n, h, Nil{}, s), o) : Spec.W}:
  match z:
    case True{}:
      emit.par(h, Nil{}, o)
    case False{}:
      {==}

def head.at.par(ok: Bool, b: Spec.Body, +h: Spec.Head, -o: List<&2, Eng.Req>, -s: List<&2, U32>) ->
  {Spec.head.at(ok, b, h, o, s) == shift(Spec.head.at(ok, b, h, Nil{}, s), o) : Spec.W}:
  match ok b:
    case False{} _:
      {==}
    case True{} Spec.BBad{}:
      {==}
    case True{} Spec.BNone{}:
      emit.par(h, Nil{}, o)
    case True{} Spec.BLen{+n}:
      head.body.par(U32.is_zero(n), n, h, o, s)
    case True{} Spec.BChunked{}:
      {==}

def head.done.par(h: Spec.Head, -o: List<&2, Eng.Req>, -s: List<&2, U32>) ->
  {Spec.head.done(h, o, s) == shift(Spec.head.done(h, Nil{}, s), o) : Spec.W}:
  match h:
    case Spec.Head{m, t, +l, cl, +hs, k, u, c, v, f}:
      match f:
        case Eng.Fx{+v10, ka, +te}:
          head.at.par(Spec.hosts.ok(v10, hs), Spec.body.of(te, v10, l),
            Spec.Head{m, t, l, cl, hs, k, u, c, v, Eng.Fx{v10, ka, te}}, o, s)

def chunk.paid.par(over: Bool, +h: Spec.Head, +at: Spec.At, +n: U32, +got: List<&2, U32>, +left: U32,
  -o: List<&2, Eng.Req>, -s: List<&2, U32>) ->
  {Spec.chunk.paid(over, h, at, n, got, left, o, s) == shift(Spec.chunk.paid(over, h, at, n, got, left, Nil{}, s), o) : Spec.W}:
  match over:
    case True{}:
      {==}
    case False{}:
      {==}

def chunk.to.par(paid: Bool, +h: Spec.Head, +at: Spec.At, +n: U32, +got: List<&2, U32>, +left: U32,
  -o: List<&2, Eng.Req>, -s: List<&2, U32>) ->
  {Spec.chunk.to(paid, h, at, n, got, left, o, s) == shift(Spec.chunk.to(paid, h, at, n, got, left, Nil{}, s), o) : Spec.W}:
  match paid:
    case True{}:
      chunk.paid.par(U32.is_le(left, n), h, at, n, got, left, o, s)
    case False{}:
      {==}

def chunk.line.par(z: Bool, +h: Spec.Head, +n: U32, +got: List<&2, U32>, +left: U32, -o: List<&2, Eng.Req>,
  -s: List<&2, U32>) ->
  {Spec.chunk.line(z, h, n, got, left, o, s) == shift(Spec.chunk.line(z, h, n, got, left, Nil{}, s), o) : Spec.W}:
  match z:
    case True{}:
      {==}
    case False{}:
      {==}

def chunk.go.par(g: Spec.Go, +h: Spec.Head, +n: U32, +got: List<&2, U32>, +left: U32, -o: List<&2, Eng.Req>,
  -s: List<&2, U32>) ->
  {Spec.chunk.go(g, h, n, got, left, o, s) == shift(Spec.chunk.go(g, h, n, got, left, Nil{}, s), o) : Spec.W}:
  match g:
    case Spec.GBad{}:
      {==}
    case Spec.GTo{at, paid}:
      chunk.to.par(paid, h, at, n, got, left, o, s)
    case Spec.GDigit{+d}:
      chunk.paid.par(U32.is_le(left, (n * 16 + d : U32)), h, Spec.ASize{}, (n * 16 + d : U32), got, left, o, s)
    case Spec.GLine{}:
      chunk.line.par(U32.is_zero(n), h, n, got, left, o, s)
    case Spec.GDone{}:
      emit.par(h, got, o)

def data.byte.par(more: Nat, +c: U32, +h: Spec.Head, +got: List<&2, U32>, +left: U32, -o: List<&2, Eng.Req>,
  -s: List<&2, U32>) ->
  {Spec.data.byte(more, c, h, got, left, o, s) == shift(Spec.data.byte(more, c, h, got, left, Nil{}, s), o) : Spec.W}:
  match more:
    case 0n:
      {==}
    case 1n+q:
      {==}

def req.ok.par(v11: Bool, v10: Bool, +m: List<&2, U32>, +t: List<&2, U32>, -o: List<&2, Eng.Req>,
  -s: List<&2, U32>) ->
  {Spec.req.ok(v11, v10, m, t, o, s) == shift(Spec.req.ok(v11, v10, m, t, Nil{}, s), o) : Spec.W}:
  match v11 v10:
    case True{} _:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def req.cr.par(v: Spec.RLine, -o: List<&2, Eng.Req>, -s: List<&2, U32>) ->
  {Spec.req.cr(v, o, s) == shift(Spec.req.cr(v, Nil{}, s), o) : Spec.W}:
  match v:
    case Spec.RNone{}:
      {==}
    case Spec.RVer{m, t, +ver}:
      req.ok.par(Spec.eq(Bytes.from_list(ver), "HTTP/1.1"), Spec.eq(Bytes.from_list(ver), "HTTP/1.0"), m, t, o, s)
    case Spec.RMeth{m}:
      {==}
    case Spec.RTarget{m, t}:
      {==}
    case Spec.RBad{}:
      {==}

def field.next.par(mh: Maybe<&2, Spec.Head>, -o: List<&2, Eng.Req>, -s: List<&2, U32>) ->
  {Spec.field.next(mh, o, s) == shift(Spec.field.next(mh, Nil{}, s), o) : Spec.W}:
  match mh:
    case Some{h}:
      {==}
    case None{}:
      {==}

def field.cr.par(+h: Spec.Head, v: Spec.FLine, -o: List<&2, Eng.Req>, -s: List<&2, U32>) ->
  {Spec.field.cr(h, v, o, s) == shift(Spec.field.cr(h, v, Nil{}, s), o) : Spec.W}:
  match v:
    case Spec.FEmpty{}:
      {==}
    case Spec.FVal{val}:
      field.next.par(Spec.field.done(h, val), o, s)
    case Spec.FName{n}:
      {==}
    case Spec.FBad{}:
      {==}

def req.byte.par(k: Eng.Cls, +c: U32, +cur: List<&2, U32>, -o: List<&2, Eng.Req>, -s: List<&2, U32>) ->
  {Spec.req.byte(k, c, cur, o, s) == shift(Spec.req.byte(k, c, cur, Nil{}, s), o) : Spec.W}:
  match k:
    case Eng.KSp{}:
      {==}
    case Eng.KHt{}:
      {==}
    case Eng.KCr{}:
      req.cr.par(Spec.req.view(cur), o, s)
    case Eng.KLf{}:
      {==}
    case Eng.KCo{}:
      {==}
    case Eng.KCm{}:
      {==}
    case Eng.KDg{}:
      {==}
    case Eng.KTk{}:
      {==}
    case Eng.KVc{}:
      {==}
    case Eng.KCt{}:
      {==}

def field.byte.par(k: Eng.Cls, +c: U32, +h: Spec.Head, +cur: List<&2, U32>, -o: List<&2, Eng.Req>,
  -s: List<&2, U32>) ->
  {Spec.field.byte(k, c, h, cur, o, s) == shift(Spec.field.byte(k, c, h, cur, Nil{}, s), o) : Spec.W}:
  match k:
    case Eng.KSp{}:
      {==}
    case Eng.KHt{}:
      {==}
    case Eng.KCr{}:
      field.cr.par(h, Spec.field.view(cur), o, s)
    case Eng.KLf{}:
      {==}
    case Eng.KCo{}:
      {==}
    case Eng.KCm{}:
      {==}
    case Eng.KDg{}:
      {==}
    case Eng.KTk{}:
      {==}
    case Eng.KVc{}:
      {==}
    case Eng.KCt{}:
      {==}

def blank.byte.par(k: Eng.Cls, -o: List<&2, Eng.Req>, -s: List<&2, U32>) ->
  {Spec.blank.byte(k, o, s) == shift(Spec.blank.byte(k, Nil{}, s), o) : Spec.W}:
  match k:
    case Eng.KSp{}:
      {==}
    case Eng.KHt{}:
      {==}
    case Eng.KCr{}:
      {==}
    case Eng.KLf{}:
      {==}
    case Eng.KCo{}:
      {==}
    case Eng.KCm{}:
      {==}
    case Eng.KDg{}:
      {==}
    case Eng.KTk{}:
      {==}
    case Eng.KVc{}:
      {==}
    case Eng.KCt{}:
      {==}

def eol.byte.par(k: Eng.Cls, +h: Spec.Head, -o: List<&2, Eng.Req>, -s: List<&2, U32>) ->
  {Spec.eol.byte(k, h, o, s) == shift(Spec.eol.byte(k, h, Nil{}, s), o) : Spec.W}:
  match k:
    case Eng.KSp{}:
      {==}
    case Eng.KHt{}:
      {==}
    case Eng.KCr{}:
      {==}
    case Eng.KLf{}:
      {==}
    case Eng.KCo{}:
      {==}
    case Eng.KCm{}:
      {==}
    case Eng.KDg{}:
      {==}
    case Eng.KTk{}:
      {==}
    case Eng.KVc{}:
      {==}
    case Eng.KCt{}:
      {==}

def eoh.byte.par(k: Eng.Cls, +h: Spec.Head, -o: List<&2, Eng.Req>, -s: List<&2, U32>) ->
  {Spec.eoh.byte(k, h, o, s) == shift(Spec.eoh.byte(k, h, Nil{}, s), o) : Spec.W}:
  match k:
    case Eng.KSp{}:
      {==}
    case Eng.KHt{}:
      {==}
    case Eng.KCr{}:
      {==}
    case Eng.KLf{}:
      head.done.par(h, o, s)
    case Eng.KCo{}:
      {==}
    case Eng.KCm{}:
      {==}
    case Eng.KDg{}:
      {==}
    case Eng.KTk{}:
      {==}
    case Eng.KVc{}:
      {==}
    case Eng.KCt{}:
      {==}

def body.byte.par(more: Nat, +c: U32, +h: Spec.Head, +got: List<&2, U32>, -o: List<&2, Eng.Req>,
  -s: List<&2, U32>) ->
  {Spec.body.byte(more, c, h, got, o, s) == shift(Spec.body.byte(more, c, h, got, Nil{}, s), o) : Spec.W}:
  match more:
    case 0n:
      emit.par(h, Spec.snoc(got, c), o)
    case 1n+q:
      {==}

def next.at.par(mode: Spec.Mode, +k: Eng.Cls, +c: U32, -o: List<&2, Eng.Req>, -s: List<&2, U32>) ->
  {Spec.next.at(mode, k, c, o, s) == shift(Spec.next.at(mode, k, c, Nil{}, s), o) : Spec.W}:
  match mode:
    case Spec.MReq{cur}:
      req.byte.par(k, c, cur, o, s)
    case Spec.MBlank{}:
      blank.byte.par(k, o, s)
    case Spec.MField{h, cur}:
      field.byte.par(k, c, h, cur, o, s)
    case Spec.MEol{h}:
      eol.byte.par(k, h, o, s)
    case Spec.MEoh{h}:
      eoh.byte.par(k, h, o, s)
    case Spec.MBody{h, more, got}:
      body.byte.par(more, c, h, got, o, s)
    case Spec.MChunk{h, at, n, got, left}:
      chunk.go.par(Spec.chunk.step(at, Spec.xk.of(k, c)), h, n, got, left, o, s)
    case Spec.MData{h, more, got, left}:
      data.byte.par(more, c, h, got, left, o, s)
    case Spec.MUp{got}:
      {==}
    case Spec.MBad{}:
      {==}

# LEMMA: a step does not look at the requests done
def next.par(+m: Spec.Mode, -o: List<&2, Eng.Req>, +s: List<&2, U32>, +c: U32) ->
  {Spec.next(Spec.W{m, o, s}, c) == shift(Spec.next(Spec.W{m, Nil{}, s}, c), o) : Spec.W}:
  next.at.par(m, Spec.cls(c), c, o, Spec.snoc(s, c))

# and when a step does a request, it is the only one, and the walk
# starts again: a fresh line, nothing since, or what follows an upgrade
def Shape(w: Spec.W) -> Type:
  match w:
    case Spec.W{m, x, s}:
      match x:
        case Nil{}:
          Unit
        case Con{r, t}:
          {t == Nil{} : List<&2, Eng.Req>} & {s == Nil{} : List<&2, U32>} & {m == Spec.emit.mode(Eng.req.ws(r)) : Spec.Mode}

def emit.go.shape(r: Eng.Req) ->
  Shape(Spec.emit.go(r, Nil{})):
  match r:
    case Eng.Req{m, p, b, cl, ws, k}:
      ({==}, ({==}, {==}))

def emit.shape(+h: Spec.Head, +body: List<&2, U32>) ->
  Shape(Spec.emit(h, body, Nil{})):
  emit.go.shape(Spec.req(h, body))

def head.body.shape(z: Bool, +n: U32, +h: Spec.Head, -s: List<&2, U32>) ->
  Shape(Spec.head.body(z, n, h, Nil{}, s)):
  match z:
    case True{}:
      emit.shape(h, Nil{})
    case False{}:
      Unit{}

def head.at.shape(ok: Bool, b: Spec.Body, +h: Spec.Head, -s: List<&2, U32>) ->
  Shape(Spec.head.at(ok, b, h, Nil{}, s)):
  match ok b:
    case False{} _:
      Unit{}
    case True{} Spec.BBad{}:
      Unit{}
    case True{} Spec.BNone{}:
      emit.shape(h, Nil{})
    case True{} Spec.BLen{+n}:
      head.body.shape(U32.is_zero(n), n, h, s)
    case True{} Spec.BChunked{}:
      Unit{}

def head.done.shape(h: Spec.Head, -s: List<&2, U32>) ->
  Shape(Spec.head.done(h, Nil{}, s)):
  match h:
    case Spec.Head{m, t, +l, cl, +hs, k, u, c, v, f}:
      match f:
        case Eng.Fx{+v10, ka, +te}:
          head.at.shape(Spec.hosts.ok(v10, hs), Spec.body.of(te, v10, l),
            Spec.Head{m, t, l, cl, hs, k, u, c, v, Eng.Fx{v10, ka, te}}, s)

def chunk.paid.shape(over: Bool, +h: Spec.Head, +at: Spec.At, +n: U32, +got: List<&2, U32>, +left: U32,
  -s: List<&2, U32>) ->
  Shape(Spec.chunk.paid(over, h, at, n, got, left, Nil{}, s)):
  match over:
    case True{}:
      Unit{}
    case False{}:
      Unit{}

def chunk.to.shape(paid: Bool, +h: Spec.Head, +at: Spec.At, +n: U32, +got: List<&2, U32>, +left: U32,
  -s: List<&2, U32>) ->
  Shape(Spec.chunk.to(paid, h, at, n, got, left, Nil{}, s)):
  match paid:
    case True{}:
      chunk.paid.shape(U32.is_le(left, n), h, at, n, got, left, s)
    case False{}:
      Unit{}

def chunk.line.shape(z: Bool, +h: Spec.Head, +n: U32, +got: List<&2, U32>, +left: U32,
  -s: List<&2, U32>) ->
  Shape(Spec.chunk.line(z, h, n, got, left, Nil{}, s)):
  match z:
    case True{}:
      Unit{}
    case False{}:
      Unit{}

def chunk.go.shape(g: Spec.Go, +h: Spec.Head, +n: U32, +got: List<&2, U32>, +left: U32,
  -s: List<&2, U32>) ->
  Shape(Spec.chunk.go(g, h, n, got, left, Nil{}, s)):
  match g:
    case Spec.GBad{}:
      Unit{}
    case Spec.GTo{at, paid}:
      chunk.to.shape(paid, h, at, n, got, left, s)
    case Spec.GDigit{+d}:
      chunk.paid.shape(U32.is_le(left, (n * 16 + d : U32)), h, Spec.ASize{}, (n * 16 + d : U32), got, left, s)
    case Spec.GLine{}:
      chunk.line.shape(U32.is_zero(n), h, n, got, left, s)
    case Spec.GDone{}:
      emit.shape(h, got)

def data.byte.shape(more: Nat, +c: U32, +h: Spec.Head, +got: List<&2, U32>, +left: U32,
  -s: List<&2, U32>) ->
  Shape(Spec.data.byte(more, c, h, got, left, Nil{}, s)):
  match more:
    case 0n:
      Unit{}
    case 1n+q:
      Unit{}

def req.ok.shape(v11: Bool, v10: Bool, +m: List<&2, U32>, +t: List<&2, U32>,
  -s: List<&2, U32>) ->
  Shape(Spec.req.ok(v11, v10, m, t, Nil{}, s)):
  match v11 v10:
    case True{} _:
      Unit{}
    case False{} True{}:
      Unit{}
    case False{} False{}:
      Unit{}

def req.cr.shape(v: Spec.RLine, -s: List<&2, U32>) ->
  Shape(Spec.req.cr(v, Nil{}, s)):
  match v:
    case Spec.RNone{}:
      Unit{}
    case Spec.RVer{m, t, +ver}:
      req.ok.shape(Spec.eq(Bytes.from_list(ver), "HTTP/1.1"), Spec.eq(Bytes.from_list(ver), "HTTP/1.0"), m, t, s)
    case Spec.RMeth{m}:
      Unit{}
    case Spec.RTarget{m, t}:
      Unit{}
    case Spec.RBad{}:
      Unit{}

def field.next.shape(mh: Maybe<&2, Spec.Head>, -s: List<&2, U32>) ->
  Shape(Spec.field.next(mh, Nil{}, s)):
  match mh:
    case Some{h}:
      Unit{}
    case None{}:
      Unit{}

def field.cr.shape(+h: Spec.Head, v: Spec.FLine, -s: List<&2, U32>) ->
  Shape(Spec.field.cr(h, v, Nil{}, s)):
  match v:
    case Spec.FEmpty{}:
      Unit{}
    case Spec.FVal{val}:
      field.next.shape(Spec.field.done(h, val), s)
    case Spec.FName{n}:
      Unit{}
    case Spec.FBad{}:
      Unit{}

def req.byte.shape(k: Eng.Cls, +c: U32, +cur: List<&2, U32>, -s: List<&2, U32>) ->
  Shape(Spec.req.byte(k, c, cur, Nil{}, s)):
  match k:
    case Eng.KSp{}:
      Unit{}
    case Eng.KHt{}:
      Unit{}
    case Eng.KCr{}:
      req.cr.shape(Spec.req.view(cur), s)
    case Eng.KLf{}:
      Unit{}
    case Eng.KCo{}:
      Unit{}
    case Eng.KCm{}:
      Unit{}
    case Eng.KDg{}:
      Unit{}
    case Eng.KTk{}:
      Unit{}
    case Eng.KVc{}:
      Unit{}
    case Eng.KCt{}:
      Unit{}

def field.byte.shape(k: Eng.Cls, +c: U32, +h: Spec.Head, +cur: List<&2, U32>,
  -s: List<&2, U32>) ->
  Shape(Spec.field.byte(k, c, h, cur, Nil{}, s)):
  match k:
    case Eng.KSp{}:
      Unit{}
    case Eng.KHt{}:
      Unit{}
    case Eng.KCr{}:
      field.cr.shape(h, Spec.field.view(cur), s)
    case Eng.KLf{}:
      Unit{}
    case Eng.KCo{}:
      Unit{}
    case Eng.KCm{}:
      Unit{}
    case Eng.KDg{}:
      Unit{}
    case Eng.KTk{}:
      Unit{}
    case Eng.KVc{}:
      Unit{}
    case Eng.KCt{}:
      Unit{}

def blank.byte.shape(k: Eng.Cls, -s: List<&2, U32>) ->
  Shape(Spec.blank.byte(k, Nil{}, s)):
  match k:
    case Eng.KSp{}:
      Unit{}
    case Eng.KHt{}:
      Unit{}
    case Eng.KCr{}:
      Unit{}
    case Eng.KLf{}:
      Unit{}
    case Eng.KCo{}:
      Unit{}
    case Eng.KCm{}:
      Unit{}
    case Eng.KDg{}:
      Unit{}
    case Eng.KTk{}:
      Unit{}
    case Eng.KVc{}:
      Unit{}
    case Eng.KCt{}:
      Unit{}

def eol.byte.shape(k: Eng.Cls, +h: Spec.Head, -s: List<&2, U32>) ->
  Shape(Spec.eol.byte(k, h, Nil{}, s)):
  match k:
    case Eng.KSp{}:
      Unit{}
    case Eng.KHt{}:
      Unit{}
    case Eng.KCr{}:
      Unit{}
    case Eng.KLf{}:
      Unit{}
    case Eng.KCo{}:
      Unit{}
    case Eng.KCm{}:
      Unit{}
    case Eng.KDg{}:
      Unit{}
    case Eng.KTk{}:
      Unit{}
    case Eng.KVc{}:
      Unit{}
    case Eng.KCt{}:
      Unit{}

def eoh.byte.shape(k: Eng.Cls, +h: Spec.Head, -s: List<&2, U32>) ->
  Shape(Spec.eoh.byte(k, h, Nil{}, s)):
  match k:
    case Eng.KSp{}:
      Unit{}
    case Eng.KHt{}:
      Unit{}
    case Eng.KCr{}:
      Unit{}
    case Eng.KLf{}:
      head.done.shape(h, s)
    case Eng.KCo{}:
      Unit{}
    case Eng.KCm{}:
      Unit{}
    case Eng.KDg{}:
      Unit{}
    case Eng.KTk{}:
      Unit{}
    case Eng.KVc{}:
      Unit{}
    case Eng.KCt{}:
      Unit{}

def body.byte.shape(more: Nat, +c: U32, +h: Spec.Head, +got: List<&2, U32>,
  -s: List<&2, U32>) ->
  Shape(Spec.body.byte(more, c, h, got, Nil{}, s)):
  match more:
    case 0n:
      emit.shape(h, Spec.snoc(got, c))
    case 1n+q:
      Unit{}

def next.at.shape(mode: Spec.Mode, +k: Eng.Cls, +c: U32, -s: List<&2, U32>) ->
  Shape(Spec.next.at(mode, k, c, Nil{}, s)):
  match mode:
    case Spec.MReq{cur}:
      req.byte.shape(k, c, cur, s)
    case Spec.MBlank{}:
      blank.byte.shape(k, s)
    case Spec.MField{h, cur}:
      field.byte.shape(k, c, h, cur, s)
    case Spec.MEol{h}:
      eol.byte.shape(k, h, s)
    case Spec.MEoh{h}:
      eoh.byte.shape(k, h, s)
    case Spec.MBody{h, more, got}:
      body.byte.shape(more, c, h, got, s)
    case Spec.MChunk{h, at, n, got, left}:
      chunk.go.shape(Spec.chunk.step(at, Spec.xk.of(k, c)), h, n, got, left, s)
    case Spec.MData{h, more, got, left}:
      data.byte.shape(more, c, h, got, left, s)
    case Spec.MUp{got}:
      Unit{}
    case Spec.MBad{}:
      Unit{}

# LEMMA: a step from no requests done does at most one
def next.shape(+m: Spec.Mode, +s: List<&2, U32>, +c: U32) -> Shape(Spec.next(Spec.W{m, Nil{}, s}, c)):
  next.at.shape(m, Spec.cls(c), c, Spec.snoc(s, c))


# The walk over two parts, and over what follows an upgrade
# ---------------------------------------------------------

def walk.app(xs: List<&2, U32>, -ys: List<&2, U32>, +w: Spec.W) ->
  {Spec.walk(List.append(&2, U32, xs, ys), w) == Spec.walk(ys, Spec.walk(xs, w)) : Spec.W}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      walk.app(t, ys, Spec.next(w, x))

def treqs.rev.go(ts: List<&2, Laws.PTook>, acc: List<&2, Laws.PTook>) ->
  {Laws.took.reqs(List.reverse.go(&2, Laws.PTook, ts, acc)) ==
    List.reverse.go(&2, Eng.Req, Laws.took.reqs(ts), Laws.took.reqs(acc)) : List<&2, Eng.Req>}:
  match ts:
    case Nil{}:
      {==}
    case Con{h, t}:
      match h:
        case Laws.PTook{raw, q}:
          treqs.rev.go(t, Con{Laws.PTook{raw, q}, acc})

def treqs.rev(ts: List<&2, Laws.PTook>) ->
  {Laws.took.reqs(List.reverse(&2, Laws.PTook, ts)) == List.reverse(&2, Eng.Req, Laws.took.reqs(ts)) :
    List<&2, Eng.Req>}:
  treqs.rev.go(ts, Nil{})

# after an upgrade, what follows is not HTTP: the walk does no more
def up.agrees(bs: List<&2, U32>, +g: List<&2, U32>, +o: List<&2, Eng.Req>, +s: List<&2, U32>,
  -us: List<&2, Laws.PTook>, hu: {Laws.took.reqs(us) == List.reverse(&2, Eng.Req, o) : List<&2, Eng.Req>}) ->
  Laws.Agrees(Laws.PScanned{us, Laws.PUpgraded{}}, Spec.finish(Spec.walk(bs, Spec.W{Spec.MUp{g}, o, s}))):
  match bs:
    case Nil{}:
      (hu, {==})
    case Con{+c, t}:
      up.agrees(t, Spec.snoc(g, c), o, Spec.snoc(s, c), us, hu)

# A refusal stays
# ---------------
#
# Once frame() refuses the bytes so far, it refuses every longer input,
# with the same requests before the refusal. The engine's reader says
# so for the spec: it is refused where frame() is (frame_sim), a refused
# reader stays refused (bad_feeds), and frame_sim again of the longer
# input can then only say refused, with the reader's requests.

def st.is.bad(st: Eng.St, h: {EL.look.st(st) == EL.Refusing{} : EL.Look}) -> {st == Eng.Bad{} : Eng.St}:
  match st:
    case Eng.Pre{}:
      look.no({Eng.Pre{} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.PreLf{}:
      look.no({Eng.PreLf{} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.InM{m0}:
      look.no({Eng.InM{m0} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.InT{p0}:
      look.no({Eng.InT{p0} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.InV{v0}:
      look.no({Eng.InV{v0} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.CrM{}:
      look.no({Eng.CrM{} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.Lin{}:
      look.no({Eng.Lin{} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.InN{n0}:
      look.no({Eng.InN{n0} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.InL0{}:
      look.no({Eng.InL0{} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.InL{v0}:
      look.no({Eng.InL{v0} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.InLt{v0}:
      look.no({Eng.InLt{v0} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.InLc{t0, cl0, up0, ka0}:
      look.no({Eng.InLc{t0, cl0, up0, ka0} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.InLu{t0, ws0}:
      look.no({Eng.InLu{t0, ws0} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.InLk0{}:
      look.no({Eng.InLk0{} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.InLk{k0}:
      look.no({Eng.InLk{k0} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.InLv{v0}:
      look.no({Eng.InLv{v0} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.InLx{}:
      look.no({Eng.InLx{} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.InLe0{}:
      look.no({Eng.InLe0{} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.InLe{v0}:
      look.no({Eng.InLe{v0} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.CrL{}:
      look.no({Eng.CrL{} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.Bod{r0, b0}:
      look.no({Eng.Bod{r0, b0} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.Chk{pos0, n0, b0, left0}:
      look.no({Eng.Chk{pos0, n0, b0, left0} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.Chd{r0, b0, left0}:
      look.no({Eng.Chd{r0, b0, left0} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.Rest{bs0}:
      look.no({Eng.Rest{bs0} == Eng.Bad{} : Eng.St}, EL.Handing{}, EL.Refusing{}, h)
    case Eng.Bad{}:
      {==}

def agree.to(-a: Eng.P, -b: Eng.P, e: {a == b : Eng.P}, -g: Spec.Frames, x: EL.agree(a, g)) -> EL.agree(b, g):
  %e : EL.agree(_, g)
  x

def bad.final.at(-pd: Eng.Pend, +out: List<&2, Eng.Req>, rs2: List<&2, Eng.Req>, e: Spec.End,
  ag: EL.agree.end(Eng.P{Eng.Bad{}, pd, out}, rs2, e)) ->
  {Spec.Frames{rs2, e} == Spec.Frames{List.reverse(&2, Eng.Req, out), Spec.Refused{}} : Spec.Frames}:
  match e:
    case Spec.Open{rest}:
      (l, q) = ag
      look.no({Spec.Frames{rs2, Spec.Open{rest}} == Spec.Frames{List.reverse(&2, Eng.Req, out), Spec.Refused{}} :
        Spec.Frames}, EL.Refusing{}, EL.Reading{},
        Equal.cong(List<&2, Eng.Req> & EL.Look, EL.Look, lk.snd, (List.reverse(&2, Eng.Req, out), EL.Refusing{}),
          (rs2, EL.Reading{}), l))
    case Spec.Refused{}:
      %Equal.cong(List<&2, Eng.Req> & EL.Look, List<&2, Eng.Req>, lk.fst, (List.reverse(&2, Eng.Req, out), EL.Refusing{}),
        (rs2, EL.Refusing{}), ag) :
        {Spec.Frames{_, Spec.Refused{}} == Spec.Frames{List.reverse(&2, Eng.Req, out), Spec.Refused{}} : Spec.Frames}
      {==}
    case Spec.Upgraded{b}:
      no({Spec.Frames{rs2, Spec.Upgraded{b}} == Spec.Frames{List.reverse(&2, Eng.Req, out), Spec.Refused{}} :
        Spec.Frames},
        Equal.cong(Eng.P, Bool, p => st.bad(st.of(p)), Eng.P{Eng.Rest{b}, Eng.pend.new(), List.reverse(&2, Eng.Req, rs2)},
          Eng.P{Eng.Bad{}, pd, out},
          Equal.sym(Eng.P, Eng.P{Eng.Bad{}, pd, out}, Eng.P{Eng.Rest{b}, Eng.pend.new(), List.reverse(&2, Eng.Req, rs2)}, ag)))

def bad.final(-pd: Eng.Pend, +out: List<&2, Eng.Req>, g: Spec.Frames, ag: EL.agree(Eng.P{Eng.Bad{}, pd, out}, g)) ->
  {g == Spec.Frames{List.reverse(&2, Eng.Req, out), Spec.Refused{}} : Spec.Frames}:
  match g:
    case Spec.Frames{rs2, e}:
      bad.final.at(pd, out, rs2, e, ag)

def bad.go(+pre: List<&2, U32>, +bs: List<&2, U32>, st: Eng.St, +pd: Eng.Pend, +out: List<&2, Eng.Req>,
  hq: {Eng.feed(pre, Eng.p.new()) == Eng.P{st, pd, out} : Eng.P}, hs: {st == Eng.Bad{} : Eng.St}) ->
  {Spec.frame(List.append(&2, U32, pre, bs)) == Spec.Frames{List.reverse(&2, Eng.Req, out), Spec.Refused{}} :
    Spec.Frames}:
  bad.final(pd, out, Spec.frame(List.append(&2, U32, pre, bs)),
    agree.to(Eng.feed(List.append(&2, U32, pre, bs), Eng.p.new()), Eng.P{Eng.Bad{}, pd, out},
      Equal.trans(Eng.P, Eng.feed(List.append(&2, U32, pre, bs), Eng.p.new()), Eng.feed(bs, Eng.P{st, pd, out}),
        Eng.P{Eng.Bad{}, pd, out},
        Equal.trans(Eng.P, Eng.feed(List.append(&2, U32, pre, bs), Eng.p.new()), Eng.feed(bs, Eng.feed(pre, Eng.p.new())),
          Eng.feed(bs, Eng.P{st, pd, out}), EL.feed_split(pre, bs, Eng.p.new()),
          Equal.cong(Eng.P, Eng.P, q => Eng.feed(bs, q), Eng.feed(pre, Eng.p.new()), Eng.P{st, pd, out}, hq)),
        %Equal.sym(Eng.St, st, Eng.Bad{}, hs) : {Eng.feed(bs, Eng.P{_, pd, out}) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}
        EL.bad_feeds(bs, pd, out)),
      Spec.frame(List.append(&2, U32, pre, bs)), EL.frame_sim(List.append(&2, U32, pre, bs))))

def bad.at2(+pre: List<&2, U32>, +bs: List<&2, U32>, +st: Eng.St, +pd: Eng.Pend, +out: List<&2, Eng.Req>,
  hq: {Eng.feed(pre, Eng.p.new()) == Eng.P{st, pd, out} : Eng.P}, rs: List<&2, Eng.Req>,
  e2: {List.reverse(&2, Eng.Req, out) == rs : List<&2, Eng.Req>} & {EL.look.st(st) == EL.Refusing{} : EL.Look}) ->
  {Spec.frame(List.append(&2, U32, pre, bs)) == Spec.Frames{rs, Spec.Refused{}} : Spec.Frames}:
  (hr, hl) = e2
  %hr : {Spec.frame(List.append(&2, U32, pre, bs)) == Spec.Frames{_, Spec.Refused{}} : Spec.Frames}
  bad.go(pre, bs, st, pd, out, hq, st.is.bad(st, hl))

def bad.at(+pre: List<&2, U32>, +bs: List<&2, U32>, q: Eng.P, hq: {Eng.feed(pre, Eng.p.new()) == q : Eng.P},
  rs: List<&2, Eng.Req>, lq: {EL.look(q) == (rs, EL.Refusing{}) : List<&2, Eng.Req> & EL.Look}) ->
  {Spec.frame(List.append(&2, U32, pre, bs)) == Spec.Frames{rs, Spec.Refused{}} : Spec.Frames}:
  match q:
    case Eng.P{+st, +pd, +out}:
      bad.at2(pre, bs, st, pd, out, hq, rs,
        pair.eqs(List.reverse(&2, Eng.Req, out), EL.look.st(st), rs, EL.Refusing{}, lq))

# LEMMA: a refusal stays
def bad.stays(+pre: List<&2, U32>, +bs: List<&2, U32>, rs: List<&2, Eng.Req>,
  h: {Spec.frame(pre) == Spec.Frames{rs, Spec.Refused{}} : Spec.Frames}) ->
  {Spec.frame(List.append(&2, U32, pre, bs)) == Spec.Frames{rs, Spec.Refused{}} : Spec.Frames}:
  bad.at(pre, bs, Eng.feed(pre, Eng.p.new()), {==}, rs,
    %h : EL.agree(Eng.feed(pre, Eng.p.new()), _)
    EL.frame_sim(pre))

# The framing a request at a time, against the walk that walks on
# ---------------------------------------------------------------
#
# FRel says where frame()'s walk over the bytes taken so far (pre) is,
# given where the reference framing is: reading with walk w, the walk
# is w with the requests taken behind it; just after a request (or an
# upgrade), it is a fresh walk (or what follows an upgrade) with that
# request in front; refused, frame() of the bytes so far is refused.

def FRel(st: Laws.PStp, acc: List<&2, Laws.PTook>, pre: List<&2, U32>) -> Type:
  match st:
    case Laws.PGo{w, raw}:
      match w:
        case Spec.W{m, x, s}:
          {x == Nil{} : List<&2, Eng.Req>} & {Spec.walk(pre, Laws.w0()) == Spec.W{m, Laws.took.reqs(acc), s} : Spec.W}
    case Laws.PMsg{raw, r}:
      {Spec.walk(pre, Laws.w0()) == Spec.W{Spec.MReq{Nil{}}, Con{r, Laws.took.reqs(acc)}, Nil{}} : Spec.W}
    case Laws.PUp{raw, r}:
      {Spec.walk(pre, Laws.w0()) == Spec.W{Spec.MUp{Nil{}}, Con{r, Laws.took.reqs(acc)}, Nil{}} : Spec.W}
    case Laws.PBad{}:
      {Spec.frame(pre) == Spec.Frames{List.reverse(&2, Eng.Req, Laws.took.reqs(acc)), Spec.Refused{}} : Spec.Frames}

def fa.end(+m2: Spec.Mode, +s2: List<&2, U32>, e: Spec.End, he: {Spec.finish.end(m2, s2) == e : Spec.End},
  -raw2: List<&2, U32>, +acc: List<&2, Laws.PTook>, +pre2: List<&2, U32>,
  hw: {Spec.walk(pre2, Laws.w0()) == Spec.W{m2, Laws.took.reqs(acc), s2} : Spec.W}) ->
  FRel(Laws.px.end(e, Spec.W{m2, Nil{}, s2}, raw2), acc, pre2):
  match e:
    case Spec.Refused{}:
      %Equal.sym(Spec.W, Spec.walk(pre2, Laws.w0()), Spec.W{m2, Laws.took.reqs(acc), s2}, hw) :
        {Spec.finish(_) == Spec.Frames{List.reverse(&2, Eng.Req, Laws.took.reqs(acc)), Spec.Refused{}} : Spec.Frames}
      %Equal.sym(Spec.End, Spec.finish.end(m2, s2), Spec.Refused{}, he) :
        {Spec.Frames{List.reverse(&2, Eng.Req, Laws.took.reqs(acc)), _} ==
          Spec.Frames{List.reverse(&2, Eng.Req, Laws.took.reqs(acc)), Spec.Refused{}} : Spec.Frames}
      {==}
    case Spec.Open{rest}:
      ({==}, hw)
    case Spec.Upgraded{b}:
      ({==}, hw)

def fa.req(b: Bool, -r: Eng.Req, -raw2: List<&2, U32>, -acc: List<&2, Laws.PTook>, -pre2: List<&2, U32>,
  hw: {Spec.walk(pre2, Laws.w0()) == Spec.W{Spec.emit.mode(b), Con{r, Laws.took.reqs(acc)}, Nil{}} : Spec.W}) ->
  FRel(Laws.px.req(b, raw2, r), acc, pre2):
  match b:
    case True{}:
      hw
    case False{}:
      hw

def fa.emit(+m2: Spec.Mode, +r: Eng.Req, +t2: List<&2, Eng.Req>, +s2: List<&2, U32>, +o: List<&2, Eng.Req>,
  sh: {t2 == Nil{} : List<&2, Eng.Req>} & {s2 == Nil{} : List<&2, U32>} & {m2 == Spec.emit.mode(Eng.req.ws(r)) : Spec.Mode}) ->
  {Spec.W{m2, Con{r, List.append(&2, Eng.Req, t2, o)}, s2} == Spec.W{Spec.emit.mode(Eng.req.ws(r)), Con{r, o}, Nil{}} :
    Spec.W}:
  (ht, hr) = sh
  (hs, hm) = hr
  %Equal.sym(List<&2, Eng.Req>, t2, Nil{}, ht) :
    {Spec.W{m2, Con{r, List.append(&2, Eng.Req, _, o)}, s2} == Spec.W{Spec.emit.mode(Eng.req.ws(r)), Con{r, o}, Nil{}} :
      Spec.W}
  %Equal.sym(List<&2, U32>, s2, Nil{}, hs) :
    {Spec.W{m2, Con{r, o}, _} == Spec.W{Spec.emit.mode(Eng.req.ws(r)), Con{r, o}, Nil{}} : Spec.W}
  %Equal.sym(Spec.Mode, m2, Spec.emit.mode(Eng.req.ws(r)), hm) :
    {Spec.W{_, Con{r, o}, Nil{}} == Spec.W{Spec.emit.mode(Eng.req.ws(r)), Con{r, o}, Nil{}} : Spec.W}
  {==}

def fa.of(w2: Spec.W, +raw2: List<&2, U32>, +acc: List<&2, Laws.PTook>, +pre2: List<&2, U32>, sh: Shape(w2),
  hw: {Spec.walk(pre2, Laws.w0()) == shift(w2, Laws.took.reqs(acc)) : Spec.W}) ->
  FRel(Laws.px.of(w2, raw2), acc, pre2):
  match w2:
    case Spec.W{+m2, x2, +s2}:
      match x2:
        case Nil{}:
          fa.end(m2, s2, Spec.finish.end(m2, s2), {==}, raw2, acc, pre2, hw)
        case Con{+r, +t2}:
          fa.req(Eng.req.ws(r), r, raw2, acc, pre2,
            Equal.trans(Spec.W, Spec.walk(pre2, Laws.w0()),
              Spec.W{m2, Con{r, List.append(&2, Eng.Req, t2, Laws.took.reqs(acc))}, s2},
              Spec.W{Spec.emit.mode(Eng.req.ws(r)), Con{r, Laws.took.reqs(acc)}, Nil{}},
              hw, fa.emit(m2, r, t2, s2, Laws.took.reqs(acc), sh)))

# one byte, on both
def fa.stp(+m: Spec.Mode, x: List<&2, Eng.Req>, +s: List<&2, U32>, +raw: List<&2, U32>, +c: U32,
  +acc: List<&2, Laws.PTook>, +pre: List<&2, U32>, rel: FRel(Laws.PGo{Spec.W{m, x, s}, raw}, acc, pre)) ->
  FRel(Laws.px.stp(Spec.W{m, x, s}, c, raw), acc, Spec.snoc(pre, c)):
  (hx, hf) = rel
  %Equal.sym(List<&2, Eng.Req>, x, Nil{}, hx) :
    FRel(Laws.px.stp(Spec.W{m, _, s}, c, raw), acc, Spec.snoc(pre, c))
  fa.of(Spec.next(Spec.W{m, Nil{}, s}, c), Spec.snoc(raw, c), acc, Spec.snoc(pre, c), next.shape(m, s, c),
    Equal.trans(Spec.W, Spec.walk(Spec.snoc(pre, c), Laws.w0()), Spec.next(Spec.W{m, Laws.took.reqs(acc), s}, c),
      shift(Spec.next(Spec.W{m, Nil{}, s}, c), Laws.took.reqs(acc)),
      Equal.trans(Spec.W, Spec.walk(Spec.snoc(pre, c), Laws.w0()), Spec.next(Spec.walk(pre, Laws.w0()), c),
        Spec.next(Spec.W{m, Laws.took.reqs(acc), s}, c), walk.snoc(pre, c, Laws.w0()),
        Equal.cong(Spec.W, Spec.W, w => Spec.next(w, c), Spec.walk(pre, Laws.w0()), Spec.W{m, Laws.took.reqs(acc), s}, hf)),
      next.par(m, Laws.took.reqs(acc), s, c)))

# the rest of a stream: the bytes so far and what follows are the whole
def fa.split(+pre: List<&2, U32>, +c: U32, +t: List<&2, U32>) ->
  {List.append(&2, U32, Spec.snoc(pre, c), t) == List.append(&2, U32, pre, Con{c, t}) : List<&2, U32>}:
  app.assoc(U32, pre, Con{c, Nil{}}, t)

def fa.nil.go(w: Spec.W, +raw: List<&2, U32>, +acc: List<&2, Laws.PTook>, +pre: List<&2, U32>,
  rel: FRel(Laws.PGo{w, raw}, acc, pre)) ->
  Laws.Agrees(Laws.px.go(Nil{}, Laws.PGo{w, raw}, acc), Spec.frame(List.append(&2, U32, pre, Nil{}))):
  match w:
    case Spec.W{+m, +x, +s}:
      (hx, hf) = rel
      %Equal.sym(List<&2, U32>, List.append(&2, U32, pre, Nil{}), pre, app.nil(U32, pre)) :
        Laws.Agrees(Laws.px.go(Nil{}, Laws.PGo{Spec.W{m, x, s}, raw}, acc), Spec.frame(_))
      %Equal.sym(Spec.W, Spec.walk(pre, Laws.w0()), Spec.W{m, Laws.took.reqs(acc), s}, hf) :
        Laws.Agrees(Laws.px.go(Nil{}, Laws.PGo{Spec.W{m, x, s}, raw}, acc), Spec.finish(_))
      (treqs.rev(acc), {==})

def fa.con.go(+c: U32, +t: List<&2, U32>, w: Spec.W, +raw: List<&2, U32>, +acc: List<&2, Laws.PTook>,
  +pre: List<&2, U32>, rel: FRel(Laws.PGo{w, raw}, acc, pre),
  ih: @+s2: Laws.PStp -> @+a2: List<&2, Laws.PTook> -> @+p2: List<&2, U32> -> FRel(s2, a2, p2) ->
    Laws.Agrees(Laws.px.go(t, s2, a2), Spec.frame(List.append(&2, U32, p2, t)))) ->
  Laws.Agrees(Laws.px.go(Con{c, t}, Laws.PGo{w, raw}, acc), Spec.frame(List.append(&2, U32, pre, Con{c, t}))):
  match w:
    case Spec.W{+m, +x, +s}:
      %fa.split(pre, c, t) :
        Laws.Agrees(Laws.px.go(Con{c, t}, Laws.PGo{Spec.W{m, x, s}, raw}, acc), Spec.frame(_))
      ih(Laws.px.stp(Spec.W{m, x, s}, c, raw), acc, Spec.snoc(pre, c), fa.stp(m, x, s, raw, c, acc, pre, rel))

def fa.go(bs: List<&2, U32>, st: Laws.PStp, +acc: List<&2, Laws.PTook>, +pre: List<&2, U32>, rel: FRel(st, acc, pre)) ->
  Laws.Agrees(Laws.px.go(bs, st, acc), Spec.frame(List.append(&2, U32, pre, bs))):
  match bs st:
    case Nil{} Laws.PGo{w, raw}:
      fa.nil.go(w, raw, acc, pre, rel)
    case Nil{} Laws.PMsg{+raw, +r}:
      %Equal.sym(List<&2, U32>, List.append(&2, U32, pre, Nil{}), pre, app.nil(U32, pre)) :
        Laws.Agrees(Laws.px.go(Nil{}, Laws.PMsg{raw, r}, acc), Spec.frame(_))
      %Equal.sym(Spec.W, Spec.walk(pre, Laws.w0()), Spec.W{Spec.MReq{Nil{}}, Con{r, Laws.took.reqs(acc)}, Nil{}}, rel) :
        Laws.Agrees(Laws.px.go(Nil{}, Laws.PMsg{raw, r}, acc), Spec.finish(_))
      (treqs.rev(Con{Laws.PTook{raw, r}, acc}), {==})
    case Nil{} Laws.PUp{+raw, +r}:
      %Equal.sym(List<&2, U32>, List.append(&2, U32, pre, Nil{}), pre, app.nil(U32, pre)) :
        Laws.Agrees(Laws.px.go(Nil{}, Laws.PUp{raw, r}, acc), Spec.frame(_))
      %Equal.sym(Spec.W, Spec.walk(pre, Laws.w0()), Spec.W{Spec.MUp{Nil{}}, Con{r, Laws.took.reqs(acc)}, Nil{}}, rel) :
        Laws.Agrees(Laws.px.go(Nil{}, Laws.PUp{raw, r}, acc), Spec.finish(_))
      (treqs.rev(Con{Laws.PTook{raw, r}, acc}), {==})
    case Nil{} Laws.PBad{}:
      %Equal.sym(List<&2, U32>, List.append(&2, U32, pre, Nil{}), pre, app.nil(U32, pre)) :
        Laws.Agrees(Laws.px.go(Nil{}, Laws.PBad{}, acc), Spec.frame(_))
      %Equal.sym(Spec.Frames, Spec.frame(pre), Spec.Frames{List.reverse(&2, Eng.Req, Laws.took.reqs(acc)), Spec.Refused{}},
        rel) : Laws.Agrees(Laws.px.go(Nil{}, Laws.PBad{}, acc), _)
      (treqs.rev(acc), {==})
    case Con{+c, +t} Laws.PBad{}:
      %Equal.sym(Spec.Frames, Spec.frame(List.append(&2, U32, pre, Con{c, t})),
        Spec.Frames{List.reverse(&2, Eng.Req, Laws.took.reqs(acc)), Spec.Refused{}},
        bad.stays(pre, Con{c, t}, List.reverse(&2, Eng.Req, Laws.took.reqs(acc)), rel)) :
        Laws.Agrees(Laws.px.go(Con{c, t}, Laws.PBad{}, acc), _)
      (treqs.rev(acc), {==})
    case Con{+c, +t} Laws.PUp{+raw, +r}:
      %Equal.sym(Spec.W, Spec.walk(List.append(&2, U32, pre, Con{c, t}), Laws.w0()),
        Spec.walk(Con{c, t}, Spec.walk(pre, Laws.w0())), walk.app(pre, Con{c, t}, Laws.w0())) :
        Laws.Agrees(Laws.px.go(Con{c, t}, Laws.PUp{raw, r}, acc), Spec.finish(_))
      %Equal.sym(Spec.W, Spec.walk(pre, Laws.w0()), Spec.W{Spec.MUp{Nil{}}, Con{r, Laws.took.reqs(acc)}, Nil{}}, rel) :
        Laws.Agrees(Laws.px.go(Con{c, t}, Laws.PUp{raw, r}, acc), Spec.finish(Spec.walk(Con{c, t}, _)))
      up.agrees(Con{c, t}, Nil{}, Con{r, Laws.took.reqs(acc)}, Nil{},
        List.reverse(&2, Laws.PTook, Con{Laws.PTook{raw, r}, acc}), treqs.rev(Con{Laws.PTook{raw, r}, acc}))
    case Con{+c, +t} Laws.PGo{w, raw}:
      fa.con.go(c, t, w, raw, acc, pre, rel, s2 => a2 => p2 => r2 => fa.go(t, s2, a2, p2, r2))
    case Con{+c, +t} Laws.PMsg{+raw, +r}:
      %fa.split(pre, c, t) :
        Laws.Agrees(Laws.px.go(Con{c, t}, Laws.PMsg{raw, r}, acc), Spec.frame(_))
      fa.go(t, Laws.px.stp(Laws.w0(), c, Nil{}), Con{Laws.PTook{raw, r}, acc}, Spec.snoc(pre, c),
        fa.stp(Spec.MReq{Nil{}}, Nil{}, Nil{}, Nil{}, c, Con{Laws.PTook{raw, r}, acc}, pre, ({==}, rel)))

def Laws.frames_agree(bs):
  fa.go(bs, Laws.PGo{Laws.w0(), Nil{}}, Nil{}, Nil{}, ({==}, {==}))
