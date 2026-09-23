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
import ../../wire/http1/resp.bend as R
import ../../wire/http1/spec.bend as RS
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

# Forwarding
# ==========

def bytes.rt(b: Bytes()) -> {Bytes.from_list(Bytes.to_list(b)) == b : Bytes()}:
  match b:
    case SNil{}:
      {==}
    case SCon{Chr{c}, t}:
      Equal.cong(Bytes(), Bytes(), x => SCon{Chr{c}, x}, Bytes.from_list(Bytes.to_list(t)), t, bytes.rt(t))

def wire.ref(+w: X.Fwd, ts: List<&2, X.Took>) -> {X.wire(w, ts) == Laws.ref.wire(w, Laws.tooks.of(ts)) : Bytes()}:
  match ts:
    case Nil{}:
      {==}
    case Con{t, r}:
      match t:
        case X.Took{+raw, q}:
          %Equal.sym(Bytes(), Bytes.from_list(Bytes.to_list(raw)), raw, bytes.rt(raw)) :
            {X.wire(w, Con{X.Took{raw, q}, r}) ==
              X.wire.at(X.fwd.at(w, X.head.of(_), q), Laws.ref.wire(w, Laws.tooks.of(r))) : Bytes()}
          %wire.ref(w, r) :
            {X.wire(w, Con{X.Took{raw, q}, r}) == X.wire.at(X.fwd.at(w, X.head.of(raw), q), _) : Bytes()}
          {==}

def conns.took(c: Laws.Conn, f: Laws.PScanned, h: Laws.Conns(c, f)) ->
  {Laws.tooks.of(Laws.conn.took(c)) == Laws.scanned.took(f) : List<&2, Laws.PTook>}:
  match c f:
    case Laws.Conn{ts, t} Laws.PScanned{us, u}:
      (h1, h2) = h
      h1

def Laws.forward_canonical(w, rs):
  Equal.trans(Bytes(), X.wire(w, Laws.conn.took(Laws.reads(rs))),
    Laws.ref.wire(w, Laws.tooks.of(Laws.conn.took(Laws.reads(rs)))),
    Laws.ref.wire(w, Laws.scanned.took(Laws.frame(Bytes.to_list(Bytes.concat(rs))))),
    wire.ref(w, Laws.conn.took(Laws.reads(rs))),
    Equal.cong(List<&2, Laws.PTook>, Bytes(), us => Laws.ref.wire(w, us), Laws.tooks.of(Laws.conn.took(Laws.reads(rs))),
      Laws.scanned.took(Laws.frame(Bytes.to_list(Bytes.concat(rs)))),
      conns.took(Laws.reads(rs), Laws.frame(Bytes.to_list(Bytes.concat(rs))), Laws.scan_is_spec(rs))))

# A refusal forwards nothing
# --------------------------

def is.nil.q(xs: List<&2, Eng.Req>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      False{}

def treqs.nil(us: List<&2, Laws.PTook>, h: {Laws.took.reqs(us) == Nil{} : List<&2, Eng.Req>}) ->
  {us == Nil{} : List<&2, Laws.PTook>}:
  match us:
    case Nil{}:
      {==}
    case Con{t, r}:
      match t:
        case Laws.PTook{raw, q}:
          no({Con{Laws.PTook{raw, q}, r} == Nil{} : List<&2, Laws.PTook>},
            Equal.cong(List<&2, Eng.Req>, Bool, is.nil.q, Con{q, Laws.took.reqs(r)}, Nil{}, h))

def is.nil.p(xs: List<&2, Laws.PTook>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      False{}

def tooks.nil(ts: List<&2, X.Took>, h: {Laws.tooks.of(ts) == Nil{} : List<&2, Laws.PTook>}) ->
  {ts == Nil{} : List<&2, X.Took>}:
  match ts:
    case Nil{}:
      {==}
    case Con{t, r}:
      no({Con{t, r} == Nil{} : List<&2, X.Took>},
        Equal.cong(List<&2, Laws.PTook>, Bool, is.nil.p, Con{Laws.took.of(t), Laws.tooks.of(r)}, Nil{}, h))

def agrees.nil(f: Laws.PScanned, ag: Laws.Agrees(f, Spec.Frames{Nil{}, Spec.Refused{}})) ->
  {Laws.scanned.took(f) == Nil{} : List<&2, Laws.PTook>}:
  match f:
    case Laws.PScanned{us, u}:
      (h1, h2) = ag
      treqs.nil(us, h1)

def Laws.refused_not_forwarded(rs, r):
  tooks.nil(Laws.conn.took(Laws.reads(rs)),
    Equal.trans(List<&2, Laws.PTook>, Laws.tooks.of(Laws.conn.took(Laws.reads(rs))),
      Laws.scanned.took(Laws.frame(Bytes.to_list(Bytes.concat(rs)))), Nil{},
      conns.took(Laws.reads(rs), Laws.frame(Bytes.to_list(Bytes.concat(rs))), Laws.scan_is_spec(rs)),
      agrees.nil(Laws.frame(Bytes.to_list(Bytes.concat(rs))),
        %r : Laws.Agrees(Laws.frame(Bytes.to_list(Bytes.concat(rs))), _)
        Laws.frames_agree(Bytes.to_list(Bytes.concat(rs))))))

# The hop's fields
# ----------------

def clean.app.at(x: Bool, -c1: Bool, -c2: Bool, -c12: Bool, e: {c12 == (c1 && c2) : Bool}) ->
  {(x && c12) == (x && c1 && c2) : Bool}:
  match x:
    case True{}:
      e
    case False{}:
      {==}

def clean.app(~m: @+n: Bytes() -> Bool, +ns: List<&2, Bytes()>, a: List<&2, X.Field>, -b: List<&2, X.Field>) ->
  {Laws.clean(~m, ns, List.append(&2, X.Field, a, b)) == (Laws.clean(~m, ns, a) && Laws.clean(~m, ns, b)) : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{f, t}:
      match f:
        case X.Field{+n, v}:
          clean.app.at(m(n) || Bool.not(Laws.hop(ns, n)), Laws.clean(~m, ns, t), Laws.clean(~m, ns, b),
            Laws.clean(~m, ns, List.append(&2, X.Field, t, b)), clean.app(~m, ns, t, b))

# a field kept is not a hop's
def and3.mid(a: Bool, b: Bool, -c: Bool, h: {(a && Bool.not(b) && c) == True{} : Bool}) -> {b == False{} : Bool}:
  match a b:
    case True{} True{}:
      no({True{} == False{} : Bool}, h)
    case True{} False{}:
      {==}
    case False{} True{}:
      no({True{} == False{} : Bool}, h)
    case False{} False{}:
      {==}

def and2.fst(a: Bool, -c: Bool, h: {(Bool.not(a) && c) == True{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      no({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def or.true(a: Bool) -> {(a || True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# the laws' own list of the hop's fields is core.bend's
def named.eq(+n: Bytes(), ns: List<&2, Bytes()>) -> {Laws.named(n, ns) == X.in.names(n, ns) : Bool}:
  match ns:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Equal.cong(Bool, Bool, b => Eng.bytes.eq(n, x) || b, Laws.named(n, t), X.in.names(n, t), named.eq(n, t))

def hop.eq(+ns: List<&2, Bytes()>, +n: Bytes()) -> {Laws.hop(ns, n) == X.hop(ns, n) : Bool}:
  Equal.cong(Bool, Bool, b => Laws.hop.fixed(n) || b, Laws.named(n, ns), X.in.names(n, ns), named.eq(n, ns))

# a field kept, then the rest clean
def kept.clean(~m: @+n: Bytes() -> Bool, +ns: List<&2, Bytes()>, +n: Bytes(), hb: {X.hop(ns, n) == False{} : Bool},
  -rest: List<&2, X.Field>, ih: {Laws.clean(~m, ns, rest) == True{} : Bool}) ->
  {((m(n) || Bool.not(Laws.hop(ns, n))) && Laws.clean(~m, ns, rest)) == True{} : Bool}:
  %Equal.sym(Bool, Laws.hop(ns, n), X.hop(ns, n), hop.eq(ns, n)) :
    {((m(n) || Bool.not(_)) && Laws.clean(~m, ns, rest)) == True{} : Bool}
  %Equal.sym(Bool, X.hop(ns, n), False{}, hb) :
    {((m(n) || Bool.not(_)) && Laws.clean(~m, ns, rest)) == True{} : Bool}
  %Equal.sym(Bool, (m(n) || True{}), True{}, or.true(m(n))) :
    {(_ && Laws.clean(~m, ns, rest)) == True{} : Bool}
  ih

def ends.at(~m: @+n: Bytes() -> Bool, +ns: List<&2, Bytes()>, k: Bool, +n: Bytes(), v: Bytes(), -t: List<&2, X.Field>,
  hk: {X.keeps(ns, n) == k : Bool}, ih: {Laws.clean(~m, ns, X.ends(ns, t)) == True{} : Bool}) ->
  {Laws.clean(~m, ns, X.ends.put(k, X.Field{n, v}, X.ends(ns, t))) == True{} : Bool}:
  match k:
    case True{}:
      kept.clean(~m, ns, n,
        and3.mid(X.is.other(Eng.fld.of(n)), X.hop(ns, n), Bool.not(X.own(n)), hk), X.ends(ns, t), ih)
    case False{}:
      ih

# LEMMA: what ends keeps is clean
def ends.clean(~m: @+n: Bytes() -> Bool, +ns: List<&2, Bytes()>, fs: List<&2, X.Field>) ->
  {Laws.clean(~m, ns, X.ends(ns, fs)) == True{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case Con{f, t}:
      match f:
        case X.Field{+n, v}:
          ends.at(~m, ns, X.keeps(ns, n), n, v, t, {==}, ends.clean(~m, ns, t))

def rends.at(~m: @+n: Bytes() -> Bool, +ns: List<&2, Bytes()>, +len: Bool, k: Bool, +n: Bytes(), v: Bytes(),
  -t: List<&2, X.Field>, hk: {X.rkeeps(ns, len, n) == k : Bool},
  ih: {Laws.clean(~m, ns, X.rends(ns, len, t)) == True{} : Bool}) ->
  {Laws.clean(~m, ns, X.ends.put(k, X.Field{n, v}, X.rends(ns, len, t))) == True{} : Bool}:
  match k:
    case True{}:
      kept.clean(~m, ns, n,
        and2.fst(X.hop(ns, n), len || Bool.not(Eng.bytes.eq(n, "content-length")), hk), X.rends(ns, len, t), ih)
    case False{}:
      ih

def rends.clean(~m: @+n: Bytes() -> Bool, +ns: List<&2, Bytes()>, +len: Bool, fs: List<&2, X.Field>) ->
  {Laws.clean(~m, ns, X.rends(ns, len, fs)) == True{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case Con{f, t}:
      match f:
        case X.Field{+n, v}:
          rends.at(~m, ns, len, X.rkeeps(ns, len, n), n, v, t, {==}, rends.clean(~m, ns, len, t))

def and.true(a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {(a && b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {(_ && b) == True{} : Bool}
  hb

def Laws.hop_by_hop_removed(w, h, body):
  match w h:
    case X.Fwd{host, proto, +ip, via} X.Head{meth, target, v10, +fs}:
      +t4 : List<&2, X.Field> = [X.Field{"x-forwarded-for", X.join(List.append(&2, Bytes(), X.values("x-forwarded-for", fs), [ip]))},
        X.Field{"x-forwarded-proto", proto}, X.Field{"x-forwarded-host", X.first(X.values("host", fs), "")},
        X.Field{"via", via}]
      %Equal.sym(Bool, Laws.clean(~Laws.own5, X.conn.names(fs), List.append(&2, X.Field, X.ends(X.conn.names(fs), fs), t4)),
        (Laws.clean(~Laws.own5, X.conn.names(fs), X.ends(X.conn.names(fs), fs)) && Laws.clean(~Laws.own5, X.conn.names(fs), t4)),
        clean.app(~Laws.own5, X.conn.names(fs), X.ends(X.conn.names(fs), fs), t4)) :
        {_ == True{} : Bool}
      and.true(Laws.clean(~Laws.own5, X.conn.names(fs), X.ends(X.conn.names(fs), fs)),
        Laws.clean(~Laws.own5, X.conn.names(fs), t4), ends.clean(~Laws.own5, X.conn.names(fs), fs), {==})

def Laws.hop_by_hop_removed_rsp(via, ns, len, fs):
  %Equal.sym(Bool, Laws.clean(~Laws.is.via, ns, List.append(&2, X.Field, X.rends(ns, len, fs), [X.Field{"via", via}])),
    (Laws.clean(~Laws.is.via, ns, X.rends(ns, len, fs)) && Laws.clean(~Laws.is.via, ns, [X.Field{"via", via}])),
    clean.app(~Laws.is.via, ns, X.rends(ns, len, fs), [X.Field{"via", via}])) : {_ == True{} : Bool}
  and.true(Laws.clean(~Laws.is.via, ns, X.rends(ns, len, fs)), Laws.clean(~Laws.is.via, ns, [X.Field{"via", via}]),
    rends.clean(~Laws.is.via, ns, len, fs), {==})

# Reading it back
# ===============
#
# no_smuggle: the upstream, reading what the proxy sent by spec.bend's
# frame(), reads one request for each one forwarded -- its method,
# target and body -- and nothing more. A forwarded request passed valid
# (core.bend), and what valid checks is what spec.bend's walk needs to
# read each line of it as the line it is: bytes a line may hold
# (gathered, no CR or LF among them), a request line split at its two
# spaces, a field line at its colon with a name no framing reads, and a
# Content-Length read back as the body's length.

# no CR and no LF: a line's bytes
def ncl(k: Eng.Cls) -> Bool:
  match k:
    case Eng.KCr{}:
      False{}
    case Eng.KLf{}:
      False{}
    case _:
      True{}

def PL(xs: List<&2, U32>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{x, t}:
      {ncl(Spec.cls(x)) == True{} : Bool} & PL(t)

# every byte one a token may hold
def AA(t: Spec.Tok, xs: List<&2, U32>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{x, r}:
      {Spec.allows(t, Spec.cls(x)) == True{} : Bool} & AA(t, r)

# no token holds a CR or an LF
def allows.ncl(t: Spec.Tok, k: Eng.Cls, h: {Spec.allows(t, k) == True{} : Bool}) -> {ncl(k) == True{} : Bool}:
  match t k:
    case Spec.TMeth{} Eng.KSp{}:
      no({ncl(Eng.KSp{}) == True{} : Bool}, h)
    case Spec.TMeth{} Eng.KHt{}:
      no({ncl(Eng.KHt{}) == True{} : Bool}, h)
    case Spec.TMeth{} Eng.KCr{}:
      no({ncl(Eng.KCr{}) == True{} : Bool}, h)
    case Spec.TMeth{} Eng.KLf{}:
      no({ncl(Eng.KLf{}) == True{} : Bool}, h)
    case Spec.TMeth{} Eng.KCo{}:
      no({ncl(Eng.KCo{}) == True{} : Bool}, h)
    case Spec.TMeth{} Eng.KCm{}:
      no({ncl(Eng.KCm{}) == True{} : Bool}, h)
    case Spec.TMeth{} Eng.KDg{}:
      {==}
    case Spec.TMeth{} Eng.KTk{}:
      {==}
    case Spec.TMeth{} Eng.KVc{}:
      no({ncl(Eng.KVc{}) == True{} : Bool}, h)
    case Spec.TMeth{} Eng.KCt{}:
      no({ncl(Eng.KCt{}) == True{} : Bool}, h)
    case Spec.TTarget{} Eng.KSp{}:
      no({ncl(Eng.KSp{}) == True{} : Bool}, h)
    case Spec.TTarget{} Eng.KHt{}:
      no({ncl(Eng.KHt{}) == True{} : Bool}, h)
    case Spec.TTarget{} Eng.KCr{}:
      no({ncl(Eng.KCr{}) == True{} : Bool}, h)
    case Spec.TTarget{} Eng.KLf{}:
      no({ncl(Eng.KLf{}) == True{} : Bool}, h)
    case Spec.TTarget{} Eng.KCo{}:
      {==}
    case Spec.TTarget{} Eng.KCm{}:
      {==}
    case Spec.TTarget{} Eng.KDg{}:
      {==}
    case Spec.TTarget{} Eng.KTk{}:
      {==}
    case Spec.TTarget{} Eng.KVc{}:
      {==}
    case Spec.TTarget{} Eng.KCt{}:
      no({ncl(Eng.KCt{}) == True{} : Bool}, h)
    case Spec.TVer{} Eng.KSp{}:
      no({ncl(Eng.KSp{}) == True{} : Bool}, h)
    case Spec.TVer{} Eng.KHt{}:
      no({ncl(Eng.KHt{}) == True{} : Bool}, h)
    case Spec.TVer{} Eng.KCr{}:
      no({ncl(Eng.KCr{}) == True{} : Bool}, h)
    case Spec.TVer{} Eng.KLf{}:
      no({ncl(Eng.KLf{}) == True{} : Bool}, h)
    case Spec.TVer{} Eng.KCo{}:
      no({ncl(Eng.KCo{}) == True{} : Bool}, h)
    case Spec.TVer{} Eng.KCm{}:
      no({ncl(Eng.KCm{}) == True{} : Bool}, h)
    case Spec.TVer{} Eng.KDg{}:
      {==}
    case Spec.TVer{} Eng.KTk{}:
      {==}
    case Spec.TVer{} Eng.KVc{}:
      {==}
    case Spec.TVer{} Eng.KCt{}:
      no({ncl(Eng.KCt{}) == True{} : Bool}, h)
    case Spec.TName{} Eng.KSp{}:
      no({ncl(Eng.KSp{}) == True{} : Bool}, h)
    case Spec.TName{} Eng.KHt{}:
      no({ncl(Eng.KHt{}) == True{} : Bool}, h)
    case Spec.TName{} Eng.KCr{}:
      no({ncl(Eng.KCr{}) == True{} : Bool}, h)
    case Spec.TName{} Eng.KLf{}:
      no({ncl(Eng.KLf{}) == True{} : Bool}, h)
    case Spec.TName{} Eng.KCo{}:
      no({ncl(Eng.KCo{}) == True{} : Bool}, h)
    case Spec.TName{} Eng.KCm{}:
      no({ncl(Eng.KCm{}) == True{} : Bool}, h)
    case Spec.TName{} Eng.KDg{}:
      {==}
    case Spec.TName{} Eng.KTk{}:
      {==}
    case Spec.TName{} Eng.KVc{}:
      no({ncl(Eng.KVc{}) == True{} : Bool}, h)
    case Spec.TName{} Eng.KCt{}:
      no({ncl(Eng.KCt{}) == True{} : Bool}, h)
    case Spec.TOws{} Eng.KSp{}:
      {==}
    case Spec.TOws{} Eng.KHt{}:
      {==}
    case Spec.TOws{} Eng.KCr{}:
      no({ncl(Eng.KCr{}) == True{} : Bool}, h)
    case Spec.TOws{} Eng.KLf{}:
      no({ncl(Eng.KLf{}) == True{} : Bool}, h)
    case Spec.TOws{} Eng.KCo{}:
      no({ncl(Eng.KCo{}) == True{} : Bool}, h)
    case Spec.TOws{} Eng.KCm{}:
      no({ncl(Eng.KCm{}) == True{} : Bool}, h)
    case Spec.TOws{} Eng.KDg{}:
      no({ncl(Eng.KDg{}) == True{} : Bool}, h)
    case Spec.TOws{} Eng.KTk{}:
      no({ncl(Eng.KTk{}) == True{} : Bool}, h)
    case Spec.TOws{} Eng.KVc{}:
      no({ncl(Eng.KVc{}) == True{} : Bool}, h)
    case Spec.TOws{} Eng.KCt{}:
      no({ncl(Eng.KCt{}) == True{} : Bool}, h)
    case Spec.TVal{} Eng.KSp{}:
      {==}
    case Spec.TVal{} Eng.KHt{}:
      {==}
    case Spec.TVal{} Eng.KCr{}:
      no({ncl(Eng.KCr{}) == True{} : Bool}, h)
    case Spec.TVal{} Eng.KLf{}:
      no({ncl(Eng.KLf{}) == True{} : Bool}, h)
    case Spec.TVal{} Eng.KCo{}:
      {==}
    case Spec.TVal{} Eng.KCm{}:
      {==}
    case Spec.TVal{} Eng.KDg{}:
      {==}
    case Spec.TVal{} Eng.KTk{}:
      {==}
    case Spec.TVal{} Eng.KVc{}:
      {==}
    case Spec.TVal{} Eng.KCt{}:
      no({ncl(Eng.KCt{}) == True{} : Bool}, h)

def aa.pl(+t: Spec.Tok, xs: List<&2, U32>, h: AA(t, xs)) -> PL(xs):
  match xs:
    case Nil{}:
      Unit{}
    case Con{+x, r}:
      (h1, h2) = h
      (allows.ncl(t, Spec.cls(x), h1), aa.pl(t, r, h2))

def pl.app(a: List<&2, U32>, -b: List<&2, U32>, pa: PL(a), pb: PL(b)) -> PL(List.append(&2, U32, a, b)):
  match a:
    case Nil{}:
      pb
    case Con{x, t}:
      (h1, h2) = pa
      (h1, pl.app(t, b, h2, pb))

def and.split(a: Bool, -b: Bool, h: {(a && b) == True{} : Bool}) -> {a == True{} : Bool} & {b == True{} : Bool}:
  match a:
    case True{}:
      ({==}, h)
    case False{}:
      no({False{} == True{} : Bool} & {b == True{} : Bool}, h)

# the proxy's check, byte by byte, as spec.bend's classes
def aa.of.at(+t: Spec.Tok, +c: U32, -r: Bytes(),
  h: {Spec.allows(t, Eng.cls(c)) == True{} : Bool} & {X.ok.all(t, r) == True{} : Bool},
  ih: {X.ok.all(t, r) == True{} : Bool} -> AA(t, Bytes.to_list(r))) ->
  AA(t, Con{c, Bytes.to_list(r)}):
  (h1, h2) = h
  (%EL.cls_every(c) : {Spec.allows(t, _) == True{} : Bool}
   h1, ih(h2))

def aa.of(+t: Spec.Tok, s: Bytes(), h: {X.ok.all(t, s) == True{} : Bool}) -> AA(t, Bytes.to_list(s)):
  match s:
    case SNil{}:
      Unit{}
    case SCon{Chr{+c}, r}:
      aa.of.at(t, c, r, and.split(Spec.allows(t, Eng.cls(c)), X.ok.all(t, r), h), h2 => aa.of(t, r, h2))

# a span over bytes its token holds, stopped by one it does not
def span.to(+t: Spec.Tok, xs: List<&2, U32>, +c: U32, +rest: List<&2, U32>, h: AA(t, xs),
  hc: {Spec.allows(t, Spec.cls(c)) == False{} : Bool}) ->
  {Spec.span(t, List.append(&2, U32, xs, Con{c, rest})) == Spec.Span{xs, Spec.SAt{Spec.cls(c), c, rest}} : Spec.Span}:
  match xs:
    case Nil{}:
      %Equal.sym(Bool, Spec.allows(t, Spec.cls(c)), False{}, hc) :
        {Spec.span.pick(_, Spec.cls(c), c, rest, Spec.span(t, rest)) == Spec.Span{Nil{}, Spec.SAt{Spec.cls(c), c, rest}} :
          Spec.Span}
      {==}
    case Con{+x, +r}:
      (h1, h2) = h
      %Equal.sym(Bool, Spec.allows(t, Spec.cls(x)), True{}, h1) :
        {Spec.span.pick(_, Spec.cls(x), x, List.append(&2, U32, r, Con{c, rest}),
          Spec.span(t, List.append(&2, U32, r, Con{c, rest}))) ==
          Spec.Span{Con{x, r}, Spec.SAt{Spec.cls(c), c, rest}} : Spec.Span}
      %Equal.sym(Spec.Span, Spec.span(t, List.append(&2, U32, r, Con{c, rest})), Spec.Span{r, Spec.SAt{Spec.cls(c), c, rest}},
        span.to(t, r, c, rest, h2, hc)) : {Spec.span.push(x, _) == Spec.Span{Con{x, r}, Spec.SAt{Spec.cls(c), c, rest}} :
        Spec.Span}
      {==}

# and a span over bytes its token all holds, to the end
def span.all(+t: Spec.Tok, xs: List<&2, U32>, h: AA(t, xs)) -> {Spec.span(t, xs) == Spec.Span{xs, Spec.SEnd{}} : Spec.Span}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      (h1, h2) = h
      %Equal.sym(Bool, Spec.allows(t, Spec.cls(x)), True{}, h1) :
        {Spec.span.pick(_, Spec.cls(x), x, r, Spec.span(t, r)) == Spec.Span{Con{x, r}, Spec.SEnd{}} : Spec.Span}
      %Equal.sym(Spec.Span, Spec.span(t, r), Spec.Span{r, Spec.SEnd{}}, span.all(t, r, h2)) : {Spec.span.push(x, _) == Spec.Span{Con{x, r}, Spec.SEnd{}} : Spec.Span}
      {==}

# a line's byte is gathered
def req.plain(k: Eng.Cls, -x: U32, -cur: List<&2, U32>, -o: List<&2, Eng.Req>, -s: List<&2, U32>,
  h: {ncl(k) == True{} : Bool}) ->
  {Spec.req.byte(k, x, cur, o, s) == Spec.W{Spec.MReq{Spec.snoc(cur, x)}, o, s} : Spec.W}:
  match k:
    case Eng.KSp{}:
      {==}
    case Eng.KHt{}:
      {==}
    case Eng.KCr{}:
      no({Spec.req.byte(Eng.KCr{}, x, cur, o, s) == Spec.W{Spec.MReq{Spec.snoc(cur, x)}, o, s} : Spec.W}, h)
    case Eng.KLf{}:
      no({Spec.req.byte(Eng.KLf{}, x, cur, o, s) == Spec.W{Spec.MReq{Spec.snoc(cur, x)}, o, s} : Spec.W}, h)
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

def field.plain(k: Eng.Cls, -x: U32, -hd: Spec.Head, -cur: List<&2, U32>, -o: List<&2, Eng.Req>, -s: List<&2, U32>,
  h: {ncl(k) == True{} : Bool}) ->
  {Spec.field.byte(k, x, hd, cur, o, s) == Spec.W{Spec.MField{hd, Spec.snoc(cur, x)}, o, s} : Spec.W}:
  match k:
    case Eng.KSp{}:
      {==}
    case Eng.KHt{}:
      {==}
    case Eng.KCr{}:
      no({Spec.field.byte(Eng.KCr{}, x, hd, cur, o, s) == Spec.W{Spec.MField{hd, Spec.snoc(cur, x)}, o, s} : Spec.W}, h)
    case Eng.KLf{}:
      no({Spec.field.byte(Eng.KLf{}, x, hd, cur, o, s) == Spec.W{Spec.MField{hd, Spec.snoc(cur, x)}, o, s} : Spec.W}, h)
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

def snoc.app(+a: List<&2, U32>, +x: U32, +t: List<&2, U32>) ->
  {List.append(&2, U32, Spec.snoc(a, x), t) == List.append(&2, U32, a, Con{x, t}) : List<&2, U32>}:
  app.assoc(U32, a, Con{x, Nil{}}, t)

# LEMMA: a request line's bytes are gathered
def gather.req(xs: List<&2, U32>, +rest: List<&2, U32>, +cur: List<&2, U32>, +o: List<&2, Eng.Req>,
  +s: List<&2, U32>, pl: PL(xs)) ->
  {Spec.walk(List.append(&2, U32, xs, rest), Spec.W{Spec.MReq{cur}, o, s}) ==
    Spec.walk(rest, Spec.W{Spec.MReq{List.append(&2, U32, cur, xs)}, o, List.append(&2, U32, s, xs)}) : Spec.W}:
  match xs:
    case Nil{}:
      %Equal.sym(List<&2, U32>, List.append(&2, U32, cur, Nil{}), cur, app.nil(U32, cur)) : {Spec.walk(rest, Spec.W{Spec.MReq{cur}, o, s}) ==
        Spec.walk(rest, Spec.W{Spec.MReq{_}, o, List.append(&2, U32, s, Nil{})}) : Spec.W}
      %Equal.sym(List<&2, U32>, List.append(&2, U32, s, Nil{}), s, app.nil(U32, s)) : {Spec.walk(rest, Spec.W{Spec.MReq{cur}, o, s}) ==
        Spec.walk(rest, Spec.W{Spec.MReq{cur}, o, _}) : Spec.W}
      {==}
    case Con{+x, +t}:
      (h1, h2) = pl
      %Equal.sym(Spec.W, Spec.req.byte(Spec.cls(x), x, cur, o, Spec.snoc(s, x)),
        Spec.W{Spec.MReq{Spec.snoc(cur, x)}, o, Spec.snoc(s, x)}, req.plain(Spec.cls(x), x, cur, o, Spec.snoc(s, x), h1)) :
        {Spec.walk(List.append(&2, U32, t, rest), _) ==
          Spec.walk(rest, Spec.W{Spec.MReq{List.append(&2, U32, cur, Con{x, t})}, o, List.append(&2, U32, s, Con{x, t})}) :
          Spec.W}
      %Equal.sym(Spec.W, Spec.walk(List.append(&2, U32, t, rest), Spec.W{Spec.MReq{Spec.snoc(cur, x)}, o, Spec.snoc(s, x)}),
        Spec.walk(rest, Spec.W{Spec.MReq{List.append(&2, U32, Spec.snoc(cur, x), t)}, o, List.append(&2, U32, Spec.snoc(s, x), t)}),
        gather.req(t, rest, Spec.snoc(cur, x), o, Spec.snoc(s, x), h2)) : {_ ==
          Spec.walk(rest, Spec.W{Spec.MReq{List.append(&2, U32, cur, Con{x, t})}, o, List.append(&2, U32, s, Con{x, t})}) :
          Spec.W}
      %Equal.sym(List<&2, U32>, List.append(&2, U32, Spec.snoc(cur, x), t), List.append(&2, U32, cur, Con{x, t}),
        snoc.app(cur, x, t)) : {Spec.walk(rest, Spec.W{Spec.MReq{_}, o, List.append(&2, U32, Spec.snoc(s, x), t)}) ==
          Spec.walk(rest, Spec.W{Spec.MReq{List.append(&2, U32, cur, Con{x, t})}, o, List.append(&2, U32, s, Con{x, t})}) :
          Spec.W}
      %Equal.sym(List<&2, U32>, List.append(&2, U32, Spec.snoc(s, x), t), List.append(&2, U32, s, Con{x, t}),
        snoc.app(s, x, t)) : {Spec.walk(rest, Spec.W{Spec.MReq{List.append(&2, U32, cur, Con{x, t})}, o, _}) ==
          Spec.walk(rest, Spec.W{Spec.MReq{List.append(&2, U32, cur, Con{x, t})}, o, List.append(&2, U32, s, Con{x, t})}) :
          Spec.W}
      {==}

# LEMMA: and a field line's
def gather.field(xs: List<&2, U32>, +rest: List<&2, U32>, +hd: Spec.Head, +cur: List<&2, U32>, +o: List<&2, Eng.Req>,
  +s: List<&2, U32>, pl: PL(xs)) ->
  {Spec.walk(List.append(&2, U32, xs, rest), Spec.W{Spec.MField{hd, cur}, o, s}) ==
    Spec.walk(rest, Spec.W{Spec.MField{hd, List.append(&2, U32, cur, xs)}, o, List.append(&2, U32, s, xs)}) : Spec.W}:
  match xs:
    case Nil{}:
      %Equal.sym(List<&2, U32>, List.append(&2, U32, cur, Nil{}), cur, app.nil(U32, cur)) : {Spec.walk(rest, Spec.W{Spec.MField{hd, cur}, o, s}) ==
        Spec.walk(rest, Spec.W{Spec.MField{hd, _}, o, List.append(&2, U32, s, Nil{})}) : Spec.W}
      %Equal.sym(List<&2, U32>, List.append(&2, U32, s, Nil{}), s, app.nil(U32, s)) : {Spec.walk(rest, Spec.W{Spec.MField{hd, cur}, o, s}) ==
        Spec.walk(rest, Spec.W{Spec.MField{hd, cur}, o, _}) : Spec.W}
      {==}
    case Con{+x, +t}:
      (h1, h2) = pl
      %Equal.sym(Spec.W, Spec.field.byte(Spec.cls(x), x, hd, cur, o, Spec.snoc(s, x)),
        Spec.W{Spec.MField{hd, Spec.snoc(cur, x)}, o, Spec.snoc(s, x)}, field.plain(Spec.cls(x), x, hd, cur, o, Spec.snoc(s, x), h1)) :
        {Spec.walk(List.append(&2, U32, t, rest), _) ==
          Spec.walk(rest, Spec.W{Spec.MField{hd, List.append(&2, U32, cur, Con{x, t})}, o, List.append(&2, U32, s, Con{x, t})}) :
          Spec.W}
      %Equal.sym(Spec.W, Spec.walk(List.append(&2, U32, t, rest), Spec.W{Spec.MField{hd, Spec.snoc(cur, x)}, o, Spec.snoc(s, x)}),
        Spec.walk(rest, Spec.W{Spec.MField{hd, List.append(&2, U32, Spec.snoc(cur, x), t)}, o, List.append(&2, U32, Spec.snoc(s, x), t)}),
        gather.field(t, rest, hd, Spec.snoc(cur, x), o, Spec.snoc(s, x), h2)) : {_ ==
          Spec.walk(rest, Spec.W{Spec.MField{hd, List.append(&2, U32, cur, Con{x, t})}, o, List.append(&2, U32, s, Con{x, t})}) :
          Spec.W}
      %Equal.sym(List<&2, U32>, List.append(&2, U32, Spec.snoc(cur, x), t), List.append(&2, U32, cur, Con{x, t}),
        snoc.app(cur, x, t)) : {Spec.walk(rest, Spec.W{Spec.MField{hd, _}, o, List.append(&2, U32, Spec.snoc(s, x), t)}) ==
          Spec.walk(rest, Spec.W{Spec.MField{hd, List.append(&2, U32, cur, Con{x, t})}, o, List.append(&2, U32, s, Con{x, t})}) :
          Spec.W}
      %Equal.sym(List<&2, U32>, List.append(&2, U32, Spec.snoc(s, x), t), List.append(&2, U32, s, Con{x, t}),
        snoc.app(s, x, t)) : {Spec.walk(rest, Spec.W{Spec.MField{hd, List.append(&2, U32, cur, Con{x, t})}, o, _}) ==
          Spec.walk(rest, Spec.W{Spec.MField{hd, List.append(&2, U32, cur, Con{x, t})}, o, List.append(&2, U32, s, Con{x, t})}) :
          Spec.W}
      {==}

# What the proxy sends, as a list of bytes
# ----------------------------------------

def tl.app(+a: Bytes(), +b: Bytes()) ->
  {Bytes.to_list(Bytes.append(a, b)) == List.append(&2, U32, Bytes.to_list(a), Bytes.to_list(b)) : List<&2, U32>}:
  Bytes.to_list_append(a, b)

def RLl(+meth: Bytes(), +target: Bytes()) -> List<&2, U32>:
  List.append(&2, U32, Bytes.to_list(meth), Con{32, List.append(&2, U32, Bytes.to_list(target), Bytes.to_list(" HTTP/1.1"))})

def FLl(f: X.Field) -> List<&2, U32>:
  match f:
    case X.Field{n, v}:
      List.append(&2, U32, Bytes.to_list(n), Con{58, Con{32, Bytes.to_list(v)}})

def FLSl(fs: List<&2, X.Field>) -> List<&2, U32>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{f, t}:
      List.append(&2, U32, FLl(f), Con{13, Con{10, FLSl(t)}})

def rl.list(+meth: Bytes(), +target: Bytes()) -> {Bytes.to_list(X.rl.ser(meth, target)) == RLl(meth, target) : List<&2, U32>}:
  %Equal.sym(List<&2, U32>, Bytes.to_list(X.rl.ser(meth, target)),
    List.append(&2, U32, Bytes.to_list(meth), Bytes.to_list(Bytes.append(" ", Bytes.append(target, " HTTP/1.1")))),
    tl.app(meth, Bytes.append(" ", Bytes.append(target, " HTTP/1.1")))) :
    {_ == RLl(meth, target) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, Bytes.to_list(Bytes.append(target, " HTTP/1.1")),
    List.append(&2, U32, Bytes.to_list(target), Bytes.to_list(" HTTP/1.1")), tl.app(target, " HTTP/1.1")) :
    {List.append(&2, U32, Bytes.to_list(meth), Con{32, _}) == RLl(meth, target) : List<&2, U32>}
  {==}

def fl.list(f: X.Field) -> {Bytes.to_list(X.fl.ser(f)) == FLl(f) : List<&2, U32>}:
  match f:
    case X.Field{+n, +v}:
      %Equal.sym(List<&2, U32>, Bytes.to_list(Bytes.append(n, Bytes.append(": ", v))),
        List.append(&2, U32, Bytes.to_list(n), Bytes.to_list(Bytes.append(": ", v))), tl.app(n, Bytes.append(": ", v))) :
        {_ == FLl(X.Field{n, v}) : List<&2, U32>}
      {==}

def fls.list(fs: List<&2, X.Field>) -> {Bytes.to_list(X.fls.ser(fs)) == FLSl(fs) : List<&2, U32>}:
  match fs:
    case Nil{}:
      {==}
    case Con{+f, +t}:
      %Equal.sym(List<&2, U32>, Bytes.to_list(X.fls.ser(Con{f, t})),
        List.append(&2, U32, Bytes.to_list(X.fl.ser(f)), Bytes.to_list(Bytes.append("\r\n", X.fls.ser(t)))),
        tl.app(X.fl.ser(f), Bytes.append("\r\n", X.fls.ser(t)))) :
        {_ == FLSl(Con{f, t}) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, Bytes.to_list(X.fl.ser(f)), FLl(f), fl.list(f)) :
        {List.append(&2, U32, _, Con{13, Con{10, Bytes.to_list(X.fls.ser(t))}}) == FLSl(Con{f, t}) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, Bytes.to_list(X.fls.ser(t)), FLSl(t), fls.list(t)) :
        {List.append(&2, U32, FLl(f), Con{13, Con{10, _}}) == FLSl(Con{f, t}) : List<&2, U32>}
      {==}

def fls.app(a: List<&2, X.Field>, +b: List<&2, X.Field>) ->
  {FLSl(List.append(&2, X.Field, a, b)) == List.append(&2, U32, FLSl(a), FLSl(b)) : List<&2, U32>}:
  match a:
    case Nil{}:
      {==}
    case Con{+f, +t}:
      %Equal.sym(List<&2, U32>, FLSl(List.append(&2, X.Field, t, b)), List.append(&2, U32, FLSl(t), FLSl(b)),
        fls.app(t, b)) :
        {List.append(&2, U32, FLl(f), Con{13, Con{10, _}}) ==
          List.append(&2, U32, List.append(&2, U32, FLl(f), Con{13, Con{10, FLSl(t)}}), FLSl(b)) : List<&2, U32>}
      Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, FLl(f), Con{13, Con{10, FLSl(t)}}), FLSl(b)),
        List.append(&2, U32, FLl(f), Con{13, Con{10, List.append(&2, U32, FLSl(t), FLSl(b))}}),
        app.assoc(U32, FLl(f), Con{13, Con{10, FLSl(t)}}, FLSl(b)))

def SERl(m: X.Msg) -> List<&2, U32>:
  match m:
    case X.Msg{+meth, +target, +host, fs, +body, +framed}:
      List.append(&2, U32, RLl(meth, target),
        Con{13, Con{10, List.append(&2, U32, FLSl(X.allf(host, fs, framed, body)), Con{13, Con{10, Bytes.to_list(body)}})}})

def ser.list(m: X.Msg) -> {Bytes.to_list(X.ser(m)) == SERl(m) : List<&2, U32>}:
  match m:
    case X.Msg{+meth, +target, +host, +fs, +body, +framed}:
      +fls = X.fls.ser(X.allf(host, fs, framed, body))
      %Equal.sym(List<&2, U32>,
        Bytes.to_list(Bytes.append(X.rl.ser(meth, target), Bytes.append("\r\n", Bytes.append(fls, Bytes.append("\r\n", body))))),
        List.append(&2, U32, Bytes.to_list(X.rl.ser(meth, target)),
          Bytes.to_list(Bytes.append("\r\n", Bytes.append(fls, Bytes.append("\r\n", body))))),
        tl.app(X.rl.ser(meth, target), Bytes.append("\r\n", Bytes.append(fls, Bytes.append("\r\n", body))))) :
        {_ == SERl(X.Msg{meth, target, host, fs, body, framed}) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, Bytes.to_list(X.rl.ser(meth, target)), RLl(meth, target), rl.list(meth, target)) :
        {List.append(&2, U32, _, Con{13, Con{10, Bytes.to_list(Bytes.append(fls, Bytes.append("\r\n", body)))}}) ==
          SERl(X.Msg{meth, target, host, fs, body, framed}) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, Bytes.to_list(Bytes.append(fls, Bytes.append("\r\n", body))),
        List.append(&2, U32, Bytes.to_list(fls), Bytes.to_list(Bytes.append("\r\n", body))),
        tl.app(fls, Bytes.append("\r\n", body))) :
        {List.append(&2, U32, RLl(meth, target), Con{13, Con{10, _}}) == SERl(X.Msg{meth, target, host, fs, body, framed}) :
          List<&2, U32>}
      %Equal.sym(List<&2, U32>, Bytes.to_list(fls), FLSl(X.allf(host, fs, framed, body)), fls.list(X.allf(host, fs, framed, body))) :
        {List.append(&2, U32, RLl(meth, target), Con{13, Con{10, List.append(&2, U32, _, Con{13, Con{10, Bytes.to_list(body)}})}}) ==
          SERl(X.Msg{meth, target, host, fs, body, framed}) : List<&2, U32>}
      {==}

# The lines read back
# -------------------

def lit.ver() -> List<&2, U32>:
  Bytes.to_list("HTTP/1.1")

def not.full(-s: Bytes(), h: {X.full(s) == True{} : Bool}) -> Type:
  Unit

# a request line: split at its two spaces into the method and target
def view.req(meth: Bytes(), target: Bytes(), am: AA(Spec.TMeth{}, Bytes.to_list(meth)),
  at: AA(Spec.TTarget{}, Bytes.to_list(target)), nm: {X.full(meth) == True{} : Bool},
  nt: {X.full(target) == True{} : Bool}) ->
  {Spec.req.view(RLl(meth, target)) == Spec.RVer{Bytes.to_list(meth), Bytes.to_list(target), lit.ver()} : Spec.RLine}:
  match meth target:
    case SNil{} _:
      no({Spec.req.view(RLl(SNil{}, target)) == Spec.RVer{Nil{}, Bytes.to_list(target), lit.ver()} : Spec.RLine}, nm)
    case SCon{Chr{m0}, mr} SNil{}:
      no({Spec.req.view(RLl(SCon{Chr{m0}, mr}, SNil{})) == Spec.RVer{Bytes.to_list(SCon{Chr{m0}, mr}), Nil{}, lit.ver()} :
        Spec.RLine}, nt)
    case SCon{Chr{+m0}, +mr} SCon{Chr{+t0}, +tr}:
      %Equal.sym(Spec.Span, Spec.span(Spec.TMeth{}, List.append(&2, U32, Con{m0, Bytes.to_list(mr)},
          Con{32, List.append(&2, U32, Con{t0, Bytes.to_list(tr)}, Bytes.to_list(" HTTP/1.1"))})),
        Spec.Span{Con{m0, Bytes.to_list(mr)}, Spec.SAt{Spec.cls(32), 32,
          List.append(&2, U32, Con{t0, Bytes.to_list(tr)}, Bytes.to_list(" HTTP/1.1"))}},
        span.to(Spec.TMeth{}, Con{m0, Bytes.to_list(mr)}, 32,
          List.append(&2, U32, Con{t0, Bytes.to_list(tr)}, Bytes.to_list(" HTTP/1.1")), am, {==})) :
        {Spec.req.meth(_) == Spec.RVer{Con{m0, Bytes.to_list(mr)}, Con{t0, Bytes.to_list(tr)}, lit.ver()} : Spec.RLine}
      %Equal.sym(Spec.Span, Spec.span(Spec.TTarget{}, List.append(&2, U32, Con{t0, Bytes.to_list(tr)}, Con{32, lit.ver()})),
        Spec.Span{Con{t0, Bytes.to_list(tr)}, Spec.SAt{Spec.cls(32), 32, lit.ver()}},
        span.to(Spec.TTarget{}, Con{t0, Bytes.to_list(tr)}, 32, lit.ver(), at, {==})) :
        {Spec.req.target(Con{m0, Bytes.to_list(mr)}, _) ==
          Spec.RVer{Con{m0, Bytes.to_list(mr)}, Con{t0, Bytes.to_list(tr)}, lit.ver()} : Spec.RLine}
      {==}

def pl.ver() -> PL(Bytes.to_list(" HTTP/1.1")):
  ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, Unit{})))))))))

# LEMMA: the request line is read, and the fields begin
def line.req(+meth: Bytes(), +target: Bytes(), +rest: List<&2, U32>, +o: List<&2, Eng.Req>, +s: List<&2, U32>,
  +hm: {X.ok.all(Spec.TMeth{}, meth) == True{} : Bool}, +ht: {X.ok.all(Spec.TTarget{}, target) == True{} : Bool},
  nm: {X.full(meth) == True{} : Bool}, nt: {X.full(target) == True{} : Bool}) ->
  {Spec.walk(List.append(&2, U32, RLl(meth, target), Con{13, Con{10, rest}}), Spec.W{Spec.MReq{Nil{}}, o, s}) ==
    Spec.walk(rest, Spec.W{Spec.MField{Spec.head.new(Bytes.to_list(meth), Bytes.to_list(target), False{}), Nil{}}, o,
      Spec.snoc(Spec.snoc(List.append(&2, U32, s, RLl(meth, target)), 13), 10)}) : Spec.W}:
  +h0 = Spec.head.new(Bytes.to_list(meth), Bytes.to_list(target), False{})
  +s1 = List.append(&2, U32, s, RLl(meth, target))
  %Equal.sym(Spec.W, Spec.walk(List.append(&2, U32, RLl(meth, target), Con{13, Con{10, rest}}), Spec.W{Spec.MReq{Nil{}}, o, s}),
    Spec.walk(Con{13, Con{10, rest}}, Spec.W{Spec.MReq{RLl(meth, target)}, o, s1}),
    gather.req(RLl(meth, target), Con{13, Con{10, rest}}, Nil{}, o, s,
      pl.app(Bytes.to_list(meth), Con{32, List.append(&2, U32, Bytes.to_list(target), Bytes.to_list(" HTTP/1.1"))},
        aa.pl(Spec.TMeth{}, Bytes.to_list(meth), aa.of(Spec.TMeth{}, meth, hm)),
        ({==}, pl.app(Bytes.to_list(target), Bytes.to_list(" HTTP/1.1"), aa.pl(Spec.TTarget{}, Bytes.to_list(target), aa.of(Spec.TTarget{}, target, ht)),
          pl.ver()))))) :
    {_ == Spec.walk(rest, Spec.W{Spec.MField{h0, Nil{}}, o, Spec.snoc(Spec.snoc(s1, 13), 10)}) : Spec.W}
  %Equal.sym(Spec.RLine, Spec.req.view(RLl(meth, target)), Spec.RVer{Bytes.to_list(meth), Bytes.to_list(target), lit.ver()},
    view.req(meth, target, aa.of(Spec.TMeth{}, meth, hm), aa.of(Spec.TTarget{}, target, ht), nm, nt)) :
    {Spec.walk(rest, Spec.next(Spec.req.cr(_, o, Spec.snoc(s1, 13)), 10)) ==
      Spec.walk(rest, Spec.W{Spec.MField{h0, Nil{}}, o, Spec.snoc(Spec.snoc(s1, 13), 10)}) : Spec.W}
  {==}

# LEMMA: a field line is read, what it says taken into the head
def line.field(+f: X.Field, +rest: List<&2, U32>, +h: Spec.Head, +h2: Spec.Head, +o: List<&2, Eng.Req>,
  +s: List<&2, U32>, +val: Spec.Val, pl: PL(FLl(f)), hv: {Spec.field.view(FLl(f)) == Spec.FVal{val} : Spec.FLine},
  hd: {Spec.field.done(h, val) == Some{h2} : Maybe<&2, Spec.Head>}) ->
  {Spec.walk(List.append(&2, U32, FLl(f), Con{13, Con{10, rest}}), Spec.W{Spec.MField{h, Nil{}}, o, s}) ==
    Spec.walk(rest, Spec.W{Spec.MField{h2, Nil{}}, o, Spec.snoc(Spec.snoc(List.append(&2, U32, s, FLl(f)), 13), 10)}) :
    Spec.W}:
  +s1 = List.append(&2, U32, s, FLl(f))
  %Equal.sym(Spec.W, Spec.walk(List.append(&2, U32, FLl(f), Con{13, Con{10, rest}}), Spec.W{Spec.MField{h, Nil{}}, o, s}),
    Spec.walk(Con{13, Con{10, rest}}, Spec.W{Spec.MField{h, FLl(f)}, o, s1}),
    gather.field(FLl(f), Con{13, Con{10, rest}}, h, Nil{}, o, s, pl)) :
    {_ == Spec.walk(rest, Spec.W{Spec.MField{h2, Nil{}}, o, Spec.snoc(Spec.snoc(s1, 13), 10)}) : Spec.W}
  %Equal.sym(Spec.FLine, Spec.field.view(FLl(f)), Spec.FVal{val}, hv) :
    {Spec.walk(rest, Spec.next(Spec.field.cr(h, _, o, Spec.snoc(s1, 13)), 10)) ==
      Spec.walk(rest, Spec.W{Spec.MField{h2, Nil{}}, o, Spec.snoc(Spec.snoc(s1, 13), 10)}) : Spec.W}
  %Equal.sym(Maybe<&2, Spec.Head>, Spec.field.done(h, val), Some{h2}, hd) :
    {Spec.walk(rest, Spec.next(Spec.field.next(_, o, Spec.snoc(s1, 13)), 10)) ==
      Spec.walk(rest, Spec.W{Spec.MField{h2, Nil{}}, o, Spec.snoc(Spec.snoc(s1, 13), 10)}) : Spec.W}
  {==}

def is.other.eq(f: Eng.Fld, h: {X.is.other(f) == True{} : Bool}) -> {f == Eng.FOther{} : Eng.Fld}:
  match f:
    case Eng.FTe{}:
      no({Eng.FTe{} == Eng.FOther{} : Eng.Fld}, h)
    case Eng.FCl{}:
      no({Eng.FCl{} == Eng.FOther{} : Eng.Fld}, h)
    case Eng.FConn{}:
      no({Eng.FConn{} == Eng.FOther{} : Eng.Fld}, h)
    case Eng.FUp{}:
      no({Eng.FUp{} == Eng.FOther{} : Eng.Fld}, h)
    case Eng.FKey{}:
      no({Eng.FKey{} == Eng.FOther{} : Eng.Fld}, h)
    case Eng.FHost{}:
      no({Eng.FHost{} == Eng.FOther{} : Eng.Fld}, h)
    case Eng.FVer{}:
      no({Eng.FVer{} == Eng.FOther{} : Eng.Fld}, h)
    case Eng.FOther{}:
      {==}

# a name no framing reads, by spec.bend's lookup
def name.other(+n: Bytes(), hc: {X.is.other(Eng.fld.of(Eng.lows(n))) == True{} : Bool}) ->
  {Spec.field(Spec.lows(Bytes.from_list(Bytes.to_list(n)))) == Eng.FOther{} : Eng.Fld}:
  Equal.trans(Eng.Fld, Spec.field(Spec.lows(Bytes.from_list(Bytes.to_list(n)))), Spec.field(Spec.lows(n)), Eng.FOther{},
    Equal.cong(Bytes(), Eng.Fld, x => Spec.field(Spec.lows(x)), Bytes.from_list(Bytes.to_list(n)), n, bytes.rt(n)),
    Equal.trans(Eng.Fld, Spec.field(Spec.lows(n)), Spec.field(Eng.lows(n)), Eng.FOther{},
      Equal.cong(Bytes(), Eng.Fld, x => Spec.field(x), Spec.lows(n), Eng.lows(n), EP.br.lows(n)),
      Equal.trans(Eng.Fld, Spec.field(Eng.lows(n)), Eng.fld.of(Eng.lows(n)), Eng.FOther{},
        Equal.sym(Eng.Fld, Eng.fld.of(Eng.lows(n)), Spec.field(Eng.lows(n)), EL.field_by_bytes(Eng.lows(n))),
        is.other.eq(Eng.fld.of(Eng.lows(n)), hc))))

# an end-to-end field's line reads as one no framing reads
def view.other.at(n: Bytes(), +v: Bytes(), hn: {X.full(n) == True{} : Bool}, an: AA(Spec.TName{}, Bytes.to_list(n)),
  fo: {Spec.field(Spec.lows(Bytes.from_list(Bytes.to_list(n)))) == Eng.FOther{} : Eng.Fld},
  av: AA(Spec.TVal{}, Bytes.to_list(v))) ->
  {Spec.field.view(FLl(X.Field{n, v})) == Spec.FVal{Spec.VSkip{}} : Spec.FLine}:
  match n:
    case SNil{}:
      no({Spec.field.view(FLl(X.Field{SNil{}, v})) == Spec.FVal{Spec.VSkip{}} : Spec.FLine}, hn)
    case SCon{Chr{+n0}, +nr}:
      %Equal.sym(Spec.Span, Spec.span(Spec.TName{}, List.append(&2, U32, Con{n0, Bytes.to_list(nr)}, Con{58, Con{32, Bytes.to_list(v)}})),
        Spec.Span{Con{n0, Bytes.to_list(nr)}, Spec.SAt{Spec.cls(58), 58, Con{32, Bytes.to_list(v)}}},
        span.to(Spec.TName{}, Con{n0, Bytes.to_list(nr)}, 58, Con{32, Bytes.to_list(v)}, an, {==})) :
        {Spec.field.name(_) == Spec.FVal{Spec.VSkip{}} : Spec.FLine}
      %Equal.sym(Eng.Fld, Spec.field(Spec.lows(Bytes.from_list(Con{n0, Bytes.to_list(nr)}))), Eng.FOther{}, fo) :
        {Spec.field.of(_, Con{32, Bytes.to_list(v)}) == Spec.FVal{Spec.VSkip{}} : Spec.FLine}
      %Equal.sym(Spec.Span, Spec.span(Spec.TVal{}, Bytes.to_list(v)), Spec.Span{Bytes.to_list(v), Spec.SEnd{}},
        span.all(Spec.TVal{}, Bytes.to_list(v), av)) :
        {Spec.skip.view(Spec.VSkip{}, Spec.span.push(32, _)) == Spec.FVal{Spec.VSkip{}} : Spec.FLine}
      {==}

def view.other(+n: Bytes(), +v: Bytes(), hn: {X.full(n) == True{} : Bool}, +ht: {X.ok.all(Spec.TName{}, n) == True{} : Bool},
  hc: {X.is.other(Eng.fld.of(Eng.lows(n))) == True{} : Bool}, +hv: {X.ok.all(Spec.TVal{}, v) == True{} : Bool}) ->
  {Spec.field.view(FLl(X.Field{n, v})) == Spec.FVal{Spec.VSkip{}} : Spec.FLine}:
  view.other.at(n, v, hn, aa.of(Spec.TName{}, n, ht), name.other(n, hc), aa.of(Spec.TVal{}, v, hv))

def pl.other(+n: Bytes(), +v: Bytes(), +ht: {X.ok.all(Spec.TName{}, n) == True{} : Bool},
  +hv: {X.ok.all(Spec.TVal{}, v) == True{} : Bool}) -> PL(FLl(X.Field{n, v})):
  pl.app(Bytes.to_list(n), Con{58, Con{32, Bytes.to_list(v)}}, aa.pl(Spec.TName{}, Bytes.to_list(n), aa.of(Spec.TName{}, n, ht)),
    ({==}, ({==}, aa.pl(Spec.TVal{}, Bytes.to_list(v), aa.of(Spec.TVal{}, v, hv)))))

# the Host line
def view.host(+hv: Bytes(), +hh: {X.ok.all(Spec.TVal{}, hv) == True{} : Bool}) ->
  {Spec.field.view(FLl(X.Field{"host", hv})) == Spec.FVal{Spec.VHost{}} : Spec.FLine}:
  %Equal.sym(Spec.Span, Spec.span(Spec.TVal{}, Bytes.to_list(hv)), Spec.Span{Bytes.to_list(hv), Spec.SEnd{}},
    span.all(Spec.TVal{}, Bytes.to_list(hv), aa.of(Spec.TVal{}, hv, hh))) :
    {Spec.skip.view(Spec.VHost{}, Spec.span.push(32, _)) == Spec.FVal{Spec.VHost{}} : Spec.FLine}
  {==}

def pl.host(+hv: Bytes(), +hh: {X.ok.all(Spec.TVal{}, hv) == True{} : Bool}) -> PL(FLl(X.Field{"host", hv})):
  ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, aa.pl(Spec.TVal{}, Bytes.to_list(hv), aa.of(Spec.TVal{}, hv, hh))))))))

# the Content-Length line: read as its value is
def view.cl(+d: Bytes()) ->
  {Spec.field.view(FLl(X.Field{"content-length", d})) == Spec.len.view(Spec.span(Spec.TOws{}, Con{32, Bytes.to_list(d)})) :
    Spec.FLine}:
  {==}

def pl.cl(+d: Bytes(), +hd: {X.ok.all(Spec.TVal{}, d) == True{} : Bool}) -> PL(FLl(X.Field{"content-length", d})):
  ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, 
    aa.pl(Spec.TVal{}, Bytes.to_list(d), aa.of(Spec.TVal{}, d, hd))))))))))))))))))

# The fields in the middle
# ------------------------

def SF(fs: List<&2, X.Field>, s: List<&2, U32>) -> List<&2, U32>:
  match fs:
    case Nil{}:
      s
    case Con{f, t}:
      SF(t, Spec.snoc(Spec.snoc(List.append(&2, U32, s, FLl(f)), 13), 10))

def split4(a: Bool, b: Bool, c: Bool, -d: Bool, h: {(a && b && c && d) == True{} : Bool}) ->
  {a == True{} : Bool} & {b == True{} : Bool} & {c == True{} : Bool} & {d == True{} : Bool}:
  match a b c:
    case True{} True{} True{}:
      ({==}, ({==}, ({==}, h)))
    case False{} _ _:
      no({False{} == True{} : Bool} & {b == True{} : Bool} & {c == True{} : Bool} & {d == True{} : Bool}, h)
    case True{} False{} _:
      no({True{} == True{} : Bool} & {False{} == True{} : Bool} & {c == True{} : Bool} & {d == True{} : Bool}, h)
    case True{} True{} False{}:
      no({True{} == True{} : Bool} & {True{} == True{} : Bool} & {False{} == True{} : Bool} & {d == True{} : Bool}, h)

def ok.field.split(+n: Bytes(), +v: Bytes(), h: {X.ok.field(X.Field{n, v}) == True{} : Bool}) ->
  {X.full(n) == True{} : Bool} & {X.ok.all(Spec.TName{}, n) == True{} : Bool} &
    {X.is.other(Eng.fld.of(Eng.lows(n))) == True{} : Bool} & {X.ok.all(Spec.TVal{}, v) == True{} : Bool}:
  split4(X.full(n), X.ok.all(Spec.TName{}, n), X.is.other(Eng.fld.of(Eng.lows(n))), X.ok.all(Spec.TVal{}, v), h)

def line.other(+n: Bytes(), +v: Bytes(), +rest: List<&2, U32>, +h: Spec.Head, +o: List<&2, Eng.Req>, +s: List<&2, U32>,
  hn: {X.full(n) == True{} : Bool}, +ht: {X.ok.all(Spec.TName{}, n) == True{} : Bool},
  hc: {X.is.other(Eng.fld.of(Eng.lows(n))) == True{} : Bool}, +hv: {X.ok.all(Spec.TVal{}, v) == True{} : Bool}) ->
  {Spec.walk(List.append(&2, U32, FLl(X.Field{n, v}), Con{13, Con{10, rest}}), Spec.W{Spec.MField{h, Nil{}}, o, s}) ==
    Spec.walk(rest, Spec.W{Spec.MField{h, Nil{}}, o, Spec.snoc(Spec.snoc(List.append(&2, U32, s, FLl(X.Field{n, v})), 13), 10)}) :
    Spec.W}:
  line.field(X.Field{n, v}, rest, h, h, o, s, Spec.VSkip{}, pl.other(n, v, ht, hv), view.other(n, v, hn, ht, hc, hv), {==})

def line.other4(+n: Bytes(), +v: Bytes(), +rest: List<&2, U32>, +h: Spec.Head, +o: List<&2, Eng.Req>, +s: List<&2, U32>,
  fk: {X.full(n) == True{} : Bool} & {X.ok.all(Spec.TName{}, n) == True{} : Bool} &
    {X.is.other(Eng.fld.of(Eng.lows(n))) == True{} : Bool} & {X.ok.all(Spec.TVal{}, v) == True{} : Bool}) ->
  {Spec.walk(List.append(&2, U32, FLl(X.Field{n, v}), Con{13, Con{10, rest}}), Spec.W{Spec.MField{h, Nil{}}, o, s}) ==
    Spec.walk(rest, Spec.W{Spec.MField{h, Nil{}}, o, Spec.snoc(Spec.snoc(List.append(&2, U32, s, FLl(X.Field{n, v})), 13), 10)}) :
    Spec.W}:
  (hn, r1) = fk
  (ht, r2) = r1
  (hc, hv) = r2
  line.other(n, v, rest, h, o, s, hn, ht, hc, hv)

# LEMMA: the end-to-end fields are read and leave the head as it was
def fields.con(+n: Bytes(), +v: Bytes(), +t: List<&2, X.Field>, +rest: List<&2, U32>, +h: Spec.Head, +o: List<&2, Eng.Req>,
  +s: List<&2, U32>, hh: {X.ok.field(X.Field{n, v}) == True{} : Bool} & {X.ok.fields(t) == True{} : Bool},
  ih: @+s2: List<&2, U32> -> {X.ok.fields(t) == True{} : Bool} ->
    {Spec.walk(List.append(&2, U32, FLSl(t), rest), Spec.W{Spec.MField{h, Nil{}}, o, s2}) ==
      Spec.walk(rest, Spec.W{Spec.MField{h, Nil{}}, o, SF(t, s2)}) : Spec.W}) ->
  {Spec.walk(List.append(&2, U32, FLSl(Con{X.Field{n, v}, t}), rest), Spec.W{Spec.MField{h, Nil{}}, o, s}) ==
    Spec.walk(rest, Spec.W{Spec.MField{h, Nil{}}, o, SF(Con{X.Field{n, v}, t}, s)}) : Spec.W}:
  (h1, h2) = hh
  +s1 = Spec.snoc(Spec.snoc(List.append(&2, U32, s, FLl(X.Field{n, v})), 13), 10)
  %Equal.sym(List<&2, U32>,
    List.append(&2, U32, List.append(&2, U32, FLl(X.Field{n, v}), Con{13, Con{10, FLSl(t)}}), rest),
    List.append(&2, U32, FLl(X.Field{n, v}), Con{13, Con{10, List.append(&2, U32, FLSl(t), rest)}}),
    app.assoc(U32, FLl(X.Field{n, v}), Con{13, Con{10, FLSl(t)}}, rest)) :
    {Spec.walk(_, Spec.W{Spec.MField{h, Nil{}}, o, s}) == Spec.walk(rest, Spec.W{Spec.MField{h, Nil{}}, o, SF(t, s1)}) : Spec.W}
  Equal.trans(Spec.W,
    Spec.walk(List.append(&2, U32, FLl(X.Field{n, v}), Con{13, Con{10, List.append(&2, U32, FLSl(t), rest)}}),
      Spec.W{Spec.MField{h, Nil{}}, o, s}),
    Spec.walk(List.append(&2, U32, FLSl(t), rest), Spec.W{Spec.MField{h, Nil{}}, o, s1}),
    Spec.walk(rest, Spec.W{Spec.MField{h, Nil{}}, o, SF(t, s1)}),
    line.other4(n, v, List.append(&2, U32, FLSl(t), rest), h, o, s, ok.field.split(n, v, h1)),
    ih(s1, h2))

# The body
# --------

def fields.walk(fs: List<&2, X.Field>, +rest: List<&2, U32>, +h: Spec.Head, +o: List<&2, Eng.Req>, +s: List<&2, U32>,
  hok: {X.ok.fields(fs) == True{} : Bool}) ->
  {Spec.walk(List.append(&2, U32, FLSl(fs), rest), Spec.W{Spec.MField{h, Nil{}}, o, s}) ==
    Spec.walk(rest, Spec.W{Spec.MField{h, Nil{}}, o, SF(fs, s)}) : Spec.W}:
  match fs:
    case Nil{}:
      {==}
    case Con{f, +t}:
      match f:
        case X.Field{+n, +v}:
          fields.con(n, v, t, rest, h, o, s, and.split(X.ok.field(X.Field{n, v}), X.ok.fields(t), hok),
            s2 => h2 => fields.walk(t, rest, h, o, s2, h2))

# LEMMA: a body of known length is counted off to its last byte, and the
# request goes out with it
def body.walk(t: Bytes(), +c: U32, +h: Spec.Head, +got: List<&2, U32>, +o: List<&2, Eng.Req>, +s: List<&2, U32>) ->
  {Spec.walk(Con{c, Bytes.to_list(t)}, Spec.W{Spec.MBody{h, Bytes.len(t), got}, o, s}) ==
    Spec.emit(h, List.append(&2, U32, got, Con{c, Bytes.to_list(t)}), o) : Spec.W}:
  match t:
    case SNil{}:
      {==}
    case SCon{Chr{+c2}, +t2}:
      %Equal.sym(Nat, Bytes.len(SCon{Chr{c2}, t2}), 1n+Bytes.len(t2), Bytes.len.shift(t2, 0n)) :
        {Spec.walk(Con{c, Con{c2, Bytes.to_list(t2)}}, Spec.W{Spec.MBody{h, _, got}, o, s}) ==
          Spec.emit(h, List.append(&2, U32, got, Con{c, Con{c2, Bytes.to_list(t2)}}), o) : Spec.W}
      %snoc.app(got, c, Con{c2, Bytes.to_list(t2)}) :
        {Spec.walk(Con{c2, Bytes.to_list(t2)}, Spec.W{Spec.MBody{h, Bytes.len(t2), Spec.snoc(got, c)}, o, Spec.snoc(s, c)}) ==
          Spec.emit(h, _, o) : Spec.W}
      body.walk(t2, c2, h, Spec.snoc(got, c), o, Spec.snoc(s, c))

# The head's end, and the body after it
# -------------------------------------

def nat.eq(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      no({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      no({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, x => 1n+x, p, q, nat.eq(p, q, h))

# the request spec.bend reads, from the bytes the proxy sent
def RQ(+meth: Bytes(), +target: Bytes(), +body: Bytes()) -> Eng.Req:
  Eng.Req{Spec.method(meth), target, body, False{}, False{}, ""}

def rq.rt(+meth: Bytes(), +target: Bytes(), +body: Bytes()) ->
  {Eng.Req{Spec.method(Bytes.from_list(Bytes.to_list(meth))), Bytes.from_list(Bytes.to_list(target)),
    Bytes.from_list(Bytes.to_list(body)), False{}, False{}, ""} == RQ(meth, target, body) : Eng.Req}:
  %Equal.sym(Bytes(), Bytes.from_list(Bytes.to_list(meth)), meth, bytes.rt(meth)) : {Eng.Req{Spec.method(_), Bytes.from_list(Bytes.to_list(target)),
    Bytes.from_list(Bytes.to_list(body)), False{}, False{}, ""} == RQ(meth, target, body) : Eng.Req}
  %Equal.sym(Bytes(), Bytes.from_list(Bytes.to_list(target)), target, bytes.rt(target)) : {Eng.Req{Spec.method(meth), _, Bytes.from_list(Bytes.to_list(body)), False{}, False{}, ""} ==
    RQ(meth, target, body) : Eng.Req}
  %Equal.sym(Bytes(), Bytes.from_list(Bytes.to_list(body)), body, bytes.rt(body)) : {Eng.Req{Spec.method(meth), target, _, False{}, False{}, ""} == RQ(meth, target, body) : Eng.Req}
  {==}

def H1(+meth: Bytes(), +target: Bytes()) -> Spec.Head:
  Spec.head.host(Spec.head.new(Bytes.to_list(meth), Bytes.to_list(target), False{}))

def H2(+meth: Bytes(), +target: Bytes(), +n: U32) -> Spec.Head:
  Spec.Head{Spec.method(Bytes.from_list(Bytes.to_list(meth))), Bytes.to_list(target), Some{n}, False{}, 1n, Nil{}, False{},
    False{}, False{}, Eng.Fx{False{}, False{}, False{}}}

def W.done(+meth: Bytes(), +target: Bytes(), +body: Bytes(), o: List<&2, Eng.Req>) -> Spec.W:
  Spec.W{Spec.MReq{Nil{}}, Con{RQ(meth, target, body), o}, Nil{}}

# no length: the head ends the request, whose body is empty
def tail.none(+meth: Bytes(), +target: Bytes(), body: Bytes(), +o: List<&2, Eng.Req>, +s: List<&2, U32>,
  hb: {String.is_empty(body) == True{} : Bool}) ->
  {Spec.walk(Con{13, Con{10, Bytes.to_list(body)}}, Spec.W{Spec.MField{H1(meth, target), Nil{}}, o, s}) ==
    W.done(meth, target, body, o) : Spec.W}:
  match body:
    case SNil{}:
      Equal.cong(Eng.Req, Spec.W, r => Spec.W{Spec.MReq{Nil{}}, Con{r, o}, Nil{}},
        Eng.Req{Spec.method(Bytes.from_list(Bytes.to_list(meth))), Bytes.from_list(Bytes.to_list(target)),
          Bytes.from_list(Bytes.to_list("")), False{}, False{}, ""}, RQ(meth, target, ""), rq.rt(meth, target, ""))
    case SCon{c, t}:
      no({Spec.walk(Con{13, Con{10, Bytes.to_list(SCon{c, t})}}, Spec.W{Spec.MField{H1(meth, target), Nil{}}, o, s}) ==
        W.done(meth, target, SCon{c, t}, o) : Spec.W}, hb)

def sub0(x: Nat) -> {Nat.sub(x, 0n) == x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def tail.z(z: Bool, +meth: Bytes(), +target: Bytes(), body: Bytes(), +n: U32, +o: List<&2, Eng.Req>, +s: List<&2, U32>,
  hz: {X.same(z, String.is_empty(body)) == True{} : Bool}, hn: {Nat.is_eq(U32.to_nat(n), Bytes.len(body)) == True{} : Bool}) ->
  {Spec.walk(Bytes.to_list(body), Spec.head.body(z, n, H2(meth, target, n), o, s)) == W.done(meth, target, body, o) : Spec.W}:
  match z body:
    case True{} SNil{}:
      Equal.cong(Eng.Req, Spec.W, r => Spec.W{Spec.MReq{Nil{}}, Con{r, o}, Nil{}},
        Eng.Req{Spec.method(Bytes.from_list(Bytes.to_list(meth))), Bytes.from_list(Bytes.to_list(target)),
          Bytes.from_list(Bytes.to_list("")), False{}, False{}, ""}, RQ(meth, target, ""), rq.rt(meth, target, ""))
    case True{} SCon{c, t}:
      no({Spec.walk(Bytes.to_list(SCon{c, t}), Spec.head.body(True{}, n, H2(meth, target, n), o, s)) ==
        W.done(meth, target, SCon{c, t}, o) : Spec.W}, hz)
    case False{} SNil{}:
      no({Spec.walk(Nil{}, Spec.head.body(False{}, n, H2(meth, target, n), o, s)) == W.done(meth, target, SNil{}, o) : Spec.W}, hz)
    case False{} SCon{Chr{+c}, +t}:
      %Equal.sym(Nat, U32.to_nat(n), Bytes.len(SCon{Chr{c}, t}), nat.eq(U32.to_nat(n), Bytes.len(SCon{Chr{c}, t}), hn)) :
        {Spec.walk(Con{c, Bytes.to_list(t)}, Spec.W{Spec.MBody{H2(meth, target, n), Nat.sub(_, 1n), Nil{}}, o, s}) ==
          W.done(meth, target, SCon{Chr{c}, t}, o) : Spec.W}
      %Equal.sym(Nat, Bytes.len(SCon{Chr{c}, t}), 1n+Bytes.len(t), Bytes.len.shift(t, 0n)) :
        {Spec.walk(Con{c, Bytes.to_list(t)}, Spec.W{Spec.MBody{H2(meth, target, n), Nat.sub(_, 1n), Nil{}}, o, s}) ==
          W.done(meth, target, SCon{Chr{c}, t}, o) : Spec.W}
      %Equal.sym(Nat, Nat.sub(Bytes.len(t), 0n), Bytes.len(t), sub0(Bytes.len(t))) :
        {Spec.walk(Con{c, Bytes.to_list(t)}, Spec.W{Spec.MBody{H2(meth, target, n), _, Nil{}}, o, s}) ==
          W.done(meth, target, SCon{Chr{c}, t}, o) : Spec.W}
      Equal.trans(Spec.W, Spec.walk(Con{c, Bytes.to_list(t)}, Spec.W{Spec.MBody{H2(meth, target, n), Bytes.len(t), Nil{}}, o, s}),
        Spec.emit(H2(meth, target, n), Con{c, Bytes.to_list(t)}, o), W.done(meth, target, SCon{Chr{c}, t}, o),
        body.walk(t, c, H2(meth, target, n), Nil{}, o, s),
        Equal.cong(Eng.Req, Spec.W, r => Spec.W{Spec.MReq{Nil{}}, Con{r, o}, Nil{}},
          Eng.Req{Spec.method(Bytes.from_list(Bytes.to_list(meth))), Bytes.from_list(Bytes.to_list(target)),
            Bytes.from_list(Bytes.to_list(SCon{Chr{c}, t})), False{}, False{}, ""},
          RQ(meth, target, SCon{Chr{c}, t}), rq.rt(meth, target, SCon{Chr{c}, t})))

# a length: the body counted off by it
def tail.len(+meth: Bytes(), +target: Bytes(), +body: Bytes(), +n: U32, +o: List<&2, Eng.Req>, +s: List<&2, U32>,
  hz: {X.same(U32.is_zero(n), String.is_empty(body)) == True{} : Bool},
  hn: {Nat.is_eq(U32.to_nat(n), Bytes.len(body)) == True{} : Bool}) ->
  {Spec.walk(Con{13, Con{10, Bytes.to_list(body)}}, Spec.W{Spec.MField{H2(meth, target, n), Nil{}}, o, s}) ==
    W.done(meth, target, body, o) : Spec.W}:
  tail.z(U32.is_zero(n), meth, target, body, n, o, Spec.snoc(Spec.snoc(s, 13), 10), hz, hn)

# A request, read back whole
# --------------------------

def T7(a: Bool, b: Bool, c: Bool, d: Bool, e: Bool, f: Bool, g: Bool) -> Type:
  {a == True{} : Bool} & {b == True{} : Bool} & {c == True{} : Bool} & {d == True{} : Bool} & {e == True{} : Bool} &
    {f == True{} : Bool} & {g == True{} : Bool}

def split7(a: Bool, b: Bool, c: Bool, d: Bool, e: Bool, f: Bool, -g: Bool,
  h: {(a && b && c && d && e && f && g) == True{} : Bool}) -> T7(a, b, c, d, e, f, g):
  match a:
    case False{}:
      no(T7(False{}, b, c, d, e, f, g), h)
    case True{}:
      match b:
        case False{}:
          no(T7(True{}, False{}, c, d, e, f, g), h)
        case True{}:
          match c:
            case False{}:
              no(T7(True{}, True{}, False{}, d, e, f, g), h)
            case True{}:
              match d:
                case False{}:
                  no(T7(True{}, True{}, True{}, False{}, e, f, g), h)
                case True{}:
                  match e:
                    case False{}:
                      no(T7(True{}, True{}, True{}, True{}, False{}, f, g), h)
                    case True{}:
                      match f:
                        case False{}:
                          no(T7(True{}, True{}, True{}, True{}, True{}, False{}, g), h)
                        case True{}:
                          ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, h))))))

def E.tail(body: Bytes()) -> List<&2, U32>:
  Con{13, Con{10, Bytes.to_list(body)}}

def mw.cl.len(+meth: Bytes(), +target: Bytes(), +body: Bytes(), +d: Bytes(), +n: U32, +ws: Bool, +o: List<&2, Eng.Req>,
  +s: List<&2, U32>, +ad: {X.ok.all(Spec.TVal{}, d) == True{} : Bool},
  hlv: {Spec.len.view(Spec.span(Spec.TOws{}, Con{32, Bytes.to_list(d)})) == Spec.FVal{Spec.VLen{n, ws}} : Spec.FLine},
  hk: {X.same(U32.is_zero(n), String.is_empty(body)) == True{} : Bool} &
    {Nat.is_eq(U32.to_nat(n), Bytes.len(body)) == True{} : Bool}) ->
  {Spec.walk(List.append(&2, U32, FLl(X.Field{"content-length", d}), Con{13, Con{10, E.tail(body)}}),
    Spec.W{Spec.MField{H1(meth, target), Nil{}}, o, s}) == W.done(meth, target, body, o) : Spec.W}:
  (hz, hn) = hk
  Equal.trans(Spec.W,
    Spec.walk(List.append(&2, U32, FLl(X.Field{"content-length", d}), Con{13, Con{10, E.tail(body)}}),
      Spec.W{Spec.MField{H1(meth, target), Nil{}}, o, s}),
    Spec.walk(E.tail(body), Spec.W{Spec.MField{H2(meth, target, n), Nil{}}, o,
      Spec.snoc(Spec.snoc(List.append(&2, U32, s, FLl(X.Field{"content-length", d})), 13), 10)}),
    W.done(meth, target, body, o),
    line.field(X.Field{"content-length", d}, E.tail(body), H1(meth, target), H2(meth, target, n), o, s, Spec.VLen{n, ws},
      pl.cl(d, ad),
      Equal.trans(Spec.FLine, Spec.field.view(FLl(X.Field{"content-length", d})),
        Spec.len.view(Spec.span(Spec.TOws{}, Con{32, Bytes.to_list(d)})), Spec.FVal{Spec.VLen{n, ws}}, view.cl(d), hlv),
      {==}),
    tail.len(meth, target, body, n, o, Spec.snoc(Spec.snoc(List.append(&2, U32, s, FLl(X.Field{"content-length", d})), 13), 10),
      hz, hn))

def mw.cl.val(val: Spec.Val, +meth: Bytes(), +target: Bytes(), +body: Bytes(), +d: Bytes(), +o: List<&2, Eng.Req>,
  +s: List<&2, U32>, +ad: {X.ok.all(Spec.TVal{}, d) == True{} : Bool},
  hlv: {Spec.len.view(Spec.span(Spec.TOws{}, Con{32, Bytes.to_list(d)})) == Spec.FVal{val} : Spec.FLine},
  ak: {X.ok.len.at(Spec.FVal{val}, body) == True{} : Bool}) ->
  {Spec.walk(List.append(&2, U32, FLl(X.Field{"content-length", d}), Con{13, Con{10, E.tail(body)}}),
    Spec.W{Spec.MField{H1(meth, target), Nil{}}, o, s}) == W.done(meth, target, body, o) : Spec.W}:
  match val:
    case Spec.VLen{+n, +ws}:
      mw.cl.len(meth, target, body, d, n, ws, o, s, ad, hlv,
        and.split(X.same(U32.is_zero(n), String.is_empty(body)), Nat.is_eq(U32.to_nat(n), Bytes.len(body)), ak))
    case Spec.VLen0{}:
      no({Spec.walk(List.append(&2, U32, FLl(X.Field{"content-length", d}), Con{13, Con{10, E.tail(body)}}),
        Spec.W{Spec.MField{H1(meth, target), Nil{}}, o, s}) == W.done(meth, target, body, o) : Spec.W}, ak)
    case Spec.VConn{dn, cu}:
      no({Spec.walk(List.append(&2, U32, FLl(X.Field{"content-length", d}), Con{13, Con{10, E.tail(body)}}),
        Spec.W{Spec.MField{H1(meth, target), Nil{}}, o, s}) == W.done(meth, target, body, o) : Spec.W}, ak)
    case Spec.VUp{dn, cu}:
      no({Spec.walk(List.append(&2, U32, FLl(X.Field{"content-length", d}), Con{13, Con{10, E.tail(body)}}),
        Spec.W{Spec.MField{H1(meth, target), Nil{}}, o, s}) == W.done(meth, target, body, o) : Spec.W}, ak)
    case Spec.VKey0{}:
      no({Spec.walk(List.append(&2, U32, FLl(X.Field{"content-length", d}), Con{13, Con{10, E.tail(body)}}),
        Spec.W{Spec.MField{H1(meth, target), Nil{}}, o, s}) == W.done(meth, target, body, o) : Spec.W}, ak)
    case Spec.VKey{k}:
      no({Spec.walk(List.append(&2, U32, FLl(X.Field{"content-length", d}), Con{13, Con{10, E.tail(body)}}),
        Spec.W{Spec.MField{H1(meth, target), Nil{}}, o, s}) == W.done(meth, target, body, o) : Spec.W}, ak)
    case Spec.VVer{v}:
      no({Spec.walk(List.append(&2, U32, FLl(X.Field{"content-length", d}), Con{13, Con{10, E.tail(body)}}),
        Spec.W{Spec.MField{H1(meth, target), Nil{}}, o, s}) == W.done(meth, target, body, o) : Spec.W}, ak)
    case Spec.VTe0{}:
      no({Spec.walk(List.append(&2, U32, FLl(X.Field{"content-length", d}), Con{13, Con{10, E.tail(body)}}),
        Spec.W{Spec.MField{H1(meth, target), Nil{}}, o, s}) == W.done(meth, target, body, o) : Spec.W}, ak)
    case Spec.VTe{t}:
      no({Spec.walk(List.append(&2, U32, FLl(X.Field{"content-length", d}), Con{13, Con{10, E.tail(body)}}),
        Spec.W{Spec.MField{H1(meth, target), Nil{}}, o, s}) == W.done(meth, target, body, o) : Spec.W}, ak)
    case Spec.VHost{}:
      no({Spec.walk(List.append(&2, U32, FLl(X.Field{"content-length", d}), Con{13, Con{10, E.tail(body)}}),
        Spec.W{Spec.MField{H1(meth, target), Nil{}}, o, s}) == W.done(meth, target, body, o) : Spec.W}, ak)
    case Spec.VSkip{}:
      no({Spec.walk(List.append(&2, U32, FLl(X.Field{"content-length", d}), Con{13, Con{10, E.tail(body)}}),
        Spec.W{Spec.MField{H1(meth, target), Nil{}}, o, s}) == W.done(meth, target, body, o) : Spec.W}, ak)

def mw.cl.view(lv: Spec.FLine, +meth: Bytes(), +target: Bytes(), +body: Bytes(), +d: Bytes(), +o: List<&2, Eng.Req>,
  +s: List<&2, U32>, +ad: {X.ok.all(Spec.TVal{}, d) == True{} : Bool},
  hlv: {Spec.len.view(Spec.span(Spec.TOws{}, Con{32, Bytes.to_list(d)})) == lv : Spec.FLine},
  ak: {X.ok.len.at(lv, body) == True{} : Bool}) ->
  {Spec.walk(List.append(&2, U32, FLl(X.Field{"content-length", d}), Con{13, Con{10, E.tail(body)}}),
    Spec.W{Spec.MField{H1(meth, target), Nil{}}, o, s}) == W.done(meth, target, body, o) : Spec.W}:
  match lv:
    case Spec.FVal{val}:
      mw.cl.val(val, meth, target, body, d, o, s, ad, hlv, ak)
    case Spec.FEmpty{}:
      no({Spec.walk(List.append(&2, U32, FLl(X.Field{"content-length", d}), Con{13, Con{10, E.tail(body)}}),
        Spec.W{Spec.MField{H1(meth, target), Nil{}}, o, s}) == W.done(meth, target, body, o) : Spec.W}, ak)
    case Spec.FName{nm}:
      no({Spec.walk(List.append(&2, U32, FLl(X.Field{"content-length", d}), Con{13, Con{10, E.tail(body)}}),
        Spec.W{Spec.MField{H1(meth, target), Nil{}}, o, s}) == W.done(meth, target, body, o) : Spec.W}, ak)
    case Spec.FBad{}:
      no({Spec.walk(List.append(&2, U32, FLl(X.Field{"content-length", d}), Con{13, Con{10, E.tail(body)}}),
        Spec.W{Spec.MField{H1(meth, target), Nil{}}, o, s}) == W.done(meth, target, body, o) : Spec.W}, ak)

def mw.cl(+meth: Bytes(), +target: Bytes(), +body: Bytes(), +o: List<&2, Eng.Req>, +s: List<&2, U32>,
  al: {X.ok.all(Spec.TVal{}, Nat.show(Bytes.len(body))) == True{} : Bool} &
    {X.ok.len.at(Spec.len.view(Spec.span(Spec.TOws{}, Con{32, Bytes.to_list(Nat.show(Bytes.len(body)))})), body) == True{} :
      Bool}) ->
  {Spec.walk(List.append(&2, U32, FLl(X.Field{"content-length", Nat.show(Bytes.len(body))}), Con{13, Con{10, E.tail(body)}}),
    Spec.W{Spec.MField{H1(meth, target), Nil{}}, o, s}) == W.done(meth, target, body, o) : Spec.W}:
  (ad, ak) = al
  mw.cl.view(Spec.len.view(Spec.span(Spec.TOws{}, Con{32, Bytes.to_list(Nat.show(Bytes.len(body)))})), meth, target, body,
    Nat.show(Bytes.len(body)), o, s, ad, {==}, ak)

# the length, or none
def mw.len(b: Bool, +meth: Bytes(), +target: Bytes(), +body: Bytes(), +o: List<&2, Eng.Req>, +s: List<&2, U32>,
  al: {X.ok.len.on(b, body) == True{} : Bool}) ->
  {Spec.walk(List.append(&2, U32, FLSl(X.clf.at(b, body)), E.tail(body)), Spec.W{Spec.MField{H1(meth, target), Nil{}}, o, s}) ==
    W.done(meth, target, body, o) : Spec.W}:
  match b:
    case False{}:
      tail.none(meth, target, body, o, s, al)
    case True{}:
      %Equal.sym(List<&2, U32>,
        List.append(&2, U32, List.append(&2, U32, FLl(X.Field{"content-length", Nat.show(Bytes.len(body))}), Con{13, Con{10, Nil{}}}),
          E.tail(body)),
        List.append(&2, U32, FLl(X.Field{"content-length", Nat.show(Bytes.len(body))}), Con{13, Con{10, E.tail(body)}}),
        app.assoc(U32, FLl(X.Field{"content-length", Nat.show(Bytes.len(body))}), Con{13, Con{10, Nil{}}}, E.tail(body))) :
        {Spec.walk(_, Spec.W{Spec.MField{H1(meth, target), Nil{}}, o, s}) == W.done(meth, target, body, o) : Spec.W}
      mw.cl(meth, target, body, o, s,
        and.split(X.ok.all(Spec.TVal{}, Nat.show(Bytes.len(body))),
          X.ok.len.at(Spec.len.view(Spec.span(Spec.TOws{}, Con{32, Bytes.to_list(Nat.show(Bytes.len(body)))})), body), al))

def WF(+h: Spec.Head, +o: List<&2, Eng.Req>, +s: List<&2, U32>) -> Spec.W:
  Spec.W{Spec.MField{h, Nil{}}, o, s}

# LEMMA: a request the proxy checked, sent, is read back as itself: its
# line, its Host, the end-to-end fields that change nothing, its length
# and its body, and the walk is back where a request begins
def mw.at(+meth: Bytes(), +target: Bytes(), +host: Bytes(), +fs: List<&2, X.Field>, +body: Bytes(), +framed: Bool,
  +o: List<&2, Eng.Req>, +s: List<&2, U32>,
  v: T7(X.full(meth), X.ok.all(Spec.TMeth{}, meth), X.full(target), X.ok.all(Spec.TTarget{}, target),
    X.ok.all(Spec.TVal{}, host), X.ok.fields(fs), X.ok.len.on(X.clen.on(framed, body), body))) ->
  {Spec.walk(SERl(X.Msg{meth, target, host, fs, body, framed}), Spec.W{Spec.MReq{Nil{}}, o, s}) ==
    W.done(meth, target, body, o) : Spec.W}:
  (nm, v1) = v
  (hm, v2) = v1
  (nt, v3) = v2
  (ht, v4) = v3
  (+hh, v5) = v4
  (hfs, hl) = v5
  +hf : X.Field = X.Field{"host", host}
  +clf = X.clf.at(X.clen.on(framed, body), body)
  +tl = E.tail(body)
  +h0 = Spec.head.new(Bytes.to_list(meth), Bytes.to_list(target), False{})
  +h1 = H1(meth, target)
  +s1 = Spec.snoc(Spec.snoc(List.append(&2, U32, s, RLl(meth, target)), 13), 10)
  +s2 = Spec.snoc(Spec.snoc(List.append(&2, U32, s1, FLl(hf)), 13), 10)
  +r = List.append(&2, X.Field, fs, clf)
  Equal.trans(Spec.W, Spec.walk(SERl(X.Msg{meth, target, host, fs, body, framed}), Spec.W{Spec.MReq{Nil{}}, o, s}),
    Spec.walk(List.append(&2, U32, FLSl(Con{hf, r}), tl), WF(h0, o, s1)),
    W.done(meth, target, body, o),
    line.req(meth, target, List.append(&2, U32, FLSl(Con{hf, r}), tl), o, s, hm, ht, nm, nt),
    Equal.trans(Spec.W, Spec.walk(List.append(&2, U32, FLSl(Con{hf, r}), tl), WF(h0, o, s1)),
      Spec.walk(List.append(&2, U32, FLl(hf), Con{13, Con{10, List.append(&2, U32, FLSl(r), tl)}}), WF(h0, o, s1)),
      W.done(meth, target, body, o),
      Equal.cong(List<&2, U32>, Spec.W, xs => Spec.walk(xs, WF(h0, o, s1)),
        List.append(&2, U32, List.append(&2, U32, FLl(hf), Con{13, Con{10, FLSl(r)}}), tl),
        List.append(&2, U32, FLl(hf), Con{13, Con{10, List.append(&2, U32, FLSl(r), tl)}}),
        app.assoc(U32, FLl(hf), Con{13, Con{10, FLSl(r)}}, tl)),
      Equal.trans(Spec.W,
        Spec.walk(List.append(&2, U32, FLl(hf), Con{13, Con{10, List.append(&2, U32, FLSl(r), tl)}}), WF(h0, o, s1)),
        Spec.walk(List.append(&2, U32, FLSl(r), tl), WF(h1, o, s2)),
        W.done(meth, target, body, o),
        line.field(hf, List.append(&2, U32, FLSl(r), tl), h0, h1, o, s1, Spec.VHost{}, pl.host(host, hh),
          view.host(host, hh), {==}),
        Equal.trans(Spec.W, Spec.walk(List.append(&2, U32, FLSl(r), tl), WF(h1, o, s2)),
          Spec.walk(List.append(&2, U32, FLSl(fs), List.append(&2, U32, FLSl(clf), tl)), WF(h1, o, s2)),
          W.done(meth, target, body, o),
          Equal.cong(List<&2, U32>, Spec.W, xs => Spec.walk(xs, WF(h1, o, s2)),
            List.append(&2, U32, FLSl(r), tl), List.append(&2, U32, FLSl(fs), List.append(&2, U32, FLSl(clf), tl)),
            Equal.trans(List<&2, U32>, List.append(&2, U32, FLSl(r), tl),
              List.append(&2, U32, List.append(&2, U32, FLSl(fs), FLSl(clf)), tl),
              List.append(&2, U32, FLSl(fs), List.append(&2, U32, FLSl(clf), tl)),
              Equal.cong(List<&2, U32>, List<&2, U32>, xs => List.append(&2, U32, xs, tl), FLSl(r),
                List.append(&2, U32, FLSl(fs), FLSl(clf)), fls.app(fs, clf)),
              app.assoc(U32, FLSl(fs), FLSl(clf), tl))),
          Equal.trans(Spec.W, Spec.walk(List.append(&2, U32, FLSl(fs), List.append(&2, U32, FLSl(clf), tl)), WF(h1, o, s2)),
            Spec.walk(List.append(&2, U32, FLSl(clf), tl), WF(h1, o, SF(fs, s2))),
            W.done(meth, target, body, o),
            fields.walk(fs, List.append(&2, U32, FLSl(clf), tl), h1, o, s2, hfs),
            mw.len(X.clen.on(framed, body), meth, target, body, o, SF(fs, s2), hl))))))

def msg.walk(m: X.Msg, v: {X.valid(m) == True{} : Bool}, +o: List<&2, Eng.Req>, +s: List<&2, U32>) ->
  {Spec.walk(SERl(m), Spec.W{Spec.MReq{Nil{}}, o, s}) == Spec.W{Spec.MReq{Nil{}}, Con{Laws.spec.req(m), o}, Nil{}} : Spec.W}:
  match m:
    case X.Msg{+meth, +target, +host, +fs, +body, +framed}:
      mw.at(meth, target, host, fs, body, framed, o, s,
        split7(X.full(meth), X.ok.all(Spec.TMeth{}, meth), X.full(target), X.ok.all(Spec.TTarget{}, target),
          X.ok.all(Spec.TVal{}, host), X.ok.fields(fs), X.ok.len.on(X.clen.on(framed, body), body), v))

# What goes upstream passed the check
# -----------------------------------

def OK(mm: Maybe<&2, X.Msg>) -> Type:
  match mm:
    case Some{x}:
      {X.valid(x) == True{} : Bool}
    case None{}:
      Unit

def pick.ok(b: Bool, +m: X.Msg, e: {X.valid(m) == b : Bool}) -> OK(Bool.pick(Maybe<&2, X.Msg>, b, Some{m}, None{})):
  match b:
    case True{}:
      e
    case False{}:
      Unit{}

def fwd.at.ok(+w: X.Fwd, mh: Maybe<&2, X.Head>, r: Eng.Req) -> OK(X.fwd.at(w, mh, r)):
  match mh r:
    case Some{+h} Eng.Req{meth, path, +body, close, ws, key}:
      pick.ok(X.valid(X.msg.of(w, h, body)), X.msg.of(w, h, body), {==})
    case None{} _:
      Unit{}

def fwd.ok(+w: X.Fwd, t: X.Took) -> OK(X.fwd(w, t)):
  match t:
    case X.Took{+raw, r}:
      fwd.at.ok(w, X.head.of(raw), r)

# The whole stream upstream, read back
# ------------------------------------

def WR(+o: List<&2, Eng.Req>) -> Spec.W:
  Spec.W{Spec.MReq{Nil{}}, o, Nil{}}

def ns.at(mm: Maybe<&2, X.Msg>, ok: OK(mm), +rest: Bytes(), +rq: List<&2, X.Msg>, +o: List<&2, Eng.Req>,
  ih: @+o2: List<&2, Eng.Req> -> {Spec.walk(Bytes.to_list(rest), WR(o2)) ==
    WR(List.reverse.go(&2, Eng.Req, Laws.spec.reqs(rq), o2)) : Spec.W}) ->
  {Spec.walk(Bytes.to_list(X.wire.at(mm, rest)), WR(o)) ==
    WR(List.reverse.go(&2, Eng.Req, Laws.spec.reqs(Laws.fwd.msgs.at(mm, rq)), o)) : Spec.W}:
  match mm:
    case None{}:
      {==}
    case Some{+x}:
      Equal.trans(Spec.W, Spec.walk(Bytes.to_list(Bytes.append(X.ser(x), rest)), WR(o)),
        Spec.walk(List.append(&2, U32, SERl(x), Bytes.to_list(rest)), WR(o)),
        WR(List.reverse.go(&2, Eng.Req, Laws.spec.reqs(rq), Con{Laws.spec.req(x), o})),
        Equal.cong(List<&2, U32>, Spec.W, xs => Spec.walk(xs, WR(o)), Bytes.to_list(Bytes.append(X.ser(x), rest)),
          List.append(&2, U32, SERl(x), Bytes.to_list(rest)),
          Equal.trans(List<&2, U32>, Bytes.to_list(Bytes.append(X.ser(x), rest)),
            List.append(&2, U32, Bytes.to_list(X.ser(x)), Bytes.to_list(rest)),
            List.append(&2, U32, SERl(x), Bytes.to_list(rest)),
            tl.app(X.ser(x), rest),
            Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.append(&2, U32, ys, Bytes.to_list(rest)),
              Bytes.to_list(X.ser(x)), SERl(x), ser.list(x)))),
        Equal.trans(Spec.W, Spec.walk(List.append(&2, U32, SERl(x), Bytes.to_list(rest)), WR(o)),
          Spec.walk(Bytes.to_list(rest), Spec.walk(SERl(x), WR(o))),
          WR(List.reverse.go(&2, Eng.Req, Laws.spec.reqs(rq), Con{Laws.spec.req(x), o})),
          walk.app(SERl(x), Bytes.to_list(rest), WR(o)),
          Equal.trans(Spec.W, Spec.walk(Bytes.to_list(rest), Spec.walk(SERl(x), WR(o))),
            Spec.walk(Bytes.to_list(rest), WR(Con{Laws.spec.req(x), o})),
            WR(List.reverse.go(&2, Eng.Req, Laws.spec.reqs(rq), Con{Laws.spec.req(x), o})),
            Equal.cong(Spec.W, Spec.W, u => Spec.walk(Bytes.to_list(rest), u), Spec.walk(SERl(x), WR(o)),
              WR(Con{Laws.spec.req(x), o}), msg.walk(x, ok, o, Nil{})),
            ih(Con{Laws.spec.req(x), o}))))

def ns.go(+w: X.Fwd, ts: List<&2, X.Took>, +o: List<&2, Eng.Req>) ->
  {Spec.walk(Bytes.to_list(X.wire(w, ts)), WR(o)) ==
    WR(List.reverse.go(&2, Eng.Req, Laws.spec.reqs(Laws.fwd.msgs(w, ts)), o)) : Spec.W}:
  match ts:
    case Nil{}:
      {==}
    case Con{+t, +r}:
      ns.at(X.fwd(w, t), fwd.ok(w, t), X.wire(w, r), Laws.fwd.msgs(w, r), o, o2 => ns.go(w, r, o2))

def Laws.no_smuggle(w, ts):
  +xs = Laws.spec.reqs(Laws.fwd.msgs(w, ts))
  Equal.trans(Spec.Frames, Spec.finish(Spec.walk(Bytes.to_list(X.wire(w, ts)), WR(Nil{}))),
    Spec.finish(WR(List.reverse(&2, Eng.Req, xs))),
    Spec.Frames{xs, Spec.Open{Nil{}}},
    Equal.cong(Spec.W, Spec.Frames, u => Spec.finish(u), Spec.walk(Bytes.to_list(X.wire(w, ts)), WR(Nil{})),
      WR(List.reverse(&2, Eng.Req, xs)), ns.go(w, ts, Nil{})),
    Equal.cong(List<&2, Eng.Req>, Spec.Frames, ys => Spec.Frames{ys, Spec.Open{Nil{}}},
      List.reverse(&2, Eng.Req, List.reverse(&2, Eng.Req, xs)), xs, rev.rev(Eng.Req, xs)))

# The response read back
# ======================
#
# rsp_reframed: what the proxy sends a client, read by wire/http1's
# spec.bend, is one final response -- the upstream's status and body,
# the connection's fate the proxy chose -- and nothing after it. As for
# a request, the proof walks the spec over the bytes the proxy writes:
# the status line, the fields that change nothing, the length, the
# Connection, the blank line, the body.

# U32 equality is equality
def beq(ab: Bool, bb: Bool, h: {Cmp.is_eq(Bool.cmp(ab, bb)) == True{} : Bool}) -> {ab == bb : Bool}:
  match ab bb:
    case True{} True{}:
      {==}
    case False{} False{}:
      {==}
    case True{} False{}:
      no({True{} == False{} : Bool}, h)
    case False{} True{}:
      no({False{} == True{} : Bool}, h)

def fin.eq(+ab: Bool, +bb: Bool, t: Cmp, h: {Cmp.is_eq(Word.cmp.fin(ab, bb, t)) == True{} : Bool}) ->
  {Cmp.is_eq(t) == True{} : Bool} & {ab == bb : Bool}:
  match t:
    case LT{}:
      no({Cmp.is_eq(LT{}) == True{} : Bool} & {ab == bb : Bool}, h)
    case GT{}:
      no({Cmp.is_eq(GT{}) == True{} : Bool} & {ab == bb : Bool}, h)
    case EQ{}:
      ({==}, beq(ab, bb, h))

def word.at(p: Nat, +ab: Bool, +at: Word(p), +bb: Bool, +bt: Word(p),
  hh: {Cmp.is_eq(Word.cmp(p, at, bt)) == True{} : Bool} & {ab == bb : Bool},
  ih: {Cmp.is_eq(Word.cmp(p, at, bt)) == True{} : Bool} -> {at == bt : Word(p)}) ->
  {WCon{ab, at} == WCon{bb, bt} : Word(1n+p)}:
  (e1, e2) = hh
  %e2 : {WCon{ab, at} == WCon{_, bt} : Word(1n+p)}
  Equal.cong(Word(p), Word(1n+p), w => WCon{ab, w}, at, bt, ih(e1))

def word.eq(n: Nat, a: Word(n), b: Word(n), h: {Cmp.is_eq(Word.cmp(n, a, b)) == True{} : Bool}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+(+p):
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          word.at(p, ab, at, bb, bt, fin.eq(ab, bb, Word.cmp(p, at, bt), h), e => word.eq(p, at, bt, e))

def u32.eq(a: U32, b: U32, h: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  match a b:
    case U32{x} U32{y}:
      Equal.cong(Word(32n), U32, w => U32{w}, x, y, word.eq(32n, x, y, h))

def not.true(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      no({True{} == False{} : Bool}, h)
    case False{}:
      {==}

# the proxy's own 502, read back
def r502(head: Bool, +closing: Bool, +v10: Bool, +code: U32, +body: Bytes()) ->
  {RS.response(X.rask(head), Bytes.to_list(X.reply(None{}, head, closing, v10))) ==
    Laws.rlook(None{}, head, code, body, closing) : R.Look}:
  match head:
    case True{}:
      {==}
    case False{}:
      {==}

# no token of the response's lines holds a CR or an LF
def rncl(k: R.Cls) -> Bool:
  match k:
    case R.KCr{}:
      False{}
    case R.KLf{}:
      False{}
    case _:
      True{}

def RPL(xs: List<&2, U32>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{x, t}:
      {rncl(R.cls(x)) == True{} : Bool} & RPL(t)

def RAA(t: RS.Tok, xs: List<&2, U32>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{x, r}:
      {RS.allows(t, R.cls(x)) == True{} : Bool} & RAA(t, r)

def rallows.ncl(t: RS.Tok, k: R.Cls, h: {RS.allows(t, k) == True{} : Bool}) -> {rncl(k) == True{} : Bool}:
  match t k:
    case RS.TVer{} R.KCr{}:
      no({rncl(R.KCr{}) == True{} : Bool}, h)
    case RS.TVer{} R.KLf{}:
      no({rncl(R.KLf{}) == True{} : Bool}, h)
    case RS.TDig{} R.KCr{}:
      no({rncl(R.KCr{}) == True{} : Bool}, h)
    case RS.TDig{} R.KLf{}:
      no({rncl(R.KLf{}) == True{} : Bool}, h)
    case RS.TName{} R.KCr{}:
      no({rncl(R.KCr{}) == True{} : Bool}, h)
    case RS.TName{} R.KLf{}:
      no({rncl(R.KLf{}) == True{} : Bool}, h)
    case RS.TOws{} R.KCr{}:
      no({rncl(R.KCr{}) == True{} : Bool}, h)
    case RS.TOws{} R.KLf{}:
      no({rncl(R.KLf{}) == True{} : Bool}, h)
    case RS.TVal{} R.KCr{}:
      no({rncl(R.KCr{}) == True{} : Bool}, h)
    case RS.TVal{} R.KLf{}:
      no({rncl(R.KLf{}) == True{} : Bool}, h)
    case _ R.KSp{}:
      {==}
    case _ R.KHt{}:
      {==}
    case _ R.KCo{}:
      {==}
    case _ R.KCm{}:
      {==}
    case _ R.KDg{}:
      {==}
    case _ R.KTk{}:
      {==}
    case _ R.KVc{}:
      {==}
    case _ R.KCt{}:
      {==}

def raa.pl(+t: RS.Tok, xs: List<&2, U32>, h: RAA(t, xs)) -> RPL(xs):
  match xs:
    case Nil{}:
      Unit{}
    case Con{+x, r}:
      (h1, h2) = h
      (rallows.ncl(t, R.cls(x), h1), raa.pl(t, r, h2))

def rpl.app(a: List<&2, U32>, -b: List<&2, U32>, pa: RPL(a), pb: RPL(b)) -> RPL(List.append(&2, U32, a, b)):
  match a:
    case Nil{}:
      pb
    case Con{x, t}:
      (h1, h2) = pa
      (h1, rpl.app(t, b, h2, pb))

def raa.of.at(+t: RS.Tok, +c: U32, -r: Bytes(),
  h: {RS.allows(t, R.cls(c)) == True{} : Bool} & {X.rok.all(t, r) == True{} : Bool},
  ih: {X.rok.all(t, r) == True{} : Bool} -> RAA(t, Bytes.to_list(r))) ->
  RAA(t, Con{c, Bytes.to_list(r)}):
  (h1, h2) = h
  (h1, ih(h2))

def raa.of(+t: RS.Tok, s: Bytes(), h: {X.rok.all(t, s) == True{} : Bool}) -> RAA(t, Bytes.to_list(s)):
  match s:
    case SNil{}:
      Unit{}
    case SCon{Chr{+c}, r}:
      raa.of.at(t, c, r, and.split(RS.allows(t, R.cls(c)), X.rok.all(t, r), h), h2 => raa.of(t, r, h2))

def rspan.to(+t: RS.Tok, xs: List<&2, U32>, +c: U32, +rest: List<&2, U32>, h: RAA(t, xs),
  hc: {RS.allows(t, R.cls(c)) == False{} : Bool}) ->
  {RS.span(t, List.append(&2, U32, xs, Con{c, rest})) == RS.Span{xs, RS.SAt{R.cls(c), c, rest}} : RS.Span}:
  match xs:
    case Nil{}:
      %Equal.sym(Bool, RS.allows(t, R.cls(c)), False{}, hc) :
        {RS.span.pick(_, R.cls(c), c, rest, RS.span(t, rest)) == RS.Span{Nil{}, RS.SAt{R.cls(c), c, rest}} : RS.Span}
      {==}
    case Con{+x, +r}:
      (h1, h2) = h
      %Equal.sym(Bool, RS.allows(t, R.cls(x)), True{}, h1) :
        {RS.span.pick(_, R.cls(x), x, List.append(&2, U32, r, Con{c, rest}),
          RS.span(t, List.append(&2, U32, r, Con{c, rest}))) ==
          RS.Span{Con{x, r}, RS.SAt{R.cls(c), c, rest}} : RS.Span}
      %Equal.sym(RS.Span, RS.span(t, List.append(&2, U32, r, Con{c, rest})), RS.Span{r, RS.SAt{R.cls(c), c, rest}},
        rspan.to(t, r, c, rest, h2, hc)) : {RS.span.push(x, _) == RS.Span{Con{x, r}, RS.SAt{R.cls(c), c, rest}} : RS.Span}
      {==}

def rspan.all(+t: RS.Tok, xs: List<&2, U32>, h: RAA(t, xs)) -> {RS.span(t, xs) == RS.Span{xs, RS.SEnd{}} : RS.Span}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      (h1, h2) = h
      %Equal.sym(Bool, RS.allows(t, R.cls(x)), True{}, h1) :
        {RS.span.pick(_, R.cls(x), x, r, RS.span(t, r)) == RS.Span{Con{x, r}, RS.SEnd{}} : RS.Span}
      %Equal.sym(RS.Span, RS.span(t, r), RS.Span{r, RS.SEnd{}}, rspan.all(t, r, h2)) :
        {RS.span.push(x, _) == RS.Span{Con{x, r}, RS.SEnd{}} : RS.Span}
      {==}

# a line's byte is gathered
def rline.plain(k: R.Cls, -c: U32, -cur: List<&2, U32>, -cr: RS.Mode, -more: List<&2, U32> -> RS.Mode,
  h: {rncl(k) == True{} : Bool}) -> {RS.line.byte(k, c, cur, cr, more) == more(RS.snoc(cur, c)) : RS.Mode}:
  match k:
    case R.KSp{}:
      {==}
    case R.KHt{}:
      {==}
    case R.KCr{}:
      no({RS.line.byte(R.KCr{}, c, cur, cr, more) == more(RS.snoc(cur, c)) : RS.Mode}, h)
    case R.KLf{}:
      no({RS.line.byte(R.KLf{}, c, cur, cr, more) == more(RS.snoc(cur, c)) : RS.Mode}, h)
    case R.KCo{}:
      {==}
    case R.KCm{}:
      {==}
    case R.KDg{}:
      {==}
    case R.KTk{}:
      {==}
    case R.KVc{}:
      {==}
    case R.KCt{}:
      {==}

def rsnoc.app(+a: List<&2, U32>, +x: U32, +t: List<&2, U32>) ->
  {List.append(&2, U32, RS.snoc(a, x), t) == List.append(&2, U32, a, Con{x, t}) : List<&2, U32>}:
  app.assoc(U32, a, Con{x, Nil{}}, t)


def rgather.st(xs: List<&2, U32>, +rest: List<&2, U32>, +cur: List<&2, U32>, +e: R.Ask, +o: List<&2, U32>,
  pl: RPL(xs)) ->
  {RS.walk(e, List.append(&2, U32, xs, rest), RS.W{RS.MStatus{cur}, o}) ==
    RS.walk(e, rest, RS.W{RS.MStatus{List.append(&2, U32, cur, xs)}, o}) : RS.W}:
  match xs:
    case Nil{}:
      Equal.cong(List<&2, U32>, RS.W, l => RS.walk(e, rest, RS.W{RS.MStatus{l}, o}), cur, List.append(&2, U32, cur, Nil{}),
        Equal.sym(List<&2, U32>, List.append(&2, U32, cur, Nil{}), cur, app.nil(U32, cur)))
    case Con{+x, +t}:
      (h1, h2) = pl
      Equal.trans(RS.W, RS.walk(e, List.append(&2, U32, Con{x, t}, rest), RS.W{RS.MStatus{cur}, o}),
        RS.walk(e, List.append(&2, U32, t, rest), RS.W{RS.MStatus{RS.snoc(cur, x)}, o}),
        RS.walk(e, rest, RS.W{RS.MStatus{List.append(&2, U32, cur, Con{x, t})}, o}),
        Equal.cong(RS.Mode, RS.W, m => RS.walk(e, List.append(&2, U32, t, rest), RS.W{m, o}),
          RS.line.byte(R.cls(x), x, cur, RS.status.cr(RS.status.view(cur)), y => RS.MStatus{y}), RS.MStatus{RS.snoc(cur, x)},
          rline.plain(R.cls(x), x, cur, RS.status.cr(RS.status.view(cur)), y => RS.MStatus{y}, h1)),
        Equal.trans(RS.W, RS.walk(e, List.append(&2, U32, t, rest), RS.W{RS.MStatus{RS.snoc(cur, x)}, o}),
          RS.walk(e, rest, RS.W{RS.MStatus{List.append(&2, U32, RS.snoc(cur, x), t)}, o}),
          RS.walk(e, rest, RS.W{RS.MStatus{List.append(&2, U32, cur, Con{x, t})}, o}),
          rgather.st(t, rest, RS.snoc(cur, x), e, o, h2),
          Equal.cong(List<&2, U32>, RS.W, l => RS.walk(e, rest, RS.W{RS.MStatus{l}, o}),
            List.append(&2, U32, RS.snoc(cur, x), t), List.append(&2, U32, cur, Con{x, t}), rsnoc.app(cur, x, t))))

def rgather.fl(xs: List<&2, U32>, +rest: List<&2, U32>, +hd: R.Head, +cur: List<&2, U32>, +e: R.Ask, +o: List<&2, U32>,
  pl: RPL(xs)) ->
  {RS.walk(e, List.append(&2, U32, xs, rest), RS.W{RS.MField{hd, cur}, o}) ==
    RS.walk(e, rest, RS.W{RS.MField{hd, List.append(&2, U32, cur, xs)}, o}) : RS.W}:
  match xs:
    case Nil{}:
      Equal.cong(List<&2, U32>, RS.W, l => RS.walk(e, rest, RS.W{RS.MField{hd, l}, o}), cur, List.append(&2, U32, cur, Nil{}),
        Equal.sym(List<&2, U32>, List.append(&2, U32, cur, Nil{}), cur, app.nil(U32, cur)))
    case Con{+x, +t}:
      (h1, h2) = pl
      Equal.trans(RS.W, RS.walk(e, List.append(&2, U32, Con{x, t}, rest), RS.W{RS.MField{hd, cur}, o}),
        RS.walk(e, List.append(&2, U32, t, rest), RS.W{RS.MField{hd, RS.snoc(cur, x)}, o}),
        RS.walk(e, rest, RS.W{RS.MField{hd, List.append(&2, U32, cur, Con{x, t})}, o}),
        Equal.cong(RS.Mode, RS.W, m => RS.walk(e, List.append(&2, U32, t, rest), RS.W{m, o}),
          RS.line.byte(R.cls(x), x, cur, RS.field.cr(e, hd, RS.field.view(e, cur)), y => RS.MField{hd, y}), RS.MField{hd, RS.snoc(cur, x)},
          rline.plain(R.cls(x), x, cur, RS.field.cr(e, hd, RS.field.view(e, cur)), y => RS.MField{hd, y}, h1)),
        Equal.trans(RS.W, RS.walk(e, List.append(&2, U32, t, rest), RS.W{RS.MField{hd, RS.snoc(cur, x)}, o}),
          RS.walk(e, rest, RS.W{RS.MField{hd, List.append(&2, U32, RS.snoc(cur, x), t)}, o}),
          RS.walk(e, rest, RS.W{RS.MField{hd, List.append(&2, U32, cur, Con{x, t})}, o}),
          rgather.fl(t, rest, hd, RS.snoc(cur, x), e, o, h2),
          Equal.cong(List<&2, U32>, RS.W, l => RS.walk(e, rest, RS.W{RS.MField{hd, l}, o}),
            List.append(&2, U32, RS.snoc(cur, x), t), List.append(&2, U32, cur, Con{x, t}), rsnoc.app(cur, x, t))))

# The status line
# ---------------

def SLl(+cd: Bytes(), +why: Bytes()) -> List<&2, U32>:
  List.append(&2, U32, Bytes.to_list("HTTP/1.1 "), List.append(&2, U32, Bytes.to_list(cd), Con{32, Bytes.to_list(why)}))

def sl.list(+cd: Bytes(), +why: Bytes()) -> {Bytes.to_list(X.sl.ser(cd, why)) == SLl(cd, why) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, Bytes.to_list(X.sl.ser(cd, why)),
    List.append(&2, U32, Bytes.to_list("HTTP/1.1 "), Bytes.to_list(Bytes.append(cd, Bytes.append(" ", why)))),
    SLl(cd, why),
    tl.app("HTTP/1.1 ", Bytes.append(cd, Bytes.append(" ", why))),
    Equal.cong(List<&2, U32>, List<&2, U32>, l => List.append(&2, U32, Bytes.to_list("HTTP/1.1 "), l),
      Bytes.to_list(Bytes.append(cd, Bytes.append(" ", why))),
      List.append(&2, U32, Bytes.to_list(cd), Con{32, Bytes.to_list(why)}),
      tl.app(cd, Bytes.append(" ", why))))

def rpl.st(+cd: Bytes(), +why: Bytes(), +ad: {X.rok.all(RS.TDig{}, cd) == True{} : Bool}, +aw: {X.rok.all(RS.TVal{}, why) == True{} : Bool}) ->
  RPL(SLl(cd, why)):
  rpl.app(Bytes.to_list("HTTP/1.1 "), List.append(&2, U32, Bytes.to_list(cd), Con{32, Bytes.to_list(why)}),
    ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, Unit{}))))))))),
    rpl.app(Bytes.to_list(cd), Con{32, Bytes.to_list(why)}, raa.pl(RS.TDig{}, Bytes.to_list(cd), raa.of(RS.TDig{}, cd, ad)),
      ({==}, raa.pl(RS.TVal{}, Bytes.to_list(why), raa.of(RS.TVal{}, why, aw)))))

# LEMMA: the status line reads as HTTP/1.1, the code, a reason
def rview.st(+cd: Bytes(), +why: Bytes(), +ad: {X.rok.all(RS.TDig{}, cd) == True{} : Bool},
  cw: {RS.code.whole(Bytes.to_list(cd)) == True{} : Bool}, +aw: {X.rok.all(RS.TVal{}, why) == True{} : Bool}) ->
  {RS.status.view(SLl(cd, why)) == RS.VWhy{False{}, RS.num(Bytes.to_list(cd))} : RS.SView}:
  %Equal.sym(RS.Span, RS.span(RS.TDig{}, List.append(&2, U32, Bytes.to_list(cd), Con{32, Bytes.to_list(why)})),
    RS.Span{Bytes.to_list(cd), RS.SAt{R.cls(32), 32, Bytes.to_list(why)}},
    rspan.to(RS.TDig{}, Bytes.to_list(cd), 32, Bytes.to_list(why), raa.of(RS.TDig{}, cd, ad), {==})) :
    {RS.sv.code(False{}, _) == RS.VWhy{False{}, RS.num(Bytes.to_list(cd))} : RS.SView}
  %Equal.sym(Bool, RS.code.whole(Bytes.to_list(cd)), True{}, cw) :
    {RS.sv.code.sp(_, False{}, Bytes.to_list(cd), Bytes.to_list(why)) == RS.VWhy{False{}, RS.num(Bytes.to_list(cd))} : RS.SView}
  %Equal.sym(RS.Span, RS.span(RS.TVal{}, Bytes.to_list(why)), RS.Span{Bytes.to_list(why), RS.SEnd{}},
    rspan.all(RS.TVal{}, Bytes.to_list(why), raa.of(RS.TVal{}, why, aw))) :
    {RS.sv.why(False{}, RS.num(Bytes.to_list(cd)), _) == RS.VWhy{False{}, RS.num(Bytes.to_list(cd))} : RS.SView}
  {==}

# LEMMA: the status line is read, and the fields begin
def rline.st(+cd: Bytes(), +why: Bytes(), +rest: List<&2, U32>, +e: R.Ask, +o: List<&2, U32>,
  +ad: {X.rok.all(RS.TDig{}, cd) == True{} : Bool}, cw: {RS.code.whole(Bytes.to_list(cd)) == True{} : Bool},
  +aw: {X.rok.all(RS.TVal{}, why) == True{} : Bool}) ->
  {RS.walk(e, List.append(&2, U32, SLl(cd, why), Con{13, Con{10, rest}}), RS.W{RS.MStatus{Nil{}}, o}) ==
    RS.walk(e, rest, RS.W{RS.MField{R.head.new(False{}, RS.num(Bytes.to_list(cd))), Nil{}}, o}) : RS.W}:
  Equal.trans(RS.W, RS.walk(e, List.append(&2, U32, SLl(cd, why), Con{13, Con{10, rest}}), RS.W{RS.MStatus{Nil{}}, o}),
    RS.walk(e, Con{13, Con{10, rest}}, RS.W{RS.MStatus{List.append(&2, U32, Nil{}, SLl(cd, why))}, o}),
    RS.walk(e, rest, RS.W{RS.MField{R.head.new(False{}, RS.num(Bytes.to_list(cd))), Nil{}}, o}),
    rgather.st(SLl(cd, why), Con{13, Con{10, rest}}, Nil{}, e, o, rpl.st(cd, why, ad, aw)),
    Equal.cong(RS.SView, RS.W, v => RS.walk(e, rest, RS.next(e, RS.W{RS.status.cr(v), o}, 10)),
      RS.status.view(SLl(cd, why)), RS.VWhy{False{}, RS.num(Bytes.to_list(cd))}, rview.st(cd, why, ad, cw, aw)))

# The field lines
# ---------------

def rother(f: RS.Fld, h: {X.ris.other(f) == True{} : Bool}) -> {f == RS.FOther{} : RS.Fld}:
  match f:
    case RS.FOther{}:
      {==}
    case RS.FCl{}:
      no({RS.FCl{} == RS.FOther{} : RS.Fld}, h)
    case RS.FTe{}:
      no({RS.FTe{} == RS.FOther{} : RS.Fld}, h)
    case RS.FConn{}:
      no({RS.FConn{} == RS.FOther{} : RS.Fld}, h)

# LEMMA: a field the check passed reads as one that changes nothing
def rview.other(+e: R.Ask, n: Bytes(), +v: Bytes(), hn: {X.full(n) == True{} : Bool}, +ht: {X.rok.all(RS.TName{}, n) == True{} : Bool},
  hc: {X.ris.other(RS.field(RS.lows(Bytes.to_list(n)))) == True{} : Bool}, +hv: {X.rok.all(RS.TVal{}, v) == True{} : Bool}) ->
  {RS.field.view(e, FLl(X.Field{n, v})) == RS.FVal{RS.VSkip{}} : RS.FLine}:
  match n:
    case SNil{}:
      no({RS.field.view(e, FLl(X.Field{SNil{}, v})) == RS.FVal{RS.VSkip{}} : RS.FLine}, hn)
    case SCon{Chr{+c}, +r}:
      %Equal.sym(RS.Span, RS.span(RS.TName{}, List.append(&2, U32, Con{c, Bytes.to_list(r)}, Con{58, Con{32, Bytes.to_list(v)}})),
        RS.Span{Con{c, Bytes.to_list(r)}, RS.SAt{R.cls(58), 58, Con{32, Bytes.to_list(v)}}},
        rspan.to(RS.TName{}, Con{c, Bytes.to_list(r)}, 58, Con{32, Bytes.to_list(v)}, raa.of(RS.TName{}, SCon{Chr{c}, r}, ht), {==})) :
        {RS.field.name(e, _) == RS.FVal{RS.VSkip{}} : RS.FLine}
      %Equal.sym(RS.Fld, RS.field(RS.lows(Con{c, Bytes.to_list(r)})), RS.FOther{},
        rother(RS.field(RS.lows(Con{c, Bytes.to_list(r)})), hc)) :
        {RS.field.of(e, _, Con{32, Bytes.to_list(v)}) == RS.FVal{RS.VSkip{}} : RS.FLine}
      %Equal.sym(RS.Span, RS.span(RS.TVal{}, Bytes.to_list(v)), RS.Span{Bytes.to_list(v), RS.SEnd{}},
        rspan.all(RS.TVal{}, Bytes.to_list(v), raa.of(RS.TVal{}, v, hv))) :
        {RS.skip.view(RS.span.push(32, _)) == RS.FVal{RS.VSkip{}} : RS.FLine}
      {==}

def rpl.fl(+n: Bytes(), +v: Bytes(), +ht: {X.rok.all(RS.TName{}, n) == True{} : Bool}, +hv: {X.rok.all(RS.TVal{}, v) == True{} : Bool}) ->
  RPL(FLl(X.Field{n, v})):
  rpl.app(Bytes.to_list(n), Con{58, Con{32, Bytes.to_list(v)}}, raa.pl(RS.TName{}, Bytes.to_list(n), raa.of(RS.TName{}, n, ht)),
    ({==}, ({==}, raa.pl(RS.TVal{}, Bytes.to_list(v), raa.of(RS.TVal{}, v, hv)))))

# LEMMA: a field line is read, what it says taken into the head
def rline.fl(f: X.Field, +rest: List<&2, U32>, +h: R.Head, h2: R.Head, +e: R.Ask, +o: List<&2, U32>, val: RS.Val,
  pl: RPL(FLl(f)), hv: {RS.field.view(e, FLl(f)) == RS.FVal{val} : RS.FLine},
  hd: {RS.field.done(e, h, val) == Some{h2} : Maybe<&2, R.Head>}) ->
  {RS.walk(e, List.append(&2, U32, FLl(f), Con{13, Con{10, rest}}), RS.W{RS.MField{h, Nil{}}, o}) ==
    RS.walk(e, rest, RS.W{RS.MField{h2, Nil{}}, o}) : RS.W}:
  Equal.trans(RS.W, RS.walk(e, List.append(&2, U32, FLl(f), Con{13, Con{10, rest}}), RS.W{RS.MField{h, Nil{}}, o}),
    RS.walk(e, Con{13, Con{10, rest}}, RS.W{RS.MField{h, List.append(&2, U32, Nil{}, FLl(f))}, o}),
    RS.walk(e, rest, RS.W{RS.MField{h2, Nil{}}, o}),
    rgather.fl(FLl(f), Con{13, Con{10, rest}}, h, Nil{}, e, o, pl),
    Equal.trans(RS.W, RS.walk(e, rest, RS.next(e, RS.W{RS.field.cr(e, h, RS.field.view(e, FLl(f))), o}, 10)),
      RS.walk(e, rest, RS.next(e, RS.W{RS.field.cr(e, h, RS.FVal{val}), o}, 10)),
      RS.walk(e, rest, RS.W{RS.MField{h2, Nil{}}, o}),
      Equal.cong(RS.FLine, RS.W, x => RS.walk(e, rest, RS.next(e, RS.W{RS.field.cr(e, h, x), o}, 10)),
        RS.field.view(e, FLl(f)), RS.FVal{val}, hv),
      Equal.cong(Maybe<&2, R.Head>, RS.W, m => RS.walk(e, rest, RS.next(e, RS.W{RS.field.next(m), o}, 10)),
        RS.field.done(e, h, val), Some{h2}, hd)))

def rok.field.split(+n: Bytes(), +v: Bytes(), h: {X.rok.field(X.Field{n, v}) == True{} : Bool}) ->
  {X.full(n) == True{} : Bool} & {X.rok.all(RS.TName{}, n) == True{} : Bool} &
    {X.ris.other(RS.field(RS.lows(Bytes.to_list(n)))) == True{} : Bool} & {X.rok.all(RS.TVal{}, v) == True{} : Bool}:
  split4(X.full(n), X.rok.all(RS.TName{}, n), X.ris.other(RS.field(RS.lows(Bytes.to_list(n)))), X.rok.all(RS.TVal{}, v), h)

def rpl.fl.at(+n: Bytes(), +v: Bytes(), fk: {X.full(n) == True{} : Bool} & {X.rok.all(RS.TName{}, n) == True{} : Bool} &
    {X.ris.other(RS.field(RS.lows(Bytes.to_list(n)))) == True{} : Bool} & {X.rok.all(RS.TVal{}, v) == True{} : Bool}) -> RPL(FLl(X.Field{n, v})):
  (hn, r1) = fk
  (ht, r2) = r1
  (hc, hv) = r2
  rpl.fl(n, v, ht, hv)

def rview.other.at(+e: R.Ask, +n: Bytes(), +v: Bytes(), fk: {X.full(n) == True{} : Bool} & {X.rok.all(RS.TName{}, n) == True{} : Bool} &
    {X.ris.other(RS.field(RS.lows(Bytes.to_list(n)))) == True{} : Bool} & {X.rok.all(RS.TVal{}, v) == True{} : Bool}) ->
  {RS.field.view(e, FLl(X.Field{n, v})) == RS.FVal{RS.VSkip{}} : RS.FLine}:
  (hn, r1) = fk
  (ht, r2) = r1
  (hc, hv) = r2
  rview.other(e, n, v, hn, ht, hc, hv)

def rline.other4(+n: Bytes(), +v: Bytes(), +rest: List<&2, U32>, +h: R.Head, +e: R.Ask, +o: List<&2, U32>,
  +hk: {X.rok.field(X.Field{n, v}) == True{} : Bool}) ->
  {RS.walk(e, List.append(&2, U32, FLl(X.Field{n, v}), Con{13, Con{10, rest}}), RS.W{RS.MField{h, Nil{}}, o}) ==
    RS.walk(e, rest, RS.W{RS.MField{h, Nil{}}, o}) : RS.W}:
  rline.fl(X.Field{n, v}, rest, h, h, e, o, RS.VSkip{}, rpl.fl.at(n, v, rok.field.split(n, v, hk)),
    rview.other.at(e, n, v, rok.field.split(n, v, hk)), {==})

def rfields.con(+n: Bytes(), +v: Bytes(), +t: List<&2, X.Field>, +rest: List<&2, U32>, +h: R.Head, +e: R.Ask,
  +o: List<&2, U32>, hh: {X.rok.field(X.Field{n, v}) == True{} : Bool} & {X.rok.fields(t) == True{} : Bool},
  ih: {X.rok.fields(t) == True{} : Bool} ->
    {RS.walk(e, List.append(&2, U32, FLSl(t), rest), RS.W{RS.MField{h, Nil{}}, o}) ==
      RS.walk(e, rest, RS.W{RS.MField{h, Nil{}}, o}) : RS.W}) ->
  {RS.walk(e, List.append(&2, U32, FLSl(Con{X.Field{n, v}, t}), rest), RS.W{RS.MField{h, Nil{}}, o}) ==
    RS.walk(e, rest, RS.W{RS.MField{h, Nil{}}, o}) : RS.W}:
  (h1, h2) = hh
  Equal.trans(RS.W, RS.walk(e, List.append(&2, U32, FLSl(Con{X.Field{n, v}, t}), rest), RS.W{RS.MField{h, Nil{}}, o}),
    RS.walk(e, List.append(&2, U32, FLl(X.Field{n, v}), Con{13, Con{10, List.append(&2, U32, FLSl(t), rest)}}),
      RS.W{RS.MField{h, Nil{}}, o}),
    RS.walk(e, rest, RS.W{RS.MField{h, Nil{}}, o}),
    Equal.cong(List<&2, U32>, RS.W, l => RS.walk(e, l, RS.W{RS.MField{h, Nil{}}, o}),
      List.append(&2, U32, List.append(&2, U32, FLl(X.Field{n, v}), Con{13, Con{10, FLSl(t)}}), rest),
      List.append(&2, U32, FLl(X.Field{n, v}), Con{13, Con{10, List.append(&2, U32, FLSl(t), rest)}}),
      app.assoc(U32, FLl(X.Field{n, v}), Con{13, Con{10, FLSl(t)}}, rest)),
    Equal.trans(RS.W,
      RS.walk(e, List.append(&2, U32, FLl(X.Field{n, v}), Con{13, Con{10, List.append(&2, U32, FLSl(t), rest)}}),
        RS.W{RS.MField{h, Nil{}}, o}),
      RS.walk(e, List.append(&2, U32, FLSl(t), rest), RS.W{RS.MField{h, Nil{}}, o}),
      RS.walk(e, rest, RS.W{RS.MField{h, Nil{}}, o}),
      rline.other4(n, v, List.append(&2, U32, FLSl(t), rest), h, e, o, h1),
      ih(h2)))

# LEMMA: the fields the proxy carries on leave the head as it was
def rfields.walk(fs: List<&2, X.Field>, +rest: List<&2, U32>, +h: R.Head, +e: R.Ask, +o: List<&2, U32>,
  hok: {X.rok.fields(fs) == True{} : Bool}) ->
  {RS.walk(e, List.append(&2, U32, FLSl(fs), rest), RS.W{RS.MField{h, Nil{}}, o}) ==
    RS.walk(e, rest, RS.W{RS.MField{h, Nil{}}, o}) : RS.W}:
  match fs:
    case Nil{}:
      {==}
    case Con{f, +t}:
      match f:
        case X.Field{+n, +v}:
          rfields.con(n, v, t, rest, h, e, o, and.split(X.rok.field(X.Field{n, v}), X.rok.fields(t), hok),
            h2 => rfields.walk(t, rest, h, e, o, h2))

# The body
# --------

# LEMMA: a body of known length is counted off to its last byte, and the
# response is final
def rbody.walk(t: Bytes(), +c: U32, +h: R.Head, +got: List<&2, U32>, +e: R.Ask, +o: List<&2, U32>) ->
  {RS.walk(e, Con{c, Bytes.to_list(t)}, RS.W{RS.MBody{h, Bytes.len(t), got}, o}) ==
    RS.W{RS.MDone{RS.resp(h, List.append(&2, U32, got, Con{c, Bytes.to_list(t)}), False{}), Nil{}}, o} : RS.W}:
  match t:
    case SNil{}:
      {==}
    case SCon{Chr{+c2}, +t2}:
      %Equal.sym(Nat, Bytes.len(SCon{Chr{c2}, t2}), 1n+Bytes.len(t2), Bytes.len.shift(t2, 0n)) :
        {RS.walk(e, Con{c, Con{c2, Bytes.to_list(t2)}}, RS.W{RS.MBody{h, _, got}, o}) ==
          RS.W{RS.MDone{RS.resp(h, List.append(&2, U32, got, Con{c, Con{c2, Bytes.to_list(t2)}}), False{}), Nil{}}, o} : RS.W}
      %rsnoc.app(got, c, Con{c2, Bytes.to_list(t2)}) :
        {RS.walk(e, Con{c2, Bytes.to_list(t2)}, RS.W{RS.MBody{h, Bytes.len(t2), RS.snoc(got, c)}, o}) ==
          RS.W{RS.MDone{RS.resp(h, _, False{}), Nil{}}, o} : RS.W}
      rbody.walk(t2, c2, h, RS.snoc(got, c), e, o)

def rtail.z(z: Bool, +h: R.Head, body: Bytes(), +n: U32, +e: R.Ask, +o: List<&2, U32>,
  hz: {X.same(z, String.is_empty(body)) == True{} : Bool}, hn: {Nat.is_eq(U32.to_nat(n), Bytes.len(body)) == True{} : Bool}) ->
  {RS.walk(e, Bytes.to_list(body), RS.W{RS.head.body(z, h, n), o}) ==
    RS.W{RS.MDone{RS.resp(h, Bytes.to_list(body), False{}), Nil{}}, o} : RS.W}:
  match z body:
    case True{} SNil{}:
      {==}
    case True{} SCon{c, t}:
      no({RS.walk(e, Bytes.to_list(SCon{c, t}), RS.W{RS.head.body(True{}, h, n), o}) ==
        RS.W{RS.MDone{RS.resp(h, Bytes.to_list(SCon{c, t}), False{}), Nil{}}, o} : RS.W}, hz)
    case False{} SNil{}:
      no({RS.walk(e, Nil{}, RS.W{RS.head.body(False{}, h, n), o}) ==
        RS.W{RS.MDone{RS.resp(h, Nil{}, False{}), Nil{}}, o} : RS.W}, hz)
    case False{} SCon{Chr{+c}, +t}:
      %Equal.sym(Nat, U32.to_nat(n), Bytes.len(SCon{Chr{c}, t}), nat.eq(U32.to_nat(n), Bytes.len(SCon{Chr{c}, t}), hn)) :
        {RS.walk(e, Con{c, Bytes.to_list(t)}, RS.W{RS.MBody{h, Nat.sub(_, 1n), Nil{}}, o}) ==
          RS.W{RS.MDone{RS.resp(h, Con{c, Bytes.to_list(t)}, False{}), Nil{}}, o} : RS.W}
      %Equal.sym(Nat, Bytes.len(SCon{Chr{c}, t}), 1n+Bytes.len(t), Bytes.len.shift(t, 0n)) :
        {RS.walk(e, Con{c, Bytes.to_list(t)}, RS.W{RS.MBody{h, Nat.sub(_, 1n), Nil{}}, o}) ==
          RS.W{RS.MDone{RS.resp(h, Con{c, Bytes.to_list(t)}, False{}), Nil{}}, o} : RS.W}
      %Equal.sym(Nat, Nat.sub(Bytes.len(t), 0n), Bytes.len(t), sub0(Bytes.len(t))) :
        {RS.walk(e, Con{c, Bytes.to_list(t)}, RS.W{RS.MBody{h, _, Nil{}}, o}) ==
          RS.W{RS.MDone{RS.resp(h, Con{c, Bytes.to_list(t)}, False{}), Nil{}}, o} : RS.W}
      rbody.walk(t, c, h, Nil{}, e, o)

# The blank line, and the framing
# -------------------------------

# the head the proxy's fields leave: HTTP/1.1, the code, a length or
# none, no coding, closing as the proxy closes
def HC(+code: U32, +l: Maybe<&2, U32>, +closing: Bool, +v10: Bool) -> R.Head:
  R.Head{False{}, code, l, False{}, closing, v10 && Bool.not(closing)}

# LEMMA: with a code of 200 or more, the framing is none (HEAD, 204,
# 304) or the length
def rfr(head: Bool, +code: U32, +l: Maybe<&2, U32>, +cl: Bool, +ka: Bool, hlt: {U32.is_lt(code, 200) == False{} : Bool}) ->
  {RS.framing(X.rask(head), R.Head{False{}, code, l, False{}, cl, ka}) ==
    RS.frame.pick(X.rbodyless(head, code), R.FNone{}, RS.frame.len(l)) : R.Frame}:
  match head:
    case True{}:
      Equal.cong(Bool, R.Frame, b => RS.frame.pick(False{}, R.FBad{}, RS.frame.pick(b && Bool.not(U32.is_eq(code, 101)), R.FNext{},
        RS.frame.pick(True{} || b || U32.is_eq(code, 204) || U32.is_eq(code, 304), R.FNone{},
          RS.frame.pick(False{}, R.FChunked{}, RS.frame.len(l))))), U32.is_lt(code, 200), False{}, hlt)
    case False{}:
      Equal.cong(Bool, R.Frame, b => RS.frame.pick(False{}, R.FBad{}, RS.frame.pick(b && Bool.not(U32.is_eq(code, 101)), R.FNext{},
        RS.frame.pick(False{} || b || U32.is_eq(code, 204) || U32.is_eq(code, 304), R.FNone{},
          RS.frame.pick(False{}, R.FChunked{}, RS.frame.len(l))))), U32.is_lt(code, 200), False{}, hlt)

def rend.none(+head: Bool, +code: U32, +l: Maybe<&2, U32>, +cl: Bool, +ka: Bool,
  hlt: {U32.is_lt(code, 200) == False{} : Bool}, hb: {X.rbodyless(head, code) == True{} : Bool}) ->
  {RS.walk(X.rask(head), Con{13, Con{10, Nil{}}}, RS.W{RS.MField{R.Head{False{}, code, l, False{}, cl, ka}, Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{RS.resp(R.Head{False{}, code, l, False{}, cl, ka}, Nil{}, False{}), Nil{}}, Nil{}} : RS.W}:
  +h : R.Head = R.Head{False{}, code, l, False{}, cl, ka}
  Equal.trans(RS.W, RS.head.at(X.rask(head), RS.framing(X.rask(head), h), h, Nil{}),
    RS.head.at(X.rask(head), RS.frame.pick(X.rbodyless(head, code), R.FNone{}, RS.frame.len(l)), h, Nil{}),
    RS.W{RS.MDone{RS.resp(h, Nil{}, False{}), Nil{}}, Nil{}},
    Equal.cong(R.Frame, RS.W, f => RS.head.at(X.rask(head), f, h, Nil{}), RS.framing(X.rask(head), h),
      RS.frame.pick(X.rbodyless(head, code), R.FNone{}, RS.frame.len(l)), rfr(head, code, l, cl, ka, hlt)),
    Equal.cong(Bool, RS.W, b => RS.head.at(X.rask(head), RS.frame.pick(b, R.FNone{}, RS.frame.len(l)), h, Nil{}),
      X.rbodyless(head, code), True{}, hb))

def rend.len(+head: Bool, +code: U32, +n: U32, +cl: Bool, +ka: Bool, +body: Bytes(),
  hlt: {U32.is_lt(code, 200) == False{} : Bool}, hb: {X.rbodyless(head, code) == False{} : Bool},
  hz: {X.same(U32.is_zero(n), String.is_empty(body)) == True{} : Bool},
  hn: {Nat.is_eq(U32.to_nat(n), Bytes.len(body)) == True{} : Bool}) ->
  {RS.walk(X.rask(head), Con{13, Con{10, Bytes.to_list(body)}},
    RS.W{RS.MField{R.Head{False{}, code, Some{n}, False{}, cl, ka}, Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{RS.resp(R.Head{False{}, code, Some{n}, False{}, cl, ka}, Bytes.to_list(body), False{}), Nil{}}, Nil{}} : RS.W}:
  +h : R.Head = R.Head{False{}, code, Some{n}, False{}, cl, ka}
  Equal.trans(RS.W, RS.walk(X.rask(head), Bytes.to_list(body), RS.head.at(X.rask(head), RS.framing(X.rask(head), h), h, Nil{})),
    RS.walk(X.rask(head), Bytes.to_list(body),
      RS.head.at(X.rask(head), RS.frame.pick(X.rbodyless(head, code), R.FNone{}, R.FLen{n}), h, Nil{})),
    RS.W{RS.MDone{RS.resp(h, Bytes.to_list(body), False{}), Nil{}}, Nil{}},
    Equal.cong(R.Frame, RS.W, f => RS.walk(X.rask(head), Bytes.to_list(body), RS.head.at(X.rask(head), f, h, Nil{})),
      RS.framing(X.rask(head), h), RS.frame.pick(X.rbodyless(head, code), R.FNone{}, R.FLen{n}),
      rfr(head, code, Some{n}, cl, ka, hlt)),
    Equal.trans(RS.W, RS.walk(X.rask(head), Bytes.to_list(body),
        RS.head.at(X.rask(head), RS.frame.pick(X.rbodyless(head, code), R.FNone{}, R.FLen{n}), h, Nil{})),
      RS.walk(X.rask(head), Bytes.to_list(body), RS.head.at(X.rask(head), R.FLen{n}, h, Nil{})),
      RS.W{RS.MDone{RS.resp(h, Bytes.to_list(body), False{}), Nil{}}, Nil{}},
      Equal.cong(Bool, RS.W, b => RS.walk(X.rask(head), Bytes.to_list(body),
          RS.head.at(X.rask(head), RS.frame.pick(b, R.FNone{}, R.FLen{n}), h, Nil{})),
        X.rbodyless(head, code), False{}, hb),
      rtail.z(U32.is_zero(n), h, body, n, X.rask(head), Nil{}, hz, hn)))

# the response the client reads: the code, HTTP/1.1, closing as the
# proxy closes
def rresp.eq(+code: U32, +l: Maybe<&2, U32>, closing: Bool, +v10: Bool, +got: List<&2, U32>,
  h101: {U32.is_eq(code, 101) == False{} : Bool}) ->
  {RS.resp(HC(code, l, closing, v10), got, False{}) == R.Resp{code, False{}, closing, Bytes.from_list(got)} : R.Resp}:
  match closing:
    case True{}:
      {==}
    case False{}:
      Equal.cong(Bool, R.Resp, b => R.Resp{code, False{}, False{} || (False{} && Bool.not(v10 && Bool.not(False{}))) || b || False{},
        Bytes.from_list(got)}, U32.is_eq(code, 101), False{}, h101)

def rafter.none(+head: Bool, +code: U32, +l: Maybe<&2, U32>, +closing: Bool, +v10: Bool,
  hlt: {U32.is_lt(code, 200) == False{} : Bool}, h101: {U32.is_eq(code, 101) == False{} : Bool},
  hb: {X.rbodyless(head, code) == True{} : Bool}) ->
  {RS.walk(X.rask(head), Con{13, Con{10, Nil{}}}, RS.W{RS.MField{HC(code, l, closing, v10), Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, ""}, Nil{}}, Nil{}} : RS.W}:
  Equal.trans(RS.W, RS.walk(X.rask(head), Con{13, Con{10, Nil{}}}, RS.W{RS.MField{HC(code, l, closing, v10), Nil{}}, Nil{}}),
    RS.W{RS.MDone{RS.resp(HC(code, l, closing, v10), Nil{}, False{}), Nil{}}, Nil{}},
    RS.W{RS.MDone{R.Resp{code, False{}, closing, ""}, Nil{}}, Nil{}},
    rend.none(head, code, l, closing, v10 && Bool.not(closing), hlt, hb),
    Equal.cong(R.Resp, RS.W, r => RS.W{RS.MDone{r, Nil{}}, Nil{}}, RS.resp(HC(code, l, closing, v10), Nil{}, False{}),
      R.Resp{code, False{}, closing, ""}, rresp.eq(code, l, closing, v10, Nil{}, h101)))

def rafter.len(+head: Bool, +code: U32, +n: U32, +closing: Bool, +v10: Bool, +body: Bytes(),
  hlt: {U32.is_lt(code, 200) == False{} : Bool}, h101: {U32.is_eq(code, 101) == False{} : Bool},
  hb: {X.rbodyless(head, code) == False{} : Bool},
  hz: {X.same(U32.is_zero(n), String.is_empty(body)) == True{} : Bool},
  hn: {Nat.is_eq(U32.to_nat(n), Bytes.len(body)) == True{} : Bool}) ->
  {RS.walk(X.rask(head), Con{13, Con{10, Bytes.to_list(body)}}, RS.W{RS.MField{HC(code, Some{n}, closing, v10), Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, body}, Nil{}}, Nil{}} : RS.W}:
  Equal.trans(RS.W,
    RS.walk(X.rask(head), Con{13, Con{10, Bytes.to_list(body)}}, RS.W{RS.MField{HC(code, Some{n}, closing, v10), Nil{}}, Nil{}}),
    RS.W{RS.MDone{RS.resp(HC(code, Some{n}, closing, v10), Bytes.to_list(body), False{}), Nil{}}, Nil{}},
    RS.W{RS.MDone{R.Resp{code, False{}, closing, body}, Nil{}}, Nil{}},
    rend.len(head, code, n, closing, v10 && Bool.not(closing), body, hlt, hb, hz, hn),
    Equal.trans(RS.W, RS.W{RS.MDone{RS.resp(HC(code, Some{n}, closing, v10), Bytes.to_list(body), False{}), Nil{}}, Nil{}},
      RS.W{RS.MDone{R.Resp{code, False{}, closing, Bytes.from_list(Bytes.to_list(body))}, Nil{}}, Nil{}},
      RS.W{RS.MDone{R.Resp{code, False{}, closing, body}, Nil{}}, Nil{}},
      Equal.cong(R.Resp, RS.W, r => RS.W{RS.MDone{r, Nil{}}, Nil{}}, RS.resp(HC(code, Some{n}, closing, v10), Bytes.to_list(body), False{}),
        R.Resp{code, False{}, closing, Bytes.from_list(Bytes.to_list(body))},
        rresp.eq(code, Some{n}, closing, v10, Bytes.to_list(body), h101)),
      Equal.cong(Bytes(), RS.W, b => RS.W{RS.MDone{R.Resp{code, False{}, closing, b}, Nil{}}, Nil{}},
        Bytes.from_list(Bytes.to_list(body)), body, bytes.rt(body))))

# The Connection
# --------------

def rhc(h: R.Head, closing: Bool, v10: Bool) -> R.Head:
  match closing:
    case True{}:
      RS.head.conn(h, True{}, False{})
    case False{}:
      match v10:
        case True{}:
          RS.head.conn(h, False{}, True{})
        case False{}:
          h

# LEMMA: the Connection sent says what the proxy does
def rconn(closing: Bool, v10: Bool, +h: R.Head, +rest: List<&2, U32>, +e: R.Ask, +o: List<&2, U32>) ->
  {RS.walk(e, List.append(&2, U32, FLSl(X.rconf(X.conn.val(closing, v10))), rest), RS.W{RS.MField{h, Nil{}}, o}) ==
    RS.walk(e, rest, RS.W{RS.MField{rhc(h, closing, v10), Nil{}}, o}) : RS.W}:
  match closing:
    case True{}:
      {==}
    case False{}:
      match v10:
        case True{}:
          {==}
        case False{}:
          {==}

def rhc.form(closing: Bool, v10: Bool, +code: U32, +l: Maybe<&2, U32>) ->
  {rhc(R.Head{False{}, code, l, False{}, False{}, False{}}, closing, v10) == HC(code, l, closing, v10) : R.Head}:
  match closing v10:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def rconn.to(+code: U32, +l: Maybe<&2, U32>, +closing: Bool, +v10: Bool, +rest: List<&2, U32>, +e: R.Ask) ->
  {RS.walk(e, List.append(&2, U32, FLSl(X.rconf(X.conn.val(closing, v10))), rest),
    RS.W{RS.MField{R.Head{False{}, code, l, False{}, False{}, False{}}, Nil{}}, Nil{}}) ==
    RS.walk(e, rest, RS.W{RS.MField{HC(code, l, closing, v10), Nil{}}, Nil{}}) : RS.W}:
  Equal.trans(RS.W, RS.walk(e, List.append(&2, U32, FLSl(X.rconf(X.conn.val(closing, v10))), rest),
      RS.W{RS.MField{R.Head{False{}, code, l, False{}, False{}, False{}}, Nil{}}, Nil{}}),
    RS.walk(e, rest, RS.W{RS.MField{rhc(R.Head{False{}, code, l, False{}, False{}, False{}}, closing, v10), Nil{}}, Nil{}}),
    RS.walk(e, rest, RS.W{RS.MField{HC(code, l, closing, v10), Nil{}}, Nil{}}),
    rconn(closing, v10, R.Head{False{}, code, l, False{}, False{}, False{}}, rest, e, Nil{}),
    Equal.cong(R.Head, RS.W, h => RS.walk(e, rest, RS.W{RS.MField{h, Nil{}}, Nil{}}),
      rhc(R.Head{False{}, code, l, False{}, False{}, False{}}, closing, v10), HC(code, l, closing, v10),
      rhc.form(closing, v10, code, l)))

# The length, the Connection, the end
# -----------------------------------

def TAIL(clen: Bytes(), +conn: Bytes(), +b: Bytes()) -> List<&2, U32>:
  List.append(&2, U32, FLSl(List.append(&2, X.Field, X.rclf(clen), X.rconf(conn))), Con{13, Con{10, Bytes.to_list(b)}})

# no length: a response with no body by its framing
def rtail.nil(bl: Bool, +head: Bool, +code: U32, +closing: Bool, +v10: Bool, +body: Bytes(),
  hbl: {X.rbodyless(head, code) == bl : Bool}, hlt: {U32.is_lt(code, 200) == False{} : Bool},
  h101: {U32.is_eq(code, 101) == False{} : Bool}, ak: {bl == True{} : Bool}) ->
  {RS.walk(X.rask(head), TAIL("", X.conn.val(closing, v10), Bool.pick(Bytes(), bl, "", body)),
    RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), bl, "", body)}, Nil{}}, Nil{}} : RS.W}:
  match bl:
    case False{}:
      no({RS.walk(X.rask(head), TAIL("", X.conn.val(closing, v10), body),
        RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}) ==
        RS.W{RS.MDone{R.Resp{code, False{}, closing, body}, Nil{}}, Nil{}} : RS.W}, ak)
    case True{}:
      Equal.trans(RS.W, RS.walk(X.rask(head), TAIL("", X.conn.val(closing, v10), ""),
          RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}),
        RS.walk(X.rask(head), Con{13, Con{10, Nil{}}}, RS.W{RS.MField{HC(code, None{}, closing, v10), Nil{}}, Nil{}}),
        RS.W{RS.MDone{R.Resp{code, False{}, closing, ""}, Nil{}}, Nil{}},
        rconn.to(code, None{}, closing, v10, Con{13, Con{10, Nil{}}}, X.rask(head)),
        rafter.none(head, code, None{}, closing, v10, hlt, h101, hbl))

def rafter.len.pr(+head: Bool, +code: U32, +n: U32, +closing: Bool, +v10: Bool, +body: Bytes(),
  hlt: {U32.is_lt(code, 200) == False{} : Bool}, h101: {U32.is_eq(code, 101) == False{} : Bool},
  hb: {X.rbodyless(head, code) == False{} : Bool},
  hh: {X.same(U32.is_zero(n), String.is_empty(body)) == True{} : Bool} &
    {Nat.is_eq(U32.to_nat(n), Bytes.len(body)) == True{} : Bool}) ->
  {RS.walk(X.rask(head), Con{13, Con{10, Bytes.to_list(body)}}, RS.W{RS.MField{HC(code, Some{n}, closing, v10), Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, body}, Nil{}}, Nil{}} : RS.W}:
  (hz, hn) = hh
  rafter.len(head, code, n, closing, v10, body, hlt, h101, hb, hz, hn)

def rtail.fin(bl: Bool, +head: Bool, +code: U32, +n: U32, +closing: Bool, +v10: Bool, +body: Bytes(),
  hbl: {X.rbodyless(head, code) == bl : Bool}, hlt: {U32.is_lt(code, 200) == False{} : Bool},
  h101: {U32.is_eq(code, 101) == False{} : Bool},
  hrest: {(bl || (X.same(U32.is_zero(n), String.is_empty(body)) && Nat.is_eq(U32.to_nat(n), Bytes.len(body)))) == True{} : Bool}) ->
  {RS.walk(X.rask(head), Con{13, Con{10, Bytes.to_list(Bool.pick(Bytes(), bl, "", body))}},
    RS.W{RS.MField{HC(code, Some{n}, closing, v10), Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), bl, "", body)}, Nil{}}, Nil{}} : RS.W}:
  match bl:
    case True{}:
      rafter.none(head, code, Some{n}, closing, v10, hlt, h101, hbl)
    case False{}:
      rafter.len.pr(head, code, n, closing, v10, body, hlt, h101, hbl,
        and.split(X.same(U32.is_zero(n), String.is_empty(body)), Nat.is_eq(U32.to_nat(n), Bytes.len(body)), hrest))

def rpl.cl(+d: Bytes(), +ad: {X.rok.all(RS.TVal{}, d) == True{} : Bool}) -> RPL(FLl(X.Field{"content-length", d})):
  rpl.app(Bytes.to_list("content-length"), Con{58, Con{32, Bytes.to_list(d)}},
    ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, Unit{})))))))))))))),
    ({==}, ({==}, raa.pl(RS.TVal{}, Bytes.to_list(d), raa.of(RS.TVal{}, d, ad)))))

# a length the client reads as the check did
def rtail.n(+n: U32, +ws: Bool, +head: Bool, +code: U32, +d: Bytes(), +closing: Bool, +v10: Bool, +bl: Bool, +body: Bytes(),
  hbl: {X.rbodyless(head, code) == bl : Bool}, hlt: {U32.is_lt(code, 200) == False{} : Bool},
  h101: {U32.is_eq(code, 101) == False{} : Bool}, +ad: {X.rok.all(RS.TVal{}, d) == True{} : Bool},
  hlv: {RS.len.view(X.rask(head), RS.span(RS.TOws{}, Con{32, Bytes.to_list(d)})) == RS.FVal{RS.VLen{n, ws}} : RS.FLine},
  al: {Bool.not(U32.is_lt(268435455, n)) == True{} : Bool} & {(bl || (X.same(U32.is_zero(n), String.is_empty(body)) &&
    Nat.is_eq(U32.to_nat(n), Bytes.len(body)))) == True{} : Bool}) ->
  {RS.walk(X.rask(head), List.append(&2, U32, FLl(X.Field{"content-length", d}),
      Con{13, Con{10, List.append(&2, U32, FLSl(X.rconf(X.conn.val(closing, v10))),
        Con{13, Con{10, Bytes.to_list(Bool.pick(Bytes(), bl, "", body))}})}}),
    RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), bl, "", body)}, Nil{}}, Nil{}} : RS.W}:
  (hcap, hrest) = al
  +e2 : List<&2, U32> = Con{13, Con{10, Bytes.to_list(Bool.pick(Bytes(), bl, "", body))}}
  +h1 : R.Head = R.Head{False{}, code, Some{n}, False{}, False{}, False{}}
  Equal.trans(RS.W,
    RS.walk(X.rask(head), List.append(&2, U32, FLl(X.Field{"content-length", d}),
      Con{13, Con{10, List.append(&2, U32, FLSl(X.rconf(X.conn.val(closing, v10))), e2)}}),
      RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}),
    RS.walk(X.rask(head), List.append(&2, U32, FLSl(X.rconf(X.conn.val(closing, v10))), e2), RS.W{RS.MField{h1, Nil{}}, Nil{}}),
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), bl, "", body)}, Nil{}}, Nil{}},
    rline.fl(X.Field{"content-length", d}, List.append(&2, U32, FLSl(X.rconf(X.conn.val(closing, v10))), e2),
      R.head.new(False{}, code), h1, X.rask(head), Nil{}, RS.VLen{n, ws}, rpl.cl(d, ad), hlv,
      Equal.cong(Bool, Maybe<&2, R.Head>, b => RS.head.big(b, R.head.new(False{}, code), n), U32.is_lt(268435455, n), False{},
        not.true(U32.is_lt(268435455, n), hcap))),
    Equal.trans(RS.W,
      RS.walk(X.rask(head), List.append(&2, U32, FLSl(X.rconf(X.conn.val(closing, v10))), e2), RS.W{RS.MField{h1, Nil{}}, Nil{}}),
      RS.walk(X.rask(head), e2, RS.W{RS.MField{HC(code, Some{n}, closing, v10), Nil{}}, Nil{}}),
      RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), bl, "", body)}, Nil{}}, Nil{}},
      rconn.to(code, Some{n}, closing, v10, e2, X.rask(head)),
      rtail.fin(bl, head, code, n, closing, v10, body, hbl, hlt, h101, hrest)))

def rtail.val(val: RS.Val, +head: Bool, +code: U32, +d: Bytes(), +closing: Bool, +v10: Bool, +bl: Bool, +body: Bytes(),
  hbl: {X.rbodyless(head, code) == bl : Bool}, hlt: {U32.is_lt(code, 200) == False{} : Bool},
  h101: {U32.is_eq(code, 101) == False{} : Bool}, +ad: {X.rok.all(RS.TVal{}, d) == True{} : Bool},
  hlv: {RS.len.view(X.rask(head), RS.span(RS.TOws{}, Con{32, Bytes.to_list(d)})) == RS.FVal{val} : RS.FLine},
  al: {X.rok.len.at(RS.FVal{val}, bl, body) == True{} : Bool}) ->
  {RS.walk(X.rask(head), List.append(&2, U32, FLl(X.Field{"content-length", d}),
      Con{13, Con{10, List.append(&2, U32, FLSl(X.rconf(X.conn.val(closing, v10))),
        Con{13, Con{10, Bytes.to_list(Bool.pick(Bytes(), bl, "", body))}})}}),
    RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), bl, "", body)}, Nil{}}, Nil{}} : RS.W}:
  match val:
    case RS.VLen{+n, +ws}:
      rtail.n(n, ws, head, code, d, closing, v10, bl, body, hbl, hlt, h101, ad, hlv,
        and.split(Bool.not(U32.is_lt(268435455, n)), bl || (X.same(U32.is_zero(n), String.is_empty(body)) &&
          Nat.is_eq(U32.to_nat(n), Bytes.len(body))), al))
    case RS.VLen0{}:
      no({RS.walk(X.rask(head), List.append(&2, U32, FLl(X.Field{"content-length", d}),
      Con{13, Con{10, List.append(&2, U32, FLSl(X.rconf(X.conn.val(closing, v10))),
        Con{13, Con{10, Bytes.to_list(Bool.pick(Bytes(), bl, "", body))}})}}),
    RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), bl, "", body)}, Nil{}}, Nil{}} : RS.W}, al)
    case RS.VTe0{}:
      no({RS.walk(X.rask(head), List.append(&2, U32, FLl(X.Field{"content-length", d}),
      Con{13, Con{10, List.append(&2, U32, FLSl(X.rconf(X.conn.val(closing, v10))),
        Con{13, Con{10, Bytes.to_list(Bool.pick(Bytes(), bl, "", body))}})}}),
    RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), bl, "", body)}, Nil{}}, Nil{}} : RS.W}, al)
    case RS.VTe{t}:
      no({RS.walk(X.rask(head), List.append(&2, U32, FLl(X.Field{"content-length", d}),
      Con{13, Con{10, List.append(&2, U32, FLSl(X.rconf(X.conn.val(closing, v10))),
        Con{13, Con{10, Bytes.to_list(Bool.pick(Bytes(), bl, "", body))}})}}),
    RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), bl, "", body)}, Nil{}}, Nil{}} : RS.W}, al)
    case RS.VConn{dn, cu}:
      no({RS.walk(X.rask(head), List.append(&2, U32, FLl(X.Field{"content-length", d}),
      Con{13, Con{10, List.append(&2, U32, FLSl(X.rconf(X.conn.val(closing, v10))),
        Con{13, Con{10, Bytes.to_list(Bool.pick(Bytes(), bl, "", body))}})}}),
    RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), bl, "", body)}, Nil{}}, Nil{}} : RS.W}, al)
    case RS.VSkip{}:
      no({RS.walk(X.rask(head), List.append(&2, U32, FLl(X.Field{"content-length", d}),
      Con{13, Con{10, List.append(&2, U32, FLSl(X.rconf(X.conn.val(closing, v10))),
        Con{13, Con{10, Bytes.to_list(Bool.pick(Bytes(), bl, "", body))}})}}),
    RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), bl, "", body)}, Nil{}}, Nil{}} : RS.W}, al)

def rtail.lv(lv: RS.FLine, +head: Bool, +code: U32, +d: Bytes(), +closing: Bool, +v10: Bool, +bl: Bool, +body: Bytes(),
  hbl: {X.rbodyless(head, code) == bl : Bool}, hlt: {U32.is_lt(code, 200) == False{} : Bool},
  h101: {U32.is_eq(code, 101) == False{} : Bool}, +ad: {X.rok.all(RS.TVal{}, d) == True{} : Bool},
  hlv: {RS.len.view(X.rask(head), RS.span(RS.TOws{}, Con{32, Bytes.to_list(d)})) == lv : RS.FLine},
  al: {X.rok.len.at(lv, bl, body) == True{} : Bool}) ->
  {RS.walk(X.rask(head), List.append(&2, U32, FLl(X.Field{"content-length", d}),
      Con{13, Con{10, List.append(&2, U32, FLSl(X.rconf(X.conn.val(closing, v10))),
        Con{13, Con{10, Bytes.to_list(Bool.pick(Bytes(), bl, "", body))}})}}),
    RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), bl, "", body)}, Nil{}}, Nil{}} : RS.W}:
  match lv:
    case RS.FVal{val}:
      rtail.val(val, head, code, d, closing, v10, bl, body, hbl, hlt, h101, ad, hlv, al)
    case RS.FEmpty{}:
      no({RS.walk(X.rask(head), List.append(&2, U32, FLl(X.Field{"content-length", d}),
      Con{13, Con{10, List.append(&2, U32, FLSl(X.rconf(X.conn.val(closing, v10))),
        Con{13, Con{10, Bytes.to_list(Bool.pick(Bytes(), bl, "", body))}})}}),
    RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), bl, "", body)}, Nil{}}, Nil{}} : RS.W}, al)
    case RS.FName{nm}:
      no({RS.walk(X.rask(head), List.append(&2, U32, FLl(X.Field{"content-length", d}),
      Con{13, Con{10, List.append(&2, U32, FLSl(X.rconf(X.conn.val(closing, v10))),
        Con{13, Con{10, Bytes.to_list(Bool.pick(Bytes(), bl, "", body))}})}}),
    RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), bl, "", body)}, Nil{}}, Nil{}} : RS.W}, al)
    case RS.FBad{}:
      no({RS.walk(X.rask(head), List.append(&2, U32, FLl(X.Field{"content-length", d}),
      Con{13, Con{10, List.append(&2, U32, FLSl(X.rconf(X.conn.val(closing, v10))),
        Con{13, Con{10, Bytes.to_list(Bool.pick(Bytes(), bl, "", body))}})}}),
    RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), bl, "", body)}, Nil{}}, Nil{}} : RS.W}, al)

def rtail.cl2(+c: Char, +t: Bytes(), +head: Bool, +code: U32, +closing: Bool, +v10: Bool, +bl: Bool, +body: Bytes(),
  hbl: {X.rbodyless(head, code) == bl : Bool}, hlt: {U32.is_lt(code, 200) == False{} : Bool},
  h101: {U32.is_eq(code, 101) == False{} : Bool},
  hh: {X.rok.all(RS.TVal{}, SCon{c, t}) == True{} : Bool} &
    {X.rok.len.at(RS.len.view(X.rask(head), RS.span(RS.TOws{}, Con{32, Bytes.to_list(SCon{c, t})})), bl, body) == True{} : Bool}) ->
  {RS.walk(X.rask(head), TAIL(SCon{c, t}, X.conn.val(closing, v10), Bool.pick(Bytes(), bl, "", body)),
    RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), bl, "", body)}, Nil{}}, Nil{}} : RS.W}:
  (ad, al) = hh
  +d : Bytes() = SCon{c, t}
  +e2 : List<&2, U32> = Con{13, Con{10, Bytes.to_list(Bool.pick(Bytes(), bl, "", body))}}
  +cf : List<&2, U32> = FLSl(X.rconf(X.conn.val(closing, v10)))
  Equal.trans(RS.W, RS.walk(X.rask(head), TAIL(d, X.conn.val(closing, v10), Bool.pick(Bytes(), bl, "", body)),
      RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}),
    RS.walk(X.rask(head), List.append(&2, U32, FLl(X.Field{"content-length", d}), Con{13, Con{10, List.append(&2, U32, cf, e2)}}),
      RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}),
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), bl, "", body)}, Nil{}}, Nil{}},
    Equal.cong(List<&2, U32>, RS.W, l => RS.walk(X.rask(head), l, RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}),
      List.append(&2, U32, List.append(&2, U32, FLl(X.Field{"content-length", d}), Con{13, Con{10, cf}}), e2),
      List.append(&2, U32, FLl(X.Field{"content-length", d}), Con{13, Con{10, List.append(&2, U32, cf, e2)}}),
      app.assoc(U32, FLl(X.Field{"content-length", d}), Con{13, Con{10, cf}}, e2)),
    rtail.lv(RS.len.view(X.rask(head), RS.span(RS.TOws{}, Con{32, Bytes.to_list(d)})), head, code, d, closing, v10, bl, body, hbl, hlt, h101, ad, {==}, al))

def rtail.cl(+c: Char, +t: Bytes(), +head: Bool, +code: U32, +closing: Bool, +v10: Bool, +bl: Bool, +body: Bytes(),
  hbl: {X.rbodyless(head, code) == bl : Bool}, hlt: {U32.is_lt(code, 200) == False{} : Bool},
  h101: {U32.is_eq(code, 101) == False{} : Bool}, ak: {X.rok.len(head, bl, SCon{c, t}, body) == True{} : Bool}) ->
  {RS.walk(X.rask(head), TAIL(SCon{c, t}, X.conn.val(closing, v10), Bool.pick(Bytes(), bl, "", body)),
    RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), bl, "", body)}, Nil{}}, Nil{}} : RS.W}:
  +d : Bytes() = SCon{c, t}
  rtail.cl2(c, t, head, code, closing, v10, bl, body, hbl, hlt, h101, and.split(X.rok.all(RS.TVal{}, d), X.rok.len.at(RS.len.view(X.rask(head), RS.span(RS.TOws{}, Con{32, Bytes.to_list(d)})), bl, body), ak))

def rtail(clen: Bytes(), +head: Bool, +code: U32, +closing: Bool, +v10: Bool, +bl: Bool, +body: Bytes(),
  hbl: {X.rbodyless(head, code) == bl : Bool}, hlt: {U32.is_lt(code, 200) == False{} : Bool},
  h101: {U32.is_eq(code, 101) == False{} : Bool}, ak: {X.rok.len(head, bl, clen, body) == True{} : Bool}) ->
  {RS.walk(X.rask(head), TAIL(clen, X.conn.val(closing, v10), Bool.pick(Bytes(), bl, "", body)),
    RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), bl, "", body)}, Nil{}}, Nil{}} : RS.W}:
  match clen:
    case SNil{}:
      rtail.nil(bl, head, code, closing, v10, body, hbl, hlt, h101, ak)
    case SCon{+c, +t}:
      rtail.cl(c, t, head, code, closing, v10, bl, body, hbl, hlt, h101, ak)


# The whole response
# ------------------

def RSERl(+cd: Bytes(), +why: Bytes(), fs: List<&2, X.Field>, clen: Bytes(), +conn: Bytes(), +b: Bytes()) -> List<&2, U32>:
  List.append(&2, U32, SLl(cd, why),
    Con{13, Con{10, List.append(&2, U32, FLSl(X.rall(fs, clen, conn)), Con{13, Con{10, Bytes.to_list(b)}})}})

def rser.list(+cd: Bytes(), +why: Bytes(), +fs: List<&2, X.Field>, +clen: Bytes(), +conn: Bytes(), +body: Bytes(), +bl: Bool) ->
  {Bytes.to_list(X.rser(X.Rsp{cd, why, fs, clen, body, bl}, conn)) ==
    RSERl(cd, why, fs, clen, conn, Bool.pick(Bytes(), bl, "", body)) : List<&2, U32>}:
  +f = X.fls.ser(X.rall(fs, clen, conn))
  +b = Bool.pick(Bytes(), bl, "", body)
  Equal.trans(List<&2, U32>, Bytes.to_list(X.rser(X.Rsp{cd, why, fs, clen, body, bl}, conn)),
    List.append(&2, U32, Bytes.to_list(X.sl.ser(cd, why)), Bytes.to_list(Bytes.append("\r\n", Bytes.append(f, Bytes.append("\r\n", b))))),
    RSERl(cd, why, fs, clen, conn, b),
    tl.app(X.sl.ser(cd, why), Bytes.append("\r\n", Bytes.append(f, Bytes.append("\r\n", b)))),
    Equal.trans(List<&2, U32>,
      List.append(&2, U32, Bytes.to_list(X.sl.ser(cd, why)), Con{13, Con{10, Bytes.to_list(Bytes.append(f, Bytes.append("\r\n", b)))}}),
      List.append(&2, U32, SLl(cd, why), Con{13, Con{10, Bytes.to_list(Bytes.append(f, Bytes.append("\r\n", b)))}}),
      RSERl(cd, why, fs, clen, conn, b),
      Equal.cong(List<&2, U32>, List<&2, U32>,
        l => List.append(&2, U32, l, Con{13, Con{10, Bytes.to_list(Bytes.append(f, Bytes.append("\r\n", b)))}}),
        Bytes.to_list(X.sl.ser(cd, why)), SLl(cd, why), sl.list(cd, why)),
      Equal.cong(List<&2, U32>, List<&2, U32>, l => List.append(&2, U32, SLl(cd, why), Con{13, Con{10, l}}),
        Bytes.to_list(Bytes.append(f, Bytes.append("\r\n", b))),
        List.append(&2, U32, FLSl(X.rall(fs, clen, conn)), Con{13, Con{10, Bytes.to_list(b)}}),
        Equal.trans(List<&2, U32>, Bytes.to_list(Bytes.append(f, Bytes.append("\r\n", b))),
          List.append(&2, U32, Bytes.to_list(f), Bytes.to_list(Bytes.append("\r\n", b))),
          List.append(&2, U32, FLSl(X.rall(fs, clen, conn)), Con{13, Con{10, Bytes.to_list(b)}}),
          tl.app(f, Bytes.append("\r\n", b)),
          Equal.cong(List<&2, U32>, List<&2, U32>, l => List.append(&2, U32, l, Con{13, Con{10, Bytes.to_list(b)}}),
            Bytes.to_list(f), FLSl(X.rall(fs, clen, conn)), fls.list(X.rall(fs, clen, conn)))))))

def T5(a: Bool, b: Bool, c: Bool, d: Bool, e: Bool) -> Type:
  {a == True{} : Bool} & {b == True{} : Bool} & {c == True{} : Bool} & {d == True{} : Bool} & {e == True{} : Bool}

def split5(a: Bool, b: Bool, c: Bool, d: Bool, -e: Bool, h: {(a && b && c && d && e) == True{} : Bool}) -> T5(a, b, c, d, e):
  match a b c d:
    case True{} True{} True{} True{}:
      ({==}, ({==}, ({==}, ({==}, h))))
    case False{} _ _ _:
      no(T5(False{}, b, c, d, e), h)
    case True{} False{} _ _:
      no(T5(True{}, False{}, c, d, e), h)
    case True{} True{} False{} _:
      no(T5(True{}, True{}, False{}, d, e), h)
    case True{} True{} True{} False{}:
      no(T5(True{}, True{}, True{}, False{}, e), h)

# LEMMA: a response the check passed, sent, is read back as the one that
# came, to its end
def rmain.at(+cd: Bytes(), +why: Bytes(), +fs: List<&2, X.Field>, +clen: Bytes(), +head: Bool, +code: U32, +body: Bytes(),
  +closing: Bool, +v10: Bool,
  hc: T5(X.rok.all(RS.TDig{}, cd), RS.code.whole(Bytes.to_list(cd)), U32.is_eq(RS.num(Bytes.to_list(cd)), code),
    Bool.not(U32.is_lt(code, 200)), Bool.not(U32.is_eq(code, 101))),
  +aw: {X.rok.all(RS.TVal{}, why) == True{} : Bool}, hfs: {X.rok.fields(fs) == True{} : Bool},
  hl: {X.rok.len(head, X.rbodyless(head, code), clen, body) == True{} : Bool}) ->
  {RS.walk(X.rask(head), Bytes.to_list(X.rser(X.Rsp{cd, why, fs, clen, body, X.rbodyless(head, code)}, X.conn.val(closing, v10))),
    RS.W{RS.MStatus{Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), X.rbodyless(head, code), "", body)}, Nil{}}, Nil{}} : RS.W}:
  (+ad, r1) = hc
  (cw, r2) = r1
  (heq, r3) = r2
  (hlt0, h1010) = r3
  +e = X.rask(head)
  +conn = X.conn.val(closing, v10)
  +bl = X.rbodyless(head, code)
  +b = Bool.pick(Bytes(), bl, "", body)
  +e2 : List<&2, U32> = Con{13, Con{10, Bytes.to_list(b)}}
  +cf : List<&2, X.Field> = List.append(&2, X.Field, X.rclf(clen), X.rconf(conn))
  Equal.trans(RS.W, RS.walk(e, Bytes.to_list(X.rser(X.Rsp{cd, why, fs, clen, body, bl}, conn)), RS.W{RS.MStatus{Nil{}}, Nil{}}),
    RS.walk(e, RSERl(cd, why, fs, clen, conn, b), RS.W{RS.MStatus{Nil{}}, Nil{}}),
    RS.W{RS.MDone{R.Resp{code, False{}, closing, b}, Nil{}}, Nil{}},
    Equal.cong(List<&2, U32>, RS.W, l => RS.walk(e, l, RS.W{RS.MStatus{Nil{}}, Nil{}}),
      Bytes.to_list(X.rser(X.Rsp{cd, why, fs, clen, body, bl}, conn)), RSERl(cd, why, fs, clen, conn, b),
      rser.list(cd, why, fs, clen, conn, body, bl)),
    Equal.trans(RS.W, RS.walk(e, RSERl(cd, why, fs, clen, conn, b), RS.W{RS.MStatus{Nil{}}, Nil{}}),
      RS.walk(e, List.append(&2, U32, FLSl(X.rall(fs, clen, conn)), e2),
        RS.W{RS.MField{R.head.new(False{}, RS.num(Bytes.to_list(cd))), Nil{}}, Nil{}}),
      RS.W{RS.MDone{R.Resp{code, False{}, closing, b}, Nil{}}, Nil{}},
      rline.st(cd, why, List.append(&2, U32, FLSl(X.rall(fs, clen, conn)), e2), e, Nil{}, ad, cw, aw),
      Equal.trans(RS.W, RS.walk(e, List.append(&2, U32, FLSl(X.rall(fs, clen, conn)), e2),
          RS.W{RS.MField{R.head.new(False{}, RS.num(Bytes.to_list(cd))), Nil{}}, Nil{}}),
        RS.walk(e, List.append(&2, U32, FLSl(X.rall(fs, clen, conn)), e2), RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}),
        RS.W{RS.MDone{R.Resp{code, False{}, closing, b}, Nil{}}, Nil{}},
        Equal.cong(U32, RS.W, x => RS.walk(e, List.append(&2, U32, FLSl(X.rall(fs, clen, conn)), e2),
            RS.W{RS.MField{R.head.new(False{}, x), Nil{}}, Nil{}}),
          RS.num(Bytes.to_list(cd)), code, u32.eq(RS.num(Bytes.to_list(cd)), code, heq)),
        Equal.trans(RS.W,
          RS.walk(e, List.append(&2, U32, FLSl(X.rall(fs, clen, conn)), e2), RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}),
          RS.walk(e, List.append(&2, U32, FLSl(fs), List.append(&2, U32, FLSl(cf), e2)),
            RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}),
          RS.W{RS.MDone{R.Resp{code, False{}, closing, b}, Nil{}}, Nil{}},
          Equal.cong(List<&2, U32>, RS.W, l => RS.walk(e, l, RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}),
            List.append(&2, U32, FLSl(X.rall(fs, clen, conn)), e2),
            List.append(&2, U32, FLSl(fs), List.append(&2, U32, FLSl(cf), e2)),
            Equal.trans(List<&2, U32>, List.append(&2, U32, FLSl(X.rall(fs, clen, conn)), e2),
              List.append(&2, U32, List.append(&2, U32, FLSl(fs), FLSl(cf)), e2),
              List.append(&2, U32, FLSl(fs), List.append(&2, U32, FLSl(cf), e2)),
              Equal.cong(List<&2, U32>, List<&2, U32>, l => List.append(&2, U32, l, e2), FLSl(X.rall(fs, clen, conn)),
                List.append(&2, U32, FLSl(fs), FLSl(cf)), fls.app(fs, cf)),
              app.assoc(U32, FLSl(fs), FLSl(cf), e2))),
          Equal.trans(RS.W,
            RS.walk(e, List.append(&2, U32, FLSl(fs), List.append(&2, U32, FLSl(cf), e2)),
              RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}),
            RS.walk(e, List.append(&2, U32, FLSl(cf), e2), RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}),
            RS.W{RS.MDone{R.Resp{code, False{}, closing, b}, Nil{}}, Nil{}},
            rfields.walk(fs, List.append(&2, U32, FLSl(cf), e2), R.head.new(False{}, code), e, Nil{}, hfs),
            rtail(clen, head, code, closing, v10, bl, body, {==}, not.true(U32.is_lt(code, 200), hlt0),
              not.true(U32.is_eq(code, 101), h1010), hl))))))

def rmain.split(+cd: Bytes(), +why: Bytes(), +fs: List<&2, X.Field>, +clen: Bytes(), +head: Bool, +code: U32, +body: Bytes(),
  +closing: Bool, +v10: Bool,
  hh: {X.rok.code(cd, code) == True{} : Bool} & {X.rok.all(RS.TVal{}, why) == True{} : Bool} &
    {X.rok.fields(fs) == True{} : Bool} & {X.rok.len(head, X.rbodyless(head, code), clen, body) == True{} : Bool}) ->
  {RS.walk(X.rask(head), Bytes.to_list(X.rser(X.Rsp{cd, why, fs, clen, body, X.rbodyless(head, code)}, X.conn.val(closing, v10))),
    RS.W{RS.MStatus{Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), X.rbodyless(head, code), "", body)}, Nil{}}, Nil{}} : RS.W}:
  (hk, r1) = hh
  (aw, r2) = r1
  (hfs, hl) = r2
  rmain.at(cd, why, fs, clen, head, code, body, closing, v10,
    split5(X.rok.all(RS.TDig{}, cd), RS.code.whole(Bytes.to_list(cd)), U32.is_eq(RS.num(Bytes.to_list(cd)), code),
      Bool.not(U32.is_lt(code, 200)), Bool.not(U32.is_eq(code, 101)), hk), aw, hfs, hl)

def rmain(+cd: Bytes(), +why: Bytes(), +fs: List<&2, X.Field>, +clen: Bytes(), +head: Bool, +code: U32, +body: Bytes(),
  +closing: Bool, +v10: Bool,
  hv: {X.rvalid(head, code, X.Rsp{cd, why, fs, clen, body, X.rbodyless(head, code)}) == True{} : Bool}) ->
  {RS.walk(X.rask(head), Bytes.to_list(X.rser(X.Rsp{cd, why, fs, clen, body, X.rbodyless(head, code)}, X.conn.val(closing, v10))),
    RS.W{RS.MStatus{Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), X.rbodyless(head, code), "", body)}, Nil{}}, Nil{}} : RS.W}:
  rmain.split(cd, why, fs, clen, head, code, body, closing, v10,
    split4(X.rok.code(cd, code), X.rok.all(RS.TVal{}, why), X.rok.fields(fs), X.rok.len(head, X.rbodyless(head, code), clen, body), hv))

# The law
# -------

def rr.valid(+cd: Bytes(), +why: Bytes(), +fs: List<&2, X.Field>, +hlen: Bytes(), +head: Bool, +code: U32, +body: Bytes(),
  +closing: Bool, +v10: Bool,
  hv: {X.rvalid(head, code, X.rsp.fin(head, code, X.RHead{cd, why, fs, hlen}, body)) == True{} : Bool}) ->
  {RS.response(X.rask(head), Bytes.to_list(X.reply(Some{X.rsp.fin(head, code, X.RHead{cd, why, fs, hlen}, body)}, head, closing, v10))) ==
    Laws.rlook(Some{X.rsp.fin(head, code, X.RHead{cd, why, fs, hlen}, body)}, head, code, body, closing) : R.Look}:
  +clen = X.rclen(head, X.rbodyless(head, code), hlen, body)
  Equal.cong(RS.W, R.Look, w => RS.finish(X.rask(head), w),
    RS.walk(X.rask(head), Bytes.to_list(X.rser(X.Rsp{cd, why, fs, clen, body, X.rbodyless(head, code)}, X.conn.val(closing, v10))),
      RS.W{RS.MStatus{Nil{}}, Nil{}}),
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), X.rbodyless(head, code), "", body)}, Nil{}}, Nil{}},
    rmain(cd, why, fs, clen, head, code, body, closing, v10, hv))

def rr.h(h: X.RHead, +head: Bool, +code: U32, +body: Bytes(), +closing: Bool, +v10: Bool,
  hv: {X.rvalid(head, code, X.rsp.fin(head, code, h, body)) == True{} : Bool}) ->
  {RS.response(X.rask(head), Bytes.to_list(X.reply(Some{X.rsp.fin(head, code, h, body)}, head, closing, v10))) ==
    Laws.rlook(Some{X.rsp.fin(head, code, h, body)}, head, code, body, closing) : R.Look}:
  match h:
    case X.RHead{+cd, +why, +fs, +hlen}:
      rr.valid(cd, why, fs, hlen, head, code, body, closing, v10, hv)

def rr.pick(b: Bool, +head: Bool, +code: U32, +h: X.RHead, +body: Bytes(), +closing: Bool, +v10: Bool,
  e: {X.rvalid(head, code, X.rsp.fin(head, code, h, body)) == b : Bool}) ->
  {RS.response(X.rask(head), Bytes.to_list(X.reply(Bool.pick(Maybe<&2, X.Rsp>, b, Some{X.rsp.fin(head, code, h, body)}, None{}),
    head, closing, v10))) ==
    Laws.rlook(Bool.pick(Maybe<&2, X.Rsp>, b, Some{X.rsp.fin(head, code, h, body)}, None{}), head, code, body, closing) : R.Look}:
  match b:
    case True{}:
      rr.h(h, head, code, body, closing, v10, e)
    case False{}:
      r502(head, closing, v10, code, body)

def rr.at(+head: Bool, +code: U32, mh: Maybe<&2, X.RHead>, +body: Bytes(), +closing: Bool, +v10: Bool) ->
  {RS.response(X.rask(head), Bytes.to_list(X.reply(X.rsp.at(head, code, mh, body), head, closing, v10))) ==
    Laws.rlook(X.rsp.at(head, code, mh, body), head, code, body, closing) : R.Look}:
  match mh:
    case Some{+h}:
      rr.pick(X.rvalid(head, code, X.rsp.fin(head, code, h, body)), head, code, h, body, closing, v10, {==})
    case None{}:
      r502(head, closing, v10, code, body)

def Laws.rsp_reframed(via, head, k, code, got, body, closing, v10):
  rr.at(head, code, X.rhead.lines(via, X.rlines(k, got)), body, closing, v10)
