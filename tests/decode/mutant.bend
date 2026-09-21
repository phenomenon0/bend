# The certificate against a liar. The decoder's first step in the demo (seed
# 35, rollout 0, from `{`, K = 4) is taken honestly, and then each field of its
# certificate is forged in one way. Each row names the property that has to
# break and the verdict the checker gives, which is the first failure found.
#
# Two rows are the reason the check has two halves:
#
#   skip    the 2nd..5th best. Every entry is genuine and in order, so the
#           chosen half alone passes it; the frontier count catches it (slack).
#   swap    an illegal token, with its true logit, in place of the best. The
#           count at or above the last kept entry still comes out to 4, so the
#           frontier half alone passes it; the chosen half catches it (illegal).
import Base
import ../../power/grammar.bend as Gr
import ../../power/heap.bend as Heap
import ../../power/decode.bend as D
import ../../demos/decode/main.bend as M

def s0() -> Gr.St:
  Gr.step(Gr.start(), 123)

def ls0() -> List<&2, U32>:
  M.model(M.vocab(), 35, 0, 0, 0)

def at0() -> D.At:
  D.At{35, 0, 0}

def dead() -> D.Step:
  D.Step{0, Gr.dead(), D.Cert{[], 0}}

def got(r: Result<&2, &2, D.Bad, D.Step>) -> D.Step:
  match r:
    case Fail{e}:
      dead()
    case Done{st}:
      st

def honest(k: U32) -> D.Step:
  got(D.decode_step(M.vocab(), s0(), ls0(), k, at0()))

def kept(st: D.Step) -> List<&2, Heap.Entry>:
  match st:
    case D.Step{t, n, c}:
      match c:
        case D.Cert{xs, r}:
          xs

# element i of a kept list, or 0@0
def ent.if(x: Heap.Entry, m: Heap.Entry, hit: Bool) -> Heap.Entry:
  match hit:
    case True{}:
      x
    case False{}:
      m

def ent.go(xs: List<&2, Heap.Entry>, +i: U32, +j: U32, m: Heap.Entry) -> Heap.Entry:
  match xs:
    case Nil{}:
      m
    case Con{x, rest}:
      ent.go(rest, i, U32.inc(j), ent.if(x, m, U32.is_eq(i, j)))

def e(i: U32) -> Heap.Entry:
  ent.go(kept(honest(6)), i, 0, Heap.Entry{0, 0})

def w.of(x: Heap.Entry) -> U32:
  match x:
    case Heap.Entry{w, id}:
      w

def id.of(x: Heap.Entry) -> U32:
  match x:
    case Heap.Entry{w, id}:
      id

def or0(m: Maybe<&2, U32>) -> U32:
  match m:
    case None{}:
      0
    case Some{w}:
      w

def logit(id: U32) -> U32:
  or0(D.nth(ls0(), id))

def with.kept(st: D.Step, xs: List<&2, Heap.Entry>) -> D.Step:
  match st:
    case D.Step{t, n, c}:
      match c:
        case D.Cert{ys, r}:
          D.Step{t, n, D.Cert{xs, r}}

def with.draw(st: D.Step, d: U32) -> D.Step:
  match st:
    case D.Step{t, n, c}:
      match c:
        case D.Cert{ys, r}:
          D.Step{t, n, D.Cert{ys, U32.add(r, d)}}

def with.tok(st: D.Step, t: U32) -> D.Step:
  match st:
    case D.Step{x, n, c}:
      D.Step{t, n, c}

def with.st(st: D.Step, n: Gr.St) -> D.Step:
  match st:
    case D.Step{t, x, c}:
      D.Step{t, n, c}

# each half on its own, to show the liar it lets through
def ch.v(c: D.Ch) -> String:
  match c:
    case D.Ch{v, n, last}:
      D.show.vd(v)

def fr.n(f: D.Fr) -> String:
  match f:
    case D.Fr{v, n}:
      U32.show(n)

def chosen(xs: List<&2, Heap.Entry>) -> String:
  ch.v(D.ch.go(5n, xs, M.vocab(), ls0(), s0(), D.Ch{D.Ok{}, 0, None{}}))

def count(fl: Heap.Entry) -> String:
  fr.n(D.fr.go(M.vocab(), ls0(), s0(), 0, Some{fl}, D.Fr{D.Ok{}, 0}))

def row(name: String, st: D.Step) -> String:
  name ++ " " ++ D.show.vd(D.check(M.vocab(), s0(), ls0(), 4, at0(), st))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("k4 " ++ D.show.kept(kept(honest(4))))
    IO.print("k6 " ++ D.show.kept(kept(honest(6))))
    IO.print(row("honest", honest(4)))
    IO.print(row("order", with.kept(honest(4), [e(1), e(0), e(2), e(3)])))
    IO.print(row("dup", with.kept(honest(4), [e(0), e(0), e(1), e(2)])))
    IO.print(row("skip", with.kept(honest(4), [e(1), e(2), e(3), e(4)])))
    IO.print(row("short", with.kept(honest(4), [e(0), e(1), e(2)])))
    IO.print(row("extra", with.kept(honest(4), [e(0), e(1), e(2), e(3), e(4)])))
    IO.print(row("inflate", with.kept(honest(4), [Heap.Entry{U32.inc(w.of(e(0))), id.of(e(0))}, e(1), e(2), e(3)])))
    IO.print(row("range", with.kept(honest(4), [Heap.Entry{w.of(e(0)), 99}, e(1), e(2), e(3)])))
    IO.print(row("swap", with.kept(honest(4), [Heap.Entry{logit(0), 0}, e(1), e(2), e(3)])))
    IO.print("skip, chosen half alone: " ++ chosen([e(1), e(2), e(3), e(4)]))
    IO.print("swap, frontier count at its last entry: " ++ count(e(3)) ++ " of 4")
    IO.print(row("draw", with.draw(honest(4), 1)))
    IO.print(row("tok", with.tok(honest(4), id.of(e(1)))))
    IO.print(row("state", with.st(honest(4), Gr.start())))
#|k4 15634743@6 15468670@7 11573860@13 11392035@1
#|k6 15634743@6 15468670@7 11573860@13 11392035@1 10175699@16 6653514@12
#|honest ok
#|order order
#|dup order
#|skip slack
#|short slack
#|extra over
#|inflate value
#|range range
#|swap illegal
#|skip, chosen half alone: ok
#|swap, frontier count at its last entry: 4 of 4
#|draw draw
#|tok draw
#|state state
