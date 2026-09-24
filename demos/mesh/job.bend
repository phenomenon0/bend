# A leaf of bend-mesh: what a worker computes, as words, and the join that
# puts two leaves back together. The worker and the coordinator both import
# this file, so "leaf i" means one thing on both ends of the wire.
#
# A leaf is a range of one computation from demos/monoids, run by the same
# fork tree the single-process program runs, summarized by the same monoid:
#
#   exact  the Kulisch sum of kulisch.bend's draws(seed, i), i in [lo, lo+n):
#          ten U32 limbs, joined by a 320-bit add
#   option option.bend's Monte Carlo call price over paths [lo, lo+n) of seed
#          a: two 96-bit fixed-point sums, joined by integer adds
#   lost   lostupdate.bend's census of schedules of rank [lo, lo+n), for m
#          increments a thread: sixteen U32 buckets, joined by adding them
#
# Because each join is associative and a leaf is a pure function of its
# range, the coordinator's answer is the single-process answer bit for bit,
# whichever machine ran which range, however many times.
#
# The wire: a request body is "job a lo n d" (a: the seed or m; d: the
# worker's own fork depth), a response body the summary's words, in ASCII.
import Base
import ../monoids/kulisch.bend as K
import ../monoids/lostupdate.bend as L
import ./option.bend as O

type Job is Data:
  Job{kind: U32, a: U32, lo: U32, n: U32, d: U32}

# -- words ----------------------------------------------------------------------------

def words.show.tail(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, t}:
      " " ++ U32.show(x) ++ words.show.tail(t)

def words.show(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, t}:
      U32.show(x) ++ words.show.tail(t)

def words.of(xs: List<&2, String>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Maybe.default(&2, U32, U32.read(x), 0) <> words.of(t)

# the words of a body, split on spaces
def words(+s: String) -> List<&2, U32>:
  words.of(String.split(String.trim(s), ' '))

def List.head.or(xs: List<&2, U32>, d: U32) -> U32:
  match xs:
    case Nil{}:
      d
    case Con{x, t}:
      x

def List.tail.of(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      t

def at(k: Nat, xs: List<&2, U32>) -> U32:
  match k:
    case 0n:
      List.head.or(xs, 0)
    case 1n++q:
      at(q, List.tail.of(xs))

# -- the summaries as words, and back --------------------------------------------------

def acc.words(a: K.Acc) -> List<&2, U32>:
  match a:
    case K.Acc{l0, l1, l2, l3, l4, l5, l6, l7, l8, l9}:
      [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9]

def acc.of(+xs: List<&2, U32>) -> K.Acc:
  K.Acc{at(0n, xs), at(1n, xs), at(2n, xs), at(3n, xs), at(4n, xs), at(5n, xs), at(6n, xs),
    at(7n, xs), at(8n, xs), at(9n, xs)}

def hist.words(h: L.Hist) -> List<&2, U32>:
  match h:
    case L.Hist{h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16}:
      [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]

def hist.of(+xs: List<&2, U32>) -> L.Hist:
  L.Hist{at(0n, xs), at(1n, xs), at(2n, xs), at(3n, xs), at(4n, xs), at(5n, xs), at(6n, xs),
    at(7n, xs), at(8n, xs), at(9n, xs), at(10n, xs), at(11n, xs), at(12n, xs), at(13n, xs),
    at(14n, xs), at(15n, xs)}

# -- jobs -------------------------------------------------------------------------------

def EXACT() -> U32:
  1

def LOST() -> U32:
  2

def opt.words(o: O.Opt) -> List<&2, U32>:
  match o:
    case O.Opt{a0, a1, a2, b0, b1, b2}:
      [a0, a1, a2, b0, b1, b2]

def opt.of(+xs: List<&2, U32>) -> O.Opt:
  O.Opt{at(0n, xs), at(1n, xs), at(2n, xs), at(3n, xs), at(4n, xs), at(5n, xs)}

def hex8(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, t}:
      " " ++ String.drop(K.hex(x), 2n) ++ hex8(t)

def kind.of(+s: String) -> U32:
  Bool.pick(U32, String.eq(s, "exact"), EXACT(), Bool.pick(U32, String.eq(s, "lost"), LOST(),
    Bool.pick(U32, String.eq(s, "option"), 3, 0)))

def kind.name(+k: U32) -> String:
  Bool.pick(String, U32.is_eq(k, EXACT()), "exact", Bool.pick(String, U32.is_eq(k, LOST()), "lost",
    Bool.pick(String, U32.is_eq(k, 3), "option", "?")))

def job.of(+kw: String, +ws: List<&2, U32>) -> Job:
  Job{kind.of(kw), at(0n, ws), at(1n, ws), at(2n, ws), at(3n, ws)}

def parse.parts(parts: List<&2, String>) -> Job:
  match parts:
    case Nil{}:
      Job{0, 0, 0, 0, 0}
    case Con{kw, rest}:
      job.of(kw, words.of(rest))

# a request body: "job a lo n d"
def parse(+s: String) -> Job:
  parse.parts(String.split(String.trim(s), ' '))

def body(+j: Job) -> String:
  match j:
    case Job{k, a, lo, n, d}:
      kind.name(k) ++ " " ++ U32.show(a) ++ " " ++ U32.show(lo) ++ " " ++ U32.show(n) ++ " " ++ U32.show(d)

def run.k(k: U32, +a: U32, +lo: U32, +n: U32, +d: U32) -> List<&2, U32>:
  match k:
    case 1:
      acc.words(K.exact(U32.to_nat(d), a, lo, n))
    case 2:
      hist.words(L.tree(U32.to_nat(d), a, lo, n))
    case 3:
      opt.words(O.tree(U32.to_nat(d), a, lo, n))
    case _:
      Nil{}

# run one leaf: its summary's words (none for a job this worker does not know)
def run(j: Job) -> List<&2, U32>:
  match j:
    case Job{k, +a, +lo, +n, +d}:
      run.k(k, a, lo, n, d)

# the join, as words: the program's own monoid
def join(k: U32, xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 1:
      acc.words(K.join(acc.of(xs), acc.of(ys)))
    case 3:
      opt.words(O.join(opt.of(xs), opt.of(ys)))
    case _:
      hist.words(L.join(hist.of(xs), hist.of(ys)))

def zero(k: U32) -> List<&2, U32>:
  match k:
    case 1:
      acc.words(K.zero())
    case 3:
      [0, 0, 0, 0, 0, 0]
    case _:
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

# the final answer, as the single-process programs print it
def render(k: U32, +a: U32, +n: U32, +xs: List<&2, U32>) -> String:
  match k:
    case 1:
      "exact " ++ K.hex(K.round(acc.of(xs)))
    case 3:
      "option paths=" ++ U32.show(n) ++ " acc=" ++ String.drop(hex8(xs), 1n) ++ " " ++ O.show(opt.of(xs), n)
    case _:
      L.show(hist.of(xs), a)

# how many items a job covers: draws for exact (given), C(4m, 2m) schedules for lost
def total(k: U32, +a: U32, +n: U32) -> U32:
  match k:
    case 2:
      L.binom(U32.shln(a, 2n), U32.shln(a, 1n))
    case _:
      n
