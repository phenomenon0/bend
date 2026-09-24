# Every schedule of a lost update, counted exactly.
#
# Two threads each run `counter++` n times, and each increment is two steps:
# LOAD r = x, then STORE x = r + 1. A schedule is the order the 4n steps
# interleave in: a 4n-bit word with 2n ones (bit i set: thread A takes step
# i). For n = 8 that is exactly 32 bits and C(32, 16) = 601,080,390 schedules,
# and this program runs every one of them and histograms the final x.
#
# The concurrency deep dive says a racing counter can lose "a substantial
# fraction of your increments -- or all of them". The census says otherwise.
# The final x is never below 2, and exactly 8 schedules reach 2, at every n
# from 3 to 8 (the fixture below and lostupdate_big.bend). The correct 2n is
# reached by exactly C(2n, n) schedules.
#
# Schedules are numbered in colex order, so a leaf needs only its first rank.
# It unranks that through the combinatorial number system, then walks its
# range with Gosper's hack (the next word with the same popcount), simulating
# each schedule in registers. The histogram is added up the tree; addition is
# associative, so the split does not show. lostupdate_gen.py is the oracle: a
# dynamic program over the machine state, not an enumeration.
import Base

type Hist is Data:
  Hist{h1: U32, h2: U32, h3: U32, h4: U32, h5: U32, h6: U32, h7: U32, h8: U32, h9: U32, h10: U32, h11: U32, h12: U32, h13: U32, h14: U32, h15: U32, h16: U32}

# -- words --------------------------------------------------------------------------

def popcount(+x: U32) -> U32:
  +a = U32.sub(x, U32.and(U32.shrn(x, 1n), 1431655765))
  +b = U32.add(U32.and(a, 858993459), U32.and(U32.shrn(a, 2n), 858993459))
  +c = U32.and(U32.add(b, U32.shrn(b, 4n)), 252645135)
  U32.shrn(U32.mul(c, 16843009), 24n)

def ctz(+x: U32) -> U32:
  popcount(U32.sub(U32.and(x, U32.sub(0, x)), 1))

# Gosper's hack: the next larger word with as many ones as v
def next(+v: U32) -> U32:
  +t = U32.or(v, U32.sub(v, 1))
  +u = U32.inc(t)
  U32.or(u, U32.shrn(U32.sub(U32.and(U32.not(t), u), 1), U32.to_nat(U32.inc(ctz(v)))))

# C(c, i), exact: every partial product C(c - i + j, j) is an integer below 2^53
def binom.go(j: Nat, +c: U32, +i: U32, +k: U32, +acc: F64) -> F64:
  match j:
    case 0n:
      acc
    case 1n++q:
      binom.go(q, c, i, U32.inc(k), F64.div(F64.mul(acc,
        U32.to_f64(U32.add(U32.sub(c, i), k))), U32.to_f64(k)))

def binom(+c: U32, +i: U32) -> U32:
  Bool.pick(U32, U32.is_lt(c, i), 0, F64.to_u32(binom.go(U32.to_nat(i), c, i, 1, 1.0d)))

# the schedule of colex rank r among the words of N bits with k ones: from the
# top bit down, set bit p whenever C(p, k) still fits under what is left of r
def unrank(j: Nat, +r: U32, +k: U32, +m: U32) -> U32:
  match j:
    case 0n:
      m
    case 1n++q:
      +p = U32.from_nat(q)
      +c = binom(p, k)
      +take = Bool.and(U32.is_gt(k, 0), U32.is_le(c, r))
      unrank(q, Bool.pick(U32, take, U32.sub(r, c), r), Bool.pick(U32, take, U32.sub(k, 1), k),
        Bool.pick(U32, take, U32.or(m, U32.shln(1, q)), m))

# -- the machine ----------------------------------------------------------------------

# run schedule m for s steps: bit set, thread A moves; an even pc loads, an odd
# pc stores. Branch-free, all in registers.
def run(s: Nat, +m: U32, +x: U32, +ra: U32, +rb: U32, +pa: U32, +pb: U32) -> U32:
  match s:
    case 0n:
      x
    case 1n++q:
      +a = U32.is_eq(U32.and(m, 1), 1)
      +st = U32.is_eq(U32.and(Bool.pick(U32, a, pa, pb), 1), 1)
      run(q, U32.shrn(m, 1n),
        Bool.pick(U32, st, U32.inc(Bool.pick(U32, a, ra, rb)), x),
        Bool.pick(U32, Bool.and(a, Bool.not(st)), x, ra),
        Bool.pick(U32, Bool.and(Bool.not(a), Bool.not(st)), x, rb),
        U32.add(pa, Bool.to_u32(a)), U32.add(pb, Bool.to_u32(Bool.not(a))))

def hit(+x: U32, j: U32) -> U32:
  Bool.to_u32(U32.is_eq(x, j))

# k schedules from m on, one bucket per final x (1..16)
def leaf(k: Nat, +s: Nat, +m: U32, +h1: U32, +h2: U32, +h3: U32, +h4: U32, +h5: U32, +h6: U32, +h7: U32, +h8: U32, +h9: U32, +h10: U32, +h11: U32, +h12: U32, +h13: U32, +h14: U32, +h15: U32, +h16: U32) -> Hist:
  match k:
    case 0n:
      Hist{h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16}
    case 1n++q:
      +x = run(s, m, 0, 0, 0, 0, 0)
      leaf(q, s, next(m),
        U32.add(h1, hit(x, 1)),
        U32.add(h2, hit(x, 2)),
        U32.add(h3, hit(x, 3)),
        U32.add(h4, hit(x, 4)),
        U32.add(h5, hit(x, 5)),
        U32.add(h6, hit(x, 6)),
        U32.add(h7, hit(x, 7)),
        U32.add(h8, hit(x, 8)),
        U32.add(h9, hit(x, 9)),
        U32.add(h10, hit(x, 10)),
        U32.add(h11, hit(x, 11)),
        U32.add(h12, hit(x, 12)),
        U32.add(h13, hit(x, 13)),
        U32.add(h14, hit(x, 14)),
        U32.add(h15, hit(x, 15)),
        U32.add(h16, hit(x, 16)))

def join(a: Hist, b: Hist) -> Hist:
  match a b:
    case Hist{a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16} Hist{b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16}:
      Hist{U32.add(a1, b1), U32.add(a2, b2), U32.add(a3, b3), U32.add(a4, b4), U32.add(a5, b5), U32.add(a6, b6), U32.add(a7, b7), U32.add(a8, b8), U32.add(a9, b9), U32.add(a10, b10), U32.add(a11, b11), U32.add(a12, b12), U32.add(a13, b13), U32.add(a14, b14), U32.add(a15, b15), U32.add(a16, b16)}

# schedules of rank lo .. lo+k-1 (n increments a thread), 2^d leaves
def tree(d: Nat, +n: U32, +lo: U32, +k: U32) -> Hist:
  match d:
    case 0n:
      leaf(U32.to_nat(k), U32.to_nat(U32.shln(n, 2n)),
        unrank(U32.to_nat(U32.shln(n, 2n)), lo, U32.shln(n, 1n), 0),
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
    case 1n++p:
      +h = U32.shr(k)
      a b = tree(p, n, lo, h) tree(p, n, U32.add(lo, h), U32.sub(k, h))
      join(a, b)

def census(d: Nat, +n: U32) -> Hist:
  tree(d, n, 0, binom(U32.shln(n, 2n), U32.shln(n, 1n)))

# -- the report -----------------------------------------------------------------------

def pick(j: U32, h1: U32, h2: U32, h3: U32, h4: U32, h5: U32, h6: U32, h7: U32, h8: U32, h9: U32, h10: U32, h11: U32, h12: U32, h13: U32, h14: U32, h15: U32, h16: U32) -> U32:
  match j:
    case 1:
      h1
    case 2:
      h2
    case 3:
      h3
    case 4:
      h4
    case 5:
      h5
    case 6:
      h6
    case 7:
      h7
    case 8:
      h8
    case 9:
      h9
    case 10:
      h10
    case 11:
      h11
    case 12:
      h12
    case 13:
      h13
    case 14:
      h14
    case 15:
      h15
    case _:
      h16

def get(j: U32, h: Hist) -> U32:
  match h:
    case Hist{h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16}:
      pick(j, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16)

def same(+a: Hist, +b: Hist, j: Nat) -> Bool:
  match j:
    case 0n:
      True{}
    case 1n++q:
      Bool.and(U32.is_eq(get(U32.inc(U32.from_nat(q)), a), get(U32.inc(U32.from_nat(q)), b)), same(a, b, q))

def total(j: Nat, +h: Hist) -> U32:
  match j:
    case 0n:
      0
    case 1n++q:
      U32.add(get(U32.inc(U32.from_nat(q)), h), total(q, h))

# the smallest x with a nonzero count, searching down from 16
def low(j: Nat, +h: Hist, +best: U32) -> U32:
  match j:
    case 0n:
      best
    case 1n++q:
      +x = U32.inc(U32.from_nat(q))
      low(q, h, Bool.pick(U32, U32.is_zero(get(x, h)), best, x))

def bars(j: Nat, +h: Hist, +x: U32) -> String:
  match j:
    case 0n:
      ""
    case 1n++q:
      +c = get(x, h)
      Bool.pick(String, U32.is_zero(c), "", " " ++ U32.show(x) ++ ":" ++ U32.show(c)) ++ bars(q, h, U32.inc(x))

def show(+h: Hist, +n: U32) -> String:
  +lo = low(16n, h, 0)
  "n=" ++ U32.show(n) ++ " schedules=" ++ U32.show(total(16n, h)) ++ " min=" ++ U32.show(lo)
    ++ " x" ++ U32.show(get(lo, h)) ++ " correct=" ++ U32.show(get(U32.shln(n, 1n), h)) ++ " |"
    ++ bars(16n, h, 1)

def report(+n: U32) -> String:
  +h = census(0n, n)
  +ok = Bool.and(same(h, census(5n, n), 16n), same(h, census(11n, n), 16n))
  show(h, n) ++ " | depths 0 5 11: " ++ Bool.pick(String, ok, "same", "DIFFER")

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(report(2))
    IO.print(report(3))
    IO.print(report(4))
    IO.print(report(5))
    IO.print(report(6))
#|n=2 schedules=70 min=2 x32 correct=6 | 2:32 3:32 4:6 | depths 0 5 11: same
#|n=3 schedules=924 min=2 x8 correct=20 | 2:8 3:300 4:416 5:180 6:20 | depths 0 5 11: same
#|n=4 schedules=12870 min=2 x8 correct=70 | 2:8 3:192 4:3056 5:5184 6:3464 7:896 8:70 | depths 0 5 11: same
#|n=5 schedules=184756 min=2 x8 correct=252 | 2:8 3:256 4:3352 5:33032 6:64072 7:56216 8:23368 9:4200 10:252 | depths 0 5 11: same
#|n=6 schedules=2704156 min=2 x8 correct=924 | 2:8 3:320 4:5504 5:51968 6:374056 7:793952 8:841552 9:477216 10:139648 11:19008 12:924 | depths 0 5 11: same
