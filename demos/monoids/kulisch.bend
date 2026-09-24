# The sum that does not care: an exact F32 sum whose bits do not depend on the
# order, the split, the thread count or the lane.
#
# Float addition is not associative -- (1e20 + 1) - 1e20 is 0, 1 + (1e20 -
# 1e20) is 1 -- so a parallel reduction that splits differently rounds
# differently, and a fork tree that re-balances across machines changes the
# answer. Kahan and Neumaier shrink the error but keep the order dependence;
# fsum is exact but a sequential algorithm. The Kulisch accumulator (1970s,
# "the exact dot product") removes the question instead: every finite F32 is an
# integer multiple of 2^-149, and the largest is below 2^128, so a fixed-point
# integer 277 bits wide holds any one of them exactly and, with 32 bits of
# headroom, the exact sum of up to 2^32 of them. Integer addition IS
# associative. The fork tree adds exactly, and one correct rounding at the
# root gives the unique nearest F32 to the true sum -- the same bits however
# the tree was cut.
#
# The accumulator: ten U32 limbs, 320 bits of two's complement, limb j worth
# 2^(32j - 149). An F32 with biased exponent E and 24-bit significand m is
# m * 2^(max(E,1) - 150): its bits start at offset o = max(E,1) - 1 (0..253),
# so it lands in limb o/32 and at most the one above -- two words and a carry
# chain. A negative value adds its two's complement: every limb xor'd with
# all-ones, carry in 1. Inputs are finite: an inf or NaN would be read as a
# large finite value (E = 255 is not special-cased), and none is ever drawn.
#
# The data is a pure function of the index, built to break naive summation:
# giants near 2^80 planted in +/- pairs that cancel exactly, over a sea of
# small values and subnormals. A naive sum loses the sea to the giants'
# rounding and returns garbage that changes with the tree shape; the exact sum
# is the sea, correctly rounded. kulisch_gen.py is the oracle: it sums with
# Python's Fraction and certifies the printed bits are the nearest F32 (ties to
# even) without rounding anything itself.
import Base
import ../../power/rng.bend as Rng

# -- the data -------------------------------------------------------------------

def mant(+x: U32) -> U32:
  U32.or(U32.and(x, 8388607), U32.shln(Bool.to_u32(U32.is_ne(U32.and(x, 2139095040), 0)), 23n))

def f32bits(s: U32, e: U32, f: U32) -> U32:
  U32.or(U32.or(U32.shln(s, 31n), U32.shln(e, 23n)), U32.and(f, 8388607))

# element j of the pair family: a giant, 2^66 .. 2^81
def giant(+seed: U32, j: U32) -> U32:
  +r = Rng.u32(seed, 1, j)
  f32bits(0, U32.add(193, U32.and(U32.shrn(r, 23n), 15)), r)

# the sea: 2^-50 .. 2^-12 with a random sign; every 97th one subnormal
def small(+seed: U32, +i: U32) -> U32:
  +r = Rng.u32(seed, 2, i)
  +sub = U32.is_eq(U32.mod(i, 97), 0)
  f32bits(U32.shrn(r, 31n),
    Bool.pick(U32, sub, 0, U32.add(77, U32.mod(U32.and(U32.shrn(r, 23n), 255), 39))), r)

def draw.pair(k: U32, +seed: U32, +i: U32) -> U32:
  match k:
    case 0:
      giant(seed, i)
    case 512:
      U32.xor(giant(seed, U32.sub(i, 512)), 2147483648) # the same giant, negated
    case _:
      small(seed, i)

# element i as F32 bits
def draw(+seed: U32, +i: U32) -> U32:
  draw.pair(U32.and(i, 1023), seed, i)

# -- the accumulator ----------------------------------------------------------------

type Acc is Data:
  Acc{l0: U32, l1: U32, l2: U32, l3: U32, l4: U32, l5: U32, l6: U32, l7: U32, l8: U32, l9: U32}

def zero() -> Acc:
  Acc{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}

# the carry out of a + b + c (c is 0 or 1)
def carry(+a: U32, +b: U32, +c: U32) -> U32:
  +s = U32.add(a, b)
  U32.or(Bool.to_u32(U32.is_lt(s, a)), Bool.to_u32(U32.is_lt(U32.add(s, c), s)))

# what limb j receives of a value whose low word goes to limb k
def put(+k: U32, j: U32, +lo: U32, +hi: U32) -> U32:
  +j2 = j
  U32.or(U32.mul(Bool.to_u32(U32.is_eq(k, j2)), lo),
    U32.mul(Bool.to_u32(U32.is_eq(U32.inc(k), j2)), hi))

# n draws from i, added exactly into ten limbs carried as ten words (no record
# is built per element); the only branch is the loop's
def leaf(n: Nat, +seed: U32, +i: U32, +l0: U32, +l1: U32, +l2: U32, +l3: U32,
  +l4: U32, +l5: U32, +l6: U32, +l7: U32, +l8: U32, +l9: U32) -> Acc:
  match n:
    case 0n:
      Acc{l0, l1, l2, l3, l4, l5, l6, l7, l8, l9}
    case 1n++q:
      +x = draw(seed, i)
      +sm = U32.sub(0, U32.shrn(x, 31n))
      +o = U32.sub(U32.max(U32.and(U32.shrn(x, 23n), 255), 1), 1)
      +k = U32.shrn(o, 5n)
      +m = mant(x)
      +lo = U32.shln(m, U32.to_nat(U32.and(o, 31)))
      +hi = U32.shrn(m, U32.to_nat(U32.sub(32, U32.and(o, 31))))
      +c = U32.and(sm, 1)
      +o0 = U32.xor(put(k, 0, lo, hi), sm)
      +c0 = carry(l0, o0, c)
      +o1 = U32.xor(put(k, 1, lo, hi), sm)
      +c1 = carry(l1, o1, c0)
      +o2 = U32.xor(put(k, 2, lo, hi), sm)
      +c2 = carry(l2, o2, c1)
      +o3 = U32.xor(put(k, 3, lo, hi), sm)
      +c3 = carry(l3, o3, c2)
      +o4 = U32.xor(put(k, 4, lo, hi), sm)
      +c4 = carry(l4, o4, c3)
      +o5 = U32.xor(put(k, 5, lo, hi), sm)
      +c5 = carry(l5, o5, c4)
      +o6 = U32.xor(put(k, 6, lo, hi), sm)
      +c6 = carry(l6, o6, c5)
      +o7 = U32.xor(put(k, 7, lo, hi), sm)
      +c7 = carry(l7, o7, c6)
      +o8 = U32.xor(put(k, 8, lo, hi), sm)
      +c8 = carry(l8, o8, c7)
      +o9 = U32.xor(put(k, 9, lo, hi), sm)
      leaf(q, seed, U32.inc(i),
        U32.add(U32.add(l0, o0), c), U32.add(U32.add(l1, o1), c0),
        U32.add(U32.add(l2, o2), c1), U32.add(U32.add(l3, o3), c2),
        U32.add(U32.add(l4, o4), c3), U32.add(U32.add(l5, o5), c4),
        U32.add(U32.add(l6, o6), c5), U32.add(U32.add(l7, o7), c6),
        U32.add(U32.add(l8, o8), c7), U32.add(U32.add(l9, o9), c8))

# the join: a 320-bit add, exact, so the tree's shape cannot show
def join(a: Acc, b: Acc) -> Acc:
  match a b:
    case Acc{+a0, +a1, +a2, +a3, +a4, +a5, +a6, +a7, +a8, a9} Acc{+b0, +b1, +b2, +b3, +b4, +b5, +b6, +b7, +b8, b9}:
      +c0 = carry(a0, b0, 0)
      +c1 = carry(a1, b1, c0)
      +c2 = carry(a2, b2, c1)
      +c3 = carry(a3, b3, c2)
      +c4 = carry(a4, b4, c3)
      +c5 = carry(a5, b5, c4)
      +c6 = carry(a6, b6, c5)
      +c7 = carry(a7, b7, c6)
      +c8 = carry(a8, b8, c7)
      Acc{U32.add(a0, b0), U32.add(U32.add(a1, b1), c0), U32.add(U32.add(a2, b2), c1),
        U32.add(U32.add(a3, b3), c2), U32.add(U32.add(a4, b4), c3),
        U32.add(U32.add(a5, b5), c4), U32.add(U32.add(a6, b6), c5),
        U32.add(U32.add(a7, b7), c6), U32.add(U32.add(a8, b8), c7),
        U32.add(U32.add(a9, b9), c8)}

def exact(d: Nat, +seed: U32, +lo: U32, +n: U32) -> Acc:
  match d:
    case 0n:
      leaf(U32.to_nat(n), seed, lo, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
    case 1n++p:
      +h = U32.shr(n)
      a b = exact(p, seed, lo, h) exact(p, seed, U32.add(lo, h), U32.sub(n, h))
      join(a, b)

# -- the one rounding ---------------------------------------------------------------

def limb(j: U32, l0: U32, l1: U32, l2: U32, l3: U32, l4: U32, l5: U32, l6: U32,
  l7: U32, l8: U32, l9: U32) -> U32:
  match j:
    case 0:
      l0
    case 1:
      l1
    case 2:
      l2
    case 3:
      l3
    case 4:
      l4
    case 5:
      l5
    case 6:
      l6
    case 7:
      l7
    case 8:
      l8
    case 9:
      l9
    case _:
      0

def at(+a: Acc, j: U32) -> U32:
  match a:
    case Acc{l0, l1, l2, l3, l4, l5, l6, l7, l8, l9}:
      limb(j, l0, l1, l2, l3, l4, l5, l6, l7, l8, l9)

# -a, for the one negative total: once, here, never per element
def negate(a: Acc) -> Acc:
  match a:
    case Acc{l0, l1, l2, l3, l4, l5, l6, l7, l8, l9}:
      join(Acc{1, 0, 0, 0, 0, 0, 0, 0, 0, 0}, Acc{U32.not(l0), U32.not(l1),
        U32.not(l2), U32.not(l3), U32.not(l4), U32.not(l5), U32.not(l6),
        U32.not(l7), U32.not(l8), U32.not(l9)})

def ge(+x: U32, +y: U32) -> U32:
  Bool.to_u32(U32.is_ge(x, y))

def nz(+x: U32) -> U32:
  Bool.to_u32(U32.is_ne(x, 0))

# the index of the top set bit (0 for 0 and 1): sum over k of [x >= 2^k]
def fls(k: Nat, +x: U32, +b: U32) -> U32:
  match k:
    case 0n:
      b
    case 1n++q:
      fls(q, x, U32.add(b, ge(x, U32.shln(2, q))))

# the top set bit of the whole 320 bits
def top(a: Acc) -> U32:
  match a:
    case Acc{+l0, +l1, +l2, +l3, +l4, +l5, +l6, +l7, +l8, +l9}:
      +s9 = l9
      +s8 = U32.or(l8, s9)
      +s7 = U32.or(l7, s8)
      +s6 = U32.or(l6, s7)
      +s5 = U32.or(l5, s6)
      +s4 = U32.or(l4, s5)
      +s3 = U32.or(l3, s4)
      +s2 = U32.or(l2, s3)
      +s1 = U32.or(l1, s2)
      +t = U32.add(U32.add(U32.add(nz(s1), nz(s2)), U32.add(nz(s3), nz(s4))),
        U32.add(U32.add(U32.add(nz(s5), nz(s6)), U32.add(nz(s7), nz(s8))), nz(s9)))
      U32.add(U32.shln(t, 5n), fls(31n, limb(t, l0, l1, l2, l3, l4, l5, l6, l7, l8, l9), 0))

# the 32 bits from bit p up
def window(+a: Acc, +p: U32) -> U32:
  +k = U32.shrn(p, 5n)
  +r = U32.and(p, 31)
  U32.or(U32.shrn(at(a, k), U32.to_nat(r)), U32.shln(at(a, U32.inc(k)), U32.to_nat(U32.sub(32, r))))

# 1 if any bit below bit p is set
def sticky(j: Nat, +a: Acc, +p: U32, +acc: U32) -> U32:
  match j:
    case 0n:
      nz(acc)
    case 1n++q:
      +w = at(a, U32.from_nat(q))
      +k = U32.shrn(p, 5n)
      +part = U32.and(w, U32.sub(U32.shln(1, U32.to_nat(U32.and(p, 31))), 1))
      +mine = Bool.pick(U32, U32.is_lt(U32.from_nat(q), k), w,
        Bool.pick(U32, U32.is_eq(U32.from_nat(q), k), part, 0))
      sticky(q, a, p, U32.or(acc, mine))

# round-to-nearest-even of a magnitude whose top bit is h >= 24
def wide(+m: Acc, +h: U32) -> U32:
  +s = U32.sub(h, 23)
  +sig = U32.and(window(m, s), 16777215)
  +g = U32.and(window(m, U32.sub(s, 1)), 1)
  +up = U32.and(g, U32.or(sticky(10n, m, U32.sub(s, 1), 0), U32.and(sig, 1)))
  # (E-1) << 23 plus the 24-bit significand: its hidden bit makes E, and a
  # round-up that carries out of the significand bumps E for free
  U32.min(U32.add(U32.add(U32.shln(s, 23n), sig), up), 2139095040)

def mag(+m: Acc) -> U32:
  +h = top(m)
  # under 2^24 the integer IS the bit pattern: subnormal below 2^23, E = 1 above
  Bool.pick(U32, U32.is_lt(h, 24), at(m, 0), wide(m, h))

# the correctly rounded F32 of the exact sum, as bits
def round(+a: Acc) -> U32:
  +neg = U32.shrn(at(a, 9), 31n)
  U32.or(U32.shln(neg, 31n), mag(Bool.pick(Acc, U32.is_eq(neg, 1), negate(a), a)))

# -- the naive sums, for contrast ------------------------------------------------------

# 2^(2^j) (or its inverse), by squaring: every step exact
def fac(j: Nat, +x: F32) -> F32:
  match j:
    case 0n:
      x
    case 1n++q:
      fac(q, F32.mul(x, x))

# 2^k for -149 <= k <= 127, a product of exact powers: never rounds
def pow2(j: Nat, +k: U32, +neg: Bool, +acc: F32) -> F32:
  match j:
    case 0n:
      acc
    case 1n++q:
      +f = fac(q, Bool.pick(F32, neg, 0.5, 2.0))
      +hit = U32.is_eq(U32.and(U32.shrn(k, q), 1), 1)
      pow2(q, k, neg, Bool.pick(F32, hit, F32.mul(acc, f), acc))

# the F32 whose bits are x: m * 2^(o - 149), both factors exact
def value(+x: U32) -> F32:
  +o = U32.sub(U32.max(U32.and(U32.shrn(x, 23n), 255), 1), 1)
  +neg = U32.is_lt(o, 149)
  +k = Bool.pick(U32, neg, U32.sub(149, o), U32.sub(o, 149))
  +v = F32.mul(U32.to_f32(mant(x)), pow2(8n, k, neg, 1.0))
  Bool.pick(F32, U32.is_eq(U32.shrn(x, 31n), 1), F32.neg(v), v)

def naive.leaf(n: Nat, +seed: U32, +i: U32, +acc: F32) -> F32:
  match n:
    case 0n:
      acc
    case 1n++q:
      naive.leaf(q, seed, U32.inc(i), F32.add(acc, value(draw(seed, i))))

def naive(d: Nat, +seed: U32, +lo: U32, +n: U32) -> F32:
  match d:
    case 0n:
      naive.leaf(U32.to_nat(n), seed, lo, 0.0)
    case 1n++p:
      +h = U32.shr(n)
      a b = naive(p, seed, lo, h) naive(p, seed, U32.add(lo, h), U32.sub(n, h))
      F32.add(a, b)

# -- printing ----------------------------------------------------------------------

def hex.d(+x: U32, s: Nat) -> String:
  +v = U32.and(U32.shrn(x, s), 15)
  String.slice("0123456789abcdef", U32.to_nat(v), U32.to_nat(U32.inc(v)))

def hex(+x: U32) -> String:
  "0x" ++ hex.d(x, 28n) ++ hex.d(x, 24n) ++ hex.d(x, 20n) ++ hex.d(x, 16n)
    ++ hex.d(x, 12n) ++ hex.d(x, 8n) ++ hex.d(x, 4n) ++ hex.d(x, 0n)

# -- the edges ---------------------------------------------------------------------

# one value as an accumulator, built the slow obvious way (a negative is the
# negation of its magnitude): a second road to the same limbs as leaf's
def place(+k: U32, +lo: U32, +hi: U32) -> Acc:
  Acc{put(k, 0, lo, hi), put(k, 1, lo, hi), put(k, 2, lo, hi), put(k, 3, lo, hi),
    put(k, 4, lo, hi), put(k, 5, lo, hi), put(k, 6, lo, hi), put(k, 7, lo, hi),
    put(k, 8, lo, hi), put(k, 9, lo, hi)}

def one(+x: U32) -> Acc:
  +o = U32.sub(U32.max(U32.and(U32.shrn(x, 23n), 255), 1), 1)
  +m = mant(x)
  +a = place(U32.shrn(o, 5n), U32.shln(m, U32.to_nat(U32.and(o, 31))),
    U32.shrn(m, U32.to_nat(U32.sub(32, U32.and(o, 31)))))
  Bool.pick(Acc, U32.is_eq(U32.shrn(x, 31n), 1), negate(a), a)

def fold(xs: List<U32>, acc: Acc) -> Acc:
  match xs:
    case Nil{}:
      acc
    case Con{x, t}:
      fold(t, join(acc, one(x)))

def edge(xs: List<U32>) -> String:
  hex(round(fold(xs, zero())))

def edges() -> String:
  "edges: " ++ edge([1065353216, 864026624])  # 1 + 2^-24: a tie, to even (down)
    ++ " " ++ edge([1065353217, 864026624])  # (1 + 2^-23) + 2^-24: a tie, to even (up)
    ++ " " ++ edge([1065353216, 864026624, 1])  # a tie plus 2^-149: up
    ++ " " ++ edge([1065353215, 855638016])  # (1 - 2^-24) + 2^-25: up, out of the significand
    ++ " " ++ edge([2139095039, 2139095039])  # max + max: past the last half ulp, inf
    ++ " " ++ edge([4286578687, 4286578687, 2139095039])  # -max -max +max
    ++ " " ++ edge([1, 1, 3])  # five times 2^-149: subnormal, exact
    ++ " " ++ edge([1065353216, 3212836864])  # 1 - 1: +0
    ++ " " ++ edge([1904214016, 2373976064])  # 2^100 - 2^-100: a borrow through every limb

# -- the report ---------------------------------------------------------------------

def report(name: String, +seed: U32, +n: U32) -> String:
  +e = round(exact(0n, seed, 0, n))
  +same = Bool.and(Bool.and(U32.is_eq(e, round(exact(3n, seed, 0, n))),
    U32.is_eq(e, round(exact(7n, seed, 0, n)))), U32.is_eq(e, round(exact(12n, seed, 0, n))))
  name ++ " n=" ++ U32.show(n) ++ " exact=" ++ hex(e) ++ " naive seq="
    ++ hex(F32.bits(naive(0n, seed, 0, n))) ++ " tree3=" ++ hex(F32.bits(naive(3n, seed, 0, n)))
    ++ " tree7=" ++ hex(F32.bits(naive(7n, seed, 0, n))) ++ " | exact at 0 3 7 12: "
    ++ Bool.pick(String, same, "same", "DIFFER")

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(report("s1", 1, 4096))
    IO.print(report("s2", 2, 5000))
    IO.print(report("s3", 3, 16384))
    IO.print(edges())
#|s1 n=4096 exact=0x3b467d7c naive seq=0x3a3af47c tree3=0x00000000 tree7=0x00000000 | exact at 0 3 7 12: same
#|s2 n=5000 exact=0xbadc10de naive seq=0x3a937421 tree3=0x00000000 tree7=0x00000000 | exact at 0 3 7 12: same
#|s3 n=16384 exact=0xbc882249 naive seq=0xbb0b0bfa tree3=0xbb58e474 tree7=0x00000000 | exact at 0 3 7 12: same
#|edges: 0x3f800000 0x3f800002 0x3f800001 0x3f800000 0x7f800000 0xff7fffff 0x00000005 0x00000000 0x71800000
