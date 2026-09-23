# One sequential random stream, run by a fork tree, bit for bit.
#
# PCG32 (O'Neill 2014; Go's math/rand/v2 and NumPy's default are its 64-bit
# cousins) is an LCG with a permuted output: state' = a * state + c mod 2^64,
# out = rotr(xorshift(state)). The usual way to parallelise a generator like
# this is to give every worker its own seed -- and then the answer depends on
# how many workers there were (the last line below shows it: the same Monte
# Carlo, reseeded per leaf, counts differently at 16 leaves and at 512).
#
# The LCG step is an affine map x -> a*x + c, and affine maps compose:
# (a2, c2) after (a1, c1) is (a2*a1, a2*c1 + c2). So k steps are one affine map,
# and squaring it log2(k) times gets there without walking (Brown, "Random
# number generation with arbitrary strides", 1994; pcg_advance_lcg_64). A leaf
# of the fork tree jumps straight to its own slice of the ONE stream, and the
# tree reproduces the sequential program exactly -- same draws, same pairs, same
# count -- at any depth, under any --threads, on any lane.
#
# 64-bit arithmetic is done on pairs of U32, so this file needs nothing a stock
# Bend lacks: a 32x32 multiply's high word comes from four 16-bit products.
# pcg_gen.py is the oracle: pcg-c-basic transcribed onto Python ints, held to
# the reference demo's outputs, and a plain sequential loop for the count.
import Base

# -- 64-bit words as U32 pairs ---------------------------------------------------

type W is Data:
  W{hi: U32, lo: U32}

# the high word of the 64-bit product a * b
def mulhi(+a: U32, +b: U32) -> U32:
  +a0 = U32.and(a, 65535)
  +a1 = U32.shrn(a, 16n)
  +b0 = U32.and(b, 65535)
  +b1 = U32.shrn(b, 16n)
  +p01 = U32.mul(a0, b1)
  +p10 = U32.mul(a1, b0)
  +mid = U32.add(U32.add(U32.shrn(U32.mul(a0, b0), 16n), U32.and(p01, 65535)), U32.and(p10, 65535))
  U32.add(U32.add(U32.mul(a1, b1), U32.shrn(mid, 16n)), U32.add(U32.shrn(p01, 16n), U32.shrn(p10, 16n)))

def mul(x: W, y: W) -> W:
  match x y:
    case W{+xh, +xl} W{+yh, +yl}:
      W{U32.add(mulhi(xl, yl), U32.add(U32.mul(xl, yh), U32.mul(xh, yl))), U32.mul(xl, yl)}

def add(x: W, y: W) -> W:
  match x y:
    case W{xh, +xl} W{yh, yl}:
      +l = U32.add(xl, yl)
      W{U32.add(U32.add(xh, yh), Bool.to_u32(U32.is_lt(l, xl))), l}

def one() -> W:
  W{0, 1}

# PCG's multiplier, 6364136223846793005
def mult() -> W:
  W{1481765933, 1284865837}

# -- the generator ------------------------------------------------------------------

# the step, on the words themselves (no record per draw): new = old * mult + inc
def next.lo(+lo: U32, +il: U32) -> U32:
  U32.add(U32.mul(lo, 1284865837), il)

def next.hi(+hi: U32, +lo: U32, +ih: U32, +il: U32) -> U32:
  +pl = U32.mul(lo, 1284865837)
  +c = Bool.to_u32(U32.is_lt(U32.add(pl, il), pl))
  U32.add(U32.add(mulhi(lo, 1284865837), U32.add(U32.mul(lo, 1481765933), U32.mul(hi, 1284865837))),
    U32.add(ih, c))

# XSH-RR: the output of the state BEFORE the step
def out(+hi: U32, +lo: U32) -> U32:
  +xl = U32.xor(lo, U32.or(U32.shrn(lo, 18n), U32.shln(hi, 14n)))
  +xh = U32.xor(hi, U32.shrn(hi, 18n))
  +xs = U32.or(U32.shrn(xl, 27n), U32.shln(xh, 5n))
  +rot = U32.shrn(hi, 27n)
  U32.or(U32.shrn(xs, U32.to_nat(rot)), U32.shln(xs, U32.to_nat(U32.and(U32.sub(0, rot), 31))))

type Pcg is Data:
  Pcg{state: W, inc: W}

def step(g: Pcg) -> Pcg:
  match g:
    case Pcg{s, +inc}:
      Pcg{add(mul(s, mult()), inc), inc}

def seed.fin(g: Pcg, init: U32) -> Pcg:
  match g:
    case Pcg{s, i}:
      step(Pcg{add(s, W{0, init}), i})

# pcg32_srandom_r: the stream is picked by seq, the place in it by init
def seed(init: U32, +seq: U32) -> Pcg:
  seed.fin(step(Pcg{W{0, 0}, W{U32.shrn(seq, 31n), U32.or(U32.shln(seq, 1n), 1)}}), init)

def draw(g: Pcg) -> U32:
  match g:
    case Pcg{s, _}:
      match s:
        case W{+hi, lo}:
          out(hi, lo)

# -- the jump ----------------------------------------------------------------------

def bit(+k: W, +b: U32) -> U32:
  match k:
    case W{hi, lo}:
      Bool.pick(U32, U32.is_lt(b, 32), U32.shrn(lo, U32.to_nat(b)),
        U32.shrn(hi, U32.to_nat(U32.sub(b, 32))))

# (am, ap) accumulates the affine map of the bits of k seen so far; (cm, cp) is
# the map of 2^j steps, squared each turn. 64 turns cover any 64-bit k.
def jump.go(j: Nat, +k: W, +am: W, +ap: W, +cm: W, +cp: W, +b: U32) -> W & W:
  match j:
    case 0n:
      (am, ap)
    case 1n++q:
      +hit = U32.is_eq(U32.and(bit(k, b), 1), 1)
      jump.go(q, k, Bool.pick(W, hit, mul(am, cm), am),
        Bool.pick(W, hit, add(mul(ap, cm), cp), ap), mul(cm, cm),
        mul(add(cm, one()), cp), U32.inc(b))

def apply(m: W & W, s: W) -> W:
  (a, c) = m
  add(mul(a, s), c)

# pcg32_advance_r: k steps in 64 squarings
def jump(g: Pcg, +k: W) -> Pcg:
  match g:
    case Pcg{s, +inc}:
      Pcg{apply(jump.go(64n, k, one(), W{0, 0}, mult(), inc, 0), s), inc}

# -- the Monte Carlo ------------------------------------------------------------------

def dart(+x: U32, +y: U32) -> U32:
  +a = U32.shrn(x, 17n)
  +b = U32.shrn(y, 17n)
  Bool.to_u32(U32.is_lt(U32.add(U32.mul(a, a), U32.mul(b, b)), 1073741824))

# n pairs off the stream at (hi, lo): two draws a turn, state in four words
def leaf(n: Nat, +hi: U32, +lo: U32, +ih: U32, +il: U32, +acc: U32) -> U32:
  match n:
    case 0n:
      acc
    case 1n++q:
      +h1 = next.hi(hi, lo, ih, il)
      +l1 = next.lo(lo, il)
      leaf(q, next.hi(h1, l1, ih, il), next.lo(l1, il), ih, il,
        U32.add(acc, dart(out(hi, lo), out(h1, l1))))

def leaf.at(g: Pcg, +n: U32) -> U32:
  match g:
    case Pcg{s, i}:
      match s i:
        case W{hi, lo} W{ih, il}:
          leaf(U32.to_nat(n), hi, lo, ih, il, 0)

# n pairs from g: the left half starts at g, the right half at g jumped by the
# 2h draws the left half will take -- the only thing a right leaf needs to know
def darts(d: Nat, +g: Pcg, +n: U32) -> U32:
  match d:
    case 0n:
      leaf.at(g, n)
    case 1n++p:
      +h = U32.shr(n)
      a b = darts(p, g, h) darts(p, jump(g, W{0, U32.shln(h, 1n)}), U32.sub(n, h))
      U32.add(a, b)

# the usual mistake, for contrast: every leaf gets a seed of its own
def reseeded(d: Nat, +j: U32, +n: U32) -> U32:
  match d:
    case 0n:
      leaf.at(seed(U32.add(42, j), 54), n)
    case 1n++p:
      +h = U32.shr(n)
      a b = reseeded(p, U32.shln(j, 1n), h) reseeded(p, U32.inc(U32.shln(j, 1n)), U32.sub(n, h))
      U32.add(a, b)

# -- the report -----------------------------------------------------------------------

def hex.d(+x: U32, s: Nat) -> String:
  +v = U32.and(U32.shrn(x, s), 15)
  String.slice("0123456789abcdef", U32.to_nat(v), U32.to_nat(U32.inc(v)))

def hex(+x: U32) -> String:
  "0x" ++ hex.d(x, 28n) ++ hex.d(x, 24n) ++ hex.d(x, 20n) ++ hex.d(x, 16n)
    ++ hex.d(x, 12n) ++ hex.d(x, 8n) ++ hex.d(x, 4n) ++ hex.d(x, 0n)

def demo(k: Nat, g: Pcg) -> String:
  match k:
    case 0n:
      ""
    case 1n++q:
      +g2 = g
      " " ++ hex(draw(g2)) ++ demo(q, step(g2))

# 2^40 + 7 = 256 * 2^32 + 7;  10^12 = 232 * 2^32 + 3567587328
def jumps(+g: Pcg) -> String:
  "jump 2^40+7=" ++ hex(draw(jump(g, W{256, 7}))) ++ " 10^12="
    ++ hex(draw(jump(g, W{232, 3567587328})))

def count(+g: Pcg, +n: U32) -> String:
  +h0 = darts(0n, g, n)
  +same = Bool.and(U32.is_eq(h0, darts(4n, g, n)), U32.is_eq(h0, darts(9n, g, n)))
  "darts pairs=" ++ U32.show(n) ++ " hits=" ++ U32.show(h0) ++ " at depths 0 4 9: "
    ++ Bool.pick(String, same, "same", "DIFFER") ++ " | reseeded per leaf, depths 4 9: "
    ++ U32.show(reseeded(4n, 0, n)) ++ " " ++ U32.show(reseeded(9n, 0, n))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("demo" ++ demo(6n, seed(42, 54)))
    IO.print(jumps(seed(42, 54)))
    IO.print(count(seed(42, 54), 65536))
#|demo 0xa15c02b7 0x7b47f409 0xba1d3330 0x83d2f293 0xbfa4784b 0xcbed606e
#|jump 2^40+7=0xdd8e85de 10^12=0x4e760141
#|darts pairs=65536 hits=51636 at depths 0 4 9: same | reseeded per leaf, depths 4 9: 51302 51369
