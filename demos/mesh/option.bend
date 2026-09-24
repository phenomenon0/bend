# A European call under Black-Scholes, by Monte Carlo, with bits that do not
# depend on the machine, the thread count, the split or the worker.
#
# Path i is a pure function of (seed, i): its normal comes from Marsaglia's
# polar method on Threefry blocks (seed, i, j), j = 0, 1, ... (16 tries; all
# rejected is p ~ 2e-11 a path, and gives 0). S_T = S0 exp(mu + sd z), the
# payoff max(S_T - K, 0).
#
# Two things usually break reproducibility, and both are designed out:
#
#   libm       exp and log differ between machines' math libraries, so they
#              are built here from + - * / sqrt floor, which IEEE rounds the
#              same everywhere: exp by Cody-Waite reduction and a degree-13
#              polynomial (<= 1 ulp from libm), log by halving to [1, sqrt 2)
#              and the atanh series (<= 2 ulp on the polar method's domain,
#              s >= 2^-63).
#   the sum    payoffs are summed as fixed point -- floor(pay * 2^32) and
#              floor(pay^2 * 2^16) -- in 96-bit integers, three U32 limbs
#              each, so the join is an integer add: associative.
#
# option_ref.py (CPython) and option_twin.c do the same operations in the same
# order; all three print the same accumulator bits.
import Base
import ../../power/rng.bend as Rng

type Opt is Data:
  Opt{a0: U32, a1: U32, a2: U32, b0: U32, b1: U32, b2: U32}

# -- deterministic exp and log ---------------------------------------------------

def TWO32() -> F64:
  4294967296.0d

def LN2_HI() -> F64:
  0.69314718036912381649d

def LN2_LO() -> F64:
  0.00000000019082149292705877d

def INV_LN2() -> F64:
  1.442695040888963387d

def SQRT2() -> F64:
  1.4142135623730951d

# n!, exactly (n <= 18)
def fact(k: Nat, +i: F64, +f: F64) -> F64:
  match k:
    case 0n:
      f
    case 1n++q:
      fact(q, F64.add(i, 1.0d), F64.mul(f, i))

def inv_fact(+n: U32) -> F64:
  F64.div(1.0d, fact(U32.to_nat(U32.sub(U32.max(n, 1), 1)), 2.0d, 1.0d))

# p = p r + 1/n!, for n from 12 down to 0
def exp.poly(k: Nat, +r: F64, +n: U32, +p: F64) -> F64:
  match k:
    case 0n:
      p
    case 1n++q:
      exp.poly(q, r, U32.sub(n, 1), F64.add(F64.mul(p, r), inv_fact(n)))

def scale(k: Nat, +s: F64, +p: F64) -> F64:
  match k:
    case 0n:
      p
    case 1n++q:
      scale(q, s, F64.mul(p, s))

def exp(+x: F64) -> F64:
  +k = F64.floor(F64.add(F64.mul(x, INV_LN2()), 0.5d))
  +r = F64.sub(F64.sub(x, F64.mul(k, LN2_HI())), F64.mul(k, LN2_LO()))
  +p = exp.poly(13n, r, 12, inv_fact(13))
  scale(U32.to_nat(F64.to_u32(F64.abs(k))), Bool.pick(F64, F64.is_gt(k, 0.0d), 2.0d, 0.5d), p)

# y into [1, 2) by doublings (80 is past the polar method's 2^-63), e the count
def norm(k: Nat, +y: F64, +e: F64) -> F64 & F64:
  match k:
    case 0n:
      (y, e)
    case 1n++q:
      +lt = F64.is_lt(y, 1.0d)
      norm(q, Bool.pick(F64, lt, F64.mul(y, 2.0d), y), Bool.pick(F64, lt, F64.sub(e, 1.0d), e))

# q = q t2 + 1/(2k+1), for k from 11 down to 0
def log.poly(k: Nat, +t2: F64, +j: F64, +q: F64) -> F64:
  match k:
    case 0n:
      q
    case 1n++z:
      log.poly(z, t2, F64.sub(j, 2.0d), F64.add(F64.mul(q, t2), F64.div(1.0d, j)))

def log.at(ye: F64 & F64) -> F64:
  (+y0, +e0) = ye
  +big = F64.is_gt(y0, SQRT2())
  +y = Bool.pick(F64, big, F64.mul(y0, 0.5d), y0)
  +e = Bool.pick(F64, big, F64.add(e0, 1.0d), e0)
  +t = F64.div(F64.sub(y, 1.0d), F64.add(y, 1.0d))
  +q = log.poly(12n, F64.mul(t, t), 23.0d, F64.div(1.0d, 25.0d))
  F64.add(F64.mul(e, LN2_HI()), F64.add(F64.mul(e, LN2_LO()), F64.mul(F64.mul(2.0d, t), q)))

# log y, for y in (0, 1]
def log(+y: F64) -> F64:
  log.at(norm(80n, y, 0.0d))

# -- one path -----------------------------------------------------------------------

def unit(+w: U32) -> F64:
  F64.sub(F64.mul(2.0d, F64.div(F64.add(U32.to_f64(w), 0.5d), TWO32())), 1.0d)

type UV is Data:
  UV{u: F64, v: F64}

def uv(ab: U32 & U32) -> UV:
  (a, b) = ab
  UV{unit(a), unit(b)}

def uv.u(w: UV) -> F64:
  match w:
    case UV{u, v}:
      u

def uv.v(w: UV) -> F64:
  match w:
    case UV{u, v}:
      v

# the polar method: accept the first (u, v) inside the unit disk
def polar(k: Nat, ok: Bool, +u: F64, +s: F64, +seed: U32, +i: U32, +j: U32) -> F64:
  match k ok:
    case _ True{}:
      F64.mul(u, F64.sqrt(F64.div(F64.mul(F64.neg(2.0d), log(s)), s)))
    case 0n False{}:
      0.0d
    case 1n++q False{}:
      +w = uv(Rng.block(seed, i, j, 0))
      +u2 = uv.u(w)
      +v2 = uv.v(w)
      +s2 = F64.add(F64.mul(u2, u2), F64.mul(v2, v2))
      polar(q, F64.is_gt(s2, 0.0d) && F64.is_lt(s2, 1.0d), u2, s2, seed, i, U32.inc(j))

def normal(+seed: U32, +i: U32) -> F64:
  polar(16n, False{}, 0.0d, 0.0d, seed, i, 0)

def S0() -> F64:
  100.0d

def K() -> F64:
  105.0d

def R() -> F64:
  0.05d

def SIG() -> F64:
  0.2d

def T() -> F64:
  1.0d

def payoff(+seed: U32, +i: U32) -> F64:
  +mu = F64.mul(F64.sub(R(), F64.mul(F64.mul(0.5d, SIG()), SIG())), T())
  +sd = F64.mul(SIG(), F64.sqrt(T()))
  +st = F64.mul(S0(), exp(F64.add(mu, F64.mul(sd, normal(seed, i)))))
  Bool.pick(F64, F64.is_gt(st, K()), F64.sub(st, K()), 0.0d)

# -- the fixed-point sums -----------------------------------------------------------------

def carry(+a: U32, +b: U32, +c: U32) -> U32:
  +s = U32.add(a, b)
  U32.or(Bool.to_u32(U32.is_lt(s, a)), Bool.to_u32(U32.is_lt(U32.add(s, c), s)))

def hi(+x: F64) -> U32:
  F64.to_u32(F64.floor(F64.div(x, TWO32())))

def lo(+x: F64) -> U32:
  F64.to_u32(F64.sub(x, F64.mul(F64.floor(F64.div(x, TWO32())), TWO32())))

# n paths from i: sum floor(pay 2^32) into a, floor(pay^2 2^16) into b
def leaf(n: Nat, +seed: U32, +i: U32, +a0: U32, +a1: U32, +a2: U32, +b0: U32, +b1: U32,
  +b2: U32) -> Opt:
  match n:
    case 0n:
      Opt{a0, a1, a2, b0, b1, b2}
    case 1n++q:
      +p = payoff(seed, i)
      +x = F64.floor(F64.mul(p, TWO32()))
      +y = F64.floor(F64.mul(F64.mul(p, p), 65536.0d))
      +xl = lo(x)
      +xh = hi(x)
      +yl = lo(y)
      +yh = hi(y)
      +ca = carry(a0, xl, 0)
      +cb = carry(b0, yl, 0)
      leaf(q, seed, U32.inc(i), U32.add(a0, xl), U32.add(U32.add(a1, xh), ca),
        U32.add(a2, carry(a1, xh, ca)), U32.add(b0, yl), U32.add(U32.add(b1, yh), cb),
        U32.add(b2, carry(b1, yh, cb)))

def join(x: Opt, y: Opt) -> Opt:
  match x y:
    case Opt{+a0, +a1, a2, +b0, +b1, b2} Opt{+c0, +c1, c2, +d0, +d1, d2}:
      +ca = carry(a0, c0, 0)
      +cb = carry(b0, d0, 0)
      Opt{U32.add(a0, c0), U32.add(U32.add(a1, c1), ca), U32.add(U32.add(a2, c2), carry(a1, c1, ca)),
        U32.add(b0, d0), U32.add(U32.add(b1, d1), cb), U32.add(U32.add(b2, d2), carry(b1, d1, cb))}

def tree(d: Nat, +seed: U32, +lo: U32, +n: U32) -> Opt:
  match d:
    case 0n:
      leaf(U32.to_nat(n), seed, lo, 0, 0, 0, 0, 0, 0)
    case 1n++p:
      +h = U32.shr(n)
      l r = tree(p, seed, lo, h) tree(p, seed, U32.add(lo, h), U32.sub(n, h))
      join(l, r)

# -- the answer, from the bits -----------------------------------------------------------

def wide(+x0: U32, +x1: U32, +x2: U32) -> F64:
  F64.add(F64.mul(F64.add(F64.mul(U32.to_f64(x2), TWO32()), U32.to_f64(x1)), TWO32()), U32.to_f64(x0))

# "price=P se=E" over n paths: discounted mean payoff and its standard error
def show(o: Opt, +n: U32) -> String:
  match o:
    case Opt{+a0, +a1, +a2, +b0, +b1, +b2}:
      +disc = exp(F64.neg(F64.mul(R(), T())))
      +fn = U32.to_f64(n)
      +mean = F64.div(F64.div(wide(a0, a1, a2), TWO32()), fn)
      +var = F64.sub(F64.div(F64.div(wide(b0, b1, b2), 65536.0d), fn), F64.mul(mean, mean))
      "price=" ++ F64.show(F64.mul(disc, mean)) ++ " se="
        ++ F64.show(F64.mul(disc, F64.sqrt(F64.div(F64.max(var, 0.0d), fn))))
