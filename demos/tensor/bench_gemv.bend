# The decode-step skeleton on flat views: one 1024x1024 matrix, one vector, and
# 256 rounds of y <- A x followed by x <- y / 16 -- a power iteration, which is
# what a decode loop is once the nonlinearity is taken out: every round's input
# is the round before's output, so nothing reorders and nothing caches.
#
# A, x and y are three views into ONE owner's block. The loop carries the
# Array and nothing else; the three descriptors are read once, outside it.
#
# Four printed lines, all four also printed by twin.c: the checksum over the
# 1024 result words, and three probes. POWER.md: agreement across backends
# proves the backends match, not that the bench measured anything, so the
# probes have to rule the degenerate answers out. `or` and `and` over the
# result's bits differ exactly when the 1024 words are not all one value
# (all-zero, the usual degenerate run, prints 0 and 0); `nonfin` is nonzero
# when any word went to an infinity or a NaN.
import Base
import ./tensor.bend as T

def h(+p: U32) -> U32:
  U32.xor(U32.mul(U32.inc(p), 2654435761), U32.shrn(p, 3n))

# a value in [-1, 1) in steps of 1/4096, exact in F32, off the TOP of the hash
def v(+p: U32) -> F32:
  F32.div(F32.sub(U32.to_f32(U32.shrn(h(p), 19n)), 4096.0), 4096.0)

def fill(fuel: Nat, +i: U32, t: T.Ten) -> T.Ten:
  match fuel:
    case 0n:
      t
    case 1n++k:
      fill(k, U32.inc(i), T.put(t, i, v(i)))

# 9/64, the one constant that keeps the iteration in range: A's spectral radius
# here is about 6.9, so dividing by 16 decays the vector to all zeros by round
# 144 and the bench would then be timing multiplications by zero (the probe
# lines below catch exactly that). At 9/64 the mean magnitude stays inside
# [0.83, 9116] for all 256 rounds -- no denormals, no infinities.
def scale(x: F32) -> F32:
  F32.mul(x, 0.140625)

def step(t: T.Ten) -> T.Ten:
  T.map(~scale, T.gemv(t, T.mat(0, 1024, 1024, 1024), T.vec(1048576, 1024),
    T.vec(1049600, 1024)), T.vec(1049600, 1024), T.vec(1048576, 1024))

def reps(fuel: Nat, t: T.Ten) -> T.Ten:
  match fuel:
    case 0n:
      t
    case 1n++k:
      reps(k, step(t))

def rot7(+v: U32) -> U32:
  U32.or(U32.shln(v, 7n), U32.shrn(v, 25n))

def mix(+acc: U32, +x: U32) -> U32:
  rot7(U32.add(U32.mul(acc, 31), x))

# 0x80000000 when the exponent is all ones (an infinity or a NaN), 0 when the
# number is finite: the exponent field plus one exponent step carries into the
# sign bit exactly then. No branch, so the probe folds like the checksum.
def nonfin(+b: U32) -> U32:
  U32.and(U32.add(U32.and(b, 2139095040), 8388608), 2147483648)

type Sum is Type:
  Sum{t: T.Ten, acc: U32, orb: U32, andb: U32, nf: U32}

def sum.bits(+acc: U32, +orb: U32, +andb: U32, +nf: U32, t: T.Ten, +b: U32) -> Sum:
  Sum{t, mix(acc, b), U32.or(orb, b), U32.and(andb, b), U32.or(nf, nonfin(b))}

def sum.add(+acc: U32, +orb: U32, +andb: U32, +nf: U32, r: T.Ten & F32) -> Sum:
  (t, x) = r
  sum.bits(acc, orb, andb, nf, t, F32.bits(x))

def sum.go(fuel: Nat, +i: U32, s: Sum) -> Sum:
  match fuel:
    case 0n:
      s
    case 1n++k:
      match s:
        case Sum{t, acc, orb, andb, nf}:
          sum.go(k, U32.inc(i), sum.add(acc, orb, andb, nf, T.get(t, i)))

def sum.run() -> Sum:
  sum.go(1024n, 1048576,
    Sum{reps(256n, fill(1049600n, 0, T.zeros(21n))), 0, 0, 4294967295, 0})

def sum.four(s: Sum) -> String:
  match s:
    case Sum{t, acc, orb, andb, nf}:
      String.join([U32.show(acc), U32.show(orb), U32.show(andb),
        U32.show(nf)], "\n")

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(sum.four(sum.run()))
