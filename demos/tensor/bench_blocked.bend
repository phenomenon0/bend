# The same decode skeleton, same owner, same three runs of the same block --
# only the REDUCTION changes. bench_gemv.bend sums a row into one accumulator,
# which is a serial chain of F32 adds: neither clang nor Bend may reassociate
# it, so both sides run at exactly one add-latency per element and the layout
# stops mattering. This one keeps four accumulators, lane c into s[c mod 4],
# and adds them as (s0+s1)+(s2+s3) at the end of the row. The order is fixed
# and the twin's `blocked` row does the identical thing, so the two still
# agree bit for bit -- but the chain is now four deep in parallel, and both
# sides widen it: Bend's through Array.get4 (docs/omen/lanes/c2b2.md).
#
# The three view offsets are written out here rather than passed as `View`s:
# the probe is about the reduction's shape, and the addresses it reads are the
# same ones T.mat(0, 1024, 1024, 1024) and T.vec(1048576, 1024) name.
import Base
import ./tensor.bend as T

def h(+p: U32) -> U32:
  U32.xor(U32.mul(U32.inc(p), 2654435761), U32.shrn(p, 3n))

def v(+p: U32) -> F32:
  F32.div(F32.sub(U32.to_f32(U32.shrn(h(p), 19n)), 4096.0), 4096.0)

def fill(fuel: Nat, +i: U32, t: T.Ten) -> T.Ten:
  match fuel:
    case 0n:
      t
    case 1n++k:
      fill(k, U32.inc(i), T.put(t, i, v(i)))

def scale(x: F32) -> F32:
  F32.mul(x, 0.140625)

type S4 is Type:
  S4{xs: Array<F32>, s0: F32, s1: F32, s2: F32, s3: F32}

type Q4 is Type:
  Q4{a0: F32, a1: F32, a2: F32, a3: F32}

def q4.fin(+s0: F32, +s1: F32, +s2: F32, +s3: F32, a: Q4,
  r: Array<F32> & (F32 & (F32 & (F32 & F32)))) -> S4:
  match a:
    case Q4{a0, a1, a2, a3}:
      (xs, q) = r
      (b0, t) = q
      (b1, u) = t
      (b2, b3) = u
      S4{xs, F32.add(s0, F32.mul(a0, b0)), F32.add(s1, F32.mul(a1, b1)),
        F32.add(s2, F32.mul(a2, b2)), F32.add(s3, F32.mul(a3, b3))}

def q4.a(+q: U32, +s0: F32, +s1: F32, +s2: F32, +s3: F32,
  r: Array<F32> & (F32 & (F32 & (F32 & F32)))) -> S4:
  (xs, w) = r
  (a0, t) = w
  (a1, u) = t
  (a2, a3) = u
  q4.fin(s0, s1, s2, s3, Q4{a0, a1, a2, a3}, Array.get4(F32, xs, q))

# Each step reads a[p..p+3] and x[q..q+3] with one Array.get4 apiece: its
# single range check is what lets the four lanes' loads widen.
def dot4.step(+p: U32, +q: U32, st: S4) -> S4:
  match st:
    case S4{xs, s0, s1, s2, s3}:
      q4.a(q, s0, s1, s2, s3, Array.get4(F32, xs, p))

def dot4.go(fuel: Nat, +p: U32, +q: U32, st: S4) -> S4:
  match fuel:
    case 0n:
      st
    case 1n++k:
      dot4.go(k, U32.add(p, 4), U32.add(q, 4), dot4.step(p, q, st))

def row4.fin(+iy: U32, st: S4) -> Array<F32>:
  match st:
    case S4{xs, s0, s1, s2, s3}:
      Array.set(F32, xs, iy, F32.add(F32.add(s0, s1), F32.add(s2, s3)))

def row4(+pa: U32, +px: U32, +iy: U32, quads: Nat, xs: Array<F32>) -> Array<F32>:
  row4.fin(iy, dot4.go(quads, pa, px, S4{xs, 0.0, 0.0, 0.0, 0.0}))

def g4.go(fuel: Nat, +pa: U32, +sa: U32, +px: U32, +iy: U32, +quads: Nat,
  xs: Array<F32>) -> Array<F32>:
  match fuel:
    case 0n:
      xs
    case 1n++k:
      g4.go(k, U32.add(pa, sa), sa, px, U32.inc(iy), quads,
        row4(pa, px, iy, quads, xs))

def gemv4.at(n: U32, d: Nat, xs: Array<F32>) -> T.Ten:
  T.Ten{n, d, g4.go(1024n, 0, 1024, 1048576, 1049600, 256n, xs)}

def gemv4(t: T.Ten) -> T.Ten:
  match t:
    case T.Ten{n, d, xs}:
      gemv4.at(n, d, xs)

def step(t: T.Ten) -> T.Ten:
  T.map(~scale, gemv4(t), T.vec(1049600, 1024), T.vec(1048576, 1024))

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

def sum.four(s: Sum) -> String:
  match s:
    case Sum{t, acc, orb, andb, nf}:
      String.join([U32.show(acc), U32.show(orb), U32.show(andb),
        U32.show(nf)], "\n")

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(sum.four(sum.go(1024n, 1048576,
      Sum{reps(256n, fill(1049600n, 0, T.zeros(21n))), 0, 0, 4294967295, 0})))
