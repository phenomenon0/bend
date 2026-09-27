# One kernel for both units: y = A x over 16384 rows of PLACE_COLS columns,
# the weights and the input hashed from their index instead of loaded (the
# decode step's dot products with no memory traffic, so neither unit waits
# on the bus the other does not use). One bang forks four ways seven times,
# 4^7 = 16384 leaves = the GPU's lane cube, one row per leaf, one flat loop
# per row. The same binary runs it on the CPU pool (--gpu off) or on the GPU
# (--gpu on); twin.c is the C twin. The four lines are the checksum and its
# probes: `or` and `and` over the result bits, and any infinity or NaN.
#   PLACE_COLS=4096 ./main --gpu on
import Base

def h(+p: U32) -> U32:
  U32.xor(U32.mul(U32.inc(p), 2654435761), U32.shrn(p, 3n))

def v(+p: U32) -> F32:
  F32.div(F32.sub(U32.to_f32(U32.shrn(h(p), 19n)), 4096.0), 4096.0)

def dot(fuel: Nat, +p: U32, +j: U32, +s: F32) -> F32:
  match fuel:
    case 0n:
      s
    case 1n++k:
      dot(k, U32.inc(p), U32.inc(j),
        F32.add(s, F32.mul(v(p), v(U32.xor(j, 2654435769)))))

type S is Data:
  S{acc: U32, orb: U32, andb: U32, nf: U32}

def nonfin(+b: U32) -> U32:
  U32.and(U32.add(U32.and(b, 2139095040), 8388608), 2147483648)

def leaf(+b: U32) -> S:
  S{b, b, b, nonfin(b)}

def mix(+acc: U32, +x: U32) -> U32:
  U32.or(U32.shln(U32.add(U32.mul(acc, 31), x), 7n),
    U32.shrn(U32.add(U32.mul(acc, 31), x), 25n))

def join(a: S, b: S) -> S:
  match a b:
    case S{a0, a1, a2, a3} S{b0, b1, b2, b3}:
      S{mix(a0, b0), U32.or(a1, b1), U32.and(a2, b2), U32.or(a3, b3)}

def node(+k: Nat, +i: U32, +m: U32) -> S:
  match k:
    case 0n:
      leaf(F32.bits(dot(U32.to_nat(m), U32.mul(i, m), 0, 0.0)))
    case 1n+e:
      a b c d = node(e, U32.mul(i, 4), m) node(e, U32.add(U32.mul(i, 4), 1), m)
        node(e, U32.add(U32.mul(i, 4), 2), m) node(e, U32.add(U32.mul(i, 4), 3), m)
      join(join(a, b), join(c, d))

def four(s: S) -> String:
  match s:
    case S{acc, orb, andb, nf}:
      String.join([U32.show(acc), U32.show(orb), U32.show(andb),
        U32.show(nf)], "\n")

def cols(r: Maybe<&2, Nat>) -> U32:
  match r:
    case Some{n}:
      U32.from_nat(n)
    case None{}:
      1024

def main() -> IO(Unit):
  do IO<Unit>:
    s : String <- IO.try(String, IO.get_env("PLACE_COLS"))
    IO.print(four(node!(7n, 0, cols(Nat.read(s)))))
