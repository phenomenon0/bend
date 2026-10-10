# Collatz steps, summed over a fork tree: the leaf is a flat tail loop (spin), the tree a bang.
#   total!(d, i) = sum over lane k < 2^d of steps(i + k + 1)   (steps of 1 is 0)
import Base

# a flat tail loop (Nat fuel counting down, accumulators carried): the Collatz
# step count of n, 512 steps of fuel (n < 2^16 needs at most 339)
def steps(fuel: Nat, +n: U32, +acc: U32) -> U32:
  match fuel:
    case 0n:
      acc
    case 1n+k:
      +odd = ((3 * n : U32) + 1 : U32)
      steps(k, Bool.pick(U32, U32.is_eq(n, 1), 1,
          Bool.pick(U32, U32.is_eq(U32.and(n, 1), 0), U32.shr(n), (odd : U32))),
        Bool.pick(U32, U32.is_eq(n, 1), acc, (acc + 1 : U32)))

def pow2(d: Nat) -> Nat:
  match d:
    case 0n:
      1n
    case 1n+p:
      +h = pow2(p)
      Nat.add(h, h)

def total(d: Nat, +i: U32) -> U32:
  match d:
    case 0n:
      steps(512n, (i + 1 : U32), 0)
    case 1n++p:
      a b = total(p, i) total(p, (i + U32.from_nat(pow2(p)) : U32))
      (a + b : U32)

def main() -> IO(Unit):
  IO.print(U32.show(total!(10n, 0)))

#|61317
