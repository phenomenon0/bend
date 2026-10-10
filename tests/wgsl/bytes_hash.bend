# A hash tree over a Bytes: lane i reads the word at byte 4i + 1 (unaligned; the last lanes run past
# the end, where a byte reads 0); the join is not commutative and reads its node's level and offset.
#   hash!(d, bs, i)   bs = fill(nb, seed, "")
import Base

def pow2(d: Nat) -> Nat:
  match d:
    case 0n:
      1n
    case 1n+p:
      +h = pow2(p)
      Nat.add(h, h)

# nb bytes of an LCG, high byte of each state
def fill(n: Nat, +s: U32, acc: Bytes()) -> Bytes():
  match n:
    case 0n:
      acc
    case 1n+k:
      +t = ((s * 1664525 : U32) + 1013904223 : U32)
      fill(k, t, Bytes.push(acc, (t >> 24n : U32)))

def mix(+w: U32) -> U32:
  (((w .^. (w >> 15n : U32)) : U32) * 2246822519 : U32)

def hj(+a: U32, +b: U32, p: Nat, +i: U32) -> U32:
  +q = U32.from_nat(p)
  ((((a * 31 : U32) + b : U32) .^. (i * 7 : U32) : U32) + q : U32)

def hash(d: Nat, +bs: Bytes(), +i: U32) -> U32:
  match d:
    case 0n:
      mix(Bytes.word_le(bs, U32.to_nat(((i * 4 : U32) + 1 : U32))))
    case 1n++p:
      a b = hash(p, bs, i) hash(p, bs, (i + U32.from_nat(pow2(p)) : U32))
      hj(a, b, p, i)

def main() -> IO(Unit):
  IO.print(U32.show(hash!(4n, fill(64n, 12345, ""), 0)))

#|913564336
