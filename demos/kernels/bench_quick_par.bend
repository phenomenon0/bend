import Base
import ./chacha20.bend as C

# Quick throughput bench, forked: 16 MB of keystream as 16 chunks of 1 MB,
# each chunk via its own counter offset. (scratch, not curated)

def key() -> C.ChaKey:
  C.ChaKey{50462976, 117835012, 185207048, 252579084,
    319951120, 387323156, 454695192, 522067228}

def nonce() -> C.Nonce:
  C.Nonce{0, 1241513984, 0}

def fold(+xs: List<&2, U32>, +acc: U32) -> U32:
  match xs:
    case Nil{}:
      acc
    case x <> t:
      fold(t, U32.add(acc, x))

def chunked(+r: Maybe<&2, List<&2, U32>>) -> U32:
  match r:
    case None{}:
      0
    case Some{bs}:
      fold(bs, 0)

def chunk(+i: U32) -> U32:
  chunked(C.keystream(key(), U32.mul(i, 16384), nonce(), 1048576n))

def tree(+d: Nat, +lo: U32, +hi: U32) -> U32:
  match d:
    case 0n:
      chunk(lo)
    case 1n++p:
      +mid = U32.shrn(U32.add(lo, hi), 1n)
      a b = tree(p, lo, mid) tree(p, mid, hi)
      U32.add(a, b)

def main() -> String:
  String.append("chacha16m-par sum=", Nat.show(U32.to_nat(tree!(4n, 0, 16))))
