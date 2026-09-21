import Base
import ./chacha20.bend as C

# Quick throughput bench: 16 MB of keystream, summed. (scratch, not curated)

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

def summarize(+r: Maybe<&2, List<&2, U32>>) -> String:
  match r:
    case None{}:
      "exhausted"
    case Some{bs}:
      String.append("chacha16m sum=", Nat.show(U32.to_nat(fold(bs, 0))))

def main() -> String:
  summarize(C.keystream(key(), 0, nonce(), 16777216n))
