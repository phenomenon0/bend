# Contract: all 64 bytes of the final counter remain usable.
import Base
import ../../demos/kernels/chacha20.bend as C

def size(r: Maybe<&2, List<&2, U32>>) -> String:
  match r:
    case None{}:
      "counter exhausted"
    case Some{bs}:
      Nat.show(List.length(&2, U32, bs))

def main() -> String:
  size(C.keystream(C.ChaKey{0, 0, 0, 0, 0, 0, 0, 0},
    4294967295, C.Nonce{0, 0, 0}, 64n))

#|"64"
