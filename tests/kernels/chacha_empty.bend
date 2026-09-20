# The empty message consumes no block, even at the last counter.
import Base
import ../../demos/kernels/chacha20.bend as C

def key() -> C.ChaKey:
  C.ChaKey{50462976, 117835012, 185207048, 252579084,
    319951120, 387323156, 454695192, 522067228}

def nonce() -> C.Nonce:
  C.Nonce{0, 1241513984, 0}

def shown(r: Maybe<&2, List<&2, U32>>) -> String:
  match r:
    case None{}:
      "counter exhausted"
    case Some{bs}:
      C.hex(bs)

def main() -> String:
  shown(C.crypt(key(), 4294967295, nonce(), []))

#|""
