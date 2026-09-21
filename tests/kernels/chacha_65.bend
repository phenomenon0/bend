# RFC 8439 section 2.4.2 prefix: byte 65 must use counter 2.
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
  shown(C.keystream(key(), 1, nonce(), 65n))

#|"224f51f3401bd9e12fde276fb8631ded8c131f823d2c06e27e4fcaec9ef3cf788a3b0aa372600a92b57974cded2b9334794cba40c63e34cdea212c4cf07d41b769"
