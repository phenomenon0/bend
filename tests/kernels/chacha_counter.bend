# RFC 8439 section 2.4.2: two complete blocks; counter 1 then 2.
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
  shown(C.keystream(key(), 1, nonce(), 128n))

#|"224f51f3401bd9e12fde276fb8631ded8c131f823d2c06e27e4fcaec9ef3cf788a3b0aa372600a92b57974cded2b9334794cba40c63e34cdea212c4cf07d41b769a6749f3f630f4122cafe28ec4dc47e26d4346d70b98c73f3e9c53ac40c5945398b6eda1a832c89c167eacd901d7e2bf363740373201aa188fbbce83991c4ed"
