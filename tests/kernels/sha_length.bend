# Contract: the high and low bit-count words serialize in big-endian order.
import Base
import ../../demos/kernels/sha256.bend as S

def texts(bs: List<&2, U32>) -> List<&2, String>:
  match bs:
    case Nil{}:
      []
    case b <> t:
      U32.show(b) <> texts(t)

def main() -> String:
  String.join(texts(
    List.append(&2, U32, S.big_endian(16909060), S.big_endian(2695938256))), ":")

#|"1:2:3:4:160:176:192:208"
