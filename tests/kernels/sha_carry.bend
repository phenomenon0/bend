# Contract: the C Length_Low + 8 carry, and big-endian length bytes.
import Base
import ../../demos/kernels/sha256.bend as S

def main() -> String:
  String.concat([U32.show(S.carry(4294967288, 7)), ":",
    S.hex_word(8n, U32.add(4294967288, 8), ""), ":",
    U32.show(S.carry(4294967280, 7))])

#|"8:00000000:7"
