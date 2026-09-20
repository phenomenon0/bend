# RFC 8439 section 2.1.1: little-endian bytes of all four result words.
import Base
import ../../demos/kernels/chacha20.bend as C

def shown(q: C.Quad) -> String:
  match q:
    case C.Quad{a, b, c, d}:
      String.concat([C.hex(C.little(a)), C.hex(C.little(b)),
        C.hex(C.little(c)), C.hex(C.little(d))])

def main() -> String:
  shown(C.quarter(286331153, 16909060, 2609737539, 19088743))

#|"f4922aeacef81ccb2e478145bbc48158"
