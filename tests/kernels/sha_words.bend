# RFC 6234 abc; nonzero discarded low byte and unused capacity must be ignored.
import Base
import ../../demos/kernels/buffer.bend as B

def main() -> String:
  B.hex(B.hash(ANode{ALeaf{1633838079}, ALeaf{4294967295}}, 3n))

#|"ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
