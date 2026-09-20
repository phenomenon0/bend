# Exact capacity is valid; capacity+1 must reject; length zero ignores storage.
import Base
import ../../demos/kernels/buffer.bend as B

def main() -> String:
  String.concat([B.hex(B.hash(ALeaf{1633837924}, 4n)), ":",
    B.hex(B.hash(ALeaf{1633837924}, 5n)), ":", B.hex(B.hash(ALeaf{4294967295}, 0n))])

#|"88d4266fd4e6338d13b845fcf289579d209c897823b9217da3e161936f031589:invalid length:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
