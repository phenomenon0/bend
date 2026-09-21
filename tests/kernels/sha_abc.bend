# RFC 6234 section 8.5 SHA256 test 1; FIPS 180-4 algorithm.
import Base
import ../../demos/kernels/sha256.bend as S

def main() -> String:
  S.hash(S.octets("abc"))

#|"ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
