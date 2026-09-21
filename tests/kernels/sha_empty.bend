# NIST CAVS 11.0 SHA256ShortMsg.rsp, Len = 0 bits (byte-oriented).
import Base
import ../../demos/kernels/sha256.bend as S

def main() -> String:
  S.hash([])

#|"e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
