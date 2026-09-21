# NIST CAVS 11.0 SHA256ShortMsg.rsp, Len = 8 bits (byte-oriented).
import Base
import ../../demos/kernels/sha256.bend as S

def main() -> String:
  S.hash([211])

#|"28969cdfa74a12c82f3bad960b0b000aca2ac329deea5c2328ebc6f2ba9802c1"
