# NIST CAVS 11.0 SHA256ShortMsg.rsp, Len = 440 bits (byte-oriented).
import Base
import ../../demos/kernels/sha256.bend as S

def main() -> String:
  S.hash([62, 191, 176, 109, 184, 195, 141, 91, 160, 55, 241, 54, 62, 17, 133, 80,
    170, 217, 70, 6, 226, 104, 53, 160, 26, 240, 80, 120, 83, 60, 194, 95,
    47, 57, 87, 60, 4, 182, 50, 246, 47, 104, 194, 148, 171, 49, 242, 163,
    226, 161, 160, 216, 194, 190, 81])

#|"6595a2ef537a69ba8583dfbf7f5bec0ab1f93ce4c8ee1916eff44a93af5749c4"
