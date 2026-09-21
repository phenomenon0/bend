# NIST CAVS 11.0 SHA256ShortMsg.rsp, Len = 448 bits (byte-oriented).
import Base
import ../../demos/kernels/sha256.bend as S

def main() -> String:
  S.hash([45, 82, 68, 125, 18, 68, 210, 235, 194, 134, 80, 231, 176, 86, 84, 186,
    211, 91, 58, 104, 238, 220, 127, 133, 21, 48, 107, 73, 109, 117, 243, 231,
    51, 133, 221, 27, 0, 38, 37, 2, 75, 129, 160, 47, 47, 214, 223, 251,
    110, 109, 86, 28, 183, 208, 189, 122])

#|"cfb88d6faf2de3a69d36195acec2e255e2af2b7d933997f348e09f6ce5758360"
