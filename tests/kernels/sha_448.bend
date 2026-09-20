# RFC 6234 section 8.5 SHA256 test 2: 448 bits need two padded blocks.
import Base
import ../../demos/kernels/sha256.bend as S

def main() -> String:
  S.hash(S.octets("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"))

#|"248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
