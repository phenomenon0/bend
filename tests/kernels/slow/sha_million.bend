# RFC 6234 section 8.5 SHA256 test 3: one million copies of octet 0x61.
# Optional resource probe: bash tests/kernels/run.sh --million.
import Base
import ../../../demos/kernels/sha256.bend as S

# A tail-recursive producer: Base's List.replicate overflows the JS stack
# at this size before hashing starts. This still builds all million octets.
def copies(n: Nat, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      copies(p, 97 <> acc)

def main() -> String:
  S.hash(copies(1000000n, []))

#|"cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"
