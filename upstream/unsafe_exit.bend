# U11: a false claim (0 == 1) "proved" by a recursion that never ends,
# which @unsafe lets past the termination check, passes
# `bend --check-only` with exit 0. The verdict line names it, but a CI
# that gates on the exit code sees a pass (WONTFIX #776, #805).
import Base

@unsafe
def zero_is_one(n: Nat) -> {0n == 1n : Nat}:
  zero_is_one(n)

def main() -> U32:
  7
