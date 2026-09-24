# U10: the checker proves a Nat equation by unfolding both sides to
# successors, so a literal of 100000n in a proof overflows its stack. The
# same fact at 1000n checks at once.
import Base

law big:
  {Nat.add(50000n, 50000n) == 100000n : Nat}

def big():
  {==}

def main() -> U32:
  7

#|7
