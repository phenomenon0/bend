# U16: `bend file.bend` on a pure main evaluates with the checker's own
# normalizer, where Nat.mul is Base's unary recursion: 2^20 * 2^20 (a
# literal-sized product, one instruction on the compiled lanes) does
# not finish. 2^10 * 2^10 is instant.
import Base

def main() -> Nat:
  Nat.mul(1048576n, 1048576n)

#|1099511627776n
