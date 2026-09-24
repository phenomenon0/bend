# U10b: a Nat literal stops at 2^32-1, while the runtime holds a Nat to
# 2^48-1 (WONTFIX #779); 2^40 must be spelt Nat.mul(1048576n, 1048576n).
import Base

def main() -> Nat:
  1099511627776n

#|1099511627776n
