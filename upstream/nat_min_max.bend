# U04: Nat.min and Nat.max are Base's unary recursions, and no lane runs
# them natively (Nat.add and Nat.sub are native). On 2^40 they peel one
# successor per step: a trillion steps for what is one comparison.
import Base

def main() -> String:
  +big = Nat.mul(1048576n, 1048576n)
  +one = Nat.add(big, 1n)
  Nat.show(Nat.min(big, one)) ++ " " ++ Nat.show(Nat.max(one, big))

#|"1099511627776 1099511627777"
