import Base

# Nat.min and Nat.max run natively on the compiled lanes and as their Bend
# bodies in the checker; every lane must print the same answers, at zero,
# at equality, both ways round, and past 2^16

def main() -> String:
  +big = Nat.add(65536n, 4464n)
  +one = Nat.add(big, 1n)
  Nat.show(Nat.min(0n, 0n)) ++ " " ++ Nat.show(Nat.max(0n, 0n)) ++ " "
    ++ Nat.show(Nat.min(0n, 7n)) ++ " " ++ Nat.show(Nat.max(0n, 7n)) ++ " "
    ++ Nat.show(Nat.min(7n, 0n)) ++ " " ++ Nat.show(Nat.max(7n, 0n)) ++ " "
    ++ Nat.show(Nat.min(5n, 5n)) ++ " " ++ Nat.show(Nat.max(5n, 5n)) ++ " "
    ++ Nat.show(Nat.min(big, one)) ++ " " ++ Nat.show(Nat.max(one, big))

#|"0 0 0 7 0 7 5 5 70000 70001"
