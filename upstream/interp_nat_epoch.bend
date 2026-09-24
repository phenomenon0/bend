# U16: a pure main's Nats are unary in the checker's normalizer, so an
# epoch-sized number (1.7*10^9 seconds) is unusable there: one addition
# and a division to minutes. JS and C answer at once.
import Base

def main() -> Nat:
  Nat.div(Nat.add(1700000000n, 60n), 60n)

#|28333334n
