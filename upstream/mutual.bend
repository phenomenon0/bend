# F04: two defs that call each other, both laws declared first. The
# second def is not filled when the first is checked, so the first is
# refused: no mutual recursion, even with every signature above.
import Base

law even:
  for n: Nat
  Bool

law odd:
  for n: Nat
  Bool

def even(n):
  match n:
    case 0n:
      True{}
    case 1n+p:
      odd(p)

def odd(n):
  match n:
    case 0n:
      False{}
    case 1n+p:
      even(p)

def main() -> Bool:
  even(10n)

#|True{}
