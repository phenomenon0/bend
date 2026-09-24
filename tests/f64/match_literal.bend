# An F64 literal pattern matches the word's bits, on every lane: 1.5 and 2.5
# take their arms, 3.5 the default, 0.0 its arm, and -0.0 -- equal to 0.0 as a
# number, a different word -- the default. The C lane once had no layout for
# an F64 word match and stopped the compiler (the 2.0.26 sync's w64 path
# covered U64 and I64 only).
import Base

def f(x: F64) -> U32:
  match x:
    case 1.5d:
      1
    case 2.5d:
      2
    case 0.0d:
      3
    case _:
      9

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(U32.show(f(1.5d)) ++ U32.show(f(2.5d)) ++ U32.show(f(3.5d)) ++ U32.show(f(0.0d))
      ++ U32.show(f(F64.neg(0.0d))))

#|12939
