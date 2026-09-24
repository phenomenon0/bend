# F06: a destructuring let of a call's result is refused with the match
# rule's message ("a match cannot scrutinize a computed value"), though
# it is written as a let; the pair must first get its own def.
import Base

def two(x: U32) -> U32 & U32:
  (x, (x + 1 : U32))

def main() -> U32:
  (a, b) = two(1)
  (a + b : U32)

#|3
