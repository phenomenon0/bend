# U09: a def used above its definition is refused with the message a
# misspelt name gets ("expected : a defined name"): nothing says the name
# exists, only further down. Compare def_typo.bend.
import Base

def main() -> U32:
  helper(1)

def helper(x: U32) -> U32:
  (x + 1 : U32)
