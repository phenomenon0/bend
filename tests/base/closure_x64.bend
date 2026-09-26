# A closure over an F64 (or a U64, an I64), dropped without being applied.
# A dropped closure drops its node's words as Terms; the C lane kept a
# 64-bit capture raw there, and a double's bits read as a Term are a wild
# reference: "memory fault", or under ASan an index 50436 out of bounds in
# term_drop. Found by tests/fuzz. Applied, the same closures answer.
import Base

def drop(f: U32 -> U32) -> Nat:
  0n

def app(f: U32 -> U32, x: U32) -> U32:
  f(x)

def pick(c: Bool, f: U32 -> U32, g: U32 -> U32) -> U32:
  match c:
    case True{}:
      f(1)
    case False{}:
      g(2)

def out() -> String:
  +v : F64 = F64.atan2(7.25d, 0.0d)
  +u : U64 = U64.not(U64.shln(U64.inc(U64{Word.zero(64n)}), 5n))
  +i : I64 = I64.neg(I64.inc(I64{Word.zero(64n)}))
  Nat.show(drop(x => F64.to_u32(v))) ++ " " ++ Nat.show(drop(x => Bool.to_u32(U64.is_zero(u))))
    ++ " " ++ Nat.show(drop(x => Bool.to_u32(I64.is_neg(i)))) ++ " "
    ++ U32.show(app(x => F64.to_u32(F64.add(v, v)), 1)) ++ " "
    ++ U32.show(pick(True{}, x => (x + F64.to_u32(v) : U32), y => Bool.to_u32(U64.is_zero(u)))) ++ " "
    ++ U32.show(pick(False{}, x => F64.to_u32(v), y => (y + Bool.to_u32(I64.is_neg(i)) : U32)))

# an IO main: the checker's normalizer holds F64 opaque
def main() -> IO(Unit):
  IO.print(out())

#|0 0 0 3 2 3
