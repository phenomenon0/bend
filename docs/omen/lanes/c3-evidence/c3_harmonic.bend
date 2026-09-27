# The harmonic sum 1/1 + 1/2 + ... + 1/n in F32, added strictly left to right.
# Strict: every lane rounds the same n additions in the same order, so the bits
# are one answer. Under BEND_REASSOC=1 clang may split the chain into partial
# sums and add those at the end: a different rounding, by declaration.
import Base

def go(fuel: Nat, +i: U32, acc: F32) -> F32:
  match fuel:
    case 0n:
      acc
    case 1n++k:
      go(k, U32.inc(i), F32.add(acc, F32.div(1.0, U32.to_f32(i))))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(U32.show(F32.bits(go(10000000n, 1, 0.0))))
