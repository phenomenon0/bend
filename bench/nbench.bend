import Base
# The native-U64 measurement: 10,000,000 U64.inc on Base's U64. The
# accumulator is built ONCE (U64{Word.zero(64n)}) because Bend is affine --
# a loop cannot carry a constant without re-deriving it, and re-deriving
# the zero per iteration would allocate 64 Word cells and measure that
# instead. The sum is printed through Nat.show(Word.to_nat(..)) so the
# result is observed and the loop cannot be dropped as dead.
#
# nbench_str.bend is the same loop over an UNREGISTERED copy of the type:
# the before-number. nbench.c is the machine baseline.
#
# Expected output: "u64 native sum: 10000000" then "NB-END".

def loop(n: Nat, acc: U64) -> U64:
  match n:
    case 0n:
      acc
    case 1n+p:
      loop(p, U64.inc(acc))

def out(a: U64) -> Nat:
  match a:
    case U64{x}:
      Word.to_nat(64n, x)

def main() -> IO(Unit):
  do IO<Unit>:
    a : U64 = loop(10000000n, U64{Word.zero(64n)})
    u : Unit <- IO.print(String.append("u64 native sum: ", Nat.show(out(a))))
    IO.print("NB-END")
