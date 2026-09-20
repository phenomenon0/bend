import Base
# The control for nbench.bend: S64 is U64's exact twin -- the same
# Word(64n) field, the same inc -- declared locally, so it is NOT in the
# compiler's WORDS/OPTIMIZED tables and stays a heap node with a 64-cell
# bit spine. This is what U64 was before this lane, and the gap between
# the two files is the lane's whole result.
#
# Expected output: "s64 struct sum: 10000000" then "NB-END".

type S64 is Data:
  S64{data: Word(64n)}

def S64.inc(a: S64) -> S64:
  match a:
    case S64{x}:
      S64{Word.inc(64n, x)}

def loop(n: Nat, acc: S64) -> S64:
  match n:
    case 0n:
      acc
    case 1n+p:
      loop(p, S64.inc(acc))

def out(a: S64) -> Nat:
  match a:
    case S64{x}:
      Word.to_nat(64n, x)

def main() -> IO(Unit):
  do IO<Unit>:
    a : S64 = loop(10000000n, S64{Word.zero(64n)})
    u : Unit <- IO.print(String.append("s64 struct sum: ", Nat.show(out(a))))
    IO.print("NB-END")
