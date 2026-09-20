import Base

# native-U64 lane test: 10M increments on BASE's U64 (not the package).

def loop(n: Nat, acc: U64) -> U64:
  match n:
    case 0n: acc
    case 1n+p: loop(p, U64.inc(acc))

def show(a: U64) -> Nat:
  match a:
    case U64{x}: Word.to_nat(64n, x)

def main() -> IO(Unit):
  do IO<Unit>:
    a : U64 = loop(10000000n, U64{Word.zero(64n)})
    u : Unit <- IO.print(String.append("u64 native sum: ", String.append(Nat.show(show(a)), "\n")))
    IO.print("NB-END\n")
