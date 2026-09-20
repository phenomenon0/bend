import Base

def show(a: U64) -> Nat:
  match a:
    case U64{x}: Word.to_nat(64n, x)

def main() -> IO(Unit):
  do IO<Unit>:
    a : U64 = U64.inc(U64{Word.zero(64n)})
    u : Unit <- IO.print(String.append("inc: ", String.append(Nat.show(show(a)), "\n")))
    IO.print("T1-END\n")
