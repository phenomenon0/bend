import Base

def f(a: U32, b: U32) -> U32:
  U32.add(a, b)

def main() -> IO(Unit):
  do IO<Unit>:
    a : U32 = f(1, 2)
    u : Unit <- IO.print(String.append(Nat.show(U32.to_nat(a)), "\n"))
    IO.print("W2-END\n")
