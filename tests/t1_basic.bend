import Base

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(F64.show(F64.add(0.1d, 0.2d)))
    IO.print(F64.show(F64.sqrt(2.0d)))
    IO.print(F64.show(F64.pi()))
    IO.print(U32.show(F64.to_u32(3.9d)))
    IO.print(F64.show(F64.sub(1.0d, 0.1d)))
