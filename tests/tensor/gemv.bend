import Base
import ../../demos/tensor/tensor.bend as T

# A is 3x4 at 0, x is 4 at 12, y is 3 at 16, all in one block of 32 cells.
def fill(fuel: Nat, +i: U32, t: T.Ten) -> T.Ten:
  match fuel:
    case 0n:
      t
    case 1n++k:
      fill(k, U32.inc(i), T.put(t, i, U32.to_f32(U32.inc(i))))

def xs(fuel: Nat, +i: U32, t: T.Ten) -> T.Ten:
  match fuel:
    case 0n:
      t
    case 1n++k:
      xs(k, U32.inc(i), T.put(t, U32.add(i, 12), U32.to_f32(U32.inc(i))))

type Sum is Type:
  Sum{t: T.Ten, acc: U32}

def sum.add(+acc: U32, r: T.Ten & F32) -> Sum:
  (t, x) = r
  Sum{t, U32.add(U32.mul(acc, 1000), F32.to_u32(x))}

def sum.go(fuel: Nat, +i: U32, s: Sum) -> Sum:
  match fuel:
    case 0n:
      s
    case 1n++k:
      match s:
        case Sum{t, acc}:
          sum.go(k, U32.inc(i), sum.add(acc, T.get(t, i)))

def sum.out(s: Sum) -> U32:
  match s:
    case Sum{t, acc}:
      acc

law main:
  IO(Unit)

def main():
  do IO<Unit>:
    IO.print(U32.show(sum.out(sum.go(3n, 16, Sum{
      T.gemv(xs(4n, 0, fill(12n, 0, T.zeros(5n))), T.mat(0, 3, 4, 4), T.vec(12, 4), T.vec(16, 3)),
      0}))))

#|30070110
