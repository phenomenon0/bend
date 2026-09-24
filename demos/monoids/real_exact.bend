# power/exact.bend on a real file: `real_exact PATH`, PATH a little-endian
# float32 array. slurp.bend reads it as Base's Bytes(), and Ex.sum_bytes adds
# its words exactly over 2^10 leaves sharing the one buffer, rounding once.
# stdout: the count and the sum's bits; stderr: the phase times. real.sh
# checks the bits against Python's exact integer sum.
import Base
import ../../power/exact.bend as Ex
import ./slurp.bend as S

def ms(+a: Nat, +b: Nat) -> String:
  Nat.show(Nat.sub(b, a)) ++ " ms"

def fin(+t1: Nat, +n: Nat, +e: U32) -> IO(Unit):
  do IO<Unit>:
    t2 : Nat <- IO.now()
    IO.print("floats=" ++ Nat.show(Nat.div(n, 4n)) ++ " exact=" ++ U32.show(e))
    IO.print_err("sum " ++ ms(t1, t2))

def loaded(+t0: Nat, +b: Bytes()) -> IO(Unit):
  do IO<Unit>:
    +t1 : Nat <- IO.now()
    IO.print_err("read " ++ ms(t0, t1))
    fin(t1, Bytes.len(b), Ex.sum_bytes(b, 10n))

def arg(xs: List<String>) -> String:
  match xs:
    case Nil{}:
      "/dev/null"
    case Con{x, t}:
      x

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    t0 : Nat <- IO.now()
    b : Bytes() <- S.load(arg(args))
    loaded(t0, b)
