# power/exact.bend on a real file: `real_exact PATH`, PATH a little-endian
# float32 array. slurp.bend packs it so each cell IS one F32's bits, and
# Ex.sum adds them exactly over 2^10 leaves of the one buffer (Array.fork, no
# copy), rounding once. stdout: the count and the sum's bits; stderr: the
# phase times. real.sh checks the bits against Python's exact integer sum.
import Base
import ../../power/vec.bend as Vec
import ../../power/bytes.bend as Bytes
import ../../power/exact.bend as Ex
import ./slurp.bend as S

def ms(+a: Nat, +b: Nat) -> String:
  Nat.show(Nat.sub(b, a)) ++ " ms"

def fin(+t1: Nat, +n: U32, r: Vec.Vec & U32) -> IO(Unit):
  (v, +e) = r
  do IO<Unit>:
    t2 : Nat <- IO.now()
    IO.print("floats=" ++ U32.show(U32.shrn(n, 2n)) ++ " exact=" ++ U32.show(e))
    IO.print_err("sum " ++ ms(t1, t2))

def loaded(+t0: Nat, b: Bytes.Bytes) -> IO(Unit):
  match b:
    case Bytes.Bytes{+n, v}:
      do IO<Unit>:
        +t1 : Nat <- IO.now()
        IO.print_err("read " ++ ms(t0, t1))
        fin(t1, n, Ex.sum(v, 10n))

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
    b : Bytes.Bytes <- S.load(arg(args))
    loaded(t0, b)
