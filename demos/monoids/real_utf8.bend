# power/utf8.bend on a real file: `real_utf8 PATH`. Reads PATH into Bytes
# (64 KiB chunks, packed four bytes to a cell), then validates it with
# U.check and finds its first bad byte with U.first_bad, both over 2^10 leaves
# of the one buffer (Array.fork, no copy). stdout is the verdict; stderr has
# the phase times from IO.now. real.sh compares the verdict with CPython's
# decoder on the same file.
import Base
import ../../power/vec.bend as Vec
import ../../power/bytes.bend as Bytes
import ../../power/utf8.bend as U
import ./slurp.bend as S

def ms(+a: Nat, +b: Nat) -> String:
  Nat.show(Nat.sub(b, a)) ++ " ms"

def said(+m: U32, +c: U32) -> String:
  "valid=" ++ Bool.pick(String, U.valid(m), "yes", "no") ++ " scalars=" ++ U32.show(c)

def fin(+t1: Nat, +t2: Nat, what: String, r: Bytes.Bytes & U32) -> IO(Unit):
  (b, +p) = r
  do IO<Unit>:
    t3 : Nat <- IO.now()
    IO.print(what ++ " first_bad=" ++ Bool.pick(String, U32.is_eq(p, U.none()), "-", U32.show(p)))
    IO.print_err("check " ++ ms(t1, t2) ++ ", first_bad " ++ ms(t2, t3))

def checked(+t1: Nat, r: Bytes.Bytes & U.Sum) -> IO(Unit):
  (b, s) = r
  match s:
    case U.Sum{+m, +c}:
      do IO<Unit>:
        t2 : Nat <- IO.now()
        fin(t1, t2, said(m, c), U.first_bad(b, 10n))

def loaded(+t0: Nat, b: Bytes.Bytes) -> IO(Unit):
  do IO<Unit>:
    +t1 : Nat <- IO.now()
    IO.print_err("read " ++ ms(t0, t1))
    checked(t1, U.check(b, 10n))

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
