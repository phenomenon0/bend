# U06: Bool.pick is an ordinary def, so a strict lane evaluates both arms
# before it picks one. The arm not taken is a 10^8-step loop (one that
# clang cannot fold away); the condition comes from IO.args(), so no lane
# can decide it early. The same pick written as a match on the Bool is
# timed beside it. Prints the two times, then "eager" when the pick costs
# more than ten times the match (and at least 10 ms), else "lazy".
import Base

law spin:
  for n: Nat
  for +acc: U32
  U32

def spin(n, acc):
  match n:
    case 0n:
      acc
    case 1n+p:
      spin(p, U32.add(U32.mul(acc, 1103515245), U32.add(acc, 12345)))

law empty:
  for xs: List<String>
  Bool

def empty(xs):
  match xs:
    case []:
      True{}
    case h <> t:
      False{}

law lazy:
  for c: Bool
  U32

def lazy(c):
  match c:
    case True{}:
      1
    case False{}:
      spin(Nat.mul(1000n, 100000n), 0)

law picked:
  for c: Bool
  IO(Unit)

def picked(c):
  IO.print_err(U32.show(Bool.pick(U32, c, 1, spin(Nat.mul(1000n, 100000n), 0))))

law matched:
  for c: Bool
  IO(Unit)

def matched(c):
  IO.print_err(U32.show(lazy(c)))

law verdict:
  for +a: Nat
  for +b: Nat
  IO(Unit)

def verdict(a, b):
  +cut = Nat.add(Nat.mul(b, 10n), 10n)
  do IO<Unit>:
    IO.print("pick " ++ Nat.show(a) ++ " ms, match " ++ Nat.show(b) ++ " ms")
    IO.print(Bool.pick(String, Nat.is_lt(cut, a), "eager", "lazy"))

law main:
  IO(Unit)

def main():
  do IO<Unit>:
    xs : List<String> <- IO.args()
    ys : List<String> <- IO.args()
    t0 : Nat <- IO.now()
    picked(empty(xs))
    +t1 : Nat <- IO.now()
    matched(empty(ys))
    t2 : Nat <- IO.now()
    verdict(Nat.sub(t1, t0), Nat.sub(t2, t1))

#|pick 0 ms, match 0 ms
#|lazy
