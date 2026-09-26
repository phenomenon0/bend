# U03t: 16384 computations sleep 2 s while main takes 4000 zero sleeps,
# a pass through the loop each. A loop that keeps deadlines in a heap
# costs what is due per pass and prints "flat" (the 4000 passes take a
# few ms); one that walks every sleeper per pass takes seconds and prints
# "slow: N ms". The same program is upstream/03b-epoll-timers's test
# io/sleep_many_waiters.
import Base

law spin:
  for n: Nat
  IO(Unit)

def spin(n):
  match n:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+p:
      do IO<Unit>:
        Unit <- IO.sleep(0)
        spin(p)

law park:
  for n: Nat
  IO(Unit)

def park(n):
  match n:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+p:
      do IO<Unit>:
        Unit <- IO.spawn(Unit, IO.sleep(2000))
        park(p)

law verdict.go:
  for fast: Bool
  for ms: Nat
  String

def verdict.go(fast, ms):
  match fast:
    case True{}:
      "flat"
    case False{}:
      "slow: " ++ Nat.show(ms) ++ " ms"

law verdict:
  for +ms: Nat
  String

def verdict(ms):
  verdict.go(Nat.is_lt(ms, 1000n), ms)

law main:
  IO(U32)

def main():
  do IO<U32>:
    Unit <- park(16384n)
    t0 : Nat <- IO.now()
    Unit <- spin(4000n)
    t1 : Nat <- IO.now()
    Unit <- IO.print(verdict(Nat.sub(t1, t0)))
    return 0

