# U03: a pass through the IO loop walks every parked computation, so
# each wake costs O(parked) and n arrivals cost O(n^2). The same 2000
# zero sleeps (a pass each) are timed alone, then beside 20000 parked
# sleepers. A loop that costs what is ready prints a ratio near 1.
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
        IO.sleep(0)
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
        IO.spawn(Unit, IO.sleep(20000))
        park(p)

law timed:
  IO(Nat)

def timed():
  do IO<Nat>:
    t0 : Nat <- IO.now()
    spin(2000n)
    t1 : Nat <- IO.now()
    return Nat.sub(t1, t0)

law report:
  for +a: Nat
  for +b: Nat
  IO(Unit)

def report(a, b):
  +x = Nat.add(a, 1n)
  IO.die(Unit, 0, "alone " ++ Nat.show(a) ++ " ms, beside 20000: "
    ++ Nat.show(b) ++ " ms, ratio " ++ Nat.show(Nat.div(b, x)))

law main:
  IO(Unit)

def main():
  do IO<Unit>:
    a : Nat <- timed()
    park(20000n)
    IO.sleep(500)
    b : Nat <- timed()
    report(a, b)
