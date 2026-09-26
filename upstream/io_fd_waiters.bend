# U03: a pass through the IO loop walks every computation parked on a
# descriptor (select: size a set, fill it, walk it again), so each wake
# costs O(parked) and a server that accepts n connections pays O(n^2).
# 2000 zero sleeps (a pass each) are timed alone, then beside 4000
# clients parked in TCP.recv. A loop that costs what is ready prints a
# ratio near 1. Port 29603.
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

law timed:
  IO(Nat)

def timed():
  do IO<Nat>:
    t0 : Nat <- IO.now()
    spin(2000n)
    t1 : Nat <- IO.now()
    return Nat.sub(t1, t0)

law client:
  IO(Unit)

def client():
  do IO<Unit>:
    s : Socket <- IO.try(Socket, TCP.connect("127.0.0.1", 29603))
    m : Socket & Result<&1, &1, U32 & String, String> <- TCP.recv(s, 16)
    return Unit{}

law accepted:
  for pr: Listener & Result<&1, &1, U32 & String, Socket>
  for k: Listener -> IO(Listener)
  IO(Listener)

def accepted(pr, k):
  (l, r) = pr
  k(l)

law accepts:
  for n: Nat
  for l: Listener
  IO(Listener)

def accepts(n, l):
  match n:
    case 0n:
      IO.pure(Listener, l)
    case 1n+p:
      do IO<Listener>:
        IO.spawn(Unit, client())
        pr : Listener & Result<&1, &1, U32 & String, Socket> <- TCP.accept(l)
        accepted(pr, m => accepts(p, m))

law report:
  for +a: Nat
  for +b: Nat
  IO(Unit)

def report(a, b):
  +x = Nat.add(a, 1n)
  IO.die(Unit, 0, "alone " ++ Nat.show(a) ++ " ms, beside 4000: "
    ++ Nat.show(b) ++ " ms, ratio " ++ Nat.show(Nat.div(b, x)))

law main:
  IO(Unit)

def main():
  do IO<Unit>:
    a : Nat <- timed()
    l : Listener <- IO.try(Listener, TCP.listen(29603))
    l : Listener <- accepts(4000n, l)
    IO.sleep(200)
    b : Nat <- timed()
    report(a, b)
