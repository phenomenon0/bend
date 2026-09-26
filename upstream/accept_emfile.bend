# U13: TCP.accept when the process is out of descriptors. verify.sh runs
# it under `ulimit -n` low and peer.py hold opens 400 connections to
# 29613. Accepted sockets are kept (dropped, never closed), so the table
# fills; the first Fail prints its errno and message, and the listener,
# handed back beside it, still works: the program can tell EMFILE (24)
# from any other failure.
import Base

law fail_or:
  for l: Listener
  for n: Nat
  for r: Result<&1, &1, U32 & String, Socket>
  for k: Listener -> Nat -> IO(Unit)
  IO(Unit)

def fail_or(l, n, r, k):
  match r:
    case Done{s}:
      k(l, n)
    case Fail{e}:
      (code, message) = e
      do IO<Unit>:
        IO.print("accepted " ++ Nat.show(n) ++ ", then Fail " ++ U32.show(code)
          ++ ": " ++ message)
        Listener.close(l)

law step:
  for n: Nat
  for pr: Listener & Result<&1, &1, U32 & String, Socket>
  for k: Listener -> Nat -> IO(Unit)
  IO(Unit)

def step(n, pr, k):
  (l, r) = pr
  fail_or(l, n, r, k)

law loop:
  for fuel: Nat
  for n: Nat
  for l: Listener
  IO(Unit)

def loop(fuel, n, l):
  match fuel:
    case 0n:
      do IO<Unit>:
        IO.print("accepted " ++ Nat.show(n) ++ " with no Fail")
        Listener.close(l)
    case 1n+f:
      do IO<Unit>:
        pr : Listener & Result<&1, &1, U32 & String, Socket> <- TCP.accept(l)
        step(n, pr, m => c => loop(f, 1n+c, m))

law main:
  IO(Unit)

def main():
  do IO<Unit>:
    l : Listener <- IO.try(Listener, TCP.listen(29613))
    loop(600n, 0n, l)
