# socket_drop: a Socket that goes out of scope without Socket.close.
# Each round connects to its own listener (port 29800), accepts, and
# drops both sockets: a match arm binds `s` and never uses it. Affine
# means "at most once", so the checker takes the drop with no erase and
# no warning; the runtime does nothing for it, so each round leaks two
# descriptors. verify.sh runs it under `ulimit -n 256`: 400 rounds need
# 800 descriptors if none is freed. After the rounds it sleeps 2 s, so
# /proc/PID/fd can be counted.
import Base

law fail:
  for n: Nat
  for l: Listener
  for e: U32 & String
  IO(Unit)

def fail(n, l, e):
  (code, message) = e
  do IO<Unit>:
    IO.print("round " ++ Nat.show(n) ++ ": Fail " ++ U32.show(code)
      ++ ": " ++ message)
    Listener.close(l)

law got:
  for n: Nat
  for pr: Listener & Result<&1, &1, U32 & String, Socket>
  for k: Listener -> IO(Unit)
  IO(Unit)

def got(n, pr, k):
  (l, r) = pr
  match r:
    case Done{s}:
      k(l)
    case Fail{e}:
      fail(n, l, e)

law dialed:
  for n: Nat
  for l: Listener
  for c: Result<&1, &1, U32 & String, Socket>
  for k: Listener -> IO(Unit)
  IO(Unit)

def dialed(n, l, c, k):
  match c:
    case Done{s}:
      do IO<Unit>:
        pr : Listener & Result<&1, &1, U32 & String, Socket> <- TCP.accept(l)
        got(n, pr, k)
    case Fail{e}:
      fail(n, l, e)

law loop:
  for fuel: Nat
  for +n: Nat
  for l: Listener
  IO(Unit)

def loop(fuel, n, l):
  match fuel:
    case 0n:
      do IO<Unit>:
        IO.print(Nat.show(n) ++ " rounds, no Fail")
        Unit <- IO.sleep(2000)
        Listener.close(l)
    case 1n+f:
      do IO<Unit>:
        c : Result<&1, &1, U32 & String, Socket> <-
          TCP.connect("127.0.0.1", 29800)
        dialed(n, l, c, m => loop(f, 1n+n, m))

law main:
  IO(Unit)

def main():
  do IO<Unit>:
    l : Listener <- IO.try(Listener, TCP.listen(29800))
    loop(400n, 0n, l)
