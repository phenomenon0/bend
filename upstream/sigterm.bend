# U07: a long IO loop (200 sleeps of 100 ms) that verify.sh sends SIGTERM
# after 1.5 s. Base has no signal effect, so the default action must end
# the process at once, in every lane.
import Base

law nap:
  for n: Nat
  IO(Unit)

def nap(n):
  match n:
    case 0n:
      IO.print("ran to the end")
    case 1n+p:
      do IO<Unit>:
        IO.sleep(100)
        nap(p)

law main:
  IO(Unit)

def main():
  nap(200n)
