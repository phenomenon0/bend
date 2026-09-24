# lostupdate.bend at n = 8: all C(32, 16) = 601,080,390 schedules, 2^12 leaves.
# Any --threads prints the same histogram.
import Base
import ./lostupdate.bend as L

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(L.show(L.census(12n, 8), 8))
