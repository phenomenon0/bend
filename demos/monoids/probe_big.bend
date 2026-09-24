# probe.bend at scale: 2^24 slots, 2^28 hash values run backwards per pass,
# 2^10 leaves, at four loads. Any --threads prints the same lines.
import Base
import ./probe.bend as P

def line(+pct: U32) -> String:
  +n = U32.div(U32.mul(16777216, pct), 100)
  P.show(P.ring(10n, 24, n, 28), 24, n, True{})

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(line(50))
    IO.print(line(75))
    IO.print(line(85))
    IO.print(line(95))
