# pcg.bend at scale: 2^30 pairs (2^31 draws) of the one (42, 54) stream,
# 2^10 leaves each jumping to its own slice. Any --threads prints the same
# count, and it is the count a sequential loop over the stream would print.
import Base
import ./pcg.bend as P

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("hits " ++ U32.show(P.darts(10n, P.seed(42, 54), 1073741824)))
