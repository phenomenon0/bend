# kulisch.bend at scale: 2^26 draws (65,536 giant pairs in the sea), 2^10
# leaves. Any --threads prints the same bits. kulisch_drift.bend prints what a
# naive F32 sum of the same data says, at two tree shapes.
import Base
import ./kulisch.bend as K

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("exact " ++ K.hex(K.round(K.exact(10n, 7, 0, 67108864))))
