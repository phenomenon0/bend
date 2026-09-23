# The naive F32 sum of kulisch_big's data, cut at 2^4 and at 2^10 leaves.
# Measured: exact 0xbe9ac177 (-0.302), tree4 0x3bdda8fe (+0.0068), tree10
# 0x3b0c3ca8 (+0.0021) -- the sign is wrong, and the tree shape moves it.
import Base
import ./kulisch.bend as K

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("naive tree4 " ++ K.hex(F32.bits(K.naive(4n, 7, 0, 67108864))) ++ " tree10 "
      ++ K.hex(F32.bits(K.naive(10n, 7, 0, 67108864))))
