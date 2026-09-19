# the F64 kit mirrors the F32 kit of tests/base/num_kit.bend: min/max pick by
# is_lt in argument order, clamp bounds on both sides and passes the inside
# through, lerp is a + (b - a) * t, hypot is the 3-4-5 triangle, and round is
# floor(a + 0.5): halves go up, toward +inf on the negative side too
import Base

law main:
  IO(Unit)

def main():
  do IO<Unit>:
    IO.print(F64.show(F64.min(1.5d, 2.5d)))
    IO.print(F64.show(F64.min(2.5d, 1.5d)))
    IO.print(F64.show(F64.max(1.5d, 2.5d)))
    IO.print(F64.show(F64.max(2.5d, 1.5d)))
    IO.print(F64.show(F64.clamp(7.0d, 0.0d, 1.0d)))
    IO.print(F64.show(F64.clamp(F64.neg(3.0d), 0.0d, 1.0d)))
    IO.print(F64.show(F64.clamp(0.5d, 0.0d, 1.0d)))
    IO.print(F64.show(F64.lerp(0.0d, 10.0d, 0.25d)))
    IO.print(F64.show(F64.lerp(2.0d, 4.0d, 1.0d)))
    IO.print(F64.show(F64.square(3.0d)))
    IO.print(F64.show(F64.hypot(3.0d, 4.0d)))
    IO.print(F64.show(F64.round(2.5d)))
    IO.print(F64.show(F64.round(2.4d)))
    IO.print(F64.show(F64.round(F64.neg(2.5d))))

#|1.5
#|1.5
#|2.5
#|2.5
#|1
#|0
#|0.5
#|2.5
#|4
#|9
#|5
#|3
#|2
#|-2
