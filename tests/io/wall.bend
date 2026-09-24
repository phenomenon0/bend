# io (io_wall): IO.wall is the wall clock, ms since the Unix epoch: past
# 2020-01-01 and before 2100 (so no clock since boot, and no seconds or
# microseconds), and the dates bend2/time.bend prints of it are of this
# century
import Base
import ../../bend2/time.bend as Time

def sane(+t: Nat) -> String:
  +s = Nat.div(t, 1000n)
  Bool.pick(String, Nat.is_lt(1577836800n, s) && Nat.is_lt(s, 4102444800n),
    String.take(Time.iso.ms(t), 2n) ++ " " ++ U32.show(U32.from_nat(String.length(Time.iso.ms(t))))
      ++ " " ++ String.drop(Time.http(s), 26n),
    "not a wall clock: " ++ Nat.show(t))

def main() -> IO(Unit):
  do IO<Unit>:
    +a : Nat <- IO.wall()
    b : Nat <- IO.wall()
    u : Unit <- IO.print(sane(a))
    IO.print(Bool.pick(String, Nat.is_le(a, b), "later", "earlier"))

#|20 24 GMT
#|later
