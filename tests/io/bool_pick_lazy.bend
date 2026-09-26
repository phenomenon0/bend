# io: Bool.pick runs only its chosen arm under IO too, where the
# interpreter runs the program as JS: `spin` never ends, so a lane that
# built the other arm (a value or the action itself) would hang
import Base

@unsafe def spin(n: U32) -> U32:
  spin((n + 1 : U32))

def say(c: Bool, +n: U32) -> IO(Unit):
  Bool.pick(IO(Unit), c, IO.print(U32.show(n)), IO.print(U32.show(spin(n))))

def both(+t: U32) -> IO(Unit):
  do IO<Unit>:
    Unit <- say(True{}, (t + 1 : U32))
    say(Bool.not(False{}), (t + 2 : U32))

def main() -> IO(Unit):
  both(Bool.pick(U32, U32.is_lt(1, 2), 40, spin(0)))

#|41
#|42
