# U08: a match over IO.OP with a default arm. IO(A) is a CPS function,
# so running an action by hand gives its IO.OP: Emit, Halt, or a foreign
# request (IO.print's), which only the default arm can take. Pure Emit is
# 7; the print, taken by the default arm, is 0: 70 in all.
import Base

law got:
  for op: IO.OP<U32>
  U32

def got(op):
  match op:
    case Emit{value}:
      value
    case _:
      0

def main() -> U32:
  a = got(IO.pure(U32, 7, U32, x => Emit{x}))
  b = got(IO.print("hi", U32, x => Emit{5}))
  (a * 10 + b : U32)

#|70
