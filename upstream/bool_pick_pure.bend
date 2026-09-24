# U06, the lane that is lazy: a pure main runs in the checker's
# normalizer, which never evaluates the arm not taken (a recursion ten
# million deep here). Only the interp lane is asked; JS overflows its
# stack on this arm, and C evaluates it (see bool_pick.bend).
import Base

law deep:
  for n: Nat
  U32

def deep(n):
  match n:
    case 0n:
      0
    case 1n+p:
      U32.add(deep(p), 1)

def main() -> U32:
  Bool.pick(U32, True{}, 1, deep(10000000n))

#|1
