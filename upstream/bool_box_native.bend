# U22: a Bool handed back by a polymorphic call (Bool.pick(Bool, ..)) fed
# to a native that takes Bools (Bool.or, Bool.xor): the C lane passes the
# box, the constructor's word, where the native wants 0/1. Every lane
# should print "TFTF".
import Base

def orp(+x: U32) -> Bool:
  Bool.or(False{}, Bool.pick(Bool, U32.is_ne(x, 0), False{}, U32.is_le(x, x)))

def xorp(+x: U32) -> Bool:
  Bool.xor(True{}, Bool.pick(Bool, U32.is_ne(x, 0), U32.is_le(x, x), U32.is_lt(x, x)))

def b(x: Bool) -> String:
  Bool.pick(String, x, "T", "F")

def main() -> String:
  b(orp(0)) ++ b(orp(3)) ++ b(xorp(0)) ++ b(xorp(3))
