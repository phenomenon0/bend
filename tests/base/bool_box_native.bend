# A Bool a polymorphic call hands back (Bool.pick(Bool, ..), its arms word
# compares, so the site is not lifted) fed to a native that takes Bools
# (Bool.or, Bool.xor). The C lane passed the box -- the constructor's word,
# not 0/1 -- straight to the native: `0 | box` read as False. Found by
# tests/fuzz (the C lane answered False where every other said True). The
# last case is the converse: a native's own Bool (U32.is_eq's 0/1), which
# the emitter labelled a box where the site's type was unknown, must not
# be read as a constructor.
import Base

def orp(+x: U32) -> Bool:
  Bool.or(False{}, Bool.pick(Bool, U32.is_ne(x, 0), False{}, U32.is_le(x, x)))

def xorp(+x: U32) -> Bool:
  Bool.xor(True{}, Bool.pick(Bool, U32.is_ne(x, 0), U32.is_le(x, x), U32.is_lt(x, x)))

def orq(+x: U64) -> Bool:
  Bool.or(Bool.pick(Bool, U64.is_zero(x), U64.is_le(x, x), False{}), False{})

def no(n: Nat) -> Bool:
  False{}

def raw(+n: Nat) -> Bool:
  no(n) || U32.is_eq(Bool.pick(U32, False{}, 0, 0), 65535)

def b(x: Bool) -> String:
  Bool.pick(String, x, "T", "F")

def main() -> String:
  +z : U64 = U64{Word.zero(64n)}
  b(orp(0)) ++ b(orp(3)) ++ b(xorp(0)) ++ b(xorp(3)) ++ b(orq(z)) ++ b(orq(U64.inc(z))) ++ b(raw(2n))

#|"TFTFTFF"
