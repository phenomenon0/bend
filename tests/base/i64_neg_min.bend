# I64.neg of the minimum is the minimum (two's complement wraps). The C
# lane negated through int64_t, which overflows there: undefined, so clang
# may fold -x == x to x == 0. Found by tests/fuzz under UBSan ("negation of
# -9223372036854775808 cannot be represented in type 'int64_t'").
import Base

def i_min() -> I64:
  I64{I64.sign_mask()}

def fixed(+x: I64) -> Bool:
  I64.is_eq(I64.neg(x), x)

def bn(b: Bool) -> String:
  Bool.pick(String, b, "T", "F")

def main() -> String:
  bn(fixed(i_min())) ++ bn(fixed(I64.inc(i_min()))) ++ bn(fixed(I64.sub(i_min(), i_min())))
    ++ bn(I64.is_neg(I64.neg(i_min()))) ++ bn(I64.is_lt(I64.neg(i_min()), I64.neg(I64.inc(i_min()))))

#|"TFTTT"
