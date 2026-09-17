import Base

def emit(name: String, x: F64) -> IO(Unit):
  IO.print(name ++ " " ++ F64.show(x))

# Match only the helper's parameter; keep Some/None visible in the output.
def parsed(name: String, result: Maybe<&2, F64>) -> IO(Unit):
  match result:
    case None{}:
      IO.print(name ++ " None")
    case Some{x}:
      IO.print(name ++ " Some(" ++ F64.show(x) ++ ")")

def main() -> IO(Unit):
  do IO<Unit>:
    emit("text_integer", 42.0d)
    emit("text_small_fixed", 1e-6d)
    emit("text_small_scientific", 1e-7d)
    emit("text_large_fixed", 1e20d)
    emit("text_large_scientific", 1e21d)
    emit("text_negative_fixed", F64.neg(1e20d))
    emit("text_negative_scientific", F64.neg(1e-7d))
    parsed("read_decimal", F64.read("0.30000000000000004"))
    parsed("read_integer", F64.read("7"))
    parsed("read_exponent", F64.read("1.5e3"))
    parsed("read_integer_exponent", F64.read("2E+3"))
    parsed("read_subnormal", F64.read("5e-324"))
    parsed("read_max_finite", F64.read("1.7976931348623157e308"))
    parsed("read_neg_zero", F64.read("-0"))
    parsed("read_neg_zero_decimal", F64.read("-0.0"))
    parsed("read_inf", F64.read("inf"))
    parsed("read_neg_inf", F64.read("-inf"))
    parsed("read_nan", F64.read("nan"))
    parsed("read_overflow", F64.read("1e309"))
    parsed("read_underflow", F64.read("1e-400"))
    parsed("read_neg_underflow", F64.read("-1e-400"))
    parsed("read_halfway_even", F64.read("1.00000000000000011102230246251565404236316680908203125"))
    parsed("read_above_halfway", F64.read("1.00000000000000011102230246251565404236316680908203126"))
    parsed("read_empty", F64.read(""))
    parsed("read_spaces_only", F64.read("   "))
    parsed("read_junk", F64.read("hello"))
    parsed("read_trailing_junk", F64.read("1.25junk"))
    parsed("read_incomplete_exp", F64.read("1e"))
    parsed("read_incomplete_sign", F64.read("+"))
    parsed("read_literal_suffix", F64.read("1.5d"))
    parsed("read_embedded_nul", F64.read("1\0junk"))
    parsed("read_hex", F64.read("0x1p0"))
    parsed("read_underscore", F64.read("1_000"))
    parsed("roundtrip_sum", F64.read(F64.show(F64.add(0.1d, 0.2d))))
    parsed("roundtrip_third", F64.read(F64.show(F64.div(1d, 3d))))
    parsed("roundtrip_subnormal", F64.read(F64.show(5e-324d)))
    parsed("roundtrip_neg_zero", F64.read(F64.show(F64.neg(0d))))
    parsed("roundtrip_inf", F64.read(F64.show(F64.div(1d, 0d))))
    parsed("roundtrip_nan", F64.read(F64.show(F64.div(0d, 0d))))
