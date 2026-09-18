import Base

def emit(name: String, x: F64) -> IO(Unit):
  IO.print(name ++ " " ++ F64.show(x))

def main() -> IO(Unit):
  do IO<Unit>:
    emit("round_sum", (0.1d + 0.2d : F64))
    emit("round_third", (1.0d / 3.0d : F64))
    emit("round_pow_half", F64.pow(2.0d, 0.5d))
    emit("round_large_swallow", (1e16d + 1.0d : F64))
    emit("round_large_cancel", F64.sub(F64.add(1e16d, 1d), 1e16d))
    emit("round_large_next", F64.add(1e16d, 2d))
    emit("round_tie_even_down", F64.add(1d, 1.1102230246251565e-16d))
    emit("round_tie_even_up", F64.add(1.0000000000000002d, 1.1102230246251565e-16d))
    emit("round_subnormal", 5e-324d)
    emit("round_subnormal_double", F64.add(5e-324d, 5e-324d))
    emit("round_subnormal_half", F64.mul(5e-324d, 0.5d))
    emit("round_subnormal_tie", F64.mul(5e-324d, 1.5d))
    emit("round_subnormal_div", F64.div(5e-324d, 2d))
    emit("round_subnormal_neg_div", F64.div(F64.neg(5e-324d), 2d))
    emit("round_min_normal", 2.2250738585072014e-308d)
    emit("round_below_normal", F64.sub(2.2250738585072014e-308d, 5e-324d))
    emit("round_recover_normal", F64.mul(F64.div(2.2250738585072014e-308d, 2d), 2d))
    emit("round_integer_literal", 2d)
    emit("round_decimal_exponent", 1.5e3d)
    emit("round_integer_exponent", 2E+3d)
    emit("round_max_finite", 1.7976931348623157e308d)
    emit("round_max_overflow", F64.mul(1.7976931348623157e308d, 2d))
    emit("round_above_f32_integer", 16777217d)
    emit("round_last_exact_integer", 9007199254740991d)
    emit("round_integer_tie", 9007199254740993d)
