import Base

def emit(name: String, x: F64) -> IO(Unit):
  IO.print(name ++ " " ++ F64.show(x))

def check(name: String, x: Bool) -> IO(Unit):
  IO.print(name ++ " " ++ Bool.show(x))

def infinity() -> F64:
  F64.div(1d, 0d)

def not_a_number() -> F64:
  F64.div(0d, 0d)

def main() -> IO(Unit):
  do IO<Unit>:
    emit("special_zero", 0.0d)
    emit("special_neg_zero", F64.neg(0.0d))
    check("special_zero_equal", F64.is_eq(F64.neg(0.0d), 0.0d))
    check("special_zero_not_less", F64.is_lt(F64.neg(0.0d), 0.0d))
    emit("special_double_neg_zero", F64.neg(F64.neg(0.0d)))
    emit("special_abs_neg_zero", F64.abs(F64.neg(0.0d)))
    emit("special_reciprocal_zero", infinity())
    emit("special_reciprocal_neg_zero", F64.div(1d, F64.neg(0d)))
    emit("special_overflow", F64.mul(1e308d, 10.0d))
    emit("special_neg_overflow", F64.mul(F64.neg(1e308d), 10d))
    emit("special_inf_add", F64.add(infinity(), 7d))
    emit("special_inf_opposite", F64.add(infinity(), F64.neg(infinity())))
    emit("special_inf_sub", F64.sub(infinity(), infinity()))
    emit("special_inf_zero_mul", F64.mul(infinity(), 0d))
    emit("special_inf_div", F64.div(infinity(), infinity()))
    emit("special_finite_div_inf", F64.div(1d, infinity()))
    emit("special_negative_div_inf", F64.div(F64.neg(1d), infinity()))
    emit("special_nan", not_a_number())
    emit("special_nan_add", F64.add(not_a_number(), 1d))
    emit("special_nan_mul", F64.mul(not_a_number(), 0d))
    emit("special_nan_div", F64.div(1d, not_a_number()))
    emit("special_sqrt_negative", F64.sqrt(F64.neg(1d)))
    check("special_nan_eq", F64.is_eq(not_a_number(), not_a_number()))
    check("special_nan_ne", F64.is_ne(not_a_number(), not_a_number()))
    check("special_nan_lt", F64.is_lt(not_a_number(), 0d))
    check("special_nan_le", F64.is_le(not_a_number(), 0d))
    check("special_nan_gt", F64.is_gt(0d, not_a_number()))
    check("special_nan_ge", F64.is_ge(0d, not_a_number()))
    check("special_inf_eq", F64.is_eq(infinity(), infinity()))
    check("special_inf_gt", F64.is_gt(infinity(), 1.7976931348623157e308d))
    check("special_neg_inf_lt", F64.is_lt(F64.neg(infinity()), F64.neg(1.7976931348623157e308d)))
    emit("special_mod_zero", F64.mod(1d, 0d))
    emit("special_mod_neg_zero", F64.mod(F64.neg(4d), 2d))
