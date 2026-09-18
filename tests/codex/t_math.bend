import Base

def emit(name: String, x: F64) -> IO(Unit):
  IO.print(name ++ " " ++ F64.show(x))

# Truncate positive transcendental results at nine decimal places so a last-bit
# libm difference does not turn a correct implementation into a string failure.
def scaled(name: String, x: F64) -> IO(Unit):
  IO.print(name ++ " " ++ U32.show(F64.to_u32(F64.mul(x, 1e9d))))

def check(name: String, x: Bool) -> IO(Unit):
  IO.print(name ++ " " ++ Bool.show(x))

def main() -> IO(Unit):
  do IO<Unit>:
    emit("math_neg", F64.neg(1.25d))
    emit("math_abs", F64.abs(F64.neg(3.5d)))
    emit("math_mod", F64.mod(5.5d, 2d))
    emit("math_mod_negative", F64.mod(F64.neg(5.5d), 2d))
    emit("math_mod_negative_divisor", F64.mod(5.5d, F64.neg(2d)))
    emit("math_pow_negative", F64.pow(F64.neg(2d), 3d))
    emit("math_sqrt", F64.sqrt(2d))
    scaled("math_atan2_scaled", F64.atan2(1d, F64.neg(1d)))
    scaled("math_exp_scaled", F64.exp(1d))
    scaled("math_log_scaled", F64.log(2d))
    scaled("math_log2_scaled", F64.log2(3d))
    scaled("math_log10_scaled", F64.log10(2d))
    scaled("math_sin_scaled", F64.sin(1d))
    scaled("math_cos_scaled", F64.cos(1d))
    scaled("math_tan_scaled", F64.tan(1d))
    scaled("math_asin_scaled", F64.asin(0.5d))
    scaled("math_acos_scaled", F64.acos(0.5d))
    scaled("math_atan_scaled", F64.atan(1d))
    scaled("math_sinh_scaled", F64.sinh(1d))
    scaled("math_cosh_scaled", F64.cosh(1d))
    scaled("math_tanh_scaled", F64.tanh(1d))
    emit("math_floor_negative", F64.floor(F64.neg(3.9d)))
    emit("math_ceil_negative", F64.ceil(F64.neg(3.9d)))
    emit("math_trunc_negative", F64.trunc(F64.neg(3.9d)))
    emit("math_floor_positive", F64.floor(3.9d))
    emit("math_ceil_positive", F64.ceil(3.9d))
    emit("math_trunc_neg_fraction", F64.trunc(F64.neg(0.5d)))
    emit("math_pi", F64.pi())
    check("math_eq", F64.is_eq(1d, 1d))
    check("math_ne", F64.is_ne(1d, 2d))
    check("math_lt", F64.is_lt(1d, 2d))
    check("math_le_equal", F64.is_le(1d, 1d))
    check("math_gt", F64.is_gt(2d, 1d))
    check("math_ge_equal", F64.is_ge(2d, 2d))
