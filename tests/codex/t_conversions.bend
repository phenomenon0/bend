import Base

def emit(name: String, x: F64) -> IO(Unit):
  IO.print(name ++ " " ++ F64.show(x))

def emit_u32(name: String, x: U32) -> IO(Unit):
  IO.print(name ++ " " ++ U32.show(x))

def emit_nat(name: String, x: Nat) -> IO(Unit):
  IO.print(name ++ " " ++ Nat.show(x))

def main() -> IO(Unit):
  do IO<Unit>:
    emit("conv_u32_zero", U32.to_f64(0))
    emit("conv_u32_max", U32.to_f64(4294967295))
    emit("conv_u32_above_f32", U32.to_f64(16777217))
    emit_u32("conv_truncate", F64.to_u32(3.9d))
    emit_u32("conv_fraction", F64.to_u32(0.99d))
    emit_u32("conv_negative", F64.to_u32(F64.neg(3.9d)))
    emit_u32("conv_u32_last_fraction", F64.to_u32(4294967295.75d))
    emit_u32("conv_u32_limit", F64.to_u32(4294967296d))
    emit_u32("conv_u32_above_limit", F64.to_u32(4294967297d))
    emit_u32("conv_u32_inf", F64.to_u32(F64.div(1d, 0d)))
    emit_u32("conv_u32_neg_inf", F64.to_u32(F64.div(F64.neg(1d), 0d)))
    emit_u32("conv_u32_nan", F64.to_u32(F64.div(0d, 0d)))
    emit("conv_widen_tenth", F32.to_f64(0.1))
    emit("conv_widen_sum", F32.to_f64(F32.add(0.1, 0.2)))
    emit("conv_narrow_tenth", F32.to_f64(F64.to_f32(0.1d)))
    emit("conv_narrow_tie", F32.to_f64(F64.to_f32(1.0000000596046448d)))
    emit("conv_narrow_above_tie", F32.to_f64(F64.to_f32(1.000000059604645d)))
    emit("conv_narrow_overflow", F32.to_f64(F64.to_f32(1e39d)))
    emit("conv_narrow_underflow", F32.to_f64(F64.to_f32(5e-324d)))
    emit("conv_narrow_neg_zero", F32.to_f64(F64.to_f32(F64.neg(0d))))
    emit("conv_from_nat", F64.from_nat(7n))
    emit("conv_from_nat_zero", F64.from_nat(0n))
    emit_nat("conv_to_nat", F64.to_nat(3.9d))
    emit_nat("conv_bits_zero", F64.bits(0d))
    emit_nat("conv_bits_subnormal", F64.bits(5e-324d))
    emit_nat("conv_bits_next_subnormal", F64.bits(1e-323d))
