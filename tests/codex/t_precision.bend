import Base

# Ten terms of atan(x) = x - x^3/3 + x^5/5 - ... . Only n is matched;
# every recursive call consumes its predecessor, and reused values carry +.
def series64(n: Nat, +term: F64, +square: F64, +denom: F64, acc: F64) -> F64:
  match n:
    case 0n:
      acc
    case 1n+p:
      series64(p, F64.neg(F64.mul(term, square)), square, F64.add(denom, 2d), F64.add(acc, F64.div(term, denom)))

def series32(n: Nat, +term: F32, +square: F32, +denom: F32, acc: F32) -> F32:
  match n:
    case 0n:
      acc
    case 1n+p:
      series32(p, F32.neg(F32.mul(term, square)), square, F32.add(denom, 2.0), F32.add(acc, F32.div(term, denom)))

def atan64(+x: F64) -> F64:
  series64(10n, x, F64.mul(x, x), 1d, 0d)

def atan32(+x: F32) -> F32:
  series32(10n, x, F32.mul(x, x), 1.0, 0.0)

# Machin's formula: pi = 16 atan(1/5) - 4 atan(1/239).
def pi64() -> F64:
  F64.sub(F64.mul(16d, atan64(F64.div(1d, 5d))), F64.mul(4d, atan64(F64.div(1d, 239d))))

def pi32() -> F32:
  F32.sub(F32.mul(16.0, atan32(F32.div(1.0, 5.0))), F32.mul(4.0, atan32(F32.div(1.0, 239.0))))

# Relative decimal accuracy against the nearest binary64 pi. The chosen ten
# terms leave nonzero errors, so log10(0) is never part of this demo.
def digits(x: F64) -> U32:
  error = F64.abs(F64.div(F64.sub(x, F64.pi()), F64.pi()))
  F64.to_u32(F64.floor(F64.neg(F64.log10(error))))

def report(+wide: F64, +narrow: F64) -> IO(Unit):
  do IO<Unit>:
    IO.print("precision_f64 " ++ F64.show(wide))
    IO.print("precision_f32_widened " ++ F64.show(narrow))
    IO.print("precision_f64_digits " ++ U32.show(digits(wide)))
    IO.print("precision_f32_digits " ++ U32.show(digits(narrow)))

def main() -> IO(Unit):
  report(pi64(), F32.to_f64(pi32()))
