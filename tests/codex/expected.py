#!/usr/bin/env python3
"""Independent binary64 oracle; no Bend imports or compiler-generated fixtures.

Usage: expected.py [t_rounding|t_special|t_conversions|t_math|t_text|t_precision]
With no suite argument, print all cases. --list and --count describe the suite.
"""

import argparse
from decimal import Decimal
import math
import re
import struct
import sys


def show(value):
    """Python shortest digits, JS fixed/exponent thresholds, Bend inf/nan/-0.

    Unlike JavaScript String(-0), the requested Bend contract preserves -0.
    Decimal is used only to expand repr's digits, never for the arithmetic.
    """
    if isinstance(value, bool):
        return str(value)  # Base.Bool.show uses True/False.
    if isinstance(value, (int, str)):
        return str(value)
    if math.isnan(value):
        return "nan"
    if math.isinf(value):
        return "-inf" if value < 0 else "inf"
    if value == 0.0:
        return "-0" if math.copysign(1.0, value) < 0 else "0"
    shortest = repr(value)
    if 1e-6 <= abs(value) < 1e21:
        fixed = format(Decimal(shortest), "f")
        return fixed.rstrip("0").rstrip(".") if "." in fixed else fixed
    mantissa, exponent = shortest.lower().split("e")
    mantissa = mantissa.rstrip("0").rstrip(".") if "." in mantissa else mantissa
    return f"{mantissa}e{int(exponent):+d}"


def f32(value):
    """Round after EACH F32 operation, including overflow and signed zero."""
    try:
        return struct.unpack(">f", struct.pack(">f", value))[0]
    except OverflowError:
        return math.copysign(math.inf, value)


def div(a, b):
    # Python raises on division by zero; Bend uses IEEE-754 nontrapping results.
    if math.isnan(a) or math.isnan(b):
        return math.nan
    if b == 0.0:
        if a == 0.0:
            return math.nan
        sign = math.copysign(1.0, a) * math.copysign(1.0, b)
        return math.copysign(math.inf, sign)
    return a / b


def ieee_math(fn, *args):
    try:
        return fn(*args)
    except ValueError:
        return math.nan


def integral(fn, value):
    result = float(fn(value))
    return math.copysign(result, value) if result == 0.0 else result


def to_u32(value):
    # The v0.1 contract saturates invalid/out-of-range inputs to zero, not max.
    return math.trunc(value) if 0.0 <= value < 2**32 else 0


def bits(value):
    return struct.unpack(">Q", struct.pack(">d", value))[0]


def read(text):
    # Validate the WHOLE decimal spelling. float() alone also accepts underscores.
    decimal = r"[+-]?(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)(?:[eE][+-]?[0-9]+)?"
    if re.fullmatch(decimal, text) or text in ("inf", "-inf", "nan"):
        return f"Some({show(float(text))})"
    return "None"


def rounding():
    tiny = float("5e-324")
    normal = sys.float_info.min
    largest = sys.float_info.max
    return [
        ("round_sum", 0.1 + 0.2),
        ("round_third", 1.0 / 3.0),
        ("round_pow_half", math.pow(2.0, 0.5)),
        ("round_large_swallow", 1e16 + 1.0),
        ("round_large_cancel", (1e16 + 1.0) - 1e16),
        ("round_large_next", 1e16 + 2.0),
        ("round_tie_even_down", 1.0 + 2.0**-53),
        ("round_tie_even_up", math.nextafter(1.0, math.inf) + 2.0**-53),
        ("round_subnormal", tiny),
        ("round_subnormal_double", tiny + tiny),
        ("round_subnormal_half", tiny * 0.5),
        ("round_subnormal_tie", tiny * 1.5),
        ("round_subnormal_div", tiny / 2.0),
        ("round_subnormal_neg_div", -tiny / 2.0),
        ("round_min_normal", normal),
        ("round_below_normal", normal - tiny),
        ("round_recover_normal", (normal / 2.0) * 2.0),
        ("round_integer_literal", float(2)),
        ("round_decimal_exponent", float("1.5e3")),
        ("round_integer_exponent", float("2E+3")),
        ("round_max_finite", largest),
        ("round_max_overflow", largest * 2.0),
        ("round_above_f32_integer", float(2**24 + 1)),
        ("round_last_exact_integer", float(2**53 - 1)),
        ("round_integer_tie", float(2**53 + 1)),
    ]


def special():
    inf = div(1.0, 0.0)
    nan = div(0.0, 0.0)
    negative_zero = -0.0
    return [
        ("special_zero", 0.0),
        ("special_neg_zero", negative_zero),
        ("special_zero_equal", negative_zero == 0.0),
        ("special_zero_not_less", negative_zero < 0.0),
        ("special_double_neg_zero", -negative_zero),
        ("special_abs_neg_zero", abs(negative_zero)),
        ("special_reciprocal_zero", inf),
        ("special_reciprocal_neg_zero", div(1.0, negative_zero)),
        ("special_overflow", 1e308 * 10.0),
        ("special_neg_overflow", -1e308 * 10.0),
        ("special_inf_add", inf + 7.0),
        ("special_inf_opposite", inf + -inf),
        ("special_inf_sub", inf - inf),
        ("special_inf_zero_mul", inf * 0.0),
        ("special_inf_div", div(inf, inf)),
        ("special_finite_div_inf", div(1.0, inf)),
        ("special_negative_div_inf", div(-1.0, inf)),
        ("special_nan", nan),
        ("special_nan_add", nan + 1.0),
        ("special_nan_mul", nan * 0.0),
        ("special_nan_div", div(1.0, nan)),
        ("special_sqrt_negative", ieee_math(math.sqrt, -1.0)),
        ("special_nan_eq", nan == nan),
        ("special_nan_ne", nan != nan),
        ("special_nan_lt", nan < 0.0),
        ("special_nan_le", nan <= 0.0),
        ("special_nan_gt", 0.0 > nan),
        ("special_nan_ge", 0.0 >= nan),
        ("special_inf_eq", inf == inf),
        ("special_inf_gt", inf > sys.float_info.max),
        ("special_neg_inf_lt", -inf < -sys.float_info.max),
        ("special_mod_zero", ieee_math(math.fmod, 1.0, 0.0)),
        ("special_mod_neg_zero", math.fmod(-4.0, 2.0)),
    ]


def conversions():
    return [
        ("conv_u32_zero", float(0)),
        ("conv_u32_max", float(2**32 - 1)),
        ("conv_u32_above_f32", float(2**24 + 1)),
        ("conv_truncate", to_u32(3.9)),
        ("conv_fraction", to_u32(0.99)),
        ("conv_negative", to_u32(-3.9)),
        ("conv_u32_last_fraction", to_u32(4294967295.75)),
        ("conv_u32_limit", to_u32(float(2**32))),
        ("conv_u32_above_limit", to_u32(float(2**32 + 1))),
        ("conv_u32_inf", to_u32(math.inf)),
        ("conv_u32_neg_inf", to_u32(-math.inf)),
        ("conv_u32_nan", to_u32(math.nan)),
        ("conv_widen_tenth", float(f32(0.1))),
        ("conv_widen_sum", float(f32(f32(0.1) + f32(0.2)))),
        ("conv_narrow_tenth", float(f32(0.1))),
        ("conv_narrow_tie", float(f32(1.0 + 2.0**-24))),
        ("conv_narrow_above_tie", float(f32(math.nextafter(1.0 + 2.0**-24, math.inf)))),
        ("conv_narrow_overflow", float(f32(1e39))),
        ("conv_narrow_underflow", float(f32(5e-324))),
        ("conv_narrow_neg_zero", float(f32(-0.0))),
        ("conv_from_nat", float(7)),
        ("conv_from_nat_zero", float(0)),
        ("conv_to_nat", to_u32(3.9)),
        ("conv_bits_zero", bits(0.0)),
        ("conv_bits_subnormal", bits(5e-324)),
        ("conv_bits_next_subnormal", bits(1e-323)),
    ]


def math_laws():
    def scaled(value):
        return to_u32(value * 1e9)

    return [
        ("math_neg", -1.25),
        ("math_abs", abs(-3.5)),
        ("math_mod", math.fmod(5.5, 2.0)),
        ("math_mod_negative", math.fmod(-5.5, 2.0)),
        ("math_mod_negative_divisor", math.fmod(5.5, -2.0)),
        ("math_pow_negative", math.pow(-2.0, 3.0)),
        ("math_sqrt", math.sqrt(2.0)),
        ("math_atan2_scaled", scaled(math.atan2(1.0, -1.0))),
        ("math_exp_scaled", scaled(math.exp(1.0))),
        ("math_log_scaled", scaled(math.log(2.0))),
        ("math_log2_scaled", scaled(math.log2(3.0))),
        ("math_log10_scaled", scaled(math.log10(2.0))),
        ("math_sin_scaled", scaled(math.sin(1.0))),
        ("math_cos_scaled", scaled(math.cos(1.0))),
        ("math_tan_scaled", scaled(math.tan(1.0))),
        ("math_asin_scaled", scaled(math.asin(0.5))),
        ("math_acos_scaled", scaled(math.acos(0.5))),
        ("math_atan_scaled", scaled(math.atan(1.0))),
        ("math_sinh_scaled", scaled(math.sinh(1.0))),
        ("math_cosh_scaled", scaled(math.cosh(1.0))),
        ("math_tanh_scaled", scaled(math.tanh(1.0))),
        ("math_floor_negative", integral(math.floor, -3.9)),
        ("math_ceil_negative", integral(math.ceil, -3.9)),
        ("math_trunc_negative", integral(math.trunc, -3.9)),
        ("math_floor_positive", integral(math.floor, 3.9)),
        ("math_ceil_positive", integral(math.ceil, 3.9)),
        ("math_trunc_neg_fraction", integral(math.trunc, -0.5)),
        ("math_pi", math.pi),
        ("math_eq", 1.0 == 1.0),
        ("math_ne", 1.0 != 2.0),
        ("math_lt", 1.0 < 2.0),
        ("math_le_equal", 1.0 <= 1.0),
        ("math_gt", 2.0 > 1.0),
        ("math_ge_equal", 2.0 >= 2.0),
    ]


def text_cases():
    values = [
        ("text_integer", 42.0),
        ("text_small_fixed", 1e-6),
        ("text_small_scientific", 1e-7),
        ("text_large_fixed", 1e20),
        ("text_large_scientific", 1e21),
        ("text_negative_fixed", -1e20),
        ("text_negative_scientific", -1e-7),
    ]
    inputs = [
        ("read_decimal", "0.30000000000000004"),
        ("read_integer", "7"),
        ("read_exponent", "1.5e3"),
        ("read_integer_exponent", "2E+3"),
        ("read_subnormal", "5e-324"),
        ("read_max_finite", "1.7976931348623157e308"),
        ("read_neg_zero", "-0"),
        ("read_neg_zero_decimal", "-0.0"),
        ("read_inf", "inf"),
        ("read_neg_inf", "-inf"),
        ("read_nan", "nan"),
        ("read_overflow", "1e309"),
        ("read_underflow", "1e-400"),
        ("read_neg_underflow", "-1e-400"),
        ("read_halfway_even", "1.00000000000000011102230246251565404236316680908203125"),
        ("read_above_halfway", "1.00000000000000011102230246251565404236316680908203126"),
        ("read_empty", ""),
        ("read_spaces_only", "   "),
        ("read_junk", "hello"),
        ("read_trailing_junk", "1.25junk"),
        ("read_incomplete_exp", "1e"),
        ("read_incomplete_sign", "+"),
        ("read_literal_suffix", "1.5d"),
        ("read_embedded_nul", "1\0junk"),
        ("read_hex", "0x1p0"),
        ("read_underscore", "1_000"),
    ]
    roundtrips = [
        ("roundtrip_sum", 0.1 + 0.2),
        ("roundtrip_third", 1.0 / 3.0),
        ("roundtrip_subnormal", 5e-324),
        ("roundtrip_neg_zero", -0.0),
        ("roundtrip_inf", div(1.0, 0.0)),
        ("roundtrip_nan", div(0.0, 0.0)),
    ]
    # Both lanes validate the whole extent with one grammar: an embedded NUL
    # is a character, not an end, and strtod's hex floats are not spellings
    # (tests/strings/numeric_text.bend pairs these for F32 and F64).
    return (values + [(name, read(value)) for name, value in inputs]
            + [(name, read(show(value))) for name, value in roundtrips])


def machin_pi(quantize):
    def atan_series(divisor):
        x = quantize(quantize(1.0) / quantize(divisor))
        square = quantize(x * x)
        term, denominator, acc = x, quantize(1.0), quantize(0.0)
        for _ in range(10):
            acc = quantize(acc + quantize(term / denominator))
            term = quantize(-quantize(term * square))
            denominator = quantize(denominator + quantize(2.0))
        return acc

    first = quantize(quantize(16.0) * atan_series(5.0))
    second = quantize(quantize(4.0) * atan_series(239.0))
    return quantize(first - second)


def precision():
    wide, narrow = machin_pi(float), machin_pi(f32)

    def digits(value):
        return to_u32(math.floor(-math.log10(abs((value - math.pi) / math.pi))))

    return [
        ("precision_f64", wide),
        ("precision_f32_widened", narrow),
        ("precision_f64_digits", digits(wide)),
        ("precision_f32_digits", digits(narrow)),
    ]


SUITES = {
    "t_rounding": rounding,
    "t_special": special,
    "t_conversions": conversions,
    "t_math": math_laws,
    "t_text": text_cases,
    "t_precision": precision,
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("suite", nargs="?", choices=tuple(SUITES))
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--list", action="store_true", help="print program basenames")
    mode.add_argument("--count", action="store_true", help="print total selected cases")
    args = parser.parse_args()
    selected = [args.suite] if args.suite else list(SUITES)
    if args.list:
        print("\n".join(selected))
        return
    assert sys.float_info.radix == 2 and sys.float_info.mant_dig == 53
    cases = [case for suite in selected for case in SUITES[suite]()]
    assert len({name for name, _ in cases}) == len(cases), "duplicate case IDs"
    if args.count:
        print(len(cases))
    else:
        for name, value in cases:
            print(f"{name} {show(value)}")


if __name__ == "__main__":
    main()
