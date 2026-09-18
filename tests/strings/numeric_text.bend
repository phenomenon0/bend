# F32.read and F64.read consume the whole extent on every lane: an embedded
# NUL is a character, not an end; strtod's hex floats and nan(...) are not
# spellings. Accepted: ASCII space, sign, digits/point/exponent, inf, nan.
import Base

def f64(m: Maybe<&2, F64>) -> String:
  match m:
    case Some{x}:
      F64.show(x)
    case None{}:
      "none"

def f32(m: Maybe<&2, F32>) -> String:
  match m:
    case Some{x}:
      F32.show(x)
    case None{}:
      "none"

def show(label: String, +s: String) -> IO(Unit):
  IO.print(label ++ " " ++ f64(F64.read(s)) ++ " " ++ f32(F32.read(s)))

def main() -> IO(Unit):
  do IO<Unit>:
    show("decimal", "1.5")
    show("point", "1.")
    show("lead_point", ".5e1")
    show("space", " 2")
    show("neg_inf", "-Infinity")
    show("nan", "NaN")
    show("nul", "1\0junk")
    show("hex", "0x1p0")
    show("junk", "1.25junk")
    show("nan_paren", "nan(1)")
    show("bare_exp", "1e")
    show("empty", "")
#|decimal 1.5 1.5
#|point 1 1
#|lead_point 5 5
#|space 2 2
#|neg_inf -inf -inf
#|nan nan nan
#|nul none none
#|hex none none
#|junk none none
#|nan_paren none none
#|bare_exp none none
#|empty none none
