import Base
# The native-I64 measurement: 10,000,000 iterations of a SIGNED test plus an
# increment on Base's I64. The signed test is the point -- inc is shared with
# U64 and was already measured there; what this lane adds is a comparison
# that is one machine compare instead of a bias and a width-64 bit walk.
# The accumulator carries `+` because the body reads it twice (once to test
# its sign, once to increment it), and is built ONCE, since Bend is affine
# and re-deriving I64{Word.zero(64n)} per iteration would allocate 64 Word
# cells and measure that instead.
#
# nbench_sigstr.bend is the same loop over an UNREGISTERED copy of the type
# carrying the same bodies: the before-number.
#
# Expected output: "i64 native sum: 10000000" then "NB-END".

def bump(b: Bool, a: I64) -> I64:
  match b:
    case True{}:
      I64.neg(a)
    case False{}:
      I64.inc(a)

def loop(n: Nat, +acc: I64) -> I64:
  match n:
    case 0n:
      acc
    case 1n+p:
      loop(p, bump(I64.is_neg(acc), acc))

def out(a: I64) -> Nat:
  match a:
    case I64{x}:
      Word.to_nat(64n, x)

def main() -> IO(Unit):
  do IO<Unit>:
    a : I64 = loop(10000000n, I64{Word.zero(64n)})
    u : Unit <- IO.print(String.append("i64 native sum: ", Nat.show(out(a))))
    IO.print("NB-END")
