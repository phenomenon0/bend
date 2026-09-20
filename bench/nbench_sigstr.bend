import Base
# The control for nbench_sig.bend: the SAME loop over T64, the same
# type{data: Word(64n)} with the same signed bodies, declared locally and
# therefore NOT in the compiler's WORDS / OPTIMIZED tables -- exactly what
# I64 was before this lane. Every operation here is the structural one: the
# sign test walks 64 Word cells four times over (two nots, a shift and a
# compare) where the native lane emits a single machine `< 0`.
#
# Expected output: "t64 struct sum: 10000000" then "NB-END".

type T64 is Data:
  T64{data: Word(64n)}

def T64.sign_mask() -> Word(64n):
  Word.not(64n, Word.shr(64n, Word.not(64n, Word.zero(64n))))

def T64.inc(a: T64) -> T64:
  match a:
    case T64{x}:
      T64{Word.inc(64n, x)}

def T64.neg(a: T64) -> T64:
  match a:
    case T64{x}:
      T64{Word.sub(64n, Word.zero(64n), x)}

def T64.is_neg(a: T64) -> Bool:
  match a:
    case T64{x}:
      Cmp.is_ge(Word.cmp(64n, x, T64.sign_mask()))

def bump(b: Bool, a: T64) -> T64:
  match b:
    case True{}:
      T64.neg(a)
    case False{}:
      T64.inc(a)

def loop(n: Nat, +acc: T64) -> T64:
  match n:
    case 0n:
      acc
    case 1n+p:
      loop(p, bump(T64.is_neg(acc), acc))

def out(a: T64) -> Nat:
  match a:
    case T64{x}:
      Word.to_nat(64n, x)

def main() -> IO(Unit):
  do IO<Unit>:
    a : T64 = loop(10000000n, T64{Word.zero(64n)})
    u : Unit <- IO.print(String.append("t64 struct sum: ", Nat.show(out(a))))
    IO.print("NB-END")
