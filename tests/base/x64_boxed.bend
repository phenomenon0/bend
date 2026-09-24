# A U64, I64 or F64 is any 64-bit pattern: 2^63-1, -1 and 0.1d read as a
# heap reference, or carry the count bit, when the word is taken as a Term.
# Each shape below puts one where the C runtime drops or shares a Term: a
# polymorphic parameter (Bool.pick, a generic swap, List.map's closure), a
# generic constructor's field (a Maybe or a List built under a pick) and a
# union slot shared with a box (Result's error String). Each value is read
# back after the other arm was dropped; C once freed it as a pointer.
import Base

def i_max() -> I64:
  I64.not(I64{I64.sign_mask()})

def i_neg1() -> I64:
  I64.not(I64{Word.zero(64n)})

def u_top() -> U64:
  U64.not(U64{Word.zero(64n)})

def ok(b: Bool) -> String:
  Bool.pick(String, b, "ok", "bad")

def pick_i(c: Bool) -> I64:
  Bool.pick(I64, c, i_max(), i_neg1())

def pick_u(c: Bool) -> U64:
  Bool.pick(U64, c, u_top(), U64.shrn(u_top(), 1n))

def pick_f(c: Bool) -> F64:
  Bool.pick(F64, c, 0.1d, F64.pi())

def pick_m(c: Bool) -> Maybe<&2, I64>:
  Bool.pick(Maybe<&2, I64>, c, Some{i_max()}, None{})

def m_is(m: Maybe<&2, I64>, x: I64) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{y}:
      I64.is_eq(x, y)

def m_none(m: Maybe<&2, I64>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{y}:
      False{}

def res(c: Bool) -> Result<&2, &2, String, I64>:
  match c:
    case False{}:
      Fail{"no"}
    case True{}:
      Done{i_neg1()}

def res_is(r: Result<&2, &2, String, I64>, x: I64) -> Bool:
  match r:
    case Fail{e}:
      String.eq(e, "no")
    case Done{y}:
      I64.is_eq(x, y)

def swap(-A: Type, -B: Type, p: A & B) -> B & A:
  (a, b) = p
  (b, a)

def swap_is(p: F64 & I64) -> Bool:
  (f, i) = p
  Bool.and(F64.is_eq(f, 0.1d), I64.is_eq(i, i_max()))

def sum(xs: List<I64>, acc: I64) -> I64:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      sum(t, I64.add(acc, h))

def app(-A: Type, f: A -> A, x: A) -> A:
  f(x)

def grow(+k: I64, xs: List<I64>) -> List<I64>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      app(I64, x => I64.xor(x, k), h) <> grow(k, t)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(ok(I64.is_eq(pick_i(True{}), i_max())))
    IO.print(ok(I64.is_eq(pick_i(False{}), i_neg1())))
    IO.print(ok(U64.is_eq(pick_u(True{}), u_top())))
    IO.print(ok(U64.is_eq(pick_u(False{}), U64.shrn(u_top(), 1n))))
    IO.print(F64.show(pick_f(True{})))
    IO.print(F64.show(pick_f(False{})))
    IO.print(ok(m_is(pick_m(True{}), i_max())))
    IO.print(ok(m_none(pick_m(False{}))))
    IO.print(ok(res_is(res(True{}), i_neg1())))
    IO.print(ok(res_is(res(False{}), i_neg1())))
    IO.print(ok(swap_is(swap(I64, F64, (i_max(), 0.1d)))))
    IO.print(ok(I64.is_eq(sum(grow(i_neg1(), [i_max(), i_neg1()]),
      I64{Word.zero(64n)}), I64.not(i_max()))))

#|ok
#|ok
#|ok
#|ok
#|0.1
#|3.141592653589793
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
