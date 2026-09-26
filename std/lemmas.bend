# Base lemmas std's deflate proofs lean on that released Bend's Base does
# not have: this repo's bend2/base.bend's own statements and proofs, word
# for word, under lower-case names (nat.lt_flip for Nat.lt_flip) so they
# neither clash with this repo's Base nor go missing on canon's.
import Base

def bool.if(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

# anything, from False == True

def bool.no(-g: Type, e: {False{} == True{} : Bool}) -> g:
  %e : bool.if(_, g, Unit)
  Unit{}

# a conjunction that holds, taken apart

law bool.and_l:
  for a: Bool
  for -b: Bool
  for e: {Bool.and(a, b) == True{} : Bool}
  {a == True{} : Bool}

def bool.and_l(a, b, e):
  match a:
    case True{}:
      {==}
    case False{}:
      bool.no({False{} == True{} : Bool}, e)

law bool.and_r:
  for a: Bool
  for b: Bool
  for e: {Bool.and(a, b) == True{} : Bool}
  {b == True{} : Bool}

def bool.and_r(a, b, e):
  match a:
    case True{}:
      e
    case False{}:
      bool.no({b == True{} : Bool}, e)

# a number's bit below the rest: 2x, or 2x + 1

def nat.bit(b: Bool, x: Nat) -> Nat:
  match b:
    case False{}:
      Nat.double(x)
    case True{}:
      1n+Nat.double(x)

law nat.cmp_bit:
  for +ab: Bool
  for +bb: Bool
  for +x: Nat
  for +y: Nat
  {Nat.cmp(nat.bit(ab, x), nat.bit(bb, y)) == Word.cmp.fin(ab, bb, Nat.cmp(x, y)) : Cmp}

def nat.cmp_bit(ba, bc, x, y):
  match ba bc x y:
    case False{} False{} 0n 0n:
      {==}
    case False{} True{} 0n 0n:
      {==}
    case True{} False{} 0n 0n:
      {==}
    case True{} True{} 0n 0n:
      {==}
    case False{} False{} 0n 1n+q:
      {==}
    case False{} True{} 0n 1n+q:
      {==}
    case True{} False{} 0n 1n+q:
      {==}
    case True{} True{} 0n 1n+q:
      {==}
    case False{} False{} 1n+p 0n:
      {==}
    case False{} True{} 1n+p 0n:
      {==}
    case True{} False{} 1n+p 0n:
      {==}
    case True{} True{} 1n+p 0n:
      {==}
    case False{} False{} 1n+p 1n+q:
      nat.cmp_bit(False{}, False{}, p, q)
    case False{} True{} 1n+p 1n+q:
      nat.cmp_bit(False{}, True{}, p, q)
    case True{} False{} 1n+p 1n+q:
      nat.cmp_bit(True{}, False{}, p, q)
    case True{} True{} 1n+p 1n+q:
      nat.cmp_bit(True{}, True{}, p, q)

law word.to_nat_bit:
  for -p: Nat
  for b: Bool
  for -t: Word(p)
  {Word.to_nat(1n+p, WCon{b, t}) == nat.bit(b, Word.to_nat(p, t)) : Nat}

def word.to_nat_bit(p, b, t):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def word.cmp_nat.go(+p: Nat, +ab: Bool, +at: Word(p), +bb: Bool, +bt: Word(p)) ->
  {Word.cmp.fin(ab, bb, Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt))) ==
    Nat.cmp(Word.to_nat(1n+p, WCon{ab, at}), Word.to_nat(1n+p, WCon{bb, bt})) : Cmp}:
  %Equal.sym(Nat, Word.to_nat(1n+p, WCon{ab, at}), nat.bit(ab, Word.to_nat(p, at)),
    word.to_nat_bit(p, ab, at)) :
    {Word.cmp.fin(ab, bb, Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt))) ==
      Nat.cmp(_, Word.to_nat(1n+p, WCon{bb, bt})) : Cmp}
  %Equal.sym(Nat, Word.to_nat(1n+p, WCon{bb, bt}), nat.bit(bb, Word.to_nat(p, bt)),
    word.to_nat_bit(p, bb, bt)) :
    {Word.cmp.fin(ab, bb, Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt))) ==
      Nat.cmp(nat.bit(ab, Word.to_nat(p, at)), _) : Cmp}
  Equal.sym(Cmp, Nat.cmp(nat.bit(ab, Word.to_nat(p, at)), nat.bit(bb, Word.to_nat(p, bt))),
    Word.cmp.fin(ab, bb, Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt))),
    nat.cmp_bit(ab, bb, Word.to_nat(p, at), Word.to_nat(p, bt)))

law word.cmp_nat:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {Word.cmp(n, a, b) == Nat.cmp(Word.to_nat(n, a), Word.to_nat(n, b)) : Cmp}

def word.cmp_nat(n, a, b):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a b:
        case WCon{ab, at} WCon{bb, bt}:
          Equal.trans(Cmp, Word.cmp.fin(ab, bb, Word.cmp(p, at, bt)),
            Word.cmp.fin(ab, bb, Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt))),
            Nat.cmp(Word.to_nat(1n+p, WCon{ab, at}), Word.to_nat(1n+p, WCon{bb, bt})),
            Equal.cong(Cmp, Cmp, x => Word.cmp.fin(ab, bb, x), Word.cmp(p, at, bt),
              Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt)), word.cmp_nat(p, at, bt)),
            word.cmp_nat.go(p, ab, at, bb, bt))

# U32's order is its value's

law u32.cmp_nat:
  for a: U32
  for b: U32
  {U32.cmp(a, b) == Nat.cmp(U32.to_nat(a), U32.to_nat(b)) : Cmp}

def u32.cmp_nat(a, b):
  match a b:
    case U32{x} U32{y}:
      word.cmp_nat(32n, x, y)

law u32.lt_nat:
  for a: U32
  for b: U32
  {U32.is_lt(a, b) == Nat.is_lt(U32.to_nat(a), U32.to_nat(b)) : Bool}

def u32.lt_nat(a, b):
  Equal.cong(Cmp, Bool, Cmp.is_lt, U32.cmp(a, b), Nat.cmp(U32.to_nat(a), U32.to_nat(b)),
    u32.cmp_nat(a, b))

law u32.eq_nat:
  for a: U32
  for b: U32
  {U32.is_eq(a, b) == Nat.is_eq(U32.to_nat(a), U32.to_nat(b)) : Bool}

def u32.eq_nat(a, b):
  Equal.cong(Cmp, Bool, Cmp.is_eq, U32.cmp(a, b), Nat.cmp(U32.to_nat(a), U32.to_nat(b)),
    u32.cmp_nat(a, b))

# Nat's order: a < b is not b <= a

law nat.lt_flip:
  for a: Nat
  for b: Nat
  {Bool.not(Nat.is_lt(a, b)) == Nat.is_le(b, a) : Bool}

def nat.lt_flip(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      nat.lt_flip(p, q)

law nat.le_flip:
  for a: Nat
  for b: Nat
  {Bool.not(Nat.is_le(a, b)) == Nat.is_lt(b, a) : Bool}

def nat.le_flip(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      nat.le_flip(p, q)

law nat.is_le_trans:
  for a: Nat
  for b: Nat
  for c: Nat
  for ab: {Nat.is_le(a, b) == True{} : Bool}
  for bc: {Nat.is_le(b, c) == True{} : Bool}
  {Nat.is_le(a, c) == True{} : Bool}

def nat.is_le_trans(a, b, c, ab, bc):
  match a b c:
    case 0n _ 0n:
      {==}
    case 0n _ 1n+r:
      {==}
    case 1n+p 0n _:
      bool.no({Nat.is_le(1n+p, c) == True{} : Bool}, ab)
    case 1n+p 1n+q 0n:
      bool.no({Nat.is_le(1n+p, 0n) == True{} : Bool}, bc)
    case 1n+p 1n+q 1n+r:
      nat.is_le_trans(p, q, r, ab, bc)

law nat.is_lt_le_trans:
  for a: Nat
  for b: Nat
  for c: Nat
  for ab: {Nat.is_lt(a, b) == True{} : Bool}
  for bc: {Nat.is_le(b, c) == True{} : Bool}
  {Nat.is_lt(a, c) == True{} : Bool}

def nat.is_lt_le_trans(a, b, c, ab, bc):
  match a b c:
    case 0n 0n _:
      bool.no({Nat.is_lt(0n, c) == True{} : Bool}, ab)
    case 1n+p 0n _:
      bool.no({Nat.is_lt(1n+p, c) == True{} : Bool}, ab)
    case 0n 1n+q 0n:
      bool.no({Nat.is_lt(0n, 0n) == True{} : Bool}, bc)
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 1n+q 0n:
      bool.no({Nat.is_lt(1n+p, 0n) == True{} : Bool}, bc)
    case 1n+p 1n+q 1n+r:
      nat.is_lt_le_trans(p, q, r, ab, bc)

# a <= b and not a < b: a is b

def nat.lt_zero(-g: Type, k: Nat, e: {Nat.is_lt(k, 0n) == True{} : Bool}) -> g:
  match k:
    case 0n:
      bool.no(g, e)
    case 1n+j:
      bool.no(g, e)
