# Facts of Nat the HPACK proofs stand on: the ring laws, the order, and
# what Nat.divmod by 128 hands back. Each is proven here from Base's
# definitions; nothing is assumed.
import Base

# Clashes
# =======

def disc(b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

# False is not True
def ft(h: {False{} == True{} : Bool}) -> Empty:
  %h : disc(_)
  Unit{}

def absurd(-g: Type, e: Empty) -> g:
  match e:

def zdisc(n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+p:
      Unit

# a successor is not zero
def sz(-n: Nat, h: {1n+n == 0n : Nat}) -> Empty:
  %h : zdisc(_)
  Unit{}

def pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def succ_inj(-a: Nat, -b: Nat, h: {1n+a == 1n+b : Nat}) -> {a == b : Nat}:
  Equal.cong(Nat, Nat, pred, 1n+a, 1n+b, h)

# Addition
# ========

def add_0r(+a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_0r(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def add_Sr(+a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_Sr(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def add_comm(+a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, add_0r(b))
    case 1n+p:
      %Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), add_Sr(b, p)) : {1n+Nat.add(p, b) == _ : Nat}
      %add_comm(p, b) : {1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

def add_assoc(+a: Nat, -b: Nat, -c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

# Multiplication
# ==============

def mul_0r(+a: Nat) -> {Nat.mul(a, 0n) == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      mul_0r(p)

def mul_1r(+a: Nat) -> {Nat.mul(a, 1n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %mul_1r(p) : {1n+Nat.mul(p, 1n) == 1n+_ : Nat}
      {==}

# b + (a + x) = a + (b + x)
def add_swap(+a: Nat, +b: Nat, +x: Nat) -> {Nat.add(b, Nat.add(a, x)) == Nat.add(a, Nat.add(b, x)) : Nat}:
  %add_assoc(b, a, x) : {_ == Nat.add(a, Nat.add(b, x)) : Nat}
  %add_assoc(a, b, x) : {Nat.add(Nat.add(b, a), x) == _ : Nat}
  %add_comm(b, a) : {Nat.add(Nat.add(b, a), x) == Nat.add(_, x) : Nat}
  {==}

def mul_Sr(+a: Nat, +b: Nat) -> {Nat.mul(a, 1n+b) == Nat.add(a, Nat.mul(a, b)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.mul(p, 1n+b), Nat.add(p, Nat.mul(p, b)), mul_Sr(p, b)) :
        {1n+Nat.add(b, _) == 1n+Nat.add(p, Nat.add(b, Nat.mul(p, b))) : Nat}
      %add_swap(p, b, Nat.mul(p, b)) : {1n+Nat.add(b, Nat.add(p, Nat.mul(p, b))) == 1n+_ : Nat}
      {==}

def mul_comm(+a: Nat, +b: Nat) -> {Nat.mul(a, b) == Nat.mul(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.mul(b, 0n), 0n, mul_0r(b))
    case 1n+p:
      %Equal.sym(Nat, Nat.mul(b, 1n+p), Nat.add(b, Nat.mul(b, p)), mul_Sr(b, p)) :
        {Nat.add(b, Nat.mul(p, b)) == _ : Nat}
      %mul_comm(p, b) : {Nat.add(b, Nat.mul(p, b)) == Nat.add(b, _) : Nat}
      {==}

def mul_distr(+a: Nat, -b: Nat, +c: Nat) ->
  {Nat.mul(Nat.add(a, b), c) == Nat.add(Nat.mul(a, c), Nat.mul(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.mul(Nat.add(p, b), c), Nat.add(Nat.mul(p, c), Nat.mul(b, c)), mul_distr(p, b, c)) :
        {Nat.add(c, _) == Nat.add(Nat.add(c, Nat.mul(p, c)), Nat.mul(b, c)) : Nat}
      Equal.sym(Nat, Nat.add(Nat.add(c, Nat.mul(p, c)), Nat.mul(b, c)),
        Nat.add(c, Nat.add(Nat.mul(p, c), Nat.mul(b, c))), add_assoc(c, Nat.mul(p, c), Nat.mul(b, c)))

def mul_assoc(+a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(Nat.mul(a, b), c) == Nat.mul(a, Nat.mul(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.mul(Nat.add(b, Nat.mul(p, b)), c), Nat.add(Nat.mul(b, c), Nat.mul(Nat.mul(p, b), c)),
          mul_distr(b, Nat.mul(p, b), c)) :
        {_ == Nat.add(Nat.mul(b, c), Nat.mul(p, Nat.mul(b, c))) : Nat}
      %mul_assoc(p, b, c) : {Nat.add(Nat.mul(b, c), Nat.mul(Nat.mul(p, b), c)) == Nat.add(Nat.mul(b, c), _) : Nat}
      {==}

# Order
# =====

def le0(+b: Nat) -> {Nat.is_le(0n, b) == True{} : Bool}:
  match b:
    case 0n:
      {==}
    case 1n+p:
      {==}

def le_refl(+a: Nat) -> {Nat.is_le(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      le_refl(p)

def le_S(+a: Nat, +b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      absurd({Nat.is_le(1n+p, 1n) == True{} : Bool}, ft(h))
    case 1n+p 1n+q:
      le_S(p, q, h)

# a <= b is a < b + 1
def le_lt(+a: Nat, +b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_lt(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      absurd({Nat.is_lt(1n+p, 1n) == True{} : Bool}, ft(h))
    case 1n+p 1n+q:
      le_lt(p, q, h)

# a < b means not b <= a
def lt_nle(+a: Nat, +b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      absurd({Nat.is_le(0n, 0n) == False{} : Bool}, ft(h))
    case 1n+p 0n:
      absurd({Nat.is_le(0n, 1n+p) == False{} : Bool}, ft(h))
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      lt_nle(p, q, h)

# r + m = k means r <= k
def le_of_add(+m: Nat, +r: Nat, +k: Nat, h: {Nat.add(m, r) == k : Nat}) -> {Nat.is_le(r, k) == True{} : Bool}:
  match m:
    case 0n:
      %h : {Nat.is_le(r, _) == True{} : Bool}
      le_refl(r)
    case 1n+p:
      match k:
        case 0n:
          absurd({Nat.is_le(r, 0n) == True{} : Bool}, sz(Nat.add(p, r), h))
        case 1n+q:
          le_S(r, q, le_of_add(p, r, q, succ_inj(Nat.add(p, r), q, h)))

# a < b and b <= c: a < c
def lt_le(+a: Nat, +b: Nat, +c: Nat, h1: {Nat.is_lt(a, b) == True{} : Bool},
  h2: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case 0n 0n _:
      absurd({Nat.is_lt(0n, c) == True{} : Bool}, ft(h1))
    case 1n+p 0n _:
      absurd({Nat.is_lt(1n+p, c) == True{} : Bool}, ft(h1))
    case 0n 1n+q 0n:
      absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, ft(h2))
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 1n+q 0n:
      absurd({Nat.is_lt(1n+p, 0n) == True{} : Bool}, ft(h2))
    case 1n+p 1n+q 1n+r:
      lt_le(p, q, r, h1, h2)

# s <= b and x <= b - s: s + x <= b
def le_add_sub(+s: Nat, +b: Nat, -x: Nat, h1: {Nat.is_le(s, b) == True{} : Bool},
  h2: {Nat.is_le(x, Nat.sub(b, s)) == True{} : Bool}) -> {Nat.is_le(Nat.add(s, x), b) == True{} : Bool}:
  match s b:
    case 0n 0n:
      h2
    case 0n 1n+c:
      h2
    case 1n+r 0n:
      absurd({Nat.is_le(Nat.add(1n+r, x), 0n) == True{} : Bool}, ft(h1))
    case 1n+r 1n+c:
      le_add_sub(r, c, x, h1, h2)

# not v < m: m + (v - m) = v
def add_sub(+m: Nat, +v: Nat, h: {Nat.is_lt(v, m) == False{} : Bool}) -> {Nat.add(m, Nat.sub(v, m)) == v : Nat}:
  match m v:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      absurd({Nat.add(1n+p, Nat.sub(0n, 1n+p)) == 0n : Nat}, ft(Equal.sym(Bool, True{}, False{}, h)))
    case 1n+p 1n+q:
      %add_sub(p, q, h) : {1n+Nat.add(p, Nat.sub(q, p)) == 1n+_ : Nat}
      {==}

def sub_0r(+a: Nat) -> {Nat.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

# Division by 128
# ===============

def eta(p: Nat & Nat) -> {p == (Nat.div.fin(p), Nat.mod.fin(p)) : Nat & Nat}:
  match p:
    case (a, b):
      {==}

# Nat.divmod(x, 128) walks x down with m to go before the quotient
# steps and r counted so far, m + r = 127 throughout
def go_eq(+n: Nat, +m: Nat, +d: Nat, +r: Nat, h: {Nat.add(m, r) == 127n : Nat}) ->
  {Nat.add(Nat.mul(Nat.div.fin(Nat.divmod.go(n, m, d, r)), 128n), Nat.mod.fin(Nat.divmod.go(n, m, d, r))) ==
    Nat.add(n, Nat.add(Nat.mul(d, 128n), r)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+np:
      match m:
        case 0n:
          %Equal.sym(Nat, r, 127n, h) :
            {Nat.add(Nat.mul(Nat.div.fin(Nat.divmod.go(np, _, 1n+d, 0n)), 128n), Nat.mod.fin(Nat.divmod.go(np, _, 1n+d, 0n))) ==
              Nat.add(1n+np, Nat.add(Nat.mul(d, 128n), _)) : Nat}
          %Equal.sym(Nat, Nat.add(Nat.mul(Nat.div.fin(Nat.divmod.go(np, 127n, 1n+d, 0n)), 128n),
              Nat.mod.fin(Nat.divmod.go(np, 127n, 1n+d, 0n))), Nat.add(np, Nat.add(Nat.mul(1n+d, 128n), 0n)),
              go_eq(np, 127n, 1n+d, 0n, {==})) :
            {_ == Nat.add(1n+np, Nat.add(Nat.mul(d, 128n), 127n)) : Nat}
          %Equal.sym(Nat, Nat.add(Nat.add(128n, Nat.mul(d, 128n)), 0n), Nat.add(128n, Nat.mul(d, 128n)),
              add_0r(Nat.add(128n, Nat.mul(d, 128n)))) :
            {Nat.add(np, _) == Nat.add(1n+np, Nat.add(Nat.mul(d, 128n), 127n)) : Nat}
          %Equal.sym(Nat, Nat.add(np, 1n+Nat.add(127n, Nat.mul(d, 128n))),
              1n+Nat.add(np, Nat.add(127n, Nat.mul(d, 128n))), add_Sr(np, Nat.add(127n, Nat.mul(d, 128n)))) :
            {_ == Nat.add(1n+np, Nat.add(Nat.mul(d, 128n), 127n)) : Nat}
          %add_comm(127n, Nat.mul(d, 128n)) :
            {1n+Nat.add(np, Nat.add(127n, Nat.mul(d, 128n))) == 1n+Nat.add(np, _) : Nat}
          {==}
        case 1n+mp:
          %Equal.sym(Nat, Nat.add(Nat.mul(Nat.div.fin(Nat.divmod.go(np, mp, d, 1n+r)), 128n),
              Nat.mod.fin(Nat.divmod.go(np, mp, d, 1n+r))), Nat.add(np, Nat.add(Nat.mul(d, 128n), 1n+r)),
              go_eq(np, mp, d, 1n+r, Equal.trans(Nat, Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), 127n,
                add_Sr(mp, r), h))) :
            {_ == Nat.add(1n+np, Nat.add(Nat.mul(d, 128n), r)) : Nat}
          %Equal.sym(Nat, Nat.add(Nat.mul(d, 128n), 1n+r), 1n+Nat.add(Nat.mul(d, 128n), r),
              add_Sr(Nat.mul(d, 128n), r)) :
            {Nat.add(np, _) == Nat.add(1n+np, Nat.add(Nat.mul(d, 128n), r)) : Nat}
          add_Sr(np, Nat.add(Nat.mul(d, 128n), r))

def go_lt(+n: Nat, +m: Nat, -d: Nat, +r: Nat, h: {Nat.add(m, r) == 127n : Nat}) ->
  {Nat.is_lt(Nat.mod.fin(Nat.divmod.go(n, m, d, r)), 128n) == True{} : Bool}:
  match n:
    case 0n:
      le_lt(r, 127n, le_of_add(m, r, 127n, h))
    case 1n+np:
      match m:
        case 0n:
          go_lt(np, r, 1n+d, 0n, Equal.trans(Nat, Nat.add(r, 0n), r, 127n, add_0r(r), h))
        case 1n+mp:
          go_lt(np, mp, d, 1n+r, Equal.trans(Nat, Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), 127n,
            add_Sr(mp, r), h))

# x = 128 (x / 128) + x % 128, and x % 128 < 128
def dm_eq(+x: Nat) ->
  {Nat.add(Nat.mul(Nat.div.fin(Nat.divmod(x, 128n)), 128n), Nat.mod.fin(Nat.divmod(x, 128n))) == x : Nat}:
  Equal.trans(Nat, Nat.add(Nat.mul(Nat.div.fin(Nat.divmod(x, 128n)), 128n), Nat.mod.fin(Nat.divmod(x, 128n))),
    Nat.add(x, 0n), x, go_eq(x, 127n, 0n, 0n, {==}), add_0r(x))

def dm_lt(+x: Nat) -> {Nat.is_lt(Nat.mod.fin(Nat.divmod(x, 128n)), 128n) == True{} : Bool}:
  go_lt(x, 127n, 0n, 0n, {==})

# 128 q + r < 128 b: q < b
def quot_lt(+q: Nat, +b: Nat, +r: Nat, h: {Nat.is_lt(Nat.add(Nat.mul(q, 128n), r), Nat.mul(b, 128n)) == True{} : Bool}) ->
  {Nat.is_lt(q, b) == True{} : Bool}:
  match q b:
    case 0n 0n:
      match r:
        case 0n:
          absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, ft(h))
        case 1n+s:
          absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, ft(h))
    case 0n 1n+c:
      {==}
    case 1n+p 0n:
      absurd({Nat.is_lt(1n+p, 0n) == True{} : Bool}, ft(h))
    case 1n+p 1n+c:
      quot_lt(p, c, r, h)

# Bytes as numbers
# ================

# a number below 256 is a byte: U32.from_nat then U32.to_nat hands it back.
# Proven by computing each of the 256 (gen.py writes it).
def byte_nat(+y: Nat, h: {Nat.is_lt(y, 256n) == True{} : Bool}) -> {U32.to_nat(U32.from_nat(y)) == y : Nat}:
  match y:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n:
      {==}
    case 11n:
      {==}
    case 12n:
      {==}
    case 13n:
      {==}
    case 14n:
      {==}
    case 15n:
      {==}
    case 16n:
      {==}
    case 17n:
      {==}
    case 18n:
      {==}
    case 19n:
      {==}
    case 20n:
      {==}
    case 21n:
      {==}
    case 22n:
      {==}
    case 23n:
      {==}
    case 24n:
      {==}
    case 25n:
      {==}
    case 26n:
      {==}
    case 27n:
      {==}
    case 28n:
      {==}
    case 29n:
      {==}
    case 30n:
      {==}
    case 31n:
      {==}
    case 32n:
      {==}
    case 33n:
      {==}
    case 34n:
      {==}
    case 35n:
      {==}
    case 36n:
      {==}
    case 37n:
      {==}
    case 38n:
      {==}
    case 39n:
      {==}
    case 40n:
      {==}
    case 41n:
      {==}
    case 42n:
      {==}
    case 43n:
      {==}
    case 44n:
      {==}
    case 45n:
      {==}
    case 46n:
      {==}
    case 47n:
      {==}
    case 48n:
      {==}
    case 49n:
      {==}
    case 50n:
      {==}
    case 51n:
      {==}
    case 52n:
      {==}
    case 53n:
      {==}
    case 54n:
      {==}
    case 55n:
      {==}
    case 56n:
      {==}
    case 57n:
      {==}
    case 58n:
      {==}
    case 59n:
      {==}
    case 60n:
      {==}
    case 61n:
      {==}
    case 62n:
      {==}
    case 63n:
      {==}
    case 64n:
      {==}
    case 65n:
      {==}
    case 66n:
      {==}
    case 67n:
      {==}
    case 68n:
      {==}
    case 69n:
      {==}
    case 70n:
      {==}
    case 71n:
      {==}
    case 72n:
      {==}
    case 73n:
      {==}
    case 74n:
      {==}
    case 75n:
      {==}
    case 76n:
      {==}
    case 77n:
      {==}
    case 78n:
      {==}
    case 79n:
      {==}
    case 80n:
      {==}
    case 81n:
      {==}
    case 82n:
      {==}
    case 83n:
      {==}
    case 84n:
      {==}
    case 85n:
      {==}
    case 86n:
      {==}
    case 87n:
      {==}
    case 88n:
      {==}
    case 89n:
      {==}
    case 90n:
      {==}
    case 91n:
      {==}
    case 92n:
      {==}
    case 93n:
      {==}
    case 94n:
      {==}
    case 95n:
      {==}
    case 96n:
      {==}
    case 97n:
      {==}
    case 98n:
      {==}
    case 99n:
      {==}
    case 100n:
      {==}
    case 101n:
      {==}
    case 102n:
      {==}
    case 103n:
      {==}
    case 104n:
      {==}
    case 105n:
      {==}
    case 106n:
      {==}
    case 107n:
      {==}
    case 108n:
      {==}
    case 109n:
      {==}
    case 110n:
      {==}
    case 111n:
      {==}
    case 112n:
      {==}
    case 113n:
      {==}
    case 114n:
      {==}
    case 115n:
      {==}
    case 116n:
      {==}
    case 117n:
      {==}
    case 118n:
      {==}
    case 119n:
      {==}
    case 120n:
      {==}
    case 121n:
      {==}
    case 122n:
      {==}
    case 123n:
      {==}
    case 124n:
      {==}
    case 125n:
      {==}
    case 126n:
      {==}
    case 127n:
      {==}
    case 128n:
      {==}
    case 129n:
      {==}
    case 130n:
      {==}
    case 131n:
      {==}
    case 132n:
      {==}
    case 133n:
      {==}
    case 134n:
      {==}
    case 135n:
      {==}
    case 136n:
      {==}
    case 137n:
      {==}
    case 138n:
      {==}
    case 139n:
      {==}
    case 140n:
      {==}
    case 141n:
      {==}
    case 142n:
      {==}
    case 143n:
      {==}
    case 144n:
      {==}
    case 145n:
      {==}
    case 146n:
      {==}
    case 147n:
      {==}
    case 148n:
      {==}
    case 149n:
      {==}
    case 150n:
      {==}
    case 151n:
      {==}
    case 152n:
      {==}
    case 153n:
      {==}
    case 154n:
      {==}
    case 155n:
      {==}
    case 156n:
      {==}
    case 157n:
      {==}
    case 158n:
      {==}
    case 159n:
      {==}
    case 160n:
      {==}
    case 161n:
      {==}
    case 162n:
      {==}
    case 163n:
      {==}
    case 164n:
      {==}
    case 165n:
      {==}
    case 166n:
      {==}
    case 167n:
      {==}
    case 168n:
      {==}
    case 169n:
      {==}
    case 170n:
      {==}
    case 171n:
      {==}
    case 172n:
      {==}
    case 173n:
      {==}
    case 174n:
      {==}
    case 175n:
      {==}
    case 176n:
      {==}
    case 177n:
      {==}
    case 178n:
      {==}
    case 179n:
      {==}
    case 180n:
      {==}
    case 181n:
      {==}
    case 182n:
      {==}
    case 183n:
      {==}
    case 184n:
      {==}
    case 185n:
      {==}
    case 186n:
      {==}
    case 187n:
      {==}
    case 188n:
      {==}
    case 189n:
      {==}
    case 190n:
      {==}
    case 191n:
      {==}
    case 192n:
      {==}
    case 193n:
      {==}
    case 194n:
      {==}
    case 195n:
      {==}
    case 196n:
      {==}
    case 197n:
      {==}
    case 198n:
      {==}
    case 199n:
      {==}
    case 200n:
      {==}
    case 201n:
      {==}
    case 202n:
      {==}
    case 203n:
      {==}
    case 204n:
      {==}
    case 205n:
      {==}
    case 206n:
      {==}
    case 207n:
      {==}
    case 208n:
      {==}
    case 209n:
      {==}
    case 210n:
      {==}
    case 211n:
      {==}
    case 212n:
      {==}
    case 213n:
      {==}
    case 214n:
      {==}
    case 215n:
      {==}
    case 216n:
      {==}
    case 217n:
      {==}
    case 218n:
      {==}
    case 219n:
      {==}
    case 220n:
      {==}
    case 221n:
      {==}
    case 222n:
      {==}
    case 223n:
      {==}
    case 224n:
      {==}
    case 225n:
      {==}
    case 226n:
      {==}
    case 227n:
      {==}
    case 228n:
      {==}
    case 229n:
      {==}
    case 230n:
      {==}
    case 231n:
      {==}
    case 232n:
      {==}
    case 233n:
      {==}
    case 234n:
      {==}
    case 235n:
      {==}
    case 236n:
      {==}
    case 237n:
      {==}
    case 238n:
      {==}
    case 239n:
      {==}
    case 240n:
      {==}
    case 241n:
      {==}
    case 242n:
      {==}
    case 243n:
      {==}
    case 244n:
      {==}
    case 245n:
      {==}
    case 246n:
      {==}
    case 247n:
      {==}
    case 248n:
      {==}
    case 249n:
      {==}
    case 250n:
      {==}
    case 251n:
      {==}
    case 252n:
      {==}
    case 253n:
      {==}
    case 254n:
      {==}
    case 255n:
      {==}
    case 256n+z:
      match z:
        case 0n:
          absurd({U32.to_nat(U32.from_nat(256n)) == 256n : Nat}, ft(h))
        case 1n+w:
          absurd({U32.to_nat(U32.from_nat(257n+w)) == 257n+w : Nat}, ft(h))
