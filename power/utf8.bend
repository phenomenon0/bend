# Utf8: validate a byte buffer as UTF-8 with a fork tree, and find its first
# bad byte, without knowing where any leaf starts in the character stream.
#
# A validator is a DFA (Unicode 15, table 3-7): 0 ACC, 1-3 tails still owed,
# 4 E0 / 5 ED / 6 F0 / 7 F4 (a lead whose next byte has a narrowed range), 8
# DEAD. A leaf does not know which state it starts in, so it computes where it
# would end from each of the eight live states (Mytkowicz et al., "Data-parallel
# finite-state machines", ASPLOS 2014). DEAD is absorbing, so that map is eight
# nibbles -- one U32 -- and maps compose associatively: `then` is both the
# per-byte step and the join. UTF-8 self-synchronizes, so four bytes into a
# leaf every live start has converged on one state; from there a leaf runs one
# DFA, one lookup a byte, carrying which starts are still alive. A byte's class
# is a telescoping sum over the thirteen edges of the table, with no branch.
#
#   check(b, d)      the map and the scalar count of all of b, over 2^d leaves;
#                    valid iff the map sends ACC to ACC (valid(map))
#   first_bad(b, d)  the first byte at which a validator dies (len(b) if it
#                    runs out mid-scalar; none() if b is valid), by descending
#                    the same tree: a left half's map says whether a DFA
#                    entering it dies inside, so only one child is entered
#
# The fork is Array.fork: two handles to the one block of cells, reads only, no
# copy. demos/monoids/utf8.bend is the showcase this was lifted from;
# tests/power/utf8.bend holds it to CPython's own decoder.
import Base
import ./vec.bend as Vec
import ./bytes.bend as Bytes

type Sum is Data:
  Sum{map: U32, count: U32}

# -- the monoid ---------------------------------------------------------------

def ident() -> U32:
  1985229328 # 0x76543210: every state to itself

def nib(+m: U32, s: Nat) -> U32:
  U32.and(U32.shrn(m, s), 15)

# where g sends state t; DEAD (8) shifts g by 32, which is 0, and t & 8 restores it
def look(+g: U32, +t: U32) -> U32:
  U32.or(U32.and(U32.shrn(g, U32.to_nat(U32.shln(t, 2n))), 15), U32.and(t, 8))

# f, then g
def then(+f: U32, +g: U32) -> U32:
  +a = U32.or(look(g, nib(f, 0n)), U32.shln(look(g, nib(f, 4n)), 4n))
  +b = U32.or(U32.shln(look(g, nib(f, 8n)), 8n), U32.shln(look(g, nib(f, 12n)), 12n))
  +c = U32.or(U32.shln(look(g, nib(f, 16n)), 16n), U32.shln(look(g, nib(f, 20n)), 20n))
  +d = U32.or(U32.shln(look(g, nib(f, 24n)), 24n), U32.shln(look(g, nib(f, 28n)), 28n))
  U32.or(U32.or(a, b), U32.or(c, d))

def join(x: Sum, y: Sum) -> Sum:
  match x y:
    case Sum{f, c} Sum{g, e}:
      Sum{then(f, g), U32.add(c, e)}

def valid(+m: U32) -> Bool:
  U32.is_zero(nib(m, 0n))

def none() -> U32:
  4294967295

# -- one byte as a map ------------------------------------------------------------

def edge(+b: U32, x: U32, d: U32) -> U32:
  U32.mul(Bool.to_u32(U32.is_ge(b, x)), d)

#   80 tails (ED, F4 take them)  90 tails (ED, F0)  A0 tails (E0, F0)
#   C0 C1 dead  C2 lead 1  E0 lead E0  E1 lead 2  ED lead ED  EE lead 2
#   F0 lead F0  F1 lead 3  F4 lead F4  F5.. dead
def cls(+b: U32) -> U32:
  +t = U32.add(U32.add(edge(b, 128, 2676988040), edge(b, 144, 1509949440)),
    U32.add(edge(b, 160, 6881280), edge(b, 192, 101148544)))
  +l = U32.add(U32.add(edge(b, 194, 4294967289), edge(b, 224, 3)),
    U32.add(edge(b, 225, 4294967294), edge(b, 237, 3)))
  +h = U32.add(U32.add(edge(b, 238, 4294967293), edge(b, 240, 4)),
    U32.add(U32.add(edge(b, 241, 4294967293), edge(b, 244, 4)), edge(b, 245, 1)))
  U32.add(2290649216, U32.add(U32.add(t, l), h))

# 1 unless b is a tail byte: the scalar count of a valid range
def starts(+b: U32) -> U32:
  Bool.to_u32(U32.is_ne(U32.and(b, 192), 128))

def byte(+w: U32, +p: U32) -> U32:
  U32.and(U32.shrn(w, U32.to_nat(U32.shln(U32.and(p, 3), 3n))), 255)

# -- a leaf ---------------------------------------------------------------------------

# k bytes from p as full maps; r is the read of p's cell
def leaf.gen(k: Nat, +p: U32, r: Array<U32> & U32, +m: U32, +c: U32) -> Array<U32> & Sum:
  match k:
    case 0n:
      (a, _) = r
      (a, Sum{m, c})
    case 1n++q:
      (a, +w) = r
      +b = byte(w, p)
      leaf.gen(q, U32.inc(p), Array.get(U32, a, U32.shrn(U32.inc(p), 2n)), then(m, cls(b)),
        U32.add(c, starts(b)))

# k bytes from p through one converged DFA in state x
def leaf.one(k: Nat, +p: U32, r: Array<U32> & U32, +x: U32, +c: U32) -> Array<U32> & Sum:
  match k:
    case 0n:
      (a, _) = r
      (a, Sum{x, c})
    case 1n++q:
      (a, +w) = r
      +b = byte(w, p)
      leaf.one(q, U32.inc(p), Array.get(U32, a, U32.shrn(U32.inc(p), 2n)), look(cls(b), x),
        U32.add(c, starts(b)))

# k whole cells from cell i: four bytes of one read a turn
def leaf.cells(k: Nat, +i: U32, r: Array<U32> & U32, +x: U32, +c: U32) -> Array<U32> & Sum:
  match k:
    case 0n:
      (a, _) = r
      (a, Sum{x, c})
    case 1n++q:
      (a, +w) = r
      +b0 = U32.and(w, 255)
      +b1 = U32.and(U32.shrn(w, 8n), 255)
      +b2 = U32.and(U32.shrn(w, 16n), 255)
      +b3 = U32.shrn(w, 24n)
      +n = U32.add(U32.add(starts(b0), starts(b1)), U32.add(starts(b2), starts(b3)))
      leaf.cells(q, U32.inc(i), Array.get(U32, a, U32.inc(i)),
        look(cls(b3), look(cls(b2), look(cls(b1), look(cls(b0), x)))), U32.add(c, n))

# 0xF on each live nibble of a converged map, the one state they hold, and back
def alive(+m: U32) -> U32:
  U32.mul(U32.and(U32.not(U32.shrn(m, 3n)), 286331153), 15)

def common(+v: U32) -> U32:
  +a = U32.or(v, U32.shrn(v, 16n))
  +b = U32.or(a, U32.shrn(a, 8n))
  U32.and(U32.or(b, U32.shrn(b, 4n)), 15)

def spread(+l: U32, +x: U32) -> U32:
  U32.or(U32.and(l, U32.mul(x, 286331153)), U32.and(U32.not(l), 2290649224))

def leaf.end(+l: U32, r: Array<U32> & Sum) -> Array<U32> & Sum:
  (a, s) = r
  match s:
    case Sum{x, c}:
      (a, Sum{spread(l, x), c})

def leaf.tail(r: Array<U32> & Sum, +k: U32, +p: U32) -> Array<U32> & Sum:
  (a, s) = r
  match s:
    case Sum{x, c}:
      leaf.one(U32.to_nat(k), p, Array.get(U32, a, U32.shrn(p, 2n)), x, c)

def leaf.mid(r: Array<U32> & Sum, +k: U32, +i: U32) -> Array<U32> & Sum:
  (a, s) = r
  match s:
    case Sum{x, c}:
      leaf.cells(U32.to_nat(k), i, Array.get(U32, a, i), x, c)

# after the first four bytes: bytewise to a cell edge, whole cells, bytewise on
def leaf.rest(r: Array<U32> & Sum, +k: U32, +p: U32) -> Array<U32> & Sum:
  (a, s) = r
  match s:
    case Sum{+m, c}:
      +l = alive(m)
      +e = U32.min(U32.and(U32.sub(0, p), 3), k)
      +q = U32.add(p, e)
      +ns = U32.shrn(U32.sub(k, e), 2n)
      leaf.end(l, leaf.tail(leaf.mid(leaf.one(U32.to_nat(e), p,
        Array.get(U32, a, U32.shrn(p, 2n)), common(U32.and(m, l)), c), ns, U32.shrn(q, 2n)),
        U32.and(U32.sub(k, e), 3), U32.add(q, U32.shln(ns, 2n))))

def leaf.short(c: Bool, r: Array<U32> & Sum, +n: U32, +p: U32) -> Array<U32> & Sum:
  match c:
    case True{}:
      r # under four bytes: no convergence promised, keep the full map
    case False{}:
      leaf.rest(r, U32.sub(n, 4), U32.add(p, 4))

def leaf(a: Array<U32>, +p: U32, +n: U32) -> Array<U32> & Sum:
  leaf.short(U32.is_lt(n, 4), leaf.gen(U32.to_nat(U32.min(n, 4)), p,
    Array.get(U32, a, U32.shrn(p, 2n)), ident(), 0), n, p)

# -- the tree -------------------------------------------------------------------------

def tree.join(l: Array<U32> & Sum, r: Array<U32> & Sum) -> Array<U32> & Sum:
  (a, x) = l
  (b, y) = r
  (Array.join(U32, a, b), join(x, y))

# bytes lo .. lo+n-1, 2^d leaves; hs is two handles to the one array
def tree(d: Nat, hs: Array<U32> & Array<U32>, +lo: U32, +n: U32) -> Array<U32> & Sum:
  match d:
    case 0n:
      (a, b) = hs
      leaf(Array.join(U32, a, b), lo, n)
    case 1n++p:
      (a, b) = hs
      +h = U32.shr(n)
      l r = tree(p, Array.fork(U32, a), lo, h) tree(p, Array.fork(U32, b), U32.add(lo, h), U32.sub(n, h))
      tree.join(l, r)

def check.fin(n: U32, vn: U32, vd: Nat, r: Array<U32> & Sum) -> Bytes.Bytes & Sum:
  (a, s) = r
  (Bytes.Bytes{n, Vec.Vec{vn, vd, a}}, s)

# the map and scalar count of all of b, over 2^d leaves; b comes back
def check(b: Bytes.Bytes, d: Nat) -> Bytes.Bytes & Sum:
  match b:
    case Bytes.Bytes{+n, v}:
      match v:
        case Vec.Vec{vn, vd, a}:
          check.fin(n, vn, vd, tree(d, Array.fork(U32, a), 0, n))

# -- the first bad byte -------------------------------------------------------------

# the first byte at or after p that kills a DFA standing in state s; if none
# does and the bytes end mid-scalar, the end; else none()
def walk(k: Nat, +p: U32, r: Array<U32> & U32, +s: U32, +at: U32) -> Array<U32> & U32:
  match k:
    case 0n:
      (a, _) = r
      (a, Bool.pick(U32, Bool.and(U32.is_eq(at, none()), U32.is_ne(s, 0)), p, at))
    case 1n++q:
      (a, +w) = r
      +s2 = look(cls(byte(w, p)), s)
      +first = Bool.and(U32.is_eq(s2, 8), U32.is_eq(at, none()))
      walk(q, U32.inc(p), Array.get(U32, a, U32.shrn(U32.inc(p), 2n)), s2,
        Bool.pick(U32, first, p, at))

# a node of n bytes from lo, entered in state s; left is its left half's
# summary (made at depth d - 1) with the array's handle. Only one child is
# entered: the left if the DFA dies there, else the right, in the state the
# left half leaves it in. If nothing dies the path is the rightmost one, so
# the last walk sees the end of the buffer.
def dead(d: Nat, left: Array<U32> & Sum, +lo: U32, +n: U32, +s: U32) -> Array<U32> & U32:
  match d:
    case 0n:
      (a, _) = left
      walk(U32.to_nat(n), lo, Array.get(U32, a, U32.shrn(lo, 2n)), s, none())
    case 1n++p:
      (a, sm) = left
      match sm:
        case Sum{f, _}:
          +h = U32.shr(n)
          +mid = look(f, s)
          +go_left = U32.is_eq(mid, 8)
          +lo2 = Bool.pick(U32, go_left, lo, U32.add(lo, h))
          +n2 = Bool.pick(U32, go_left, h, U32.sub(n, h))
          dead(p, tree(Nat.sub(p, 1n), Array.fork(U32, a), lo2, U32.shr(n2)), lo2, n2,
            Bool.pick(U32, go_left, s, mid))

def bad.fin(n: U32, vn: U32, vd: Nat, r: Array<U32> & U32) -> Bytes.Bytes & U32:
  (a, p) = r
  (Bytes.Bytes{n, Vec.Vec{vn, vd, a}}, p)

# where a validator reading b from the start dies: the first byte it cannot
# take; len(b) if b ends mid-scalar; none() if b is valid. 2^d leaves, d >= 1.
def first_bad(b: Bytes.Bytes, +d: Nat) -> Bytes.Bytes & U32:
  match b:
    case Bytes.Bytes{+n, v}:
      match v:
        case Vec.Vec{vn, vd, a}:
          bad.fin(n, vn, vd, dead(d, tree(Nat.sub(d, 1n), Array.fork(U32, a), 0, U32.shr(n)), 0, n, 0))
