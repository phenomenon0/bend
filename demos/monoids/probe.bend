# A linear-probing hash table, measured exactly, never built.
#
# Insert n keys into M slots with linear probing and ask what a lookup costs:
# the mean displacement of a key (a hit) and the mean distance from a slot to
# the next empty one (a miss). Knuth's answers are asymptotic -- 1/2(1 + 1/(1-a))
# and 1/2(1 + 1/(1-a)^2) -- and a real table of a real size with a real hash is
# not asymptotic. This program gets the exact numbers without a table,
# without an insertion, and in parallel.
#
# Three facts make it a fork tree:
#
#  1. The final set of occupied slots, and the total displacement, do not
#     depend on the order keys were inserted in. Only a_s, the number of keys
#     whose home is slot s, matters.
#  2. a_s is a function of s. The hash is a bijection on D bits (xorshifts and
#     odd multiplies, each invertible), and slot s owns the 2^(D-B) hash values
#     with s on top. So a_s counts those x whose preimage h^-1(x) is a key
#     (below n): the hash is run backwards, with no scatter and no array.
#  3. The number of keys carried past slot s obeys c_s = max(0, c_{s-1} + a_s - 1),
#     and c -> max(p, c + q) maps compose into maps of the same shape:
#     (p2, q2) after (p1, q1) is (max(p2, p1 + q2), q1 + q2). So a range of
#     slots summarizes to two words, whatever its size. The table is a ring,
#     and the whole ring's map (P, Q) has Q = n - M < 0, so its only fixed
#     point -- the carry into slot 0 -- is P.
#
# Pass 1 builds the tree of maps. Pass 2 walks it with the exact inflow: a
# left child gets its parent's, a right child gets the left map applied to it.
# The two children still run in parallel. Each leaf then scans its slots with
# a known carry. Total displacement is the sum of the carries, and the miss
# cost comes from the runs of occupied slots, summed by a run-length monoid
# that stitches runs across leaf edges and around the ring.
#
# probe_gen.py is the oracle: it really inserts the keys into a list.
import Base

# -- the hash, both ways, on D bits ---------------------------------------------------

def mask(d: U32) -> U32:
  U32.sub(U32.shln(1, U32.to_nat(d)), 1)

def c1(+d: U32) -> U32:
  U32.or(U32.and(2654435761, mask(d)), 1)

def c2(+d: U32) -> U32:
  U32.or(U32.and(2246822507, mask(d)), 1)

# the inverse of an odd c mod 2^32, by Newton: each turn doubles the good bits
def inv.go(k: Nat, +c: U32, +x: U32) -> U32:
  match k:
    case 0n:
      x
    case 1n++q:
      inv.go(q, c, U32.mul(x, U32.sub(2, U32.mul(c, x))))

def inv(+c: U32) -> U32:
  inv.go(5n, c, c)

def xs(+x: U32, s: Nat) -> U32:
  U32.xor(x, U32.shrn(x, s))

# x ^= x >> s undone: iterate y = x ^ (y >> s) until the shifts run out
def xs.inv(k: Nat, +x: U32, +s: Nat, +y: U32) -> U32:
  match k:
    case 0n:
      y
    case 1n++q:
      xs.inv(q, x, s, U32.xor(x, U32.shrn(y, s)))

def h(+k: U32, +d: U32) -> U32:
  +m = mask(d)
  xs(U32.and(U32.mul(xs(U32.and(U32.mul(xs(k, 11n), c1(d)), m), 9n), c2(d)), m), 13n)

# the key whose hash is x (D bits); the fuel covers ceil(32 / s) shifts
def unh(+x: U32, +d: U32, +i1: U32, +i2: U32) -> U32:
  +m = mask(d)
  +a = xs.inv(3n, x, 13n, x)
  +b = xs.inv(4n, U32.and(U32.mul(a, i2), m), 9n, U32.and(U32.mul(a, i2), m))
  +c = U32.and(U32.mul(b, i1), m)
  xs.inv(3n, c, 11n, c)

# -- arrivals: a_s by inversion ----------------------------------------------------

def arr.go(k: Nat, +x: U32, +n: U32, +d: U32, +i1: U32, +i2: U32, +acc: U32) -> U32:
  match k:
    case 0n:
      acc
    case 1n++q:
      arr.go(q, U32.inc(x), n, d, i1, i2, U32.add(acc, Bool.to_u32(U32.is_lt(unh(x, d, i1, i2), n))))

# how many of keys 0..n-1 hash home to slot s of 2^b
def arrivals(+s: U32, +b: U32, +n: U32, +d: U32, +i1: U32, +i2: U32) -> U32:
  +w = U32.sub(d, b)
  arr.go(U32.to_nat(U32.shln(1, U32.to_nat(w))), U32.shln(s, U32.to_nat(w)), n, d, i1, i2, 0)

# -- pass 1: the (max, +) maps -----------------------------------------------------

# signed compare on U32 words (all values here are far below 2^31 in magnitude)
def smax(+a: U32, +b: U32) -> U32:
  Bool.pick(U32, U32.is_gt(U32.xor(a, 2147483648), U32.xor(b, 2147483648)), a, b)

type Mt is Data:
  Lf{p: U32, q: U32}
  Nd{p: U32, q: U32, l: Mt, r: Mt}

def mp(+t: Mt) -> U32:
  match t:
    case Lf{p, _}:
      p
    case Nd{p, _, _, _}:
      p

def mq(+t: Mt) -> U32:
  match t:
    case Lf{_, q}:
      q
    case Nd{_, q, _, _}:
      q

# the carry out of a range whose map is t, given the carry in
def apply(+t: Mt, +c: U32) -> U32:
  smax(mp(t), U32.add(c, mq(t)))

def maps.leaf(k: Nat, +s: U32, +b: U32, +n: U32, +d: U32, +i1: U32, +i2: U32, +p: U32,
  +q: U32) -> Mt:
  match k:
    case 0n:
      Lf{p, q}
    case 1n++r:
      +a1 = U32.sub(arrivals(s, b, n, d, i1, i2), 1)
      maps.leaf(r, U32.inc(s), b, n, d, i1, i2, smax(0, U32.add(p, a1)), U32.add(q, a1))

def node(+l: Mt, +r: Mt) -> Mt:
  Nd{smax(mp(r), U32.add(mp(l), mq(r))), U32.add(mq(l), mq(r)), l, r}

def maps(e: Nat, +b: U32, +n: U32, +d: U32, +i1: U32, +i2: U32, +lo: U32, +k: U32) -> Mt:
  match e:
    case 0n:
      maps.leaf(U32.to_nat(k), lo, b, n, d, i1, i2, 0, 0)
    case 1n++z:
      +h2 = U32.shr(k)
      l r = maps(z, b, n, d, i1, i2, lo, h2) maps(z, b, n, d, i1, i2, U32.add(lo, h2), U32.sub(k, h2))
      node(l, r)

# -- pass 2: the scan with a known carry ----------------------------------------------

# sum: carries (= displacement); mx: the largest carry; runs of occupied slots:
# pre / suf touch the range's edges, full says the range has no empty slot,
# tri is sum L(L+1)/2 over the runs closed inside
type Run is Data:
  Run{sum: U32, mx: U32, pre: U32, suf: U32, full: U32, tri: U32}

def tri(+l: U32) -> U32:
  U32.shr(U32.mul(l, U32.inc(l)))

def scan(k: Nat, +s: U32, +b: U32, +n: U32, +d: U32, +i1: U32, +i2: U32, +c: U32,
  +sum: U32, +mx: U32, +pre: U32, +cur: U32, +full: U32, +tr: U32) -> Run:
  match k:
    case 0n:
      Run{sum, mx, pre, cur, full, tr}
    case 1n++r:
      +t = U32.add(c, arrivals(s, b, n, d, i1, i2))
      +occ = Bool.to_u32(U32.is_ne(t, 0))
      +c2 = U32.sub(t, occ)
      scan(r, U32.inc(s), b, n, d, i1, i2, c2, U32.add(sum, c2), U32.max(mx, c2),
        U32.add(pre, U32.and(full, occ)), U32.mul(occ, U32.inc(cur)), U32.and(full, occ),
        U32.add(tr, U32.mul(U32.mul(U32.sub(1, occ), U32.sub(1, full)), tri(cur))))

def join(x: Run, y: Run) -> Run:
  match x y:
    case Run{s1, m1, +p1, +f1, +u1, t1} Run{s2, m2, +p2, +f2, +u2, t2}:
      +both = U32.and(u1, u2)
      Run{U32.add(s1, s2), U32.max(m1, m2),
        Bool.pick(U32, U32.is_eq(u1, 1), U32.add(p1, p2), p1),
        Bool.pick(U32, U32.is_eq(u2, 1), U32.add(f1, p2), f2),
        both,
        U32.add(U32.add(t1, t2), U32.mul(U32.mul(U32.sub(1, u1), U32.sub(1, u2)), tri(U32.add(f1, p2))))}

# the tree of maps is also the fork tree: its shape is pass 1's split
def walk(t: Mt, +b: U32, +n: U32, +d: U32, +i1: U32, +i2: U32, +lo: U32, +k: U32,
  +c: U32) -> Run:
  match t:
    case Lf{_, _}:
      scan(U32.to_nat(k), lo, b, n, d, i1, i2, c, 0, 0, 0, 0, 1, 0)
    case Nd{_, _, +l, r}:
      +h2 = U32.shr(k)
      x y = walk(l, b, n, d, i1, i2, lo, h2, c) walk(r, b, n, d, i1, i2, U32.add(lo, h2), U32.sub(k, h2), apply(l, c))
      join(x, y)

# the run that wraps (its end in the last leaf, its start in the first)
def close(x: Run) -> Run:
  match x:
    case Run{s, m, +p, +f, u, r}:
      Run{s, m, p, f, u, U32.add(r, tri(U32.add(f, p)))}

# the whole ring: the fixed point of the ring's map is the carry into slot 0
def ring(+e: Nat, +b: U32, +n: U32, +d: U32) -> Run:
  +i1 = inv(c1(d))
  +i2 = inv(c2(d))
  +t = maps(e, b, n, d, i1, i2, 0, U32.shln(1, U32.to_nat(b)))
  close(walk(t, b, n, d, i1, i2, 0, U32.shln(1, U32.to_nat(b)), mp(t)))

# -- the report -----------------------------------------------------------------------

def pad4(+v: U32) -> String:
  Bool.pick(String, U32.is_lt(v, 1000), "0", "") ++ Bool.pick(String, U32.is_lt(v, 100), "0", "")
    ++ Bool.pick(String, U32.is_lt(v, 10), "0", "") ++ U32.show(v)

# x floored to four decimals
def fmt(x: F64) -> String:
  +v = F64.to_u32(F64.floor(F64.mul(x, 10000.0d)))
  U32.show(U32.div(v, 10000)) ++ "." ++ pad4(U32.mod(v, 10000))

def ratio(+a: U32, +b: U32) -> F64:
  F64.add(1.0d, F64.div(U32.to_f64(a), U32.to_f64(b)))

# does the hash invert? (a spot check over 4096 keys)
def round.go(k: Nat, +d: U32, +i1: U32, +i2: U32, +x: U32, +ok: Bool) -> Bool:
  match k:
    case 0n:
      ok
    case 1n++q:
      +key = U32.and(U32.mul(x, 2654435761), mask(d))
      round.go(q, d, i1, i2, U32.inc(x), Bool.and(ok, U32.is_eq(unh(h(key, d), d, i1, i2), key)))

def same(+x: Run, y: Run) -> Bool:
  match x y:
    case Run{s1, m1, _, _, _, t1} Run{s2, m2, _, _, _, t2}:
      Bool.and(U32.is_eq(s1, s2), Bool.and(U32.is_eq(m1, m2), U32.is_eq(t1, t2)))

def show(x: Run, +b: U32, +n: U32, ok: Bool) -> String:
  match x:
    case Run{+s, m, _, _, _, +r}:
      +a = F64.div(U32.to_f64(n), U32.to_f64(U32.shln(1, U32.to_nat(b))))
      +z = F64.sub(1.0d, a)
      "M=2^" ++ U32.show(b) ++ " n=" ++ U32.show(n) ++ " disp=" ++ U32.show(s) ++ " maxcarry="
        ++ U32.show(m) ++ " runs=" ++ U32.show(r) ++ " | hit " ++ fmt(ratio(s, n)) ++ " knuth "
        ++ fmt(F64.mul(0.5d, F64.add(1.0d, F64.div(1.0d, z)))) ++ " | miss "
        ++ fmt(ratio(r, U32.shln(1, U32.to_nat(b)))) ++ " knuth "
        ++ fmt(F64.mul(0.5d, F64.add(1.0d, F64.div(1.0d, F64.mul(z, z))))) ++ " | depths 0 4 9: "
        ++ Bool.pick(String, ok, "same", "DIFFER")

def report(+b: U32, +d: U32, pct: U32) -> String:
  +n = U32.div(U32.mul(U32.shln(1, U32.to_nat(b)), pct), 100)
  +x = ring(4n, b, n, d)
  +ok = Bool.and(round.go(4096n, d, inv(c1(d)), inv(c2(d)), 0, True{}),
    Bool.and(same(x, ring(0n, b, n, d)), same(x, ring(9n, b, n, d))))
  show(x, b, n, ok)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(report(12, 16, 50))
    IO.print(report(14, 18, 75))
    IO.print(report(14, 18, 90))
    IO.print(report(16, 20, 85))
#|M=2^12 n=2048 disp=908 maxcarry=4 runs=5987 | hit 1.4433 knuth 1.5000 | miss 2.4616 knuth 2.5000 | depths 0 4 9: same
#|M=2^14 n=12288 disp=18331 maxcarry=11 runs=123342 | hit 2.4917 knuth 2.5000 | miss 8.5281 knuth 8.5000 | depths 0 4 9: same
#|M=2^14 n=14745 disp=60404 maxcarry=21 runs=551109 | hit 5.0965 knuth 5.4981 | miss 34.6370 knuth 50.4633 | depths 0 4 9: same
#|M=2^16 n=55705 disp=174706 maxcarry=36 runs=1726615 | hit 4.1362 knuth 3.8331 | miss 27.3460 knuth 22.7195 | depths 0 4 9: same
