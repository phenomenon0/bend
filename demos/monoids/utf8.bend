# UTF-8 validation as a monoid: eight nibbles, one U32, any split.
#
# A validator is a DFA, and a DFA looks sequential: byte i's verdict needs the
# state byte i-1 left behind. The trick (Mytkowicz et al., "Data-parallel
# finite-state machines", ASPLOS 2014) is to stop asking "which state am I in"
# and ask "from each state I could be in, where do I end up". That is a map
# from states to states, and maps compose associatively, so a fork tree can
# validate the halves of a buffer without knowing where either half starts.
#
# UTF-8 needs nine states (Unicode 15, table 3-7):
#
#   0 ACC  between scalars          4 E0   after E0: next is A0..BF
#   1 T1   one tail byte to go      5 ED   after ED: next is 80..9F (no surrogates)
#   2 T2   two to go                6 F0   after F0: next is 90..BF (no overlongs)
#   3 T3   three to go              7 F4   after F4: next is 80..8F (<= U+10FFFF)
#   8 DEAD absorbing
#
# DEAD maps to DEAD, so a map only needs the eight live entries, and a live
# state's image fits a nibble (0..8): the whole summary of any byte range is one
# U32. Nibble s of the summary is where a DFA started in state s finishes. The
# range is valid on its own iff nibble 0 is 0; its nibble 3 says whether it would
# be valid had it begun three tails short of a 4-byte scalar -- which is exactly
# what a right half cut mid-emoji needs to know.
#
# Every byte class is itself such a map, so the per-byte step and the join are
# the same function, `then`. Its one trick is the DEAD lane: looking nibble 8 up
# shifts the map right by 32, which the U32 row answers with 0, and or-ing in
# (t & 8) puts the 8 back. Eight lookups, no branch, no table in memory.
#
# The corpus is a pure function of the byte index (a Threefry word per 4-byte
# slot, see utf8_gen.py for the rule), so a leaf owns nothing and the fork tree
# pays no copy. utf8_gen.py is the oracle: it rebuilds the bytes and asks
# CPython's decoder, not a DFA, for every verdict printed below.
import Base
import ../../power/rng.bend as Rng

# -- the monoid ---------------------------------------------------------------

# the summary of a byte range: its state map, and how many scalars start in it
type Sum is Data:
  Sum{f: U32, c: U32}

def ident() -> U32:
  1985229328 # 0x76543210: every state to itself

def nib(+m: U32, s: Nat) -> U32:
  U32.and(U32.shrn(m, s), 15)

# where g sends state t; DEAD (8) stays DEAD
def look(+g: U32, +t: U32) -> U32:
  U32.or(U32.and(U32.shrn(g, U32.to_nat(U32.shln(t, 2n))), 15), U32.and(t, 8))

# f, then g: nibble s of the answer is g(f(s))
def then(+f: U32, +g: U32) -> U32:
  +a = U32.or(look(g, nib(f, 0n)), U32.shln(look(g, nib(f, 4n)), 4n))
  +b = U32.or(U32.shln(look(g, nib(f, 8n)), 8n), U32.shln(look(g, nib(f, 12n)), 12n))
  +c = U32.or(U32.shln(look(g, nib(f, 16n)), 16n), U32.shln(look(g, nib(f, 20n)), 20n))
  +d = U32.or(U32.shln(look(g, nib(f, 24n)), 24n), U32.shln(look(g, nib(f, 28n)), 28n))
  U32.or(U32.or(a, b), U32.or(c, d))

# -- one byte as a map ----------------------------------------------------------

# One byte as a map, with no branch: the map is a step function of the byte,
# so it is the ASCII map plus, at each of the thirteen edges of table 3-7, the
# difference to the next class (mod 2^32; the sum telescopes). A chain of ifs
# here is a data-dependent branch per byte, and on real mixed text it is
# mispredicted about as often as the text changes script.
def edge(+b: U32, x: U32, d: U32) -> U32:
  U32.mul(Bool.to_u32(U32.is_ge(b, x)), d)

def cls(+b: U32) -> U32:
  +t = U32.add(U32.add(edge(b, 128, 2676988040), edge(b, 144, 1509949440)),
    U32.add(edge(b, 160, 6881280), edge(b, 192, 101148544)))
  +l = U32.add(U32.add(edge(b, 194, 4294967289), edge(b, 224, 3)),
    U32.add(edge(b, 225, 4294967294), edge(b, 237, 3)))
  +h = U32.add(U32.add(edge(b, 238, 4294967293), edge(b, 240, 4)),
    U32.add(U32.add(edge(b, 241, 4294967293), edge(b, 244, 4)), edge(b, 245, 1)))
  #   80 tails (ED, F4 take them)  90 tails (ED, F0)  A0 tails (E0, F0)
  #   C0 C1 dead  C2 lead 1  E0 lead E0  E1 lead 2  ED lead ED  EE lead 2
  #   F0 lead F0  F1 lead 3  F4 lead F4  F5.. dead
  U32.add(2290649216, U32.add(U32.add(t, l), h))

# 1 unless b is a tail byte: the scalar count of a valid range
def starts(+b: U32) -> U32:
  Bool.to_u32(U32.is_ne(U32.and(b, 192), 128))

# -- the corpus: slot i is four bytes, little end first -------------------------

def asc(+r: U32, s: Nat) -> U32:
  U32.add(48, U32.and(U32.shrn(r, s), 63))

def tail(+c: U32, s: Nat) -> U32:
  U32.or(128, U32.and(U32.shrn(c, s), 63))

def enc2(+c: U32) -> U32:
  U32.or(U32.or(192, U32.shrn(c, 6n)), U32.shln(tail(c, 0n), 8n))

def enc3(+c: U32) -> U32:
  U32.or(U32.or(224, U32.shrn(c, 12n)),
    U32.or(U32.shln(tail(c, 6n), 8n), U32.shln(tail(c, 0n), 16n)))

def enc4(+c: U32) -> U32:
  U32.or(U32.or(240, U32.shrn(c, 18n)), U32.or(U32.shln(tail(c, 12n), 8n),
    U32.or(U32.shln(tail(c, 6n), 16n), U32.shln(tail(c, 0n), 24n))))

# a 3-byte scalar off 16 random bits: lifted past the overlong range, and a
# surrogate folded down into D000..D7FF, so ED still gets exercised
def cp3.lo(c: Bool, +x: U32) -> U32:
  match c:
    case True{}:
      U32.add(x, 2048)
    case False{}:
      x

def cp3.sur(c: Bool, +x: U32) -> U32:
  match c:
    case True{}:
      U32.sub(x, 2048)
    case False{}:
      x

def cp3(+r: U32) -> U32:
  +x = U32.and(U32.shrn(r, 3n), 65535)
  +y = cp3.lo(U32.is_lt(x, 2048), x)
  cp3.sur(Bool.and(U32.is_ge(y, 55296), U32.is_lt(y, 57344)), y)

def two(+r: U32) -> U32:
  enc2(U32.add(128, U32.and(U32.shrn(r, 3n), 1023)))

def gen.k(k: U32, +r: U32) -> U32:
  match k:
    case 2:
      U32.or(two(r), U32.shln(enc2(U32.add(128, U32.and(U32.shrn(r, 13n), 1023))), 16n))
    case 3:
      U32.or(enc3(cp3(r)), U32.shln(asc(r, 19n), 24n))
    case 4:
      U32.or(asc(r, 19n), U32.shln(enc3(cp3(r)), 8n))
    case 5:
      enc4(U32.add(65536, U32.mod(U32.shrn(r, 3n), 1048576)))
    case 6:
      enc4(U32.add(65536, U32.mod(U32.shrn(r, 3n), 1048576)))
    case 7:
      U32.or(two(r), U32.or(U32.shln(asc(r, 13n), 16n), U32.shln(asc(r, 19n), 24n)))
    case _:
      U32.or(U32.or(asc(r, 3n), U32.shln(asc(r, 9n), 8n)),
        U32.or(U32.shln(asc(r, 15n), 16n), U32.shln(asc(r, 21n), 24n)))

def gen(+seed: U32, +i: U32) -> U32:
  +r = Rng.u32(seed, 0, i)
  gen.k(U32.and(r, 7), r)

# the eight injuries, one per rule of table 3-7 that a real decoder must enforce
def poison(t: U32) -> U32:
  match t:
    case 0:
      1094795648 # 80 'A' 'A' 'A'   a lone tail
    case 1:
      1094823872 # C0 AF 'A' 'A'    an overlong '/'
    case 2:
      1098948845 # ED A0 80 'A'     U+D800
    case 3:
      1094812386 # E2 82 'A' 'A'    a euro sign cut short
    case 4:
      1094795765 # F5 'A' 'A' 'A'   past the last plane's lead
    case 5:
      2155909364 # F4 90 80 80      U+110000
    case 6:
      1098940640 # E0 80 80 'A'     an overlong NUL
    case _:
      1094828865 # 'A' C3 'A' 'A'   a lead with no tail

# Where: slot k1 carries injury t1, slot k2 injury t2 (4294967295: none).
type Where is Data:
  Where{seed: U32, k1: U32, t1: U32, k2: U32, t2: U32}

def slot.2(c: Bool, t2: U32, +seed: U32, +i: U32) -> U32:
  match c:
    case True{}:
      poison(t2)
    case False{}:
      gen(seed, i)

def slot.1(c: Bool, t1: U32, +k2: U32, t2: U32, +seed: U32, +i: U32) -> U32:
  match c:
    case True{}:
      poison(t1)
    case False{}:
      slot.2(U32.is_eq(i, k2), t2, seed, i)

def slot(+seed: U32, +k1: U32, +t1: U32, +k2: U32, +t2: U32, +i: U32) -> U32:
  slot.1(U32.is_eq(i, k1), t1, k2, t2, seed, i)

def byte(+seed: U32, +k1: U32, +t1: U32, +k2: U32, +t2: U32, +p: U32) -> U32:
  U32.and(U32.shrn(slot(seed, k1, t1, k2, t2, U32.shrn(p, 2n)),
    U32.to_nat(U32.shln(U32.and(p, 3), 3n))), 255)

# -- the fork tree ----------------------------------------------------------------

# the slot word under byte p: kept while p stays inside it, rebuilt on entry
def refill(c: Bool, +w: U32, +seed: U32, +k1: U32, +t1: U32, +k2: U32, +t2: U32,
  +p: U32) -> U32:
  match c:
    case True{}:
      slot(seed, k1, t1, k2, t2, U32.shrn(p, 2n))
    case False{}:
      w

# The first bytes of a leaf, as full maps. w is the slot word p sits in, so one
# Threefry block serves four bytes.
def leaf.gen(k: Nat, +seed: U32, +k1: U32, +t1: U32, +k2: U32, +t2: U32, +p: U32,
  +w: U32, +m: U32, +c: U32) -> Sum:
  match k:
    case 0n:
      Sum{m, c}
    case 1n++q:
      +b = U32.and(U32.shrn(w, U32.to_nat(U32.shln(U32.and(p, 3), 3n))), 255)
      +p2 = U32.inc(p)
      leaf.gen(q, seed, k1, t1, k2, t2, p2,
        refill(U32.is_zero(U32.and(p2, 3)), w, seed, k1, t1, k2, t2, p2),
        then(m, cls(b)), U32.add(c, starts(b)))

# The rest of a leaf, as ONE state. UTF-8 is self-synchronizing: a byte that
# is not a tail is only legal from ACC, so after it every live entry of the map
# holds the same state; and three tails in a row leave only ACC alive. Either
# way, four bytes in, the eight speculative DFAs have converged -- Mytkowicz's
# "convergence", which UTF-8 guarantees by design -- and a leaf runs one DFA,
# one lookup a byte, carrying just which starts are still alive.
def leaf.one(k: Nat, +seed: U32, +k1: U32, +t1: U32, +k2: U32, +t2: U32, +p: U32,
  +w: U32, +x: U32, +c: U32) -> Sum:
  match k:
    case 0n:
      Sum{x, c}
    case 1n++q:
      +b = U32.and(U32.shrn(w, U32.to_nat(U32.shln(U32.and(p, 3), 3n))), 255)
      +p2 = U32.inc(p)
      leaf.one(q, seed, k1, t1, k2, t2, p2,
        refill(U32.is_zero(U32.and(p2, 3)), w, seed, k1, t1, k2, t2, p2),
        look(cls(b), x), U32.add(c, starts(b)))

# 0xF in every nibble of a converged map that is still alive (0..7, bit 3 clear)
def alive(+m: U32) -> U32:
  U32.mul(U32.and(U32.not(U32.shrn(m, 3n)), 286331153), 15)

# the one state every live nibble holds (0 if none is live: then alive is 0)
def common(+v: U32) -> U32:
  +a = U32.or(v, U32.shrn(v, 16n))
  +b = U32.or(a, U32.shrn(a, 8n))
  U32.and(U32.or(b, U32.shrn(b, 4n)), 15)

# the converged map back in full: x on the live nibbles, DEAD on the rest
def spread(+l: U32, +x: U32) -> U32:
  U32.or(U32.and(l, U32.mul(x, 286331153)), U32.and(U32.not(l), 2290649224))

def leaf.end(+l: U32, s: Sum) -> Sum:
  match s:
    case Sum{x, c}:
      Sum{spread(l, x), c}

# whole slots: four bytes of one Threefry word per turn, the DFA unrolled
def byte4(+w: U32, s: Nat) -> U32:
  U32.and(U32.shrn(w, s), 255)

def leaf.slots(k: Nat, +seed: U32, +k1: U32, +t1: U32, +k2: U32, +t2: U32, +i: U32,
  +x: U32, +c: U32) -> Sum:
  match k:
    case 0n:
      Sum{x, c}
    case 1n++q:
      +w = slot(seed, k1, t1, k2, t2, i)
      +b0 = byte4(w, 0n)
      +b1 = byte4(w, 8n)
      +b2 = byte4(w, 16n)
      +b3 = byte4(w, 24n)
      +n = U32.add(U32.add(starts(b0), starts(b1)), U32.add(starts(b2), starts(b3)))
      leaf.slots(q, seed, k1, t1, k2, t2, U32.inc(i),
        look(cls(b3), look(cls(b2), look(cls(b1), look(cls(b0), x)))), U32.add(c, n))

def leaf.bytes(s: Sum, +k: U32, +seed: U32, +k1: U32, +t1: U32, +k2: U32, +t2: U32,
  +p: U32) -> Sum:
  match s:
    case Sum{x, c}:
      leaf.one(U32.to_nat(k), seed, k1, t1, k2, t2, p, slot(seed, k1, t1, k2, t2,
        U32.shrn(p, 2n)), x, c)

def leaf.mid(s: Sum, +k: U32, +seed: U32, +k1: U32, +t1: U32, +k2: U32, +t2: U32,
  +i: U32) -> Sum:
  match s:
    case Sum{x, c}:
      leaf.slots(U32.to_nat(k), seed, k1, t1, k2, t2, i, x, c)

# the r bytes after the first four: bytewise up to a slot edge, whole slots,
# bytewise to the end
def leaf.rest(s: Sum, +r: U32, +seed: U32, +k1: U32, +t1: U32, +k2: U32, +t2: U32,
  +p: U32) -> Sum:
  match s:
    case Sum{+m, c}:
      +l = alive(m)
      +a = U32.min(U32.and(U32.sub(0, p), 3), r)
      +q = U32.add(p, a)
      +ns = U32.shrn(U32.sub(r, a), 2n)
      +x = common(U32.and(m, l))
      leaf.end(l, leaf.bytes(leaf.mid(leaf.bytes(Sum{x, c}, a, seed, k1, t1, k2, t2, p),
        ns, seed, k1, t1, k2, t2, U32.shrn(q, 2n)), U32.and(U32.sub(r, a), 3),
        seed, k1, t1, k2, t2, U32.add(q, U32.shln(ns, 2n))))

def leaf.short(c: Bool, s: Sum, +n: U32, +seed: U32, +k1: U32, +t1: U32, +k2: U32,
  +t2: U32, +p: U32) -> Sum:
  match c:
    case True{}:
      s # under four bytes: no convergence promised, keep the full map
    case False{}:
      leaf.rest(s, U32.sub(n, 4), seed, k1, t1, k2, t2, U32.add(p, 4))

# one leaf: the map of n bytes from p, and how many scalars start there
def leaf(+n: U32, +seed: U32, +k1: U32, +t1: U32, +k2: U32, +t2: U32, +p: U32) -> Sum:
  leaf.short(U32.is_lt(n, 4), leaf.gen(U32.to_nat(U32.min(n, 4)), seed, k1, t1, k2,
    t2, p, slot(seed, k1, t1, k2, t2, U32.shrn(p, 2n)), ident(), 0), n, seed, k1,
    t1, k2, t2, p)

def join(l: Sum, r: Sum) -> Sum:
  match l r:
    case Sum{fl, cl} Sum{fr, cr}:
      Sum{then(fl, fr), U32.add(cl, cr)}

# 2^d leaves over n bytes from lo; odd n splits unevenly, and a split lands
# mid-scalar as often as not -- which is the point
def tree(d: Nat, +seed: U32, +k1: U32, +t1: U32, +k2: U32, +t2: U32, +lo: U32,
  +n: U32) -> Sum:
  match d:
    case 0n:
      leaf(n, seed, k1, t1, k2, t2, lo)
    case 1n++p:
      +h = U32.shr(n)
      l r = tree(p, seed, k1, t1, k2, t2, lo, h) tree(p, seed, k1, t1, k2, t2, U32.add(lo, h), U32.sub(n, h))
      join(l, r)

def run(d: Nat, w: Where, +lo: U32, +n: U32) -> Sum:
  match w:
    case Where{+seed, +k1, +t1, +k2, +t2}:
      tree(d, seed, k1, t1, k2, t2, lo, n)

# -- where it died --------------------------------------------------------------

def none() -> U32:
  4294967295

# the first byte at or after p that kills a DFA standing in state s, else
# none(). No early exit (a def may only call itself), but DEAD is absorbing, so
# once `at` is set it stays set.
def walk(k: Nat, +seed: U32, +k1: U32, +t1: U32, +k2: U32, +t2: U32, +p: U32,
  +s: U32, +at: U32) -> U32:
  match k:
    case 0n:
      at
    case 1n++q:
      +s2 = look(cls(byte(seed, k1, t1, k2, t2, p)), s)
      +first = Bool.and(U32.is_eq(s2, 8), U32.is_eq(at, none()))
      walk(q, seed, k1, t1, k2, t2, U32.inc(p), s2, Bool.pick(U32, first, p, at))

# where a DFA entering the left half in state s leaves it (8: it died there)
def enter(l: Sum, +s: U32) -> U32:
  match l:
    case Sum{f, _}:
      look(f, s)

# Descend the same tree: the left half's map says whether a DFA entering it in
# state s dies inside, so only one child is ever entered -- O(n) in all.
def dead(d: Nat, +seed: U32, +k1: U32, +t1: U32, +k2: U32, +t2: U32, +lo: U32,
  +n: U32, +s: U32) -> U32:
  match d:
    case 0n:
      walk(U32.to_nat(n), seed, k1, t1, k2, t2, lo, s, none())
    case 1n++p:
      +h = U32.shr(n)
      +mid = enter(tree(p, seed, k1, t1, k2, t2, lo, h), s)
      +left = U32.is_eq(mid, 8)
      dead(p, seed, k1, t1, k2, t2, Bool.pick(U32, left, lo, U32.add(lo, h)),
        Bool.pick(U32, left, h, U32.sub(n, h)), Bool.pick(U32, left, s, mid))

def died(d: Nat, w: Where, +lo: U32, +n: U32) -> U32:
  match w:
    case Where{+seed, +k1, +t1, +k2, +t2}:
      dead(d, seed, k1, t1, k2, t2, lo, n, 0)

# -- the report -------------------------------------------------------------------

def digits(+m: U32) -> String:
  U32.show(nib(m, 0n)) ++ U32.show(nib(m, 4n)) ++ U32.show(nib(m, 8n)) ++ U32.show(nib(m, 12n))
    ++ U32.show(nib(m, 16n)) ++ U32.show(nib(m, 20n)) ++ U32.show(nib(m, 24n)) ++ U32.show(nib(m, 28n))

def same(+a: Sum, b: Sum) -> Bool:
  match a b:
    case Sum{fa, ca} Sum{fb, cb}:
      Bool.and(U32.is_eq(fa, fb), U32.is_eq(ca, cb))

def yes(c: Bool) -> String:
  match c:
    case True{}:
      "yes"
    case False{}:
      "no"

def where.if(c: Bool, +p: U32, +lo: U32, +n: U32) -> String:
  match c:
    case True{}:
      U32.show(n) # never died: it ran out of bytes mid-scalar
    case False{}:
      U32.show(U32.sub(p, lo))

def where.at(+p: U32, +lo: U32, +n: U32) -> String:
  where.if(U32.is_eq(p, none()), p, lo, n)

def verdict(ok: Bool, +w: Where, +lo: U32, +n: U32) -> String:
  match ok:
    case True{}:
      "-"
    case False{}:
      where.at(died(11n, w, lo, n), lo, n)

def agree(+w: Where, +lo: U32, +n: U32) -> Bool:
  +a = run(0n, w, lo, n)
  +d = died(0n, w, lo, n)
  Bool.and(Bool.and(same(a, run(1n, w, lo, n)), same(a, run(5n, w, lo, n))),
    Bool.and(Bool.and(same(a, run(11n, w, lo, n)), same(a, run(15n, w, lo, n))),
      Bool.and(U32.is_eq(d, died(5n, w, lo, n)), U32.is_eq(d, died(15n, w, lo, n)))))

def show.go(+m: U32, c: U32, name: String, +w: Where, +lo: U32, +n: U32) -> String:
  +ok = U32.is_eq(nib(m, 0n), 0)
  name ++ " n=" ++ U32.show(n) ++ " map=" ++ digits(m) ++ " valid=" ++ yes(ok)
    ++ " cps=" ++ U32.show(c) ++ " dead=" ++ verdict(ok, w, lo, n)
    ++ " splits 0 1 5 11 15: " ++ Bool.pick(String, agree(w, lo, n), "same", "DIFFER")

def show(s: Sum, name: String, +w: Where, +lo: U32, +n: U32) -> String:
  match s:
    case Sum{+m, c}:
      show.go(m, c, name, w, lo, n)

def report(name: String, +w: Where, +lo: U32, +n: U32) -> String:
  show(run(7n, w, lo, n), name, w, lo, n)

def clean(seed: U32) -> Where:
  Where{seed, none(), 0, none(), 0}

def hurt(+k: U32) -> Where:
  Where{U32.add(9, k), U32.add(1000, U32.mul(97, k)), k, 3000, U32.mod(U32.add(k, 3), 8)}

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(report("clean", clean(1), 0, 16384))
    IO.print(report("cut", clean(3), 0, 16393))
    IO.print(report("mid", clean(3), 1, 16000))
    IO.print(report("poison0", hurt(0), 0, 20001))
    IO.print(report("poison1", hurt(1), 0, 20001))
    IO.print(report("poison2", hurt(2), 0, 20001))
    IO.print(report("poison3", hurt(3), 0, 20001))
    IO.print(report("poison4", hurt(4), 0, 20001))
    IO.print(report("poison5", hurt(5), 0, 20001))
    IO.print(report("poison6", hurt(6), 0, 20001))
    IO.print(report("poison7", hurt(7), 0, 20001))
#|clean n=16384 map=08888888 valid=yes cps=9684 dead=- splits 0 1 5 11 15: same
#|cut n=16393 map=38888888 valid=no cps=9766 dead=16393 splits 0 1 5 11 15: same
#|mid n=16000 map=88818818 valid=no cps=9530 dead=0 splits 0 1 5 11 15: same
#|poison0 n=20001 map=88888888 valid=no cps=11874 dead=4000 splits 0 1 5 11 15: same
#|poison1 n=20001 map=88888888 valid=no cps=11900 dead=4388 splits 0 1 5 11 15: same
#|poison2 n=20001 map=88888888 valid=no cps=11887 dead=4777 splits 0 1 5 11 15: same
#|poison3 n=20001 map=88888888 valid=no cps=11940 dead=5166 splits 0 1 5 11 15: same
#|poison4 n=20001 map=88888888 valid=no cps=11984 dead=5552 splits 0 1 5 11 15: same
#|poison5 n=20001 map=88888888 valid=no cps=11860 dead=5941 splits 0 1 5 11 15: same
#|poison6 n=20001 map=88888888 valid=no cps=11893 dead=6329 splits 0 1 5 11 15: same
#|poison7 n=20001 map=88888888 valid=no cps=11899 dead=6718 splits 0 1 5 11 15: same
