# What std's byte scans count, stated once for both implementations
# (std/bytes_list.bend and std/bytes_packed.bend). Each is the plain
# structural walk: a law about a scan is proved about this, and each
# implementation proves its own scan counts this (its .is laws).
#
# A specification computes the count of the rest before it asks the
# byte (sel), which is the one way to say it without a second def:
# outside Base a def may only call itself. It is never run, only
# unfolded; the loops that run stop at the byte.
import Base

def inc(ok: Bool, k: Nat) -> Nat:
  match ok:
    case True{}:
      1n+k
    case False{}:
      k

# x, w, y or z: the test a class of four bytes is written with
def find_any.in(+c: U32, w: U32, x: U32, y: U32, z: U32) -> Bool:
  Bool.or(U32.is_eq(c, w), Bool.or(U32.is_eq(c, x), Bool.or(U32.is_eq(c, y), U32.is_eq(c, z))))

# lo <= c < hi
def span.in(+c: U32, lo: U32, hi: U32) -> Bool:
  Bool.and(Bool.not(U32.is_lt(c, lo)), Bool.not(U32.is_le(hi, c)))

# a step of a count: 0 where the walk stops, one more where it goes on
def sel(stop: Bool, n: Nat) -> Nat:
  match stop:
    case True{}:
      0n
    case False{}:
      1n+n

# n where a walk goes on, 0 where it has stopped
def flag(on: Bool, n: Nat) -> Nat:
  match on:
    case True{}:
      n
    case False{}:
      0n

# how many bytes of s come before the first x (all of them, if none is x)
def find_byte.go(s: String, +x: U32) -> Nat:
  match s:
    case SNil{}:
      0n
    case SCon{Chr{+c}, t}:
      sel(U32.is_eq(c, x), find_byte.go(t, x))

# how many bytes of s come before the first of w, x, y, z
def find_any.go(s: String, +w: U32, +x: U32, +y: U32, +z: U32) -> Nat:
  match s:
    case SNil{}:
      0n
    case SCon{Chr{+c}, t}:
      sel(find_any.in(c, w, x, y, z), find_any.go(t, w, x, y, z))

# how many bytes of s from its first are in [lo, hi)
def span.go(s: String, +lo: U32, +hi: U32) -> Nat:
  match s:
    case SNil{}:
      0n
    case SCon{Chr{+c}, t}:
      sel(Bool.not(span.in(c, lo, hi)), span.go(t, lo, hi))

# Nat.add's facts the implementations' proofs need (canon's Base has none)
def add0(+k: Nat) -> {k == Nat.add(k, 0n) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, y => 1n+y, p, Nat.add(p, 0n), add0(p))

def add_s(+k: Nat, +n: Nat) -> {Nat.add(1n+k, n) == Nat.add(k, 1n+n) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, y => 1n+y, Nat.add(1n+p, n), Nat.add(p, 1n+n), add_s(p, n))

def inc_add.go(h: Bool, +k: Nat, +g: Nat) ->
  {Nat.add(inc(Bool.not(h), k), flag(Bool.not(h), g)) == Nat.add(k, sel(h, g)) : Nat}:
  match h:
    case True{}:
      {==}
    case False{}:
      add_s(k, g)

# a loop that counted one more (or stopped) is the count one on
def inc_add(h: Bool, +k: Nat, +r: Nat, +g: Nat,
  e: {r == Nat.add(inc(Bool.not(h), k), flag(Bool.not(h), g)) : Nat}) ->
  {r == Nat.add(k, sel(h, g)) : Nat}:
  Equal.trans(Nat, r, Nat.add(inc(Bool.not(h), k), flag(Bool.not(h), g)), Nat.add(k, sel(h, g)), e,
    inc_add.go(h, k, g))
