# std's bytes on released Bend: every operation of the interface
# (std/bytes.bend) written in plain Bend over canon's Base, so it runs on
# any Bend, stock runtime or ours. A byte string is a String whose every
# Char is below 256, as Base's Bytes() is on our runtime; here nothing is
# packed, so a byte is a cell and a read at i walks i cells.
#
# The definitions a proof unfolds (get, len.go, cut, push, to_list,
# from_list) are word for word the bodies this repo's Base gives its Bytes
# natives, and the scans (find_byte, find_any, span) are loops proved to
# count what bytes_spec.bend says, so a law proved over the interface
# holds here too. The random-access reader (Buf, at, take) is where the
# two differ most: here it is a cursor that remembers where the last read
# landed, so a scan that only moves forward walks each cell once.
import Base
import ./bytes_spec.bend as Sp

# Byte strings
# ============

def byte(m: Maybe<&2, Char>) -> U32:
  match m:
    case None{}:
      256
    case Some{Chr{c}}:
      c

# the byte at i; past the end, 256, which no byte is
def get(+b: String, +i: Nat) -> U32:
  byte(String.get(b, i))

# the length, counted in an accumulator (a loop, as this repo's
# String.length is: the proofs count with len.go and len.shift)
def len.go(s: String, m: Nat) -> Nat:
  match s:
    case SNil{}:
      m
    case SCon{h, t}:
      len.go(t, 1n+m)

def len(+b: String) -> Nat:
  len.go(b, 0n)

def len.shift(+s: String, +m: Nat) -> {len.go(s, 1n+m) == 1n+len.go(s, m) : Nat}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      len.shift(t, 1n+m)

def from_list(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      SNil{}
    case Con{h, t}:
      SCon{Chr{h}, from_list(t)}

def to_list(b: String) -> List<&2, U32>:
  match b:
    case SNil{}:
      Nil{}
    case SCon{Chr{c}, t}:
      Con{c, to_list(t)}

# b with the byte x on its end
def push(b: String, x: U32) -> String:
  String.append(b, SCon{Chr{x}, SNil{}})

# the first n bytes and the rest
# String.drop, counted on n first: dropping none hands s back as it is,
# where String.drop takes s apart and builds it again (on the JS lane a
# fresh string, which the next slice copies whole)
def tail(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{h, t}:
      t

def skip(n: Nat, s: String) -> String:
  match n:
    case 0n:
      s
    case 1n+p:
      skip(p, tail(s))

def skip.nil(n: Nat) -> {skip(n, SNil{}) == SNil{} : String}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      skip.nil(p)

def skip.is(+s: String, +n: Nat) -> {skip(n, s) == String.drop(s, n) : String}:
  match s n:
    case SNil{} 0n:
      {==}
    case SNil{} 1n+p:
      skip.nil(p)
    case SCon{h, t} 0n:
      {==}
    case SCon{h, t} 1n+p:
      skip.is(t, p)

def cut(+s: String, +n: Nat) -> String & String:
  (String.take(s, n), skip(n, s))

# cut is the pair of Base's take and drop
def cut.is(+s: String, +n: Nat) -> {cut(s, n) == (String.take(s, n), String.drop(s, n)) : String & String}:
  Equal.cong(String, String & String, x => (String.take(s, n), x), skip(n, s), String.drop(s, n),
    skip.is(s, n))

# n bytes from at, clamped to the end
def slice(b: String, +at: Nat, n: Nat) -> String:
  String.take(String.drop(b, at), n)

def find.go(s: String, +p: String, i: Nat, hit: Bool) -> Maybe<&2, Nat>:
  match s hit:
    case _ True{}:
      Some{i}
    case SNil{} False{}:
      None{}
    case SCon{h, +t} False{}:
      find.go(t, p, 1n+i, String.starts_with(t, p))

# the first offset of p in b; the empty p is found at 0
def find(+b: String, +p: String) -> Maybe<&2, Nat>:
  find.go(b, p, 0n, String.starts_with(b, p))

# The scans
# ---------
#
# A scan is one self-recursive loop (outside Base a def may only call
# itself), counting in an accumulator, so a long run is a loop and never
# a deep stack. std/bytes_spec.bend states what each counts, and the
# .is laws below prove each counts it.

# the offset of the first x in s, counted from k; on is False once the
# byte before was x
def find_byte.run(s: String, +x: U32, on: Bool, k: Nat) -> Nat:
  match s on:
    case _ False{}:
      k
    case SNil{} True{}:
      k
    case SCon{Chr{+c}, t} True{}:
      +go = Bool.not(U32.is_eq(c, x))
      find_byte.run(t, x, go, Sp.inc(go, k))

# the first offset of the byte x at or after i; absent, the end
def find_byte(+b: String, +i: Nat, x: U32) -> Nat:
  find_byte.run(skip(i, b), x, True{}, i)

def find_any.run(s: String, +w: U32, +x: U32, +y: U32, +z: U32, on: Bool, k: Nat) -> Nat:
  match s on:
    case _ False{}:
      k
    case SNil{} True{}:
      k
    case SCon{Chr{+c}, t} True{}:
      +go = Bool.not(Sp.find_any.in(c, w, x, y, z))
      find_any.run(t, w, x, y, z, go, Sp.inc(go, k))

# the first offset at or after i of any of w, x, y, z; absent, the end
def find_any(+b: String, +i: Nat, w: U32, x: U32, y: U32, z: U32) -> Nat:
  find_any.run(skip(i, b), w, x, y, z, True{}, i)

def span.run(s: String, +lo: U32, +hi: U32, on: Bool, k: Nat) -> Nat:
  match s on:
    case _ False{}:
      k
    case SNil{} True{}:
      k
    case SCon{Chr{+c}, t} True{}:
      +go = Sp.span.in(c, lo, hi)
      span.run(t, lo, hi, go, Sp.inc(go, k))

# how many bytes from i are in [lo, hi)
def span(+b: String, +i: Nat, lo: U32, hi: U32) -> Nat:
  span.run(skip(i, b), lo, hi, True{}, 0n)

def word_le.at(+b: String, i: Nat) -> U32:
  U32.and(get(b, i), 255)

# the four bytes from i as one U32, little end first, a byte past the end 0
def word_le(+b: String, +i: Nat) -> U32:
  U32.or(U32.or(word_le.at(b, i), U32.shln(word_le.at(b, 1n+i), 8n)),
    U32.or(U32.shln(word_le.at(b, 2n+i), 16n), U32.shln(word_le.at(b, 3n+i), 24n)))

# The laws the interface promises
# -------------------------------

def list(xs: List<&2, U32>) -> {to_list(from_list(xs)) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(List<&2, U32>, List<&2, U32>, ys => Con{h, ys},
        to_list(from_list(t)), t, list(t))

def to_list_append(+a: String, +b: String) ->
  {to_list(String.append(a, b)) == List.append(&2, U32, to_list(a), to_list(b)) : List<&2, U32>}:
  match a:
    case SNil{}:
      {==}
    case SCon{Chr{c}, t}:
      Equal.cong(List<&2, U32>, List<&2, U32>, ys => Con{c, ys},
        to_list(String.append(t, b)), List.append(&2, U32, to_list(t), to_list(b)),
        to_list_append(t, b))

def push_list(+b: String, +x: U32) ->
  {to_list(push(b, x)) == List.append(&2, U32, to_list(b), Con{x, Nil{}}) : List<&2, U32>}:
  to_list_append(b, SCon{Chr{x}, SNil{}})

# each loop counts what its specification does, from any k
def find_byte.run_is(+s: String, +x: U32, on: Bool, +k: Nat) ->
  {find_byte.run(s, x, on, k) == Nat.add(k, Sp.flag(on, Sp.find_byte.go(s, x))) : Nat}:
  match s on:
    case SNil{} False{}:
      Sp.add0(k)
    case SCon{Chr{c}, t} False{}:
      Sp.add0(k)
    case SNil{} True{}:
      Sp.add0(k)
    case SCon{Chr{+c}, t} True{}:
      Sp.inc_add(U32.is_eq(c, x), k,
        find_byte.run(t, x, Bool.not(U32.is_eq(c, x)), Sp.inc(Bool.not(U32.is_eq(c, x)), k)),
        Sp.find_byte.go(t, x),
        find_byte.run_is(t, x, Bool.not(U32.is_eq(c, x)), Sp.inc(Bool.not(U32.is_eq(c, x)), k)))

def find_any.run_is(+s: String, +w: U32, +x: U32, +y: U32, +z: U32, on: Bool, +k: Nat) ->
  {find_any.run(s, w, x, y, z, on, k) == Nat.add(k, Sp.flag(on, Sp.find_any.go(s, w, x, y, z))) : Nat}:
  match s on:
    case SNil{} False{}:
      Sp.add0(k)
    case SCon{Chr{c}, t} False{}:
      Sp.add0(k)
    case SNil{} True{}:
      Sp.add0(k)
    case SCon{Chr{+c}, t} True{}:
      Sp.inc_add(Sp.find_any.in(c, w, x, y, z), k,
        find_any.run(t, w, x, y, z, Bool.not(Sp.find_any.in(c, w, x, y, z)),
          Sp.inc(Bool.not(Sp.find_any.in(c, w, x, y, z)), k)),
        Sp.find_any.go(t, w, x, y, z),
        find_any.run_is(t, w, x, y, z, Bool.not(Sp.find_any.in(c, w, x, y, z)),
          Sp.inc(Bool.not(Sp.find_any.in(c, w, x, y, z)), k)))

# find_byte and find_any are their specifications' counts from i
def find_byte.is(+b: String, +i: Nat, +x: U32) ->
  {find_byte(b, i, x) == Nat.add(i, Sp.find_byte.go(String.drop(b, i), x)) : Nat}:
  %skip.is(b, i) : {find_byte(b, i, x) == Nat.add(i, Sp.find_byte.go(_, x)) : Nat}
  find_byte.run_is(skip(i, b), x, True{}, i)

def find_any.is(+b: String, +i: Nat, +w: U32, +x: U32, +y: U32, +z: U32) ->
  {find_any(b, i, w, x, y, z) == Nat.add(i, Sp.find_any.go(String.drop(b, i), w, x, y, z)) : Nat}:
  %skip.is(b, i) : {find_any(b, i, w, x, y, z) == Nat.add(i, Sp.find_any.go(_, w, x, y, z)) : Nat}
  find_any.run_is(skip(i, b), w, x, y, z, True{}, i)

# The reader
# ==========
#
# A cursor over a byte string: the whole string, the rest from pos, and
# the length. at(b, i) walks from the cursor when i is at or past it
# (from the start when it is behind), and leaves the cursor at i, so a
# scanner that reads forward pays one cell a byte.
type Cur is Data:
  Cur{whole: String, rest: String, pos: Nat, n: Nat}

def Buf() -> Data:
  Cur

def open(s: String) -> Buf():
  +s = s
  Cur{s, s, 0n, String.length(s)}

def bytes(b: Buf()) -> String:
  match b:
    case Cur{whole, rest, pos, n}:
      whole

def size(b: Buf()) -> Buf() & U32:
  match b:
    case Cur{whole, rest, pos, +n}:
      (Cur{whole, rest, pos, n}, U32.from_nat(n))

def seek.if(+whole: String, rest: String, +pos: Nat, +n: Nat, +k: Nat, ahead: Bool) -> Buf():
  match ahead:
    case True{}:
      Cur{whole, skip(Nat.sub(k, pos), rest), k, n}
    case False{}:
      Cur{whole, skip(k, whole), k, n}

# the cursor moved to k
def seek(b: Buf(), +k: Nat) -> Buf():
  match b:
    case Cur{+whole, rest, +pos, +n}:
      seek.if(whole, rest, pos, n, k, Nat.is_le(pos, k))

# the first byte, 0 for none; s is only looked at, so the cursor keeps the
# very string it had (rebuilding SCon{h, t} is a fresh string on the JS
# lane, which its next slice copies whole)
def first(+s: String) -> U32:
  match s:
    case SNil{}:
      0
    case SCon{Chr{c}, t}:
      U32.and(c, 255)

def head(b: Buf()) -> Buf() & U32:
  match b:
    case Cur{whole, +rest, pos, n}:
      (Cur{whole, rest, pos, n}, first(rest))

# the byte at i, 0 past the end
def at(b: Buf(), +i: U32) -> Buf() & U32:
  head(seek(b, U32.to_nat(i)))

# Loops for the JS lane: Base's String.take and a structural to_list
# recurse once a char, and canon's JS lane overflows its stack near 30000
# (UPSTREAM.md F11); these count in an accumulator instead.

# the chars of acc (newest first) in front of s
def rev(acc: List<&2, Char>, s: String) -> String:
  match acc:
    case Nil{}:
      s
    case Con{c, t}:
      rev(t, SCon{c, s})

def take.go(s: String, n: Nat, acc: List<&2, Char>) -> String:
  match s n:
    case SNil{} _:
      rev(acc, SNil{})
    case SCon{h, t} 0n:
      rev(acc, SNil{})
    case SCon{h, t} 1n+p:
      take.go(t, p, Con{h, acc})

def list.go(s: String, acc: List<&2, U32>) -> List<&2, U32>:
  match s:
    case SNil{}:
      List.reverse(&2, U32, acc)
    case SCon{Chr{c}, t}:
      list.go(t, Con{c, acc})

def take.fin(+n: Nat, b: Buf()) -> Buf() & String:
  match b:
    case Cur{whole, +rest, pos, m}:
      (Cur{whole, rest, pos, m}, take.go(rest, n, Nil{}))

# the n bytes from at, as a string of their own
def take(b: Buf(), +at: U32, +n: U32) -> Buf() & String:
  take.fin(U32.to_nat(n), seek(b, U32.to_nat(at)))

# Files
# =====

def chunk.plan(got: File & Result<&1, &1, U32 & String, List<&2, U32>>) ->
  File & Result<&1, &1, U32 & String, String>:
  (file, r) = got
  match r:
    case Fail{e}:
      (file, Fail{e})
    case Done{bs}:
      (file, Done{from_list(bs)})

# up to max bytes of the file, as a byte string; the empty string at its
# end. The bytes are read as a list and joined (canon has no buffer read).
def read_chunk(file: File, max: U32) -> IO(File & Result<&1, &1, U32 & String, String>):
  IO.bind(File & Result<&1, &1, U32 & String, List<&2, U32>>,
    File & Result<&1, &1, U32 & String, String>, File.read_bytes(file, max),
    got => IO.pure(File & Result<&1, &1, U32 & String, String>, chunk.plan(got)))

# the chunk size a file loop should read: the list read builds a cell a
# byte, and a deep list is a deep stack on the JS lane
def chunk_size() -> U32:
  4096

def write(file: File, data: String) -> IO(File & Result<&1, &1, U32 & String, Unit>):
  File.write_bytes(file, list.go(data, Nil{}))

# The writer
# ==========
#
# A string built a piece at a time: here the pieces, newest first, joined
# once at the end, so a document of n bytes costs n and not n^2 (a String
# append walks its left side).
def Out() -> Data:
  List<&2, String>

def out.new() -> Out():
  Nil{}

def out.add(o: Out(), s: String) -> Out():
  Con{s, o}

def out.push(o: Out(), x: U32) -> Out():
  Con{SCon{Chr{x}, SNil{}}, o}

def out.join(o: Out(), acc: String) -> String:
  match o:
    case Nil{}:
      acc
    case Con{s, t}:
      out.join(t, String.append(s, acc))

def out.done(o: Out()) -> String:
  out.join(o, SNil{})
