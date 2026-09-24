# std's bytes on this repo's runtime: the interface (std/bytes.bend) over
# Base's Bytes() natives, which pack a byte a cell, cut by view and scan
# with memchr. It needs this repo's Base: released Bend has no Bytes, so
# std/bytes.bend imports std/bytes_list.bend there instead.
#
# Every name here means what the same name in bytes_list.bend means; the
# laws are the same laws, proved here of Base's bodies (the definitions
# the natives are held to).
import Base
import ./bytes_spec.bend as Sp

# Byte strings
# ============

def get(+b: String, +i: Nat) -> U32:
  Bytes.get(b, i)

def byte(m: Maybe<&2, Char>) -> U32:
  Bytes.byte(m)

def len.go(s: String, m: Nat) -> Nat:
  String.length.go(s, m)

def len(+b: String) -> Nat:
  Bytes.len(b)

def len.shift(+s: String, +m: Nat) -> {len.go(s, 1n+m) == 1n+len.go(s, m) : Nat}:
  Bytes.len.shift(s, m)

def from_list(xs: List<&2, U32>) -> String:
  Bytes.from_list(xs)

def to_list(b: String) -> List<&2, U32>:
  Bytes.to_list(b)

def push(b: String, x: U32) -> String:
  Bytes.push(b, x)

def cut(+s: String, +n: Nat) -> String & String:
  String.cut(s, n)

def cut.is(+s: String, +n: Nat) -> {cut(s, n) == (String.take(s, n), String.drop(s, n)) : String & String}:
  {==}

def slice(b: String, +at: Nat, n: Nat) -> String:
  Bytes.slice(b, at, n)

def find(+b: String, +p: String) -> Maybe<&2, Nat>:
  Bytes.find(b, p)

def find_byte(+b: String, +i: Nat, x: U32) -> Nat:
  Bytes.find_byte(b, i, x)

def find_any(+b: String, +i: Nat, w: U32, x: U32, y: U32, z: U32) -> Nat:
  Bytes.find_any(b, i, w, x, y, z)

def span(+b: String, +i: Nat, lo: U32, hi: U32) -> Nat:
  Bytes.span(b, i, lo, hi)

def word_le(+b: String, +i: Nat) -> U32:
  Bytes.word_le(b, i)

# The laws
# --------

def list(xs: List<&2, U32>) -> {to_list(from_list(xs)) == xs : List<&2, U32>}:
  Bytes.list(xs)

def to_list_append(+a: String, +b: String) ->
  {to_list(String.append(a, b)) == List.append(&2, U32, to_list(a), to_list(b)) : List<&2, U32>}:
  Bytes.to_list_append(a, b)

def push_list(+b: String, +x: U32) ->
  {to_list(push(b, x)) == List.append(&2, U32, to_list(b), Con{x, Nil{}}) : List<&2, U32>}:
  Bytes.push_list(b, x)

# Base's walks count what the specification's do
def find_byte.go_is.at(hit: Bool, +t: String, +x: U32,
  ih: {Bytes.find_byte.go(t, x) == Sp.find_byte.go(t, x) : Nat}) ->
  {Bytes.find_byte.at(hit, t, x) == Sp.sel(hit, Sp.find_byte.go(t, x)) : Nat}:
  match hit:
    case True{}:
      {==}
    case False{}:
      Equal.cong(Nat, Nat, y => 1n+y, Bytes.find_byte.go(t, x), Sp.find_byte.go(t, x), ih)

def find_byte.go_is(+s: String, +x: U32) -> {Bytes.find_byte.go(s, x) == Sp.find_byte.go(s, x) : Nat}:
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{+c}, t}:
      find_byte.go_is.at(U32.is_eq(c, x), t, x, find_byte.go_is(t, x))

def find_any.go_is.at(hit: Bool, +t: String, +w: U32, +x: U32, +y: U32, +z: U32,
  ih: {Bytes.find_any.go(t, w, x, y, z) == Sp.find_any.go(t, w, x, y, z) : Nat}) ->
  {Bytes.find_any.at(hit, t, w, x, y, z) == Sp.sel(hit, Sp.find_any.go(t, w, x, y, z)) : Nat}:
  match hit:
    case True{}:
      {==}
    case False{}:
      Equal.cong(Nat, Nat, v => 1n+v, Bytes.find_any.go(t, w, x, y, z), Sp.find_any.go(t, w, x, y, z), ih)

def find_any.go_is(+s: String, +w: U32, +x: U32, +y: U32, +z: U32) ->
  {Bytes.find_any.go(s, w, x, y, z) == Sp.find_any.go(s, w, x, y, z) : Nat}:
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{+c}, t}:
      find_any.go_is.at(Bytes.find_any.in(c, w, x, y, z), t, w, x, y, z, find_any.go_is(t, w, x, y, z))

def find_byte.is(+b: String, +i: Nat, +x: U32) ->
  {find_byte(b, i, x) == Nat.add(i, Sp.find_byte.go(String.drop(b, i), x)) : Nat}:
  Equal.cong(Nat, Nat, y => Nat.add(i, y), Bytes.find_byte.go(String.drop(b, i), x),
    Sp.find_byte.go(String.drop(b, i), x), find_byte.go_is(String.drop(b, i), x))

def find_any.is(+b: String, +i: Nat, +w: U32, +x: U32, +y: U32, +z: U32) ->
  {find_any(b, i, w, x, y, z) == Nat.add(i, Sp.find_any.go(String.drop(b, i), w, x, y, z)) : Nat}:
  Equal.cong(Nat, Nat, v => Nat.add(i, v), Bytes.find_any.go(String.drop(b, i), w, x, y, z),
    Sp.find_any.go(String.drop(b, i), w, x, y, z), find_any.go_is(String.drop(b, i), w, x, y, z))

# The reader
# ==========
#
# A packed buffer reads any byte in one load, so the reader is the
# buffer itself and moving it costs nothing.

def Buf() -> Data:
  String

def open(s: String) -> Buf():
  s

def bytes(b: Buf()) -> String:
  b

def size(+b: Buf()) -> Buf() & U32:
  +n = U32.from_nat(Bytes.len(b))
  (b, n)

# the byte at i, 0 past the end
def at(+b: Buf(), +i: U32) -> Buf() & U32:
  +x = U32.and(Bytes.get(b, U32.to_nat(i)), 255)
  (b, x)

# the n bytes from at: a view, nothing copied
def take(+b: Buf(), +at: U32, +n: U32) -> Buf() & String:
  +s = Bytes.slice(b, U32.to_nat(at), U32.to_nat(n))
  (b, s)

# Files
# =====

def read_chunk(file: File, max: U32) -> IO(File & Result<&1, &1, U32 & String, String>):
  File.read_buf(file, max)

def chunk_size() -> U32:
  65536

def write(file: File, data: String) -> IO(File & Result<&1, &1, U32 & String, Unit>):
  File.write_buf(file, data)

# The writer
# ==========
#
# A packed buffer with one owner appends in place, so the writer is the
# buffer itself.
def Out() -> Data:
  String

def out.new() -> Out():
  ""

def out.add(o: Out(), s: String) -> Out():
  String.append(o, s)

def out.push(o: Out(), x: U32) -> Out():
  Bytes.push(o, x)

def out.done(o: Out()) -> String:
  o
