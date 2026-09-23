# Bytes: power's names over Base's one byte type, `Bytes()` -- a String whose
# every Char is below 256, which the C runtime packs a byte a cell, cuts by view
# (slice and drop copy nothing) and appends to in place when it has one owner.
# It is what the IO effects hand back (TCP.recv_buf, File.read_buf), so a
# buffer read off a socket goes to json, blake3 or cdc with no conversion.
#
# Bytes() is Data, so a read needs no threading; the reads here still hand the
# buffer back beside their answer, the shape every power caller was written
# in, and cost one reference count for it. Indexes are U32, as power's are.
#
# A read past the end answers 0 (Base's Bytes.get answers 256 there): the
# scanners over it read a few bytes ahead of the width they end up wanting and
# mask what they read, as they did over the packed cells this module used to be.
import Base

# the byte at i, 0 past the end
def byte(+b: Bytes(), +i: U32) -> U32:
  U32.and(Bytes.get(b, U32.to_nat(i)), 255)

def new() -> Bytes():
  ""

def len(+b: Bytes()) -> Bytes() & U32:
  (b, U32.from_nat(Bytes.len(b)))

# at: unchecked, 0 past the end
def at(+b: Bytes(), +i: U32) -> Bytes() & U32:
  (b, byte(b, i))

def get.if(+b: Bytes(), +i: U32, ok: Bool) -> Bytes() & Maybe<&2, U32>:
  match ok:
    case True{}:
      (b, Some{byte(b, i)})
    case False{}:
      (b, None{})

def get(+b: Bytes(), +i: U32) -> Bytes() & Maybe<&2, U32>:
  get.if(b, i, Nat.is_lt(U32.to_nat(i), Bytes.len(b)))

# word_le: the four bytes at byte index i, little end first, as one U32; the
# bytes past the end count as 0
def word_le(+b: Bytes(), +i: U32) -> Bytes() & U32:
  (b, U32.or(U32.or(byte(b, i), U32.shln(byte(b, U32.add(i, 1)), 8n)),
    U32.or(U32.shln(byte(b, U32.add(i, 2)), 16n), U32.shln(byte(b, U32.add(i, 3)), 24n))))

# the one-byte buffer holding the low eight bits of x
def one(x: U32) -> Bytes():
  SCon{Chr{U32.and(x, 255)}, SNil{}}

# put: unchecked write of the low eight bits of x into slot i. Base has no
# in-place byte write, so this is two views and a join: O(n), and nothing in
# power writes a byte back into the middle of a buffer.
def put(+b: Bytes(), +i: U32, x: U32) -> Bytes():
  Bytes.concat([Bytes.slice(b, 0n, U32.to_nat(i)), one(x), Bytes.drop(b, 1n+U32.to_nat(i))])

def set.if(b: Bytes(), i: U32, x: U32, ok: Bool) -> Bytes() & Bool:
  match ok:
    case True{}:
      (put(b, i, x), True{})
    case False{}:
      (b, False{})

def set(+b: Bytes(), +i: U32, x: U32) -> Bytes() & Bool:
  set.if(b, i, x, Nat.is_lt(U32.to_nat(i), Bytes.len(b)))

# push: in place while the buffer has one owner and room, else it doubles.
# (String.pad_end to one past the length writes into the room without the
# one-byte buffer and is 1.6x faster on C, but its JS twin measures the length
# every call, which makes a filling loop quadratic there.)
def push(b: Bytes(), x: U32) -> Bytes():
  Bytes.append(b, one(x))

def pop.if(+b: Bytes(), +n: Nat, empty: Bool) -> Bytes() & Maybe<&2, U32>:
  match empty:
    case True{}:
      (b, None{})
    case False{}:
      (Bytes.slice(b, 0n, Nat.sub(n, 1n)), Some{U32.and(Bytes.get(b, Nat.sub(n, 1n)), 255)})

def pop(+b: Bytes()) -> Bytes() & Maybe<&2, U32>:
  +n = Bytes.len(b)
  pop.if(b, n, Nat.is_eq(n, 0n))

# slice: a view of n bytes from at, clamped to the end; nothing is copied
def slice(b: Bytes(), +at: U32, +n: U32) -> Bytes():
  Bytes.slice(b, U32.to_nat(at), U32.to_nat(n))

# truncate: a view of the first k bytes; nothing moves
def truncate(b: Bytes(), +k: U32) -> Bytes():
  Bytes.slice(b, 0n, U32.to_nat(k))

# from_list: the list's bytes pushed onto b, each its low eight bits
def bytes(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{U32.and(x, 255), bytes(t)}

def from_list(xs: List<&2, U32>, b: Bytes()) -> Bytes():
  Bytes.append(b, Bytes.from_list(bytes(xs)))

def to_list(+b: Bytes()) -> Bytes() & List<&2, U32>:
  (b, Bytes.to_list(b))
