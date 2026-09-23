# The laws of power/deflate.bend and power/gzip.bend. They are stated
# here and proved in deflate_proof.bend; `bun bend2/main.ts
# power/deflate_proof.bend` is the gate, and prints "All terms check."
# only when every one of them holds.
import Base
import ../wire/reader.bend as Wr
import ./deflate.bend as D
import ./gzip.bend as Z

# The reads
# =========

# LAW: chunking does not change the decode. Feeding a read and then the
# next lands exactly where feeding the two joined would have: a code, a
# length and its distance, a stored block's LEN, a dynamic header cut
# anywhere, to the bit, read as the stream whole.
law inflate_split:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +st: D.St
  {D.feed_list(List.append(&2, U32, a, b), st) == D.feed_list(b, D.feed_list(a, st)) : D.St}

# LAW: the walk over a read's Bytes is the machine over its bytes ...
law inflate_buf:
  for +s: Bytes()
  for +st: D.St
  {D.feed(s, st) == D.feed_list(Bytes.to_list(s), st) : D.St}

# ... so reads cut anywhere decode as the stream whole.
law inflate_buf_split:
  for +a: Bytes()
  for +b: Bytes()
  for +st: D.St
  {D.feed(Bytes.append(a, b), st) == D.feed(b, D.feed(a, st)) : D.St}

# LAW: a refusal is terminal, and so is the end: no byte moves the
# machine out of Bad or End (at any bit of a byte), so nothing after a
# refused byte revives the stream and nothing after its end is read.
law inflate_bad:
  for +s: List<&2, U32>
  for +why: D.Why
  for +o: D.O
  for +bp: Nat
  for lt: {Nat.is_lt(bp, 8n) == True{} : Bool}
  {D.feed_list(s, D.St{D.Bad{why}, o, bp}) == D.St{D.Bad{why}, o, bp} : D.St}

law inflate_end:
  for +s: List<&2, U32>
  for +o: D.O
  for +bp: Nat
  for lt: {Nat.is_lt(bp, 8n) == True{} : Bool}
  {D.feed_list(s, D.St{D.End{}, o, bp}) == D.St{D.End{}, o, bp} : D.St}

# LAW: the same for gunzip: chunking never changes a read ...
law gunzip_split:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +g: Z.G
  {Z.feed_list(List.append(&2, U32, a, b), g) == Z.feed_list(b, Z.feed_list(a, g)) : Z.G}

law gunzip_buf:
  for +s: Bytes()
  for +g: Z.G
  {Z.feed(s, g) == Z.feed_list(Bytes.to_list(s), g) : Z.G}

# ... and a refused file stays refused, at the byte that broke it.
law gunzip_bad:
  for +s: List<&2, U32>
  for +at: Nat
  for +why: Z.Why
  for +done: Bytes()
  for +crc: U32
  for +cap: Nat
  for +pos: Nat
  {Z.feed_list(s, Z.G{Z.Bad{at, why}, done, crc, cap, pos}) ==
    Z.G{Z.Bad{at, why}, done, crc, cap, pos} : Z.G}
