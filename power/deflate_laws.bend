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

# CRC-32
# ======

# The reference: the register a bit at a time, eight bits to a byte,
# each bit D.crc.bit -- shift right, and fold in the polynomial
# 0xEDB88320 when the bit shifted out is 1 -- the byte first xored into
# the register's low eight bits. As RFC 1952 8 and ISO 3309 give it.
def crc_ref(x: Bytes(), c: U32) -> U32:
  match x:
    case SNil{}:
      c
    case SCon{Chr{b}, t}:
      crc_ref(t, D.crc.bits(8n, U32.xor(c, U32.and(b, 255))))

# LAW: the table-driven CRC-32 is the bit-at-a-time one, for every input
# and every CRC it is continued from: the table's 256 cells are right,
# and a byte folded in by its cell is the byte's eight bits folded in.
law crc32_ref:
  for +x: Bytes()
  for +prev: U32
  {D.crc32(x, prev) == U32.not(crc_ref(x, U32.not(prev))) : U32}

# Round trips
# ===========

# LAW: stored blocks read back. Any bytes (each below 256, as Bytes()
# promises), stored at level 0 as blocks of 65535 and the rest, inflate
# to themselves under any cap they fit: every header, LEN, NLEN, byte
# and block boundary as the writer put it, to the bit.
law stored_round_trip:
  for +x: Bytes()
  for +cap: Nat
  for +vx: {D.valid(x) == True{} : Bool}
  for fits: {Nat.is_le(Bytes.len(x), cap) == True{} : Bool}
  {D.inflate(cap, D.deflate(x, 0n)) == Done{x} : Result<&2, &2, D.Why, Bytes()>}
