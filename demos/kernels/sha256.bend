# FIPS 180-4 sections 4.1.2, 4.2.2, 5.1.1, 5.3.3 and 6.2: SHA-256.
# C reference: RFC 6234 section 8.2.2, sha224-256.c, SHA256Reset,
# SHA224_256ProcessMessageBlock and SHA224_256PadMessage.
# Octet messages only: List<U32> elements use their low eight bits, as C
# uint8_t does. The bit length is two U32 words (Base has no U64), modulo
# 2^64; the FIPS domain is less than 2^64 bits. No IO or native ops.
import Base

type Hash is Data:
  Hash{a: U32, b: U32, c: U32, d: U32, e: U32, f: U32, g: U32, h: U32}

def rotr(+x: U32, +n: Nat) -> U32:
  U32.or(U32.shrn(x, n), U32.shln(x, Nat.sub(32n, n)))

def small0(+x: U32) -> U32:
  U32.xor(U32.xor(rotr(x, 7n), rotr(x, 18n)), U32.shrn(x, 3n))

def small1(+x: U32) -> U32:
  U32.xor(U32.xor(rotr(x, 17n), rotr(x, 19n)), U32.shrn(x, 10n))

def big0(+x: U32) -> U32:
  U32.xor(U32.xor(rotr(x, 2n), rotr(x, 13n)), rotr(x, 22n))

def big1(+x: U32) -> U32:
  U32.xor(U32.xor(rotr(x, 6n), rotr(x, 11n)), rotr(x, 25n))

def choose(+x: U32, y: U32, z: U32) -> U32:
  U32.xor(U32.and(x, y), U32.and(U32.not(x), z))

def majority(+x: U32, +y: U32, +z: U32) -> U32:
  U32.xor(U32.xor(U32.and(x, y), U32.and(x, z)), U32.and(y, z))

def initial() -> Hash:
  Hash{1779033703, 3144134277, 1013904242, 2773480762,
    1359893119, 2600822924, 528734635, 1541459225}

def constants() -> List<&2, U32>:
  [1116352408, 1899447441, 3049323471, 3921009573,
   961987163, 1508970993, 2453635748, 2870763221,
   3624381080, 310598401, 607225278, 1426881987,
   1925078388, 2162078206, 2614888103, 3248222580,
   3835390401, 4022224774, 264347078, 604807628,
   770255983, 1249150122, 1555081692, 1996064986,
   2554220882, 2821834349, 2952996808, 3210313671,
   3336571891, 3584528711, 113926993, 338241895,
   666307205, 773529912, 1294757372, 1396182291,
   1695183700, 1986661051, 2177026350, 2456956037,
   2730485921, 2820302411, 3259730800, 3345764771,
   3516065817, 3600352804, 4094571909, 275423344,
   430227734, 506948616, 659060556, 883997877,
   958139571, 1322822218, 1537002063, 1747873779,
   1955562222, 2024104815, 2227730452, 2361852424,
   2428436474, 2756734187, 3204031479, 3329325298]

def at(ws: List<&2, U32>, n: Nat) -> U32:
  Maybe.default(&2, U32, List.get(&2, U32, ws, n), 0)

def load(+bs: List<&2, U32>) -> U32:
  U32.or(U32.or(U32.shln(at(bs, 0n), 24n), U32.shln(at(bs, 1n), 16n)),
    U32.or(U32.shln(at(bs, 2n), 8n), at(bs, 3n)))

def step(k: U32, w: U32, st: Hash) -> Hash:
  match st:
    case Hash{+a, +b, +c, d, +e, +f, +g, h}:
      +t1 = U32.add(U32.add(U32.add(h, big1(e)), choose(e, f, g)),
        U32.add(k, w))
      t2 = U32.add(big0(a), majority(a, b, c))
      Hash{U32.add(t1, t2), a, b, c, U32.add(d, t1), e, f, g}

# The head is W[t]; shifting in W[t+16] retains exactly the four recurrence lags.
def rounds(ks: List<&2, U32>, +w0: U32, +w1: U32, +w2: U32, +w3: U32, +w4: U32, +w5: U32, +w6: U32, +w7: U32, +w8: U32, +w9: U32, +w10: U32, +w11: U32, +w12: U32, +w13: U32, +w14: U32, +w15: U32, st: Hash) -> Hash:
  match ks:
    case Nil{}:
      st
    case k <> rest:
      next = U32.add(U32.add(small1(w14), w9), U32.add(small0(w1), w0))
      rounds(rest, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, next, step(k, w0, st))

def feed(x: Hash, y: Hash) -> Hash:
  match x y:
    case Hash{a, b, c, d, e, f, g, h} Hash{i, j, k, l, m, n, o, p}:
      Hash{U32.add(a, i), U32.add(b, j), U32.add(c, k), U32.add(d, l),
        U32.add(e, m), U32.add(f, n), U32.add(g, o), U32.add(h, p)}

def compress16(w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, w15: U32, +st: Hash) -> Hash:
  feed(st, rounds(constants(), w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, st))

# The legacy byte API buffers one block; it shares the register compressor.
def compress(+bs: List<&2, U32>, st: Hash) -> Hash:
  compress16(load(bs), load(List.drop(&2, U32, bs, 4n)), load(List.drop(&2, U32, bs, 8n)), load(List.drop(&2, U32, bs, 12n)), load(List.drop(&2, U32, bs, 16n)), load(List.drop(&2, U32, bs, 20n)), load(List.drop(&2, U32, bs, 24n)), load(List.drop(&2, U32, bs, 28n)), load(List.drop(&2, U32, bs, 32n)), load(List.drop(&2, U32, bs, 36n)), load(List.drop(&2, U32, bs, 40n)), load(List.drop(&2, U32, bs, 44n)), load(List.drop(&2, U32, bs, 48n)), load(List.drop(&2, U32, bs, 52n)), load(List.drop(&2, U32, bs, 56n)), load(List.drop(&2, U32, bs, 60n)), st)

def big_endian(+x: U32) -> List<&2, U32>:
  [U32.shrn(x, 24n), U32.and(U32.shrn(x, 16n), 255),
   U32.and(U32.shrn(x, 8n), 255), U32.and(x, 255)]

# Zero padding before the length, after the 0x80 byte.
def zeros(n: Nat, two: Bool) -> Nat:
  match two:
    case False{}:
      Nat.sub(55n, n)
    case True{}:
      Nat.sub(119n, n)

# The final suffix fits in at most two blocks (including a full pending
# block). The full pending block is consumed before padding is constructed.
def finish_blocks(n: Nat, +bs: List<&2, U32>, st: Hash) -> Hash:
  match n:
    case 0n:
      st
    case 1n+p:
      finish_blocks(p, List.drop(&2, U32, bs, 64n),
        compress(List.take(&2, U32, bs, 64n), st))

def pad(bs: List<&2, U32>, +n: Nat, st: Hash, hi: U32, lo: U32) -> Hash:
  +two = Nat.is_ge(n, 56n)
  suffix = List.append(&2, U32, big_endian(hi), big_endian(lo))
  padded = List.append(&2, U32, bs, 128 <>
    List.append(&2, U32, List.replicate(U32, zeros(n, two), 0), suffix))
  finish_blocks(Bool.pick(Nat, two, 2n, 1n), padded, st)

def finish(+buf: List<&2, U32>, st: Hash, hi: U32, lo: U32, full: Bool) -> Hash:
  match full:
    case True{}:
      pad([], 0n, compress(List.reverse(&2, U32, buf), st), hi, lo)
    case False{}:
      pad(List.reverse(&2, U32, buf), List.length(&2, U32, buf), st, hi, lo)

# A 64-bit bit count, with the same carry as Length_High / Length_Low in C.
def carry(+lo: U32, hi: U32) -> U32:
  U32.add(hi, Bool.to_u32(U32.is_lt(U32.add(lo, 8), lo)))

# Structural recursion on the input. Only a reversed block is buffered.
def absorb(msg: List<&2, U32>, room: Nat, buf: List<&2, U32>, st: Hash,
  hi: U32, +lo: U32) -> Hash:
  match msg room:
    case Nil{} room:
      finish(buf, st, hi, lo, Nat.is_eq(room, 0n))
    case b <> t 0n:
      absorb(t, 63n, [U32.and(b, 255)],
        compress(List.reverse(&2, U32, buf), st), carry(lo, hi), U32.add(lo, 8))
    case b <> t 1n+r:
      absorb(t, r, U32.and(b, 255) <> buf, st, carry(lo, hi), U32.add(lo, 8))

def digit(x: U32) -> Char:
  Maybe.default(&2, Char, String.get("0123456789abcdef", U32.to_nat(x)), '?')

def hex_word(n: Nat, +x: U32, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+p:
      hex_word(p, U32.shrn(x, 4n), SCon{digit(U32.and(x, 15)), acc})

def show(st: Hash) -> String:
  match st:
    case Hash{a, b, c, d, e, f, g, h}:
      String.concat([hex_word(8n, a, ""), hex_word(8n, b, ""),
        hex_word(8n, c, ""), hex_word(8n, d, ""), hex_word(8n, e, ""),
        hex_word(8n, f, ""), hex_word(8n, g, ""), hex_word(8n, h, "")])

# Word output is the computational API; hex is presentation of the same state.
def digest_state(st: Hash) -> Array<U32>:
  match st:
    case Hash{a, b, c, d, e, f, g, h}:
      ANode{ANode{ANode{ALeaf{a}, ALeaf{b}}, ANode{ALeaf{c}, ALeaf{d}}},
        ANode{ANode{ALeaf{e}, ALeaf{f}}, ANode{ALeaf{g}, ALeaf{h}}}}

def digest(msg: List<&2, U32>) -> Array<U32>:
  digest_state(absorb(msg, 64n, [], initial(), 0, 0))

def hash(msg: List<&2, U32>) -> String:
  show(absorb(msg, 64n, [], initial(), 0, 0))

# An octet string helper, not a UTF-8 encoder. Use a byte list for binary data.
def octets(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      []
    case SCon{Chr{x}, t}:
      U32.and(x, 255) <> octets(t)

def main() -> String:
  hash(octets("abc"))

#|"ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
