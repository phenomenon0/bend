# RFC 8439 sections 2.1, 2.3 and 2.4: quarter round, block and cipher.
# C source: libsodium crypto_stream/chacha20/ref/chacha20_ref.c,
# QUARTERROUND, chacha_keysetup, chacha_ietf_ivsetup, chacha20_encrypt_bytes
# (Bernstein's public-domain chacha-merged.c, 20080118).
# The IETF counter is one word: crypt refuses wrap instead of carrying into
# the nonce. ChaKey and nonce fields are little-endian words; message elements
# are octets in U32 (only the low eight bits are used). No IO or native ops.
import Base

type ChaKey is Data:
  ChaKey{k0: U32, k1: U32, k2: U32, k3: U32,
    k4: U32, k5: U32, k6: U32, k7: U32}

type Nonce is Data:
  Nonce{n0: U32, n1: U32, n2: U32}

type Quad is Data:
  Quad{a: U32, b: U32, c: U32, d: U32}

type State is Data:
  State{x0: U32, x1: U32, x2: U32, x3: U32,
    x4: U32, x5: U32, x6: U32, x7: U32,
    x8: U32, x9: U32, x10: U32, x11: U32,
    x12: U32, x13: U32, x14: U32, x15: U32}

def rotl(+x: U32, +n: Nat) -> U32:
  U32.or(U32.shln(x, n), U32.shrn(x, Nat.sub(32n, n)))

def quarter(a: U32, +b: U32, c: U32, d: U32) -> Quad:
  +a1 = U32.add(a, b)
  +d1 = rotl(U32.xor(d, a1), 16n)
  +c1 = U32.add(c, d1)
  +b1 = rotl(U32.xor(b, c1), 12n)
  +a2 = U32.add(a1, b1)
  +d2 = rotl(U32.xor(d1, a2), 8n)
  +c2 = U32.add(c1, d2)
  b2 = rotl(U32.xor(b1, c2), 7n)
  Quad{a2, b2, c2, d2}

# The same eight QUARTERROUND calls as the C loop, with explicit wiring.
def gather(p: Quad, q: Quad, r: Quad, s: Quad) -> State:
  match p q r s:
    case Quad{z0, z5, z10, z15} Quad{z1, z6, z11, z12} Quad{z2, z7, z8, z13} Quad{z3, z4, z9, z14}:
      State{z0, z1, z2, z3, z4, z5, z6, z7,
        z8, z9, z10, z11, z12, z13, z14, z15}

def diagonals(p: Quad, q: Quad, r: Quad, s: Quad) -> State:
  match p q r s:
    case Quad{y0, y4, y8, y12} Quad{y1, y5, y9, y13} Quad{y2, y6, y10, y14} Quad{y3, y7, y11, y15}:
      gather(quarter(y0, y5, y10, y15),
        quarter(y1, y6, y11, y12),
        quarter(y2, y7, y8, y13),
        quarter(y3, y4, y9, y14))

def double_round(s: State) -> State:
  match s:
    case State{x0, x1, x2, x3, x4, x5, x6, x7,
      x8, x9, x10, x11, x12, x13, x14, x15}:
      diagonals(quarter(x0, x4, x8, x12),
        quarter(x1, x5, x9, x13),
        quarter(x2, x6, x10, x14),
        quarter(x3, x7, x11, x15))

def rounds(n: Nat, s: State) -> State:
  match n:
    case 0n:
      s
    case 1n+p:
      rounds(p, double_round(s))

def initial(key: ChaKey, counter: U32, nonce: Nonce) -> State:
  match key nonce:
    case ChaKey{k0, k1, k2, k3, k4, k5, k6, k7} Nonce{n0, n1, n2}:
      State{1634760805, 857760878, 2036477234, 1797285236,
        k0, k1, k2, k3, k4, k5, k6, k7, counter, n0, n1, n2}

def words(s: State) -> List<&2, U32>:
  match s:
    case State{x0, x1, x2, x3, x4, x5, x6, x7,
      x8, x9, x10, x11, x12, x13, x14, x15}:
      [x0, x1, x2, x3, x4, x5, x6, x7,
       x8, x9, x10, x11, x12, x13, x14, x15]

def little(+x: U32) -> List<&2, U32>:
  [U32.and(x, 255), U32.and(U32.shrn(x, 8n), 255),
   U32.and(U32.shrn(x, 16n), 255), U32.shrn(x, 24n)]

# Fixed state fields preserve the word boundary before little-endian presentation.
def feed_state(x: State, y: State) -> State:
  match x y:
    case State{a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15} State{b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15}:
      State{U32.add(a0, b0), U32.add(a1, b1), U32.add(a2, b2), U32.add(a3, b3), U32.add(a4, b4), U32.add(a5, b5), U32.add(a6, b6), U32.add(a7, b7), U32.add(a8, b8), U32.add(a9, b9), U32.add(a10, b10), U32.add(a11, b11), U32.add(a12, b12), U32.add(a13, b13), U32.add(a14, b14), U32.add(a15, b15)}

def block_words(key: ChaKey, counter: U32, nonce: Nonce) -> State:
  +s = initial(key, counter, nonce)
  feed_state(s, rounds(10n, s))

def bytes(ws: List<&2, U32>) -> List<&2, U32>:
  match ws:
    case Nil{}:
      []
    case w <> rest:
      List.append(&2, U32, little(w), bytes(rest))

# A ChaCha block is keystream, not a cryptographic digest.
def block(key: ChaKey, counter: U32, nonce: Nonce) -> List<&2, U32>:
  bytes(words(block_words(key, counter, nonce)))

# One byte per step; Nil keystream obtains a fresh block. An exhausted
# counter can still consume the rest of its last block, but never a new one.
def crypt_go(msg: List<&2, U32>, +key: ChaKey, +nonce: Nonce,
  +counter: U32, exhausted: Bool, ks: List<&2, U32>, acc: List<&2, U32>) ->
  Maybe<&2, List<&2, U32>>:
  match msg exhausted ks:
    case Nil{} _ _:
      Some{List.reverse(&2, U32, acc)}
    case m <> mt exhausted k <> kt:
      crypt_go(mt, key, nonce, counter, exhausted, kt,
        U32.xor(U32.and(m, 255), k) <> acc)
    case m <> mt True{} Nil{}:
      None{}
    case m <> mt False{} Nil{}:
      +bs = block(key, counter, nonce)
      k = Maybe.default(&2, U32, List.head(&2, U32, bs), 0)
      crypt_go(mt, key, nonce, U32.add(counter, 1),
        U32.is_eq(counter, 4294967295), List.tail(&2, U32, bs),
        U32.xor(U32.and(m, 255), k) <> acc)

def crypt(key: ChaKey, counter: U32, nonce: Nonce, msg: List<&2, U32>) ->
  Maybe<&2, List<&2, U32>>:
  crypt_go(msg, key, nonce, counter, False{}, [], [])

def keystream(key: ChaKey, counter: U32, nonce: Nonce, n: Nat) ->
  Maybe<&2, List<&2, U32>>:
  crypt(key, counter, nonce, List.replicate(U32, n, 0))

def digit(x: U32) -> Char:
  Maybe.default(&2, Char, String.get("0123456789abcdef", U32.to_nat(x)), '?')

def hex(bs: List<&2, U32>) -> String:
  match bs:
    case Nil{}:
      ""
    case b <> t:
      +v = U32.and(b, 255)
      SCon{digit(U32.shrn(v, 4n)), SCon{digit(U32.and(v, 15)), hex(t)}}

def main() -> String:
  hex(block(ChaKey{50462976, 117835012, 185207048, 252579084,
    319951120, 387323156, 454695192, 522067228}, 1,
    Nonce{150994944, 1241513984, 0}))

#|"10f1e7e4d13b5915500fdd1fa32071c4c7d1f4c733c068030422aa9ac3d46c4ed2826446079faa0914c2d705d98b02a2b5129cd1de164eb9cbd083e8a2503c4e"
