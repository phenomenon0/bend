import Base
import ./sha256.bend as S
import ./buffer.bend as B
import ./chacha20.bend as C
import ./fips.bend as F
import ./observations.bend as O
import ./LAWS.bend as L

# A size estimate would miss malformed trees; this counts every actual digest leaf.
law digest_size:
  for s: S.Hash
  {List.length(&2, U32, O.words(S.digest_state(s))) == 8n : Nat}

def digest_size(s):
  match s:
    case S.Hash{a,b,c,d,e,f,g,h}: {==}

law checked_shape:
  for +valid: Bool
  for a: Array<U32>
  for length: Nat
  {O.result_size(B.checked(valid, a, length)) == O.expected_size(valid) : Maybe<&2, Nat>}

def checked_shape(valid, a, length):
  match valid:
    case False{}: {==}
    case True{}:
      Equal.cong(Nat, Maybe<&2, Nat>, n => Some{n},
        List.length(&2, U32, O.words(S.digest_state(B.raw(a, length)))), 8n,
        digest_size(B.raw(a, length)))

law sized_shape:
  for +length: Nat
  for pair: Array<U32> & U32
  {O.result_size(B.sized(length, pair)) == O.bounded_size(length, pair) : Maybe<&2, Nat>}

def sized_shape(length, pair):
  (a, capacity) = pair
  checked_shape(Nat.is_le(length, Nat.mul(4n, U32.to_nat(capacity))), a, length)

# Lifting through the public ownership-threaded size call closes arbitrary inputs.
def L.sha_words_shape(a, length):
  sized_shape(length, Array.size(U32, a))

law checked_none:
  for +valid: Bool
  for a: Array<U32>
  for length: Nat
  {Maybe.is_none(&1, Array<U32>, B.checked(valid, a, length)) == Bool.not(valid) : Bool}

def checked_none(valid, a, length):
  match valid:
    case False{}: {==}
    case True{}: {==}

law complement:
  for +order: Cmp
  {Bool.not(Cmp.is_le(order)) == Cmp.is_gt(order) : Bool}

def complement(order):
  match order:
    case LT{}: {==}
    case EQ{}: {==}
    case GT{}: {==}

law sized_none:
  for +length: Nat
  for pair: Array<U32> & U32
  {Maybe.is_none(&1, Array<U32>, B.sized(length, pair)) == O.too_long(length, pair) : Bool}

def sized_none(length, pair):
  (a, +capacity) = pair
  Equal.trans(Bool,
    Maybe.is_none(&1, Array<U32>, B.sized(length, (a, capacity))),
    Bool.not(Nat.is_le(length, Nat.mul(4n, U32.to_nat(capacity)))),
    Nat.is_gt(length, Nat.mul(4n, U32.to_nat(capacity))),
    checked_none(Nat.is_le(length, Nat.mul(4n, U32.to_nat(capacity))), a, length),
    complement(Nat.cmp(length, Nat.mul(4n, U32.to_nat(capacity)))))

def L.sha_none_iff_oversize(a, length):
  sized_none(length, Array.size(U32, a))

def L.sha_legacy_words_length(msg):
  digest_size(S.absorb(msg, 64n, [], S.initial(), 0, 0))

def L.sha_digest_order(s):
  match s:
    case S.Hash{a,b,c,d,e,f,g,h}: {==}

def L.sha_initial():
  {==}

def L.sha_constants():
  {==}

def L.sha_rotation(x, n):
  {==}

def L.sha_choice(x, y, z):
  {==}

def L.sha_feed(x, y):
  match x y:
    case S.Hash{a,b,c,d,e,f,g,h} S.Hash{i,j,k,l,m,n,o,p}: {==}

# Base proves Word.add_comm but no xor law; bit-level induction supplies the
# rewrite the differently associated spec/production round functions need.
law word_xor_assoc:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  for c: Word(n)
  {Word.xor(n, Word.xor(n, a, b), c) == Word.xor(n, a, Word.xor(n, b, c)) : Word(n)}

def word_xor_assoc(n, a, b, c):
  match n:
    case 0n:
      match a b c:
        case WNil{} WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b c:
        case WCon{False{}, at} WCon{False{}, bt} WCon{False{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w},
            Word.xor(p, Word.xor(p, at, bt), ct),
            Word.xor(p, at, Word.xor(p, bt, ct)),
            word_xor_assoc(p, at, bt, ct))
        case WCon{False{}, at} WCon{False{}, bt} WCon{True{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w},
            Word.xor(p, Word.xor(p, at, bt), ct),
            Word.xor(p, at, Word.xor(p, bt, ct)),
            word_xor_assoc(p, at, bt, ct))
        case WCon{False{}, at} WCon{True{}, bt} WCon{False{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w},
            Word.xor(p, Word.xor(p, at, bt), ct),
            Word.xor(p, at, Word.xor(p, bt, ct)),
            word_xor_assoc(p, at, bt, ct))
        case WCon{False{}, at} WCon{True{}, bt} WCon{True{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w},
            Word.xor(p, Word.xor(p, at, bt), ct),
            Word.xor(p, at, Word.xor(p, bt, ct)),
            word_xor_assoc(p, at, bt, ct))
        case WCon{True{}, at} WCon{False{}, bt} WCon{False{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w},
            Word.xor(p, Word.xor(p, at, bt), ct),
            Word.xor(p, at, Word.xor(p, bt, ct)),
            word_xor_assoc(p, at, bt, ct))
        case WCon{True{}, at} WCon{False{}, bt} WCon{True{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w},
            Word.xor(p, Word.xor(p, at, bt), ct),
            Word.xor(p, at, Word.xor(p, bt, ct)),
            word_xor_assoc(p, at, bt, ct))
        case WCon{True{}, at} WCon{True{}, bt} WCon{False{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w},
            Word.xor(p, Word.xor(p, at, bt), ct),
            Word.xor(p, at, Word.xor(p, bt, ct)),
            word_xor_assoc(p, at, bt, ct))
        case WCon{True{}, at} WCon{True{}, bt} WCon{True{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w},
            Word.xor(p, Word.xor(p, at, bt), ct),
            Word.xor(p, at, Word.xor(p, bt, ct)),
            word_xor_assoc(p, at, bt, ct))

law u32_xor_assoc:
  for a: U32
  for b: U32
  for c: U32
  {U32.xor(U32.xor(a, b), c) == U32.xor(a, U32.xor(b, c)) : U32}

def u32_xor_assoc(a, b, c):
  match a b c:
    case U32{x} U32{y} U32{z}:
      Equal.cong(Word(32n), U32, w => U32{w},
        Word.xor(32n, Word.xor(32n, x, y), z),
        Word.xor(32n, x, Word.xor(32n, y, z)),
        word_xor_assoc(32n, x, y, z))

def L.sha_majority(x, y, z):
  u32_xor_assoc(U32.and(x, y), U32.and(x, z), U32.and(y, z))

def L.sha_small0(x):
  u32_xor_assoc(S.rotr(x, 7n), S.rotr(x, 18n), U32.shrn(x, 3n))

def L.sha_small1(x):
  u32_xor_assoc(S.rotr(x, 17n), S.rotr(x, 19n), U32.shrn(x, 10n))

def L.sha_big0(x):
  u32_xor_assoc(S.rotr(x, 2n), S.rotr(x, 13n), S.rotr(x, 22n))

def L.sha_big1(x):
  u32_xor_assoc(S.rotr(x, 6n), S.rotr(x, 11n), S.rotr(x, 25n))

law chacha_state_size:
  for s: C.State
  {List.length(&2, U32, C.words(s)) == 16n : Nat}

def chacha_state_size(s):
  match s:
    case C.State{a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p}: {==}

law chacha_serialized_size:
  for s: C.State
  {List.length(&2, U32, C.bytes(C.words(s))) == 64n : Nat}

def chacha_serialized_size(s):
  match s:
    case C.State{a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p}: {==}

def L.chacha_words_length(key, counter, nonce):
  chacha_state_size(C.block_words(key, counter, nonce))

def L.chacha_block_bytes_length(key, counter, nonce):
  chacha_serialized_size(C.block_words(key, counter, nonce))
