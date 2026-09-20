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
