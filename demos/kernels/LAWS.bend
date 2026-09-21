import Base
import ./sha256.bend as S
import ./buffer.bend as B
import ./chacha20.bend as C
import ./fips.bend as F
import ./spec_state.bend as T
import ./observations.bend as O

# These claims cover the actual APIs, not a legacy model. Shape and rejection
# do not establish digest contents. Full FIPS/RFC equivalence remains conjectural.
def state(s: S.Hash) -> T.State:
  match s:
    case S.Hash{a,b,c,d,e,f,g,h}: T.H{a,b,c,d,e,f,g,h}

law sha_words_shape:
  for a: Array<U32>
  for +length: Nat
  {O.result_size(B.hash(a, length)) == O.bounded_size(length, Array.size(U32, a)) : Maybe<&2, Nat>}

# Equality of Booleans is both directions: rejects all and accepts all are excluded.
law sha_none_iff_oversize:
  for a: Array<U32>
  for +length: Nat
  {Maybe.is_none(&1, Array<U32>, B.hash(a, length)) == O.too_long(length, Array.size(U32, a)) : Bool}

law sha_legacy_words_length:
  for msg: List<&2, U32>
  {List.length(&2, U32, O.words(S.digest(msg))) == 8n : Nat}

law sha_digest_order:
  for +s: S.Hash
  {O.words(S.digest_state(s)) == F.digest(state(s)) : List<&2, U32>}

law sha_initial:
  {state(S.initial()) == F.initial() : T.State}

law sha_constants:
  {S.constants() == F.constants() : List<&2, U32>}

law sha_rotation:
  for +x: U32
  for +n: Nat
  {S.rotr(x, n) == F.rotate(x, n) : U32}

law sha_choice:
  for +x: U32
  for +y: U32
  for +z: U32
  {S.choose(x, y, z) == F.choice(x, y, z) : U32}

# The two transcriptions associate their xor chains differently, so these
# need U32 xor associativity; they are not definitional conversions.
law sha_majority:
  for +x: U32
  for +y: U32
  for +z: U32
  {S.majority(x, y, z) == F.majority(x, y, z) : U32}

law sha_small0:
  for +x: U32
  {S.small0(x) == F.sigma0(x) : U32}

law sha_small1:
  for +x: U32
  {S.small1(x) == F.sigma1(x) : U32}

law sha_big0:
  for +x: U32
  {S.big0(x) == F.sum0(x) : U32}

law sha_big1:
  for +x: U32
  {S.big1(x) == F.sum1(x) : U32}

law sha_feed:
  for +x: S.Hash
  for +y: S.Hash
  {state(S.feed(x, y)) == F.add(state(x), state(y)) : T.State}

law chacha_words_length:
  for key: C.ChaKey
  for counter: U32
  for nonce: C.Nonce
  {List.length(&2, U32, C.words(C.block_words(key, counter, nonce))) == 16n : Nat}

law chacha_block_bytes_length:
  for key: C.ChaKey
  for counter: U32
  for nonce: C.Nonce
  {List.length(&2, U32, C.block(key, counter, nonce)) == 64n : Nat}
