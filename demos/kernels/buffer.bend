# Packed big-endian SHA-256 input. The array is consumed; unused low bytes
# of the last word and unused capacity do not belong to the message.
import Base
import ./sha256.bend as S

# This adapter is intentionally explicit; the next slice removes whole-input unpacking.
def octets(a: Array<U32>) -> List<&2, U32>:
  match a:
    case ALeaf{w}:
      S.big_endian(w)
    case ANode{l, r}:
      List.append(&2, U32, octets(l), octets(r))

def checked(valid: Bool, a: Array<U32>, length: Nat) -> Maybe<&1, Array<U32>>:
  match valid:
    case False{}:
      None{}
    case True{}:
      Some{S.digest(List.take(&2, U32, octets(a), length))}

def sized(+length: Nat, pair: Array<U32> & U32) -> Maybe<&1, Array<U32>>:
  (a, capacity) = pair
  checked(Nat.is_le(length, Nat.mul(4n, U32.to_nat(capacity))), a, length)

# Array.size is Base's capacity contract (balanced power-of-two storage).
def hash(a: Array<U32>, length: Nat) -> Maybe<&1, Array<U32>>:
  sized(length, Array.size(U32, a))

def hex_words(a: Array<U32>) -> String:
  match a:
    case ALeaf{x}:
      S.hex_word(8n, x, "")
    case ANode{l, r}:
      String.concat([hex_words(l), hex_words(r)])

def hex(result: Maybe<&1, Array<U32>>) -> String:
  match result:
    case None{}:
      "invalid length"
    case Some{a}:
      hex_words(a)
