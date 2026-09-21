# Proof-only observations count actual leaves, not Array.size's capacity estimate.
# They never execute on the production hashing path.
import Base

def words(a: Array<U32>) -> List<&2, U32>:
  match a:
    case ALeaf{x}: [x]
    case ANode{left, right}:
      List.append(&2, U32, words(left), words(right))

def result_size(r: Maybe<&1, Array<U32>>) -> Maybe<&2, Nat>:
  match r:
    case None{}: None{}
    case Some{a}: Some{List.length(&2, U32, words(a))}

def expected_size(valid: Bool) -> Maybe<&2, Nat>:
  match valid:
    case False{}: None{}
    case True{}: Some{8n}

# Capacity means precisely Base.Array.size's U32 result. Byte semantics of
# arbitrary ragged arrays are not claimed; ordinary storage is balanced.
def bounded_size(+length: Nat, pair: Array<U32> & U32) -> Maybe<&2, Nat>:
  (a, capacity) = pair
  expected_size(Nat.is_le(length, Nat.mul(4n, U32.to_nat(capacity))))

def too_long(length: Nat, pair: Array<U32> & U32) -> Bool:
  (a, capacity) = pair
  Nat.is_gt(length, Nat.mul(4n, U32.to_nat(capacity)))
