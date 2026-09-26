# F05: List.map takes only a List<&1, A>, while List.length, foldl,
# foldr and for_each are generic in the quantity. Mapping a List<&2, A>
# (what File.read_bytes answers) is refused.
import Base

def inc(x: U32) -> U32:
  (x + 1 : U32)

def xs() -> List<&2, U32>:
  [1, 2, 3]

def main() -> List<&2, U32>:
  List.map(~U32, ~U32, ~inc, xs())

#|[2, 3, 4]
