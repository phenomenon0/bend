# search: find is the first start, find_last the last (overlaps allowed),
# count is nonoverlapping, replace never rescans what it inserted; the empty
# needle matches at 0, at length, length+1 times, and at every boundary
import Base

def main() -> (Maybe<&2, Nat> & (Maybe<&2, Nat> & Maybe<&2, Nat>)) & ((Maybe<&2, Nat> & (Maybe<&2, Nat> & Maybe<&2, Nat>)) & ((Nat & (Nat & Nat)) & ((String & (String & String)) & (Bool & (Bool & (Bool & Bool)))))):
  ((String.find("banana", "ana"), (String.find("banana", "nab"), String.find("banana", ""))),
   ((String.find_last("banana", "ana"), (String.find_last("banana", ""), String.find_last("", "a"))),
    ((String.count("banana", "ana"), (String.count("aaaa", "aa"), String.count("abc", ""))),
     ((String.replace("aaa", "aa", "b"), (String.replace("abc", "", "-"), String.replace("banana", "an", "$&"))),
      (String.contains("banana", "nan"),
       (String.starts_with("banana", "ban"),
        (String.ends_with("banana", "nana"), String.ends_with("na", "nana"))))))))

#|((Some{1n}, None{}, Some{0n}), (Some{3n}, Some{6n}, None{}), (1n, 2n, 4n), ("ba", "-a-b-c-", "b$&$&a"), True{}, True{}, True{}, False{})
