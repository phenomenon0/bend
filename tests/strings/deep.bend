# 44 code points x 4096 = 180224, consumed to a small pure result. This is
# real normalization in the interpret lane, not an IO main's implicit JS.
import Base

def count.go(xs: List<&2, String>, n: Nat) -> Nat:
  match xs:
    case Nil{}:
      n
    case h <> t:
      count.go(t, 1n+n)

def sample() -> String:
  String.repeat("the quick brown fox jumps over the lazy dog\n", 4096n)

def main() -> Bool & (Bool & (Bool & Bool)):
  (Nat.is_eq(String.length(sample()), Nat.mul(44n, 4096n)),
   (Nat.is_eq(count.go(String.split(sample(), '\n'), 0n), 4097n),
    (Nat.is_eq(count.go(String.words(sample()), 0n), Nat.mul(9n, 4096n)),
     String.eq(String.to_upper(sample()),
       String.repeat("THE QUICK BROWN FOX JUMPS OVER THE LAZY DOG\n", 4096n)))))

#|(True{}, True{}, True{}, True{})
