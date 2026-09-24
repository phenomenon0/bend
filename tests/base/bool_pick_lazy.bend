import Base

# Bool.pick is lazy on every lane: only the chosen arm runs. `spin` never
# ends, so a lane that built both arms would hang. The arms consume
# different variables (a list only one arm reads, a string only the
# other), sit in tail, let, argument and field positions, nest, close over
# an erased type, and pick a function; each untaken arm's values drop.

@unsafe def spin(n: U32) -> U32:
  spin((n + 1 : U32))

@unsafe def spin.str(s: String) -> String:
  spin.str(s ++ "!")

def sum(xs: List<U32>) -> U32:
  match xs:
    case []:
      0
    case x <> rest:
      (x + sum(rest) : U32)

# tail position: each arm reads its own variable
def tail(c: Bool, xs: List<U32>, s: String) -> U32:
  Bool.pick(U32, c, sum(xs), U32.from_nat(String.length(s)))

# let and argument position, the scrutinee a call
def lets(+n: U32, xs: List<U32>) -> String:
  +t = Bool.pick(U32, U32.is_lt(n, 10), sum(xs), spin(n))
  U32.show(t) ++ "/" ++ U32.show(Bool.pick(U32, U32.is_lt(10, n), spin(t), (t + n : U32)))

# nested picks
def nest(+b: Bool, a: Bool) -> String:
  Bool.pick(String, a, Bool.pick(String, b, "tt", spin.str("tf")),
    Bool.pick(String, b, spin.str("ft"), "ff"))

# constructor fields
def fields(+a: Bool) -> String & String:
  (Bool.pick(String, a, "x", spin.str("f")), Bool.pick(String, a, "y" ++ "z", spin.str("g")))

def head.or(-A: Type, xs: List<A>, d: A) -> A:
  match xs:
    case []:
      d
    case x <> rest:
      x

# an arm over an erased type
def first(-A: Data, c: Bool, xs: List<A>, +d: A) -> A:
  Bool.pick(A, c, head.or(A, xs, d), d)

# an arm that is a function
def pick.fn(c: Bool) -> U32 -> U32:
  Bool.pick(U32 -> U32, c, n => (n + 1 : U32), n => spin(n))

# many rounds: the list or the string the untaken arm would read drops
def rounds(n: Nat, acc: U32) -> U32:
  match n:
    case 0n:
      acc
    case 1n+(+p):
      rounds(p, (tail(U32.is_eq(U32.from_nat(Nat.mod(p, 2n)), 0), [acc, 1, 2], "four")
        + U32.from_nat(Nat.mod(p, 2n)) : U32))

def both(p: String & String) -> String:
  (x, y) = p
  x ++ "," ++ y

def main() -> String:
  U32.show(tail(True{}, [1, 2, 3], "abc")) ++ " "
    ++ U32.show(tail(False{}, [1, 2, 3], "abc")) ++ " "
    ++ lets(3, [4, 5]) ++ " "
    ++ nest(True{}, True{}) ++ " " ++ nest(False{}, False{}) ++ " "
    ++ both(fields(True{})) ++ " "
    ++ U32.show(first(U32, True{}, [7, 8], 9)) ++ " "
    ++ U32.show(first(U32, False{}, [7, 8], 9)) ++ " "
    ++ U32.show(pick.fn(True{})(41)) ++ " "
    ++ U32.show(rounds(10000n, 0))

#|"6 3 9/12 tt ff x,yz 7 9 42 8"
