# A borrowed Bytes read (len, get, span, a find) of a value built at the
# call, not a variable: the value is made once, read, then dropped. A
# read's tail rebuilt as SCon{h, t} and measured, then walked, must leave
# t whole; an append measured must not be appended twice.
import Base

def walk(s: Bytes(), n: Nat) -> Nat:
  match s:
    case SNil{}:
      n
    case SCon{Chr{c}, t}:
      walk(t, 1n+n)

def rebuilt(s: Bytes()) -> String:
  match s:
    case SNil{}:
      "nil"
    case SCon{+h, +t}:
      Nat.show(Bytes.len(SCon{h, t})) ++ " " ++ Nat.show(walk(SCon{h, t}, 0n)) ++ " "
        ++ Nat.show(Bytes.span(SCon{h, t}, 0n, 65, 91)) ++ " [" ++ t ++ "]"

def main() -> IO(Unit):
  +r = Bytes.from_list([72, 69, 76, 76, 79, 119, 111, 114, 108, 100])
  +a = Bytes.append(r, "")
  do IO<Unit>:
    IO.print(rebuilt(a))
    IO.print(rebuilt(Bytes.drop(a, 4n)))
    IO.print(Nat.show(Bytes.len(Bytes.append(a, "!"))) ++ " " ++ a)
    IO.print(U32.show(Bytes.get(Bytes.push(a, 33), 10n)) ++ " "
      ++ Nat.show(Bytes.find_byte(Bytes.drop(a, 1n), 0n, 119)))

#|10 10 5 [ELLOworld]
#|6 6 1 [world]
#|11 HELLOworld
#|33 4
