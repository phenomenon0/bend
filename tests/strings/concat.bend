# Unique growth in either direction, direction switches, generic application.
import Base

def prepend(n: Nat, s: String) -> String:
  match n:
    case 0n:
      s
    case 1n+p:
      prepend(p, SCon{'a', s})

def append(n: Nat, s: String) -> String:
  match n:
    case 0n:
      s
    case 1n+p:
      append(p, String.append(s, "b"))

def apply(f: String -> String, s: String) -> String:
  f(s)

def main() -> List<&2, String> & (Nat & (String & Cmp)):
  +s = append(12n, prepend(12n, "!"))
  (([s, prepend(3n, append(3n, prepend(3n, ""))),
     String.concat(["", "ab", "", "😀", "cd"]),
     String.join(["", "ab", "", "😀", "cd", ""], "/"),
     String.join([], "/"), String.join(["x"], "/"), String.repeat("ab", 5n),
     String.repeat("", Nat.pow(2n, 32n)), String.repeat("x", 0n),
     apply(String.append("prefix:"), "tail"),
     apply(String.to_upper, "abc")]),
   (String.length(s), (String.from_list(String.to_list("A😀é\0")),
    String.order("😀", "\u{e000}"))))

#|(["aaaaaaaaaaaa!bbbbbbbbbbbb", "aaaaaabbb", "ab😀cd", "/ab//😀/cd/", "", "x", "ababababab", "", "", "prefix:tail", "ABC"], 25n, "A😀é\0", GT{})
