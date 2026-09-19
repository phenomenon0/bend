# Captures keep their last value; absent (None) differs from empty (Some);
# offsets are code points (supplementary chars count once); fullmatch, match_at.
import Base

def go(r: Result<&2, &2, Regex.Error, Regex>, s: String, at: Nat, mode: Nat) -> Maybe<&2, Match>:
  match r mode:
    case Fail{e}, _:
      None{}
    case Done{re}, 0n:
      Regex.exec(re, s, at)
    case Done{re}, 1n:
      Regex.match_at(re, s, at)
    case Done{re}, 2n+_:
      Regex.fullmatch(re, s)

def m(p: String, s: String) -> Maybe<&2, Match>:
  go(Regex.compile(p, ""), s, 0n, 0n)

def main() -> List<&2, Maybe<&2, Match>>:
  [m("(a(b)?)+", "aba"), m("(a)|b", "b"), m("a(b)?c", "ac"), m("a(b*)c", "ac"),
   m(".", "😀x"), m("x😀y", "ax😀yb"), m("[😀-🙏]", "🙂"), m("(😀)+", "😀😀"),
   go(Regex.compile("(a)(b)?", ""), "a", 0n, 2n), go(Regex.compile("a+", ""), "aa\n", 0n, 2n), go(Regex.compile("a*?", ""), "aa", 0n, 2n),
   go(Regex.compile("a", ""), "ba", 0n, 1n), go(Regex.compile("a", ""), "ba", 1n, 1n)]

#|[Some{Match{0n, 3n, [Some{(2n, 3n)}, Some{(1n, 2n)}]}}, Some{Match{0n, 1n, [None{}]}}, Some{Match{0n, 2n, [None{}]}}, Some{Match{0n, 2n, [Some{(1n, 1n)}]}}, Some{Match{0n, 1n, []}}, Some{Match{1n, 4n, []}}, Some{Match{0n, 1n, []}}, Some{Match{0n, 2n, [Some{(1n, 2n)}]}}, Some{Match{0n, 1n, [Some{(0n, 1n)}, None{}]}}, None{}, Some{Match{0n, 2n, []}}, None{}, Some{Match{1n, 2n, []}}]
