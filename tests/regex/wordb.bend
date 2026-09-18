# \b \B are ASCII word boundaries, also at the ends and at `at`.
import Base

def go(r: Result<&2, &2, Regex.Error, Regex>, s: String, at: Nat) -> Maybe<&2, Match>:
  match r:
    case Fail{e}:
      None{}
    case Done{re}:
      Regex.exec(re, s, at)

def m(p: String, s: String, at: Nat) -> Maybe<&2, Match>:
  go(Regex.compile(p, ""), s, at)

def main() -> List<&2, Maybe<&2, Match>>:
  [m("\\bfoo\\b", "a foo b", 0n), m("\\bfoo\\b", "afoo", 0n), m("\\Bo", "foo", 0n), m("\\b", "", 0n), m("\\b", "a", 0n),
   m("a\\b", "a", 0n), m("x\\B", "x", 0n), m("\\Bx", "x", 0n), m("\\b\\w+\\b", "hi there", 0n), m("\\w+\\b", "héllo", 0n),
   m("\\b_\\b", " _ ", 0n), m("\\bab", "xab", 1n), m("\\bab", "x ab", 1n)]

#|[Some{Match{2n, 5n, []}}, None{}, Some{Match{1n, 2n, []}}, None{}, Some{Match{0n, 0n, []}}, Some{Match{0n, 1n, []}}, None{}, None{}, Some{Match{0n, 2n, []}}, Some{Match{0n, 1n, []}}, Some{Match{1n, 2n, []}}, None{}, Some{Match{2n, 4n, []}}]
