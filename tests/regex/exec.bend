# Reference VM: leftmost-first, catastrophic pattern terminates, lazy star,
# `$` before a final newline, `at`, match_at, size cap.
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
  [m("a|ab", "ab", 0n), m("^(a+)+$", "aaab", 0n), m("(a|b)*?c", "abc", 0n), m("a$", "a\n", 0n), m("a", "ba", 1n), m("^a", "aa", 1n), m("", "", 0n), m("x", "abc", 5n)]

#|[Some{Match{0n, 1n, []}}, None{}, Some{Match{0n, 3n, [Some{(1n, 2n)}]}}, Some{Match{0n, 1n, []}}, Some{Match{1n, 2n, []}}, None{}, Some{Match{0n, 0n, []}}, None{}]
