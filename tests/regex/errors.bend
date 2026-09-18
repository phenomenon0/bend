# Regex.parse errors: pos is the code-point offset where the parser gave up.
# `(?:a?)*` is NullableRepeat (an unbounded repeat of a body that can be
# empty); `(?:a?){0,2}` is fine. `{,n}` is a bad repeat, not {0,n}.
import Base

def e(s: String) -> Result<&2, &2, Regex.Error, Re>:
  Regex.parse(s)

def main() -> List<&2, Result<&2, &2, Regex.Error, Re>>:
  [e("(?:a?)*"), e("(a*)*"), e("(?:a?){0,2}"), e("a{,3}"), e("[z-a]"), e("*a"), e("a**"),
   e("(a"), e("a)"), e("(?=a)"), e("\\1"), e("\\q"), e("[abc"), e("a{3,2}"), e("a{300}"),
   e("\\ud800"), e("\\x4")]

#|[Fail{RErr{6n, "NullableRepeat"}}, Fail{RErr{4n, "NullableRepeat"}}, Done{RRep{RRep{RLit{'a'}, 0n, Some{1n}, True{}}, 0n, Some{2n}, True{}}}, Fail{RErr{1n, "bad repeat"}}, Fail{RErr{4n, "bad character range"}}, Fail{RErr{0n, "nothing to repeat"}}, Fail{RErr{2n, "multiple repeat"}}, Fail{RErr{2n, "missing )"}}, Fail{RErr{1n, "unbalanced parenthesis"}}, Fail{RErr{0n, "unsupported group extension"}}, Fail{RErr{0n, "backreferences are not supported"}}, Fail{RErr{0n, "bad escape"}}, Fail{RErr{4n, "unterminated character set"}}, Fail{RErr{1n, "min repeat greater than max repeat"}}, Fail{RErr{1n, "repeat count exceeds max_rep"}}, Fail{RErr{0n, "bad escape"}}, Fail{RErr{0n, "bad escape"}}]
