# Tuples at the fragment's edge: `tuple[A, B]` is a chain Tup<A, Tup<B, Unit>>,
# so the arity is in the type and an unpack or index that CPython would reject
# (ValueError, IndexError) is a type error here. `tuple` and `for tuple target`
# are the positive controls. Kept apart from refuse.bend so each pin file stays
# small enough to interpret.
import Base
import ../../demos/python/syntax.bend as S
import ../../demos/python/translate.bend as Tr

def line(r: Result<&2, &2, S.Error, String>) -> String:
  match r:
    case Done{s}:
      "emitted"
    case Fail{e}:
      S.error_text(e)

def one(label: String, body: String) -> String:
  label ++ ": " ++ line(Tr.translate(body, Tr.contracts(), "f")) ++ "\n"

def opt() -> String:
  "def f(s: str, xs: list[str]) -> str | None:\n    "

def main() -> String:
  one("unpack arity", opt() ++ "a, b, c = s, s\n    return a\n") ++
  one("unpack list", opt() ++ "a, b = xs\n    return a\n") ++
  one("unpack str", opt() ++ "a, b = s\n    return a\n") ++
  one("unpack star", opt() ++ "a, *b = s, s\n    return a\n") ++
  one("unpack name taken", opt() ++ "tup_3_4_3_8 = s\n    a, b = s, s\n    return a\n") ++
  one("tuple index range", opt() ++ "t = (s, s)\n    return t[2]\n") ++
  one("tuple equality", opt() ++ "t = (s, s)\n    if t == (s, s):\n        return s\n    return None\n") ++
  one("tuple truthiness", opt() ++ "t = (s, s)\n    if t:\n        return s\n    return None\n") ++
  one("for tuple target", opt() ++ "best = None\n    for a, b in [(s, s)]:\n        best = a + b\n    return best\n") ++
  one("for tuple arity", opt() ++ "best = None\n    for a, b in [(s, s, s)]:\n        best = a\n    return best\n") ++
  one("tuple ellipsis", "def f(s: tuple[str, ...]) -> str:\n    return s[0]\n") ++
  one("tuple empty", "def f(s: str) -> tuple[()]:\n    return ()\n") ++
  one("tuple", "def f(p: tuple[str, bool]) -> tuple[bool, str]:\n    s, b = p\n    return b, s\n")
#|"unpack arity: error Unsupported 2 4 unpack: a tuple of exactly 3 items, not (Tup<String, Tup<String, Unit>>) at 2:4\nunpack list: error Unsupported 2 4 unpack: a tuple of exactly 2 items, not (List<&2, String>) at 2:4\nunpack str: error Unsupported 2 4 unpack: a tuple of exactly 2 items, not (String) at 2:4\nunpack star: error Unsupported 2 4 outside the fragment: statement Assign at 2:4\nunpack name taken: error Unsupported 3 4 unpack: the name tup_3_4_3_8 is taken at 3:4\ntuple index range: error Unsupported 3 11 subscript: only a tuple, at an index within its length (Tup<String, Tup<String, Unit>>) at 3:11\ntuple equality: error Unsupported 3 7 no verified contract for .__eq__ on (Tup<String, Tup<String, Unit>>) with (Tup<String, Tup<String, Unit>>;) at 3:7\ntuple truthiness: error Unsupported 3 7 truthiness of a non-bool is outside the fragment at 3:7\nfor tuple target: emitted\nfor tuple arity: error Unsupported 3 8 unpack: a tuple of exactly 2 items, not (Tup<String, Tup<String, Tup<String, Unit>>>) at 3:8\ntuple ellipsis: error Unsupported 1 20 annotation outside the fragment (str, bool, list[T], tuple[A, B], T | None) at 1:20\ntuple empty: error Unsupported 1 17 annotation outside the fragment (str, bool, list[T], tuple[A, B], T | None) at 1:17\ntuple: emitted\n"
