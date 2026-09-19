# Never a silent guess: every source outside the T1 fragment blocks emission
# with a positioned diagnostic. `near` is the one positive control: a literal
# receiver is inside the fragment. Spelling is not authority (`str.lower(s)`,
# `len(s)`), a method is granted only at its contracted arity and types.
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

def head() -> String:
  "def f(s: str) -> str:\n    "

def main() -> String:
  one("near", head() ++ "return ' A '.strip().lower()\n") ++
  one("method", head() ++ "return s.title()\n") ++
  one("arity", head() ++ "return s.strip('x')\n") ++
  one("keyword", head() ++ "return s.replace(' ', new='-')\n") ++
  one("spelling", head() ++ "return str.lower(s)\n") ++
  one("builtin", head() ++ "return len(s)\n") ++
  one("name", head() ++ "return t.strip()\n") ++
  one("escape", head() ++ "return s.replace('\\t', '-')\n") ++
  one("adjacent", head() ++ "return s.replace('a' 'b', '-')\n") ++
  one("unbound method", head() ++ "return s.strip\n") ++
  one("ifexp", head() ++ "return s if s else s\n") ++
  one("assign", head() ++ "x = s.strip()\n    return x\n") ++
  one("after", head() ++ "return s\n    return s.lower()\n") ++
  one("bare", head() ++ "return\n") ++
  one("falls", head() ++ "pass\n") ++
  one("untyped", "def f(s) -> str:\n    return s\n") ++
  one("int", "def f(s: int) -> str:\n    return s\n") ++
  one("returns", "def f(s: str) -> bool:\n    return s\n") ++
  one("default", "def f(s: str = 'a') -> str:\n    return s\n") ++
  one("open module", "import re\n" ++ head() ++ "return s\n") ++
  one("twice", head() ++ "return s\n" ++ head() ++ "return s.lower()\n") ++
  one("absent", "def g(s: str) -> str:\n    return s\n")
#|"near: emitted\nmethod: error Unsupported 2 11 no verified contract for .title on (String) with () at 2:11\narity: error Unsupported 2 11 no verified contract for .strip on (String) with (String;) at 2:11\nkeyword: error Unsupported 2 11 outside the T1 fragment: Call at 2:11\nspelling: error Unsupported 2 11 unresolved name str at 2:11\nbuiltin: error Unsupported 2 11 outside the T1 fragment: Call at 2:11\nname: error Unsupported 2 11 unresolved name t at 2:11\nescape: error Unsupported 2 21 literal outside the T1 contract (one plain ASCII string, no escapes) at 2:21\nadjacent: error Unsupported 2 21 literal outside the T1 contract (one plain ASCII string, no escapes) at 2:21\nunbound method: error Unsupported 2 11 outside the T1 fragment: Attribute at 2:11\nifexp: error Unsupported 2 11 outside the T1 fragment: IfExp at 2:11\nassign: error Unsupported 2 4 outside the T1 fragment: statement Assign at 2:4\nafter: error Unsupported 3 4 statement after return at 3:4\nbare: error Unsupported 2 4 outside the T1 fragment: statement Return at 2:4\nfalls: error Unsupported 2 4 outside the T1 fragment: statement Pass at 2:4\nuntyped: error Unsupported 1 0 missing or non-builtin annotation\nint: error Unsupported 1 9 annotation outside the T1 fragment (str only) at 1:9\nreturns: error Unsupported 1 17 annotation outside the T1 fragment (str only) at 1:17\ndefault: error Unsupported 1 0 decorated or non-simple parameters\nopen module: error Unsupported 2 0 module not closed: Import at 1:0\ntwice: error Unsupported 1 0 no unique def f\nabsent: error Unsupported 0 0 no unique def f\n"
