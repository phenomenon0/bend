# Never a silent guess: every source outside the fragment blocks emission with
# a positioned diagnostic. `near` and `let` are the positive controls: a literal
# receiver and a single-use let are inside the fragment. Spelling is not authority (`str.lower(s)`,
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

# T2: the control idioms. What is refused is what `repo_of` does not need, or
# what Python could make observable: truthiness, an early return from a loop
# (T3), a loop with no or several accumulators, a partial operation whose guard
# is not known on the path (the kernel's refusal, positioned at the def).
def opt() -> String:
  "def f(s: str, xs: list[str]) -> str | None:\n    "

def t2() -> String:
  one("loop", opt() ++ "best = None\n    for x in xs:\n        if x == s:\n            best = x\n    return best\n") ++
  one("break", opt() ++ "best = None\n    for x in xs:\n        if x == s:\n            best = x\n            break\n    return best\n") ++
  one("guarded split", opt() ++ "if '.' not in s:\n        return None\n    return s.split('.', 1)[1]\n") ++
  one("guard and", opt() ++ "if s.startswith('a') and '.' in s:\n        return s.split('.', 1)[1]\n    return None\n") ++
  one("unguarded split", opt() ++ "return s.split('.', 1)[1]\n") ++
  one("other guard", opt() ++ "if '-' not in s:\n        return None\n    return s.split('.', 1)[1]\n") ++
  one("guard rebound", opt() ++ "if '.' not in s:\n        return None\n    s = s.lower()\n    return s.split('.', 1)[1]\n") ++
  one("guard or", opt() ++ "if '.' in s or s == 'a':\n        return s.split('.', 1)[1]\n    return None\n") ++
  one("empty sep", opt() ++ "if '' not in s:\n        return None\n    return s.split('', 1)[1]\n") ++
  one("split all", opt() ++ "return s.split('.')[1]\n") ++
  one("index", opt() ++ "return s[1]\n") ++
  one("truthy if", opt() ++ "if s:\n        return s\n    return None\n") ++
  one("truthy or", opt() ++ "if s or s == 'a':\n        return s\n    return None\n") ++
  one("early return", opt() ++ "best = None\n    for x in xs:\n        best = x\n        return x\n    return best\n") ++
  one("no accumulator", opt() ++ "for x in xs:\n        y = x\n    return None\n") ++
  one("two accumulators", opt() ++ "a = None\n    b = None\n    for x in xs:\n        a = x\n        b = x\n    return a\n") ++
  one("for else", opt() ++ "a = None\n    for x in xs:\n        a = x\n    else:\n        a = None\n    return a\n") ++
  one("target bound", opt() ++ "a = None\n    for s in xs:\n        a = s\n    return a\n") ++
  one("nested for", opt() ++ "a = None\n    for x in xs:\n        for y in xs:\n            a = y\n    return a\n") ++
  one("after if in loop", opt() ++ "a = None\n    for x in xs:\n        if x == s:\n            a = x\n        a = None\n    return a\n") ++
  one("for over str", opt() ++ "a = None\n    for x in s:\n        a = x\n    return a\n") ++
  one("break outside", opt() ++ "break\n") ++
  one("while", opt() ++ "while s == 'a':\n        return s\n    return None\n") ++
  one("path falls", opt() ++ "if s == 'a':\n        s = 'b'\n    return s\n") ++
  one("is none", opt() ++ "if s is None:\n        return None\n    return s\n") ++
  one("none type", "def f(s: str) -> str:\n    return None\n") ++
  one("retyped", opt() ++ "a = None\n    a = s == 'a'\n    return a\n") ++
  one("user call", opt() ++ "return g(s)\n") ++
  one("chain", opt() ++ "if s == s == s:\n        return s\n    return None\n") ++
  one("augassign", opt() ++ "s += 'a'\n    return s\n") ++
  one("tuple target", opt() ++ "a, b = s, s\n    return a\n") ++
  one("len escapes", opt() ++ "return len(s)\n")

def main() -> String:
  one("near", head() ++ "return ' A '.strip().lower()\n") ++
  one("let", head() ++ "x = s.strip()\n    return x\n") ++
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
  one("after", head() ++ "return s\n    return s.lower()\n") ++
  one("bare", head() ++ "return\n") ++
  one("falls", head() ++ "pass\n") ++
  one("untyped", "def f(s) -> str:\n    return s\n") ++
  one("int", "def f(s: int) -> str:\n    return s\n") ++
  one("returns", "def f(s: str) -> bool:\n    return s\n") ++
  one("default", "def f(s: str = 'a') -> str:\n    return s\n") ++
  one("open module", "import re\n" ++ head() ++ "return s\n") ++
  one("twice", head() ++ "return s\n" ++ head() ++ "return s.lower()\n") ++
  one("absent", "def g(s: str) -> str:\n    return s\n") ++
  t2()
#|"near: emitted\nlet: emitted\nmethod: error Unsupported 2 11 no verified contract for .title on (String) with () at 2:11\narity: error Unsupported 2 11 no verified contract for .strip on (String) with (String;) at 2:11\nkeyword: error Unsupported 2 11 outside the fragment: Call at 2:11\nspelling: error Unsupported 2 11 unresolved name str at 2:11\nbuiltin: error Unsupported 2 4 type mismatch: (Nat) where (String) is expected at 2:4\nname: error Unsupported 2 11 unresolved name t at 2:11\nescape: error Unsupported 2 21 literal outside the contract (one plain ASCII string, no escapes; True, False, None) at 2:21\nadjacent: error Unsupported 2 21 literal outside the contract (one plain ASCII string, no escapes; True, False, None) at 2:21\nunbound method: error Unsupported 2 11 outside the fragment: Attribute at 2:11\nifexp: error Unsupported 2 16 truthiness of a non-bool is outside the fragment at 2:16\nafter: error Unsupported 3 4 statement after return at 3:4\nbare: error Unsupported 2 4 outside the fragment: statement Return at 2:4\nfalls: error Unsupported 2 4 outside the fragment: statement Pass at 2:4\nuntyped: error Unsupported 1 0 missing or non-builtin annotation\nint: error Unsupported 1 9 annotation outside the fragment (str, bool, list[T], T | None) at 1:9\nreturns: error Unsupported 2 4 type mismatch: (String) where (Bool) is expected at 2:4\ndefault: error Unsupported 1 0 decorated or non-simple parameters\nopen module: error Unsupported 2 0 module not closed: Import at 1:0\ntwice: error Unsupported 1 0 no unique def f\nabsent: error Unsupported 0 0 no unique def f\nloop: emitted\nbreak: emitted\nguarded split: emitted\nguard and: emitted\nunguarded split: error Unsupported 1 0 primitive Py.after is not granted by a contract (or its guard is not known here) at 2:11\nother guard: error Unsupported 1 0 primitive Py.after is not granted by a contract (or its guard is not known here) at 4:11\nguard rebound: error Unsupported 1 0 primitive Py.after is not granted by a contract (or its guard is not known here) at 5:11\nguard or: error Unsupported 1 0 primitive Py.after is not granted by a contract (or its guard is not known here) at 3:15\nempty sep: error Unsupported 1 0 primitive Py.after is not granted by a contract (or its guard is not known here) at 4:11\nsplit all: error Unsupported 2 11 outside the fragment: Subscript at 2:11\nindex: error Unsupported 2 11 outside the fragment: Subscript at 2:11\ntruthy if: error Unsupported 2 7 truthiness of a non-bool is outside the fragment at 2:7\ntruthy or: error Unsupported 2 7 truthiness of a non-bool is outside the fragment at 2:7\nearly return: error Unsupported 5 8 early return inside a loop is outside the fragment (T3) at 5:8\nno accumulator: error Unsupported 2 4 for: the body must assign exactly one name bound before the loop (the accumulator) at 2:4\ntwo accumulators: error Unsupported 4 4 for: the body must assign exactly one name bound before the loop (the accumulator) at 4:4\nfor else: error Unsupported 3 4 for: the target must be one fresh name and there is no else at 3:4\ntarget bound: error Unsupported 3 4 for: the target must be one fresh name and there is no else at 3:4\nnested for: error Unsupported 4 8 outside the fragment: statement For at 4:8\nafter if in loop: error Unsupported 6 8 statement after if inside a loop is outside the fragment at 6:8\nfor over str: error Unsupported 3 13 for over a non-list (String) at 3:13\nbreak outside: error Unsupported 2 4 outside the fragment: statement Break at 2:4\nwhile: error Unsupported 2 4 outside the fragment: statement While at 2:4\npath falls: error Unsupported 3 8 no return: falling off the end is outside the fragment at 3:8\nis none: error Unsupported 2 7 `is None` on a name that is not Optional: s at 2:7\nnone type: error Unsupported 2 11 None outside an Optional return type at 2:11\nretyped: error Unsupported 3 4 type mismatch: (Bool) where (Maybe<&2, String>) is expected at 3:4\nuser call: error Unsupported 2 11 outside the fragment: Call at 2:11\nchain: error Unsupported 2 7 outside the fragment: Compare chain at 2:7\naugassign: error Unsupported 2 4 outside the fragment: statement AugAssign at 2:4\ntuple target: error Unsupported 2 4 outside the fragment: statement Assign at 2:4\nlen escapes: error Unsupported 2 4 type mismatch: (Nat) where (Maybe<&2, String>) is expected at 2:4\n"
