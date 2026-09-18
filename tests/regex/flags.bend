# Flags i m s fold into the program; duplicate/unknown flags and oversized
# programs are compile errors.
import Base

def go(r: Result<&2, &2, Regex.Error, Regex>, s: String) -> Maybe<&2, Match>:
  match r:
    case Fail{e}:
      None{}
    case Done{re}:
      Regex.exec(re, s, 0n)

def m(p: String, f: String, s: String) -> Maybe<&2, Match>:
  go(Regex.compile(p, f), s)

def e(r: Result<&2, &2, Regex.Error, Regex>) -> Maybe<&2, Regex.Error>:
  match r:
    case Fail{e}:
      Some{e}
    case Done{re}:
      None{}

def main() -> List<&2, Maybe<&2, Match>> & List<&2, Maybe<&2, Regex.Error>>:
  ([m("abc", "i", "xABC"), m("[a-c]+", "i", "aBcD"), m("[^a]", "i", "A"), m("[^a]", "i", "b"),
    m("^b", "m", "a\nb"), m("^b", "", "a\nb"), m("a$", "m", "a\nb"), m("b$", "", "a\nb\n"),
    m("a.b", "s", "a\nb"), m("a.b", "", "a\nb"), m("^a.b$", "ims", "x\nA\nB")],
   [e(Regex.compile("a", "ii")), e(Regex.compile("a", "x")), e(Regex.compile("(a{256}){256}", "")), e(Regex.compile("a", "smi"))])

#|([Some{Match{1n, 4n, []}}, Some{Match{0n, 3n, []}}, None{}, Some{Match{0n, 1n, []}}, Some{Match{2n, 3n, []}}, None{}, Some{Match{0n, 1n, []}}, Some{Match{2n, 3n, []}}, Some{Match{0n, 3n, []}}, None{}, Some{Match{2n, 5n, []}}], [Some{RErr{0n, "duplicate flag"}}, Some{RErr{0n, "unknown flag"}}, Some{RErr{0n, "program exceeds max_prog"}}, None{}])
