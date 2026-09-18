# The global driver in Python finditer order: after an empty match the same
# position is retried refusing the empty match (`|a` on `a`), an empty match
# may touch the end of the one before (`a*` on `ab`). split = the gaps only
# (no separators, no groups: Python would give ['a', ',', 'b'] for `(,)`);
# find_all = Match records; replace text is literal; group: absent is None.
import Base

def all(r: Result<&2, &2, Regex.Error, Regex>, s: String) -> Result<&2, &2, Regex.Error, List<&2, Match>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{re}:
      Regex.find_all(re, s, 1000000)

def cut(r: Result<&2, &2, Regex.Error, Regex>, s: String) -> Result<&2, &2, Regex.Error, List<&2, String>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{re}:
      Regex.split(re, s, 1000000)

def sub(r: Result<&2, &2, Regex.Error, Regex>, s: String, by: String) -> Result<&2, &2, Regex.Error, String>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{re}:
      Regex.replace(re, s, by, 1000000)

def grp.of(m: Maybe<&2, Match>, s: String, k: Nat) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{m}:
      Regex.group(s, m, k)

def grp(r: Result<&2, &2, Regex.Error, Regex>, +s: String, k: Nat) -> Maybe<&2, String>:
  match r:
    case Fail{e}:
      None{}
    case Done{re}:
      grp.of(Regex.find(re, s), s, k)

def main() -> List<&2, Result<&2, &2, Regex.Error, List<&2, Match>>> & List<&2, Result<&2, &2, Regex.Error, List<&2, String>>> & List<&2, Result<&2, &2, Regex.Error, String>> & List<&2, Maybe<&2, String>>:
  ([all(Regex.compile("|a", ""), "a"), all(Regex.compile("a*", ""), "ab"), all(Regex.compile("a*?", ""), "aa"), all(Regex.compile("x", ""), "abc")],
   ([cut(Regex.compile("x*", ""), "axb"), cut(Regex.compile(",", ""), "a,,b"), cut(Regex.compile("(,)", ""), "a,b"), cut(Regex.compile("|a", ""), "a"), cut(Regex.compile("x", ""), "")],
    ([sub(Regex.compile("x*", ""), "abxd", "-"), sub(Regex.compile("\\d+", ""), "a1b22", "\\1&"), sub(Regex.compile("$", "m"), "a\nb\n", "!"), sub(Regex.compile("😀", ""), "a😀b", "")],
     [grp(Regex.compile("x(a)(b)?", ""), "zxa", 0n), grp(Regex.compile("x(a)(b)?", ""), "zxa", 1n), grp(Regex.compile("x(a)(b)?", ""), "zxa", 2n), grp(Regex.compile("x(a)(b)?", ""), "zxa", 3n), grp(Regex.compile("x(a*)", ""), "zx", 1n)])))

#|([Done{[Match{0n, 0n, []}, Match{0n, 1n, []}, Match{1n, 1n, []}]}, Done{[Match{0n, 1n, []}, Match{1n, 1n, []}, Match{2n, 2n, []}]}, Done{[Match{0n, 0n, []}, Match{0n, 1n, []}, Match{1n, 1n, []}, Match{1n, 2n, []}, Match{2n, 2n, []}]}, Done{[]}], [Done{["", "a", "", "b", ""]}, Done{["a", "", "b"]}, Done{["a", "b"]}, Done{["", "", "", ""]}, Done{[""]}], [Done{"-a-b--d-"}, Done{"a\\1&b\\1&"}, Done{"a!\nb!\n!"}, Done{"ab"}], [Some{"xa"}, Some{"a"}, None{}, None{}, Some{""}])
