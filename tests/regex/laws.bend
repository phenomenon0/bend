# Laws tying the derived API together, one row of six per (pattern, subject):
# is_match <=> is_some(find); join(split, "") = replace(.., "") (either way
# round); group 0 = the source slice; find_all starts increase, or stay put
# only for empty-then-non-empty (the finditer retry); match_at(i) starts at
# i; fullmatch ends at the length. A pattern that fails to compile or a
# search that runs out of budget is a False, never a skipped row.
import Base

def iff(+re: Regex, +s: String) -> Bool:
  Bool.not(Bool.xor(Regex.is_match(re, s), Maybe.is_some(&2, Match, Regex.find(re, s))))

def joined(sp: Result<&2, &2, Regex.Error, List<&2, String>>, rp: Result<&2, &2, Regex.Error, String>) -> Bool:
  match sp rp:
    case Done{ps} Done{r}:
      String.eq(String.join(ps, ""), r)
    case _ _:
      False{}

def whole(g: Maybe<&2, String>, want: String) -> Bool:
  match g:
    case None{}:
      False{}
    case Some{t}:
      String.eq(t, want)

def group0.go(ms: List<&2, Match>, +s: String) -> Bool:
  match ms:
    case Nil{}:
      True{}
    case Match{+a, +b, +gs} <> t:
      Bool.and(whole(Regex.group(s, Match{a, b, gs}, 0n), String.slice(s, a, b)), group0.go(t, s))

def group0(r: Result<&2, &2, Regex.Error, List<&2, Match>>, s: String) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{ms}:
      group0.go(ms, s)

def order.go(ms: List<&2, Match>, +a: Nat, +b: Nat) -> Bool:
  match ms:
    case Nil{}:
      True{}
    case Match{+c, +d, gs} <> t:
      Bool.and(Bool.and(Nat.is_ge(c, b), Bool.or(Nat.is_gt(c, a), Bool.and(Nat.is_eq(a, b), Nat.is_gt(d, c)))), order.go(t, c, d))

def order(r: Result<&2, &2, Regex.Error, List<&2, Match>>) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{Nil{}}:
      True{}
    case Done{Match{a, b, gs} <> t}:
      order.go(t, a, b)

def starts(m: Maybe<&2, Match>, i: Nat) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Match{a, b, gs}}:
      Nat.is_eq(a, i)

def anchored(ks: List<&2, Nat>, +re: Regex, +s: String) -> Bool:
  match ks:
    case Nil{}:
      True{}
    case +i <> t:
      Bool.and(starts(Regex.match_at(re, s, i), i), anchored(t, re, s))

def ends(m: Maybe<&2, Match>, n: Nat) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Match{a, b, gs}}:
      Nat.is_eq(b, n)

def laws(r: Result<&2, &2, Regex.Error, Regex>, +s: String) -> List<&2, Bool>:
  match r:
    case Fail{e}:
      [False{}]
    case Done{+re}:
      [iff(re, s), joined(Regex.split(re, s, 1000000), Regex.replace(re, s, "", 1000000)), group0(Regex.find_all(re, s, 1000000), s), order(Regex.find_all(re, s, 1000000)), anchored(List.range(1n+String.length(s)), re, s), ends(Regex.fullmatch(re, s), String.length(s))]

def main() -> List<&2, List<&2, Bool>>:
  [laws(Regex.compile("|a", ""), "aba"), laws(Regex.compile("a*", ""), "baac"), laws(Regex.compile("a*?", ""), "aa"),
   laws(Regex.compile("(a)|b", ""), "abc"), laws(Regex.compile("\\b", ""), "ab cd"), laws(Regex.compile("$", "m"), "a\nb\n"),
   laws(Regex.compile("x", ""), "abc"), laws(Regex.compile("", ""), ""), laws(Regex.compile("(?:a|ab)(c|bcd)?", ""), "abcdab"),
   laws(Regex.compile("😀*", ""), "a😀😀b")]

#|[[True{}, True{}, True{}, True{}, True{}, True{}], [True{}, True{}, True{}, True{}, True{}, True{}], [True{}, True{}, True{}, True{}, True{}, True{}], [True{}, True{}, True{}, True{}, True{}, True{}], [True{}, True{}, True{}, True{}, True{}, True{}], [True{}, True{}, True{}, True{}, True{}, True{}], [True{}, True{}, True{}, True{}, True{}, True{}], [True{}, True{}, True{}, True{}, True{}, True{}], [True{}, True{}, True{}, True{}, True{}, True{}], [True{}, True{}, True{}, True{}, True{}, True{}]]
