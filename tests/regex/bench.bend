# The regex bench: bench.py keeps every def here and swaps main for one case
# at size. A text is k 64-code-point lines and one tail line, the only place
# any of the four patterns matches, so one exec reads all of it: O(n * m).
# `native` is Regex.exec (the native row of comp.ts), `reference` the Pike VM
# of base. The rescan case is `a.*b|a` on n `a`s, one search per `a`, each to
# the end of the text: n(n+1)/2 steps. `Regex.find_all` drives it on the
# reference VM (its `ne` retry has no native row); `rescan` is the same walk
# on the native.
import Base

def text(k: Nat) -> String:
  String.append(String.repeat("the quick brown fox 0123 jumps over the lazy dog; é😀 abc@de fgh\n", k), "id=2026-09-18 <Fable@Bend.org> quiet aXbz\n")

def pat(i: Nat) -> Result<&2, &2, Regex.Error, Regex>:
  match i:
    case 0n:
      Regex.compile("Fable@Bend", "")
    case 1n:
      Regex.compile("[0-9]{4}-[0-9]{2}-[0-9]{2}", "")
    case 2n:
      Regex.compile("<(\\w+)@(\\w+)\\.(com|net|org)>", "i")
    case 1n+p:
      Regex.compile("q.*X.z$", "m")

def span(m: Maybe<&2, Match>) -> Maybe<&2, Regex.Span()>:
  match m:
    case None{}:
      None{}
    case Some{Match{a, b, gs}}:
      Some{(a, b)}

def native(r: Result<&2, &2, Regex.Error, Regex>, s: String) -> Maybe<&2, Regex.Span()>:
  match r:
    case Fail{e}:
      None{}
    case Done{re}:
      span(Regex.exec(re, s, 0n))

def reference(r: Result<&2, &2, Regex.Error, Regex>, s: String) -> Maybe<&2, Regex.Span()>:
  match r:
    case Fail{e}:
      None{}
    case Done{re}:
      span(Regex.exec.go(re, s, 0n, False{}, False{}, False{}))

def rescan.go(fuel: Nat, +re: Regex, +s: String, m: Maybe<&2, Match>, n: Nat) -> Nat:
  match fuel:
    case 0n:
      n
    case 1n+f:
      match m:
        case None{}:
          n
        case Some{Match{a, b, gs}}:
          rescan.go(f, re, s, Regex.exec(re, s, b), 1n+n)

def rescan.at(fuel: Nat, +re: Regex, +s: String) -> Nat:
  rescan.go(fuel, re, s, Regex.exec(re, s, 0n), 0n)

# matches found by the native walk
def rescan(r: Result<&2, &2, Regex.Error, Regex>, +n: Nat) -> Nat:
  match r:
    case Fail{e}:
      0n
    case Done{re}:
      rescan.at(1n+n, re, String.repeat("a", n))

def rescan.len(r: Result<&2, &2, Regex.Error, List<&2, Match>>) -> Nat:
  match r:
    case Fail{e}:
      0n
    case Done{ms}:
      List.length(&2, Match, ms)

# matches found by find_all (0n: the budget ran out)
def rescan.all(r: Result<&2, &2, Regex.Error, Regex>, n: Nat) -> Nat:
  match r:
    case Fail{e}:
      0n
    case Done{re}:
      rescan.len(Regex.find_all(re, String.repeat("a", n), 4294967295))

def main() -> List<&2, Maybe<&2, Regex.Span()>> & List<&2, Maybe<&2, Regex.Span()>> & (Nat & Nat):
  ([native(pat(0n), text(2n)), native(pat(1n), text(2n)), native(pat(2n), text(2n)), native(pat(3n), text(2n))],
   ([reference(pat(0n), text(2n)), reference(pat(1n), text(2n)), reference(pat(2n), text(2n)), reference(pat(3n), text(2n))],
    (rescan(Regex.compile("a.*b|a", ""), 8n), rescan.all(Regex.compile("a.*b|a", ""), 8n))))

#|([Some{(143n, 153n)}, Some{(131n, 141n)}, Some{(142n, 158n)}, Some{(159n, 169n)}], [Some{(143n, 153n)}, Some{(131n, 141n)}, Some{(142n, 158n)}, Some{(159n, 169n)}], 8n, 8n)
