# One budget for a whole global call. A search from `at` must afford
# (1 + length - at) * weight before it runs and pays the span it walked, so
# a plain scan is linear while the rescan pattern `a.*b|a` on n `a`s costs weight * (n+1)(n+2)/2: quadratic, pinned, never
# exponential (`^(a+)+$` is one search). Output is paid from what is left:
# 1 + ngroups per Match, 1 per code point. One unit short at any stage is
# an error carrying where it ran out, never a partial answer.
import Base

def left(r: Result<&2, &2, Regex.Error, Regex.scan.Out()>) -> U32:
  match r:
    case Fail{e}:
      0
    case Done{(l, ms)}:
      l

# (weight, what a full scan spends out of 1000000)
def spent(r: Result<&2, &2, Regex.Error, Regex>, s: String) -> Sigma<&2, &2, U32, _ => U32>:
  match r:
    case Fail{e}:
      (0, 0)
    case Done{+re}:
      (Regex.weight(re), U32.sub(1000000, left(Regex.scan(re, s, 1000000))))

def all(r: Result<&2, &2, Regex.Error, Regex>, s: String, limit: U32) -> Result<&2, &2, Regex.Error, List<&2, Match>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{re}:
      Regex.find_all(re, s, limit)

def sub(r: Result<&2, &2, Regex.Error, Regex>, s: String, by: String, limit: U32) -> Result<&2, &2, Regex.Error, String>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{re}:
      Regex.replace(re, s, by, limit)

def cut(r: Result<&2, &2, Regex.Error, Regex>, s: String, limit: U32) -> Result<&2, &2, Regex.Error, List<&2, String>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{re}:
      Regex.split(re, s, limit)

def main() -> List<&2, Sigma<&2, &2, U32, _ => U32>> & List<&2, Result<&2, &2, Regex.Error, List<&2, Match>>> & List<&2, Result<&2, &2, Regex.Error, String>> & List<&2, Result<&2, &2, Regex.Error, List<&2, String>>>:
  ([spent(Regex.compile("a.*b|a", ""), "aaaa"), spent(Regex.compile("a.*b|a", ""), "aaaaaaaa"), spent(Regex.compile("a.*b|a", ""), "aaaaaaaaaaaaaaaa"), spent(Regex.compile("^(a+)+$", ""), "aaaaaaaaaaaaaaaaaaaaaaaab")],
   ([all(Regex.compile("a.*b|a", ""), "aaaa", 514), all(Regex.compile("a.*b|a", ""), "aaaa", 513), all(Regex.compile("a.*b|a", ""), "aaaa", 509), all(Regex.compile("a.*b|a", ""), "aaaa", 0), all(Regex.compile("(a)|b", ""), "ab", 1000)],
    ([sub(Regex.compile("a", ""), "aba", "xyz", 98), sub(Regex.compile("a", ""), "aba", "xyz", 97)],
     [cut(Regex.compile("a", ""), "aba", 92), cut(Regex.compile("a", ""), "aba", 91)])))

#|([(34, 510), (34, 1530), (34, 5202), (96, 2496)], [Done{[Match{0n, 1n, []}, Match{1n, 2n, []}, Match{2n, 3n, []}, Match{3n, 4n, []}]}, Fail{RErr{4n, "budget exhausted"}}, Fail{RErr{4n, "budget exhausted"}}, Fail{RErr{0n, "budget exhausted"}}, Done{[Match{0n, 1n, [Some{(0n, 1n)}]}, Match{1n, 2n, [None{}]}]}], [Done{"xyzbxyz"}, Fail{RErr{3n, "budget exhausted"}}], [Done{["", "b", ""]}, Fail{RErr{3n, "budget exhausted"}}])
