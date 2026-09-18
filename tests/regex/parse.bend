# Regex.parse: 14 trees. Alternation and concatenation nest to the right;
# groups number by their open paren; a lazy repeat is greedy=False.
import Base

def p(s: String) -> Result<&2, &2, Regex.Error, Re>:
  Regex.parse(s)

def main() -> List<&2, Result<&2, &2, Regex.Error, Re>>:
  [p(""), p("a"), p("ab"), p("a|b|c"), p("a*"), p("a+?"), p("a??"), p("a{2}"),
   p("a{2,}"), p("a{2,3}?"), p("(a)(?:b)"), p("(a(b)?)+"), p("[^a-z\\d_]"), p("^\\bx.$")]

#|[Done{REmpty{}}, Done{RLit{'a'}}, Done{RCat{RLit{'a'}, RLit{'b'}}}, Done{RAlt{RLit{'a'}, RAlt{RLit{'b'}, RLit{'c'}}}}, Done{RRep{RLit{'a'}, 0n, None{}, True{}}}, Done{RRep{RLit{'a'}, 1n, None{}, False{}}}, Done{RRep{RLit{'a'}, 0n, Some{1n}, False{}}}, Done{RRep{RLit{'a'}, 2n, Some{2n}, True{}}}, Done{RRep{RLit{'a'}, 2n, None{}, True{}}}, Done{RRep{RLit{'a'}, 2n, Some{3n}, False{}}}, Done{RCat{RCap{1n, RLit{'a'}}, RLit{'b'}}}, Done{RRep{RCap{1n, RCat{RLit{'a'}, RRep{RCap{2n, RLit{'b'}}, 0n, Some{1n}, True{}}}}, 1n, None{}, True{}}}, Done{RSet{True{}, [(95, 95), (48, 57), (97, 122)]}}, Done{RCat{RBol{}, RCat{RWordB{False{}}, RCat{RLit{'x'}, RCat{RAny{}, REol{}}}}}}]
