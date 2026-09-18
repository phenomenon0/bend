import Base
import ./syntax.bend as S

# P0 interface. The consuming scanner lands in P1.
def lex(s: String) -> Result<&2, &2, S.Error, List<&2, S.Tok>>:
  S.choose(Result<&2, &2, S.Error, List<&2, S.Tok>>, String.is_empty(s),
    u => Done{[S.Tok{"ENDMARKER", "", S.Pos{1n, 0n}, S.Pos{1n, 0n}}]},
    u => Fail{S.PErr{S.Unsupported{}, S.Pos{1n, 0n}, "P0 lexer skeleton"}})
