import Base
import ./syntax.bend as S

# P0 interface. P2 replaces this with direct recursion and precedence climbing.
def parse(ts: List<&2, S.Tok>) -> Result<&2, &2, S.Error, S.Module>:
  match ts:
    case Con{S.Tok{k, text, lo, hi}, Nil{}}:
      S.choose(Result<&2, &2, S.Error, S.Module>, String.eq(k, "ENDMARKER"),
        u => Done{S.Module{S.JEnd{}}},
        u => Fail{S.PErr{S.Unsupported{}, lo, "P0 parser skeleton"}})
    case _:
      Fail{S.PErr{S.Unsupported{}, S.Pos{1n, 0n}, "P0 parser skeleton"}}
