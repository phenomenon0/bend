# The demo's rollout, pinned: seed 35, rollout 0, K = 4, from `{`. Every lane
# has to print these bytes, the C lane on one thread and on many.
#
# Determinism is the claim that the draw is a function of (seed, rollout,
# position) and of nothing else. So the same rollout run twice must print the
# same bytes, and changing the seed or the rollout id must change them. If the
# second half failed, the first half would prove nothing.
import Base
import ../../demos/decode/main.bend as M

def doc(r: M.Run) -> String:
  match r:
    case M.Run{s, pos, d, out, bad, stop}:
      d

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(M.report(M.rollout(48n, 4, 35, 0, True{})))
    IO.print("twice, same bytes: " ++ M.yn(String.eq(M.report(M.rollout(48n, 4, 35, 0, True{})), M.report(M.rollout(48n, 4, 35, 0, True{})))))
    IO.print("seed 36 differs: " ++ M.yn(Bool.not(String.eq(doc(M.rollout(48n, 4, 35, 0, False{})), doc(M.rollout(48n, 4, 36, 0, False{}))))))
    IO.print("rollout 1 differs: " ++ M.yn(Bool.not(String.eq(doc(M.rollout(48n, 4, 35, 0, False{})), doc(M.rollout(48n, 4, 35, 1, False{}))))))
    # K = 1 keeps only the heaviest legal token, so the draw has one choice: greedy
    IO.print("greedy " ++ doc(M.rollout(48n, 1, 35, 0, False{})))
#|0 `"a"` kept 15634743@6 15468670@7 11573860@13 11392035@1 draw 15119279/54069308 -> colon/1 ok
#|1 ` ` kept 11140507@12 2413349@5 draw 483318/13553856 -> colon/1 ok
#|2 `:` kept 14527481@5 10285782@12 draw 4103405/24813263 -> val/1 ok
#|3 `[` kept 16756538@9 14754127@2 13480422@10 13199765@6 draw 17570302/58190852 -> vale/2 ok
#|4 `1` kept 14974288@15 13339763@8 11841958@6 10552938@2 draw 23527677/50708947 -> int/2 ok
#|5 ` ` kept 14502547@12 9122507@4 8783431@8 8627454@3 draw 7943887/41035939 -> sep/2 ok
#|6 `,` kept 9745293@12 9651510@3 6330760@4 draw 23052648/25727563 -> val/2 ok
#|7 `"b"` kept 16635400@7 16133872@10 15587821@14 13526870@11 draw 1317864/61883963 -> sep/2 ok
#|8 ` ` kept 11571657@12 10723886@3 5457667@4 draw 7316782/27753210 -> sep/2 ok
#|9 `]` kept 15275906@3 6337863@12 5587899@4 draw 8470311/27201668 -> sep/1 ok
#|10 `,` kept 10433186@4 4792222@1 2008453@12 draw 4485536/17233861 -> key/1 ok
#|11 `"a":` kept 10806927@13 9937379@6 9402941@16 1926834@12 draw 10337867/32074081 -> val/1 ok
#|12 `23` kept 16575347@10 16465202@9 12607437@8 11875068@12 draw 27713353/57523054 -> int/1 ok
#|13 `}` kept 15742991@4 6822595@8 5855413@1 4879121@12 draw 25739613/33300120 -> fin/0 ok
#|doc {"a" :[1 ,"b" ],"a":23}
#|steps 14 done Y bad certs 0
#|twice, same bytes: Y
#|seed 36 differs: Y
#|rollout 1 differs: Y
#|greedy {"a" :230.5 }
