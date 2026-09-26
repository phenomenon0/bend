# F10: the JS lane walks a String 15-20x slower than the C lane. A String
# is a JS string there: SCon builds with `h + t` and a match takes it
# apart with slice(1) and codePointAt (comp.ts's String native), so a
# million-character walk costs about a second (C: 0.05 s). std/csv.bend
# reads 0.34 MB/s in canon's JS lane and 7.3 MB/s in its C lane.
import Base

def count(s: String, +n: U32) -> U32:
  match s:
    case SNil{}:
      n
    case SCon{Chr{c}, t}:
      count(t, Bool.pick(U32, U32.is_eq(c, 97), U32.inc(n), n))

def build(k: Nat, acc: String) -> String:
  match k:
    case 0n:
      acc
    case 1n+j:
      build(j, SCon{Chr{97}, SCon{Chr{98}, acc}})

def main() -> IO(Unit):
  IO.print(U32.show(count(build(500000n, ""), 0)))

#|500000
