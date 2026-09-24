# F11: Base's String.take recurses once a char (SCon{h, take(t, p)}), and
# the JS lane (and the interpreter, for an IO main) runs that on the
# machine stack: 40000 chars end in "bend: memory fault (machine stack
# overflow?)", 20000 pass. The C lane takes it. So does from_list, a
# structural to_list, List.append: a CSV field or a JSON string past a few
# ten thousand bytes, cut with Base's String.take, crashes canon's JS lane.
import Base

def build(k: Nat, acc: String) -> String:
  match k:
    case 0n:
      acc
    case 1n+j:
      build(j, SCon{Chr{97}, acc})

def main() -> IO(Unit):
  IO.print(Nat.show(String.length(String.take(build(300000n, ""), 40000n))))

#|40000
