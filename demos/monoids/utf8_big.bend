# utf8.bend at scale: 2^28 bytes of the same corpus, 2^d leaves. Prints the
# summary; any --threads and any d must print the same line.
import Base
import ./utf8.bend as U

def line(s: U.Sum) -> String:
  match s:
    case U.Sum{m, c}:
      "map=" ++ U.digits(m) ++ " cps=" ++ U32.show(c)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(line(U.run(10n, U.clean(1), 0, 268435456)))
