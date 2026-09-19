# main.bend's scan over one whole-file File.read: the materialized twin.
import Base

type Scan is Data:
  Scan{hash: U32, chars: U32, words: U32, gap: Bool}

def Scan.starts(gap: Bool, space: Bool) -> U32:
  match gap space:
    case True{} False{}:
      1
    case g s:
      0

def Scan.text(s: String, st: Scan) -> Scan:
  match s st:
    case SNil{} st:
      st
    case SCon{+c, t} Scan{h, n, w, gap}:
      +space = Char.is_space(c)
      Scan.text(t, Scan{String.hash.cell(h, Char.to_u32(c)), (n + 1 : U32),
        (w + Scan.starts(gap, space) : U32), space})

def Scan.show(st: Scan) -> String:
  Scan{h, n, w, gap} = st
  U32.show(h) ++ " " ++ U32.show(n) ++ " chars " ++ U32.show(w) ++ " words"

def choose(-A: Type, b: Bool, yes: Unit -> A, no: Unit -> A) -> A:
  match b:
    case True{}:
      yes(Unit{})
    case False{}:
      no(Unit{})

def scan(read: File & Result<&1, &1, U32 & String, String>) -> IO(Unit):
  (f, r) = read
  do IO<Unit>:
    s : String <- IO.pass(String, r)
    File.close(f)
    IO.print(Scan.show(Scan.text(s, Scan{2166136261, 0, 0, True{}})))

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("BEND_FILE"))
    f : File <- IO.try(File, File.open(path, "r"))
    read : File & Result<&1, &1, U32 & String, String> <- File.read(f, 2147483647)
    scan(read)
