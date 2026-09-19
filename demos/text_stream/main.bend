# A text scan in constant memory: $BEND_FILE is read through File.read_text
# in 64 KiB chunks, and only a hash, two counts, a flag and the decoder's
# <= 3 carried bytes live between chunks, so the resident set does not grow
# with the file. whole.bend is the same scan over one File.read, which
# holds the file's 4-byte cells at once; both print the same line. Try it:
#   bash demos/text_stream/bench.sh
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

def chunk.go(k: Utf8.Dec -> String -> IO(Scan), ds: Utf8.Dec & String) -> IO(Scan):
  (d, t) = ds
  k(d, t)

def chunk(k: File -> Utf8.Dec -> String -> IO(Scan),
  got: File & Result<&1, &1, U32 & String, Utf8.Dec & String>) -> IO(Scan):
  (f, r) = got
  IO.bind(Utf8.Dec & String, Scan, IO.pass(Utf8.Dec & String, r), chunk.go(k(f)))

@unsafe
def stream(f: File, dec: Utf8.Dec, st: Scan) -> IO(Scan):
  IO.bind(File & Result<&1, &1, U32 & String, Utf8.Dec & String>, Scan,
    File.read_text(f, dec, 65536), chunk(g => d => text =>
      +nd = d
      +ns = Scan.text(text, st)
      choose(File -> IO(Scan), Utf8.Dec.eof(nd),
        u => h => IO.bind(Unit, Scan, File.close(h), v => IO.pure(Scan, ns)),
        u => h => stream(h, nd, ns))(g)))

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("BEND_FILE"))
    f : File <- IO.try(File, File.open(path, "r"))
    st : Scan <- stream(f, Utf8.Dec.new(), Scan{2166136261, 0, 0, True{}})
    IO.print(Scan.show(st))
