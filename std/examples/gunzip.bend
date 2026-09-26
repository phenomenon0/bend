# Gunzip a file and print what it held; then gzip it again and write the
# member next to it.
#   bend std/examples/gunzip.bend [FILE.gz]    (from the directory holding std/)
import Base
import ../bytes.bend as By
import ../gzip.bend as Gzip
import ../text.bend as Text

# the output is capped (here at 1 MB): a gzip bomb is refused, not obeyed
def unzip(+gz: String) -> Result<&2, &2, Gzip.Err, String>:
  Gzip.gunzip(1048576n, gz)

def show(r: Result<&2, &2, Gzip.Err, String>) -> String:
  match r:
    case Done{+b}:
      Nat.show(By.len(b)) ++ " bytes:\n" ++ Text.decode(b)
    case Fail{e}:
      "not a gzip file, or a damaged one"

def read(r: Result<&1, &1, U32 & String, String>) -> String:
  match r:
    case Done{+gz}:
      show(unzip(gz))
    case Fail{(code, msg)}:
      "cannot read the file: " ++ msg

# one gzip member at level 9, which any gunzip reads back
def zip(r: Result<&2, &2, Gzip.Err, String>) -> String:
  match r:
    case Done{+b}:
      Gzip.gzip(b, 9n)
    case Fail{e}:
      ""

def run(r: Result<&1, &1, U32 & String, String>) -> IO(Unit):
  match r:
    case Done{+gz}:
      do IO<Unit>:
        IO.print(show(unzip(gz)))
        w : Result<&1, &1, U32 & String, Unit> <- By.write_file("/tmp/bend-std-hello.txt.gz", zip(unzip(gz)))
        back : Result<&1, &1, U32 & String, String> <- By.read_file("/tmp/bend-std-hello.txt.gz")
        IO.print(read(back))
    case Fail{(code, msg)}:
      IO.print("cannot read the file: " ++ msg)

def path(args: List<String>) -> String:
  match args:
    case Nil{}:
      "std/examples/data/hello.txt.gz"
    case Con{p, t}:
      p

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    r : Result<&1, &1, U32 & String, String> <- By.read_file(path(args))
    run(r)

#|108 bytes:
#|Hello from a gzip file.
#|Olá, naïve café: UTF-8 survives.
#|Hello from a gzip file.
#|Hello from a gzip file.
#|
#|108 bytes:
#|Hello from a gzip file.
#|Olá, naïve café: UTF-8 survives.
#|Hello from a gzip file.
#|Hello from a gzip file.
