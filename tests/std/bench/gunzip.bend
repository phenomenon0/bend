# std's gunzip bench: a .gz file read whole and inflated by Gzip.gunzip
# (the output capped at 1 GB); prints the output's length and CRC-32, which
# run.py holds to CPython's gzip and zlib.
#   bend tests/std/bench/gunzip.bend -o gz && ./gz FILE.gz
import Base
import ../../../std/bytes.bend as By
import ../../../std/deflate.bend as D
import ../../../std/gzip.bend as Z

def path(args: List<String>) -> String:
  match args:
    case Nil{}:
      "/tmp/bend-gunzip-bench.gz"
    case Con{p, t}:
      p

def out(r: Result<&2, &2, Z.Err, String>) -> String:
  match r:
    case Done{+b}:
      Nat.show(By.len(b)) ++ " bytes, crc32 " ++ U32.show(D.crc32(b, 0))
    case Fail{e}:
      "refused"

def got(r: Result<&1, &1, U32 & String, String>) -> String:
  match r:
    case Fail{e}:
      "no file"
    case Done{+b}:
      out(Z.gunzip(U32.to_nat(1000000000), b))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    r : Result<&1, &1, U32 & String, String> <- By.read_file(path(args))
    IO.print(got(r))
