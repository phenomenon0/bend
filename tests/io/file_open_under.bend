# File.open_under opens a regular file below a directory and nothing
# else: no symbolic link on the way, no "." or "..", no directory at
# the end. The fixtures are this test's own directory and /dev/stdin,
# a symbolic link on Linux and on macOS.
import Base

def check(name: String, ok: Bool) -> IO(Unit):
  match ok:
    case True{}:
      IO.print(name)
    case False{}:
      IO.die(Unit, 1, "FAIL " ++ name)

def same(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, xt} Con{y, yt}:
      U32.is_eq(x, y) && same(xt, yt)
    case _ _:
      False{}

def refused(r: Result<&1, &1, U32 & String, File>, +want: U32, name: String) ->
  IO(Unit):
  match r:
    case Done{f}:
      do IO<Unit>:
        File.close(f)
        IO.die(Unit, 1, "FAIL opened: " ++ name)
    case Fail{e}:
      (+code, text) = e
      check(name, U32.is_eq(want, 0) || U32.is_eq(code, want))

def head(got: File & Result<&1, &1, U32 & String, List<&2, U32>>, name: String) ->
  IO(Unit):
  (f, r) = got
  match r:
    case Fail{e}:
      IO.die(Unit, 1, "FAIL read: " ++ name)
    case Done{bs}:
      do IO<Unit>:
        File.close(f)
        check(name, same(bs, [35, 32, 70, 105, 108, 101]))

def opened(r: Result<&1, &1, U32 & String, File>, name: String) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.die(Unit, 1, "FAIL refused: " ++ name)
    case Done{f}:
      do IO<Unit>:
        got : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 6)
        head(got, name)

def main() -> IO(Unit):
  do IO<Unit>:
    a : Result<&1, &1, U32 & String, File> <- File.open_under("tests/io", "file_open_under.bend")
    opened(a, "a file under the root")
    b : Result<&1, &1, U32 & String, File> <- File.open_under("tests", "io/file_open_under.bend")
    opened(b, "a file two components down")
    c : Result<&1, &1, U32 & String, File> <- File.open_under("tests", "io")
    refused(c, 21, "a directory is not a file")
    d : Result<&1, &1, U32 & String, File> <- File.open_under("tests/io", "../io/file_open_under.bend")
    refused(d, 13, "a climb is refused")
    e : Result<&1, &1, U32 & String, File> <- File.open_under("tests", "io/./file_open_under.bend")
    refused(e, 13, "a dot is refused")
    f : Result<&1, &1, U32 & String, File> <- File.open_under("tests", "io//file_open_under.bend")
    refused(f, 13, "an empty component is refused")
    g : Result<&1, &1, U32 & String, File> <- File.open_under("tests/io", "nope.bend")
    refused(g, 2, "a missing file is ENOENT")
    h : Result<&1, &1, U32 & String, File> <- File.open_under("tests/io", "file_open_under.bend/x")
    refused(h, 20, "a file is not a directory")
    i : Result<&1, &1, U32 & String, File> <- File.open_under("tests/io/file_open_under.bend", "x")
    refused(i, 20, "the root must be a directory")
    j : Result<&1, &1, U32 & String, File> <- File.open_under("/dev", "stdin")
    refused(j, 0, "a symbolic link at the end is refused")
    k : Result<&1, &1, U32 & String, File> <- File.open_under("/", "dev/stdin")
    refused(k, 0, "a symbolic link below a directory is refused")

#|a file under the root
#|a file two components down
#|a directory is not a file
#|a climb is refused
#|a dot is refused
#|an empty component is refused
#|a missing file is ENOENT
#|a file is not a directory
#|the root must be a directory
#|a symbolic link at the end is refused
#|a symbolic link below a directory is refused
