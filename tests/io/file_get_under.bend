# File.get_under opens what File.open_under opens and answers its size:
# a file under small bytes read whole and closed, a larger one left
# open with no body. The fixtures are this test's own directory and
# /dev/stdin, a symbolic link on Linux and on macOS.
import Base

def check(name: String, ok: Bool) -> IO(Unit):
  match ok:
    case True{}:
      IO.print(name)
    case False{}:
      IO.die(Unit, 1, "FAIL " ++ name)

def Got() -> Type:
  Result<&1, &1, U32 & String, U32 & U32 & Maybe<&1, File> & Bytes()>

def refused(r: Got(), +want: U32, name: String) -> IO(Unit):
  match r:
    case Done{g}:
      IO.die(Unit, 1, "FAIL opened: " ++ name)
    case Fail{e}:
      (+code, text) = e
      check(name, U32.is_eq(want, 0) || U32.is_eq(code, want))

# a small file: its bytes, as many as its size, the file closed
def held.at(+n: U32, may: Maybe<&1, File>, +bs: Bytes(), name: String) -> IO(Unit):
  match may:
    case Some{f}:
      do IO<Unit>:
        File.close(f)
        IO.die(Unit, 1, "FAIL left open: " ++ name)
    case None{}:
      check(name, Nat.is_eq(Bytes.len(bs), U32.to_nat(n))
        && Bytes.starts_with(bs, "# File.get_under"))

def held.go(g: U32 & U32 & Maybe<&1, File> & Bytes(), name: String) -> IO(Unit):
  (n, rest) = g
  (mt, fb) = rest
  (may, bs) = fb
  held.at(n, may, bs, name)

def held(r: Got(), name: String) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.die(Unit, 1, "FAIL refused: " ++ name)
    case Done{g}:
      held.go(g, name)

# a file at or past small: left open, no body, read from its start
def opened.read(got: File & Result<&1, &1, U32 & String, Bytes()>, name: String) -> IO(Unit):
  (f, r) = got
  match r:
    case Fail{e}:
      IO.die(Unit, 1, "FAIL read: " ++ name)
    case Done{bs}:
      do IO<Unit>:
        File.close(f)
        check(name, String.eq(bs, "# File"))

def opened.at(may: Maybe<&1, File>, name: String) -> IO(Unit):
  match may:
    case None{}:
      IO.die(Unit, 1, "FAIL held: " ++ name)
    case Some{f}:
      IO.bind(File & Result<&1, &1, U32 & String, Bytes()>, Unit, File.read_buf(f, 6),
        got => opened.read(got, name))

def opened.go(g: U32 & U32 & Maybe<&1, File> & Bytes(), name: String) -> IO(Unit):
  (n, rest) = g
  (mt, fb) = rest
  (may, bs) = fb
  opened.at(may, name)

def opened(r: Got(), name: String) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.die(Unit, 1, "FAIL refused: " ++ name)
    case Done{g}:
      opened.go(g, name)

def main() -> IO(Unit):
  do IO<Unit>:
    a : Got() <- File.get_under("tests/io", "file_get_under.bend", 65536)
    held(a, "a small file is read whole")
    b : Got() <- File.get_under("tests/io", "file_get_under.bend", 65536)
    held(b, "and again")
    c : Got() <- File.get_under("tests", "io/file_get_under.bend", 16)
    opened(c, "a file past small is left open")
    d : Got() <- File.get_under("tests", "io", 65536)
    refused(d, 21, "a directory is not a file")
    e : Got() <- File.get_under("tests/io", "../io/file_get_under.bend", 65536)
    refused(e, 13, "a climb is refused")
    f : Got() <- File.get_under("tests", "io/./file_get_under.bend", 65536)
    refused(f, 13, "a dot is refused")
    g : Got() <- File.get_under("tests", "io//file_get_under.bend", 65536)
    refused(g, 13, "an empty component is refused")
    h : Got() <- File.get_under("tests/io", "nope.bend", 65536)
    refused(h, 2, "a missing file is ENOENT")
    i : Got() <- File.get_under("tests/io", "file_get_under.bend/x", 65536)
    refused(i, 20, "a file is not a directory")
    j : Got() <- File.get_under("/dev", "stdin", 65536)
    refused(j, 0, "a symbolic link at the end is refused")
    k : Got() <- File.get_under("/", "dev/stdin", 65536)
    refused(k, 0, "a symbolic link below a directory is refused")

#|a small file is read whole
#|and again
#|a file past small is left open
#|a directory is not a file
#|a climb is refused
#|a dot is refused
#|an empty component is refused
#|a missing file is ENOENT
#|a file is not a directory
#|a symbolic link at the end is refused
#|a symbolic link below a directory is refused
