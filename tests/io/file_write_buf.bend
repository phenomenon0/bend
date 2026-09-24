# File.write_buf writes a Bytes as it lies: every byte value 0..255 comes
# back from the file as it went in, an empty write writes nothing, and a
# Char past 255 fails with EINVAL before any byte is written.
import Base

def bytes(n: Nat, +at: U32) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      at <> bytes(p, U32.add(at, 1))

def same(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case x <> xt y <> yt:
      Bool.and(U32.is_eq(x, y), same(xt, yt))
    case _ _:
      False{}

def check(name: String, ok: Bool) -> IO(Unit):
  match ok:
    case True{}:
      IO.print(name)
    case False{}:
      IO.die(Unit, 1, "FAIL " ++ name)

def wrote(pair: File & Result<&1, &1, U32 & String, Unit>) -> IO(File):
  (file, result) = pair
  do IO<File>:
    IO.pass(Unit, result)
    return file

def refused(pair: File & Result<&1, &1, U32 & String, Unit>) -> IO(File):
  (file, result) = pair
  match result:
    case Done{u}:
      do IO<File>:
        IO.die(Unit, 1, "FAIL a Char past 255 written")
        return file
    case Fail{(code, msg)}:
      do IO<File>:
        check("a Char past 255 is EINVAL", U32.is_eq(code, 22))
        return file

def sized(pair: File & Result<&1, &1, U32 & String, U32>, want: U32, name: String) -> IO(File):
  (file, result) = pair
  do IO<File>:
    got : U32 <- IO.pass(U32, result)
    check(name, U32.is_eq(got, want))
    return file

def read(pair: File & Result<&1, &1, U32 & String, List<&2, U32>>, want: List<&2, U32>, name: String) -> IO(File):
  (file, result) = pair
  do IO<File>:
    got : List<&2, U32> <- IO.pass(List<&2, U32>, result)
    check(name, same(got, want))
    return file

def main() -> IO(Unit):
  do IO<Unit>:
    f : File <- IO.try(File, File.open("/tmp/bend_io_file_write_buf", "w"))
    p : File & Result<&1, &1, U32 & String, Unit> <- File.write_buf(f, "")
    f : File <- wrote(p)
    p : File & Result<&1, &1, U32 & String, Unit> <- File.write_buf(f, "ab\u{100}")
    f : File <- refused(p)
    p : File & Result<&1, &1, U32 & String, U32> <- File.size(f)
    f : File <- sized(p, 0, "nothing written before the refusal")
    p : File & Result<&1, &1, U32 & String, Unit> <- File.write_buf(f, Bytes.from_list(bytes(256n, 0)))
    f : File <- wrote(p)
    File.close(f)
    g : File <- IO.try(File, File.open("/tmp/bend_io_file_write_buf", "r"))
    q : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_at(g, 0, 300)
    g : File <- read(q, bytes(256n, 0), "every byte value, as it went in")
    File.close(g)

#|a Char past 255 is EINVAL
#|nothing written before the refusal
#|every byte value, as it went in
