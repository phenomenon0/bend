# U05: File.write takes a String (code points) and writes its UTF-8, so
# U+0080 and U+00E9 are the four bytes c2 80 c3 a9, which is right for
# text; bytes go through File.write_bytes, which writes 80 e9 as they
# are. Both are read back with File.read_bytes, from a file in the
# working directory.
import Base

law hex:
  for xs: List<&2, U32>
  String

def hex(xs):
  match xs:
    case []:
      ""
    case x <> t:
      U32.show(x) ++ " " ++ hex(t)

law read_done:
  for m: File & Result<&1, &1, U32 & String, List<&2, U32>>
  IO(Unit)

def read_done(m):
  (f, r) = m
  do IO<Unit>:
    xs : List<&2, U32> <- IO.pass(List<&2, U32>, r)
    IO.print(hex(xs))
    File.close(f)

law wrote:
  for m: File & Result<&1, &1, U32 & String, Unit>
  IO(Unit)

def wrote(m):
  (f, r) = m
  do IO<Unit>:
    IO.pass(Unit, r)
    File.close(f)

law back:
  for path: String
  IO(Unit)

def back(path):
  do IO<Unit>:
    f : File <- IO.try(File, File.open(path, "r"))
    m : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 64)
    read_done(m)

law main:
  IO(Unit)

def main():
  do IO<Unit>:
    f : File <- IO.try(File, File.open("bend_upstream_u05", "w"))
    m : File & Result<&1, &1, U32 & String, Unit> <- File.write(f, "\u{80}\u{e9}")
    wrote(m)
    back("bend_upstream_u05")
    f : File <- IO.try(File, File.open("bend_upstream_u05", "w"))
    m : File & Result<&1, &1, U32 & String, Unit> <- File.write_bytes(f, [128, 233])
    wrote(m)
    back("bend_upstream_u05")

#|194 128 195 169
#|128 233
