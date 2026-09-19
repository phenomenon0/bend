# File.fold_text: a fold over a file's File.read_text chunks answers the
# whole file's fold at every chunk size (utf8.bin decodes to 15 scalars,
# as io_stream's "15 chars"), wherever a chunk cuts a scalar.
import Base

def count(n: U32, s: String) -> U32:
  (n + U32.from_nat(String.length(s)) : U32)

def run(max: U32) -> IO(Unit):
  do IO<Unit>:
    f : File <- IO.try(File, File.open("tests/strings/utf8.bin", "r"))
    n : U32 <- File.fold_text(~U32, ~count, 4000n, f, Utf8.Dec.new(), max, 0)
    IO.print(U32.show(n))

def main() -> IO(Unit):
  do IO<Unit>:
    run(1)
    run(3)
    run(4096)

#|15
#|15
#|15
