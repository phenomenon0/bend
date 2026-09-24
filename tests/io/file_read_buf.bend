# io (io_file_read_buf): File.read_buf answers a file's bytes as one
# Bytes, where File.read_bytes answers a List cell per byte. "Olá\n" is
# written as text (the á is C3 A1 on disk) and read back whole and
# capped at 3 bytes: the bytes are the ones on disk, not decoded text.
import Base

def path() -> String:
  "/tmp/bend_io_file_read_buf"

def line(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      ""
    case [x]:
      U32.show(x)
    case x <> rest:
      U32.show(x) ++ " " ++ line(rest)

law write_go:
  for w: File & Result<&1, &1, (U32 & String), Unit>
  IO(Unit)

def write_go(w):
  (f, r) = w
  do IO<Unit>:
    u : Unit <- IO.pass(Unit, r)
    File.close(f)

law read_go:
  for m: File & Result<&1, &1, (U32 & String), Bytes()>
  IO(Unit)

def read_go(m):
  (f, r) = m
  do IO<Unit>:
    +b : Bytes() <- IO.pass(Bytes(), r)
    p  : Unit <- IO.print(Nat.show(Bytes.len(b)) ++ ": " ++ line(Bytes.to_list(b)))
    File.close(f)

law read_max:
  for max: U32
  IO(Unit)

def read_max(max):
  do IO<Unit>:
    g : File <- IO.try(File, File.open(path(), "r"))
    m : File & Result<&1, &1, (U32 & String), Bytes()> <- File.read_buf(g, max)
    read_go(m)

law main:
  IO(U32)

def main():
  do IO<U32>:
    f : File <- IO.try(File, File.open(path(), "w"))
    w : File & Result<&1, &1, (U32 & String), Unit> <- File.write(f, "Olá\n")
    x : Unit <- write_go(w)
    y : Unit <- read_max(64)
    z : Unit <- read_max(3)
    return 0

#|5: 79 108 195 161 10
#|3: 79 108 195
