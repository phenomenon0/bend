# slurp: a whole file as Base's Bytes(), 1 MiB reads through File.read_buf,
# each appended in place (the buffer has one owner). A file of little-endian
# F32s is then its words, four bytes apiece (Bytes.word_le).
import Base

def chunk(k: File -> Bytes() -> IO(Bytes()),
  got: File & Result<&1, &1, U32 & String, Bytes()>) -> IO(Bytes()):
  (h, r) = got
  IO.bind(Bytes(), Bytes(), IO.pass(Bytes(), r), k(h))

def choose(-A: Type, b: Bool, yes: Unit -> A, no: Unit -> A) -> A:
  match b:
    case True{}:
      yes(Unit{})
    case False{}:
      no(Unit{})

def finish(acc: Bytes(), h: File) -> IO(Bytes()):
  do IO<Bytes()>:
    File.close(h)
    return acc

def slurp(fuel: Nat, f: File, acc: Bytes()) -> IO(Bytes()):
  match fuel:
    case 0n:
      do IO<Bytes()>:
        File.close(f)
        IO.die(Bytes(), 1, "file past 4 GiB")
    case 1n++q:
      IO.bind(File & Result<&1, &1, U32 & String, Bytes()>, Bytes(),
        File.read_buf(f, 1048576), chunk(h => got =>
          +xs = got
          choose(Bytes() -> File -> IO(Bytes()), Nat.is_eq(Bytes.len(xs), 0n),
            u => a => g => finish(a, g), u => a => g => slurp(q, g, Bytes.append(a, xs)))(acc)(h)))

def load(path: String) -> IO(Bytes()):
  do IO<Bytes()>:
    f : File <- IO.try(File, File.open(path, "r"))
    slurp(4096n, f, "")
