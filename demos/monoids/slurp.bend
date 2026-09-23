# slurp: a whole file into power/bytes.bend's Bytes, 64 KiB at a time, four
# bytes packed to a cell (little end first) -- so a file of little-endian U32s
# or F32s arrives as exactly those words, one to a cell. A partial last cell
# is carried open across chunk edges and pushed once, at the end.
import Base
import ../../power/vec.bend as Vec
import ../../power/bytes.bend as Bytes

# the buffer being filled: n bytes so far, w the open cell's word (n % 4 of it)
type In is Type:
  In{n: U32, w: U32, v: Vec.Vec}

def put(full: Bool, +n: U32, +w: U32, v: Vec.Vec) -> In:
  match full:
    case True{}:
      In{U32.inc(n), 0, Vec.push(v, w)}
    case False{}:
      In{U32.inc(n), w, v}

def pack(xs: List<&2, U32>, i: In) -> In:
  match xs:
    case Nil{}:
      i
    case Con{+x, t}:
      match i:
        case In{+n, +w, v}:
          pack(t, put(U32.is_eq(U32.and(n, 3), 3), n,
            U32.or(w, U32.shln(x, U32.to_nat(U32.shln(U32.and(n, 3), 3n)))), v))

def close.if(open: Bool, +n: U32, +w: U32, v: Vec.Vec) -> Bytes.Bytes:
  match open:
    case True{}:
      Bytes.Bytes{n, Vec.push(v, w)}
    case False{}:
      Bytes.Bytes{n, v}

def close(i: In) -> Bytes.Bytes:
  match i:
    case In{+n, +w, v}:
      close.if(U32.is_ne(U32.and(n, 3), 0), n, w, v)

def chunk(k: File -> List<&2, U32> -> IO(Bytes.Bytes),
  got: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(Bytes.Bytes):
  (h, r) = got
  IO.bind(List<&2, U32>, Bytes.Bytes, IO.pass(List<&2, U32>, r), k(h))

def choose(-A: Type, b: Bool, yes: Unit -> A, no: Unit -> A) -> A:
  match b:
    case True{}:
      yes(Unit{})
    case False{}:
      no(Unit{})

def finish(i: In, h: File) -> IO(Bytes.Bytes):
  do IO<Bytes.Bytes>:
    File.close(h)
    return close(i)

def slurp(fuel: Nat, f: File, i: In) -> IO(Bytes.Bytes):
  match fuel:
    case 0n:
      do IO<Bytes.Bytes>:
        File.close(f)
        IO.die(Bytes.Bytes, 1, "file past 4 GiB")
    case 1n++q:
      IO.bind(File & Result<&1, &1, U32 & String, List<&2, U32>>, Bytes.Bytes,
        File.read_bytes(f, 65536), chunk(h => bs =>
          +xs = bs
          choose(In -> File -> IO(Bytes.Bytes), List.is_empty(&2, U32, xs),
            u => j => g => finish(j, g), u => j => g => slurp(q, g, pack(xs, j)))(i)(h)))

def load(path: String) -> IO(Bytes.Bytes):
  do IO<Bytes.Bytes>:
    f : File <- IO.try(File, File.open(path, "r"))
    slurp(65536n, f, In{0, 0, Vec.new(0)})

