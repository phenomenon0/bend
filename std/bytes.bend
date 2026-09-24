# Bytes: the one byte interface std/ is written against.
#
# A byte string is a String whose every Char is below 256. What reads it
# fast differs between runtimes, so the interface has two
# implementations and this file picks one with its import line:
#
#   bytes_list.bend    plain Bend over canon's Base: runs on released Bend
#                      and on this repo's runtime alike (the default)
#   bytes_packed.bend  this repo's packed Bytes natives: a byte a cell,
#                      views, memchr scans; needs this repo's Base
#
# Bend has no conditional compilation, and an import names a file, so
# the switch is the line below. Everything in std/ imports this file and
# nothing else of the two, so changing that one line moves all of std/.
# bytes_spec.bend says what the scans count; both implementations prove
# their .is laws against it, and every law in std/ is stated over these
# names, so a proof checks whichever file the line names.
import Base
import ./bytes_list.bend as Impl
import ./bytes_spec.bend as Sp

# Byte strings
# ============

# the byte at i; past the end, 256, which no byte is
def get(+b: String, +i: Nat) -> U32:
  Impl.get(b, i)

def len(+b: String) -> Nat:
  Impl.len(b)

def from_list(xs: List<&2, U32>) -> String:
  Impl.from_list(xs)

def to_list(b: String) -> List<&2, U32>:
  Impl.to_list(b)

# b with the byte x on its end
def push(b: String, x: U32) -> String:
  Impl.push(b, x)

# the first n bytes and the rest: (String.take(s, n), String.drop(s, n))
def cut(+s: String, +n: Nat) -> String & String:
  Impl.cut(s, n)

# n bytes from at, clamped to the end
def slice(b: String, +at: Nat, n: Nat) -> String:
  Impl.slice(b, at, n)

# the first offset of p in b; the empty p is found at 0
def find(+b: String, +p: String) -> Maybe<&2, Nat>:
  Impl.find(b, p)

# the first offset of the byte x at or after i; absent, the end
def find_byte(+b: String, +i: Nat, x: U32) -> Nat:
  Impl.find_byte(b, i, x)

# the first offset at or after i of any of w, x, y, z (name one twice for
# fewer); absent, the end
def find_any(+b: String, +i: Nat, w: U32, x: U32, y: U32, z: U32) -> Nat:
  Impl.find_any(b, i, w, x, y, z)

# how many bytes from i are in [lo, hi)
def span(+b: String, +i: Nat, lo: U32, hi: U32) -> Nat:
  Impl.span(b, i, lo, hi)

# the four bytes from i as one U32, little end first, a byte past the end 0
def word_le(+b: String, +i: Nat) -> U32:
  Impl.word_le(b, i)

# the one-byte string
def one(x: U32) -> String:
  SCon{Chr{x}, SNil{}}

# The laws
# --------

def list(xs: List<&2, U32>) -> {to_list(from_list(xs)) == xs : List<&2, U32>}:
  Impl.list(xs)

def to_list_append(+a: String, +b: String) ->
  {to_list(String.append(a, b)) == List.append(&2, U32, to_list(a), to_list(b)) : List<&2, U32>}:
  Impl.to_list_append(a, b)

def push_list(+b: String, +x: U32) ->
  {to_list(push(b, x)) == List.append(&2, U32, to_list(b), Con{x, Nil{}}) : List<&2, U32>}:
  Impl.push_list(b, x)

def find_byte.is(+b: String, +i: Nat, +x: U32) ->
  {find_byte(b, i, x) == Nat.add(i, Sp.find_byte.go(String.drop(b, i), x)) : Nat}:
  Impl.find_byte.is(b, i, x)

def find_any.is(+b: String, +i: Nat, +w: U32, +x: U32, +y: U32, +z: U32) ->
  {find_any(b, i, w, x, y, z) == Nat.add(i, Sp.find_any.go(String.drop(b, i), w, x, y, z)) : Nat}:
  Impl.find_any.is(b, i, w, x, y, z)

# The reader
# ==========
#
# Random access for a scanner: open a byte string, read the byte at any
# offset, take a span out as a string of its own. Every read hands the
# reader back. On a packed buffer a read is a load; on the list, the
# reader is a cursor and a scan that reads forward pays a cell a byte.

def Buf() -> Data:
  Impl.Buf()

def open(s: String) -> Buf():
  Impl.open(s)

# the byte string it reads
def bytes(b: Buf()) -> String:
  Impl.bytes(b)

def size(b: Buf()) -> Buf() & U32:
  Impl.size(b)

# the byte at i, 0 past the end
def at(b: Buf(), +i: U32) -> Buf() & U32:
  Impl.at(b, i)

# the n bytes from at
def take(b: Buf(), +at: U32, +n: U32) -> Buf() & String:
  Impl.take(b, at, n)

# Files
# =====

# up to max bytes of an open file; the empty string at its end
def read_chunk(file: File, max: U32) -> IO(File & Result<&1, &1, U32 & String, String>):
  Impl.read_chunk(file, max)

# the read size a file loop should ask for
def chunk_size() -> U32:
  Impl.chunk_size()

# the bytes as they are, none re-encoded
def write(file: File, data: String) -> IO(File & Result<&1, &1, U32 & String, Unit>):
  Impl.write(file, data)

# The writer
# ==========
#
# A string built a piece at a time, in time linear in what it holds on
# either implementation: new, then add a string or push a byte, then done.
def Out() -> Data:
  Impl.Out()

def out.new() -> Out():
  Impl.out.new()

def out.add(o: Out(), s: String) -> Out():
  Impl.out.add(o, s)

def out.push(o: Out(), x: U32) -> Out():
  Impl.out.push(o, x)

def out.done(o: Out()) -> String:
  Impl.out.done(o)

# Whole files
# ===========

type Rd is Type:
  RMore{f: File, o: Out()}
  RStop{f: File, r: Result<&1, &1, U32 & String, String>}

def rd.at(z: Bool, f: File, b: String, o: Out()) -> Rd:
  match z:
    case True{}:
      RStop{f, Done{out.done(o)}}
    case False{}:
      RMore{f, out.add(o, b)}

def rd.plan(o: Out(), got: File & Result<&1, &1, U32 & String, String>) -> Rd:
  (f, r) = got
  match r:
    case Fail{e}:
      RStop{f, Fail{e}}
    case Done{+b}:
      rd.at(String.is_empty(b), f, b, o)

def rd.loop(fuel: Nat, +max: U32, st: Rd) -> IO(File & Result<&1, &1, U32 & String, String>):
  match fuel:
    case 0n:
      match st:
        case RMore{f, o}:
          IO.pure(File & Result<&1, &1, U32 & String, String>, (f, Done{out.done(o)}))
        case RStop{f, r}:
          IO.pure(File & Result<&1, &1, U32 & String, String>, (f, r))
    case 1n+n:
      match st:
        case RStop{f, r}:
          IO.pure(File & Result<&1, &1, U32 & String, String>, (f, r))
        case RMore{f, o}:
          IO.bind(File & Result<&1, &1, U32 & String, String>, File & Result<&1, &1, U32 & String, String>,
            read_chunk(f, max), got => rd.loop(n, max, rd.plan(o, got)))

def rd.close(x: File & Result<&1, &1, U32 & String, String>) -> IO(Result<&1, &1, U32 & String, String>):
  (f, r) = x
  do IO<Result<&1, &1, U32 & String, String>>:
    File.close(f)
    return r

def rd.open(r: Result<&1, &1, U32 & String, File>) -> IO(Result<&1, &1, U32 & String, String>):
  match r:
    case Fail{e}:
      IO.pure(Result<&1, &1, U32 & String, String>, Fail{e})
    case Done{f}:
      IO.bind(File & Result<&1, &1, U32 & String, String>, Result<&1, &1, U32 & String, String>,
        rd.loop(U32.to_nat(4294967295), chunk_size(), RMore{f, out.new()}), rd.close)

# the file at path, every byte of it, or the error the file system gave
def read_file(path: String) -> IO(Result<&1, &1, U32 & String, String>):
  IO.bind(Result<&1, &1, U32 & String, File>, Result<&1, &1, U32 & String, String>,
    File.open(path, "r"), rd.open)

def wr.close(x: File & Result<&1, &1, U32 & String, Unit>) -> IO(Result<&1, &1, U32 & String, Unit>):
  (f, r) = x
  do IO<Result<&1, &1, U32 & String, Unit>>:
    File.close(f)
    return r

def wr.open(data: String, r: Result<&1, &1, U32 & String, File>) -> IO(Result<&1, &1, U32 & String, Unit>):
  match r:
    case Fail{e}:
      IO.pure(Result<&1, &1, U32 & String, Unit>, Fail{e})
    case Done{f}:
      IO.bind(File & Result<&1, &1, U32 & String, Unit>, Result<&1, &1, U32 & String, Unit>,
        write(f, data), wr.close)

# the bytes as the whole of the file at path, made or emptied first
def write_file(path: String, data: String) -> IO(Result<&1, &1, U32 & String, Unit>):
  IO.bind(Result<&1, &1, U32 & String, File>, Result<&1, &1, U32 & String, Unit>,
    File.open(path, "w"), r => wr.open(data, r))
