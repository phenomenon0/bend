# bendgrep: count the lines of $FILE that contain $NEEDLE, show the first 5.
#   FILE=app.log NEEDLE=ERROR ./bendgrep --gpu off
# The file is read once; every line is a zero-copy view into that one string.
import Base

# state: (lines seen, hits) and the first five hits, newest first
def keep(n: U32, +l: String, shown: List<&2, String>, room: Bool) ->
  List<&2, String>:
  match room:
    case False{}:
      shown
    case True{}:
      String.append(String.pad_start(U32.show(n), 9n, ' '),
        String.append(": ", l)) <> shown

def step(+n: U32, +hits: U32, shown: List<&2, String>, +l: String, hit: Bool) ->
  (U32 & U32) & List<&2, String>:
  match hit:
    case False{}:
      ((n, hits), shown)
    case True{}:
      ((n, U32.add(hits, 1)), keep(n, l, shown, U32.is_lt(hits, 5)))

def scan(ls: List<&2, String>, +needle: String,
  st: (U32 & U32) & List<&2, String>) -> (U32 & U32) & List<&2, String>:
  match ls:
    case Nil{}:
      st
    case Con{+l, t}:
      ((n, hits), shown) = st
      scan(t, needle,
        step(U32.add(n, 1), hits, shown, l, String.contains(l, needle)))

def report(st: (U32 & U32) & List<&2, String>, t0: Nat, +t1: Nat) -> IO(Unit):
  ((n, hits), shown) = st
  do IO<Unit>:
    IO.print(String.join(List.reverse(&2, String, shown), "\n"))
    IO.print(String.concat([U32.show(hits), " matching lines of ", U32.show(n)]))
    t2 : Nat <- IO.now()
    IO.print_err(String.concat(["read ", Nat.show(Nat.sub(t1, t0)),
      " ms, search ", Nat.show(Nat.sub(t2, t1)), " ms"]))

def search(read: File & Result<&1, &1, U32 & String, String>, +needle: String,
  t0: Nat) -> IO(Unit):
  (f, result) = read
  do IO<Unit>:
    s : String <- IO.pass(String, result)
    File.close(f)
    t1 : Nat <- IO.now()
    report(scan(String.splitlines(s), needle, ((0, 0), [])), t0, t1)

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("FILE"))
    needle : String <- IO.try(String, IO.get_env("NEEDLE"))
    t0 : Nat <- IO.now()
    f : File <- IO.try(File, File.open(path, "r"))
    read : File & Result<&1, &1, U32 & String, String> <- File.read(f, 2147483647)
    search(read, needle, t0)
