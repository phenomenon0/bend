# topwords: word report for $FILE: total words, unique words, the top 20.
#   FILE=book.txt ./topwords --gpu off
# to_lower -> strip ".," -> lines -> words -> count in a Map -> sort by count.
import Base

def bump(r: Map<&2, U32> & U32, w: String, by: U32) -> Map<&2, U32>:
  (m, c) = r
  Map.set(&2, U32, m, w, U32.add(c, by))

def count(ws: List<&2, String>, n: U32, m: Map<&2, U32>) -> U32 & Map<&2, U32>:
  match ws:
    case Nil{}:
      (n, m)
    case Con{+w, t}:
      count(t, U32.add(n, 1), bump(Map.get(U32, 0, m, w), w, 1))

# One line's words at a time: a view holds a count on the string it reads,
# and the runtime's counts are 24-bit, so 16.7M live views is the ceiling.
def each(ls: List<&2, String>, r: U32 & Map<&2, U32>) -> U32 & Map<&2, U32>:
  match ls:
    case Nil{}:
      r
    case l <> t:
      (n, m) = r
      each(t, count(String.words(l), n, m))

# Fork-join over every core: deal the lines into two piles, count both in
# parallel, then add the right pile's counts into the left map.
def pile(ls: List<&2, String>, mine: Bool) -> List<&2, String>:
  match ls mine:
    case Nil{} _:
      []
    case l <> t True{}:
      l <> pile(t, False{})
    case l <> t False{}:
      pile(t, True{})

def add(kvs: List<&2, Sigma<&2, &2, String, _ => U32>>, m: Map<&2, U32>) ->
  Map<&2, U32>:
  match kvs:
    case Nil{}:
      m
    case (+k, v) <> t:
      add(t, bump(Map.get(U32, 0, m, k), k, v))

def merge(x: U32 & Map<&2, U32>, y: U32 & Map<&2, U32>) -> U32 & Map<&2, U32>:
  (nx, mx) = x
  (ny, my) = y
  (U32.add(nx, ny), add(Map.to_list(&2, U32, my), mx))

def fork(+depth: Nat, +ls: List<&2, String>) -> U32 & Map<&2, U32>:
  match depth:
    case 0n:
      each(ls, (0, Map.new(&2, U32)))
    case 1n+d:
      x y = fork(d, pile(ls, True{})) fork(d, pile(ls, False{}))
      merge(x, y)

# most frequent first; ties in alphabetical order
def before(a: Sigma<&2, &2, String, _ => U32>,
  b: Sigma<&2, &2, String, _ => U32>) -> Bool:
  (+ka, +na) = a
  (+kb, +nb) = b
  U32.is_gt(na, nb) || (U32.is_eq(na, nb) && String.is_le(ka, kb))

def rows(xs: List<&2, Sigma<&2, &2, String, _ => U32>>, +rank: U32) ->
  List<&2, String>:
  match xs:
    case Nil{}:
      []
    case (k, v) <> t:
      String.concat([String.pad_start(U32.show(rank), 2n, ' '), ". ",
        String.pad_end(k, 16n, ' '), String.pad_start(U32.show(v), 10n, ' ')])
        <> rows(t, U32.add(rank, 1))

def report(r: U32 & Map<&2, U32>, t0: Nat, +t1: Nat) -> IO(Unit):
  (n, +m) = r
  do IO<Unit>:
    IO.print(String.append("total words:  ", U32.show(n)))
    IO.print(String.append("unique words: ", Nat.show(Map.size(&2, U32, m))))
    IO.print(String.join(rows(List.take(&2, Sigma<&2, &2, String, _ => U32>,
      List.sort(~(Sigma<&2, &2, String, _ => U32>), ~before, Map.to_list(&2, U32, m)), 20n), 1), "\n"))
    t2 : Nat <- IO.now()
    IO.print_err(String.concat(["read ", Nat.show(Nat.sub(t1, t0)),
      " ms, count+rank ", Nat.show(Nat.sub(t2, t1)), " ms"]))

def clean(s: String) -> String:
  String.replace(String.replace(String.to_lower(s), ".", " "), ",", " ")

def run(read: File & Result<&1, &1, U32 & String, String>, t0: Nat) -> IO(Unit):
  (f, result) = read
  do IO<Unit>:
    s : String <- IO.pass(String, result)
    File.close(f)
    t1 : Nat <- IO.now()
    report(fork(9n, String.lines(clean(s))), t0, t1)

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("FILE"))
    t0 : Nat <- IO.now()
    f : File <- IO.try(File, File.open(path, "r"))
    read : File & Result<&1, &1, U32 & String, String> <- File.read(f, 2147483647)
    run(read, t0)
