# Search a corpus for a literal needle: per file, the lines that contain it,
# counted as `grep -c` counts them. The files are read once, in manifest order
# (IO, sequential); then the whole corpus is one fork/join tree, the shape
# parse_corpus.bend uses. There is no thread code in this file.
#   PAR_MANIFEST=files.txt PAR_NEEDLE=import ./search_corpus --threads 16
#   PAR_MODE=seq PAR_MANIFEST=files.txt ./search_corpus  # same leaves, one by one
# Prints `count path` per file, then the total and a hash of it all: every mode
# at every --threads must print the same bytes.
import Base

type Item is Data:
  Item{path: String, src: String}

# count and lines travel together, so the total is the tree's, not the shell's
type Tally is Data:
  Tally{count: Nat, lines: List<&2, String>}

# The leaf. One file: its matching lines, counted.
def hits(ls: List<&2, String>, +needle: String, +n: Nat) -> Nat:
  match ls:
    case Nil{}:
      n
    case l <> tail:
      hits(tail, needle, Bool.pick(Nat, String.contains(l, needle), 1n+n, n))

def one(file: Item, +needle: String) -> Tally:
  Item{path, src} = file
  +n = hits(String.splitlines(src), needle, 0n)
  Tally{n, [Nat.show(n) ++ " " ++ path]}

def merge(a: Tally, b: Tally) -> Tally:
  Tally{an, als} = a
  Tally{bn, bls} = b
  Tally{Nat.add(an, bn), List.append(&2, String, als, bls)}

# Sequential: the leaves one after another, left to right.
def seq(xs: List<&2, Item>, +needle: String) -> Tally:
  match xs:
    case Nil{}:
      Tally{0n, []}
    case f <> tail:
      merge(one(f, needle), seq(tail, needle))

# Parallel: halve the corpus until one file is left. `a b = f(x) g(y)` is the
# whole parallel API. The halves merge in order, so neither the counts nor the
# lines can depend on which thread finished first.
def par(d: Nat, +n: Nat, +xs: List<&2, Item>, +needle: String) -> Tally:
  match d:
    case 0n:
      seq(xs, needle)
    case 1n++p:
      +half = Nat.div(n, 2n)
      a b = par(p, half, List.take(&2, Item, xs, half), needle)
            par(p, Nat.sub(n, half), List.drop(&2, Item, xs, half), needle)
      merge(a, b)

# floor(log2(n)) + 1, so the tree has at least one leaf per file (the knob's
# fuelled log2: every step runs, the fuel bounds them)
def log2(fuel: Nat, +n: Nat) -> Nat:
  match fuel:
    case 0n:
      0n
    case 1n+f:
      Bool.pick(Nat, Nat.is_lt(1n, n), 1n+log2(f, Nat.div(n, 2n)), 0n)

# match, not Bool.pick: only the chosen mode runs
def run(+n: Nat, xs: List<&2, Item>, +needle: String, one_thread: Bool) ->
  Tally:
  match one_thread:
    case True{}:
      seq(xs, needle)
    case False{}:
      par(1n+log2(32n, n), n, xs, needle)

# The clock stops after IO.print: printing is what forces the search, so
# t2 - t1 is the search and not a thunk handed to the printer.
def report(pair: String & String, t0: Nat, +t1: Nat) -> IO(Unit):
  (out, keep) = pair
  do IO<Unit>:
    IO.print(out)
    t2 : Nat <- IO.now()
    IO.print("corpus " ++ U32.show(String.hash(keep)))
    IO.print_err(String.concat(["read ", Nat.show(Nat.sub(t1, t0)), " ms, search ",
      Nat.show(Nat.sub(t2, t1)), " ms"]))

def text(t: Tally, +n: Nat) -> String:
  Tally{count, lines} = t
  String.join(lines, "\n") ++ String.concat(["\ntotal ", Nat.show(count),
    " matching lines in ", Nat.show(n), " files"])

# Reading is IO, so it stays sequential: every file, in manifest order.
def slurp_done(path: String,
  r: File & Result<&1, &1, U32 & String, String>) -> IO(Item):
  (f, res) = r
  do IO<Item>:
    s : String <- IO.pass(String, res)
    File.close(f)
    IO.pure(Item, Item{path, s})

def slurp_open(pair: String & String) -> IO(Item):
  (open, keep) = pair
  do IO<Item>:
    f : File <- IO.try(File, File.open(open, "r"))
    r : File & Result<&1, &1, U32 & String, String> <- File.read(f, 2147483647)
    slurp_done(keep, r)

def slurp(path: String) -> IO(Item):
  slurp_open(String.clone(path))

def read_all(paths: List<&2, String>, acc: List<&2, Item>, n: Nat) ->
  IO(List<&2, Item> & Nat):
  match paths:
    case Nil{}:
      IO.pure(List<&2, Item> & Nat, (List.reverse(&2, Item, acc), n))
    case p <> rest:
      IO.bind(Item, List<&2, Item> & Nat, slurp(p),
        it => read_all(rest, it <> acc, 1n+n))

def go(one_thread: Bool, needle: String, got: List<&2, Item> & Nat, t0: Nat,
  t1: Nat) -> IO(Unit):
  (files, +n) = got
  report(String.clone(text(run(n, files, needle, one_thread), n)), t0, t1)

def start(one_thread: Bool, needle: String, paths: List<&2, String>,
  t0: Nat) -> IO(Unit):
  do IO<Unit>:
    got : List<&2, Item> & Nat <- read_all(paths, [], 0n)
    t1 : Nat <- IO.now()
    go(one_thread, needle, got, t0, t1)

def seq_mode(r: Result<&1, &1, U32 & String, String>) -> Bool:
  match r:
    case Done{s}:
      String.eq(s, "seq")
    case Fail{e}:
      False{}

def loaded(one_thread: Bool, needle: String, t0: Nat,
  r: File & Result<&1, &1, U32 & String, String>) -> IO(Unit):
  (f, res) = r
  do IO<Unit>:
    s : String <- IO.pass(String, res)
    File.close(f)
    start(one_thread, needle,
      List.filter(~String, ~(l => Bool.not(String.is_empty(l))),
        String.lines(s)), t0)

def main() -> IO(Unit):
  do IO<Unit>:
    manifest : String <- IO.try(String, IO.get_env("PAR_MANIFEST"))
    needle : String <- IO.try(String, IO.get_env("PAR_NEEDLE"))
    opt : Result<&1, &1, U32 & String, String> <- IO.get_env("PAR_MODE")
    t0 : Nat <- IO.now()
    f : File <- IO.try(File, File.open(manifest, "r"))
    r : File & Result<&1, &1, U32 & String, String> <- File.read(f, 2147483647)
    loaded(seq_mode(opt), needle, t0, r)
