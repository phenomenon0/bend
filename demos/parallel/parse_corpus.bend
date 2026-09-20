# Parse a corpus of Python files with demos/python's parser. The files are read
# once, in manifest order (IO, sequential); then the whole corpus is one
# fork/join tree. There is no thread code in this file.
#   PAR_MANIFEST=files.txt ./parse_corpus --threads 16
#   PAR_MODE=seq PAR_MANIFEST=files.txt ./parse_corpus   # same leaves, one by one
# Prints `status hash path` per file and a hash of all of them, in manifest
# order: every mode at every --threads must print the same bytes.
import Base
import ../python/syntax.bend as S
import ../python/intake.bend as I
import ../python/lexer.bend as L
import ../python/parser.bend as P

type Item is Data:
  Item{path: String, src: String}

# The leaf. One file: the status word and the FNV hash of its AST JSON, or of
# the error text when it does not parse.
def failed(e: S.Error) -> String:
  S.PErr{+k, pos, msg} = e
  S.kind(k) ++ " " ++ U32.show(String.hash(S.error_text(S.PErr{k, pos, msg})))

def parsed(r: Result<&2, &2, S.Error, S.Module>) -> String:
  match r:
    case Done{m}:
      "ok " ++ U32.show(String.hash(S.json(S.module(m))))
    case Fail{e}:
      failed(e)

def lexed(r: Result<&2, &2, S.Error, List<&2, S.Tok>>) -> String:
  match r:
    case Done{ts}:
      parsed(P.parse(ts))
    case Fail{e}:
      failed(e)

def one(file: Item) -> String:
  Item{path, src} = file
  lexed(L.lex(src)) ++ " " ++ path

# Sequential: the leaves one after another, left to right.
def seq(xs: List<&2, Item>) -> List<&2, String>:
  match xs:
    case Nil{}:
      []
    case f <> tail:
      one(f) <> seq(tail)

# Parallel: halve the corpus until one file is left. `a b = f(x) g(y)` is the
# whole parallel API. The halves are appended in order, so the output cannot
# depend on which thread finished first.
def par(d: Nat, +n: Nat, +xs: List<&2, Item>) -> List<&2, String>:
  match d:
    case 0n:
      seq(xs)
    case 1n++p:
      +half = Nat.div(n, 2n)
      a b = par(p, half, List.take(&2, Item, xs, half))
            par(p, Nat.sub(n, half), List.drop(&2, Item, xs, half))
      List.append(&2, String, a, b)

# floor(log2(n)) + 1, so the tree has at least one leaf per file (the knob's
# fuelled log2: every step runs, the fuel bounds them)
def log2(fuel: Nat, +n: Nat) -> Nat:
  match fuel:
    case 0n:
      0n
    case 1n+f:
      Bool.pick(Nat, Nat.is_lt(1n, n), 1n+log2(f, Nat.div(n, 2n)), 0n)

# match, not Bool.pick: only the chosen mode runs
def run(+n: Nat, xs: List<&2, Item>, one_thread: Bool) ->
  List<&2, String>:
  match one_thread:
    case True{}:
      seq(xs)
    case False{}:
      par(1n+log2(32n, n), n, xs)

# The clock stops after IO.print: printing the lines is what forces the parses,
# so t2 - t1 is the parse, not a thunk handed to the printer.
def report(pair: String & String, t0: Nat, +t1: Nat) -> IO(Unit):
  (out, keep) = pair
  do IO<Unit>:
    IO.print(out)
    t2 : Nat <- IO.now()
    IO.print("corpus " ++ U32.show(String.hash(keep)))
    IO.print_err(String.concat(["read ", Nat.show(Nat.sub(t1, t0)), " ms, parse ",
      Nat.show(Nat.sub(t2, t1)), " ms"]))

# Reading is IO, so it stays sequential: every file, in manifest order.
def slurp_done(path: String,
  r: File & Result<&1, &1, U32 & String, String>) -> IO(Item):
  (f, res) = r
  do IO<Item>:
    s : String <- IO.pass(String, res)
    File.close(f)
    IO.pure(Item, Item{path, I.strip_bom(s)})

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

def go(one_thread: Bool, got: List<&2, Item> & Nat, t0: Nat, t1: Nat) ->
  IO(Unit):
  (files, n) = got
  report(String.clone(String.join(run(n, files, one_thread), "\n")), t0, t1)

def start(one_thread: Bool, paths: List<&2, String>, t0: Nat) -> IO(Unit):
  do IO<Unit>:
    got : List<&2, Item> & Nat <- read_all(paths, [], 0n)
    t1 : Nat <- IO.now()
    go(one_thread, got, t0, t1)

def seq_mode(r: Result<&1, &1, U32 & String, String>) -> Bool:
  match r:
    case Done{s}:
      String.eq(s, "seq")
    case Fail{e}:
      False{}

def loaded(one_thread: Bool, t0: Nat,
  r: File & Result<&1, &1, U32 & String, String>) -> IO(Unit):
  (f, res) = r
  do IO<Unit>:
    s : String <- IO.pass(String, res)
    File.close(f)
    start(one_thread,
      List.filter(~String, ~(l => Bool.not(String.is_empty(l))),
        String.lines(s)), t0)

def main() -> IO(Unit):
  do IO<Unit>:
    manifest : String <- IO.try(String, IO.get_env("PAR_MANIFEST"))
    opt : Result<&1, &1, U32 & String, String> <- IO.get_env("PAR_MODE")
    t0 : Nat <- IO.now()
    f : File <- IO.try(File, File.open(manifest, "r"))
    r : File & Result<&1, &1, U32 & String, String> <- File.read(f, 2147483647)
    loaded(seq_mode(opt), t0, r)
