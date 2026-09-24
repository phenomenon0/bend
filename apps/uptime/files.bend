# Files: a whole file read (the config), and the two NDJSON logs replayed
# into the store at start, a MiB at a time, a line at a time.
#
#   <state>.monitors.ndjson   {"op":"add",...spec} and {"op":"del","name":..}
#   <state>.results.ndjson    one probe a line (model.probe.line)
import Base
import ../../net/json.bend as Json
import ../../power/json_value.bend as J
import ./model.bend as M

def chunk() -> U32:
  1048576

# Whole files
# -----------

def slurp.more(empty: Bool, f: File, +b: Bytes(), acc: List<&2, Bytes()>,
  again: File -> List<&2, Bytes()> -> IO(Bytes())) -> IO(Bytes()):
  match empty:
    case True{}:
      IO.bind(Unit, Bytes(), File.close(f), u => IO.pure(Bytes(), Bytes.concat(List.reverse(&2, Bytes(), acc))))
    case False{}:
      again(f, Con{b, acc})

def slurp.got(g: File & Result<&1, &1, U32 & String, Bytes()>, acc: List<&2, Bytes()>,
  again: File -> List<&2, Bytes()> -> IO(Bytes())) -> IO(Bytes()):
  (f, r) = g
  match r:
    case Fail{(code, msg)}:
      IO.bind(Unit, Bytes(), File.close(f), u => IO.die(Bytes(), 1, "uptime: a read failed: " ++ msg))
    case Done{+b}:
      slurp.more(String.is_empty(b), f, b, acc, again)

def slurp.go(fuel: Nat, f: File, acc: List<&2, Bytes()>) -> IO(Bytes()):
  match fuel:
    case 0n:
      IO.bind(Unit, Bytes(), File.close(f), u => IO.pure(Bytes(), Bytes.concat(List.reverse(&2, Bytes(), acc))))
    case 1n+k:
      IO.bind(File & Result<&1, &1, U32 & String, Bytes()>, Bytes(), File.read_buf(f, chunk()),
        g => slurp.got(g, acc, ff => a => slurp.go(k, ff, a)))

def slurp.opened(+path: Bytes(), r: Result<&1, &1, U32 & String, File>) -> IO(Maybe<&2, Bytes()>):
  match r:
    case Done{f}:
      IO.bind(Bytes(), Maybe<&2, Bytes()>, slurp.go(4096n, f, []), b => IO.pure(Maybe<&2, Bytes()>, Some{b}))
    case Fail{e}:
      IO.pure(Maybe<&2, Bytes()>, None{})

# a file's bytes (at most 4 GiB), or None when it cannot be opened
def slurp(+path: Bytes()) -> IO(Maybe<&2, Bytes()>):
  IO.bind(Result<&1, &1, U32 & String, File>, Maybe<&2, Bytes()>, File.open(path, "r"), r => slurp.opened(path, r))

# The logs, replayed
# ------------------

def parse.line(+line: Bytes()) -> Result<&2, &2, J.Why, J.Json>:
  Json.parse(line, U32.from_nat(Nat.add(Bytes.len(line), 16n)))

def results.apply.pr(st: M.Store, np: Bytes() & M.Probe) -> M.Store:
  (+name, +p) = np
  Pair.fst(M.Store, U32, M.record(st, name, p))

# a results line: the probe put on its monitor (none there: ignored)
def results.apply.at(st: M.Store, r: Result<&2, &2, J.Why, J.Json>) -> M.Store:
  match r:
    case Done{+j}:
      results.apply.pr(st, M.probe.of(j))
    case Fail{w}:
      st

def ops.add(+st: M.Store, +c: M.Checked) -> M.Store:
  Bool.pick(M.Store, List.is_empty(&2, Bytes(), M.checked.errs(c)), Pair.fst(M.Store, Maybe<&2, U32>, M.add(st, M.checked.spec(c))), st)

def ops.apply.op(+st: M.Store, +j: J.Json, +op: Bytes()) -> M.Store:
  Bool.pick(M.Store, String.eq(op, "add"), ops.add(st, M.check(j)),
    Bool.pick(M.Store, String.eq(op, "del"),
      Pair.fst(M.Store, Bool, M.del(st, Maybe.default(&2, Bytes(), Json.get.str(j, "name"), ""))), st))

# an ops line: a monitor added (when its spec passes) or deleted
def ops.apply.at(st: M.Store, r: Result<&2, &2, J.Why, J.Json>) -> M.Store:
  match r:
    case Done{+j}:
      ops.apply.op(st, j, Maybe.default(&2, Bytes(), Json.get.str(j, "op"), ""))
    case Fail{w}:
      st

# the choice is a match: Bool.pick once evaluated both arms, and parsed
# every line twice (FRICTION.md 1; lazy since, and as fast)
def apply.kind(results: Bool, st: M.Store, +line: Bytes()) -> M.Store:
  match results:
    case True{}:
      results.apply.at(st, parse.line(line))
    case False{}:
      ops.apply.at(st, parse.line(line))

def apply.some(empty: Bool, +kind: U32, st: M.Store, +line: Bytes()) -> M.Store:
  match empty:
    case True{}:
      st
    case False{}:
      apply.kind(U32.is_eq(kind, 0), st, line)

def apply.line(+kind: U32, st: M.Store, +line: Bytes()) -> M.Store:
  apply.some(String.is_empty(line), kind, st, line)

# every line but the last applied; the last (cut by the chunk) handed back
def feed(xs: List<&2, Bytes()>, +kind: U32, st: M.Store, prev: Bytes()) -> M.Store & Bytes():
  match xs:
    case Nil{}:
      (st, prev)
    case Con{x, t}:
      feed(t, kind, apply.line(kind, st, prev), x)

def feed.chunk(+kind: U32, xs: List<&2, Bytes()>, st: M.Store) -> M.Store & Bytes():
  match xs:
    case Nil{}:
      (st, "")
    case Con{x, t}:
      feed(t, kind, st, x)

def replay.more(empty: Bool, +kind: U32, f: File, +b: Bytes(), sc: M.Store & Bytes(),
  again: File -> M.Store & Bytes() -> IO(M.Store)) -> IO(M.Store):
  match empty:
    case True{}:
      (st, carry) = sc
      IO.bind(Unit, M.Store, File.close(f), u => IO.pure(M.Store, apply.line(kind, st, carry)))
    case False{}:
      (st, carry) = sc
      again(f, feed.chunk(kind, String.split_on(Bytes.append(carry, b), "\n"), st))

def replay.got(+kind: U32, g: File & Result<&1, &1, U32 & String, Bytes()>, sc: M.Store & Bytes(),
  again: File -> M.Store & Bytes() -> IO(M.Store)) -> IO(M.Store):
  (f, r) = g
  match r:
    case Fail{(code, msg)}:
      IO.bind(Unit, M.Store, File.close(f), u => IO.die(M.Store, 1, "uptime: a read failed: " ++ msg))
    case Done{+b}:
      replay.more(String.is_empty(b), kind, f, b, sc, again)

def replay.go(fuel: Nat, +kind: U32, f: File, sc: M.Store & Bytes()) -> IO(M.Store):
  match fuel:
    case 0n:
      IO.bind(Unit, M.Store, File.close(f), u => IO.pure(M.Store, Pair.fst(M.Store, Bytes(), sc)))
    case 1n+k:
      IO.bind(File & Result<&1, &1, U32 & String, Bytes()>, M.Store, File.read_buf(f, chunk()),
        g => replay.got(kind, g, sc, ff => s => replay.go(k, kind, ff, s)))

def replay.opened(+kind: U32, st: M.Store, r: Result<&1, &1, U32 & String, File>) -> IO(M.Store):
  match r:
    case Done{f}:
      replay.go(65536n, kind, f, (st, ""))
    case Fail{e}:
      IO.pure(M.Store, st)

# the store after a log's lines (kind 0: results, 1: ops); a missing log
# is an empty one
def replay(+kind: U32, +path: Bytes(), st: M.Store) -> IO(M.Store):
  IO.bind(Result<&1, &1, U32 & String, File>, M.Store, File.open(path, "r"), r => replay.opened(kind, st, r))

def opened(+path: Bytes(), r: Result<&1, &1, U32 & String, File>) -> IO(File):
  match r:
    case Done{f}:
      IO.pure(File, f)
    case Fail{(code, msg)}:
      IO.die(File, 1, "uptime: cannot open " ++ path ++ ": " ++ msg)

# a log opened to append (made when missing)
def appending(+path: Bytes()) -> IO(File):
  IO.bind(Result<&1, &1, U32 & String, File>, File, File.open(path, "a"), r => opened(path, r))
