# std's json bench: a file read whole, parsed into a tree by JsonValue.parse,
# then walked. For a top-level array it prints the item count, how many items
# have a "type" of "PushEvent", and the "login" under the first item's
# "actor" (the shape of GitHub's event archive, json-iterator's large-file.json);
# run.py holds the line to CPython's json and times the lanes.
#   bend tests/std/bench/json_read.bend -o jr && ./jr FILE
import Base
import ../../../std/bytes.bend as By
import ../../../std/json_value.bend as JV

def path(args: List<String>) -> String:
  match args:
    case Nil{}:
      "/tmp/bend-json-bench.json"
    case Con{p, t}:
      p

def is_push.at(m: Maybe<&2, JV.Json>) -> Bool:
  match m:
    case Some{v}:
      JV.eq(v, JV.Str{"PushEvent"})
    case None{}:
      False{}

def is_push(j: JV.Json) -> Bool:
  is_push.at(JV.get(j, "type"))

def count(xs: List<&2, JV.Json>, +n: U32, +k: U32) -> U32 & U32:
  match xs:
    case Nil{}:
      (n, k)
    case Con{x, t}:
      count(t, U32.inc(n), Bool.pick(U32, is_push(x), U32.inc(k), k))

def login(m: Maybe<&2, JV.Json>) -> String:
  match m:
    case Some{v}:
      JV.show(v)
    case None{}:
      "-"

def first(xs: List<&2, JV.Json>) -> String:
  match xs:
    case Nil{}:
      "-"
    case Con{x, t}:
      login(JV.path(x, ["actor", "login"]))

def report.at(r: U32 & U32, s: String) -> String:
  (n, k) = r
  U32.show(n) ++ " items, " ++ U32.show(k) ++ " PushEvent, first login " ++ s

def report(+xs: List<&2, JV.Json>) -> String:
  report.at(count(xs, 0, 0), first(xs))

def arr(m: Maybe<&2, List<&2, JV.Json>>) -> String:
  match m:
    case Some{+xs}:
      report(xs)
    case None{}:
      "not an array"

def tree(r: JV.Out()) -> String:
  match r:
    case Fail{w}:
      "refused"
    case Done{j}:
      arr(JV.items(j))

def parse(+b: String) -> String:
  tree(JV.parse(b, JV.lim(U32.from_nat(By.len(b)))))

def got(r: Result<&1, &1, U32 & String, String>) -> String:
  match r:
    case Fail{e}:
      "no file"
    case Done{+b}:
      parse(b)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    r : Result<&1, &1, U32 & String, String> <- By.read_file(path(args))
    IO.print(got(r))
