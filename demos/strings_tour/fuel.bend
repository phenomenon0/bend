# The fuel gauge. Line 2 of gen_log.py's log is ReDoS bait: `bait aaaa...a!`.
# Only the first 64 KiB of $FILE are read. `^(a+)+$` is the classic
# catastrophic pattern; here it is one linear search whose cost is known
# before it runs: weight x (length + 1). `a.*b|a` rescans, so its cost is
# quadratic: the budget runs out and the call says so, where, and gives no
# partial answer. Every global regex call takes its budget as an argument.
#   FILE=hostile.log ./fuel --gpu off
import Base
import ../text/slices.bend as Slices

def bait(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      ""
    case +l <> t:
      Bool.pick(String, String.starts_with(l, "bait "), String.drop(l, 5n), bait(t))

def spent(r: Result<&2, &2, Regex.Error, Regex.scan.Out()>) -> String:
  match r:
    case Fail{RErr{at, msg}}:
      String.concat([msg, " at code point ", Nat.show(at)])
    case Done{(left, ms)}:
      String.concat([Nat.show(List.length(&2, Match, ms)), " matches, spent ",
        U32.show(U32.sub(4294967295, left)), " units"])

def found(r: Result<&2, &2, Regex.Error, List<&2, Match>>) -> String:
  match r:
    case Fail{RErr{at, msg}}:
      String.concat([msg, " at code point ", Nat.show(at), ", no partial answer"])
    case Done{ms}:
      String.append(Nat.show(List.length(&2, Match, ms)), " matches")

def linear(r: Result<&2, &2, Regex.Error, Regex>, s: String) -> String:
  match r:
    case Fail{RErr{at, msg}}:
      msg
    case Done{+re}:
      String.concat([spent(Regex.scan(re, s, 4294967295)), " = weight ",
        U32.show(Regex.weight(re)), " x (length + 1)"])

def rescan(r: Result<&2, &2, Regex.Error, Regex>, s: String) -> String:
  match r:
    case Fail{RErr{at, msg}}:
      msg
    case Done{re}:
      found(Regex.find_all(re, s, 1000000))

def run(read: File & Result<&1, &1, U32 & String, String>) -> IO(Unit):
  (f, result) = read
  do IO<Unit>:
    s : String <- IO.pass(String, result)
    File.close(f)
    +line : String = bait(String.splitlines(s))
    IO.print(Slices.row("bait line", String.append(Nat.show(String.length(line)), " code points")))
    t0 : Nat <- IO.now()
    IO.print(Slices.row("^(a+)+$", linear(Regex.compile("^(a+)+$", ""), line)))
    +t1 : Nat <- IO.now()
    IO.print(Slices.row("a.*b|a  budget 1000000", rescan(Regex.compile("a.*b|a", ""), line)))
    t2 : Nat <- IO.now()
    IO.print_err(String.concat(["^(a+)+$ ", Nat.show(Nat.sub(t1, t0)), " ms | a.*b|a to the budget error ",
      Nat.show(Nat.sub(t2, t1)), " ms"]))

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("FILE"))
    f : File <- IO.try(File, File.open(path, "r"))
    read : File & Result<&1, &1, U32 & String, String> <- File.read(f, 65536)
    run(read)
