# The fuel gauge. Line 3 of gen_log.py's log rebuilds the line that took Stack
# Overflow down on July 20, 2016 (their comment, 20,000 spaces, one `x`), met
# by their trim regex; line 2 is the textbook ReDoS bait. Only the first
# 64 KiB of $FILE are read. Every global regex call takes its budget as an
# argument: a search from `at` must afford weight x (length + 1 - at) before
# it starts, then pays only the span it walked. A search that cannot afford
# that is an error saying where: never a partial answer, never a hang. A scan
# with matches is many searches: `a.*b|a` rescans, is quadratic, and runs dry.
#   FILE=hostile.log ./fuel --gpu off
import Base
import ../text/slices.bend as Slices

# fail loud: a log without the line is an error, never a scan of ""
def pick(ls: List<&2, String>, +pre: String) -> Result<&1, &1, U32 & String, String>:
  match ls:
    case Nil{}:
      Fail{(1, String.concat(["this log has no line starting \"", pre, "\": regenerate it"]))}
    case +l <> t:
      Bool.pick(Result<&1, &1, U32 & String, String>, String.starts_with(l, pre), Done{l}, pick(t, pre))

def must(r: Result<&2, &2, Regex.Error, Regex>) -> Result<&1, &1, U32 & String, Regex>:
  match r:
    case Fail{RErr{at, msg}}:
      Fail{(1, String.concat(["regex: ", msg, " at ", Nat.show(at)]))}
    case Done{re}:
      Done{re}

# 20 cells, rounded to nearest; U32-safe while tank <= 209,510,599
def gauge(+spent: U32, +tank: U32) -> String:
  +n = U32.to_nat(U32.div(U32.add(U32.mul(spent, 20), U32.div(tank, 2)), tank))
  String.concat(["▕", String.repeat("█", n), String.repeat("░", Nat.sub(20n, n)), "▏ ", U32.show(spent),
    " of ", U32.show(tank), " units"])

# n1 = length + 1: a search refused at `at` needed w x (n1 - at) up front
def paid(r: Result<&2, &2, Regex.Error, Regex.scan.Out()>, +tank: U32, w: U32, n1: Nat) -> String:
  match r:
    case Fail{RErr{+at, msg}}:
      String.concat(["refused: ", msg, " at code point ", Nat.show(at), ": needs ",
        U32.show(Regex.cost(U32.from_nat(Nat.sub(n1, at)), w))])
    case Done{(left, ms)}:
      String.concat([gauge(U32.sub(tank, left), tank), ", ", Nat.show(List.length(&2, Match, ms)), " matches"])

def shot(+re: Regex, +s: String, +tank: U32) -> String:
  paid(Regex.scan(re, s, tank), tank, Regex.weight(re), Nat.add(1n, String.length(s)))

# the line's first `skip` code points (the comment), k of its spaces, one `x`
def dose(re: Regex, line: String, skip: Nat, k: U32, tank: U32) -> String:
  shot(re, String.append(String.take(line, Nat.add(skip, U32.to_nat(k))), "x"), tank)

def found(r: Result<&2, &2, Regex.Error, List<&2, Match>>) -> String:
  match r:
    case Fail{RErr{at, msg}}:
      String.concat([msg, " at code point ", Nat.show(at), ", no partial answer"])
    case Done{ms}:
      String.append(Nat.show(List.length(&2, Match, ms)), " matches")

def ms(label: String, a: Nat, b: Nat) -> String:
  String.concat([label, " ", Nat.show(Nat.sub(b, a)), " ms"])

def run(read: File & Result<&1, &1, U32 & String, String>) -> IO(Unit):
  (f, result) = read
  do IO<Unit>:
    s : String <- IO.pass(String, result)
    File.close(f)
    +ls : List<&2, String> = String.splitlines(s)
    +head : String = "-- play happy sound for player to enjoy"
    +pat : String = "^[\\s\\u200c]+|[\\s\\u200c]+$"
    +so : String <- IO.pass(String, pick(ls, head))
    b : String <- IO.pass(String, pick(ls, "bait "))
    +bait : String = String.drop(b, 5n)
    +re : Regex <- IO.pass(Regex, must(Regex.compile(pat, "")))
    evil : Regex <- IO.pass(Regex, must(Regex.compile("^(a+)+$", "")))
    rescan : Regex <- IO.pass(Regex, must(Regex.compile("a.*b|a", "")))
    +skip : Nat = String.length(head)
    IO.print(Slices.row("Stack Overflow line", String.append(Nat.show(String.length(so)), " code points")))
    IO.print(Slices.row(pat, String.append("weight ", U32.show(Regex.weight(re)))))
    t0 : Nat <- IO.now()
    IO.print(Slices.row("5000 spaces", dose(re, so, skip, 5000, 2000000)))
    +t1 : Nat <- IO.now()
    IO.print(Slices.row("10000 spaces", dose(re, so, skip, 10000, 2000000)))
    +t2 : Nat <- IO.now()
    IO.print(Slices.row("20000 spaces", dose(re, so, skip, 20000, 2000000)))
    +t3 : Nat <- IO.now()
    IO.print(Slices.row("20000, tank 1000000", dose(re, so, skip, 20000, 1000000)))
    +t4 : Nat <- IO.now()
    IO.print(Slices.row("bait line", String.append(Nat.show(String.length(bait)), " code points")))
    IO.print(Slices.row("^(a+)+$", shot(evil, bait, 2000000)))
    +t5 : Nat <- IO.now()
    IO.print(Slices.row("a.*b|a  find_all", found(Regex.find_all(rescan, bait, 2000000))))
    t6 : Nat <- IO.now()
    IO.print_err(String.join([ms("5000", t0, t1), ms("10000", t1, t2), ms("20000", t2, t3), ms("refused", t3, t4),
      ms("^(a+)+$", t4, t5), ms("a.*b|a to the budget error", t5, t6)], " | "))

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("FILE"))
    f : File <- IO.try(File, File.open(path, "r"))
    read : File & Result<&1, &1, U32 & String, String> <- File.read(f, 65536)
    run(read)
