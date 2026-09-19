# slices: the instant-slice tour. $FILE holds 16-character records, record k
# spelling the number k (gen_records.py), so every value printed below proves
# which characters were reached. One read; after it, no operation copies or
# walks the text: length, get, take, drop, slice, take_end, drop_end are O(1).
#   FILE=records.txt ./slices --gpu off
import Base

def row(label: String, value: String) -> String:
  String.append(String.pad_end(label, 26n, ' '), value)

def char(c: Maybe<&2, Char>) -> String:
  match c:
    case None{}:
      "(none)"
    case Some{c}:
      SCon{c, SNil{}}

# record k: the 15 digits at offset 16k
def record(s: String, +k: Nat) -> String:
  String.slice(s, Nat.mul(k, 16n), Nat.add(Nat.mul(k, 16n), 15n))

def tour(+s: String, +n: Nat) -> List<&2, String>:
  +recs = Nat.div(n, 16n)
  +mid = Nat.div(recs, 2n)
  +last = Nat.sub(recs, 1n)
  [row("length", Nat.show(n)),
   row("records", Nat.show(recs)),
   row("get 14", char(String.get(s, 14n))),
   row(String.append("get ", Nat.show(Nat.add(Nat.mul(mid, 16n), 14n))),
     char(String.get(s, Nat.add(Nat.mul(mid, 16n), 14n)))),
   row("get_end 2", char(String.get_end(s, 2n))),
   row("take 15", String.take(s, 15n)),
   row(String.append("record ", Nat.show(mid)), record(s, mid)),
   row(String.append("record ", Nat.show(last)), record(s, last)),
   row("drop to last | take 15", String.take(String.drop(s, Nat.mul(last, 16n)), 15n)),
   row("take_end 16 | trim", String.trim(String.take_end(s, 16n))),
   row("drop_end all but 15", String.drop_end(s, Nat.sub(n, 15n)))]

def parse(m: Maybe<&2, U32>) -> U32:
  match m:
    case None{}:
      0
    case Some{x}:
      x

# `fuel` scattered records: slice each, parse its digits, sum what was read
# (got) beside the record numbers asked for (want)
def hammer(fuel: Nat, +s: String, +recs: U32, +i: U32, got: U32, want: U32) ->
  U32 & U32:
  match fuel:
    case 0n:
      (got, want)
    case 1n+p:
      +k = U32.mod(U32.mul(i, 2654435761), recs)
      hammer(p, s, recs, U32.add(i, 1),
        U32.add(got, parse(U32.read(record(s, U32.to_nat(k))))), U32.add(want, k))

def verdict.if(got: U32, same: Bool) -> String:
  match same:
    case False{}:
      "MISMATCH"
    case True{}:
      String.append("all correct, checksum ", U32.show(got))

def verdict(sums: U32 & U32) -> String:
  (+got, want) = sums
  verdict.if(got, U32.is_eq(got, want))

# $N: how many scattered records to visit (default 1000000)
def visits(r: Result<&1, &1, U32 & String, String>) -> U32:
  match r:
    case Fail{e}:
      1000000
    case Done{text}:
      parse(U32.read(text))

def timing(+count: U32, t0: Nat, t1: Nat, t2: Nat, +t3: Nat) -> IO(Unit):
  do IO<Unit>:
    t4 : Nat <- IO.now()
    IO.print_err(String.concat(["load ", Nat.show(Nat.sub(t1, t0)), " ms | tour ",
      Nat.show(Nat.sub(t3, t2)), " ms | ", U32.show(count), " deep slices ",
      Nat.show(Nat.sub(t4, t3)), " ms"]))

def run(read: File & Result<&1, &1, U32 & String, String>, +t0: Nat) -> IO(Unit):
  (f, result) = read
  do IO<Unit>:
    +s : String <- IO.pass(String, result)
    File.close(f)
    t1 : Nat <- IO.now()
    +n : Nat = String.length(s)
    t2 : Nat <- IO.now()
    IO.print(String.join(tour(s, n), "\n"))
    t3 : Nat <- IO.now()
    env : Result<&1, &1, U32 & String, String> <- IO.get_env("N")
    +count : U32 = visits(env)
    IO.print(row(String.append(U32.show(count), " scattered records"),
      verdict(hammer(U32.to_nat(count), s, U32.from_nat(Nat.div(n, 16n)), 1, 0, 0))))
    timing(count, t0, t1, t2, t3)

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("FILE"))
    t0 : Nat <- IO.now()
    f : File <- IO.try(File, File.open(path, "r"))
    read : File & Result<&1, &1, U32 & String, String> <- File.read(f, 2147483647)
    run(read, t0)
