# Read once, view forever. $FILE is a log of gen_log.py: every 65,536 code
# points a stamp line spells its own block number. One read; then every line
# is a view into that one string (counted, the longest measured), and $N
# scattered visits each slice a stamp's 15 digits, parse them and check them
# against the block asked for. Only the load touches every character.
#   FILE=hostile.log N=1000000 ./views --gpu off
import Base
import ../text/slices.bend as Slices

# (lines, the longest line's length)
def survey(ls: List<&2, String>, +n: U32, +longest: Nat) -> U32 & Nat:
  match ls:
    case Nil{}:
      (n, longest)
    case l <> t:
      survey(t, U32.add(n, 1), Nat.max(longest, String.length(l)))

# block k's digits: 15 code points at offset 65536 k + 7
def stamp(s: String, +k: U32) -> String:
  +at = Nat.add(Nat.mul(U32.to_nat(k), U32.to_nat(65536)), 7n)
  String.slice(s, at, Nat.add(at, 15n))

def hammer(fuel: Nat, +s: String, +blocks: U32, +i: U32, got: U32, want: U32) ->
  U32 & U32:
  match fuel:
    case 0n:
      (got, want)
    case 1n+p:
      +k = U32.mod(U32.mul(i, 2654435761), blocks)
      hammer(p, s, blocks, U32.add(i, 1),
        U32.add(got, Slices.parse(U32.read(stamp(s, k)))), U32.add(want, k))

def surveyed(r: U32 & Nat) -> String:
  (n, longest) = r
  String.concat([U32.show(n), ", the longest ", Nat.show(longest), " code points"])

def run(read: File & Result<&1, &1, U32 & String, String>, +t0: Nat) -> IO(Unit):
  (f, result) = read
  do IO<Unit>:
    +s : String <- IO.pass(String, result)
    File.close(f)
    +t1 : Nat <- IO.now()
    +n : Nat = String.length(s)
    IO.print(Slices.row("code points", Nat.show(n)))
    IO.print(Slices.row("lines, each a view", surveyed(survey(String.splitlines(s), 0, 0n))))
    +t2 : Nat <- IO.now()
    env : Result<&1, &1, U32 & String, String> <- IO.get_env("N")
    +count : U32 = Slices.visits(env)
    IO.print(Slices.row(String.append(U32.show(count), " scattered stamps"),
      Slices.verdict(hammer(U32.to_nat(count), s, U32.from_nat(Nat.div(n, U32.to_nat(65536))), 1, 0, 0))))
    t3 : Nat <- IO.now()
    IO.print_err(String.concat(["load ", Nat.show(Nat.sub(t1, t0)), " ms | every line a view ",
      Nat.show(Nat.sub(t2, t1)), " ms | ", U32.show(count), " slice+parse visits ",
      Nat.show(Nat.sub(t3, t2)), " ms"]))

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("FILE"))
    t0 : Nat <- IO.now()
    f : File <- IO.try(File, File.open(path, "r"))
    read : File & Result<&1, &1, U32 & String, String> <- File.read(f, 2147483647)
    run(read, t0)
