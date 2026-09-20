# Decode a UTF-8 file and count its code points: File.read does the decode,
# String.length walks the decoded payload. The clock stops after IO.print,
# so the walk is forced inside the window and not handed to the printer.
# The length phase carries String.length's Nat and the Nat -> U32 it is shown
# through; both walk the same code points once.
#   DECODE_FILE=ascii-8MiB.txt ./decode_len --gpu off --threads 1
import Base

def report(n: Nat, t0: Nat, +t1: Nat) -> IO(Unit):
  do IO<Unit>:
    IO.print(U32.show(U32.from_nat(n)))
    t2 : Nat <- IO.now()
    IO.print_err(String.concat(["read ", Nat.show(Nat.sub(t1, t0)),
      " ms, length ", Nat.show(Nat.sub(t2, t1)), " ms"]))

def read_done(t0: Nat,
  r: File & Result<&1, &1, U32 & String, String>) -> IO(Unit):
  (f, res) = r
  do IO<Unit>:
    s : String <- IO.pass(String, res)
    File.close(f)
    t1 : Nat <- IO.now()
    report(String.length(s), t0, t1)

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("DECODE_FILE"))
    t0 : Nat <- IO.now()
    f : File <- IO.try(File, File.open(path, "r"))
    r : File & Result<&1, &1, U32 & String, String> <- File.read(f, 2147483647)
    read_done(t0, r)
