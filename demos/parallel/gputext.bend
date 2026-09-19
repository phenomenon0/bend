# The GPU lane: independent chunks of a corpus, each scanned for its words
# (knob.bend's lines/trim/words/checksum) and its occurrences of "gpu", the
# results joined in order. The one `!` below hands the whole fork/join tree to
# the GPU; no CUDA is written, and --gpu off runs the same binary on the CPU.
#   GPUTEXT_CORPUS=~/videokit-corpus/knob-1024.txt ./gputext --gpu 4GB
# Prints tokens:checksum:occurrences (stdout) and the phase times (stderr).
import Base
import ./knob.bend as Knob

def chunk(+s: String) -> (U32 & U32) & Nat:
  (Knob.lines(String.lines(s), (0, 0)), String.count(s, "gpu"))

def join(a: (U32 & U32) & Nat, b: (U32 & U32) & Nat) -> (U32 & U32) & Nat:
  (aw, ac) = a
  (bw, bc) = b
  (Knob.join(aw, bw), Nat.add(ac, bc))

# 2^d chunks of `block` code points; a chunk is a private copy (see knob.bend)
def scan(d: Nat, +block: Nat, +s: String) -> (U32 & U32) & Nat:
  match d:
    case 0n:
      chunk(String.copy(s))
    case 1n++p:
      +half = Nat.mul(Knob.pow2(p), block)
      a b = scan(p, block, String.take(s, half)) scan(p, block, String.drop(s, half))
      join(a, b)

def report(t0: Nat, +t1: Nat, r: (U32 & U32) & Nat) -> IO(Unit):
  ((n, h), c) = r
  do IO<Unit>:
    IO.print(String.join([U32.show(n), U32.show(h), Nat.show(c)], ":"))
    t2 : Nat <- IO.now()
    IO.print_err(String.concat(["read+decode ", Nat.show(Nat.sub(t1, t0)),
      " ms, scan ", Nat.show(Nat.sub(t2, t1)), " ms"]))

def ready(t0: Nat, +s: String) -> IO(Unit):
  do IO<Unit>:
    t1 : Nat <- IO.now()
    report(t0, t1, scan!(Knob.log2(32n, Nat.div(String.length(s), U32.to_nat(65536))),
      U32.to_nat(65536), s))

def read_done(t0: Nat, read: File & Result<&1, &1, U32 & String, String>) -> IO(Unit):
  (f, r) = read
  do IO<Unit>:
    s : String <- IO.pass(String, r)
    File.close(f)
    ready(t0, s)

def main() -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    path : String <- IO.try(String, IO.get_env("GPUTEXT_CORPUS"))
    f : File <- IO.try(File, File.open(path, "r"))
    r : File & Result<&1, &1, U32 & String, String> <- File.read(f, 2147483647)
    read_done(t0, r)
