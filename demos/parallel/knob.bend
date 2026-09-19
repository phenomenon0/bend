# The thread knob: a text scan (lines, trim, words, a rolling checksum of every
# code point) as a fork/join tree over the corpus of gen_corpus.py. No thread
# code: `a b = f(x) g(y)` is the whole parallel API, --threads is the knob.
#   KNOB_CORPUS=~/videokit-corpus/knob.txt ./knob --threads 8
# Prints tokens:checksum (stdout) and the phase times (stderr).
import Base

def token(s: String, h: U32) -> U32:
  match s:
    case SNil{}:
      h
    case SCon{Chr{x}, t}:
      token(t, U32.add(U32.mul(h, 33), x))

def tokens(xs: List<&2, String>, n: U32, h: U32) -> U32 & U32:
  match xs:
    case Nil{}:
      (n, h)
    case s <> tail:
      tokens(tail, U32.add(n, 1), U32.add(h, token(s, 0)))

def lines(xs: List<&2, String>, acc: U32 & U32) -> U32 & U32:
  match xs:
    case Nil{}:
      acc
    case s <> tail:
      (n, h) = acc
      lines(tail, tokens(String.words(String.trim(s)), n, h))

def join(a: U32 & U32, b: U32 & U32) -> U32 & U32:
  (an, ah) = a
  (bn, bh) = b
  (U32.add(an, bn), U32.add(ah, bh))

def pow2(d: Nat) -> Nat:
  match d:
    case 0n:
      1n
    case 1n+p:
      +h = pow2(p)
      Nat.add(h, h)

# the text of 2^d blocks of `block` code points: halves fork, a block scans.
# The leaf copies its block: every word is a view that counts a reference on
# its payload, and sixteen threads counting on ONE shared payload contend on
# that cell (measured: no scaling; run_knob.sh SHARED=1 shows it). A private
# 64K block per leaf keeps the counts core-local.
def scan(d: Nat, +block: Nat, +s: String) -> U32 & U32:
  match d:
    case 0n:
      lines(String.lines(String.copy(s)), (0, 0))
    case 1n++p:
      +half = Nat.mul(pow2(p), block)
      a b = scan(p, block, String.take(s, half)) scan(p, block, String.drop(s, half))
      join(a, b)

# floor(log2(n)); every step runs (Bool.pick is strict), the fuel bounds them
def log2(fuel: Nat, +n: Nat) -> Nat:
  match fuel:
    case 0n:
      0n
    case 1n+f:
      Bool.pick(Nat, Nat.is_lt(1n, n), 1n+log2(f, Nat.div(n, 2n)), 0n)

def report(t0: Nat, +t1: Nat, r: U32 & U32) -> IO(Unit):
  (n, h) = r
  do IO<Unit>:
    IO.print(String.append(U32.show(n), String.append(":", U32.show(h))))
    t2 : Nat <- IO.now()
    IO.print_err(String.concat(["read+decode ", Nat.show(Nat.sub(t1, t0)),
      " ms, scan ", Nat.show(Nat.sub(t2, t1)), " ms"]))

def ready(t0: Nat, +s: String) -> IO(Unit):
  do IO<Unit>:
    t1 : Nat <- IO.now()
    report(t0, t1, scan(log2(32n, Nat.div(String.length(s), U32.to_nat(65536))), U32.to_nat(65536), s))

def read_done(t0: Nat, read: File & Result<&1, &1, U32 & String, String>) -> IO(Unit):
  (f, r) = read
  do IO<Unit>:
    s : String <- IO.pass(String, r)
    File.close(f)
    ready(t0, s)

def main() -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    path : String <- IO.try(String, IO.get_env("KNOB_CORPUS"))
    f : File <- IO.try(File, File.open(path, "r"))
    r : File & Result<&1, &1, U32 & String, String> <- File.read(f, 2147483647)
    read_done(t0, r)
