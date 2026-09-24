# F09: Base's only byte container is String, a list: String.get(s, i)
# walks i cells, so a decoder that reads by offset (inflate's window, a
# hash's word, a table's cell) is quadratic. Summing the bytes of a
# 16384-byte string by offset takes n^2/2 = 134M steps: about 0.5 s in the
# C lane where a scan by pattern match takes 0.2 ms, and 4x that for twice
# the bytes. std/gzip.bend on canon inflates 30 KB in 16 s (this repo's
# packed bytes: 1 MB in 0.4 s).
import Base

def build(k: Nat, +x: U32, acc: String) -> String:
  match k:
    case 0n:
      acc
    case 1n+j:
      build(j, U32.inc(x), SCon{Chr{U32.and(x, 255)}, acc})

def byte(m: Maybe<&2, Char>) -> U32:
  match m:
    case None{}:
      0
    case Some{Chr{c}}:
      c

def sum(k: Nat, +s: String, +i: Nat, +acc: U32) -> U32:
  match k:
    case 0n:
      acc
    case 1n+j:
      sum(j, s, 1n+i, U32.add(acc, byte(String.get(s, i))))

def main() -> IO(Unit):
  IO.print(U32.show(sum(16384n, build(16384n, 0, ""), 0n, 0)))

#|2088960
