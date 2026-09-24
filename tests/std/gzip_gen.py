#!/usr/bin/env python3
# Prints tests/std/gzip.bend: std/gzip.bend against CPython, small enough to
# run on released Bend's list bytes in every lane. gunzip: CPython's
# gzip.compress of five inputs at levels 0, 1 and 9 (and two members
# joined), each read back as its length and CRC-32. gzip: std's own member
# at the same levels, read back by std's gunzip and compared with the
# input. refused: a bad magic, a flipped trailer CRC, a cut member, and a
# cap one byte short, each refused as zlib's reader refuses it.
#   python3 tests/std/gzip_gen.py > tests/std/gzip.bend
import gzip
import zlib

INPUTS = [
  ("empty", b""),
  ("one", b"a"),
  ("repeat", b"hello hello hello hello hello hello"),
  ("bytes", bytes(range(0, 256, 3))),
  ("text", b" ".join(b"lorem ipsum dolor sit amet %d" % (i * 7 % 13) for i in range(16))),
]
LEVELS = [0, 1, 9]


def lit(b):
  return "By.from_list([" + ", ".join(str(x) for x in b) + "])"


def main():
  rows, want = [], []
  for name, x in INPUTS:
    for lvl in LEVELS:
      z = gzip.compress(x, lvl, mtime=0)
      rows.append('    IO.print("gunzip %s %d " ++ gun(%s, 1000000n))' % (name, lvl, lit(z)))
      want.append("gunzip %s %d ok %d %d" % (name, lvl, len(x), zlib.crc32(x)))
  two = gzip.compress(b"first,", 6, mtime=0) + gzip.compress(b"second", 6, mtime=0)
  rows.append('    IO.print("gunzip two " ++ gun(%s, 1000000n))' % lit(two))
  want.append("gunzip two ok 12 %d" % zlib.crc32(b"first,second"))
  for name, x in INPUTS:
    for lvl in LEVELS:
      rows.append('    IO.print("gzip %s %d " ++ zip(%s, %dn))' % (name, lvl, lit(x), lvl))
      want.append("gzip %s %d back %d %d" % (name, lvl, len(x), zlib.crc32(x)))
  x = INPUTS[4][1]
  z = gzip.compress(x, 6, mtime=0)
  bad = [
    ("magic", b"\x1f\x8c" + z[2:], "NotGzip"),
    ("crc", z[:-8] + bytes([z[-8] ^ 1]) + z[-7:], "BadCrc"),
    ("cut", z[:len(z) // 2], "Truncated"),
  ]
  for name, b, why in bad:
    rows.append('    IO.print("refused %s " ++ gun(%s, 1000000n))' % (name, lit(b)))
    want.append("refused %s %s" % (name, why))
  rows.append('    IO.print("refused cap " ++ gun(%s, %dn))' % (lit(z), len(x) - 1))
  want.append("refused cap Inflate")
  print(HEAD + "\n".join(rows) + "\n\n" + "\n".join("#|" + w for w in want))


HEAD = '''# std/gzip.bend against CPython (tests/std/gzip_gen.py prints this file).
# gunzip: CPython's gzip.compress of five inputs at levels 0, 1 and 9
# (and two members joined), each read back as its length and CRC-32.
# gzip: std's own member at those levels, read back by std's gunzip and
# compared with the input. refused: a bad magic, a flipped trailer CRC, a
# cut member and a cap one byte short. Small enough for released Bend's
# list bytes in every lane.
import Base
import ../../std/bytes.bend as By
import ../../std/deflate.bend as D
import ../../std/gzip.bend as Z

def why(w: Z.Why) -> String:
  match w:
    case Z.Inflate{i}:
      "Inflate"
    case _:
      Z.why.show(w)

def res(r: Result<&2, &2, Z.Err, String>) -> String:
  match r:
    case Done{+b}:
      "ok " ++ Nat.show(By.len(b)) ++ " " ++ U32.show(D.crc32(b, 0))
    case Fail{Z.Err{at, w}}:
      why(w)

def gun(+gz: String, cap: Nat) -> String:
  res(Z.gunzip(cap, gz))

def back(+x: String, r: Result<&2, &2, Z.Err, String>) -> String:
  match r:
    case Done{+b}:
      Bool.pick(String, String.eq(b, x), "back ", "WRONG ") ++ Nat.show(By.len(b)) ++ " " ++
        U32.show(D.crc32(b, 0))
    case Fail{Z.Err{at, w}}:
      why(w)

def zip(+x: String, lvl: Nat) -> String:
  back(x, Z.gunzip(1000000n, Z.gzip(x, lvl)))

def main() -> IO(Unit):
  do IO<Unit>:
'''

main()
