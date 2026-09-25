# U21: the JS lane runs a non-tail recursion on the host's stack: a list of
# 100000 counted by a def that conses after its call overflows it (bun,
# 32 MiB of stack as gates/test.ts gives it), where C (heap frames)
# answers; `bend` runs an IO main on the JS runtime too. Every lane should
# print 100000.
import Base

def count(xs: List<&2, U32>) -> Nat:
  match xs:
    case []:
      0n
    case x <> rest:
      1n+count(rest)

def main() -> IO(Unit):
  IO.print(Nat.show(count(List.replicate(U32, 100000n, 7))))
