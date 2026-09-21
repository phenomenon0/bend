# Ties. The order is (weight, id), greatest first, so of two equal weights the
# larger id ranks higher. That is TopK's order, and the checker holds a
# certificate to it: the reversed tie is out of order, and a K = 1 list that
# kept the smaller id leaves the larger one above its floor (slack).
#
# After `{"a"` only ` ` (12) and `:` (5) are legal; both weigh 1000.
import Base
import ../../power/heap.bend as Heap
import ../../power/decode.bend as D
import ../../demos/decode/main.bend as M
import ./mutant.bend as Mu
import ./refuse.bend as R

def tie() -> List<&2, U32>:
  R.ls([5, 12], 1000)

def honest(k: U32) -> D.Step:
  Mu.got(D.decode_step(M.vocab(), R.colon(), tie(), k, R.at()))

def row(name: String, k: U32, st: D.Step) -> String:
  name ++ " " ++ D.show.vd(D.check(M.vocab(), R.colon(), tie(), k, R.at(), st))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("k2 kept " ++ D.show.kept(Mu.kept(honest(2))) ++ ", " ++ R.say(honest(2)))
    IO.print("k1 kept " ++ D.show.kept(Mu.kept(honest(1))) ++ ", " ++ R.say(honest(1)))
    IO.print(row("k2 honest", 2, honest(2)))
    IO.print(row("k2 reversed", 2, Mu.with.kept(honest(2), [Heap.Entry{1000, 5}, Heap.Entry{1000, 12}])))
    IO.print(row("k1 honest", 1, honest(1)))
    IO.print(row("k1 smaller id", 1, Mu.with.tok(Mu.with.kept(honest(1), [Heap.Entry{1000, 5}]), 5)))
#|k2 kept 1000@12 1000@5, ` ` -> colon/1
#|k1 kept 1000@12, ` ` -> colon/1
#|k2 honest ok
#|k2 reversed order
#|k1 honest ok
#|k1 smaller id slack
