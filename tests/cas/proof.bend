# cas (proof): the inclusion checker on its own. The tree is five leaves,
# because five is odd at every level it has (5 -> 3 -> 2 -> 1) and odd is
# where a Merkle tree goes wrong: the last node is PROMOTED, never duplicated,
# or two different leaf lists share a root. The leaves are made by hand, not
# hashed -- what a leaf hashes is chunk.bend's business; this file is about
# what the fold does with one. Every refusal below is a range the daemon would
# have had to answer with nothing.
import Base
import ../../power/blake3.bend as B3
import ../../demos/io_cas_store/cas.bend as Cas

def leaf(+i: U32) -> B3.Cv:
  B3.Cv{U32.add(i, 1), 0, 0, 0, 0, 0, 0, 0}

def lv() -> List<&2, B3.Cv>:
  [leaf(0), leaf(1), leaf(2), leaf(3), leaf(4)]

def rt() -> B3.Cv:
  Cas.root(lv(), 5)

def yn(b: Bool) -> String:
  match b:
    case True{}:
      "yes"
    case False{}:
      "no"

# drop the first sibling: a witness one level short
def tl(xs: List<&2, B3.Cv>) -> List<&2, B3.Cv>:
  match xs:
    case Nil{}:
      []
    case Con{h, t}:
      t

# swap the first sibling for one the tree never held
def forge(xs: List<&2, B3.Cv>) -> List<&2, B3.Cv>:
  match xs:
    case Nil{}:
      []
    case Con{h, t}:
      Con{leaf(9), t}

# a witness longer than any tree of 2^32 leaves could need
def many(fuel: Nat, acc: List<&2, B3.Cv>) -> List<&2, B3.Cv>:
  match fuel:
    case 0n:
      acc
    case 1n++f:
      many(f, Con{leaf(0), acc})

def ok(+i: U32) -> String:
  yn(Cas.check(rt(), 5, i, leaf(i), Cas.prove(lv(), i, 5)))

def tampered(+i: U32) -> String:
  yn(Cas.check(rt(), 5, i, leaf(7), Cas.prove(lv(), i, 5)))

def forged(+i: U32) -> String:
  yn(Cas.check(rt(), 5, i, leaf(i), forge(Cas.prove(lv(), i, 5))))

def short(+i: U32) -> String:
  yn(Cas.check(rt(), 5, i, leaf(i), tl(Cas.prove(lv(), i, 5))))

def moved(+i: U32, +j: U32) -> String:
  yn(Cas.check(rt(), 5, j, leaf(i), Cas.prove(lv(), i, 5)))

def row(+i: U32) -> String:
  String.concat([U32.show(i), " ok ", ok(i), " tampered ", tampered(i),
    " forged ", forged(i), " short ", short(i)])

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(row(0))
    IO.print(row(1))
    IO.print(row(2))
    IO.print(row(3))
    IO.print(row(4))
    IO.print("moved 0->1 " ++ moved(0, 1))
    IO.print("moved 4->0 " ++ moved(4, 0))
    IO.print("index past the end " ++ yn(Cas.check(rt(), 5, 5, leaf(0), [])))
    IO.print("witness over budget " ++ yn(Cas.check(rt(), 5, 0, leaf(0), many(40n, []))))
#|0 ok yes tampered no forged no short no
#|1 ok yes tampered no forged no short no
#|2 ok yes tampered no forged no short no
#|3 ok yes tampered no forged no short no
#|4 ok yes tampered no forged no short no
#|moved 0->1 no
#|moved 4->0 no
#|index past the end no
#|witness over budget no
