# std/bytes.bend, whichever implementation its import line names: the byte
# string reads (get past the end is 256), the scans from an offset (absent
# is the end), cut and slice, the reader (at past the end is 0; reads
# forward, back and forward again), the writer, and a file of every byte
# value written and read back whole, no byte re-encoded.
import Base
import ../../std/bytes.bend as By

def ns.go(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, t}:
      " " ++ U32.show(x) ++ ns.go(t)

def ns(b: String) -> String:
  "[" ++ ns.go(By.to_list(b)) ++ " ]"

def mb(m: Maybe<&2, Nat>) -> String:
  match m:
    case None{}:
      "none"
    case Some{n}:
      Nat.show(n)

def pair(p: String & String) -> String:
  (a, b) = p
  ns(a) ++ " " ++ ns(b)

def ab() -> String:
  By.from_list([104, 101, 108, 108, 111, 44, 32, 119, 111, 114, 108, 100, 0, 255])

type Rd is Data:
  Rd{b: By.Buf(), acc: String}

def rd.at(acc: String, r: By.Buf() & U32) -> Rd:
  (b, x) = r
  Rd{b, acc ++ " " ++ U32.show(x)}

def rd(r: Rd, +i: U32) -> Rd:
  match r:
    case Rd{b, acc}:
      rd.at(acc, By.at(b, i))

def rd.take(acc: String, r: By.Buf() & String) -> Rd:
  (b, s) = r
  Rd{b, acc ++ " " ++ ns(s)}

def take(r: Rd, +i: U32, +n: U32) -> Rd:
  match r:
    case Rd{b, acc}:
      rd.take(acc, By.take(b, i, n))

def rd.size(acc: String, r: By.Buf() & U32) -> String:
  (b, n) = r
  acc ++ " size " ++ U32.show(n)

def rd.fin(r: Rd) -> String:
  match r:
    case Rd{b, acc}:
      rd.size(acc, By.size(b))

def reads() -> String:
  rd.fin(take(take(rd(rd(rd(rd(rd(Rd{By.open(ab()), "at"}, 0), 4), 13), 1), 14), 7, 5), 12, 9))

def every(k: Nat, +x: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      acc
    case 1n+j:
      every(j, U32.sub(x, 1), Con{x, acc})

def file(r: Result<&1, &1, U32 & String, String>) -> String:
  match r:
    case Fail{(c, m)}:
      "no file"
    case Done{+b}:
      Nat.show(By.len(b)) ++ " bytes, " ++
        Bool.pick(String, String.eq(b, By.from_list(every(256n, 255, Nil{}))), "every byte back", "WRONG")

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(ns(ab()) ++ " len " ++ Nat.show(By.len(ab())))
    IO.print("get " ++ U32.show(By.get(ab(), 0n)) ++ " " ++ U32.show(By.get(ab(), 13n)) ++ " " ++
      U32.show(By.get(ab(), 14n)))
    IO.print("find_byte " ++ Nat.show(By.find_byte(ab(), 0n, 111)) ++ " " ++ Nat.show(By.find_byte(ab(), 5n, 111)) ++
      " " ++ Nat.show(By.find_byte(ab(), 9n, 111)) ++ " " ++ Nat.show(By.find_byte(ab(), 20n, 111)))
    IO.print("find_any " ++ Nat.show(By.find_any(ab(), 0n, 44, 32, 0, 0)) ++ " " ++
      Nat.show(By.find_any(ab(), 6n, 44, 32, 0, 0)) ++ " " ++ Nat.show(By.find_any(ab(), 0n, 1, 2, 3, 4)))
    IO.print("span " ++ Nat.show(By.span(ab(), 0n, 97, 123)) ++ " " ++ Nat.show(By.span(ab(), 7n, 97, 123)) ++
      " " ++ Nat.show(By.span(ab(), 5n, 97, 123)))
    IO.print("find " ++ mb(By.find(ab(), "world")) ++ " " ++ mb(By.find(ab(), "")) ++ " " ++ mb(By.find(ab(), "xyz")))
    IO.print("word_le " ++ U32.show(By.word_le(ab(), 0n)) ++ " " ++ U32.show(By.word_le(ab(), 12n)))
    IO.print("cut " ++ pair(By.cut(ab(), 5n)) ++ " slice " ++ ns(By.slice(ab(), 7n, 5n)) ++ " " ++
      ns(By.slice(ab(), 12n, 9n)))
    IO.print("push " ++ ns(By.push(By.push("", 1), 200)) ++ " one " ++ ns(By.one(7)))
    IO.print(reads())
    IO.print("out " ++ By.out.done(By.out.push(By.out.add(By.out.add(By.out.new(), "ab"), ""), 99)) ++
      "|" ++ By.out.done(By.out.new()) ++ "|")
    w : Result<&1, &1, U32 & String, Unit> <- By.write_file("/tmp/bend-std-bytes.bin", By.from_list(every(256n, 255, Nil{})))
    r : Result<&1, &1, U32 & String, String> <- By.read_file("/tmp/bend-std-bytes.bin")
    IO.print(file(r))
    n : Result<&1, &1, U32 & String, String> <- By.read_file("/tmp/bend-std-no-such-file")
    IO.print(file(n))

#|[ 104 101 108 108 111 44 32 119 111 114 108 100 0 255 ] len 14
#|get 104 255 256
#|find_byte 4 8 14 20
#|find_any 5 6 14
#|span 5 5 0
#|find 7 0 none
#|word_le 1819043176 65280
#|cut [ 104 101 108 108 111 ] [ 44 32 119 111 114 108 100 0 255 ] slice [ 119 111 114 108 100 ] [ 0 255 ]
#|push [ 1 200 ] one [ 7 ]
#|at 104 111 255 101 0 [ 119 111 114 108 100 ] [ 0 255 ] size 14
#|out abc||
#|256 bytes, every byte back
#|no file
