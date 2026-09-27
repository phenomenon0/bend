# Bulk native copies must preserve every cell and independent ownership at
# the 128-byte cutoff. Splitting and rebuilding also exercise blk_fill;
# boxed clones must still retain their cells rather than copying handles.
import Base

def fill(n: Nat, a: Array<U32>) -> Array<U32>:
  match n:
    case 0n:
      a
    case 1n++k:
      fill(k, Array.set(U32, a, U32.from_nat(k), U32.from_nat(k)))

def values(a: Array<U32>) -> String:
  match a:
    case ALeaf{x}:
      U32.show(x) ++ ","
    case ANode{l, r}:
      values(l) ++ values(r)

def rebuild(a: Array<U32>) -> Array<U32>:
  match a:
    case ALeaf{x}:
      ALeaf{x}
    case ANode{l, r}:
      ANode{l, r}

def both(+n: U32, r: Array<U32> & Array<U32>) -> String:
  (a, b) = r
  values(a) ++ ":" ++ values(rebuild(Array.set(U32, b, U32.sub(n, 1), 1000)))

def row(+d: Nat, +n: U32) -> String:
  both(n, Array.clone(U32, fill(U32.to_nat(n), Array.new(U32, d, 0))))

def fill_text(n: Nat, a: Array<String>) -> Array<String>:
  match n:
    case 0n:
      a
    case 1n++k:
      fill_text(k, Array.set(String, a, U32.from_nat(k), U32.show(U32.from_nat(k)) ++ ","))

def text(a: Array<String>) -> String:
  match a:
    case ALeaf{x}:
      x
    case ANode{l, r}:
      text(l) ++ text(r)

def boxed(r: Array<String> & Array<String>) -> String:
  (a, b) = r
  text(a) ++ ":" ++ text(Array.set(String, b, 31, "z"))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(row(4n, 16))
    IO.print(row(5n, 32))
    IO.print(row(6n, 64))
    IO.print(boxed(Array.clone(String, fill_text(32n, Array.new(String, 5n, "")))))

#|0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,:0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,1000,
#|0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,:0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,1000,
#|0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,:0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,1000,
#|0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,:0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,z
