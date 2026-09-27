# Array.get4 wraps each of its four indexes exactly as Array.get does. Its
# native read checks the range once for the group and takes a wide path
# only when all four slots are in range, so every group here that crosses
# the block end (i = 5..7 on 8 slots, any i on 1 or 2 slots, i near 2^32
# where i+k itself wraps) must take the scalar fallback and still print the
# same line as four separate Array.gets. The widths cover the three native
# cell shapes: a U32 buffer, a two-word record, and boxed Strings.
import Base

type P is Data:
  P{a: U32, b: U32}

def P.show(p: P) -> String:
  match p:
    case P{a, b}:
      U32.show(a) ++ ":" ++ U32.show(b)

def mk8(+n: Nat) -> Array<U32>:
  Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32,
  Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32,
    [0 : U32^n], 0, 10), 1, 11), 2, 12), 3, 13), 4, 14), 5, 15), 6, 16), 7, 17)

def u4(r: Array<U32> & (U32 & (U32 & (U32 & U32)))) -> Array<U32> & String:
  (a, q) = r
  (x0, t) = q
  (x1, u) = t
  (x2, x3) = u
  (a, String.join([U32.show(x0), U32.show(x1), U32.show(x2), U32.show(x3)], ","))

def g.d(x0: U32, x1: U32, x2: U32, r: Array<U32> & U32) -> Array<U32> & String:
  (a, x3) = r
  (a, String.join([U32.show(x0), U32.show(x1), U32.show(x2), U32.show(x3)], ","))

def g.c(+i: U32, x0: U32, x1: U32, r: Array<U32> & U32) -> Array<U32> & String:
  (a, x2) = r
  g.d(x0, x1, x2, Array.get(U32, a, U32.add(i, 3)))

def g.b(+i: U32, x0: U32, r: Array<U32> & U32) -> Array<U32> & String:
  (a, x1) = r
  g.c(i, x0, x1, Array.get(U32, a, U32.add(i, 2)))

def g.a(+i: U32, r: Array<U32> & U32) -> Array<U32> & String:
  (a, x0) = r
  g.b(i, x0, Array.get(U32, a, U32.add(i, 1)))

def gets(a: Array<U32>, +i: U32) -> Array<U32> & String:
  g.a(i, Array.get(U32, a, i))

def row.fin(+i: U32, s: String, r: Array<U32> & String) -> String:
  (a, t) = r
  U32.show(i) ++ " " ++ s ++ (" " ++ t)

def row(+i: U32, r: Array<U32> & String) -> String:
  (a, s) = r
  row.fin(i, s, gets(a, i))

def rows(fuel: Nat, +i: U32, +n: Nat) -> List<&2, String>:
  match fuel:
    case 0n:
      []
    case 1n++k:
      row(i, u4(Array.get4(U32, mk8(n), i))) <> rows(k, U32.inc(i), n)

def p4(r: Array<P> & (P & (P & (P & P)))) -> String:
  (a, q) = r
  (x0, t) = q
  (x1, u) = t
  (x2, x3) = u
  String.join([P.show(x0), P.show(x1), P.show(x2), P.show(x3)], ",")

def mkp() -> Array<P>:
  Array.set(P, Array.set(P, Array.set(P, Array.set(P,
    [P{0, 0} : P^2n], 0, P{1, 2}), 1, P{3, 4}), 2, P{5, 6}), 3, P{7, 8})

def s4(r: Array<String> & (String & (String & (String & String)))) -> String:
  (a, q) = r
  (x0, t) = q
  (x1, u) = t
  (x2, x3) = u
  String.join([x0, x1, x2, x3], ",")

def mks() -> Array<String>:
  Array.set(String, Array.set(String, Array.set(String, Array.set(String,
    ["" : String^2n], 0, "w"), 1, "x"), 2, "y"), 3, "z")

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(String.join(rows(12n, 0, 3n), "\n"))
    IO.print(String.join(rows(3n, 4294967293, 3n), "\n"))
    IO.print(String.join(rows(3n, 0, 1n), "\n"))
    IO.print(String.join(rows(2n, 7, 0n), "\n"))
    IO.print(p4(Array.get4(P, mkp(), 0)))
    IO.print(p4(Array.get4(P, mkp(), 2)))
    IO.print(s4(Array.get4(String, mks(), 0)))
    IO.print(s4(Array.get4(String, mks(), 3)))

#|0 10,11,12,13 10,11,12,13
#|1 11,12,13,14 11,12,13,14
#|2 12,13,14,15 12,13,14,15
#|3 13,14,15,16 13,14,15,16
#|4 14,15,16,17 14,15,16,17
#|5 15,16,17,10 15,16,17,10
#|6 16,17,10,11 16,17,10,11
#|7 17,10,11,12 17,10,11,12
#|8 10,11,12,13 10,11,12,13
#|9 11,12,13,14 11,12,13,14
#|10 12,13,14,15 12,13,14,15
#|11 13,14,15,16 13,14,15,16
#|4294967293 15,16,17,10 15,16,17,10
#|4294967294 16,17,10,11 16,17,10,11
#|4294967295 17,10,11,12 17,10,11,12
#|0 16,17,16,17 16,17,16,17
#|1 17,16,17,16 17,16,17,16
#|2 16,17,16,17 16,17,16,17
#|7 17,17,17,17 17,17,17,17
#|8 17,17,17,17 17,17,17,17
#|1:2,3:4,5:6,7:8
#|5:6,7:8,1:2,3:4
#|w,x,y,z
#|z,w,x,y
