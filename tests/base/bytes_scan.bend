# The scanner's reads: Bytes.get (256 past the end), Bytes.push, Bytes.span
# (how many bytes from i lie in [lo, hi)), Bytes.find_byte (the first
# offset of a byte at or after i, the end when absent) and Bytes.find_any
# (the same for any of four bytes). Natively C and JS
# read the packed cells in place and push writes into spare room; the
# interpreter runs their Bend bodies, so the four lanes agreeing is the
# natives equal to the spec. The edges: the empty buffer, i at and past
# the end, an empty and an inverted range, a view with an offset, a
# buffer built by pushing (shared midway, so one push copies), a cell
# past 255 (a wide string), and a buffer read after it was borrowed.
import Base

def n(x: Nat) -> String:
  Nat.show(x)

def u(x: U32) -> String:
  U32.show(x)

def gets(k: Nat, +b: Bytes(), +i: Nat) -> String:
  match k:
    case 0n:
      ""
    case 1n+j:
      u(Bytes.get(b, i)) ++ " " ++ gets(j, b, 1n+i)

# push the bytes lo, lo+1, .. (mod 256) k times
def fill(k: Nat, b: Bytes(), +x: U32) -> Bytes():
  match k:
    case 0n:
      b
    case 1n+j:
      fill(j, Bytes.push(b, U32.and(x, 255)), U32.add(x, 7))

# a sum of every byte, read by index: a loop over one borrowed buffer
def sum(k: Nat, +b: Bytes(), +i: Nat, acc: U32) -> U32:
  match k:
    case 0n:
      acc
    case 1n+j:
      sum(j, b, 1n+i, U32.add(U32.mul(acc, 31), Bytes.get(b, i)))

# the runs of a token scanner: digits, then letters, then to the next ','
def runs(k: Nat, +b: Bytes(), +i: Nat) -> String:
  match k:
    case 0n:
      ""
    case 1n+j:
      +d = Bytes.span(b, i, 48, 58)
      +a = Bytes.span(b, Nat.add(i, d), 97, 123)
      +c = Bytes.find_byte(b, Nat.add(i, Nat.add(d, a)), 44)
      n(d) ++ "," ++ n(a) ++ "," ++ n(c) ++ " " ++ runs(j, b, 1n+c)

def main() -> IO(Unit):
  +e : Bytes() = ""
  +r : Bytes() = "12ab,345,,x9,cd"
  +w = Bytes.push("a\u{1F600}bc", 98)
  +v = Bytes.slice(r, 5n, 6n)
  +f = fill(300n, "", 250)
  +g = Bytes.push(f, 0)
  +h = Bytes.push(f, 1)
  do IO<Unit>:
    IO.print(gets(2n, e, 0n) ++ "| " ++ gets(4n, r, 13n) ++ "| " ++ u(Bytes.get(r, Nat.mul(4294967295n, 256n))))
    IO.print(gets(6n, w, 0n) ++ "| " ++ gets(7n, v, 0n))
    IO.print(n(Bytes.len(w)) ++ " " ++ n(Bytes.len(f)) ++ " " ++ gets(4n, f, 297n))
    IO.print(gets(3n, g, 298n) ++ "| " ++ gets(3n, h, 298n) ++ "| " ++ n(Bytes.len(f)))
    IO.print(u(sum(300n, f, 0n, 7)) ++ " " ++ u(sum(20n, r, 0n, 7)))
    IO.print(Bytes.push(Bytes.push("", 104), 105) ++ " " ++ Bytes.push("ok", 33))
    IO.print(n(Bytes.len(Bytes.push("x", 300))) ++ " " ++ u(Bytes.get(Bytes.push("x", 300), 1n)))
    IO.print(n(Bytes.span(e, 0n, 0, 256)) ++ " " ++ n(Bytes.span(r, 0n, 0, 256)) ++ " "
      ++ n(Bytes.span(r, 0n, 50, 48)) ++ " " ++ n(Bytes.span(r, 0n, 49, 49)) ++ " "
      ++ n(Bytes.span(r, 15n, 0, 256)) ++ " " ++ n(Bytes.span(r, 99n, 0, 256)))
    IO.print(n(Bytes.span(r, 1n, 48, 51)) ++ " " ++ n(Bytes.span(r, 0n, 48, 51)) ++ " "
      ++ n(Bytes.span(v, 0n, 44, 58)) ++ " " ++ n(Bytes.span(w, 0n, 97, 99)) ++ " "
      ++ n(Bytes.span(w, 0n, 0, 131072)) ++ " " ++ n(Bytes.span(w, 2n, 97, 100)))
    IO.print(runs(5n, r, 0n))
    IO.print(n(Bytes.find_byte(r, 0n, 44)) ++ " " ++ n(Bytes.find_byte(r, 4n, 44)) ++ " "
      ++ n(Bytes.find_byte(r, 5n, 44)) ++ " " ++ n(Bytes.find_byte(r, 0n, 122)) ++ " "
      ++ n(Bytes.find_byte(r, 20n, 44)) ++ " " ++ n(Bytes.find_byte(r, 0n, 300)) ++ " "
      ++ n(Bytes.find_byte(e, 0n, 0)))
    IO.print(n(Bytes.find_byte(w, 0n, 128512)) ++ " " ++ n(Bytes.find_byte(w, 0n, 98)) ++ " "
      ++ n(Bytes.find_byte(v, 0n, 44)) ++ " " ++ n(Bytes.find_byte(v, 2n, 120)) ++ " "
      ++ n(Bytes.find_byte(f, 0n, 5)) ++ " " ++ n(Bytes.find_byte(f, 250n, 250)))
    IO.print(n(Bytes.find_any(r, 0n, 44, 34, 13, 10)) ++ " " ++ n(Bytes.find_any(r, 0n, 120, 57, 99, 98))
      ++ " " ++ n(Bytes.find_any(r, 11n, 120, 57, 99, 98)) ++ " " ++ n(Bytes.find_any(r, 3n, 0, 0, 0, 0))
      ++ " " ++ n(Bytes.find_any(r, 99n, 44, 44, 44, 44)) ++ " " ++ n(Bytes.find_any(e, 0n, 1, 2, 3, 4))
      ++ " " ++ n(Bytes.find_any(w, 0n, 300, 128512, 99, 99)) ++ " " ++ n(Bytes.find_any(v, 1n, 120, 44, 0, 0))
      ++ " " ++ n(Bytes.find_any(f, 0n, 5, 1000, 4, 6)))
    IO.print(Bytes.append(r, "!") ++ " " ++ n(Bytes.len(r)) ++ " " ++ v)

#|256 256 | 99 100 256 256 | 256
#|97 128512 98 99 98 256 | 51 52 53 44 44 120 256
#|5 300 25 32 39 256
#|32 39 0 | 32 39 1 | 300
#|3635909921 2619669925
#|hi ok!
#|2 300
#|0 15 0 0 0 0
#|1 2 5 1 5 3
#|2,2,4 3,0,8 0,0,9 0,1,12 0,2,15
#|4 4 8 15 20 15 0
#|1 2 3 5 221 256
#|4 3 11 15 99 0 1 3 38
#|12ab,345,,x9,cd! 15 345,,x
