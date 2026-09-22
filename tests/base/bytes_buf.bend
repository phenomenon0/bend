# Bytes, the flat byte buffer: a String below 256 in every Char. Its
# length, a byte by index (256 past the end), a slice as (at, n), drop,
# append and concat, the prefix test and the CRLF CRLF search a head
# parser needs, and the round trip through a List of U32 that the byte
# pair carries -- byte 200 and byte 0 included, which text would not.
import Base

def at(m: Maybe<&2, Nat>) -> String:
  match m:
    case None{}:
      "absent"
    case Some{n}:
      Nat.show(n)

def nums(xs: List<&2, U32>) -> String:
  List.show(~&2, ~U32, ~(x => U32.show(x)), xs)

def req() -> Bytes():
  "GET / HTTP/1.1\r\nhost: x\r\n\r\nNEXT"

def main() -> IO(Unit):
  +raw = Bytes.from_list([0, 200, 255, 10])
  +r = req()
  do IO<Unit>:
    IO.print(Nat.show(Bytes.len(r)))
    IO.print(U32.show(Bytes.get(r, 0n)) ++ " " ++ U32.show(Bytes.get(r, 99n)))
    IO.print(Bytes.slice(r, 4n, 1n) ++ "|" ++ Bytes.slice(r, 6n, 8n) ++ "|")
    IO.print(at(Bytes.find(r, "\r\n\r\n")) ++ " " ++ at(Bytes.find(r, "\n\n")))
    IO.print(Bytes.drop(r, 27n))
    IO.print(Bool.show(Bytes.starts_with(r, "GET ")) ++ " "
      ++ Bool.show(Bytes.starts_with(r, "POST")))
    IO.print(nums(Bytes.to_list(raw)))
    IO.print(Nat.show(Bytes.len(Bytes.append(raw, raw))))
    IO.print(Bytes.concat(["HTTP/1.1 ", "200 OK", "!"]))
    IO.print(U32.show(Bytes.get(Bytes.slice(raw, 1n, 2n), 1n)) ++ " "
      ++ U32.show(Bytes.get(Bytes.slice(raw, 1n, 2n), 2n)))

#|31
#|71 256
#|/|HTTP/1.1|
#|23 absent
#|NEXT
#|True False
#|[0, 200, 255, 10]
#|8
#|HTTP/1.1 200 OK!
#|255 256
