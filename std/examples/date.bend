# Format dates: seconds since 1970-01-01 (UTC) as ISO 8601 and as an HTTP
# date, a day number as year, month and day, and back.
#   bend std/examples/date.bend
import Base
import ../time.bend as Time

def ymd(d: Nat & Nat & Nat) -> String:
  (y, md) = d
  (m, day) = md
  Nat.show(y) ++ "/" ++ Nat.show(m) ++ "/" ++ Nat.show(day)

def secs(m: Maybe<&2, Nat>) -> String:
  match m:
    case Some{t}:
      Nat.show(t)
    case None{}:
      "not a date"

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(Time.iso(1727222400n))
    IO.print(Time.http(1727222400n))
    IO.print(Time.iso.ms(Nat.add(Nat.mul(1727222400n, 1000n), 123n)))
    IO.print(ymd(Time.date(19991n)))
    IO.print(secs(Time.from(2024n, 9n, 25n, 0n, 0n, 0n)))
    IO.print(secs(Time.iso.read("2024-02-29T12:00:00Z")))
    IO.print(secs(Time.iso.read("2023-02-29T12:00:00Z")))

#|2024-09-25T00:00:00Z
#|Wed, 25 Sep 2024 00:00:00 GMT
#|2024-09-25T00:00:00.123Z
#|2024/9/25
#|1727222400
#|1709208000
#|not a date
