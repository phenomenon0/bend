import Base
import ../../std/time.bend as Time

# std/time.bend: tests/base/time.bend over std/, plus weekday, from and
# iso.read (its own dates read back, and text that is not one). Vectors at the epoch,
# a leap day of a century year (2000), the last signed 32-bit second
# (2038), a century that is no leap year (2100) and RFC 9110's own
# example; days no month has; and the calendar's round trip, a day to
# its date and back, every 97th day from 1970 to the year 2501.

def ymd.show(ymd: Nat & Nat & Nat) -> String:
  (y, md) = ymd
  (m, d) = md
  Nat.show(y) ++ "/" ++ Nat.show(m) ++ "/" ++ Nat.show(d)

def day.show(m: Maybe<&2, Nat>) -> String:
  match m:
    case None{}:
      "none"
    case Some{x}:
      Nat.show(x)

def day.p(ymd: Nat & Nat & Nat) -> Maybe<&2, Nat>:
  (y, md) = ymd
  (m, d) = md
  Time.day(y, m, d)

# 1 when day n does not come back from its date
def trip.is(m: Maybe<&2, Nat>, +n: Nat) -> Nat:
  match m:
    case None{}:
      1n
    case Some{x}:
      Bool.pick(Nat, Nat.is_eq(x, n), 0n, 1n)

def trip(f: Nat, +n: Nat, +bad: Nat) -> Nat:
  match f:
    case 0n:
      bad
    case 1n+g:
      trip(g, Nat.add(n, 97n), Nat.add(bad, trip.is(day.p(Time.date(n)), n)))

def text() -> String:
  Time.iso(0n) ++ " " ++ Time.http(0n) ++ "\n"
    ++ Time.iso(951827696n) ++ " " ++ Time.http(951827696n) ++ "\n"
    ++ Time.iso(2147483647n) ++ " " ++ Time.http(2147483647n) ++ "\n"
    ++ Time.iso(Nat.mul(47541n, 86400n)) ++ " " ++ Time.http(Nat.mul(47540n, 86400n)) ++ "\n"
    ++ Time.http(784111777n) ++ " " ++ Time.iso.ms(Nat.add(Nat.mul(951827696n, 1000n), 7n)) ++ "\n"
    ++ ymd.show(Time.date(11016n)) ++ " " ++ day.show(Time.day(2000n, 2n, 29n)) ++ " "
    ++ day.show(Time.day(2100n, 2n, 29n)) ++ " " ++ day.show(Time.day(2023n, 4n, 31n)) ++ " "
    ++ day.show(Time.day(1969n, 12n, 31n)) ++ " " ++ day.show(Time.day(2024n, 13n, 1n)) ++ "\n"
    ++ "round trip misses: " ++ Nat.show(trip(2000n, 0n, 0n)) ++ "\n"
    ++ Nat.show(Time.weekday(11016n)) ++ " " ++ day.show(Time.from(2000n, 2n, 29n, 12n, 34n, 56n)) ++ " "
    ++ day.show(Time.from(2000n, 2n, 29n, 24n, 0n, 0n)) ++ "\n"
    ++ day.show(Time.iso.read(Time.iso(951827696n))) ++ " " ++ day.show(Time.iso.read(Time.iso(2147483647n))) ++ " "
    ++ day.show(Time.iso.read("2000-02-30T00:00:00Z")) ++ " " ++ day.show(Time.iso.read("2000-02-29 12:34:56"))

# an IO main: the interpreter runs it as the JS lane does, on machine
# numbers (a pure main's are the checker's, one unit at a time)
def main() -> IO(Unit):
  IO.print(text())

#|1970-01-01T00:00:00Z Thu, 01 Jan 1970 00:00:00 GMT
#|2000-02-29T12:34:56Z Tue, 29 Feb 2000 12:34:56 GMT
#|2038-01-19T03:14:07Z Tue, 19 Jan 2038 03:14:07 GMT
#|2100-03-01T00:00:00Z Sun, 28 Feb 2100 00:00:00 GMT
#|Sun, 06 Nov 1994 08:49:37 GMT 2000-02-29T12:34:56.007Z
#|2000/2/29 11016 none none none none
#|round trip misses: 0
#|2 951827696 none
#|951827696 2147483647 none none
