# Time: IO.wall's dates in UTC, std/time.bend's by this path (the rest of
# it, iso.read, from and weekday, is there)
import Base
import ../std/time.bend as T

# 951827696n as 2000-02-29T12:34:56Z
def iso(t: Nat) -> String:
  T.iso(t)

# ms, as IO.wall answers: ...T12:34:56.789Z
def iso.ms(t: Nat) -> String:
  T.iso.ms(t)

# Tue, 29 Feb 2000 12:34:56 GMT
def http(t: Nat) -> String:
  T.http(t)

# day 11016n as (2000n, (2n, 29n))
def date(n: Nat) -> Nat & Nat & Nat:
  T.date(n)

# ... and back: Some{11016n}, None for a day no month has or before 1970
def day(y: Nat, m: Nat, d: Nat) -> Maybe<&2, Nat>:
  T.day(y, m, d)
