# The wall clock and the dates it prints.
#
# Base's IO.now is monotonic (ms since boot): good for latency and
# deadlines, useless for a log line that outlives the process. Clock.wall
# is a foreign effect (clock.c, clock.js) answering ms since the Unix
# epoch, and iso(t) prints one as 2026-09-24T15:58:13.426Z: Base has no
# date formatting, so this is Howard Hinnant's civil_from_days by hand.
import Base

def Clock.wall() -> IO(Nat):
  import "./clock.c"
  import "./clock.js"

def two(+n: Nat) -> String:
  String.pad_start(Nat.show(n), 2n, '0')

def three(+n: Nat) -> String:
  String.pad_start(Nat.show(n), 3n, '0')

# a day of the proleptic Gregorian calendar (from 1970-01-01), as
# yyyy-mm-dd; z, era, doe, yoe, doy, mp are civil_from_days's names
def date.ymd(+yoe: Nat, +era: Nat, +doe: Nat) -> String:
  +doy = Nat.sub(doe, Nat.sub(Nat.add(Nat.mul(365n, yoe), Nat.div(yoe, 4n)), Nat.div(yoe, 100n)))
  +mp = Nat.div(Nat.add(Nat.mul(5n, doy), 2n), 153n)
  +d = Nat.add(Nat.sub(doy, Nat.div(Nat.add(Nat.mul(153n, mp), 2n), 5n)), 1n)
  +m = Bool.pick(Nat, Nat.is_lt(mp, 10n), Nat.add(mp, 3n), Nat.sub(mp, 9n))
  +y = Nat.add(Nat.add(yoe, Nat.mul(era, 400n)), Bool.pick(Nat, Nat.is_le(m, 2n), 1n, 0n))
  Nat.show(y) ++ "-" ++ two(m) ++ "-" ++ two(d)

def date(+days: Nat) -> String:
  +z = Nat.add(days, 719468n)
  +era = Nat.div(z, 146097n)
  +doe = Nat.sub(z, Nat.mul(era, 146097n))
  +yoe = Nat.div(Nat.sub(Nat.add(Nat.sub(doe, Nat.div(doe, 1460n)), Nat.div(doe, 36524n)), Nat.div(doe, 146096n)), 365n)
  date.ymd(yoe, era, doe)

# ms since the epoch, as ISO 8601 in UTC
def iso(+t: Nat) -> String:
  +s = Nat.div(t, 1000n)
  +day = Nat.mod(s, 86400n)
  date(Nat.div(s, 86400n)) ++ "T" ++ two(Nat.div(day, 3600n)) ++ ":" ++ two(Nat.mod(Nat.div(day, 60n), 60n))
    ++ ":" ++ two(Nat.mod(day, 60n)) ++ "." ++ three(Nat.mod(t, 1000n)) ++ "Z"
