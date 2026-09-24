# Time: dates in UTC (no zones, no leap seconds), from seconds or days since
# 1970-01-01: bend2/time.bend over canon's Base, so it runs on released Bend
# too, with the calendar's vectors stated as laws the checker computes.
#
#   import <std>/time.bend as Time
#   Time.iso(951827696n)    # "2000-02-29T12:34:56Z"  (seconds since the epoch)
#   Time.iso.ms(t)          # "2000-02-29T12:34:56.789Z"  (ms since the epoch)
#   Time.http(951827696n)   # "Tue, 29 Feb 2000 12:34:56 GMT"  (IMF-fixdate)
#   Time.date(11016n)       # (2000n, (2n, 29n)): a day from 1970-01-01
#   Time.day(2000n, 2n, 29n) # Some{11016n}, None for a day no month has
#
# The calendar is demos/io_http_engine/cond.bend's, whose LAWS.bend proves
# it (date_round_trip, and the dated vectors): a year counted from 1970
# with the Gregorian leap rule, 1461-day blocks of four years to 2097,
# then whole years and whole months walked. Every number is a Nat, so
# no date overflows. tests/base/time.bend walks the round trip.
import Base

# The calendar
# ============

# year 1970 + k is a leap year by the Gregorian rule
def leap.c(+y: Nat) -> Bool:
  Bool.not(Nat.is_eq(Nat.mod(y, 100n), 0n)) || Nat.is_eq(Nat.mod(y, 400n), 0n)

def leap.at(q: Bool, +y: Nat) -> Bool:
  match q:
    case True{}:
      leap.c(y)
    case False{}:
      False{}

def leap(k: Nat) -> Bool:
  +y = Nat.add(k, 1970n)
  leap.at(Nat.is_eq(Nat.mod(y, 4n), 0n), y)

def ylen(k: Nat) -> Nat:
  Bool.pick(Nat, leap(k), 366n, 365n)

# the months' lengths, January first
def mlens(lp: Bool) -> List<&2, Nat>:
  match lp:
    case True{}:
      [31n, 29n, 31n, 30n, 31n, 30n, 31n, 31n, 30n, 31n, 30n, 31n]
    case False{}:
      [31n, 28n, 31n, 30n, 31n, 30n, 31n, 31n, 30n, 31n, 30n, 31n]

# the days before year k
def before(+k: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+j:
      Nat.add(before(j), ylen(j))

# day rem of a year as a month and a day of it (both from 0): each month
# taken whole while rem is past it (l its length, t the months after it)
def mon.up(jd: Nat & Nat) -> Nat & Nat:
  (j, d) = jd
  (1n+j, d)

def mon(t: List<&2, Nat>, +l: Nat, fits: Bool, +rem: Nat) -> Nat & Nat:
  match t:
    case Nil{}:
      (0n, rem)
    case Con{+l2, t2}:
      match fits:
        case True{}:
          (0n, rem)
        case False{}:
          +r2 = Nat.sub(rem, l)
          mon.up(mon(t2, l2, Nat.is_lt(r2, l2), r2))

def mon.of(ls: List<&2, Nat>, +rem: Nat) -> Nat & Nat:
  match ls:
    case Nil{}:
      (0n, rem)
    case Con{+l, t}:
      mon(t, l, Nat.is_lt(rem, l), rem)

# day rem from year k on: each year taken whole while rem is past it (yl
# its length); f bounds the walk
def cal(f: Nat, fits: Bool, +rem: Nat, +k: Nat, +yl: Nat) -> Nat & Nat & Nat:
  match f:
    case 0n:
      (k, (0n, rem))
    case 1n+g:
      match fits:
        case True{}:
          (k, mon.of(mlens(leap(k)), rem))
        case False{}:
          +r2 = Nat.sub(rem, yl)
          +y2 = ylen(1n+k)
          cal(g, Nat.is_lt(r2, y2), r2, 1n+k, y2)

# whole blocks of four years first: each of the first 32 has 1461 days
def blk(f: Nat, ok: Bool, +q: Nat, +k: Nat, +rem: Nat) -> Nat & Nat:
  match f:
    case 0n:
      (k, rem)
    case 1n+g:
      match ok:
        case True{}:
          +r2 = Nat.sub(rem, 1461n)
          blk(g, Nat.is_lt(1n+q, 32n) && Nat.is_le(1461n, r2), 1n+q, 1n+1n+1n+1n+k, r2)
        case False{}:
          (k, rem)

def civil.from(kr: Nat & Nat) -> Nat & Nat & Nat:
  (+k, +r) = kr
  +y = ylen(k)
  cal(1n+r, Nat.is_lt(r, y), r, k, y)

# a day as its year from 1970, month from 0 and day of the month from 0
def civil(+days: Nat) -> Nat & Nat & Nat:
  civil.from(blk(32n, Nat.is_le(1461n, days), 0n, 0n, days))

# ... and back: the days before a day of a month, when the month has it
def mdays.fit(ok: Bool, d: Nat) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      Some{d}
    case False{}:
      None{}

def mdays.add(+l: Nat, m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      Some{Nat.add(l, x)}

def mdays(ls: List<&2, Nat>, j: Nat, +d: Nat) -> Maybe<&2, Nat>:
  match ls:
    case Nil{}:
      None{}
    case Con{+l, t}:
      match j:
        case 0n:
          mdays.fit(Nat.is_lt(d, l), d)
        case 1n+i:
          mdays.add(l, mdays(t, i, d))

# Dates
# =====

def date.of(kjd: Nat & Nat & Nat) -> Nat & Nat & Nat:
  (k, jd) = kjd
  (j, d) = jd
  (Nat.add(k, 1970n), (1n+j, 1n+d))

# a day (from 1970-01-01) as its year, month (1 to 12) and day (1 to 31)
def date(+days: Nat) -> Nat & Nat & Nat:
  date.of(civil(days))

def day.at(ok: Bool, +k: Nat, +m: Nat, +d: Nat) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      mdays.add(before(k), mdays(mlens(leap(k)), Nat.sub(m, 1n), Nat.sub(d, 1n)))
    case False{}:
      None{}

# the day a date is, from 1970-01-01: None before 1970, or for a day its
# month does not have
def day(+y: Nat, +m: Nat, +d: Nat) -> Maybe<&2, Nat>:
  day.at(Nat.is_le(1970n, y) && Nat.is_le(1n, m) && Nat.is_le(1n, d), Nat.sub(y, 1970n), m, d)

# Text
# ====

def zeros(k: Nat, s: String) -> String:
  match k:
    case 0n:
      s
    case 1n+j:
      zeros(j, SCon{'0', s})

# n in decimal, zeros in front to w places
def pad(+w: Nat, +n: Nat) -> String:
  +s = Nat.show(n)
  zeros(Nat.sub(w, String.length(s)), s)

def nth(xs: List<&2, String>, i: Nat) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, t}:
      match i:
        case 0n:
          x
        case 1n+j:
          nth(t, j)

# a second of a day as HH:MM:SS
def hms(+s: Nat) -> String:
  pad(2n, Nat.div(s, 3600n)) ++ ":" ++ pad(2n, Nat.mod(Nat.div(s, 60n), 60n)) ++ ":" ++ pad(2n, Nat.mod(s, 60n))

def iso.ymd(ymd: Nat & Nat & Nat) -> String:
  (y, md) = ymd
  (m, d) = md
  pad(4n, y) ++ "-" ++ pad(2n, m) ++ "-" ++ pad(2n, d)

def iso.of(ds: Nat & Nat) -> String:
  (days, s) = ds
  iso.ymd(date(days)) ++ "T" ++ hms(s)

# seconds since the epoch as ISO 8601 in UTC: 2000-02-29T12:34:56Z
def iso(t: Nat) -> String:
  iso.of(Nat.divmod(t, 86400n)) ++ "Z"

# ms since the epoch as ISO 8601 in UTC: ...T12:34:56.789Z
def iso.ms(+t: Nat) -> String:
  iso.of(Nat.divmod(Nat.div(t, 1000n), 86400n)) ++ "." ++ pad(3n, Nat.mod(t, 1000n)) ++ "Z"

def wkc() -> List<&2, String>:
  ["Thu, ", "Fri, ", "Sat, ", "Sun, ", "Mon, ", "Tue, ", "Wed, "]

def monc() -> List<&2, String>:
  ["Jan ", "Feb ", "Mar ", "Apr ", "May ", "Jun ", "Jul ", "Aug ", "Sep ", "Oct ", "Nov ", "Dec "]

def http.ymd(ymd: Nat & Nat & Nat) -> String:
  (y, md) = ymd
  (m, d) = md
  pad(2n, d) ++ " " ++ nth(monc(), Nat.sub(m, 1n)) ++ pad(4n, y)

def http.of(ds: Nat & Nat) -> String:
  (+days, s) = ds
  nth(wkc(), Nat.mod(days, 7n)) ++ http.ymd(date(days)) ++ " " ++ hms(s) ++ " GMT"

# seconds since the epoch as an IMF-fixdate (RFC 9110 5.6.7): the HTTP
# Date, Last-Modified and Expires form, Tue, 29 Feb 2000 12:34:56 GMT
def http(t: Nat) -> String:
  http.of(Nat.divmod(t, 86400n))

# a day's weekday, 0 for Sunday to 6 for Saturday (1970-01-01 was a Thursday)
def weekday(+days: Nat) -> Nat:
  Nat.mod(Nat.add(days, 4n), 7n)

def from.at(m: Maybe<&2, Nat>, +s: Nat) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{d}:
      Some{Nat.add(Nat.mul(d, 86400n), s)}

def from.ok(ok: Bool, +y: Nat, +mo: Nat, +d: Nat, +s: Nat) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      from.at(day(y, mo, d), s)
    case False{}:
      None{}

# a date and a time of day as seconds since the epoch: None for a day no
# month has, a year before 1970, or an hour, minute or second out of range
def from(+y: Nat, +mo: Nat, +d: Nat, +h: Nat, +mi: Nat, +s: Nat) -> Maybe<&2, Nat>:
  from.ok(Nat.is_lt(h, 24n) && Nat.is_lt(mi, 60n) && Nat.is_lt(s, 60n), y, mo, d,
    Nat.add(Nat.add(Nat.mul(h, 3600n), Nat.mul(mi, 60n)), s))

# Reading
# =======

type Rd is Data:
  Rd{rest: String, ok: Bool}

def dig(c: U32) -> Nat:
  U32.to_nat(U32.sub(c, 48))

def is_dig(+c: U32) -> Bool:
  U32.is_le(48, c) && U32.is_le(c, 57)

# k decimal places from the front of s, and the rest
def num(k: Nat, s: String, +acc: Nat, ok: Bool) -> Nat & Rd:
  match k s:
    case 0n _:
      (acc, Rd{s, ok})
    case 1n+j SNil{}:
      (acc, Rd{SNil{}, False{}})
    case 1n+j SCon{Chr{+c}, t}:
      num(j, t, Nat.add(Nat.mul(acc, 10n), dig(c)), ok && is_dig(c))

def lit(+c: U32, r: Rd) -> Rd:
  match r:
    case Rd{s, ok}:
      match s:
        case SNil{}:
          Rd{SNil{}, False{}}
        case SCon{Chr{+x}, t}:
          Rd{t, ok && U32.is_eq(x, c)}

def iso.end(r: Rd) -> Bool:
  match r:
    case Rd{s, ok}:
      ok && String.is_empty(s)


def num.rd(k: Nat, r: Rd) -> Nat & Rd:
  match r:
    case Rd{s, ok}:
      num(k, s, 0n, ok)

def read.fin(ok: Bool, +y: Nat, +mo: Nat, +d: Nat, +h: Nat, +mi: Nat, +s: Nat) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      from(y, mo, d, h, mi, s)
    case False{}:
      None{}

# ISO 8601 as iso writes it, YYYY-MM-DDTHH:MM:SSZ, as seconds since the
# epoch: None for any other text, or for a date or time that is not one
def read.s(+y: Nat, +mo: Nat, +d: Nat, +h: Nat, +mi: Nat, p: Nat & Rd) -> Maybe<&2, Nat>:
  (+sec, r) = p
  read.fin(iso.end(lit(90, r)), y, mo, d, h, mi, sec)

def read.mi(+y: Nat, +mo: Nat, +d: Nat, +h: Nat, p: Nat & Rd) -> Maybe<&2, Nat>:
  (+mi, r) = p
  read.s(y, mo, d, h, mi, num.rd(2n, lit(58, r)))

def read.h(+y: Nat, +mo: Nat, +d: Nat, p: Nat & Rd) -> Maybe<&2, Nat>:
  (+h, r) = p
  read.mi(y, mo, d, h, num.rd(2n, lit(58, r)))

def read.d(+y: Nat, +mo: Nat, p: Nat & Rd) -> Maybe<&2, Nat>:
  (+d, r) = p
  read.h(y, mo, d, num.rd(2n, lit(84, r)))

def read.mo(+y: Nat, p: Nat & Rd) -> Maybe<&2, Nat>:
  (+mo, r) = p
  read.d(y, mo, num.rd(2n, lit(45, r)))

def read.y(p: Nat & Rd) -> Maybe<&2, Nat>:
  (+y, r) = p
  read.mo(y, num.rd(2n, lit(45, r)))

def iso.read(s: String) -> Maybe<&2, Nat>:
  read.y(num(4n, s, 0n, True{}))

# The laws
# ========
#
# The calendar by known days (and seconds of the day), computed by the
# checker: RFC 9110's own example, leap days in 2000 (a century that is
# one) and 2024, 2100 (a century that is not), the epoch, a year's last
# second, the last second a U32 holds; days no month has; weekdays; and
# reading back what iso writes.

law http_rfc_example:
  {http.of((9075n, 31777n)) == "Sun, 06 Nov 1994 08:49:37 GMT" : String}

def http_rfc_example():
  {==}

law leap_2000:
  {iso.of((11016n, 0n)) ++ " " ++ http.of((11016n, 0n)) ==
    "2000-02-29T00:00:00 Tue, 29 Feb 2000 00:00:00 GMT" : String}

def leap_2000():
  {==}

law leap_2024:
  {http.of((19782n, 45296n)) == "Thu, 29 Feb 2024 12:34:56 GMT" : String}

def leap_2024():
  {==}

law no_leap_2100:
  {http.of((47541n, 0n)) == "Mon, 01 Mar 2100 00:00:00 GMT" : String}

def no_leap_2100():
  {==}

law epoch:
  {iso.of((0n, 0n)) == "1970-01-01T00:00:00" : String}

def epoch():
  {==}

law year_end:
  {http.of((1095n, 86399n)) == "Sun, 31 Dec 1972 23:59:59 GMT" : String}

def year_end():
  {==}

law last_u32:
  {iso.of((49710n, 23295n)) == "2106-02-07T06:28:15" : String}

def last_u32():
  {==}

law days_back:
  {(day(2000n, 2n, 29n), (day(2100n, 2n, 29n), (day(2023n, 4n, 31n), day(1969n, 12n, 31n)))) ==
    (Some{11016n}, (None{}, (None{}, None{}))) :
    Maybe<&2, Nat> & (Maybe<&2, Nat> & (Maybe<&2, Nat> & Maybe<&2, Nat>))}

def days_back():
  {==}

law weekdays:
  {(weekday(0n), (weekday(9075n), weekday(11016n))) == (4n, (0n, 2n)) : Nat & (Nat & Nat)}

def weekdays():
  {==}

law read_back:
  {(iso.read("1970-01-01T00:01:01Z"), (iso.read("1970-02-30T00:00:00Z"),
    (iso.read("1970-01-01T24:00:00Z"), iso.read("1970-01-01 00:00:00")))) ==
    (Some{61n}, (None{}, (None{}, None{}))) :
    Maybe<&2, Nat> & (Maybe<&2, Nat> & (Maybe<&2, Nat> & Maybe<&2, Nat>))}

def read_back():
  {==}
