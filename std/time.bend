# Time: UTC dates (no zones, no leap seconds) of seconds or days since
# 1970-01-01, on canon's Base (released Bend runs it; bend2/time.bend is
# it). Closed form, Hinnant's civil_from_days as Neri and Schneider write
# it, on U32 from 0000-03-01: good to about the year 2,900,000, and
# tests/std/time_check.py checks every day to 9999-12-31.
import Base

# day n (from 1970-01-01) as its year, month and day (from 1)
def civil(n: U32) -> U32 & U32 & U32:
  +a = ((n + 719468) * 4 + 3 : U32)
  +b = (a % 146097 .|. 3 : U32)
  +g = (b % 1461 / 4 * 5 + 461 : U32)
  +m = (g / 153 : U32)
  ((a / 146097 * 100 + b / 1461 + m / 13 : U32), ((m - 1) % 12 + 1 : U32), (g % 153 / 5 + 1 : U32))

# ... and back, from 1970 on (a month or day out of range runs on)
def days(y: U32, m: U32, d: U32) -> U32:
  +k = (y * 12 + m - 3 : U32)
  +z = (k / 12 : U32)
  (z * 365 + z / 4 - z / 100 + z / 400 + (k % 12 * 153 + 2) / 5 + d - 719469 : U32)

def nat3(c: U32 & U32 & U32) -> Nat & Nat & Nat:
  (y, m, d) = c
  (U32.to_nat(y), U32.to_nat(m), U32.to_nat(d))

# (2000n, (2n, 29n)) of day 11016n
def date(n: Nat) -> Nat & Nat & Nat:
  nat3(civil(U32.from_nat(n)))

def day.is(+y: Nat, +m: Nat, +d: Nat, c: Nat & Nat & Nat) -> Bool:
  (a, b, e) = c
  Nat.is_le(1970n, y) && Nat.is_eq(a, y) && Nat.is_eq(b, m) && Nat.is_eq(e, d)

# Some{11016n} of 2000-02-29: None before 1970 or for a day no month has
def day(+y: Nat, +m: Nat, +d: Nat) -> Maybe<&2, Nat>:
  +n = days(U32.from_nat(y), U32.from_nat(m), U32.from_nat(d))
  Bool.pick(Maybe<&2, Nat>, day.is(y, m, d, nat3(civil(n))), Some{U32.to_nat(n)}, None{})

# 0 for a Sunday
def weekday(n: Nat) -> Nat:
  Nat.mod(Nat.add(n, 4n), 7n)

# a date and time as seconds since the epoch, None if either is not one
def from(+y: Nat, +mo: Nat, +d: Nat, +h: Nat, +mi: Nat, +s: Nat) -> Maybe<&2, Nat>:
  Maybe.bind(&2, Nat, Nat, day(y, mo, d), n => Bool.pick(Maybe<&2, Nat>,
    Nat.is_lt(h, 24n) && Nat.is_lt(mi, 60n) && Nat.is_lt(s, 60n),
    Some{Nat.add(Nat.mul(Nat.add(Nat.mul(Nat.add(Nat.mul(n, 24n), h), 60n), mi), 60n), s)}, None{}))

# Text is written back to front onto one tail, a char at a time (on our
# runtime, in place)

# k decimal places of n, before s
def dg(k: Nat, +n: U32, s: String) -> String:
  match k:
    case 0n:
      s
    case 1n+j:
      dg(j, (n / 10 : U32), SCon{Chr{(n % 10 + 48 : U32)}, s})

# p before s
def pre(p: String, s: String) -> String:
  match p:
    case SNil{}:
      s
    case SCon{h, t}:
      SCon{h, pre(t, s)}

# the weekdays from Sunday, then the months from January
def name(i: U32, s: String) -> String:
  pre(String.take(String.drop("SunMonTueWedThuFriSatJanFebMarAprMayJunJulAugSepOctNovDec",
    U32.to_nat((i * 3 : U32))), 3n), s)

def hms(+s: U32, t: String) -> String:
  dg(2n, (s / 3600 : U32), SCon{':', dg(2n, (s / 60 % 60 : U32), SCon{':', dg(2n, (s % 60 : U32), t)})})

def iso.ymd(c: U32 & U32 & U32, t: String) -> String:
  (y, m, d) = c
  pre(U32.show(y), SCon{'-', dg(2n, m, SCon{'-', dg(2n, d, t)})})

# day n at second s, then t
def iso.at(n: U32, s: U32, t: String) -> String:
  iso.ymd(civil(n), SCon{'T', hms(s, t)})

def iso.t(+t: Nat, e: String) -> String:
  iso.at(U32.from_nat(Nat.div(t, 86400n)), U32.from_nat(Nat.mod(t, 86400n)), e)

def iso(t: Nat) -> String:
  iso.t(t, "Z")

def iso.ms(+t: Nat) -> String:
  iso.t(Nat.div(t, 1000n), SCon{'.', dg(3n, U32.from_nat(Nat.mod(t, 1000n)), "Z")})

def http.dmy(c: U32 & U32 & U32, t: String) -> String:
  (y, m, d) = c
  dg(2n, d, SCon{' ', name((m + 6 : U32), SCon{' ', pre(U32.show(y), t)})})

def http.at(+n: U32, s: U32) -> String:
  name(((n + 4) % 7 : U32), SCon{',', SCon{' ', http.dmy(civil(n), SCon{' ', hms(s, " GMT")})}})

# IMF-fixdate (RFC 9110 5.6.7): HTTP's Date, Last-Modified and Expires
def http(+t: Nat) -> String:
  http.at(U32.from_nat(Nat.div(t, 86400n)), U32.from_nat(Nat.mod(t, 86400n)))

def f2(+x: U32, k: U32) -> Nat:
  U32.to_nat((x / k % 100 : U32))

# YYYYMMDD and HHMMSS as a date, if the text was one
def read(ok: Bool, +a: U32, +b: U32) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      from(U32.to_nat((a / 10000 : U32)), f2(a, 100), f2(a, 1), f2(b, 10000), f2(b, 100), f2(b, 1))
    case False{}:
      None{}

# s against the pattern p (d a digit), the digits before its T in hi
def rd(p: String, s: String, +hi: U32, +lo: U32, ok: Bool) -> Maybe<&2, Nat>:
  match p s:
    case SNil{} SNil{}:
      read(ok, hi, lo)
    case SCon{Chr{+q}, pt} SCon{Chr{+c}, st}:
      +x = U32.is_eq(q, 84)
      +g = U32.is_eq(q, 100)
      rd(pt, st, Bool.pick(U32, x, lo, hi), Bool.pick(U32, x, 0, Bool.pick(U32, g, (lo * 10 + c - 48 : U32), lo)),
        ok && Bool.pick(Bool, g, U32.is_lt((c - 48 : U32), 10), U32.is_eq(c, q)))
    case _ _:
      None{}

# YYYY-MM-DDTHH:MM:SSZ, as iso writes it, as seconds since the epoch
def iso.read(s: String) -> Maybe<&2, Nat>:
  rd("dddd-dd-ddTdd:dd:ddZ", s, 0, 0, True{})

# The laws: the epoch, RFC 9110's example, 2000's leap day, 2100's none,
# the last I32 second, 9999's last; days and text that are not one

def sh(m: Maybe<&2, Nat>) -> String:
  " " ++ Maybe.show(&2, Nat, Nat.show, m)

law vectors:
  {iso.at(0, 0, " ") ++ http.at(9075, 31777) ++ " " ++ http.at(11016, 0) ++ " " ++ http.at(47541, 0) ++ " "
    ++ iso.at(24855, 11647, " ") ++ iso.at(2932896, 86399, " ") ++ U32.show(days(9999, 12, 31))
    ++ sh(day(2000n, 2n, 29n)) ++ sh(day(2100n, 2n, 29n)) ++ sh(day(1969n, 12n, 31n)) ++ sh(day(2024n, 13n, 1n))
    ++ sh(day(2024n, 1n, 0n)) ++ " " ++ Nat.show(weekday(9075n)) ++ " " ++ iso.ms(61007n) ==
    "1970-01-01T00:00:00 Sun, 06 Nov 1994 08:49:37 GMT Tue, 29 Feb 2000 00:00:00 GMT Mon, 01 Mar 2100 00:00:00 GMT "
    ++ "2038-01-19T03:14:07 9999-12-31T23:59:59 2932896 Some(11016) None None None None 0 1970-01-01T00:01:01.007Z" : String}

def vectors():
  {==}

law read_back:
  {sh(iso.read("1970-01-01T00:01:01Z")) ++ sh(iso.read("1970-04-31T00:00:00Z")) ++ sh(iso.read("1970-01-01T24:00:00Z"))
    ++ sh(iso.read("1970-01-01T00:00:60Z")) ++ sh(iso.read("1970-01-01 00:00:00Z")) ++ sh(iso.read("1970-1-01T00:00:00Z"))
    ++ sh(iso.read("1970-01-01T00:00:0:Z")) == " Some(61) None None None None None None" : String}

def read_back():
  {==}
