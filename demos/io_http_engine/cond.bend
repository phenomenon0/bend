# A static file, conditionally and in part: RFC 9110 8.8 (validators),
# 13 (conditional requests), 14 (range requests), 15.3.7 (206), 15.4.5
# (304), 15.5.13 (412), 15.5.17 (416).
#
# What a GET or HEAD of a file gets is decided from the file's size and
# mtime, which only the open file knows, and the request's fields, so it
# is bend-wire's ~fhead hook (main.bend's h.fhead): the head, and which
# of the file's bytes follow it (L.Fr). This file is that decision, pure,
# and what it reads and writes on the way:
#
# - the validators: an entity-tag of the mtime and the size in hex, as
#   nginx writes it ("65e079f0-3e8"), and Last-Modified, the mtime as an
#   IMF-fixdate, by a calendar of whole years and months (date.fmt), and
#   the date read back from any of the three forms RFC 9110 5.6.7 has a
#   recipient accept (date.read);
# - the preconditions, in RFC 9110 13.2.2's order: If-Match, else
#   If-Unmodified-Since (412 when false); If-None-Match, else
#   If-Modified-Since (304 when false);
# - the range: one "bytes=" range-spec that the file satisfies is a 206
#   of exactly those bytes, none it satisfies a 416, a Range that is not
#   one of RFC 9110 14.1.1's forms is ignored, and If-Range lets the
#   range through only when its validator is the file's.
#
# The entity-tag is nginx's so that caches and clients that already hold
# one keep matching. It is sent strong, as nginx sends it, but it is a
# weak validator in truth: two versions of a file written within one
# second at the same size share it (RFC 9110 8.8.1). Weak comparison
# (If-None-Match) is what it is fit for; If-Range and If-Match compare
# it strongly, as RFC 9110 asks and nginx does.
#
# Every number here is a Nat: a machine word when compiled, and a chain
# the checker can reason about, which is what lets LAWS.bend prove the
# calendar, the heads and the byte counts for every mtime and every size.
# The checker counts in unary, and compares a number it has counted one
# unit at a time, so no closed number here is large: a day is split by
# 60, 60 and 24, never by 86400; the calendar has no checkpoint past
# 1970; and a sum puts its small side first.
import Base
import ../../wire/reader.bend as Wr
import ../../wire/loop.bend as L

# Digits
# ======
#
# A head is built where it grows: each piece appended to, or each byte
# pushed onto, the one buffer the head is, in place. What a piece is is
# also written as its own bytes (d2, date.fmt, etag.of), and LAWS.bend
# says the two are the same bytes, so the laws about the pieces are laws
# about the heads.

# the byte of a digit
def dig(d: Nat) -> U32:
  U32.from_nat(Nat.add(48n, d))

# a number under 100 as its two digits
def d2.qr(ab: Nat & Nat) -> Bytes():
  (a, b) = ab
  SCon{Chr{dig(a)}, SCon{Chr{dig(b)}, SNil{}}}

def d2(n: Nat) -> Bytes():
  d2.qr(Nat.divmod(n, 10n))

# ... pushed where a head grows
def p2.qr(acc: Bytes(), ab: Nat & Nat) -> Bytes():
  (a, b) = ab
  Bytes.push(Bytes.push(acc, dig(a)), dig(b))

def p2(acc: Bytes(), n: Nat) -> Bytes():
  p2.qr(acc, Nat.divmod(n, 10n))

# the byte of a digit in any base up to 16: 0-9, then a-f
def hdig(+d: Nat) -> U32:
  U32.from_nat(Bool.pick(Nat, Nat.is_lt(d, 10n), Nat.add(48n, d), Nat.add(87n, d)))

# a number's digits in base b, from the top, each a quotient and a
# remainder by b (f bounds them), pushed where a head grows
def num.go(f: Nat, +b: Nat, acc: Bytes(), qr: Nat & Nat) -> Bytes():
  match f:
    case 0n:
      acc
    case 1n+g:
      (q, +r) = qr
      match q:
        case 0n:
          Bytes.push(acc, hdig(r))
        case 1n+p:
          Bytes.push(num.go(g, b, acc, Nat.divmod(1n+p, b)), hdig(r))

# in decimal, and as its own bytes
def num.into(acc: Bytes(), n: Nat) -> Bytes():
  num.go(20n, 10n, acc, Nat.divmod(n, 10n))

def num(n: Nat) -> Bytes():
  num.into("", n)

# a 32-bit number in lowercase hex with no leading zeros: its nibbles
# from the top, each pushed once one has been (on) or it is not zero or
# it is the last; the walk is a loop, so a head pays no frame per digit
def nib(+x: U32, +g: Nat) -> U32:
  U32.and(U32.shrn(x, Nat.mul(4n, g)), 15)

def hex.on(+x: U32, +g: Nat) -> Bool:
  U32.is_lt(0, nib(x, Nat.sub(g, 1n))) || Nat.is_le(g, 1n)

def hex.go(+f: Nat, on: Bool, +x: U32, acc: Bytes()) -> Bytes():
  match f:
    case 0n:
      acc
    case 1n+g:
      match on:
        case True{}:
          hex.go(g, True{}, x, Bytes.push(acc, hdig(U32.to_nat(nib(x, g)))))
        case False{}:
          hex.go(g, hex.on(x, g), x, acc)

def hex(acc: Bytes(), +x: U32) -> Bytes():
  hex.go(8n, hex.on(x, 8n), x, acc)

# The calendar
# ============
#
# A year is counted from 1970 (k is the year 1970 + k), and is a leap
# year by the Gregorian rule. A day is counted from 1970-01-01.
def leap.c(+y: Nat) -> Bool:
  Bool.not(Nat.is_eq(Nat.mod(y, 100n), 0n)) || Nat.is_eq(Nat.mod(y, 400n), 0n)

# the century is looked at only in a year divisible by four
def leap.at(q: Bool, +y: Nat) -> Bool:
  match q:
    case True{}:
      leap.c(y)
    case False{}:
      False{}

def leap.of(+y: Nat) -> Bool:
  leap.at(Nat.is_eq(Nat.mod(y, 4n), 0n), y)

def leap(k: Nat) -> Bool:
  leap.of(Nat.add(k, 1970n))

def ylen.of(lp: Bool) -> Nat:
  Bool.pick(Nat, lp, 366n, 365n)

def ylen(k: Nat) -> Nat:
  ylen.of(leap(k))

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

# day rem of a year, as a month (0 for January) and a day of it (0 for
# the first): the months are walked, each taken whole while rem is past
# it (l is this month's length, fits whether rem is within it, t the
# months after it; the last month takes what is left)
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

# day rem from year k on, as a year, a month and a day: the years are
# walked, each taken whole while rem is past it (yl is year k's length,
# and fits says whether rem is within it). f bounds the walk; the day's
# own number bounds the years it can span, since every year has a day.
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

# a day's year (from 1970), month (from 0) and day of the month (from 0).
# The walk takes whole blocks of four years first: each of the first 32
# from 1970 (to 2097) has 1461 days, its third year a leap year (2000
# being one); q counts the blocks taken, k the years, and ok says whether
# the next block is one of them and within rem. What is left is walked a
# year at a time.
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

def civil(+days: Nat) -> Nat & Nat & Nat:
  civil.from(blk(32n, Nat.is_lt(0n, 32n) && Nat.is_le(1461n, days), 0n, 0n, days))

# ... and back: the days before a day of a month of a year, when there
# is such a day
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

# a month and a day of it, as one
def mdays.p(ls: List<&2, Nat>, jd: Nat & Nat) -> Maybe<&2, Nat>:
  (j, d) = jd
  mdays(ls, j, d)

def days.of(+k: Nat, jd: Nat & Nat) -> Maybe<&2, Nat>:
  mdays.add(before(k), mdays.p(mlens(leap(k)), jd))

# Names
# =====
#
# Each with what follows it in the form that uses it: IMF-fixdate's
# weekday and its comma, its month and its space; rfc850-date's long
# weekday and its comma, its bare month; asctime-date's weekday and its
# space.
def wkc() -> List<&2, Bytes()>:
  ["Sun, ", "Mon, ", "Tue, ", "Wed, ", "Thu, ", "Fri, ", "Sat, "]

def wkl() -> List<&2, Bytes()>:
  ["Sunday, ", "Monday, ", "Tuesday, ", "Wednesday, ", "Thursday, ", "Friday, ", "Saturday, "]

def wks() -> List<&2, Bytes()>:
  ["Sun ", "Mon ", "Tue ", "Wed ", "Thu ", "Fri ", "Sat "]

def monc() -> List<&2, Bytes()>:
  ["Jan ", "Feb ", "Mar ", "Apr ", "May ", "Jun ", "Jul ", "Aug ", "Sep ", "Oct ", "Nov ", "Dec "]

def mon3() -> List<&2, Bytes()>:
  ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"]

def nth(xs: List<&2, Bytes()>, i: Nat) -> Bytes():
  match xs:
    case Nil{}:
      ""
    case Con{x, t}:
      match i:
        case 0n:
          x
        case 1n+j:
          nth(t, j)

# IMF-fixdate
# ===========
#
# "Sun, 06 Nov 1994 08:49:37 GMT" (RFC 9110 5.6.7), from seconds since
# the epoch: the seconds split into minutes and a second, the minutes
# into hours and a minute, the hours into days and an hour; the day's
# weekday (1970-01-01 was a Thursday) and its place in the calendar.
# date.fmt is its bytes, the pieces joined; date.into writes the same
# bytes where a head grows.
def date.y(yy: Nat & Nat, tail: List<&2, Bytes()>) -> List<&2, Bytes()>:
  (a, b) = yy
  Con{d2(a), Con{d2(b), Con{" ", tail}}}

def date.ymd(ymd: Nat & Nat & Nat, tail: List<&2, Bytes()>) -> List<&2, Bytes()>:
  (k, jd) = ymd
  (j, d) = jd
  Con{d2(1n+d), Con{" ", Con{nth(monc(), j), date.y(Nat.divmod(Nat.add(k, 1970n), 100n), tail)}}}

def date.ds(+days: Nat, +h: Nat, +m: Nat, +x: Nat) -> List<&2, Bytes()>:
  Con{nth(wkc(), Nat.mod(Nat.add(4n, days), 7n)),
    date.ymd(civil(days), [d2(h), ":", d2(m), ":", d2(x), " GMT"])}

def date.q3(+m: Nat, +x: Nat, dh: Nat & Nat) -> Bytes():
  (days, h) = dh
  Bytes.concat(date.ds(days, h, m, x))

def date.q2(+x: Nat, hm: Nat & Nat) -> Bytes():
  (hs, m) = hm
  date.q3(m, x, Nat.divmod(hs, 24n))

def date.q1(mx: Nat & Nat) -> Bytes():
  (ms, x) = mx
  date.q2(x, Nat.divmod(ms, 60n))

def date.fmt(t: Nat) -> Bytes():
  date.q1(Nat.divmod(t, 60n))

def di.y(acc: Bytes(), yy: Nat & Nat) -> Bytes():
  (a, b) = yy
  Bytes.push(p2(p2(acc, a), b), 32)

def di.ymd(acc: Bytes(), ymd: Nat & Nat & Nat) -> Bytes():
  (k, jd) = ymd
  (j, d) = jd
  di.y(Bytes.append(Bytes.push(p2(acc, 1n+d), 32), nth(monc(), j)),
    Nat.divmod(Nat.add(k, 1970n), 100n))

def di.ds(acc: Bytes(), +days: Nat, +h: Nat, +m: Nat, +x: Nat) -> Bytes():
  Bytes.append(p2(Bytes.push(p2(Bytes.push(p2(
    di.ymd(Bytes.append(acc, nth(wkc(), Nat.mod(Nat.add(4n, days), 7n))), civil(days)),
      h), 58), m), 58), x), " GMT")

def di.q3(acc: Bytes(), +m: Nat, +x: Nat, dh: Nat & Nat) -> Bytes():
  (days, h) = dh
  di.ds(acc, days, h, m, x)

def di.q2(acc: Bytes(), +x: Nat, hm: Nat & Nat) -> Bytes():
  (hs, m) = hm
  di.q3(acc, m, x, Nat.divmod(hs, 24n))

def di.q1(acc: Bytes(), mx: Nat & Nat) -> Bytes():
  (ms, x) = mx
  di.q2(acc, x, Nat.divmod(ms, 60n))

def date.into(acc: Bytes(), t: Nat) -> Bytes():
  di.q1(acc, Nat.divmod(t, 60n))

# the year a time falls in: IMF-fixdate writes four digits of it, so
# date.fmt reads back for every time before the year 10000
def year.of(kjd: Nat & Nat & Nat) -> Nat:
  (k, jd) = kjd
  Nat.add(k, 1970n)

def year.q3(dh: Nat & Nat) -> Nat:
  (days, h) = dh
  year.of(civil(days))

def year.q2(hm: Nat & Nat) -> Nat:
  (hs, m) = hm
  year.q3(Nat.divmod(hs, 24n))

def year.q1(mx: Nat & Nat) -> Nat:
  (ms, x) = mx
  year.q2(Nat.divmod(ms, 60n))

def date.year(t: Nat) -> Nat:
  year.q1(Nat.divmod(t, 60n))

# whether IMF-fixdate's four digits hold the year: its hundreds are two
def year.hi(yy: Nat & Nat) -> Nat:
  (a, b) = yy
  a

def year.ok(t: Nat) -> Bool:
  Nat.is_lt(year.hi(Nat.divmod(date.year(t), 100n)), 100n)

# Reading a date
# ==============
#
# Each reader takes what it knows off the front of the bytes and hands
# back the rest, or None.
# the bytes after p, when they start with p
def rd.pre(p: Bytes(), s: Bytes()) -> Maybe<&2, Bytes()>:
  match p:
    case SNil{}:
      Some{s}
    case SCon{Chr{+c}, pt}:
      match s:
        case SNil{}:
          None{}
        case SCon{Chr{+d}, st}:
          Bool.pick(Maybe<&2, Bytes()>, U32.is_eq(c, d), rd.pre(pt, st), None{})

def rd.lit(s: Bytes(), p: Bytes()) -> Maybe<&2, Bytes()>:
  rd.pre(p, s)

# one of the names, as its place in the list
def rd.name.up(m: Maybe<&1, Nat & Bytes()>) -> Maybe<&1, Nat & Bytes()>:
  match m:
    case None{}:
      None{}
    case Some{ir}:
      (i, r) = ir
      Some{(1n+i, r)}

def rd.name.at(m: Maybe<&2, Bytes()>, rest: Maybe<&1, Nat & Bytes()>) -> Maybe<&1, Nat & Bytes()>:
  match m:
    case Some{r}:
      Some{(0n, r)}
    case None{}:
      rd.name.up(rest)

def rd.name(+s: Bytes(), xs: List<&2, Bytes()>) -> Maybe<&1, Nat & Bytes()>:
  match xs:
    case Nil{}:
      None{}
    case Con{x, t}:
      rd.name.at(rd.lit(s, x), rd.name(s, t))

# a digit, and a run of them read as one number
def rd.dig.at(ok: Bool, +c: U32, t: Bytes()) -> Maybe<&1, Nat & Bytes()>:
  match ok:
    case True{}:
      Some{(Nat.sub(U32.to_nat(c), 48n), t)}
    case False{}:
      None{}

def rd.dig(s: Bytes()) -> Maybe<&1, Nat & Bytes()>:
  match s:
    case SNil{}:
      None{}
    case SCon{Chr{+c}, t}:
      rd.dig.at(U32.is_le(48, c) && U32.is_le(c, 57), c, t)

def rd.d2.b(+a: Nat, m: Maybe<&1, Nat & Bytes()>) -> Maybe<&1, Nat & Bytes()>:
  match m:
    case None{}:
      None{}
    case Some{br}:
      (b, r) = br
      Some{(Nat.add(Nat.mul(a, 10n), b), r)}

def rd.d2.a(m: Maybe<&1, Nat & Bytes()>) -> Maybe<&1, Nat & Bytes()>:
  match m:
    case None{}:
      None{}
    case Some{ar}:
      (a, r) = ar
      rd.d2.b(a, rd.dig(r))

def rd.d2(s: Bytes()) -> Maybe<&1, Nat & Bytes()>:
  rd.d2.a(rd.dig(s))

# asctime's day: two digits, or a space and one
def rd.sd.at(sp: Bool, s: Bytes(), t: Bytes()) -> Maybe<&1, Nat & Bytes()>:
  match sp:
    case True{}:
      rd.dig(t)
    case False{}:
      rd.d2(s)

def rd.sd(s: Bytes()) -> Maybe<&1, Nat & Bytes()>:
  match s:
    case SNil{}:
      None{}
    case SCon{Chr{+c}, +t}:
      rd.sd.at(U32.is_eq(c, 32), SCon{Chr{c}, t}, t)

# a time from a day (counted from 1970-01-01) and an hour, a minute and
# a second of it, the way the seconds were split
def stamp.at(m: Maybe<&2, Nat>, +h: Nat, +mi: Nat, +x: Nat) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{days}:
      Some{Nat.add(Nat.mul(Nat.add(Nat.mul(Nat.add(Nat.mul(days, 24n), h), 60n), mi), 60n), x)}

# ... from a year, a month (from 0) and a day of it (from 1), when the
# year is 1970 or later and the day is one the month has
def stamp.go(y1970: Bool, +y: Nat, j: Nat, +d: Nat, +h: Nat, +mi: Nat, +x: Nat) -> Maybe<&2, Nat>:
  match y1970:
    case False{}:
      None{}
    case True{}:
      match d:
        case 0n:
          None{}
        case 1n+d0:
          stamp.at(days.of(Nat.sub(y, 1970n), (j, d0)), h, mi, x)

# ... and when the hour, the minute and the second are each in range
def stamp.ok(ok: Bool, +y: Nat, j: Nat, +d: Nat, +h: Nat, +mi: Nat, +x: Nat) -> Maybe<&2, Nat>:
  match ok:
    case False{}:
      None{}
    case True{}:
      stamp.go(Nat.is_le(1970n, y), y, j, d, h, mi, x)

def stamp(+y: Nat, j: Nat, +d: Nat, +h: Nat, +mi: Nat, +x: Nat) -> Maybe<&2, Nat>:
  stamp.ok(Bool.and(Nat.is_lt(h, 24n), Bool.and(Nat.is_lt(mi, 60n), Nat.is_lt(x, 60n))), y, j, d, h,
    mi, x)

# The three forms, each a list of what comes in order: a name from a
# list, a literal, two digits, or asctime's day. What a name or a number
# reads goes to a slot of the date: the day, the month (a name's place),
# the year's first two digits, its last two, or a two-digit year, the
# hour, the minute and the second; a weekday is read and not kept (RFC
# 9110 has it redundant, and nginx does not check it either).
type Sl is Data:
  SDay{}
  SMon{}
  SYh{}
  SYl{}
  SYy{}
  SH{}
  SM{}
  SS{}
  SNone{}

type Tok is Data:
  TName{xs: List<&2, Bytes()>, sl: Sl}
  TLit{s: Bytes()}
  TD2{sl: Sl}
  TSd{sl: Sl}

# a date as it is read: day, month (from 0), year, hour, minute, second
type Dt is Data:
  Dt{d: Nat, j: Nat, y: Nat, h: Nat, m: Nat, x: Nat}

def yy.full(+y: Nat) -> Nat:
  Bool.pick(Nat, Nat.is_lt(y, 70n), Nat.add(y, 2000n), Nat.add(y, 1900n))

def dt.put(dt: Dt, sl: Sl, +v: Nat) -> Dt:
  match dt:
    case Dt{d, j, y, h, m, x}:
      match sl:
        case SDay{}:
          Dt{v, j, y, h, m, x}
        case SMon{}:
          Dt{d, v, y, h, m, x}
        case SYh{}:
          Dt{d, j, Nat.mul(v, 100n), h, m, x}
        case SYl{}:
          Dt{d, j, Nat.add(v, y), h, m, x}
        case SYy{}:
          Dt{d, j, yy.full(v), h, m, x}
        case SH{}:
          Dt{d, j, y, v, m, x}
        case SM{}:
          Dt{d, j, y, h, v, x}
        case SS{}:
          Dt{d, j, y, h, m, v}
        case SNone{}:
          Dt{d, j, y, h, m, x}

def tok.num(m: Maybe<&1, Nat & Bytes()>, sl: Sl, dt: Dt) -> Maybe<&1, Dt & Bytes()>:
  match m:
    case None{}:
      None{}
    case Some{vr}:
      (v, r) = vr
      Some{(dt.put(dt, sl, v), r)}

def tok.lit(m: Maybe<&2, Bytes()>, dt: Dt) -> Maybe<&1, Dt & Bytes()>:
  match m:
    case None{}:
      None{}
    case Some{r}:
      Some{(dt, r)}

def tok.read(t: Tok, +s: Bytes(), dt: Dt) -> Maybe<&1, Dt & Bytes()>:
  match t:
    case TName{xs, sl}:
      tok.num(rd.name(s, xs), sl, dt)
    case TLit{p}:
      tok.lit(rd.lit(s, p), dt)
    case TD2{sl}:
      tok.num(rd.d2(s), sl, dt)
    case TSd{sl}:
      tok.num(rd.sd(s), sl, dt)

def rd.end(s: Bytes()) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      False{}

# the tokens in order over what the one before left, to the value's end
def run.end(m: Maybe<&1, Dt & Bytes()>) -> Maybe<&2, Dt>:
  match m:
    case None{}:
      None{}
    case Some{dr}:
      (dt, r) = dr
      Bool.pick(Maybe<&2, Dt>, rd.end(r), Some{dt}, None{})

def run(ts: List<&2, Tok>, m: Maybe<&1, Dt & Bytes()>) -> Maybe<&2, Dt>:
  match ts:
    case Nil{}:
      run.end(m)
    case Con{t, rest}:
      match m:
        case None{}:
          None{}
        case Some{dr}:
          (dt, r) = dr
          run(rest, tok.read(t, r, dt))

def hms.toks(tail: List<&2, Tok>) -> List<&2, Tok>:
  Con{TD2{SH{}}, Con{TLit{":"}, Con{TD2{SM{}}, Con{TLit{":"}, Con{TD2{SS{}}, tail}}}}}

# IMF-fixdate: "Sun, 06 Nov 1994 08:49:37 GMT"
def imf.toks() -> List<&2, Tok>:
  Con{TName{wkc(), SNone{}}, Con{TD2{SDay{}}, Con{TLit{" "}, Con{TName{monc(), SMon{}},
    Con{TD2{SYh{}}, Con{TD2{SYl{}}, Con{TLit{" "}, hms.toks([TLit{" GMT"}])}}}}}}}

# rfc850-date: "Sunday, 06-Nov-94 08:49:37 GMT"; a two-digit year is
# 19yy from 70 and 20yy below it
def rfc850.toks() -> List<&2, Tok>:
  Con{TName{wkl(), SNone{}}, Con{TD2{SDay{}}, Con{TLit{"-"}, Con{TName{mon3(), SMon{}},
    Con{TLit{"-"}, Con{TD2{SYy{}}, Con{TLit{" "}, hms.toks([TLit{" GMT"}])}}}}}}}

# asctime-date: "Sun Nov  6 08:49:37 1994"
def asctime.toks() -> List<&2, Tok>:
  Con{TName{wks(), SNone{}}, Con{TName{monc(), SMon{}}, Con{TSd{SDay{}}, Con{TLit{" "},
    hms.toks([TLit{" "}, TD2{SYh{}}, TD2{SYl{}}])}}}}

def dt.stamp(m: Maybe<&2, Dt>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{dt}:
      match dt:
        case Dt{d, j, y, h, mi, x}:
          stamp(y, j, d, h, mi, x)

# whether a walk read this date, each field compared as a number (as
# LAWS.bend's vectors compare them)
def dt.is(m: Maybe<&2, Dt>, +d0: Nat, +j0: Nat, +y0: Nat, +h0: Nat, +m0: Nat, +x0: Nat) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{dt}:
      match dt:
        case Dt{d, j, y, h, mi, x}:
          Nat.is_eq(d, d0) && Nat.is_eq(j, j0) && Nat.is_eq(y, y0) && Nat.is_eq(h, h0)
            && Nat.is_eq(mi, m0) && Nat.is_eq(x, x0)

def dt0() -> Dt:
  Dt{0n, 0n, 0n, 0n, 0n, 0n}

def rd.form(ts: List<&2, Tok>, s: Bytes()) -> Maybe<&2, Nat>:
  dt.stamp(run(ts, Some{(dt0(), s)}))

# an HTTP-date, in seconds since the epoch, or None: not one of the three
# forms, or not a day the calendar has, or before 1970
def date.read(+s: Bytes()) -> Maybe<&2, Nat>:
  Maybe.or(&2, Nat, rd.form(imf.toks(), s),
    Maybe.or(&2, Nat, rd.form(rfc850.toks(), s), rd.form(asctime.toks(), s)))

# Entity-tags
# ===========

# the file's entity-tag, quotes and all: its mtime and its size in hex,
# pushed where a head grows, or as its own bytes
def etag.into(acc: Bytes(), mt: U32, n: U32) -> Bytes():
  Bytes.push(hex(Bytes.push(hex(Bytes.push(acc, 34), mt), 45), n), 34)

def etag.of(mt: U32, n: U32) -> Bytes():
  etag.into("", mt, n)

# Where a list of entity-tags is read: between elements (after a comma or
# at the start), after a "W", after a "W/" (weak) or at the start of an
# opaque-tag (strong), inside one (with its bytes so far), or after one.
type Tg is Data:
  TSep{}
  TW{}
  TQ{weak: Bool}
  TIn{weak: Bool, acc: Bytes()}
  TAfter{}
  TBad{}

# a byte of an opaque-tag: etagc, anything visible but '"', or obs-text
def etagc(+c: U32) -> Bool:
  U32.is_eq(c, 33) || (U32.is_le(35, c) && U32.is_le(c, 126)) || U32.is_le(128, c)

def ows.b(+c: U32) -> Bool:
  U32.is_eq(c, 32) || U32.is_eq(c, 9)

# a tag that closes: whether it is the one sought, by weak comparison
# (weak: W/ tags count) or strong (they never do)
def tg.close(tag: Bytes(), strong: Bool, weak: Bool, acc: Bytes()) -> Bool:
  Bool.not(strong && weak) && String.eq(acc, tag)

def tg.step(st: Tg, +c: U32) -> Tg:
  match st:
    case TSep{}:
      Bool.pick(Tg, ows.b(c) || U32.is_eq(c, 44), TSep{},
        Bool.pick(Tg, U32.is_eq(c, 87), TW{},
          Bool.pick(Tg, U32.is_eq(c, 34), TIn{False{}, "\""}, TBad{})))
    case TW{}:
      Bool.pick(Tg, U32.is_eq(c, 47), TQ{True{}}, TBad{})
    case TQ{weak}:
      Bool.pick(Tg, U32.is_eq(c, 34), TIn{weak, "\""}, TBad{})
    case TIn{weak, acc}:
      Bool.pick(Tg, etagc(c), TIn{weak, Bytes.push(acc, c)}, TBad{})
    case TAfter{}:
      Bool.pick(Tg, ows.b(c), TAfter{}, Bool.pick(Tg, U32.is_eq(c, 44), TSep{}, TBad{}))
    case TBad{}:
      TBad{}

# the list walked a byte at a time; hit says a tag closed that matched.
# A list that breaks its grammar matches nothing.
def tg.hit(+tag: Bytes(), strong: Bool, st: Tg, c: U32) -> Bool:
  match st:
    case TIn{weak, +acc}:
      U32.is_eq(c, 34) && tg.close(tag, strong, weak, Bytes.push(acc, 34))
    case _:
      False{}

def tg.next(st: Tg, +c: U32) -> Tg:
  match st:
    case TIn{weak, acc}:
      Bool.pick(Tg, U32.is_eq(c, 34), TAfter{}, tg.step(TIn{weak, acc}, c))
    case _:
      tg.step(st, c)

# a list may end between elements or after a tag, not inside one
def tg.ok(st: Tg) -> Bool:
  match st:
    case TSep{}:
      True{}
    case TAfter{}:
      True{}
    case _:
      False{}

def tg.walk(+tag: Bytes(), +strong: Bool, s: Bytes(), +st: Tg, hit: Bool) -> Bool:
  match s:
    case SNil{}:
      tg.ok(st) && hit
    case SCon{Chr{+c}, t}:
      tg.walk(tag, strong, t, tg.next(st, c), hit || tg.hit(tag, strong, st, c))

# whether a field value names the tag: "*" (the file exists), or a list
# of entity-tags with it among them
# "*", or the tag itself (as a client sends back the one it was given),
# are hits at once; anything else is walked
def tags.at(hit: Bool, +v: Bytes(), +tag: Bytes(), strong: Bool) -> Bool:
  match hit:
    case True{}:
      True{}
    case False{}:
      tg.walk(tag, strong, v, TSep{}, False{})

def tags.hit(+v: Bytes(), +tag: Bytes(), strong: Bool) -> Bool:
  tags.at(String.eq(v, "*") || String.eq(v, tag), v, tag, strong)

# Ranges
# ======

# a range-spec: first-last, first- (last is None), or -suffix
type Spec is Data:
  From{a: Nat, b: Maybe<&2, Nat>}
  Last{n: Nat}

# a number is read saturating at 2^32, past any file's size, so a long
# run of digits is never a way to overflow
def big() -> Nat:
  1n+4294967295n

def num.push(+acc: Nat, +d: Nat) -> Nat:
  Bool.pick(Nat, Nat.is_lt(acc, big()), Nat.min(Nat.add(Nat.mul(acc, 10n), d), big()), big())

# Where a ranges-specifier is read: the unit's bytes so far (lowercased
# as they come: the unit is case-insensitive), then between specs, in a
# first-pos (with its digits so far), after its '-', in a last-pos, in a
# suffix, after a spec; the specs so far, newest first.
type Rs is Data:
  RUnit{i: Nat}
  RSep{}
  RFirst{a: Nat}
  RDash{a: Nat}
  RLastN{a: Nat, b: Nat}
  RSuf0{}
  RSuf{n: Nat}
  RAfter{}
  RBad{}

def lowc(+c: U32) -> U32:
  Bool.pick(U32, U32.is_le(65, c) && U32.is_le(c, 90), (c + 32 : U32), c)

def isdig(+c: U32) -> Bool:
  U32.is_le(48, c) && U32.is_le(c, 57)

def dval(+c: U32) -> Nat:
  Nat.sub(U32.to_nat(c), 48n)

# "bytes=": the byte expected at i of the unit
def unit.at(+i: Nat) -> U32:
  Bytes.get("bytes=", i)

# a spec closes: a first-pos past its last-pos makes the whole field
# invalid (RFC 9110 14.1.1), so it is ignored
def rs.spec(st: Rs, +sp: List<&2, Spec>) -> Rs & List<&2, Spec>:
  match st:
    case RDash{a}:
      (RAfter{}, Con{From{a, None{}}, sp})
    case RLastN{+a, +b}:
      Bool.pick(Rs & List<&2, Spec>, Nat.is_le(a, b), (RAfter{}, Con{From{a, Some{b}}, sp}),
        (RBad{}, sp))
    case RSuf{n}:
      (RAfter{}, Con{Last{n}, sp})
    case _:
      (RBad{}, sp)

# after a spec: whitespace, or a comma and the next
def rs.sep(q: Rs & List<&2, Spec>, +c: U32) -> Rs & List<&2, Spec>:
  (st, +sp) = q
  match st:
    case RAfter{}:
      Bool.pick(Rs & List<&2, Spec>, ows.b(c), (RAfter{}, sp),
        Bool.pick(Rs & List<&2, Spec>, U32.is_eq(c, 44), (RSep{}, sp), (RBad{}, sp)))
    case _:
      (RBad{}, sp)

def rs.step(st: Rs, +c: U32, +sp: List<&2, Spec>) -> Rs & List<&2, Spec>:
  match st:
    case RUnit{+i}:
      Bool.pick(Rs & List<&2, Spec>, U32.is_eq(lowc(c), unit.at(i)),
        Bool.pick(Rs & List<&2, Spec>, Nat.is_eq(i, 5n), (RSep{}, sp), (RUnit{1n+i}, sp)),
        (RBad{}, sp))
    case RSep{}:
      Bool.pick(Rs & List<&2, Spec>, ows.b(c) || U32.is_eq(c, 44), (RSep{}, sp),
        Bool.pick(Rs & List<&2, Spec>, isdig(c), (RFirst{dval(c)}, sp),
          Bool.pick(Rs & List<&2, Spec>, U32.is_eq(c, 45), (RSuf0{}, sp), (RBad{}, sp))))
    case RFirst{+a}:
      Bool.pick(Rs & List<&2, Spec>, isdig(c), (RFirst{num.push(a, dval(c))}, sp),
        Bool.pick(Rs & List<&2, Spec>, U32.is_eq(c, 45), (RDash{a}, sp), (RBad{}, sp)))
    case RDash{+a}:
      Bool.pick(Rs & List<&2, Spec>, isdig(c), (RLastN{a, dval(c)}, sp),
        rs.sep(rs.spec(RDash{a}, sp), c))
    case RLastN{+a, +b}:
      Bool.pick(Rs & List<&2, Spec>, isdig(c), (RLastN{a, num.push(b, dval(c))}, sp),
        rs.sep(rs.spec(RLastN{a, b}, sp), c))
    case RSuf0{}:
      Bool.pick(Rs & List<&2, Spec>, isdig(c), (RSuf{dval(c)}, sp), (RBad{}, sp))
    case RSuf{+n}:
      Bool.pick(Rs & List<&2, Spec>, isdig(c), (RSuf{num.push(n, dval(c))}, sp),
        rs.sep(rs.spec(RSuf{n}, sp), c))
    case RAfter{}:
      rs.sep((RAfter{}, sp), c)
    case RBad{}:
      (RBad{}, sp)

def rs.walk(s: Bytes(), q: Rs & List<&2, Spec>) -> Rs & List<&2, Spec>:
  match s:
    case SNil{}:
      q
    case SCon{Chr{+c}, t}:
      (st, sp) = q
      rs.walk(t, rs.step(st, c, sp))

def rs.some(sp: List<&2, Spec>) -> Maybe<&2, List<&2, Spec>>:
  match sp:
    case Nil{}:
      None{}
    case Con{h, t}:
      Some{List.reverse(&2, Spec, Con{h, t})}

def rs.end.at(q: Rs & List<&2, Spec>) -> Maybe<&2, List<&2, Spec>>:
  (st, sp) = q
  match st:
    case RAfter{}:
      rs.some(sp)
    case _:
      None{}

# the end of the field: a spec in progress closes; the field is a range
# set only if it named at least one spec and broke no rule
def rs.end(q: Rs & List<&2, Spec>) -> Maybe<&2, List<&2, Spec>>:
  (st, sp) = q
  match st:
    case RSep{}:
      rs.some(sp)
    case RAfter{}:
      rs.some(sp)
    case RDash{a}:
      rs.end.at(rs.spec(RDash{a}, sp))
    case RLastN{a, b}:
      rs.end.at(rs.spec(RLastN{a, b}, sp))
    case RSuf{n}:
      rs.end.at(rs.spec(RSuf{n}, sp))
    case _:
      None{}

# a Range field's value: its specs in order, or None when it is not a
# "bytes" ranges-specifier by RFC 9110 14.1.1's grammar (and so ignored)
def rg.parse(s: Bytes()) -> Maybe<&2, List<&2, Spec>>:
  rs.end(rs.walk(s, (RUnit{0n}, Nil{})))

# What a range asks of a file of n bytes: bytes a to b (a <= b < n), or
# nothing it has. A first-pos at or past the end is unsatisfiable; a
# last-pos past it is the end; a suffix is the last n bytes, the whole
# file when it is longer, and nothing when it is zero (RFC 9110 14.1.1).
type Want is Data:
  Span{a: Nat, b: Nat}
  Unsat{}

def want.from(ok: Bool, +a: Nat, b: Nat) -> Want:
  match ok:
    case True{}:
      Span{a, b}
    case False{}:
      Unsat{}

def want.last(+n: Nat, +k: Nat) -> Want:
  match n:
    case 0n:
      Unsat{}
    case 1n+m:
      match k:
        case 0n:
          Unsat{}
        case 1n+j:
          Span{Nat.sub(m, Nat.min(j, m)), m}

# (a first-pos past its last-pos never reaches here, rg.parse having
# refused the field; want refuses it too, so that what it gives is a
# range of the file whatever spec it is handed)
def want(sp: Spec, +n: Nat) -> Want:
  match sp:
    case From{+a, b}:
      match b:
        case None{}:
          want.from(Nat.is_lt(a, n), a, Nat.sub(n, 1n))
        case Some{+b2}:
          want.from(Nat.is_lt(a, n) && Nat.is_le(a, b2), a, Nat.min(b2, Nat.sub(n, 1n)))
    case Last{k}:
      want.last(n, k)

# What a request gets of a file: all of it (200), that it has not
# changed (304), a range of it (206), that no range of it was one it has
# (416), or that a precondition failed (412).
type Got is Data:
  Full{}
  Same{}
  Part{a: Nat, b: Nat}
  NoPart{}
  Fails{}

def got.one(p: Nat, ab: Nat & Nat) -> Got:
  match p:
    case 0n:
      (a, b) = ab
      Part{a, b}
    case 1n+q:
      Full{}

def got.fin(hit: Maybe<&1, Nat & Nat>, k: Nat) -> Got:
  match hit:
    case None{}:
      NoPart{}
    case Some{ab}:
      got.one(Nat.sub(k, 1n), ab)

# the specs a file satisfies decide: none is a 416, one is its 206, and
# more than one is the whole file (a multipart/byteranges reply is one
# this engine does not make; RFC 9110 14.2 lets a server ignore Range)
def got.of(ws: List<&2, Want>, hit: Maybe<&1, Nat & Nat>, +k: Nat) -> Got:
  match ws:
    case Nil{}:
      got.fin(hit, k)
    case Con{w, t}:
      match w:
        case Span{a, b}:
          got.of(t, Some{(a, b)}, 1n+k)
        case Unsat{}:
          got.of(t, hit, k)

def wants(sp: List<&2, Spec>, +n: Nat) -> List<&2, Want>:
  match sp:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{want(h, n), wants(t, n)}

def ranged(m: Maybe<&2, List<&2, Spec>>, +n: Nat) -> Got:
  match m:
    case None{}:
      Full{}
    case Some{sp}:
      got.of(wants(sp, n), None{}, 0n)

# The request's fields
# ====================

# the six fields a file's reply reads, each its first occurrence (If-
# Match and If-None-Match, lists, are every occurrence joined, as RFC
# 9110 5.3 combines field lines), trimmed of whitespace at either end
type Ask is Data:
  Ask{im: Maybe<&2, Bytes()>, ius: Maybe<&2, Bytes()>, inm: Maybe<&2, Bytes()>,
    ims: Maybe<&2, Bytes()>, rg: Maybe<&2, Bytes()>, ir: Maybe<&2, Bytes()>}

def ask.none() -> Ask:
  Ask{None{}, None{}, None{}, None{}, None{}, None{}}

def first(m: Maybe<&2, Bytes()>, v: Bytes()) -> Maybe<&2, Bytes()>:
  match m:
    case None{}:
      Some{v}
    case Some{x}:
      Some{x}

def joined(m: Maybe<&2, Bytes()>, v: Bytes()) -> Maybe<&2, Bytes()>:
  match m:
    case None{}:
      Some{v}
    case Some{x}:
      Some{Bytes.append(x, Bytes.append(", ", v))}

# a value's leading and trailing whitespace: a value carries no control
# but HTAB (the reader refuses the rest), so the whitespace String.trim
# takes off is exactly RFC 9110's OWS, SP and HTAB
def ows.trim(s: Bytes()) -> Bytes():
  String.trim(s)

# which of the six a field is
type Which is Data:
  WIm{}
  WIus{}
  WInm{}
  WIms{}
  WRg{}
  WIr{}

def ask.set(k: Ask, w: Which, v: Bytes()) -> Ask:
  match k:
    case Ask{im, ius, inm, ims, rg, ir}:
      match w:
        case WIm{}:
          Ask{joined(im, ows.trim(v)), ius, inm, ims, rg, ir}
        case WIus{}:
          Ask{im, first(ius, ows.trim(v)), inm, ims, rg, ir}
        case WInm{}:
          Ask{im, ius, joined(inm, ows.trim(v)), ims, rg, ir}
        case WIms{}:
          Ask{im, ius, inm, first(ims, ows.trim(v)), rg, ir}
        case WRg{}:
          Ask{im, ius, inm, ims, first(rg, ows.trim(v)), ir}
        case WIr{}:
          Ask{im, ius, inm, ims, rg, first(ir, ows.trim(v))}

def ask.if(hit: Bool, k: Ask, w: Which, v: Bytes()) -> Ask:
  match hit:
    case True{}:
      ask.set(k, w, v)
    case False{}:
      k

# a name is compared only when its length is one of the six's, so the
# fields of an ordinary request (a Host, an Accept) cost a length each
def ask.put.at(+l: Nat, +n: Bytes(), +v: Bytes(), k: Ask) -> Ask:
  match l:
    case 5n:
      ask.if(String.eq(n, "range"), k, WRg{}, v)
    case 8n:
      ask.if(String.eq(n, "if-match"), ask.if(String.eq(n, "if-range"), k, WIr{}, v), WIm{}, v)
    case 13n:
      ask.if(String.eq(n, "if-none-match"), k, WInm{}, v)
    case 17n:
      ask.if(String.eq(n, "if-modified-since"), k, WIms{}, v)
    case 19n:
      ask.if(String.eq(n, "if-unmodified-since"), k, WIus{}, v)
    case _:
      k

def ask.put(k: Ask, +n: Bytes(), v: Bytes()) -> Ask:
  ask.put.at(Bytes.len(n), n, v, k)

def ask.go(fs: List<&2, Wr.Field>, k: Ask) -> Ask:
  match fs:
    case Nil{}:
      k
    case Con{f, t}:
      match f:
        case Wr.Field{n, v}:
          ask.go(t, ask.put(k, n, v))

def ask.of(fs: List<&2, Wr.Field>) -> Ask:
  ask.go(fs, ask.none())

# The decision
# ============
#
# RFC 9110 13.2.2, for a GET or a HEAD of a file with this tag and this
# mtime (in seconds) and n bytes:
#   1. If-Match: unless it names the tag (strongly), 412.
#   2. else If-Unmodified-Since, a date: if the file changed after it, 412.
#   3. If-None-Match: if it names the tag (weakly), 304; and whether or
#      not it does, If-Modified-Since is not read.
#   4. else If-Modified-Since, a date: if the file has not changed since
#      it, 304.
#   5. Range, for a file of at least a byte: If-Range, if present, must
#      be the tag (strongly) or exactly the mtime, else the whole file;
#      a Range that is a ranges-specifier decides by its specs.
# A date that does not read is ignored, as if the field were absent.

def pre.ius(v: Maybe<&2, Nat>, +mt: Nat) -> Bool:
  match v:
    case None{}:
      True{}
    case Some{d}:
      Nat.is_le(mt, d)

def pre.ok(im: Maybe<&2, Bytes()>, ius: Maybe<&2, Bytes()>, +mt32: U32, +n32: U32) -> Bool:
  match im:
    case Some{v}:
      tags.hit(v, etag.of(mt32, n32), True{})
    case None{}:
      match ius:
        case None{}:
          True{}
        case Some{v}:
          pre.ius(date.read(v), U32.to_nat(mt32))

def ir.date(m: Maybe<&2, Nat>, +mt: Nat) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{d}:
      Nat.is_eq(d, mt)

def ir.at(et: Bool, +v: Bytes(), +mt32: U32, +n32: U32) -> Bool:
  match et:
    case True{}:
      String.eq(v, etag.of(mt32, n32))
    case False{}:
      ir.date(date.read(v), U32.to_nat(mt32))

# If-Range: an entity-tag is compared strongly (exactly the file's own),
# anything else is a date that must be exactly the file's
def ir.ok(+v: Bytes(), +mt32: U32, +n32: U32) -> Bool:
  ir.at(Bytes.starts_with(v, "\"") || Bytes.starts_with(v, "W/"), v, mt32, n32)

def part.go(ir: Maybe<&2, Bytes()>, rg: Bytes(), +mt32: U32, +n32: U32, +n: Nat) -> Got:
  match ir:
    case None{}:
      ranged(rg.parse(rg), n)
    case Some{v}:
      Bool.pick(Got, ir.ok(v, mt32, n32), ranged(rg.parse(rg), n), Full{})

def part(rg: Maybe<&2, Bytes()>, ir: Maybe<&2, Bytes()>, +mt32: U32, +n32: U32, +n: Nat) -> Got:
  match rg:
    case None{}:
      Full{}
    case Some{v}:
      match n:
        case 0n:
          Full{}
        case 1n+p:
          part.go(ir, v, mt32, n32, 1n+p)

def ims.go(m: Maybe<&2, Nat>, +mt: Nat, later: Got) -> Got:
  match m:
    case None{}:
      later
    case Some{d}:
      Bool.pick(Got, Nat.is_le(mt, d), Same{}, later)

def cond(inm: Maybe<&2, Bytes()>, ims: Maybe<&2, Bytes()>, +mt32: U32, +n32: U32, later: Got) ->
  Got:
  match inm:
    case Some{v}:
      Bool.pick(Got, tags.hit(v, etag.of(mt32, n32), False{}), Same{}, later)
    case None{}:
      match ims:
        case None{}:
          later
        case Some{v}:
          ims.go(date.read(v), U32.to_nat(mt32), later)

# what the request gets of a file of n32 bytes last written at mt32 (in
# seconds since the epoch); the file's entity-tag is written only when a
# field asks for it
def decide(k: Ask, +mt32: U32, +n32: U32) -> Got:
  match k:
    case Ask{im, ius, inm, ims, rg, ir}:
      Bool.pick(Got, pre.ok(im, ius, mt32, n32),
        cond(inm, ims, mt32, n32, part(rg, ir, mt32, n32, U32.to_nat(n32))), Fails{})

# The replies
# ===========
#
# Each head ends "connection: keep-alive" and a blank line, which the
# engine turns into "close" on a connection's last reply. ct is the head
# the file's type keeps ready (main.bend's mime table): "HTTP/1.1 200
# OK", its Content-Type line, and the name of its Content-Length; a 206
# keeps the two lines after the status line, 17 bytes in. Each head is
# built where it grows; hd.*.is says what bytes it is, piece by piece.
def ka() -> Bytes():
  "\r\nconnection: keep-alive\r\n\r\n"

def vals(acc: Bytes(), +mt32: U32, +n32: U32) -> Bytes():
  etag.into(Bytes.append(date.into(Bytes.append(acc, "\r\nlast-modified: "), U32.to_nat(mt32)),
    "\r\netag: "), mt32, n32)

def vals.is(+mt32: U32, +n32: U32, tail: List<&2, Bytes()>) -> List<&2, Bytes()>:
  Con{"\r\nlast-modified: ", Con{date.fmt(U32.to_nat(mt32)), Con{"\r\netag: ",
    Con{etag.of(mt32, n32), tail}}}}

def ranges() -> Bytes():
  "\r\naccept-ranges: bytes\r\nconnection: keep-alive\r\n\r\n"

def hd.full(ct: Bytes(), +n32: U32, +mt32: U32) -> Bytes():
  Bytes.append(vals(num.into(Bytes.append("", ct), U32.to_nat(n32)), mt32, n32), ranges())

def hd.full.is(ct: Bytes(), +n32: U32, +mt32: U32) -> Bytes():
  Bytes.concat(Con{ct, Con{num(U32.to_nat(n32)), vals.is(mt32, n32, [ranges()])}})

def hd.same(+mt32: U32, +n32: U32) -> Bytes():
  Bytes.append(vals(Bytes.append("", "HTTP/1.1 304 Not Modified"), mt32, n32), ka())

def hd.same.is(+mt32: U32, +n32: U32) -> Bytes():
  Bytes.concat(Con{"HTTP/1.1 304 Not Modified", vals.is(mt32, n32, [ka()])})

# the 206's content-range: the first and the last byte sent, and the size
def crange(+a: Nat, +b: Nat, +n: Nat) -> List<&2, Bytes()>:
  ["\r\ncontent-range: bytes ", num(a), "-", num(b), "/", num(n)]

def hd.part(ct: Bytes(), +a: Nat, +b: Nat, +n32: U32, +mt32: U32) -> Bytes():
  Bytes.append(vals(Bytes.append(Bytes.append(Bytes.append("HTTP/1.1 206 Partial Content\r\n",
    Bytes.drop(ct, 17n)), num(Nat.sub(1n+b, a))), Bytes.concat(crange(a, b, U32.to_nat(n32)))),
    mt32, n32), ka())

def hd.part.is(ct: Bytes(), +a: Nat, +b: Nat, +n32: U32, +mt32: U32) -> Bytes():
  Bytes.concat(Con{"HTTP/1.1 206 Partial Content\r\n", Con{Bytes.drop(ct, 17n),
    Con{num(Nat.sub(1n+b, a)), Con{Bytes.concat(crange(a, b, U32.to_nat(n32))),
      vals.is(mt32, n32, [ka()])}}}})

# the 416 and the 412 say why in a line of text, which a HEAD leaves out
def body.or(head: Bool, b: Bytes()) -> Bytes():
  match head:
    case True{}:
      ""
    case False{}:
      b

def hd.nopart(+n32: U32, head: Bool) -> Bytes():
  Bytes.concat(["HTTP/1.1 416 Range Not Satisfiable\r\ncontent-type: text/plain\r\ncontent-length: 22\r\ncontent-range: bytes */",
    num(U32.to_nat(n32)), ka(), body.or(head, "range not satisfiable\n")])

def hd.fails(head: Bool) -> Bytes():
  Bytes.append("HTTP/1.1 412 Precondition Failed\r\ncontent-type: text/plain\r\ncontent-length: 20\r\nconnection: keep-alive\r\n\r\n",
    body.or(head, "precondition failed\n"))

# What a file's reply is: its head, and the part of the file after it,
# len bytes from off (bend-wire's L.Fr, which the writer sends as it is)
def fr.of(g: Got, ct: Bytes(), head: Bool, +n32: U32, +mt32: U32) -> L.Fr:
  match g:
    case Full{}:
      L.Fr{hd.full(ct, n32, mt32), 0, n32}
    case Same{}:
      L.Fr{hd.same(mt32, n32), 0, 0}
    case Part{+a, +b}:
      L.Fr{hd.part(ct, a, b, n32, mt32), U32.from_nat(a), U32.from_nat(Nat.sub(1n+b, a))}
    case NoPart{}:
      L.Fr{hd.nopart(n32, head), 0, 0}
    case Fails{}:
      L.Fr{hd.fails(head), 0, 0}

# the reply to a GET (or a HEAD) of a file of n32 bytes last written at
# mt32, as the request's fields ask
def reply(ct: Bytes(), fs: List<&2, Wr.Field>, head: Bool, +n32: U32, +mt32: U32) -> L.Fr:
  fr.of(decide(ask.of(fs), mt32, n32), ct, head, n32, mt32)
