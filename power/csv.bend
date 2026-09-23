# Csv: RFC 4180 and the common dialect knobs, as a streaming reader over
# Base's Bytes() and a minimal-quoting writer.
#
# The reader is a byte-at-a-time machine (step), so a read may end
# anywhere -- inside a quoted field, between the CR and the LF of a line
# end, between the two quotes of an escaped quote -- and the next read
# carries on from the state the last one left. feed_buf is the same
# machine walked in runs: an unquoted field, or the text between quotes,
# is found and cut from the read whole, so a field that lies in one read
# is a view of it and not a byte rebuilt. A field that had a doubled
# quote, or that a read boundary cut, is built.
#
# csv_laws.bend states, and csv_proof.bend proves, for every dialect and
# every input: feed_buf is feed; chunking never changes the parse; the
# reader is csv_spec.bend's whole-input reference, written from RFC
# 4180's ABNF, over one read and over any split into reads; and reading
# back what show wrote gives the records it was given.
#
# Records. A record is its fields, oldest first; its width is its field
# count, List.length. A blank line is a record of one empty field, as
# the ABNF reads it (CPython's reader says [] for it; the writer writes
# a lone empty field as "" so the two never meet). The empty input, and
# a line end at the very end, add no record.
#
# Ragged rows. Every record's width is reported (it is its length). With
# ragged off, a record whose width differs from the first record's is
# refused: Bad{at, Ragged}, at the byte that ended it.
#
# Line ends. crlf: CR LF ends a record. cr: a CR alone does. lf: an LF
# alone does. A CR or LF outside quotes that the dialect does not accept
# is refused: a CR is judged at the CR (with crlf alone, by the byte
# after it), an LF at the LF. Inside quotes CR and LF are data, always.
#
# Refusals are terminal: Bad{at, why} is kept whatever follows. at is
# the offset of the byte that broke the rule (the input's length when
# the end of input did); for a line end, the offset of its first byte.
#   QuoteInField   a quote inside an unquoted field
#   Unclosed       the input ended inside quotes
#   AfterQuote     a byte other than a delimiter or a line end after the
#                  closing quote
#   BareCR BareLF  a line end the dialect does not accept
#   FieldTooLong   a field past max_field bytes (content bytes: a doubled
#                  quote is one, counted at its second quote)
#   TooManyFields  a record past max_fields fields
#   Ragged         a record wider or narrower than the first
# The budgets make hostile input a refusal and never a hang: the reader
# holds at most one record of max_fields fields of max_field bytes, plus
# the records not yet taken.
#
# BOM: a UTF-8 byte order mark is data, the first bytes of the first
# field, as every other byte past 127 is. Csv.drop_bom strips one.
#
# Byte classes are judged first match: the quote, the delimiter, CR,
# LF. A dialect whose quote or delimiter is CR or LF, or whose quote is
# its delimiter, reads by that order; the writer's round trip is only
# promised for a sane dialect (see fits).
import Base

type Dialect is Data:
  Dialect{delim: U32, quote: U32, crlf: Bool, lf: Bool, cr: Bool, header: Bool,
    max_field: Nat, max_fields: Nat, ragged: Bool, pad: Bool}

def Rec() -> Data:
  List<&2, Bytes()>

# RFC 4180 as CPython's csv reads it: a comma, a double quote, any of
# the three line ends, CPython's 131072-byte field limit
def excel() -> Dialect:
  Dialect{44, 34, True{}, True{}, True{}, False{}, 131072n, 65536n, True{}, False{}}

# excel with a tab for the comma, as CPython's excel-tab
def tsv() -> Dialect:
  Dialect{9, 34, True{}, True{}, True{}, False{}, 131072n, 65536n, True{}, False{}}

# RFC 4180 to the letter: CRLF only, and every record as wide as the first
def rfc() -> Dialect:
  Dialect{44, 34, True{}, False{}, False{}, False{}, 131072n, 65536n, False{}, False{}}

def delim(d: Dialect) -> U32:
  match d:
    case Dialect{dl, q, a, b, c, h, mf, mn, rg, pd}:
      dl

def quote(d: Dialect) -> U32:
  match d:
    case Dialect{dl, q, a, b, c, h, mf, mn, rg, pd}:
      q

def crlf(d: Dialect) -> Bool:
  match d:
    case Dialect{dl, q, a, b, c, h, mf, mn, rg, pd}:
      a

def lf(d: Dialect) -> Bool:
  match d:
    case Dialect{dl, q, a, b, c, h, mf, mn, rg, pd}:
      b

def cr(d: Dialect) -> Bool:
  match d:
    case Dialect{dl, q, a, b, c, h, mf, mn, rg, pd}:
      c

def header(d: Dialect) -> Bool:
  match d:
    case Dialect{dl, q, a, b, c, h, mf, mn, rg, pd}:
      h

def max_field(d: Dialect) -> Nat:
  match d:
    case Dialect{dl, q, a, b, c, h, mf, mn, rg, pd}:
      mf

def max_fields(d: Dialect) -> Nat:
  match d:
    case Dialect{dl, q, a, b, c, h, mf, mn, rg, pd}:
      mn

def ragged(d: Dialect) -> Bool:
  match d:
    case Dialect{dl, q, a, b, c, h, mf, mn, rg, pd}:
      rg

def pad(d: Dialect) -> Bool:
  match d:
    case Dialect{dl, q, a, b, c, h, mf, mn, rg, pd}:
      pd

# Bytes
# =====

def one(c: U32) -> Bytes():
  SCon{Chr{c}, SNil{}}

def push(acc: Bytes(), c: U32) -> Bytes():
  Bytes.append(acc, one(c))

def drop_bom.at(ok: Bool, +b: Bytes()) -> Bytes():
  match ok:
    case True{}:
      Bytes.drop(b, 3n)
    case False{}:
      b

# the bytes after a UTF-8 byte order mark, or all of them without one
def drop_bom(+b: Bytes()) -> Bytes():
  drop_bom.at(Bytes.starts_with(b, Bytes.from_list([239, 187, 191])), b)

# Classes
# =======

type K is Data:
  KQ{}
  KD{}
  KCR{}
  KLF{}
  KO{}

def k.pick(b: Bool, x: K, y: K) -> K:
  match b:
    case True{}:
      x
    case False{}:
      y

# what a byte is to the grammar, first match wins
def cls(+d: Dialect, +c: U32) -> K:
  k.pick(U32.is_eq(c, quote(d)), KQ{},
  k.pick(U32.is_eq(c, delim(d)), KD{},
  k.pick(U32.is_eq(c, 13), KCR{},
  k.pick(U32.is_eq(c, 10), KLF{}, KO{}))))

# The reader
# ==========

type Why is Data:
  QuoteInField{}
  Unclosed{}
  AfterQuote{}
  BareCR{}
  BareLF{}
  FieldTooLong{}
  TooManyFields{}
  Ragged{}

# where the reader is. left counts down the bytes the field may still
# take; CRp holds the field a CR ended and the CR's offset until the
# next byte says what the CR was.
type Mode is Data:
  RS{}
  FS{}
  Unq{acc: Bytes(), left: Nat}
  Quo{acc: Bytes(), left: Nat}
  QQ{acc: Bytes(), left: Nat}
  CRp{acc: Bytes(), at: Nat}
  Bad{at: Nat, why: Why}

# the reader: its mode; fl, the fields the record may still take; cur,
# the record's fields so far, newest first; out, the records not yet
# taken, newest first; w, the fl the first record left (its width,
# counted down), which every record must leave when ragged is off; pos,
# the offset of the next byte
type P is Data:
  P{m: Mode, fl: Nat, cur: List<&2, Bytes()>, out: List<&2, List<&2, Bytes()>>,
    w: Maybe<&2, Nat>, pos: Nat}

def new(+d: Dialect) -> P:
  P{RS{}, max_fields(d), Nil{}, Nil{}, None{}, 0n}

def grow(q: Bool, acc: Bytes(), l: Nat) -> Mode:
  match q:
    case True{}:
      Quo{acc, l}
    case False{}:
      Unq{acc, l}

# a byte joins the field, if the field has room for it
def put(q: Bool, c: U32, acc: Bytes(), left: Nat, fl: Nat, cur: List<&2, Bytes()>,
  out: List<&2, List<&2, Bytes()>>, w: Maybe<&2, Nat>, +pos: Nat) -> P:
  match left:
    case 0n:
      P{Bad{pos, FieldTooLong{}}, fl, cur, out, w, pos}
    case 1n+l:
      P{grow(q, push(acc, c), l), fl, cur, out, w, 1n+pos}

# a field ends, if the record has room for it; the reader goes on in
# next from np
def endf(acc: Bytes(), fl: Nat, cur: List<&2, Bytes()>, out: List<&2, List<&2, Bytes()>>,
  w: Maybe<&2, Nat>, +pos: Nat, next: Mode, np: Nat) -> P:
  match fl:
    case 0n:
      P{Bad{pos, TooManyFields{}}, 0n, cur, out, w, pos}
    case 1n+f:
      P{next, f, acc <> cur, out, w, np}

def endr.ok(ok: Bool, +d: Dialect, rec: List<&2, Bytes()>, out: List<&2, List<&2, Bytes()>>,
  x: Nat, +at: Nat, next: Mode, np: Nat) -> P:
  match ok:
    case True{}:
      P{next, max_fields(d), Nil{}, rec <> out, Some{x}, np}
    case False{}:
      P{Bad{at, Ragged{}}, 0n, Nil{}, out, Some{x}, at}

# a record ends, f being the fl it left: kept, and if it is the first,
# its width is the one to keep
def endr(+d: Dialect, +f: Nat, rec: List<&2, Bytes()>, out: List<&2, List<&2, Bytes()>>,
  w: Maybe<&2, Nat>, +at: Nat, next: Mode, np: Nat) -> P:
  match w:
    case None{}:
      P{next, max_fields(d), Nil{}, rec <> out, Some{f}, np}
    case Some{+x}:
      endr.ok(ragged(d) || Nat.is_eq(f, x), d, rec, out, x, at, next, np)

# a line end at `at`: the field acc ends, then the record
def endl(+d: Dialect, acc: Bytes(), fl: Nat, cur: List<&2, Bytes()>,
  out: List<&2, List<&2, Bytes()>>, w: Maybe<&2, Nat>, +at: Nat, np: Nat) -> P:
  match fl:
    case 0n:
      P{Bad{at, TooManyFields{}}, 0n, cur, out, w, at}
    case 1n+f:
      endr(d, f, List.reverse(&2, Bytes(), acc <> cur), out, w, at, RS{}, np)

# a CR where a field may end: held with the field until the next byte
def cr.at.ok(ok: Bool, acc: Bytes(), fl: Nat, cur: List<&2, Bytes()>,
  out: List<&2, List<&2, Bytes()>>, w: Maybe<&2, Nat>, +pos: Nat) -> P:
  match ok:
    case True{}:
      P{CRp{acc, pos}, fl, cur, out, w, 1n+pos}
    case False{}:
      P{Bad{pos, BareCR{}}, fl, cur, out, w, pos}

def cr.at(+d: Dialect, acc: Bytes(), fl: Nat, cur: List<&2, Bytes()>,
  out: List<&2, List<&2, Bytes()>>, w: Maybe<&2, Nat>, +pos: Nat) -> P:
  cr.at.ok(crlf(d) || cr(d), acc, fl, cur, out, w, pos)

# an LF where a field may end
def lf.at.ok(+d: Dialect, ok: Bool, acc: Bytes(), fl: Nat, cur: List<&2, Bytes()>,
  out: List<&2, List<&2, Bytes()>>, w: Maybe<&2, Nat>, +pos: Nat) -> P:
  match ok:
    case True{}:
      endl(d, acc, fl, cur, out, w, pos, 1n+pos)
    case False{}:
      P{Bad{pos, BareLF{}}, fl, cur, out, w, pos}

def lf.at(+d: Dialect, acc: Bytes(), fl: Nat, cur: List<&2, Bytes()>,
  out: List<&2, List<&2, Bytes()>>, w: Maybe<&2, Nat>, +pos: Nat) -> P:
  lf.at.ok(d, lf(d), acc, fl, cur, out, w, pos)

# a byte where a field starts: after a line end, or after a delimiter
def fresh(+d: Dialect, k: K, c: U32, fl: Nat, cur: List<&2, Bytes()>,
  out: List<&2, List<&2, Bytes()>>, w: Maybe<&2, Nat>, +pos: Nat) -> P:
  match k:
    case KQ{}:
      P{Quo{"", max_field(d)}, fl, cur, out, w, 1n+pos}
    case KD{}:
      endf("", fl, cur, out, w, pos, FS{}, 1n+pos)
    case KCR{}:
      cr.at(d, "", fl, cur, out, w, pos)
    case KLF{}:
      lf.at(d, "", fl, cur, out, w, pos)
    case KO{}:
      put(False{}, c, "", max_field(d), fl, cur, out, w, pos)

# after a CR the dialect took alone: the byte after it starts a record,
# unless the line end was refused
def fresh.after(+d: Dialect, p: P, k: K, c: U32) -> P:
  match p:
    case P{m, fl, cur, out, w, pos}:
      match m:
        case RS{}:
          fresh(d, k, c, fl, cur, out, w, pos)
        case _:
          P{m, fl, cur, out, w, pos}

# the byte after a CR: an LF that completes a CRLF, or the first byte
# after a CR the dialect takes alone, or a refusal
def crp.at(+d: Dialect, both: Bool, alone: Bool, acc: Bytes(), +at: Nat, k: K, c: U32, fl: Nat,
  cur: List<&2, Bytes()>, out: List<&2, List<&2, Bytes()>>, w: Maybe<&2, Nat>, +pos: Nat) -> P:
  match both:
    case True{}:
      endl(d, acc, fl, cur, out, w, at, 1n+pos)
    case False{}:
      match alone:
        case True{}:
          fresh.after(d, endl(d, acc, fl, cur, out, w, at, pos), k, c)
        case False{}:
          P{Bad{at, BareCR{}}, fl, cur, out, w, pos}

def is_lf(k: K) -> Bool:
  match k:
    case KLF{}:
      True{}
    case _:
      False{}

def step.at(+d: Dialect, m: Mode, +k: K, c: U32, fl: Nat, cur: List<&2, Bytes()>,
  out: List<&2, List<&2, Bytes()>>, w: Maybe<&2, Nat>, +pos: Nat) -> P:
  match m k:
    case RS{} _:
      fresh(d, k, c, fl, cur, out, w, pos)
    case FS{} _:
      fresh(d, k, c, fl, cur, out, w, pos)
    case Unq{acc, left} KQ{}:
      P{Bad{pos, QuoteInField{}}, fl, cur, out, w, pos}
    case Unq{acc, left} KD{}:
      endf(acc, fl, cur, out, w, pos, FS{}, 1n+pos)
    case Unq{acc, left} KCR{}:
      cr.at(d, acc, fl, cur, out, w, pos)
    case Unq{acc, left} KLF{}:
      lf.at(d, acc, fl, cur, out, w, pos)
    case Unq{acc, left} KO{}:
      put(False{}, c, acc, left, fl, cur, out, w, pos)
    case Quo{acc, left} KQ{}:
      P{QQ{acc, left}, fl, cur, out, w, 1n+pos}
    case Quo{acc, left} _:
      put(True{}, c, acc, left, fl, cur, out, w, pos)
    case QQ{acc, left} KQ{}:
      put(True{}, c, acc, left, fl, cur, out, w, pos)
    case QQ{acc, left} KD{}:
      endf(acc, fl, cur, out, w, pos, FS{}, 1n+pos)
    case QQ{acc, left} KCR{}:
      cr.at(d, acc, fl, cur, out, w, pos)
    case QQ{acc, left} KLF{}:
      lf.at(d, acc, fl, cur, out, w, pos)
    case QQ{acc, left} KO{}:
      P{Bad{pos, AfterQuote{}}, fl, cur, out, w, pos}
    case CRp{acc, at} _:
      crp.at(d, is_lf(k) && crlf(d), cr(d), acc, at, k, c, fl, cur, out, w, pos)
    case Bad{at, why} _:
      P{Bad{at, why}, fl, cur, out, w, pos}

def step(+d: Dialect, p: P, +c: U32) -> P:
  match p:
    case P{m, fl, cur, out, w, pos}:
      step.at(d, m, cls(d, c), c, fl, cur, out, w, pos)

# feed: the machine over a byte list, one byte at a time. The state that
# comes out is the state to feed the next read, so a document split
# anywhere reads as the document whole.
def feed(+d: Dialect, bs: List<&2, U32>, p: P) -> P:
  match bs:
    case Nil{}:
      p
    case Con{c, t}:
      feed(d, t, step(d, p, c))

# The same walk over Bytes, a byte at a time.
def feed_buf.slow(+d: Dialect, s: Bytes(), p: P) -> P:
  match s:
    case SNil{}:
      p
    case SCon{Chr{c}, t}:
      feed_buf.slow(d, t, step(d, p, c))

# The walk feed_buf runs. In an unquoted field (q False) a run is the
# bytes that are neither quote, delimiter, CR nor LF; between quotes (q
# True), every byte but the quote. A run is cut from the read whole and
# never goes past the field's room: the byte that ends it -- the one
# the field has no room for, too -- is stepped at once.
def stay(q: Bool, k: K) -> Bool:
  match q k:
    case True{} KQ{}:
      False{}
    case True{} _:
      True{}
    case False{} KO{}:
      True{}
    case False{} _:
      False{}

def inc(ok: Bool, k: Nat) -> Nat:
  match ok:
    case True{}:
      1n+k
    case False{}:
      k

# how many bytes of s the run takes from its first: at most left, and
# only ones it stays on. It looks one byte past the run and no further.
def run.len(+d: Dialect, s: Bytes(), go: Bool, +q: Bool, left: Nat, k: Nat) -> Nat:
  match s go left:
    case SNil{} _ _:
      k
    case SCon{h, t} False{} _:
      k
    case SCon{h, t} True{} 0n:
      k
    case SCon{Chr{c}, t} True{} 1n+l:
      +ok = stay(q, cls(d, c))
      run.len(d, t, ok, q, l, inc(ok, k))

# one byte, stepped
def one.step(+d: Dialect, p: P, s: Bytes()) -> P & Bytes():
  match s:
    case SNil{}:
      (p, SNil{})
    case SCon{Chr{c}, t}:
      (step(d, p, c), t)

def run.took(+d: Dialect, q: Bool, acc: Bytes(), +left: Nat, +j: Nat, fl: Nat,
  cur: List<&2, Bytes()>, out: List<&2, List<&2, Bytes()>>, w: Maybe<&2, Nat>, +pos: Nat,
  ab: Bytes() & Bytes()) -> P & Bytes():
  (a, b) = ab
  one.step(d, P{grow(q, Bytes.append(acc, a), Nat.sub(left, 1n+j)), fl, cur, out, w,
    Nat.add(1n+j, pos)}, b)

def run.cut(+d: Dialect, q: Bool, acc: Bytes(), +left: Nat, s: Bytes(), fl: Nat,
  cur: List<&2, Bytes()>, out: List<&2, List<&2, Bytes()>>, w: Maybe<&2, Nat>, +pos: Nat,
  +k: Nat) -> P & Bytes():
  match k:
    case 0n:
      one.step(d, P{grow(q, acc, left), fl, cur, out, w, pos}, s)
    case 1n+j:
      run.took(d, q, acc, left, j, fl, cur, out, w, pos, String.cut(s, 1n+j))

def run.go(+d: Dialect, +q: Bool, acc: Bytes(), +left: Nat, +s: Bytes(), fl: Nat,
  cur: List<&2, Bytes()>, out: List<&2, List<&2, Bytes()>>, w: Maybe<&2, Nat>, +pos: Nat) ->
  P & Bytes():
  run.cut(d, q, acc, left, s, fl, cur, out, w, pos, run.len(d, s, True{}, q, left, 0n))

# a field from its first byte: a byte that starts an unquoted field
# steps exactly as the empty unquoted field does, so the whole field is
# one cut and a view of the read
def ent.cut(+d: Dialect, m: Mode, s: Bytes(), fl: Nat, cur: List<&2, Bytes()>,
  out: List<&2, List<&2, Bytes()>>, w: Maybe<&2, Nat>, +pos: Nat, +k: Nat) -> P & Bytes():
  match k:
    case 0n:
      one.step(d, P{m, fl, cur, out, w, pos}, s)
    case 1n+j:
      run.took(d, False{}, "", max_field(d), j, fl, cur, out, w, pos, String.cut(s, 1n+j))

def ent.go(+d: Dialect, m: Mode, +s: Bytes(), fl: Nat, cur: List<&2, Bytes()>,
  out: List<&2, List<&2, Bytes()>>, w: Maybe<&2, Nat>, +pos: Nat) -> P & Bytes():
  ent.cut(d, m, s, fl, cur, out, w, pos, run.len(d, s, True{}, False{}, max_field(d), 0n))

# one move of the walk: a run, or one byte
def adv.at(+d: Dialect, m: Mode, +s: Bytes(), fl: Nat, cur: List<&2, Bytes()>,
  out: List<&2, List<&2, Bytes()>>, w: Maybe<&2, Nat>, +pos: Nat) -> P & Bytes():
  match m:
    case RS{}:
      ent.go(d, RS{}, s, fl, cur, out, w, pos)
    case FS{}:
      ent.go(d, FS{}, s, fl, cur, out, w, pos)
    case Unq{acc, left}:
      run.go(d, False{}, acc, left, s, fl, cur, out, w, pos)
    case Quo{acc, left}:
      run.go(d, True{}, acc, left, s, fl, cur, out, w, pos)
    case QQ{acc, left}:
      one.step(d, P{QQ{acc, left}, fl, cur, out, w, pos}, s)
    case CRp{acc, at}:
      one.step(d, P{CRp{acc, at}, fl, cur, out, w, pos}, s)
    case Bad{at, why}:
      (P{Bad{at, why}, fl, cur, out, w, pos}, "")

def adv(+d: Dialect, +s: Bytes(), p: P) -> P & Bytes():
  match p:
    case P{m, fl, cur, out, w, pos}:
      adv.at(d, m, s, fl, cur, out, w, pos)

# the rest of a walk the fuel ran out on, a byte at a time
def feed_buf.last(+d: Dialect, q: P & Bytes()) -> P:
  (p, s) = q
  feed_buf.slow(d, s, p)

# n bounds the moves; every move takes at least one byte, so a walk
# over n bytes never runs out
def feed_buf.go(+d: Dialect, n: Nat, q: P & Bytes()) -> P:
  match n:
    case 0n:
      feed_buf.last(d, q)
    case 1n+m:
      (p, s) = q
      match s:
        case SNil{}:
          p
        case SCon{h, t}:
          feed_buf.go(d, m, adv(d, SCon{h, t}, p))

def feed_buf(+d: Dialect, +s: Bytes(), p: P) -> P:
  feed_buf.go(d, Bytes.len(s), (p, s))

# The end of input
# ================

def finish.cr(+d: Dialect, alone: Bool, acc: Bytes(), at: Nat, fl: Nat, cur: List<&2, Bytes()>,
  out: List<&2, List<&2, Bytes()>>, w: Maybe<&2, Nat>, +pos: Nat) -> P:
  match alone:
    case True{}:
      endl(d, acc, fl, cur, out, w, at, pos)
    case False{}:
      P{Bad{at, BareCR{}}, fl, cur, out, w, pos}

def finish(+d: Dialect, p: P) -> P:
  match p:
    case P{m, fl, cur, out, w, +pos}:
      match m:
        case RS{}:
          P{RS{}, fl, cur, out, w, pos}
        case FS{}:
          endl(d, "", fl, cur, out, w, pos, pos)
        case Unq{acc, left}:
          endl(d, acc, fl, cur, out, w, pos, pos)
        case Quo{acc, left}:
          P{Bad{pos, Unclosed{}}, fl, cur, out, w, pos}
        case QQ{acc, left}:
          endl(d, acc, fl, cur, out, w, pos, pos)
        case CRp{acc, at}:
          finish.cr(d, cr(d), acc, at, fl, cur, out, w, pos)
        case Bad{at, why}:
          P{Bad{at, why}, fl, cur, out, w, pos}

# What was read
# =============

type Out is Data:
  Refused{at: Nat, why: Why}
  Read{head: Maybe<&2, List<&2, Bytes()>>, rows: List<&2, List<&2, Bytes()>>}

# the records, oldest first, with the first one taken as the header when
# the dialect has one
def table.at(h: Bool, rs: List<&2, List<&2, Bytes()>>) -> Out:
  match h rs:
    case True{} Con{r, t}:
      Read{Some{r}, t}
    case True{} Nil{}:
      Read{None{}, Nil{}}
    case False{} _:
      Read{None{}, rs}

def table(+d: Dialect, rs: List<&2, List<&2, Bytes()>>) -> Out:
  table.at(header(d), rs)

def result(+d: Dialect, p: P) -> Out:
  match p:
    case P{m, fl, cur, out, w, pos}:
      match m:
        case Bad{at, why}:
          Refused{at, why}
        case _:
          table(d, List.reverse(&2, List<&2, Bytes()>, out))

# a whole document, in one read
def read(+d: Dialect, +b: Bytes()) -> Out:
  result(d, finish(d, feed_buf(d, b, new(d))))

# the records completed so far, oldest first, and the reader without
# them: a streaming consumer takes them after every read
def take(p: P) -> P & List<&2, List<&2, Bytes()>>:
  match p:
    case P{m, fl, cur, out, w, pos}:
      (P{m, fl, cur, Nil{}, w, pos}, List.reverse(&2, List<&2, Bytes()>, out))

def width(r: List<&2, Bytes()>) -> Nat:
  List.length(&2, Bytes(), r)

def why.show(y: Why) -> String:
  match y:
    case QuoteInField{}:
      "quote-in-field"
    case Unclosed{}:
      "unclosed"
    case AfterQuote{}:
      "after-quote"
    case BareCR{}:
      "bare-cr"
    case BareLF{}:
      "bare-lf"
    case FieldTooLong{}:
      "field-too-long"
    case TooManyFields{}:
      "too-many-fields"
    case Ragged{}:
      "ragged"

# The writer
# ==========
#
# A field is quoted exactly when it must be: it holds a quote, the
# delimiter, a CR or an LF; with pad, when it starts or ends with a
# space; and a record of one empty field is written "" so that it is
# not a blank line to CPython. Inside quotes a quote is doubled. Every
# record ends with CRLF.

def is_o(k: K) -> Bool:
  match k:
    case KO{}:
      True{}
    case _:
      False{}

def special(+d: Dialect, s: Bytes()) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{Chr{+c}, t}:
      Bool.not(is_o(cls(d, c))) || special(d, t)

def spaced(s: Bytes()) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{Chr{+c}, t}:
      U32.is_eq(c, 32) || U32.is_eq(Bytes.byte(String.get_end(SCon{Chr{c}, t}, 0n)), 32)

def needs(+d: Dialect, +s: Bytes()) -> Bool:
  special(d, s) || (pad(d) && spaced(s))

# a byte inside quotes: a quote is doubled
def esc.put(k: K, +c: U32, acc: Bytes()) -> Bytes():
  match k:
    case KQ{}:
      push(push(acc, c), c)
    case _:
      push(acc, c)

# the bytes of s, quotes doubled
def esc(+d: Dialect, s: Bytes(), acc: Bytes()) -> Bytes():
  match s:
    case SNil{}:
      acc
    case SCon{Chr{+c}, t}:
      esc(d, t, esc.put(cls(d, c), c, acc))

def quoted(+d: Dialect, s: Bytes(), acc: Bytes()) -> Bytes():
  push(esc(d, s, push(acc, quote(d))), quote(d))

def field.at(+d: Dialect, q: Bool, s: Bytes(), acc: Bytes()) -> Bytes():
  match q:
    case True{}:
      quoted(d, s, acc)
    case False{}:
      Bytes.append(acc, s)

def field(+d: Dialect, +s: Bytes(), acc: Bytes()) -> Bytes():
  field.at(d, needs(d, s), s, acc)

def crlf.put(acc: Bytes()) -> Bytes():
  push(push(acc, 13), 10)

# the fields after the first, each after a delimiter
def fields(+d: Dialect, r: List<&2, Bytes()>, acc: Bytes()) -> Bytes():
  match r:
    case Nil{}:
      acc
    case Con{+f, t}:
      fields(d, t, field(d, f, push(acc, delim(d))))

def record(+d: Dialect, r: List<&2, Bytes()>, acc: Bytes()) -> Bytes():
  match r:
    case Nil{}:
      crlf.put(acc)
    case Con{+f, t}:
      match t:
        case Nil{}:
          crlf.put(field.at(d, needs(d, f) || String.is_empty(f), f, acc))
        case Con{g, u}:
          crlf.put(fields(d, Con{g, u}, field(d, f, acc)))

def show.go(+d: Dialect, rs: List<&2, List<&2, Bytes()>>, acc: Bytes()) -> Bytes():
  match rs:
    case Nil{}:
      acc
    case Con{r, t}:
      show.go(d, t, record(d, r, acc))

def show(+d: Dialect, rs: List<&2, List<&2, Bytes()>>) -> Bytes():
  show.go(d, rs, "")

# Files
# =====
#
# fold_file reads a file in chunks of `chunk` bytes, hands each record
# to f as soon as it is complete, and keeps nothing of it: memory is one
# chunk and one record. It stops at the first refusal, and at the end of
# the file or a failed read it reads the end of input. read_file keeps
# every record.

def at_pos(p: P) -> Nat:
  match p:
    case P{m, fl, cur, out, w, pos}:
      pos

type Plan<A: Type> is Type:
  More{p: P, a: A}
  Stop{a: A, end: Out}

def fold.take(~A: Type, ~f: A -> List<&2, Bytes()> -> A, rs: List<&2, List<&2, Bytes()>>,
  a: A) -> A:
  match rs:
    case Nil{}:
      a
    case Con{r, t}:
      fold.take(~A, ~f, t, f(a, r))

# the records a read completed go to f; a refusal stops the loop
def fold.go(~A: Type, ~f: A -> List<&2, Bytes()> -> A, +d: Dialect, a: A, p: P) -> Plan<A>:
  match p:
    case P{m, fl, cur, out, w, pos}:
      match m:
        case Bad{at, why}:
          Stop{fold.take(~A, ~f, List.reverse(&2, List<&2, Bytes()>, out), a), Refused{at, why}}
        case _:
          More{P{m, fl, cur, Nil{}, w, pos},
            fold.take(~A, ~f, List.reverse(&2, List<&2, Bytes()>, out), a)}

def fold.last(~A: Type, ~f: A -> List<&2, Bytes()> -> A, +d: Dialect, a: A, qr: P & List<&2, List<&2, Bytes()>>) -> Plan<A>:
  (q, rs) = qr
  Stop{fold.take(~A, ~f, rs, a), result(d, q)}

def fold.end(~A: Type, ~f: A -> List<&2, Bytes()> -> A, +d: Dialect, a: A, p: P) -> Plan<A>:
  fold.last(~A, ~f, d, a, take(finish(d, p)))

def fold.at(~A: Type, ~f: A -> List<&2, Bytes()> -> A, +d: Dialect, z: Bool, +b: Bytes(),
  p: P, a: A) -> Plan<A>:
  match z:
    case True{}:
      fold.end(~A, ~f, d, a, p)
    case False{}:
      fold.go(~A, ~f, d, a, feed_buf(d, b, p))

def fold.plan(~A: Type, ~f: A -> List<&2, Bytes()> -> A, +d: Dialect,
  got: File & Result<&1, &1, U32 & String, Bytes()>, p: P, a: A) -> File & Plan<A>:
  (file, r) = got
  match r:
    case Fail{e}:
      (file, fold.end(~A, ~f, d, a, p))
    case Done{+b}:
      (file, fold.at(~A, ~f, d, String.is_empty(b), b, p, a))

def fold.stop(~A: Type, pl: Plan<A>) -> A & Out:
  match pl:
    case More{p, a}:
      (a, Refused{at_pos(p), Unclosed{}})
    case Stop{a, e}:
      (a, e)

def fold.loop(~A: Type, ~f: A -> List<&2, Bytes()> -> A, +d: Dialect, fuel: Nat, +chunk: U32,
  fp: File & Plan<A>) -> IO(File & (A & Out)):
  match fuel:
    case 0n:
      (file, pl) = fp
      IO.pure(File & (A & Out), (file, fold.stop(~A, pl)))
    case 1n+n:
      (file, pl) = fp
      match pl:
        case Stop{a, e}:
          IO.pure(File & (A & Out), (file, (a, e)))
        case More{p, a}:
          IO.bind(File & Result<&1, &1, U32 & String, Bytes()>, File & (A & Out),
            File.read_buf(file, chunk), got =>
              fold.loop(~A, ~f, d, n, chunk, fold.plan(~A, ~f, d, got, p, a)))

def fold.close(-A: Type, r: File & (A & Out)) -> IO(A & Out):
  (file, x) = r
  do IO<A & Out>:
    File.close(file)
    return x

def fold.open(~A: Type, ~f: A -> List<&2, Bytes()> -> A, +d: Dialect, +chunk: U32, a: A,
  r: Result<&1, &1, U32 & String, File>) -> IO(Result<&1, &1, U32 & String, A & Out>):
  match r:
    case Fail{e}:
      IO.pure(Result<&1, &1, U32 & String, A & Out>, Fail{e})
    case Done{file}:
      do IO<Result<&1, &1, U32 & String, A & Out>>:
        got : File & (A & Out) <- fold.loop(~A, ~f, d, U32.to_nat(4294967295), chunk,
          (file, More{new(d), a}))
        x : A & Out <- fold.close(A, got)
        return Done{x}

# every record of the file at path, in order, given to f from a; the
# answer is the fold and how the document ended: Read{head, []} with the
# header (the rows went to f), or the refusal
def fold_file(~A: Type, ~f: A -> List<&2, Bytes()> -> A, path: String, +d: Dialect,
  +chunk: U32, a: A) -> IO(Result<&1, &1, U32 & String, A & Out>):
  do IO<Result<&1, &1, U32 & String, A & Out>>:
    r : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
    fold.open(~A, ~f, d, chunk, a, r)

def keep(rs: List<&2, List<&2, Bytes()>>, r: List<&2, Bytes()>) -> List<&2, List<&2, Bytes()>>:
  r <> rs

def read_file.at(+d: Dialect, r: Result<&1, &1, U32 & String, List<&2, List<&2, Bytes()>> & Out>) ->
  Result<&1, &1, U32 & String, Out>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{(rs, e)}:
      match e:
        case Refused{at, why}:
          Done{Refused{at, why}}
        case Read{h, rows}:
          Done{table(d, List.reverse(&2, List<&2, Bytes()>, rs))}

# the whole file at path, read in 64 KiB chunks: what read gives for its
# bytes, or the error the file system gave
def read_file(path: String, +d: Dialect) -> IO(Result<&1, &1, U32 & String, Out>):
  do IO<Result<&1, &1, U32 & String, Out>>:
    r : Result<&1, &1, U32 & String, List<&2, List<&2, Bytes()>> & Out> <-
      fold_file(~List<&2, List<&2, Bytes()>>, ~keep, path, d, 65536, Nil{})
    return read_file.at(d, r)
