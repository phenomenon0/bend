# RESP, the Redis serialisation protocol, read and written.
#
# This file exists to test a claim rather than to serve Redis: that the
# reader shape the HTTP engine found -- one structural walk over
# whatever bytes arrive, the whole state in one node, never stopping --
# is a shape other protocols fit, and that its laws come with it. RESP
# is the harder case on purpose. HTTP framing is flat; RESP nests, an
# array holding arrays holding bulk strings, so the reader carries a
# stack and a finished value has to be handed to whatever was waiting
# for it, which may itself finish.
#
# What it accepts is RESP2, all five types, with a cap on a bulk, on an
# array's length and on how deep nesting may go. Anything else is Bad{}
# and never left, as in the HTTP reader and for the same reason.
import Base

# Bytes
# =====

# an ASCII literal as bytes
def bytes(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{Chr{c}, t}:
      Con{c, bytes(t)}

def cat(a: List<&2, U32>, b: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, a, b)

def rev(a: List<&2, U32>) -> List<&2, U32>:
  List.reverse(&2, U32, a)

def beq(a: List<&2, U32>, b: List<&2, U32>, acc: Bool) -> Bool:
  match a b:
    case Nil{} Nil{}:
      acc
    case Nil{} Con{y, u}:
      False{}
    case Con{x, t} Nil{}:
      False{}
    case Con{x, t} Con{y, u}:
      beq(t, u, acc && U32.is_eq(x, y))

def digit(+c: U32) -> Bool:
  U32.is_le(48, c) && U32.is_le(c, 57)

def lower.go(+c: U32, up: Bool) -> U32:
  match up:
    case True{}:
      (c + 32 : U32)
    case False{}:
      c

def lower(+c: U32) -> U32:
  lower.go(c, U32.is_le(65, c) && U32.is_le(c, 90))

# Values
# ======

# the five things RESP2 carries, and the null that a length of -1 means
type Val is Data:
  VStr{bs: List<&2, U32>}
  VErr{bs: List<&2, U32>}
  VInt{bs: List<&2, U32>}
  VBulk{bs: List<&2, U32>}
  VNil{}
  VArr{xs: List<&2, Val>}

# which line type is being read
type Ln is Data:
  KStr{}
  KErr{}
  KInt{}

def val.line(k: Ln, bs: List<&2, U32>) -> Val:
  match k:
    case KStr{}:
      VStr{bs}
    case KErr{}:
      VErr{bs}
    case KInt{}:
      VInt{bs}

# Caps
# ====

# the most a single bulk string may carry, the most elements an array
# may have, and the deepest arrays may nest. Each is refused at the
# byte that announces it, before anything is allocated for it.
def cap.bulk() -> U32:
  1048576

def cap.arr() -> U32:
  1048576

def cap.deep() -> U32:
  32

# The reader
# ==========

# Top    expecting a type byte
# Line   a simple string, error or integer, to its CR
# LineC  its CR seen, expecting the LF
# Len    the digits of a bulk's or an array's length
# LenC   their CR seen, expecting the LF
# Body   the bytes of a bulk, rem to go
# BodyC  all of them read, expecting the CR
# BodyL  expecting the LF
# Bad    the framing broke; absorbing, and never left
type Fs is Data:
  Top{}
  Line{k: Ln, acc: List<&2, U32>}
  LineC{k: Ln, acc: List<&2, U32>}
  Len{arr: Bool, n: U32, neg: Bool, any: Bool}
  LenC{arr: Bool, n: U32, neg: Bool}
  Body{rem: U32, acc: List<&2, U32>}
  BodyC{bs: List<&2, U32>}
  BodyL{bs: List<&2, U32>}
  Bad{}

# An array being filled: how many elements it still wants, and the ones
# it has, newest first. left is a Nat so the reader can match on it
# without computing, which is what lets close below be one self-
# recursive def rather than two that call each other.
type Fr is Data:
  Fr{left: Nat, got: List<&2, Val>}

# the whole reader: where it is, the arrays it is inside, how deep that
# is, and the values it has finished, newest first
type Rd is Data:
  Rd{at: Fs, up: List<&2, Fr>, deep: U32, out: List<&2, Val>}

def new() -> Rd:
  Rd{Top{}, Nil{}, 0, Nil{}}

def rev.vals(xs: List<&2, Val>) -> List<&2, Val>:
  List.reverse(&2, Val, xs)

# A finished value goes to the array that was waiting for it. If that
# array is now full it is a finished value itself, so this walks out
# through the stack it is given, which is why it terminates: every step
# is on a shorter stack.
def close(up: List<&2, Fr>, deep: U32, v: Val, out: List<&2, Val>) -> Rd:
  match up:
    case Nil{}:
      Rd{Top{}, Nil{}, 0, Con{v, out}}
    case Con{f, rest}:
      match f:
        case Fr{left, got}:
          match left:
            case 0n:
              Rd{Bad{}, Nil{}, 0, out}
            case 1n+k:
              match k:
                case 0n:
                  close(rest, (deep - 1 : U32), VArr{rev.vals(Con{v, got})}, out)
                case 1n+j:
                  Rd{Top{}, Con{Fr{1n+j, Con{v, got}}, rest}, deep, out}

# the type byte, its five tests handed in so the match is on parameters
def step.top.go(
  up: List<&2, Fr>, deep: U32, out: List<&2, Val>,
  str: Bool, err: Bool, int: Bool, blk: Bool, arr: Bool
) -> Rd:
  match str err int blk arr:
    case True{} _ _ _ _:
      Rd{Line{KStr{}, Nil{}}, up, deep, out}
    case False{} True{} _ _ _:
      Rd{Line{KErr{}, Nil{}}, up, deep, out}
    case False{} False{} True{} _ _:
      Rd{Line{KInt{}, Nil{}}, up, deep, out}
    case False{} False{} False{} True{} _:
      Rd{Len{False{}, 0, False{}, False{}}, up, deep, out}
    case False{} False{} False{} False{} True{}:
      Rd{Len{True{}, 0, False{}, False{}}, up, deep, out}
    case False{} False{} False{} False{} False{}:
      Rd{Bad{}, Nil{}, 0, out}

def step.top(up: List<&2, Fr>, deep: U32, out: List<&2, Val>, +c: U32) -> Rd:
  step.top.go(up, deep, out, U32.is_eq(c, 43), U32.is_eq(c, 45),
    U32.is_eq(c, 58), U32.is_eq(c, 36), U32.is_eq(c, 42))

def step.len.cr(
  arr: Bool, n: U32, neg: Bool, up: List<&2, Fr>, deep: U32,
  out: List<&2, Val>, any: Bool
) -> Rd:
  match any:
    case True{}:
      Rd{LenC{arr, n, neg}, up, deep, out}
    case False{}:
      Rd{Bad{}, Nil{}, 0, out}

# what a finished length means: a null, an empty array, a new frame to
# fill, an empty bulk, or a bulk body to read
def step.len.big(
  arr: Bool, n: U32, neg: Bool, up: List<&2, Fr>, deep: U32,
  out: List<&2, Val>, over: Bool
) -> Rd:
  match over:
    case True{}:
      Rd{Bad{}, Nil{}, 0, out}
    case False{}:
      Rd{Len{arr, n, neg, True{}}, up, deep, out}

def step.len.at(
  arr: Bool, +n: U32, neg: Bool, up: List<&2, Fr>, deep: U32,
  out: List<&2, Val>
) -> Rd:
  step.len.big(arr, n, neg, up, deep, out, U32.is_lt(cap.bulk(), n))

def step.len.on(
  arr: Bool, +n: U32, neg: Bool, up: List<&2, Fr>, deep: U32,
  out: List<&2, Val>, +c: U32
) -> Rd:
  step.len.at(arr, ((n * 10 : U32) + (c - 48 : U32) : U32), neg, up, deep, out)

def step.len.go(
  arr: Bool, n: U32, neg: Bool, any: Bool, up: List<&2, Fr>, deep: U32,
  out: List<&2, Val>, c: U32, cr: Bool, dig: Bool, minus: Bool
) -> Rd:
  match cr dig minus:
    case True{} _ _:
      step.len.cr(arr, n, neg, up, deep, out, any)
    case False{} True{} _:
      step.len.on(arr, n, neg, up, deep, out, c)
    case False{} False{} True{}:
      Rd{Len{arr, n, True{}, any}, up, deep, out}
    case False{} False{} False{}:
      Rd{Bad{}, Nil{}, 0, out}

def step.len(
  arr: Bool, n: U32, neg: Bool, +any: Bool, up: List<&2, Fr>, deep: U32,
  out: List<&2, Val>, +c: U32
) -> Rd:
  step.len.go(arr, n, neg, any, up, deep, out, c, U32.is_eq(c, 13), digit(c),
    U32.is_eq(c, 45) && Bool.not(any))

# a length past the cap is refused as it is read, so a huge one never
# becomes a huge allocation and never wraps
def step.len.done(
  arr: Bool, n: U32, up: List<&2, Fr>, deep: U32, out: List<&2, Val>,
  zero: Bool, over: Bool
) -> Rd:
  match arr zero over:
    case _ _ True{}:
      Rd{Bad{}, Nil{}, 0, out}
    case True{} True{} False{}:
      close(up, deep, VArr{Nil{}}, out)
    case True{} False{} False{}:
      Rd{Top{}, Con{Fr{U32.to_nat(n), Nil{}}, up}, (deep + 1 : U32), out}
    case False{} True{} False{}:
      Rd{BodyC{Nil{}}, up, deep, out}
    case False{} False{} False{}:
      Rd{Body{n, Nil{}}, up, deep, out}

def step.len.lf(
  +arr: Bool, +n: U32, neg: Bool, up: List<&2, Fr>, +deep: U32,
  out: List<&2, Val>
) -> Rd:
  match neg:
    case True{}:
      close(up, deep, VNil{}, out)
    case False{}:
      step.len.done(arr, n, up, deep, out, U32.is_zero(n),
        (arr && U32.is_lt(cap.arr(), n)) || (arr && U32.is_le(cap.deep(), deep)))

# a bulk's bytes, counted down
# a bulk's bytes, counted down
def step.body.go(
  rem: U32, acc: List<&2, U32>, up: List<&2, Fr>, deep: U32,
  out: List<&2, Val>, c: U32, last: Bool
) -> Rd:
  match last:
    case True{}:
      Rd{BodyC{rev(Con{c, acc})}, up, deep, out}
    case False{}:
      Rd{Body{(rem - 1 : U32), Con{c, acc}}, up, deep, out}

def step.body(
  +rem: U32, acc: List<&2, U32>, up: List<&2, Fr>, deep: U32,
  out: List<&2, Val>, c: U32
) -> Rd:
  step.body.go(rem, acc, up, deep, out, c, U32.is_eq(rem, 1))

def step.at.go(
  at: Fs, up: List<&2, Fr>, deep: U32, out: List<&2, Val>, c: U32,
  cr: Bool, lf: Bool
) -> Rd:
  match at:
    case Top{}:
      step.top(up, deep, out, c)
    case Line{k, acc}:
      match cr:
        case True{}:
          Rd{LineC{k, acc}, up, deep, out}
        case False{}:
          Rd{Line{k, Con{c, acc}}, up, deep, out}
    case LineC{k, acc}:
      match lf:
        case True{}:
          close(up, deep, val.line(k, rev(acc)), out)
        case False{}:
          Rd{Bad{}, Nil{}, 0, out}
    case Len{arr, n, neg, any}:
      step.len(arr, n, neg, any, up, deep, out, c)
    case LenC{arr, n, neg}:
      match lf:
        case True{}:
          step.len.lf(arr, n, neg, up, deep, out)
        case False{}:
          Rd{Bad{}, Nil{}, 0, out}
    case Body{rem, acc}:
      step.body(rem, acc, up, deep, out, c)
    case BodyC{bs}:
      match cr:
        case True{}:
          Rd{BodyL{bs}, up, deep, out}
        case False{}:
          Rd{Bad{}, Nil{}, 0, out}
    case BodyL{bs}:
      match lf:
        case True{}:
          close(up, deep, VBulk{bs}, out)
        case False{}:
          Rd{Bad{}, Nil{}, 0, out}
    case Bad{}:
      Rd{Bad{}, Nil{}, 0, out}

def step.at(
  at: Fs, up: List<&2, Fr>, deep: U32, out: List<&2, Val>, +c: U32
) -> Rd:
  step.at.go(at, up, deep, out, c, U32.is_eq(c, 13), U32.is_eq(c, 10))

def step(r: Rd, c: U32) -> Rd:
  match r:
    case Rd{at, up, deep, out}:
      step.at(at, up, deep, out, c)

# one structural walk over a chunk: the state that comes out is the
# state to feed the next chunk, and LAWS.bend says so
def feed(bs: List<&2, U32>, r: Rd) -> Rd:
  match bs:
    case Nil{}:
      r
    case Con{c, t}:
      feed(t, step(r, c))

# the values finished so far, oldest first, and the reader emptied
def take(r: Rd) -> Rd & List<&2, Val>:
  match r:
    case Rd{at, up, deep, out}:
      (Rd{at, up, deep, Nil{}}, rev.vals(out))

def dead.at(at: Fs, up: List<&2, Fr>, deep: U32, out: List<&2, Val>) -> Rd & Bool:
  match at:
    case Bad{}:
      (Rd{Bad{}, Nil{}, 0, out}, True{})
    case Top{}:
      (Rd{Top{}, up, deep, out}, False{})
    case Line{k, acc}:
      (Rd{Line{k, acc}, up, deep, out}, False{})
    case LineC{k, acc}:
      (Rd{LineC{k, acc}, up, deep, out}, False{})
    case Len{arr, n, neg, any}:
      (Rd{Len{arr, n, neg, any}, up, deep, out}, False{})
    case LenC{arr, n, neg}:
      (Rd{LenC{arr, n, neg}, up, deep, out}, False{})
    case Body{rem, acc}:
      (Rd{Body{rem, acc}, up, deep, out}, False{})
    case BodyC{bs}:
      (Rd{BodyC{bs}, up, deep, out}, False{})
    case BodyL{bs}:
      (Rd{BodyL{bs}, up, deep, out}, False{})

def dead(r: Rd) -> Rd & Bool:
  match r:
    case Rd{at, up, deep, out}:
      dead.at(at, up, deep, out)

# Writing
# =======

def crlf() -> List<&2, U32>:
  [13, 10]

def line(tag: U32, bs: List<&2, U32>) -> List<&2, U32>:
  Con{tag, cat(bs, crlf())}

def simple(s: String) -> List<&2, U32>:
  line(43, bytes(s))

def error(s: String) -> List<&2, U32>:
  line(45, bytes(s))

def integer(+n: U32) -> List<&2, U32>:
  line(58, bytes(U32.show(n)))

def nil() -> List<&2, U32>:
  bytes("$-1\r\n")

# a bulk carries its own length, so it is the one reply that has to
# measure what it is sending
def bulk(+bs: List<&2, U32>) -> List<&2, U32>:
  cat(line(36, bytes(Nat.show(List.length(&2, U32, bs)))), cat(bs, crlf()))

def array.go(xs: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      cat(h, array.go(t))

def array(+xs: List<&2, List<&2, U32>>) -> List<&2, U32>:
  cat(line(42, bytes(Nat.show(List.length(&2, List<&2, U32>, xs)))), array.go(xs))
