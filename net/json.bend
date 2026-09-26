# bend-net: JSON bodies, on power/json_value.bend.
#
#   Json.respond(200, Json.obj([Json.kv("ok", Json.yes())]))    a response
#   Json.body(req, 65536)                       a request's body, parsed
#   Json.of(resp, 1048576)                      a response's body, parsed
#
#   Json.get.u32(j, "limits.max")               a field, typed: its value or why not
#
# A body is parsed under a budget of bytes (json_value's limits: 64
# deep, the budget, duplicate keys kept and the last one read), and a
# body that is not JSON is a typed refusal (J.Why), never a guess.
import Base
import ../power/json_value.bend as J
import ./http.bend as Http

def Json() -> Data:
  J.Json

def str(s: Bytes()) -> J.Json:
  J.Str{s}

# A number is its text (J.Num); the getters below read one back.
def num(n: U32) -> J.Json:
  J.Num{U32.show(n)}

def nat(n: Nat) -> J.Json:
  J.Num{Nat.show(n)}

def dec.frac(+q: Nat, +r: Nat, +places: Nat) -> Bytes():
  Bool.pick(Bytes(), Nat.is_eq(places, 0n), Nat.show(q),
    Bytes.concat([Nat.show(q), ".", String.pad_start(Nat.show(r), places, '0')]))

# n / 10^places, written with that many decimals: dec(9995n, 2n) is 99.95
def dec(n: Nat, +places: Nat) -> J.Json:
  +p = Nat.pow(10n, places)
  +m = n
  J.Num{dec.frac(Nat.div(m, p), Nat.mod(m, p), places)}

def i64.mag(n: I64) -> Bytes():
  match n:
    case I64{w}:
      Nat.show(Word.to_nat(64n, w))

def i64(+n: I64) -> J.Json:
  J.Num{Bool.pick(Bytes(), I64.is_neg(n), Bytes.append("-", i64.mag(I64.neg(n))), i64.mag(n))}

def f64.of(+t: Bytes()) -> J.Json:
  Bool.pick(J.Json, String.eq(t, "nan") || String.eq(t, "inf") || String.eq(t, "-inf"), J.Null{}, J.Num{t})

# the shortest text that reads back as x (-1.5, 0.1, 1e+21); JSON has no
# NaN or infinity, so those are null
def f64(x: F64) -> J.Json:
  f64.of(F64.show(x))

def yes() -> J.Json:
  J.Flag{True{}}

def no() -> J.Json:
  J.Flag{False{}}

def flag(b: Bool) -> J.Json:
  J.Flag{b}

def null() -> J.Json:
  J.Null{}

def arr(xs: List<&2, J.Json>) -> J.Json:
  J.Arr{xs}

def kv(k: Bytes(), v: J.Json) -> Sigma<&2, &2, Bytes(), _ => J.Json>:
  (k, v)

def obj(kvs: List<&2, Sigma<&2, &2, Bytes(), _ => J.Json>>) -> J.Json:
  J.Obj{kvs}

# a value's text
def text(j: J.Json) -> Bytes():
  J.show(j)

# a JSON response
def respond(status: U32, j: J.Json) -> Http.Response:
  Http.json(status, J.show(j))

# a parse, under a budget of bytes
def parse(+b: Bytes(), +budget: U32) -> Result<&2, &2, J.Why, J.Json>:
  J.parse(b, J.lim(budget))

# a request's body, parsed
def body(r: Http.Request, +budget: U32) -> Result<&2, &2, J.Why, J.Json>:
  parse(Http.body(r), budget)

# a response's body, parsed
def of(r: Http.Response, +budget: U32) -> Result<&2, &2, J.Why, J.Json>:
  parse(Http.resp.body(r), budget)

# an object's value at key (the last, if it repeats)
def get(j: J.Json, +key: Bytes()) -> Maybe<&2, J.Json>:
  J.get(j, key)

# Paths
# -----
#
# A path is keys joined by '.': "a.b" is b in a's object, and a segment
# of digits in an array is its item ("monitors.0.name"). Json.get reads
# one key as it is, a '.' in it too.

def path.item(xs: List<&2, J.Json>, m: Maybe<&2, Nat>) -> Maybe<&2, J.Json>:
  match m:
    case Some{i}:
      J.at(J.Arr{xs}, i)
    case None{}:
      None{}

def path.in(v: J.Json, +k: Bytes()) -> Maybe<&2, J.Json>:
  match v:
    case J.Arr{xs}:
      path.item(xs, Maybe.map(&2, U32, Nat, U32.to_nat, U32.read(k)))
    case J.Obj{kvs}:
      J.get(J.Obj{kvs}, k)
    case _:
      None{}

def path.go(ks: List<&2, Bytes()>, m: Maybe<&2, J.Json>) -> Maybe<&2, J.Json>:
  match ks:
    case Nil{}:
      m
    case Con{+k, t}:
      path.go(t, Maybe.bind(&2, J.Json, J.Json, m, v => path.in(v, k)))

# a path's keys: its bytes cut at every '.'
def path.keys(s: Bytes(), +cur: Bytes()) -> List<&2, Bytes()>:
  match s:
    case SNil{}:
      [cur]
    case SCon{Chr{+c}, +t}:
      Bool.pick(List<&2, Bytes()>, U32.is_eq(c, 46), Con{cur, path.keys(t, "")}, path.keys(t, Bytes.push(cur, c)))

# the value at a path, or None
def path(j: J.Json, +p: Bytes()) -> Maybe<&2, J.Json>:
  path.go(path.keys(p, ""), Some{j})

# Typed fields
# ------------
#
# Json.get.str/u32/nat/i64/f64/bool/arr/obj(j, path): the value, of that
# type, or why not, as a message naming the path: "name is required",
# "interval_ms must be a number", "expect must be a whole number from 0
# to 4294967295". Nothing is converted: a number is not a string, "1" is
# not a number, 1.5 is not a whole one. Json.or gives a default for a
# missing field (a wrong one still fails), Json.fails gathers every
# reason, and Json.errors answers them.

def Got(A: Data) -> Data:
  Result<&2, &2, Bytes(), A>

def missing(-A: Data, +p: Bytes()) -> Got(A):
  Fail{Bytes.append(p, " is required")}

def wrong(-A: Data, +p: Bytes(), what: Bytes()) -> Got(A):
  Fail{Bytes.concat([p, " must be ", what])}

def str.at(+p: Bytes(), m: Maybe<&2, J.Json>) -> Got(Bytes()):
  match m:
    case None{}:
      missing(Bytes(), p)
    case Some{v}:
      match v:
        case J.Str{s}:
          Done{s}
        case _:
          wrong(Bytes(), p, "a string")

def get.str(j: J.Json, p: Bytes()) -> Got(Bytes()):
  +q = p
  str.at(q, path(j, q))

def u32.of(+p: Bytes(), m: Maybe<&2, U32>) -> Got(U32):
  match m:
    case Some{n}:
      Done{n}
    case None{}:
      wrong(U32, p, "a whole number from 0 to 4294967295")

def u32.at(+p: Bytes(), m: Maybe<&2, J.Json>) -> Got(U32):
  match m:
    case None{}:
      missing(U32, p)
    case Some{v}:
      match v:
        case J.Num{t}:
          u32.of(p, U32.read(t))
        case _:
          wrong(U32, p, "a number")

def get.u32(j: J.Json, p: Bytes()) -> Got(U32):
  +q = p
  u32.at(q, path(j, q))

def nat.of(+p: Bytes(), m: Maybe<&2, Nat>) -> Got(Nat):
  match m:
    case Some{n}:
      Done{n}
    case None{}:
      wrong(Nat, p, "a whole number from 0 to 281474976710655")

# digits only, at most 15 of them, and 281474976710655 (2^48 - 1, Nat's
# bound) at most
def nat.digit(+c: U32) -> Bool:
  (c >= 48 : U32) && (c <= 57 : U32)

def nat.digits(s: Bytes()) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{Chr{+c}, t}:
      nat.digit(c) && nat.digits(t)

def nat.fits(+t: Bytes()) -> Bool:
  +n = Bytes.len(t)
  Nat.is_gt(n, 0n) && nat.digits(t) && (Nat.is_lt(n, 15n) || (Nat.is_eq(n, 15n) && Bool.not(String.is_gt(t, "281474976710655"))))

def nat.value(s: Bytes(), acc: Nat) -> Nat:
  match s:
    case SNil{}:
      acc
    case SCon{Chr{c}, t}:
      nat.value(t, Nat.add(Nat.mul(acc, 10n), U32.to_nat(U32.sub(c, 48))))

def nat.read(+t: Bytes()) -> Maybe<&2, Nat>:
  Bool.pick(Maybe<&2, Nat>, nat.fits(t), Some{nat.value(t, 0n)}, None{})

def nat.at(+p: Bytes(), m: Maybe<&2, J.Json>) -> Got(Nat):
  match m:
    case None{}:
      missing(Nat, p)
    case Some{v}:
      match v:
        case J.Num{t}:
          nat.of(p, nat.read(t))
        case _:
          wrong(Nat, p, "a number")

def get.nat(j: J.Json, p: Bytes()) -> Got(Nat):
  +q = p
  nat.at(q, path(j, q))

def i64.of(+p: Bytes(), m: Maybe<&2, I64>) -> Got(I64):
  match m:
    case Some{n}:
      Done{n}
    case None{}:
      wrong(I64, p, "a whole number from -9223372036854775808 to 9223372036854775807")

def i64.at(+p: Bytes(), m: Maybe<&2, J.Json>) -> Got(I64):
  match m:
    case None{}:
      missing(I64, p)
    case Some{v}:
      match v:
        case J.Num{t}:
          i64.of(p, J.to_i64(J.Num{t}))
        case _:
          wrong(I64, p, "a number")

def get.i64(j: J.Json, p: Bytes()) -> Got(I64):
  +q = p
  i64.at(q, path(j, q))

def f64.num(+p: Bytes(), m: Maybe<&2, F64>) -> Got(F64):
  match m:
    case Some{x}:
      Done{x}
    case None{}:
      wrong(F64, p, "a number")

def f64.at(+p: Bytes(), m: Maybe<&2, J.Json>) -> Got(F64):
  match m:
    case None{}:
      missing(F64, p)
    case Some{v}:
      f64.num(p, J.to_f64(v))

def get.f64(j: J.Json, p: Bytes()) -> Got(F64):
  +q = p
  f64.at(q, path(j, q))

def bool.at(+p: Bytes(), m: Maybe<&2, J.Json>) -> Got(Bool):
  match m:
    case None{}:
      missing(Bool, p)
    case Some{v}:
      match v:
        case J.Flag{b}:
          Done{b}
        case _:
          wrong(Bool, p, "true or false")

def get.bool(j: J.Json, p: Bytes()) -> Got(Bool):
  +q = p
  bool.at(q, path(j, q))

def arr.at(+p: Bytes(), m: Maybe<&2, J.Json>) -> Got(List<&2, J.Json>):
  match m:
    case None{}:
      missing(List<&2, J.Json>, p)
    case Some{v}:
      match v:
        case J.Arr{xs}:
          Done{xs}
        case _:
          wrong(List<&2, J.Json>, p, "an array")

def get.arr(j: J.Json, p: Bytes()) -> Got(List<&2, J.Json>):
  +q = p
  arr.at(q, path(j, q))

def obj.at(+p: Bytes(), m: Maybe<&2, J.Json>) -> Got(J.Json):
  match m:
    case None{}:
      missing(J.Json, p)
    case Some{v}:
      match v:
        case J.Obj{kvs}:
          Done{J.Obj{kvs}}
        case _:
          wrong(J.Json, p, "an object")

# an object, as a J.Json the getters read on
def get.obj(j: J.Json, p: Bytes()) -> Got(J.Json):
  +q = p
  obj.at(q, path(j, q))

def or.at(-A: Data, j: J.Json, +p: Bytes(), d: A, get: J.Json -> Bytes() -> Got(A), m: Maybe<&2, J.Json>) -> Got(A):
  match m:
    case None{}:
      Done{d}
    case Some{v}:
      get(j, p)

# get(j, p), or d when the field is missing (a wrong one still fails):
# Json.or(U32, j, "interval_ms", 60000, Json.get.u32)
def or(-A: Data, +j: J.Json, +p: Bytes(), d: A, get: J.Json -> Bytes() -> Got(A)) -> Got(A):
  or.at(A, j, p, d, get, path(j, p))

# why r failed, in front of whys; whys when it did not
def fails(-A: Data, r: Got(A), whys: List<&2, Bytes()>) -> List<&2, Bytes()>:
  match r:
    case Done{v}:
      whys
    case Fail{e}:
      Con{e, whys}

def strs(xs: List<&2, Bytes()>) -> List<&2, J.Json>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{str(x), strs(t)}

def why.show(w: J.Why) -> Bytes():
  match w:
    case J.Syntax{at, e}:
      Bytes.append("syntax error at byte ", U32.show(at))
    case J.TooDeep{at}:
      Bytes.append("nested too deep at byte ", U32.show(at))
    case J.Budget{at}:
      Bytes.append("past the budget at byte ", U32.show(at))
    case J.DupKey{at}:
      Bytes.append("a key twice at byte ", U32.show(at))
    case J.BadUtf8{at}:
      Bytes.append("not UTF-8 at byte ", U32.show(at))
    case J.Lone{at}:
      Bytes.append("a lone surrogate at byte ", U32.show(at))

# a 400 saying why a body was refused, as JSON
def refused(w: J.Why) -> Http.Response:
  respond(400, obj([kv("error", str(why.show(w)))]))

# every reason a request is refused, as JSON: {"errors": ["...", ...]}
def errors(status: U32, whys: List<&2, Bytes()>) -> Http.Response:
  respond(status, obj([kv("errors", arr(strs(whys)))]))
