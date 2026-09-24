# bend-net: JSON bodies, on power/json_value.bend.
#
#   Json.respond(200, Json.obj([Json.kv("ok", Json.yes())]))    a response
#   Json.body(req, 65536)                       a request's body, parsed
#   Json.of(resp, 1048576)                      a response's body, parsed
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

# A number is its text (J.Num); J.to_i64 and J.to_f64 read one back.
def num(n: U32) -> J.Json:
  J.Num{U32.show(n)}

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

def as.str(m: Maybe<&2, J.Json>) -> Maybe<&2, Bytes()>:
  match m:
    case Some{v}:
      match v:
        case J.Str{s}:
          Some{s}
        case J.Num{t}:
          Some{t}
        case _:
          None{}
    case None{}:
      None{}

# a string's bytes, a number's text, or None
def get.str(j: J.Json, +key: Bytes()) -> Maybe<&2, Bytes()>:
  as.str(J.get(j, key))

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
