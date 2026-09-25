# JSON

`net/json.bend` writes and reads JSON on `power/json_value.bend`. The tour is
`bend guide networking`.

## Values Out

Build a value with `Json.obj`, `Json.kv`, `Json.arr`, `Json.str`, `Json.num` (a
`U32`), `Json.nat` (a `Nat`), `Json.i64` (an `I64`), `Json.f64` (an `F64`; NaN
and infinities are `null`), `Json.dec(n, places)` (`n` over `10^places`, with
that many decimals: `Json.dec(9995n, 2n)` is `99.95`), `Json.flag(b)`,
`Json.yes`, `Json.no` and `Json.null`, and answer it with
`Json.respond(status, j)`. `Json.text(j)` is its text, for a request body.

```python
def note(id: Bytes(), text: Bytes()) -> J.Json:
  Json.obj([Json.kv("id", Json.str(id)), Json.kv("text", Json.str(text))])
```

## Values In

`Json.body(req, budget)` parses a request's body and `Json.of(resp, budget)` a
response's. Both answer `Result<&2, &2, J.Why, J.Json>`: the value, or why it
was refused (a syntax error, too deep, past the budget, not UTF-8, a lone
surrogate, each with its byte). `Json.refused(why)` is a 400 that says why, as
JSON:

```python
def add.body(+db: Chan(Store), r: Result<&2, &2, J.Why, J.Json>) -> IO(Http.Response):
  match r:
    case Done{j}:
      add.text(db, Json.get.str(j, "text"))
    case Fail{w}:
      Http.reply(Json.refused(w))
```

## Typed Fields

`Json.get.str`, `u32`, `nat`, `i64`, `f64`, `bool`, `arr` and `obj`, each
`(j, path)`, answer `Json.Got(A)`, which is `Result<&2, &2, Bytes(), A>`: the
field's value, or why not, in words that name it: `name is required`, `text
must be a string`, `age must be a whole number from 0 to 4294967295`. Nothing
is converted: a number is not a string, `"1"` is not a number, `1.5` is not a
whole one. A path is keys joined by `.`, and a segment of digits is an
array's item: `Json.get.str(j, "monitors.0.name")`. `Json.get(j, key)` reads
one key as it is, untyped, as a `Maybe`.

```python
# the note's text: a string, or a 422 that says why not ("text is
# required", "text must be a string")
def add.text(+db: Chan(Store), m: Json.Got(Bytes())) -> IO(Http.Response):
  match m:
    case Done{+text}:
      locked(db, st => add.of(text, st))
    case Fail{why}:
      Http.reply(Json.errors(422, [why]))
```

`Json.or(A, j, path, d, get)` is `get(j, path)`, or `d` when the field is
missing (one of the wrong type still fails). `Json.fails(A, r, whys)` puts
`r`'s reason in front of `whys` when it failed, so every field is read and every
problem kept; `Json.errors(status, whys)` answers them as
`{"errors": [...]}`; and `Result.default` takes a value out. A handler that
checks a whole body in one go:

```python
# every field read, every reason kept: a 201 with what was read, or a 400
def checked(+name: Json.Got(Bytes()), +age: Json.Got(U32), +email: Json.Got(Bytes()),
  +tags: Json.Got(List<&2, J.Json>), +news: Json.Got(Bool)) -> Http.Response:
  +whys = Json.fails(Bytes(), name, Json.fails(U32, age, Json.fails(Bytes(), email,
    Json.fails(List<&2, J.Json>, tags, Json.fails(Bool, news, [])))))
```

```python
def signup.of(+j: J.Json) -> Http.Response:
  checked(Json.get.str(j, "name"), age.ok(Json.get.u32(j, "age")), Json.get.str(j, "email"),
    Json.or(List<&2, J.Json>, j, "tags", [], Json.get.arr), Json.or(Bool, j, "newsletter", False{}, Json.get.bool))
```

```bash
curl -s localhost:8080/signup -d '{"name":7,"age":-1}'
{"errors":["name must be a string","age must be a whole number from 0 to 4294967295","email is required"]}
```

The whole program is `net/examples/signup.bend`.

## Fetch, Parse, Serve

`net/examples/relay.bend` is a small API in front of another one. It gets the
upstream's JSON, keeps the fields it promises, and gives every failure its own
answer:

```python
# GET /users/:id: on the session's connections, the upstream given 2 s
# (the session's timeout, 5 s, is for its other requests)
def user(+env: Env, r: Http.Request) -> IO(Http.Response):
  +id = Http.param(r, "id")
  +up = env.up(env)
  +url = Bytes.concat([up, "/users/", Http.pct.encode(id)])
  do IO<Http.Response>:
    res : Client.Res() <- Client.fetch.with(env.s(env), Client.req("GET", url), o => Client.with.timeout(o, 2000))
    fetched(id, up, res)
```

A body is parsed under the budget you pass, at most 64 containers deep, with
a repeated key's last value read.
