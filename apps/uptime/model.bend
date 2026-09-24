# bend-uptime's data: a monitor's spec, its probes, its hourly counts,
# and the store of all of them; their JSON both ways, and the checks a
# spec must pass (from the config file, the ops log, or POST).
import Base
import ../../net/json.bend as Json
import ../../net/url.bend as Url
import ../../power/json_value.bend as J
import ./clock.bend as Time

# one probe: when (wall ms), up or not, latency, status (0: none came),
# why it is down ("" when up), and how late it started (ms past its slot)
type Probe is Data:
  Probe{t: Nat, up: Bool, ms: U32, code: U32, err: Bytes(), lag: U32}

# the probes of one hour (t / 3600000): how many were up, of how many
type Bucket is Data:
  Bucket{hour: Nat, up: U32, all: U32}

type Spec is Data:
  Spec{name: Bytes(), url: Bytes(), every: U32, timeout: U32, expect: U32, needle: Bytes()}

# state: 0 pending (no probe yet), 1 up, 2 down; hist newest first, n
# its length; hours newest first, at most 25
type Mon is Data:
  Mon{id: U32, spec: Spec, state: U32, n: Nat, hist: List<&2, Probe>, hours: List<&2, Bucket>}

type Store is Data:
  Store{next: U32, mons: List<&2, Mon>}

# a spec that passed, or every reason it did not
type Checked is Data:
  Checked{errs: List<&2, Bytes()>, spec: Spec}

def cap() -> Nat:
  500n

def store.new() -> Store:
  Store{1, []}

# Accessors
# ---------

def spec.name(s: Spec) -> Bytes():
  match s:
    case Spec{name, url, every, timeout, expect, needle}:
      name

def spec.url(s: Spec) -> Bytes():
  match s:
    case Spec{name, url, every, timeout, expect, needle}:
      url

def spec.every(s: Spec) -> U32:
  match s:
    case Spec{name, url, every, timeout, expect, needle}:
      every

def spec.timeout(s: Spec) -> U32:
  match s:
    case Spec{name, url, every, timeout, expect, needle}:
      timeout

def spec.expect(s: Spec) -> U32:
  match s:
    case Spec{name, url, every, timeout, expect, needle}:
      expect

def spec.needle(s: Spec) -> Bytes():
  match s:
    case Spec{name, url, every, timeout, expect, needle}:
      needle

def mon.id(m: Mon) -> U32:
  match m:
    case Mon{id, spec, state, n, hist, hours}:
      id

def mon.spec(m: Mon) -> Spec:
  match m:
    case Mon{id, spec, state, n, hist, hours}:
      spec

def mon.name(m: Mon) -> Bytes():
  spec.name(mon.spec(m))

def mon.hist(m: Mon) -> List<&2, Probe>:
  match m:
    case Mon{id, spec, state, n, hist, hours}:
      hist

def mon.hours(m: Mon) -> List<&2, Bucket>:
  match m:
    case Mon{id, spec, state, n, hist, hours}:
      hours

def mon.state(m: Mon) -> U32:
  match m:
    case Mon{id, spec, state, n, hist, hours}:
      state

def probe.up(p: Probe) -> Bool:
  match p:
    case Probe{t, up, ms, code, err, lag}:
      up

def probe.t(p: Probe) -> Nat:
  match p:
    case Probe{t, up, ms, code, err, lag}:
      t

def state.of(up: Bool) -> U32:
  match up:
    case True{}:
      1
    case False{}:
      2

def state.show(+s: U32) -> Bytes():
  Bool.pick(Bytes(), U32.is_eq(s, 1), "up", Bool.pick(Bytes(), U32.is_eq(s, 2), "down", "pending"))

# JSON out
# --------

def nat(+n: Nat) -> J.Json:
  J.Num{Nat.show(n)}

def spec.kvs(s: Spec) -> List<&2, Sigma<&2, &2, Bytes(), _ => J.Json>>:
  match s:
    case Spec{name, url, every, timeout, expect, needle}:
      [Json.kv("name", Json.str(name)), Json.kv("url", Json.str(url)), Json.kv("interval_ms", Json.num(every)),
       Json.kv("timeout_ms", Json.num(timeout)), Json.kv("expect", Json.num(expect)), Json.kv("body", Json.str(needle))]

def spec.json(s: Spec) -> J.Json:
  Json.obj(spec.kvs(s))

def probe.kvs(p: Probe) -> List<&2, Sigma<&2, &2, Bytes(), _ => J.Json>>:
  match p:
    case Probe{+t, up, ms, code, err, lag}:
      [Json.kv("t", nat(t)), Json.kv("at", Json.str(Time.iso(t))), Json.kv("up", Json.flag(up)),
       Json.kv("ms", Json.num(ms)), Json.kv("code", Json.num(code)), Json.kv("err", Json.str(err)),
       Json.kv("lag", Json.num(lag))]

def probe.json(p: Probe) -> J.Json:
  Json.obj(probe.kvs(p))

# a probe as a log line and a live message: its monitor's name first
def probe.line(name: Bytes(), p: Probe) -> Bytes():
  Json.text(Json.obj(Con{Json.kv("name", Json.str(name)), probe.kvs(p)}))

def probes.json(ps: List<&2, Probe>) -> List<&2, J.Json>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      Con{probe.json(p), probes.json(t)}

# the ups and alls of the buckets of the last 24 hours (the current one
# and the 23 before it)
def hours.sum(hs: List<&2, Bucket>, +now: Nat, acc: U32 & U32) -> U32 & U32:
  match hs:
    case Nil{}:
      acc
    case Con{b, t}:
      match b:
        case Bucket{+hour, +up, +all}:
          (+u, +a) = acc
          hours.sum(t, now, Bool.pick(U32 & U32, Nat.is_lt(now, Nat.add(hour, 24n)), ((u + up : U32), (a + all : U32)), (u, a)))

# up / all as a percentage with two decimals (99.95), a JSON number;
# null when nothing was probed
def percent(+up: U32, +all: U32) -> J.Json:
  +bp = U32.div((up * 10000 : U32), all)
  Bool.pick(J.Json, U32.is_eq(all, 0), Json.null(),
    J.Num{U32.show(U32.div(bp, 100)) ++ "." ++ String.pad_start(U32.show(U32.mod(bp, 100)), 2n, '0')})

def last.json(hist: List<&2, Probe>) -> J.Json:
  match hist:
    case Nil{}:
      Json.null()
    case Con{p, t}:
      probe.json(p)

def mon.json.at(m: Mon, ua: U32 & U32) -> J.Json:
  match m:
    case Mon{id, spec, +state, n, hist, hours}:
      (+up, +all) = ua
      Json.obj(List.append(&2, Sigma<&2, &2, Bytes(), _ => J.Json>, spec.kvs(spec),
        [Json.kv("state", Json.str(state.show(state))), Json.kv("last", last.json(hist)),
         Json.kv("uptime_24h", percent(up, all)), Json.kv("checks_24h", Json.num(all))]))

# a monitor as GET /api/monitors shows it; now is the current hour
def mon.json(+now: Nat, +m: Mon) -> J.Json:
  mon.json.at(m, hours.sum(mon.hours(m), now, (0, 0)))

# JSON in: the checks
# -------------------

# a field read as a string: missing is d (None: required)
def field.str(m: Maybe<&2, J.Json>, +key: Bytes(), d: Maybe<&2, Bytes()>) -> Result<&2, &2, Bytes(), Bytes()>:
  match m:
    case None{}:
      match d:
        case Some{v}:
          Done{v}
        case None{}:
          Fail{key ++ " is required"}
    case Some{v}:
      match v:
        case J.Str{s}:
          Done{s}
        case _:
          Fail{key ++ " must be a string"}

def field.num.read(+key: Bytes(), r: Maybe<&2, U32>) -> Result<&2, &2, Bytes(), U32>:
  match r:
    case Some{n}:
      Done{n}
    case None{}:
      Fail{key ++ " must be a whole number of at most 4294967295"}

# a field read as a U32: missing is d (None: required)
def field.num(m: Maybe<&2, J.Json>, +key: Bytes(), d: Maybe<&2, U32>) -> Result<&2, &2, Bytes(), U32>:
  match m:
    case None{}:
      match d:
        case Some{v}:
          Done{v}
        case None{}:
          Fail{key ++ " is required"}
    case Some{v}:
      match v:
        case J.Num{t}:
          field.num.read(key, U32.read(t))
        case _:
          Fail{key ++ " must be a number"}

# a U32 in [lo, hi]
def within(r: Result<&2, &2, Bytes(), U32>, +key: Bytes(), +lo: U32, +hi: U32) -> Result<&2, &2, Bytes(), U32>:
  match r:
    case Done{+n}:
      Bool.pick(Result<&2, &2, Bytes(), U32>, (n >= lo : U32) && (n <= hi : U32), Done{n},
        Fail{key ++ " must be between " ++ U32.show(lo) ++ " and " ++ U32.show(hi)})
    case Fail{e}:
      Fail{e}

def name.char(+c: Char) -> Bool:
  Char.is_alpha(c) || Char.is_digit(c) || Char.is_eq(c, '-') || Char.is_eq(c, '_') || Char.is_eq(c, '.')

def name.chars(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      name.char(c) && name.chars(t)

# a name is a path segment: 1 to 64 of [A-Za-z0-9._-]
def name.ok(r: Result<&2, &2, Bytes(), Bytes()>) -> Result<&2, &2, Bytes(), Bytes()>:
  match r:
    case Done{+s}:
      Bool.pick(Result<&2, &2, Bytes(), Bytes()>,
        Nat.is_gt(Bytes.len(s), 0n) && Nat.is_le(Bytes.len(s), 64n) && name.chars(s), Done{s},
        Fail{"name must be 1 to 64 of A-Z a-z 0-9 . _ -"})
    case Fail{e}:
      Fail{e}

def url.why(r: Result<&2, &2, Bytes(), Url.Url>) -> Maybe<&2, Bytes()>:
  match r:
    case Done{u}:
      None{}
    case Fail{e}:
      Some{e}

def url.ok.at(+s: Bytes(), m: Maybe<&2, Bytes()>) -> Result<&2, &2, Bytes(), Bytes()>:
  match m:
    case None{}:
      Done{s}
    case Some{e}:
      Fail{"url is not an http(s) URL: " ++ e}

def url.ok(r: Result<&2, &2, Bytes(), Bytes()>) -> Result<&2, &2, Bytes(), Bytes()>:
  match r:
    case Done{+s}:
      url.ok.at(s, url.why(Url.parse(s)))
    case Fail{e}:
      Fail{e}

def errs.one(-A: Data, r: Result<&2, &2, Bytes(), A>, rest: List<&2, Bytes()>) -> List<&2, Bytes()>:
  match r:
    case Done{v}:
      rest
    case Fail{e}:
      Con{e, rest}

def val(-A: Data, r: Result<&2, &2, Bytes(), A>, d: A) -> A:
  match r:
    case Done{v}:
      v
    case Fail{e}:
      d

# the timeout must leave the interval room
def timeout.fits(t: Result<&2, &2, Bytes(), U32>, +every: U32) -> Result<&2, &2, Bytes(), U32>:
  match t:
    case Done{+n}:
      Bool.pick(Result<&2, &2, Bytes(), U32>, (n <= every : U32), Done{n},
        Fail{"timeout_ms must not exceed interval_ms"})
    case Fail{e}:
      Fail{e}

def check.fields(+name: Result<&2, &2, Bytes(), Bytes()>, +url: Result<&2, &2, Bytes(), Bytes()>,
  +every: Result<&2, &2, Bytes(), U32>, +timeout: Result<&2, &2, Bytes(), U32>, +expect: Result<&2, &2, Bytes(), U32>,
  +needle: Result<&2, &2, Bytes(), Bytes()>) -> Checked:
  +tfit = timeout.fits(timeout, val(U32, every, 4294967295))
  Checked{errs.one(Bytes(), name, errs.one(Bytes(), url, errs.one(U32, every, errs.one(U32, tfit,
      errs.one(U32, expect, errs.one(Bytes(), needle, [])))))),
    Spec{val(Bytes(), name, ""), val(Bytes(), url, ""), val(U32, every, 0), val(U32, tfit, 0),
      val(U32, expect, 0), val(Bytes(), needle, "")}}

def check.obj(+j: J.Json) -> Checked:
  check.fields(name.ok(field.str(Json.get(j, "name"), "name", None{})),
    url.ok(field.str(Json.get(j, "url"), "url", None{})),
    within(field.num(Json.get(j, "interval_ms"), "interval_ms", Some{60000}), "interval_ms", 200, 86400000),
    within(field.num(Json.get(j, "timeout_ms"), "timeout_ms", Some{5000}), "timeout_ms", 50, 60000),
    within(field.num(Json.get(j, "expect"), "expect", Some{200}), "expect", 100, 599),
    field.str(Json.get(j, "body"), "body", Some{""}))

# a monitor's JSON, checked: every reason it is refused, or its spec
def check(+j: J.Json) -> Checked:
  match j:
    case J.Obj{kvs}:
      check.obj(j)
    case _:
      Checked{["a monitor must be a JSON object"], Spec{"", "", 0, 0, 0, ""}}

def checked.errs(c: Checked) -> List<&2, Bytes()>:
  match c:
    case Checked{errs, spec}:
      errs

def checked.spec(c: Checked) -> Spec:
  match c:
    case Checked{errs, spec}:
      spec

def u32.of(m: Maybe<&2, Bytes()>) -> U32:
  Maybe.default(&2, U32, Maybe.bind(&2, Bytes(), U32, m, U32.read), 0)

def flag.of(m: Maybe<&2, J.Json>) -> Bool:
  match m:
    case Some{v}:
      match v:
        case J.Flag{b}:
          b
        case _:
          False{}
    case None{}:
      False{}

# a probe read back from a log line, with its monitor's name
def probe.of(+j: J.Json) -> Bytes() & Probe:
  +t = Maybe.default(&2, Nat, Maybe.bind(&2, Bytes(), Nat, Json.get.str(j, "t"), Nat.read), 0n)
  (Maybe.default(&2, Bytes(), Json.get.str(j, "name"), ""),
   Probe{t, flag.of(Json.get(j, "up")), u32.of(Json.get.str(j, "ms")), u32.of(Json.get.str(j, "code")),
     Maybe.default(&2, Bytes(), Json.get.str(j, "err"), ""), u32.of(Json.get.str(j, "lag"))})

# The store
# ---------

def has(ms: List<&2, Mon>, +name: Bytes()) -> Bool:
  match ms:
    case Nil{}:
      False{}
    case Con{m, t}:
      String.eq(mon.name(m), name) || has(t, name)

# a spec added as a new monitor at the end: its id, or None when the
# name is taken
def add(st: Store, +s: Spec) -> Store & Maybe<&2, U32>:
  match st:
    case Store{+next, +ms}:
      Bool.pick(Store & Maybe<&2, U32>, has(ms, spec.name(s)), (Store{next, ms}, None{}),
        (Store{(next + 1 : U32), List.append(&2, Mon, ms, [Mon{next, s, 0, 0n, [], []}])}, Some{next}))

def without(ms: List<&2, Mon>, +name: Bytes()) -> List<&2, Mon>:
  match ms:
    case Nil{}:
      Nil{}
    case Con{+m, +t}:
      Bool.pick(List<&2, Mon>, String.eq(mon.name(m), name), t, Con{m, without(t, name)})

# the store without the named monitor, and whether it had one
def del(st: Store, +name: Bytes()) -> Store & Bool:
  match st:
    case Store{next, +ms}:
      (Store{next, without(ms, name)}, has(ms, name))

def find(ms: List<&2, Mon>, +name: Bytes()) -> Maybe<&2, Mon>:
  match ms:
    case Nil{}:
      None{}
    case Con{+m, +t}:
      Bool.pick(Maybe<&2, Mon>, String.eq(mon.name(m), name), Some{m}, find(t, name))

def store.mons(st: Store) -> List<&2, Mon>:
  match st:
    case Store{next, ms}:
      ms

# the named monitor's spec, while its id is still id (a monitor deleted,
# or deleted and added again, ends the old probe loop)
def spec.for(m: Maybe<&2, Mon>, +id: U32) -> Maybe<&2, Spec>:
  match m:
    case Some{+mm}:
      Bool.pick(Maybe<&2, Spec>, U32.is_eq(mon.id(mm), id), Some{mon.spec(mm)}, None{})
    case None{}:
      None{}

def hours.add(hs: List<&2, Bucket>, +hour: Nat, +up: Bool) -> List<&2, Bucket>:
  match hs:
    case Nil{}:
      [Bucket{hour, Bool.pick(U32, up, 1, 0), 1}]
    case Con{b, +t}:
      match b:
        case Bucket{+h, +bu, +ba}:
          +u = Bool.pick(U32, up, 1, 0)
          Bool.pick(List<&2, Bucket>, Nat.is_eq(h, hour), Con{Bucket{h, (bu + u : U32), (ba + 1 : U32)}, t},
            Con{Bucket{hour, u, 1}, List.take(&2, Bucket, Con{Bucket{h, bu, ba}, t}, 24n)})

# the history, newest first, cut back to cap() once it holds twice that
def hist.cut(room: Bool, +n: Nat, hist: List<&2, Probe>) -> Nat & List<&2, Probe>:
  match room:
    case True{}:
      (Nat.add(n, 1n), hist)
    case False{}:
      (cap(), List.take(&2, Probe, hist, cap()))

def hist.push(+n: Nat, p: Probe, hist: List<&2, Probe>) -> Nat & List<&2, Probe>:
  hist.cut(Nat.is_lt(n, Nat.mul(2n, cap())), n, Con{p, hist})

def mon.record.at(+id: U32, +spec: Spec, hours: List<&2, Bucket>, +p: Probe, nh: Nat & List<&2, Probe>) -> Mon:
  (n, hist) = nh
  Mon{id, spec, state.of(probe.up(p)), n, hist, hours.add(hours, Nat.div(probe.t(p), 3600000n), probe.up(p))}

def mon.record(m: Mon, +p: Probe) -> Mon:
  match m:
    case Mon{id, spec, state, n, hist, hours}:
      mon.record.at(id, spec, hours, p, hist.push(n, p, hist))

def record.on(m: Mon, r: List<&2, Mon> & U32) -> List<&2, Mon> & U32:
  (t, s) = r
  (Con{m, t}, s)

def record.hit(hit: Bool, +m: Mon, t: List<&2, Mon>, +p: Probe, rest: Unit -> List<&2, Mon> & U32) -> List<&2, Mon> & U32:
  match hit:
    case True{}:
      (Con{mon.record(m, p), t}, mon.state(m))
    case False{}:
      record.on(m, rest(Unit{}))

# the probe put on the named monitor: the list, and the state before it
# (9 when there is no such monitor)
def record.in(ms: List<&2, Mon>, +name: Bytes(), +p: Probe) -> List<&2, Mon> & U32:
  match ms:
    case Nil{}:
      (Nil{}, 9)
    case Con{+m, +t}:
      record.hit(String.eq(mon.name(m), name), m, t, p, u => record.in(t, name, p))

def record.put(+next: U32, r: List<&2, Mon> & U32) -> Store & U32:
  (t, s) = r
  (Store{next, t}, s)

def record(st: Store, +name: Bytes(), +p: Probe) -> Store & U32:
  match st:
    case Store{next, ms}:
      record.put(next, record.in(ms, name, p))

def mons.json(ms: List<&2, Mon>, +now: Nat) -> List<&2, J.Json>:
  match ms:
    case Nil{}:
      Nil{}
    case Con{m, t}:
      Con{mon.json(now, m), mons.json(t, now)}
