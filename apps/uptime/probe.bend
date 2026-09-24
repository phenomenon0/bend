# The probe loop: one computation per monitor, each on a pooled client
# session of its own (the session's options carry the monitor's timeout),
# and the webhook.
#
# Concurrency: IO.spawn starts a computation; the runtime's one event
# loop interleaves them all (and the server's connections), each waiting
# on its socket or its sleep. So the monitors are probed concurrently: a
# slow target holds only its own loop. Each loop keeps a schedule of
# slots (due, due + every, ...) on the monotonic clock, skips the slots
# a slow probe overran, sleeps in slices of 250 ms so SIGTERM ends it
# quickly, and ends when its monitor is deleted.
import Base
import ../../net/http.bend as Http
import ../../net/client.bend as Client
import ../../net/json.bend as Json
import ../../net/ws_frame.bend as F
import ../../net/ws_server.bend as WsServer
import ./model.bend as M
import ./env.bend as E

def fuel() -> Nat:
  U32.to_nat(4294967295)

# The webhook
# -----------

def hook.ok(r: Client.Res()) -> Bool:
  match r:
    case Done{resp}:
      +s = Http.status(resp)
      (s >= 200 : U32) && (s < 300 : U32)
    case Fail{e}:
      False{}

def hook.why(r: Client.Res()) -> Bytes():
  match r:
    case Done{resp}:
      "status " ++ U32.show(Http.status(resp))
    case Fail{e}:
      Client.error.show(e)

def hook.after(ok: Bool, +r: Client.Res(), +left: Nat, again: Unit -> IO(Unit)) -> IO(Unit):
  match ok:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      do IO<Unit>:
        IO.print_err("uptime: webhook failed (" ++ hook.why(r) ++ "), " ++ Nat.show(left) ++ " tries left")
        IO.sleep(1000)
        again(Unit{})

# POST body to url, tried `tries` times, a second apart, until a 2xx
def hook.send(tries: Nat, +url: Bytes(), +body: Bytes()) -> IO(Unit):
  match tries:
    case 0n:
      IO.print_err("uptime: webhook gave up")
    case 1n+(+k):
      do IO<Unit>:
        +r : Client.Res() <- Client.request(
          Client.req.body(Client.req.header(Client.req("POST", url), "content-type", "application/json"), body),
          Client.with.connect(Client.with.timeout(Client.opts(), 5000), 2000))
        hook.after(hook.ok(r), r, k, u => hook.send(k, url, body))

def hook.body(+s: M.Spec, +p: M.Probe) -> Bytes():
  Json.text(Json.obj([Json.kv("event", Json.str(Bool.pick(Bytes(), M.probe.up(p), "up", "down"))),
    Json.kv("name", Json.str(M.spec.name(s))), Json.kv("url", Json.str(M.spec.url(s))),
    Json.kv("probe", M.probe.json(p))]))

def alert.go(go: Bool, url: Bytes(), body: Bytes()) -> IO(Unit):
  match go:
    case True{}:
      IO.spawn(Unit, hook.send(3n, url, body))
    case False{}:
      IO.pure(Unit, Unit{})

# up to down or down to up: the webhook, in a computation of its own
def alert(+e: E.Env, +s: M.Spec, +p: M.Probe, +prev: U32) -> IO(Unit):
  +turned = (U32.is_eq(prev, 1) && Bool.not(M.probe.up(p))) || (U32.is_eq(prev, 2) && M.probe.up(p))
  +go = turned && Bool.not(String.is_empty(E.hook(e)))
  alert.go(go, E.hook(e), hook.body(s, p))

# One probe
# ---------

def judged.body(+needle: Bytes(), +body: Bytes()) -> Bool:
  String.is_empty(needle) || Maybe.is_some(&2, Nat, Bytes.find(body, needle))

def judged.at(+s: M.Spec, +t: Nat, +ms: U32, +lag: U32, +code: U32, +body_ok: Bool) -> M.Probe:
  +code_ok = U32.is_eq(code, M.spec.expect(s))
  +err = Bool.pick(Bytes(), code_ok,
    Bool.pick(Bytes(), body_ok, "", "body lacks \"" ++ M.spec.needle(s) ++ "\""),
    "status " ++ U32.show(code) ++ ", expected " ++ U32.show(M.spec.expect(s)))
  M.Probe{t, code_ok && body_ok, ms, code, err, lag}

# a response or an error, judged against the spec
def judged(+s: M.Spec, +t: Nat, +ms: U32, +lag: U32, r: Client.Res()) -> M.Probe:
  match r:
    case Done{+resp}:
      judged.at(s, t, ms, lag, Http.status(resp), judged.body(M.spec.needle(s), Http.resp.body(resp)))
    case Fail{e}:
      M.Probe{t, False{}, ms, 0, Client.error.show(e), lag}

def ms.between(+t0: Nat, +t1: Nat) -> U32:
  U32.from_nat(Nat.min(Nat.sub(t1, t0), 4294967295n))

# a probe told: logged, recorded (the state before it answered), sent
# to every dashboard, and a turn alerted
def told(+e: E.Env, +s: M.Spec, +p: M.Probe) -> IO(Unit):
  +line = M.probe.line(M.spec.name(s), p)
  do IO<Unit>:
    E.append(E.log(e), line)
    prev : U32 <- E.locked(U32, e, st => M.record(st, M.spec.name(s), p), 9)
    WsServer.publish(E.hub(e), F.Text{line})
    alert(e, s, p, prev)

# the next slot after t (a probe that overran its slot skips the ones
# it covered, so the schedule never drifts)
def next.due(+due: Nat, +every: Nat, +t: Nat) -> Nat:
  Nat.add(due, Nat.mul(every, Nat.add(1n, Nat.div(Nat.sub(t, due), every))))

# sleep until the monotonic time `until`, in slices of at most 250 ms,
# stopping early on SIGTERM
def wait.slice(more: Bool, ms: U32, again: Unit -> IO(Unit)) -> IO(Unit):
  match more:
    case True{}:
      IO.bind(Unit, Unit, IO.sleep(ms), again)
    case False{}:
      IO.pure(Unit, Unit{})

def wait.at(+until: Nat, +now: Nat, stop: Bool, again: Unit -> IO(Unit)) -> IO(Unit):
  match stop:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      wait.slice(Nat.is_lt(now, until), U32.from_nat(Nat.min(Nat.sub(until, now), 250n)), again)

def wait(fuel: Nat, +until: Nat) -> IO(Unit):
  match fuel:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+k:
      do IO<Unit>:
        now : Nat <- IO.now()
        stop : Bool <- IO.signal_seen(15)
        wait.at(until, now, stop, u => wait(k, until))

# one probe of s at the slot due, then the wait for the next slot
def probe.run(+e: E.Env, +ss: Client.Session, +s: M.Spec, +due: Nat, again: Nat -> IO(Unit)) -> IO(Unit):
  do IO<Unit>:
    +t0 : Nat <- IO.now()
    +w : Nat <- IO.wall()
    r : Client.Res() <- Client.fetch(ss, Client.req("GET", M.spec.url(s)))
    +t1 : Nat <- IO.now()
    told(e, s, judged(s, w, ms.between(t0, t1), ms.between(due, t0), r))
    +next : Nat = next.due(due, U32.to_nat(M.spec.every(s)), t1)
    wait(fuel(), next)
    again(next)

def probe.step(+e: E.Env, +ss: Client.Session, +due: Nat, stop: Bool, m: Maybe<&2, M.Spec>, again: Nat -> IO(Unit)) -> IO(Unit):
  match stop m:
    case False{} Some{s}:
      probe.run(e, ss, s, due, again)
    case _ _:
      Client.close(ss)

def probe.loop(fuel: Nat, +e: E.Env, +ss: Client.Session, +name: Bytes(), +id: U32, +due: Nat) -> IO(Unit):
  match fuel:
    case 0n:
      Client.close(ss)
    case 1n+k:
      do IO<Unit>:
        stop : Bool <- IO.signal_seen(15)
        m : Maybe<&2, M.Spec> <- E.peek(Maybe<&2, M.Spec>, e, st => M.spec.for(M.find(M.store.mons(st), name), id), None{})
        probe.step(e, ss, due, stop, m, nx => probe.loop(k, e, ss, name, id, nx))

# the loop of one monitor, on a session whose timeouts are its own
def start(+e: E.Env, +s: M.Spec, +id: U32) -> IO(Unit):
  +o = Client.with.redirects(Client.with.connect(Client.with.timeout(Client.opts(), M.spec.timeout(s)), M.spec.timeout(s)), 0)
  do IO<Unit>:
    +ss : Client.Session <- Client.session(o)
    +now : Nat <- IO.now()
    IO.spawn(Unit, probe.loop(fuel(), e, ss, M.spec.name(s), id, now))
