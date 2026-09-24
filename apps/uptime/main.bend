# bend-uptime: a small self-hosted uptime monitor, on net/.
#
#   bend apps/uptime/main.bend -o uptime
#   ./uptime --config monitors.json --state data/uptime --port 8080
#   open http://127.0.0.1:8080/
#
# Flags: --config (monitors.json), --state (a path prefix: <state>.results.ndjson
# and <state>.monitors.ndjson; its directory must exist), --web (the dashboard's
# directory, apps/uptime/web), --webhook (overrides the config's), and every
# Server.args flag (--port --host ...). The config:
#
#   {"webhook": "http://127.0.0.1:9000/hook",
#    "monitors": [{"name": "api", "url": "http://127.0.0.1:9001/health",
#                  "interval_ms": 30000, "timeout_ms": 5000, "expect": 200, "body": "ok"}]}
#
# At start the config's monitors are the store; the ops log's adds and
# deletes (from the API) are replayed over them, then the results log
# rebuilds each monitor's state, history and hourly counts. Each monitor
# is then probed by a loop of its own (probe.bend), and the API, the live
# feed and the dashboard are served (api.bend) until SIGTERM.
import Base
import ../../net/server.bend as Server
import ../../net/json.bend as Json
import ../../net/ws_server.bend as WsServer
import ../../power/json_value.bend as J
import ./model.bend as M
import ./env.bend as E
import ./files.bend as Files
import ./probe.bend as P
import ./api.bend as Api

# The config
# ----------

def cfg.add.at(+i: U32, st: M.Store & Maybe<&2, U32>, +name: Bytes(), errs: List<&2, Bytes()>) -> M.Store & List<&2, Bytes()>:
  (s, m) = st
  match m:
    case Some{id}:
      (s, errs)
    case None{}:
      (s, Con{"monitors[" ++ U32.show(i) ++ "]: the name " ++ name ++ " is taken", errs})

def prefixed(+i: U32, xs: List<&2, Bytes()>) -> List<&2, Bytes()>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{"monitors[" ++ U32.show(i) ++ "]: " ++ x, prefixed(i, t)}

def cfg.one(+i: U32, +c: M.Checked, +st: M.Store, +errs: List<&2, Bytes()>) -> M.Store & List<&2, Bytes()>:
  Bool.pick(M.Store & List<&2, Bytes()>, List.is_empty(&2, Bytes(), M.checked.errs(c)),
    cfg.add.at(i, M.add(st, M.checked.spec(c)), M.spec.name(M.checked.spec(c)), errs),
    (st, List.append(&2, Bytes(), errs, prefixed(i, M.checked.errs(c)))))

def cfg.monitors(xs: List<&2, J.Json>, +i: U32, r: M.Store & List<&2, Bytes()>) -> M.Store & List<&2, Bytes()>:
  match xs:
    case Nil{}:
      r
    case Con{x, t}:
      (st, errs) = r
      cfg.monitors(t, (i + 1 : U32), cfg.one(i, M.check(x), st, errs))

def cfg.list(m: Maybe<&2, J.Json>) -> M.Store & List<&2, Bytes()>:
  match m:
    case Some{v}:
      match v:
        case J.Arr{xs}:
          cfg.monitors(xs, 0, (M.store.new(), []))
        case _:
          (M.store.new(), ["monitors must be an array"])
    case None{}:
      (M.store.new(), [])

def cfg.done(r: M.Store & List<&2, Bytes()>) -> IO(M.Store):
  (st, errs) = r
  match errs:
    case Nil{}:
      IO.pure(M.Store, st)
    case Con{e, t}:
      IO.die(M.Store, 2, "uptime: the config is refused:\n  " ++ String.join(Con{e, t}, "\n  "))

def cfg.parsed(r: Result<&2, &2, J.Why, J.Json>) -> IO(J.Json):
  match r:
    case Done{j}:
      IO.pure(J.Json, j)
    case Fail{w}:
      IO.die(J.Json, 2, "uptime: the config is not JSON: " ++ Json.why.show(w))

def cfg.read(+path: Bytes(), m: Maybe<&2, Bytes()>) -> IO(J.Json):
  match m:
    case Some{+b}:
      cfg.parsed(Json.parse(b, U32.from_nat(Nat.add(Bytes.len(b), 16n))))
    case None{}:
      IO.die(J.Json, 2, "uptime: cannot read the config " ++ path)

# Start
# -----

def start.all(+e: E.Env, ms: List<&2, M.Mon>) -> IO(Unit):
  match ms:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{+m, t}:
      IO.bind(Unit, Unit, P.start(e, M.mon.spec(m), M.mon.id(m)), u => start.all(e, t))

def count(st: M.Store) -> Nat:
  List.length(&2, M.Mon, M.store.mons(st))

def main() -> IO(Unit):
  do IO<Unit>:
    a1 : List<String> <- IO.args()
    a2 : List<String> <- IO.args()
    a3 : List<String> <- IO.args()
    a4 : List<String> <- IO.args()
    a5 : List<String> <- IO.args()
    +cpath : Bytes() = Server.flag(a1, "--config", "monitors.json")
    +state : Bytes() = Server.flag(a2, "--state", "uptime")
    +web : Bytes() = Server.flag(a3, "--web", "apps/uptime/web")
    +hookf : Bytes() = Server.flag(a4, "--webhook", "")
    ctext : Maybe<&2, Bytes()> <- Files.slurp(cpath)
    +cj : J.Json <- cfg.read(cpath, ctext)
    st0 : M.Store <- cfg.done(cfg.list(Json.get(cj, "monitors")))
    st1 : M.Store <- Files.replay(1, state ++ ".monitors.ndjson", st0)
    +st2 : M.Store <- Files.replay(0, state ++ ".results.ndjson", st1)
    lf : File <- Files.appending(state ++ ".results.ndjson")
    of : File <- Files.appending(state ++ ".monitors.ndjson")
    +db : Chan(M.Store) <- Chan.new(M.Store, 1)
    ok1 : Bool <- Chan.send(M.Store, db, st2)
    +lc : Chan(File) <- Chan.new(File, 1)
    ok2 : Bool <- Chan.send(File, lc, lf)
    +oc : Chan(File) <- Chan.new(File, 1)
    ok3 : Bool <- Chan.send(File, oc, of)
    +hub : WsServer.Hub <- WsServer.hub.new()
    +hook : Bytes() = Bool.pick(Bytes(), String.is_empty(hookf), Maybe.default(&2, Bytes(), Json.get.str(cj, "webhook"), ""), hookf)
    +e : E.Env = E.Env{db, hub, lc, oc, hook, web}
    IO.print_err("uptime: " ++ Nat.show(count(st2)) ++ " monitors, state " ++ state ++ ", webhook " ++ hook)
    start.all(e, M.store.mons(st2))
    WsServer.serve.with(~E.Env, ~Api.routes, e, Server.args(a5, Server.config(8080)))
