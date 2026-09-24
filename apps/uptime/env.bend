# What every handler and every probe loop shares: the store (a channel
# of one used as a lock), the WebSocket hub, the two append-only logs
# (each a channel of one holding its File), the webhook's URL and the
# dashboard's directory.
import Base
import ../../net/ws_server.bend as WsServer
import ./model.bend as M

type Env is Data:
  Env{db: Chan(M.Store), hub: WsServer.Hub, log: Chan(File), ops: Chan(File), hook: Bytes(), web: Bytes()}

def db(e: Env) -> Chan(M.Store):
  match e:
    case Env{db, hub, log, ops, hook, web}:
      db

def hub(e: Env) -> WsServer.Hub:
  match e:
    case Env{db, hub, log, ops, hook, web}:
      hub

def log(e: Env) -> Chan(File):
  match e:
    case Env{db, hub, log, ops, hook, web}:
      log

def ops(e: Env) -> Chan(File):
  match e:
    case Env{db, hub, log, ops, hook, web}:
      ops

def hook(e: Env) -> Bytes():
  match e:
    case Env{db, hub, log, ops, hook, web}:
      hook

def web(e: Env) -> Bytes():
  match e:
    case Env{db, hub, log, ops, hook, web}:
      web

# The lock
# --------
#
# locked(A, env, f, d): the store taken, changed by f, put back; f's
# answer (d when the channel is closed). Every read and write of the
# store goes through here, so two requests or probes never see half a
# change.

def locked.put(-A: Data, +db: Chan(M.Store), r: M.Store & A) -> IO(A):
  (st, a) = r
  IO.bind(Bool, A, Chan.send(M.Store, db, st), ok => IO.pure(A, a))

def locked.at(-A: Data, +db: Chan(M.Store), f: M.Store -> M.Store & A, d: A, m: Maybe<&1, M.Store>) -> IO(A):
  match m:
    case Some{st}:
      locked.put(A, db, f(st))
    case None{}:
      IO.pure(A, d)

def locked(-A: Data, +e: Env, f: M.Store -> M.Store & A, d: A) -> IO(A):
  IO.bind(Maybe<&1, M.Store>, A, Chan.recv(M.Store, db(e)), m => locked.at(A, db(e), f, d, m))

# a read of the store: what f makes of it
def peek(-A: Data, +e: Env, f: M.Store -> A, d: A) -> IO(A):
  locked(A, e, +st => (st, f(st)), d)

# The logs
# --------

def wrote.why(r: Result<&1, &1, U32 & String, Unit>) -> IO(Unit):
  match r:
    case Done{u}:
      IO.pure(Unit, Unit{})
    case Fail{(code, msg)}:
      IO.print_err("uptime: a log write failed: " ++ msg)

def wrote(+ch: Chan(File), g: File & Result<&1, &1, U32 & String, Unit>) -> IO(Unit):
  (f, r) = g
  do IO<Unit>:
    ok : Bool <- Chan.send(File, ch, f)
    wrote.why(r)

def append.at(+ch: Chan(File), line: Bytes(), m: Maybe<&1, File>) -> IO(Unit):
  match m:
    case Some{f}:
      IO.bind(File & Result<&1, &1, U32 & String, Unit>, Unit, File.write_buf(f, Bytes.append(line, "\n")),
        g => wrote(ch, g))
    case None{}:
      IO.pure(Unit, Unit{})

# a line appended to the log held by ch (one write, whole)
def append(+ch: Chan(File), line: Bytes()) -> IO(Unit):
  IO.bind(Maybe<&1, File>, Unit, Chan.recv(File, ch), m => append.at(ch, line, m))
