# bend-wire: the real world.
#
# The loops of wire/loop.bend instantiated with IO and the effects
# themselves: a connection served over TCP.poll_buf and
# TCP.send_buf_poll (plain or TLS, whichever the listener carries), and
# an accept loop with a connection limit, SIGTERM and a grace time. A
# protocol hands in its hooks (wire/loop.bend's list) and a def that
# serves one connection, and gets the server.
#
# What the model in wire/world.bend assumes of each effect is its
# contract, stated there as a relation (rx.ok, tx.ok, lsn.ok, fopen.ok,
# fread.ok) and beside each effect in bend2/base.bend; wire/conform.bend
# drives the effects below through the contracts' cases and judges them
# by those very relations.
import Base
import ./loop.bend as L

# The adapters
# ============
#
# The three effects the loop wants beside the handle they were given,
# and the stop request as a flag beside the listener.
def net.now(s: Socket) -> IO(Socket & Nat):
  IO.bind(Nat, Socket & Nat, IO.now(), t => IO.pure(Socket & Nat, (s, t)))

def net.nap(s: Socket, ms: U32) -> IO(Socket):
  IO.bind(Unit, Socket, IO.sleep(ms), u => IO.pure(Socket, s))

def net.open(s: Socket, root: String, path: String) ->
  IO(Socket & Result<&1, &1, U32 & String, File>):
  IO.bind(Result<&1, &1, U32 & String, File>, Socket & Result<&1, &1, U32 & String, File>,
    File.open_under(root, path), r => IO.pure(Socket & Result<&1, &1, U32 & String, File>, (s, r)))

def net.sig(l: Listener) -> IO(Listener & Bool):
  IO.bind(Bool, Listener & Bool, IO.signal_pending(15), b => IO.pure(Listener & Bool, (l, b)))

# One connection
# ==============

# the connection loop with the real effects, from its first read to the
# socket it leaves to be closed
def serve(
  ~E: Data, ~P: Data, ~U: Data, ~idle: E -> U32, ~hdms: E -> U32,
  ~plan: E -> Bytes() -> P -> L.Plan<P, U>, ~mid: P -> Bool, ~big: Bytes(),
  ~uplan: U -> Bytes() -> L.Plan<P, U>, ~gap: U32, ~event: U32 -> Bytes(),
  ~shut: Bool -> Bytes() -> Bytes(), ~fhead: List<&2, U32> -> U32 -> Bytes(),
  ~miss: Bool -> Bytes(), ~lnote: Bytes() -> Bytes() -> String,
  ~lsize: Bytes() -> Bytes() -> U32 -> String, +srv: E, p0: P, s: Socket
) -> IO(Socket):
  L.conn.start(~(A => IO(A)), ~IO.pure, ~IO.bind, ~Socket, ~File, ~TCP.poll_buf,
    ~TCP.send_buf_poll, ~net.now, ~net.nap, ~IO.print_err, ~net.open, ~File.size, ~File.read_buf,
    ~File.close, ~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead,
    ~miss, ~lnote, ~lsize, srv, p0, s)

# The accept loop
# ===============
#
# ~go serves one connection and answers its socket (a protocol's
# instance of serve). A connection ends by closing its socket and giving
# its slot back: the semaphore is a channel with as much room as
# connections allowed, a slot is a Unit sent into it, and accepting
# parks on a full one.
def fin(+sem: Chan(Unit), s: Socket) -> IO(Unit):
  do IO<Unit>:
    Socket.close(s)
    got : Maybe<&1, Unit> <- Chan.recv(Unit, sem)
    return Unit{}

def start(~E: Data, ~go: @+srv: E -> Socket -> IO(Socket), +srv: E, +sem: Chan(Unit), s: Socket) ->
  IO(Unit):
  do IO<Unit>:
    s2 : Socket <- go(srv, s)
    fin(sem, s2)

# what serving needs: the protocol's own, and the slots
type Env<-E: Data> is Data:
  Env{srv: E, sem: Chan(Unit)}

def hand(~E: Data, ~go: @+srv: E -> Socket -> IO(Socket), +env: Env<E>, l: Listener, s: Socket) ->
  IO(Listener):
  match env:
    case Env{srv, sem}:
      do IO<Listener>:
        ok : Bool <- Chan.send(Unit, sem, Unit{})
        IO.spawn(Unit, start(~E, ~go, srv, sem, s))
        return l

# every slot taken back means every connection has ended
def drain(k: Nat, +sem: Chan(Unit)) -> IO(Unit):
  match k:
    case 0n:
      do IO<Unit>:
        return Unit{}
    case 1n+j:
      do IO<Unit>:
        ok : Bool <- Chan.send(Unit, sem, Unit{})
        drain(j, sem)

def grace(name: String, ms: U32) -> IO(Unit):
  do IO<Unit>:
    IO.sleep(ms)
    IO.die(Unit, 0, name ++ ": stopped with connections still open")

# Stopping, on SIGTERM: the listener closes so nothing more arrives, the
# connections open finish what they are doing, and the process ends when
# they have all ended or when the grace time is up, whichever is first.
def stopping(+name: String, ms: U32, conns: U32, +sem: Chan(Unit), l: Listener) -> IO(Unit):
  do IO<Unit>:
    IO.print_err(name ++ ": stopping")
    Listener.close(l)
    IO.spawn(Unit, grace(name, ms))
    drain(U32.to_nat(conns), sem)
    IO.die(Unit, 0, name ++ ": stopped")

# the turns one run of the loop takes before it is started again
def accept.fuel() -> Nat:
  U32.to_nat(1048576)

# The accept loop is the one place that runs until it is told to stop,
# so it is the one @unsafe def of a server, and all it does is start
# accept.run again when its turns are spent. It stops for a stop request
# and for a listener that is no longer one. ~name heads its log lines;
# ~grace and ~conns are the grace time and the connection limit.
@unsafe
def accept(
  ~E: Data, ~go: @+srv: E -> Socket -> IO(Socket), ~grace: E -> U32, ~conns: E -> U32,
  +name: String, +srv: E, +sem: Chan(Unit), lw: Listener & L.Why
) -> IO(Unit):
  (l, why) = lw
  match why:
    case L.Spent{}:
      do IO<Unit>:
        lw2 : Listener & L.Why <- L.accept.run(~(A => IO(A)), ~IO.pure, ~IO.bind, ~Listener,
            ~Socket, ~Env<E>, ~TCP.accept_poll, ~net.sig, ~hand(~E, ~go), accept.fuel(),
            Env{srv, sem}, (l, None{}))
        accept(~E, ~go, ~grace, ~conns, name, srv, sem, lw2)
    case L.Asked{}:
      stopping(name, grace(srv), conns(srv), sem, l)
    case L.Dead{code}:
      stopping(name, grace(srv), conns(srv), sem, l)

def early(stop: Bool) -> L.Why:
  match stop:
    case True{}:
      L.Asked{}
    case False{}:
      L.Spent{}

# A server on a listener: the slots, the stop request asked before the
# first accept, and the accept loop.
def run(
  ~E: Data, ~go: @+srv: E -> Socket -> IO(Socket), ~grace: E -> U32, ~conns: E -> U32,
  +name: String, +srv: E, l: Listener
) -> IO(Unit):
  do IO<Unit>:
    sem  : Chan(Unit) <- Chan.new(Unit, conns(srv))
    stop : Bool <- IO.signal_pending(15)
    accept(~E, ~go, ~grace, ~conns, name, srv, sem, (l, early(stop)))
