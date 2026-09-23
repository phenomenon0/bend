# The world the engine runs in, as a pure model, and the contracts that
# tie the model to the effects.
#
# main.bend writes the connection loop (conn, turn, send.segs and all
# under them) and the accept loop (accept.run) once, over an effect
# interface: a monad and one template parameter per effect. main.bend's
# start and accept instantiate them with IO and the real effects. This
# file instantiates the same defs with the identity monad and a scripted
# world, so LAWS.bend can state, and PROOF.bend prove, what the loops do
# to every peer the script can describe.
#
# The model is only as good as the contracts: what it assumes of each
# effect is written below as a relation on what the effect answers
# (rx.ok, tx.ok, lsn.ok, fopen.ok, fread.ok), the model is proved to
# keep them (LAWS.bend), and conform.bend drives each real effect
# through the same cases and checks the same relations against what it
# observes. That is the bridge; what is left trusted is that the
# effects keep their contract in the cases conform.bend does not try.
import Base
import ./main.bend as Eng
import ./ws.bend as Ws

# The identity monad
# ==================

def Id(A: Type) -> Type:
  A

def Id.pure(-A: Type, x: A) -> Id(A):
  x

def Id.bind(-A: Type, -B: Type, m: Id(A), f: A -> Id(B)) -> Id(B):
  f(m)

# The scripted peer
# =================
#
# What the peer does for each read, in order: its bytes arrive wait ms
# after the read began (the empty Bytes is its FIN), it says nothing, or
# the read fails. Past the script's end the peer is silent.
type Rd is Data:
  Give{wait: Nat, bs: Bytes()}
  Hush{}
  Cut{code: U32}

# What the peer does while a send is under way, in order: after wait ms
# without progress it takes 1+more bytes, or it resets. Past the
# script's end an eager peer takes everything at once and any other
# stops reading for good.
type Wr is Data:
  Take{wait: Nat, more: Nat}
  Reset{code: U32}

type Fil is Data:
  Fil{name: String, body: Bytes()}

# The socket's world: the two scripts, whether the peer reads eagerly
# past its script, the clock (ms), the files under the root, and every
# byte the peer has taken so far.
type World is Data:
  World{rd: List<&2, Rd>, wr: List<&2, Wr>, eager: Bool, now: Nat, fs: List<&2, Fil>,
    out: Bytes()}

def w.now(w: World) -> Nat:
  match w:
    case World{rd, wr, eager, now, fs, out}:
      now

def w.out(w: World) -> Bytes():
  match w:
    case World{rd, wr, eager, now, fs, out}:
      out

def w.rd(w: World) -> List<&2, Rd>:
  match w:
    case World{rd, wr, eager, now, fs, out}:
      rd

# The model's effects
# ===================

# TCP.poll_buf: the next scripted read, if it arrives within ms; the
# clock moves by what the read waited
def w.rx.give(
  t: List<&2, Rd>, +wait: Nat, bs: Bytes(), +ms: U32, wr: List<&2, Wr>, eager: Bool,
  now: Nat, fs: List<&2, Fil>, out: Bytes(), soon: Bool
) -> Eng.Got(World):
  match soon:
    case True{}:
      (World{t, wr, eager, Nat.add(now, wait), fs, out}, Done{Some{bs}})
    case False{}:
      (World{Con{Give{Nat.sub(wait, U32.to_nat(ms)), bs}, t}, wr, eager,
        Nat.add(now, U32.to_nat(ms)), fs, out}, Done{None{}})

def w.rx.go(s: World, +ms: U32) -> Eng.Got(World):
  match s:
    case World{rd, wr, eager, now, fs, out}:
      match rd:
        case Nil{}:
          (World{Nil{}, wr, eager, Nat.add(now, U32.to_nat(ms)), fs, out}, Done{None{}})
        case Con{e, t}:
          match e:
            case Hush{}:
              (World{t, wr, eager, Nat.add(now, U32.to_nat(ms)), fs, out}, Done{None{}})
            case Cut{code}:
              (World{t, wr, eager, now, fs, out}, Fail{(code, "reset")})
            case Give{+wait, bs}:
              w.rx.give(t, wait, bs, ms, wr, eager, now, fs, out,
                Nat.is_lt(wait, U32.to_nat(ms)))

def w.rx(s: World, max: U32, ms: U32) -> Eng.Got(World):
  w.rx.go(s, ms)

# TCP.send_buf_poll: the peer takes the buffer as its script says; a
# wait of ms or more without progress fails the send with ETIMEDOUT
def w.tx.on(
  +wr: List<&2, Wr>, +bs: Bytes(), +ms: U32, +rd: List<&2, Rd>, +eager: Bool, +now: Nat,
  +fs: List<&2, Fil>, +out: Bytes()
) -> Eng.Put(World):
  match wr:
    case Nil{}:
      match bs:
        case SNil{}:
          (World{rd, Nil{}, eager, now, fs, out}, Done{Unit{}})
        case SCon{h, r}:
          Bool.pick(Eng.Put(World), eager,
            (World{rd, Nil{}, True{}, now, fs, Bytes.append(out, SCon{h, r})}, Done{Unit{}}),
            (World{rd, Nil{}, False{}, Nat.add(now, U32.to_nat(ms)), fs, out},
              Fail{(110, "timed out")}))
    case Con{e, t}:
      match e:
        case Reset{code}:
          match bs:
            case SNil{}:
              (World{rd, Con{Reset{code}, t}, eager, now, fs, out}, Done{Unit{}})
            case SCon{h, r}:
              (World{rd, t, eager, now, fs, out}, Fail{(code, "reset")})
        case Take{+wait, +more}:
          match bs:
            case SNil{}:
              (World{rd, Con{Take{wait, more}, t}, eager, now, fs, out}, Done{Unit{}})
            case SCon{h, r}:
              Bool.pick(Eng.Put(World), Nat.is_lt(wait, U32.to_nat(ms)),
                w.tx.on(t, String.drop(SCon{h, r}, 1n+more), ms, rd, eager, Nat.add(now, wait),
                  fs, Bytes.append(out, String.take(SCon{h, r}, 1n+more))),
                (World{rd, Con{Take{Nat.sub(wait, U32.to_nat(ms)), more}, t}, eager,
                  Nat.add(now, U32.to_nat(ms)), fs, out}, Fail{(110, "timed out")}))

def w.tx.go(s: World, bs: Bytes(), +ms: U32) -> Eng.Put(World):
  match s:
    case World{rd, wr, eager, now, fs, out}:
      w.tx.on(wr, bs, ms, rd, eager, now, fs, out)

def w.tx(s: World, bs: Bytes(), ms: U32) -> Eng.Put(World):
  w.tx.go(s, bs, ms)

def w.clk.go(+s: World) -> World & Nat:
  (s, w.now(s))

def w.clk(s: World) -> World & Nat:
  w.clk.go(s)

def w.nap(s: World, ms: U32) -> World:
  match s:
    case World{rd, wr, eager, now, fs, out}:
      World{rd, wr, eager, Nat.add(now, U32.to_nat(ms)), fs, out}

def w.say(text: String) -> Unit:
  Unit{}

# File.open_under: a file of that name, whatever the root; a model file
# is the bytes it has left
def w.find(+fs: List<&2, Fil>, +path: String) -> Result<&1, &1, U32 & String, Bytes()>:
  match fs:
    case Nil{}:
      Fail{(2, "no such file")}
    case Con{f, t}:
      match f:
        case Fil{name, body}:
          Bool.pick(Result<&1, &1, U32 & String, Bytes()>, String.eq(name, path), Done{body},
            w.find(t, path))

def w.fopen.go(+s: World, path: String) -> World & Result<&1, &1, U32 & String, Bytes()>:
  match s:
    case World{rd, wr, eager, now, fs, out}:
      (World{rd, wr, eager, now, fs, out}, w.find(fs, path))

def w.fopen(s: World, root: String, path: String) ->
  World & Result<&1, &1, U32 & String, Bytes()>:
  w.fopen.go(s, path)

def w.fsize.go(+f: Bytes()) -> Bytes() & Result<&1, &1, U32 & String, U32>:
  (f, Done{U32.from_nat(Bytes.len(f))})

def w.fsize(f: Bytes()) -> Bytes() & Result<&1, &1, U32 & String, U32>:
  w.fsize.go(f)

def w.fread.go(+f: Bytes(), +n: Nat) -> Bytes() & Result<&1, &1, U32 & String, Bytes()>:
  (String.drop(f, n), Done{String.take(f, n)})

def w.fread(f: Bytes(), max: U32) -> Bytes() & Result<&1, &1, U32 & String, Bytes()>:
  w.fread.go(f, U32.to_nat(max))

def w.fclose(f: Bytes()) -> Unit:
  Unit{}

# The loop in the model
# =====================
#
# The same defs the server runs, with the identity monad and the model's
# effects: each is a pure function from a world to a world.

def sim.note(may: Maybe<&2, Bytes()>, +out: Bytes()) -> Bytes():
  Eng.flat.note(~Id, ~Id.pure, ~Id.bind, ~w.say, may, out)

def sim.hold(+ms: U32, s: World, +acc: Bytes()) -> Eng.Em<World>:
  Eng.send.hold(~Id, ~Id.pure, ~Id.bind, ~World, ~w.tx, ms, s, acc)

def sim.raw(+ms: U32, may: Maybe<&2, Bytes()>, bs: Bytes(), st: Eng.Em<World>) -> Eng.Em<World>:
  Eng.send.raw(~Id, ~Id.pure, ~Id.bind, ~World, ~w.tx, ~w.say, ms, may, bs, st)

def sim.page(
  +ms: U32, root: List<&2, U32>, path: List<&2, U32>, ct: List<&2, U32>, head: Bool,
  may: Maybe<&2, Bytes()>, sh: Bool, st: Eng.Em<World>
) -> Eng.Em<World>:
  Eng.send.page(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~w.tx, ~w.say, ~w.fopen, ~w.fsize,
    ~w.fread, ~w.fclose, ms, root, path, ct, head, may, sh, st)

def sim.go(
  xs: List<&2, Eng.Seg>, +ms: U32, may: Maybe<&2, Bytes()>, sh: Bool, st: Eng.Em<World>
) -> Eng.Put(World):
  Eng.send.go(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~w.tx, ~w.say, ~w.fopen, ~w.fsize,
    ~w.fread, ~w.fclose, xs, ms, may, sh, st)

def sim.segs(s: World, xs: List<&2, Eng.Seg>, +ms: U32) -> Eng.Put(World):
  Eng.send.segs(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~w.tx, ~w.say, ~w.fopen, ~w.fsize,
    ~w.fread, ~w.fclose, s, xs, ms)

def sim.turn.h(+srv: Eng.Srv, s: World, p: Eng.P, hw: Eng.Hw) -> (World & Eng.Plan) & Eng.Hw:
  Eng.turn.h(~Id, ~Id.pure, ~Id.bind, ~World, ~w.rx, ~w.clk, srv, s, p, hw)

def sim.left(
  +srv: Eng.Srv, s: World, p: Eng.P, t0: Nat, n: U32, +el: Nat, ok: Bool
) -> (World & Eng.Plan) & Eng.Hw:
  Eng.turn.left(~Id, ~Id.pure, ~Id.bind, ~World, ~w.rx, srv, s, p, t0, n, el, ok)

def sim.held(+ms: U32, s: World, acc: Bytes(), c: Cmp) -> Eng.Em<World>:
  Eng.send.held(~Id, ~Id.pure, ~Id.bind, ~World, ~w.tx, ms, s, acc, c)

def sim.flushed(m: Eng.Put(World)) -> Eng.Em<World>:
  Eng.send.flushed(~Id, ~Id.pure, ~Id.bind, ~World, m)

def sim.pleft(+ms: U32, f: Bytes(), left: U32, s: World, pre: Bytes(), done: Bool) ->
  Eng.Pump<World, Bytes()>:
  Eng.pump.left(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~w.tx, ~w.fclose, ms, f, left, s, pre,
    done)

def sim.psent(+ms: U32, m: Eng.Put(World), f: Bytes(), +left: U32) -> Eng.Pump<World, Bytes()>:
  Eng.pump.sent(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~w.tx, ~w.fclose, ms, m, f, left)

def sim.pblock(
  +ms: U32, f: Bytes(), +left: U32, s: World, pre: Bytes(), bs: Bytes(), +n: U32, empty: Bool
) -> Eng.Pump<World, Bytes()>:
  Eng.pump.block(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~w.tx, ~w.fclose, ms, f, left, s,
    pre, bs, n, empty)

def sim.pgot(
  +ms: U32, got: Bytes() & Result<&1, &1, U32 & String, Bytes()>, left: U32, s: World,
  pre: Bytes()
) -> Eng.Pump<World, Bytes()>:
  Eng.pump.got(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~w.tx, ~w.fclose, ms, got, left, s, pre)

def sim.pump(k: Nat, +ms: U32, p: Eng.Pump<World, Bytes()>) -> Eng.Em<World>:
  Eng.pump(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~w.tx, ~w.fread, ~w.fclose, k, ms, p)

def sim.miss(
  +ms: U32, head: Bool, may: Maybe<&2, Bytes()>, sh: Bool, s: World, acc: Bytes()
) -> Eng.Em<World>:
  Eng.page.miss(~Id, ~Id.pure, ~Id.bind, ~World, ~w.tx, ~w.say, ms, head, may, sh, s, acc)

def sim.pstart(
  +ms: U32, f: Bytes(), +n: U32, +hd: Bytes(), head: Bool, may: Maybe<&2, Bytes()>,
  s: World, acc: Bytes()
) -> Eng.Em<World>:
  Eng.page.start(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~w.tx, ~w.say, ~w.fread, ~w.fclose,
    ms, f, n, hd, head, may, s, acc)

def sim.psized(
  +ms: U32, got: Bytes() & Result<&1, &1, U32 & String, U32>, ct: List<&2, U32>, head: Bool,
  may: Maybe<&2, Bytes()>, sh: Bool, s: World, acc: Bytes()
) -> Eng.Em<World>:
  Eng.page.sized(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~w.tx, ~w.say, ~w.fread, ~w.fclose,
    ms, got, ct, head, may, sh, s, acc)

def sim.opened(
  +ms: U32, m: World & Result<&1, &1, U32 & String, Bytes()>, ct: List<&2, U32>, head: Bool,
  may: Maybe<&2, Bytes()>, sh: Bool, acc: Bytes()
) -> Eng.Em<World>:
  Eng.page.opened(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~w.tx, ~w.say, ~w.fsize, ~w.fread,
    ~w.fclose, ms, m, ct, head, may, sh, acc)

def sim.turn(+srv: Eng.Srv, m: Eng.Put(World), p: Eng.P, hw: Eng.Hw) ->
  (World & Eng.Plan) & Eng.Hw:
  Eng.turn(~Id, ~Id.pure, ~Id.bind, ~World, ~w.rx, ~w.clk, srv, m, p, hw)

def sim.turn.ws(+srv: Eng.Srv, m: Eng.Put(World), wr: Ws.W) -> World & Eng.Plan:
  Eng.turn.ws(~Id, ~Id.pure, ~Id.bind, ~World, ~w.rx, srv, m, wr)

def sim.tick(m: Eng.Put(World), n: U32) -> World & Eng.Plan:
  Eng.tick(~Id, ~Id.pure, ~Id.bind, ~World, ~w.nap, m, n)

def sim.conn(f: Nat, +srv: Eng.Srv, sph: (World & Eng.Plan) & Eng.Hw, w: Nat) -> World:
  Eng.conn(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~w.rx, ~w.tx, ~w.clk, ~w.nap, ~w.say,
    ~w.fopen, ~w.fsize, ~w.fread, ~w.fclose, f, srv, sph, w)

def sim.start(+srv: Eng.Srv, s: World) -> World:
  Eng.conn.start(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~w.rx, ~w.tx, ~w.clk, ~w.nap,
    ~w.say, ~w.fopen, ~w.fsize, ~w.fread, ~w.fclose, srv, s)

# The mute peer
# =============
#
# A peer that has stopped: every read waits out its time and answers
# nothing, every send that has bytes to move waits out its time and
# fails, and an empty send, which moves nothing, succeeds. It is the
# scripted peer with both scripts spent, not eager, with the clock left
# out: what it answers does not depend on the world, which is what lets
# a law quantify over every state the loop can be in when it stops.

def m.rx(s: World, max: U32, ms: U32) -> Eng.Got(World):
  (s, Done{None{}})

def m.tx(s: World, bs: Bytes(), ms: U32) -> Eng.Put(World):
  match bs:
    case SNil{}:
      (s, Done{Unit{}})
    case SCon{h, t}:
      (s, Fail{(110, "timed out")})

def m.nap(s: World, ms: U32) -> World:
  s

def mute.conn(f: Nat, +srv: Eng.Srv, sph: (World & Eng.Plan) & Eng.Hw, w: Nat) -> World:
  Eng.conn(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~m.rx, ~m.tx, ~w.clk, ~m.nap, ~w.say,
    ~w.fopen, ~w.fsize, ~w.fread, ~w.fclose, f, srv, sph, w)

def mute.turn(+srv: Eng.Srv, m: Eng.Put(World), p: Eng.P, hw: Eng.Hw) ->
  (World & Eng.Plan) & Eng.Hw:
  Eng.turn(~Id, ~Id.pure, ~Id.bind, ~World, ~m.rx, ~w.clk, srv, m, p, hw)

def mute.segs(s: World, xs: List<&2, Eng.Seg>, +ms: U32) -> Eng.Put(World):
  Eng.send.segs(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~m.tx, ~w.say, ~w.fopen, ~w.fsize,
    ~w.fread, ~w.fclose, s, xs, ms)

def mute.turn.h(+srv: Eng.Srv, s: World, p: Eng.P, hw: Eng.Hw) -> (World & Eng.Plan) & Eng.Hw:
  Eng.turn.h(~Id, ~Id.pure, ~Id.bind, ~World, ~m.rx, ~w.clk, srv, s, p, hw)

def mute.left(
  +srv: Eng.Srv, s: World, p: Eng.P, t0: Nat, n: U32, +el: Nat, ok: Bool
) -> (World & Eng.Plan) & Eng.Hw:
  Eng.turn.left(~Id, ~Id.pure, ~Id.bind, ~World, ~m.rx, srv, s, p, t0, n, el, ok)

def mute.turn.ws(+srv: Eng.Srv, m: Eng.Put(World), wr: Ws.W) -> World & Eng.Plan:
  Eng.turn.ws(~Id, ~Id.pure, ~Id.bind, ~World, ~m.rx, srv, m, wr)

def mute.tick(m: Eng.Put(World), n: U32) -> World & Eng.Plan:
  Eng.tick(~Id, ~Id.pure, ~Id.bind, ~World, ~m.nap, m, n)

def mute.held(+ms: U32, s: World, acc: Bytes(), c: Cmp) -> Eng.Em<World>:
  Eng.send.held(~Id, ~Id.pure, ~Id.bind, ~World, ~m.tx, ms, s, acc, c)

def mute.go(
  xs: List<&2, Eng.Seg>, +ms: U32, may: Maybe<&2, Bytes()>, sh: Bool, st: Eng.Em<World>
) -> Eng.Put(World):
  Eng.send.go(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~m.tx, ~w.say, ~w.fopen, ~w.fsize,
    ~w.fread, ~w.fclose, xs, ms, may, sh, st)

def empty(bs: Bytes()) -> Bool:
  match bs:
    case SNil{}:
      True{}
    case SCon{h, t}:
      False{}

# The listener's world
# ====================
#
# What each timed accept meets, in order: a connection, nothing before
# the tick, a failure with this code, or a stop request (SIGTERM) and
# nothing else. Past the script's end nothing arrives. stop is whether a
# stop was asked; served counts the connections handed off.
type Ac is Data:
  Come{}
  Idle{}
  Err{code: U32}
  Term{}

type Lw is Data:
  Lw{evs: List<&2, Ac>, stop: Bool, served: Nat}

def l.lsn(l: Lw, ms: U32) -> Lw & Result<&1, &1, U32 & String, Maybe<&1, Unit>>:
  match l:
    case Lw{evs, stop, served}:
      match evs:
        case Nil{}:
          (Lw{Nil{}, stop, served}, Done{None{}})
        case Con{e, t}:
          match e:
            case Come{}:
              (Lw{t, stop, served}, Done{Some{Unit{}}})
            case Idle{}:
              (Lw{t, stop, served}, Done{None{}})
            case Err{code}:
              (Lw{t, stop, served}, Fail{(code, "accept")})
            case Term{}:
              (Lw{t, True{}, served}, Done{None{}})

def l.sig(l: Lw) -> Lw & Bool:
  match l:
    case Lw{evs, +stop, served}:
      (Lw{evs, stop, served}, stop)

def l.hand(+env: Unit, l: Lw, c: Unit) -> Lw:
  match l:
    case Lw{evs, stop, served}:
      Lw{evs, stop, 1n+served}

def sim.acc.run(k: Nat, lw: Lw & Maybe<&2, Eng.Why>) -> Lw & Eng.Why:
  Eng.accept.run(~Id, ~Id.pure, ~Id.bind, ~Lw, ~Unit, ~Unit, ~l.lsn, ~l.sig, ~l.hand, k,
    Unit{}, lw)

def sim.acc.dead(k: Nat, l: Lw, +code: U32, soft: Bool) -> Lw & Eng.Why:
  sim.acc.run(k, Eng.accept.dead(~Id, ~Id.pure, ~Id.bind, ~Lw, ~l.sig, l, code, soft))

def sim.accept(k: Nat, l: Lw) -> Lw & Eng.Why:
  Eng.accept.run(~Id, ~Id.pure, ~Id.bind, ~Lw, ~Unit, ~Unit, ~l.lsn, ~l.sig, ~l.hand, k,
    Unit{}, (l, None{}))

# The contracts
# =============
#
# What the model assumes of each effect, as a relation on what one call
# answered. The same text stands beside each effect in bend2/base.bend;
# conform.bend checks the real effects against these very defs.

# TCP.poll_buf(s, max, ms), called at t and answering after took ms:
# nothing (None) only once ms have passed; bytes (Some) within ms and
# at most max of them, the empty Bytes meaning the peer's FIN; a failure
# at any time, after which the socket is not read again.
def rx.ok(
  max: U32, +ms: U32, +took: Nat, r: Result<&1, &1, U32 & String, Maybe<&1, Bytes()>>
) -> Bool:
  match r:
    case Fail{e}:
      True{}
    case Done{may}:
      match may:
        case None{}:
          Nat.is_le(U32.to_nat(ms), took)
        case Some{+bs}:
          U32.is_le(U32.from_nat(Bytes.len(bs)), max) && Nat.is_le(took, U32.to_nat(ms))

# TCP.send_buf_poll(s, bytes, ms): Done once every byte has gone to the
# peer however long that takes, as long as it never waits ms without
# progress; a peer that leaves it waiting ms without progress fails it
# with ETIMEDOUT (110 on Linux, 60 on macOS) after at least ms. stalled
# is whether the peer did; took is how long the send took.
def etimedout(+code: U32) -> Bool:
  U32.is_eq(code, 110) || U32.is_eq(code, 60)

def tx.timed(e: U32 & String, +took: Nat, +ms: U32) -> Bool:
  (code, msg) = e
  etimedout(code) && Nat.is_le(U32.to_nat(ms), took)

def tx.ok(+ms: U32, stalled: Bool, +took: Nat, r: Result<&1, &1, U32 & String, Unit>) -> Bool:
  match stalled:
    case False{}:
      Result.is_done(&1, &1, U32 & String, Unit, r)
    case True{}:
      match r:
        case Done{u}:
          False{}
        case Fail{e}:
          tx.timed(e, took, ms)

# TCP.accept_poll(l, ms): a connection, nothing (once ms have passed, or
# after it shed one arrival it had no descriptor for), or a failure --
# and a failure only for a listener that is no longer one: never with a
# code of the passing set (Eng.accept.soft).
def lsn.dead(e: U32 & String) -> Bool:
  (code, msg) = e
  Bool.not(Eng.accept.soft(code))

def lsn.ok(r: Result<&1, &1, U32 & String, Maybe<&1, Unit>>) -> Bool:
  match r:
    case Done{may}:
      True{}
    case Fail{e}:
      lsn.dead(e)

# What a name under the root is, for File.open_under: a regular file, a
# name no file has, a symbolic link (to anything), a directory, or a
# name that climbs out of the root.
type Name is Data:
  Plain{}
  Absent{}
  Linked{}
  Dir{}
  Climbs{}

# File.open_under(root, path): Done for a regular file and nothing else
def fopen.ok(k: Name, r: Result<&1, &1, U32 & String, Unit>) -> Bool:
  match k:
    case Plain{}:
      Result.is_done(&1, &1, U32 & String, Unit, r)
    case Absent{}:
      Result.is_fail(&1, &1, U32 & String, Unit, r)
    case Linked{}:
      Result.is_fail(&1, &1, U32 & String, Unit, r)
    case Dir{}:
      Result.is_fail(&1, &1, U32 & String, Unit, r)
    case Climbs{}:
      Result.is_fail(&1, &1, U32 & String, Unit, r)

# File.read_buf(f, max) with left bytes left in the file: at most max
# bytes and at most what is left, and none only at the end
def fread.ok(max: U32, +left: Nat, r: Result<&1, &1, U32 & String, Bytes()>) -> Bool:
  match r:
    case Fail{e}:
      True{}
    case Done{+bs}:
      U32.is_le(U32.from_nat(Bytes.len(bs)), max) && Nat.is_le(Bytes.len(bs), left)
        && Bool.not(Nat.is_eq(Bytes.len(bs), 0n) && Bool.not(Nat.is_eq(left, 0n)))

# What the laws speak of
# ======================

# a writer that may still take replies holds a batch below the cap; one
# that may not (a send failed, a file came up short) holds what it will
# write last
def em.fine(em: Eng.Em<World>) -> Bool:
  match em:
    case Eng.Em{s, acc, ok}:
      match ok:
        case True{}:
          U32.is_lt(U32.from_nat(Bytes.len(acc)), Eng.send.cap())
        case False{}:
          True{}

def pump.fine(p: Eng.Pump<World, Bytes()>) -> Bool:
  match p:
    case Eng.Going{f, left, s, pre}:
      True{}
    case Eng.Over{em}:
      em.fine(em)

# a head in progress has had at most head.cap() bytes since the read it
# began in
def hw.fine(hw: Eng.Hw) -> Bool:
  match hw:
    case Eng.NoHead{}:
      True{}
    case Eng.Begun{}:
      True{}
    case Eng.Since{t0, n}:
      Bool.not(U32.is_lt(Eng.head.cap(), n))

def hw.of(q: (World & Eng.Plan) & Eng.Hw) -> Eng.Hw:
  (sp, hw) = q
  hw

def put.done(m: Eng.Put(World)) -> Bool:
  (s, r) = m
  Result.is_done(&1, &1, U32 & String, Unit, r)

def why.of(r: Lw & Eng.Why) -> Eng.Why:
  (l, why) = r
  why

# a listener script with no stop request, whose every failure has a
# code of the passing set
def calm(evs: List<&2, Ac>) -> Bool:
  match evs:
    case Nil{}:
      True{}
    case Con{e, t}:
      match e:
        case Come{}:
          calm(t)
        case Idle{}:
          calm(t)
        case Err{+code}:
          Eng.accept.soft(code) && calm(t)
        case Term{}:
          False{}

# the loop ended as it may: its turns spent, a stop asked, or a code
# outside the passing set
def ok.end(why: Eng.Why) -> Bool:
  match why:
    case Eng.Spent{}:
      True{}
    case Eng.Asked{}:
      True{}
    case Eng.Dead{+code}:
      Bool.not(Eng.accept.soft(code))

# The replies a read's requests are owed, in their order, then tail;
# and whether a request's reply leaves the connection reading requests
# (it neither closes, nor streams, nor switches to frames), computed as
# answer.go computes it.
def ag.c(+srv: Eng.Srv, +r: Eng.Req) -> Bool:
  Eng.ans.close(Eng.serve(srv, r)) || Eng.req.close(r)
    || (Eng.req.ws(r) && Bool.not(Eng.ans.sock(Eng.serve(srv, r))))

def ag.k(+srv: Eng.Srv, +r: Eng.Req) -> Bool:
  Eng.ans.sock(Eng.serve(srv, r))

def ag.s(+srv: Eng.Srv, +r: Eng.Req) -> U32:
  Eng.ans.stream(Eng.serve(srv, r))

def ag.o(+srv: Eng.Srv, +r: Eng.Req) -> List<&2, Eng.Seg>:
  Eng.ans.out(Eng.serve(srv, r))

def keeps(+srv: Eng.Srv, +r: Eng.Req) -> Bool:
  Bool.not(ag.c(srv, r) || ag.k(srv, r) || Bool.not(U32.is_zero(ag.s(srv, r))))

def all.keep(+srv: Eng.Srv, rs: List<&2, Eng.Req>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{+r, t}:
      keeps(srv, r) && all.keep(srv, t)

def owed(+srv: Eng.Srv, rs: List<&2, Eng.Req>, tail: List<&2, Eng.Seg>) -> List<&2, Eng.Seg>:
  match rs:
    case Nil{}:
      tail
    case Con{+r, t}:
      List.append(&2, Eng.Seg, ag.o(srv, r), owed(srv, t, tail))

# The bytes a list of segments puts on the wire, when the peer takes
# them all: each reply as flat.shut leaves it, notes adding nothing. A
# Page's bytes are the file's, which this does not model, and raws says
# a list has none.
def wire(xs: List<&2, Eng.Seg>, sh: Bool) -> Bytes():
  match xs:
    case Nil{}:
      ""
    case Con{g, t}:
      match g:
        case Eng.Raw{bs}:
          Bytes.append(Eng.flat.shut(sh, bs), wire(t, False{}))
        case Eng.Note{bs}:
          wire(t, sh)
        case Eng.Shut{}:
          wire(t, True{})
        case Eng.Page{root, path, ct, head}:
          wire(t, False{})

def raws(xs: List<&2, Eng.Seg>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{g, t}:
      match g:
        case Eng.Raw{bs}:
          raws(t)
        case Eng.Note{bs}:
          raws(t)
        case Eng.Shut{}:
          raws(t)
        case Eng.Page{root, path, ct, head}:
          False{}

# the 400 that answers a grammar that broke
def bad.reply() -> List<&2, Eng.Seg>:
  [Eng.Raw{Eng.resp.bad()}]

# a peer that takes every byte at once, and what a send to it answers
def eager(rd: List<&2, Rd>, now: Nat, fs: List<&2, Fil>, out: Bytes()) -> World:
  World{rd, Nil{}, True{}, now, fs, out}

def sent(rd: List<&2, Rd>, now: Nat, fs: List<&2, Fil>, out: Bytes()) -> Eng.Put(World):
  (World{rd, Nil{}, True{}, now, fs, out}, Done{Unit{}})

# The model against the contracts: what one model read answers, judged
# by rx.ok, when the peer's next bytes fit the read; what one model send
# to a peer that has stopped reading answers, judged by tx.ok.
def fits(rd: List<&2, Rd>, +max: U32) -> Bool:
  match rd:
    case Nil{}:
      True{}
    case Con{e, t}:
      match e:
        case Give{wait, +bs}:
          U32.is_le(U32.from_nat(Bytes.len(bs)), max)
        case Hush{}:
          True{}
        case Cut{code}:
          True{}

def rx.seen(max: U32, +ms: U32, +t0: Nat, m: Eng.Got(World)) -> Bool:
  (s, r) = m
  rx.ok(max, ms, Nat.sub(w.now(s), t0), r)

def tx.seen(+ms: U32, stalled: Bool, +t0: Nat, m: Eng.Put(World)) -> Bool:
  (s, r) = m
  tx.ok(ms, stalled, Nat.sub(w.now(s), t0), r)
