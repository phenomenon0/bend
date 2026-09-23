# bend-wire: the world, as a pure model, its contracts, and the laws of
# the loops in it.
#
# wire/loop.bend writes the connection loop (conn, turn, send.segs and
# all under them) and the accept loop (accept.run) once, over an effect
# interface: a monad and one template parameter per effect.
# wire/effects.bend instantiates them with IO and the real effects. This
# file instantiates the same defs with the identity monad and a scripted
# world, and states and proves below what the loops do to every peer the
# script can describe -- for every protocol at once: the protocol's
# hooks are template parameters of every law, opaque to its proof, so a
# law here holds of any planner, any reader and any framing of replies.
#
# What a law needs of the protocol is written in it as an obligation,
# a template argument the protocol proves and hands in. There is one:
#
#   stall_ends   ~event_ok: an event of a stream is never empty once it
#                is framed, @+n: U32 -> {empty(shut(False{}, event(n)))
#                == False{}}, so a send of it to a stopped peer fails
#
# Everything else holds of the loop alone: the last act, the order of
# replies, nothing after a failed send, the buffers' bounds, the head's
# budget and deadline, a stopped peer let go, the accept loop staying up.
#
# The model is only as good as the contracts: what it assumes of each
# effect is written below as a relation on what the effect answers
# (rx.ok, tx.ok, lsn.ok, fopen.ok, fread.ok; cx.ok and tls.ok for the
# client's connects, idle.ok for its pool's probe), the model is proved to
# keep them (rx_model, tx_stalled, tx_served, fread_model), and
# wire/conform.bend drives each real effect through the same cases and
# checks the same relations against what it observes. That is the
# bridge; what is left trusted is that the effects keep their contract
# in the cases conform.bend does not try.
import Base
import ./loop.bend as L

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
) -> L.Got(World):
  match soon:
    case True{}:
      (World{t, wr, eager, Nat.add(now, wait), fs, out}, Done{Some{bs}})
    case False{}:
      (World{Con{Give{Nat.sub(wait, U32.to_nat(ms)), bs}, t}, wr, eager,
        Nat.add(now, U32.to_nat(ms)), fs, out}, Done{None{}})

def w.rx.go(s: World, +ms: U32) -> L.Got(World):
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

def w.rx(s: World, max: U32, ms: U32) -> L.Got(World):
  w.rx.go(s, ms)

# TCP.send_buf_poll: the peer takes the buffer as its script says; a
# wait of ms or more without progress fails the send with ETIMEDOUT
def w.tx.on(
  +wr: List<&2, Wr>, +bs: Bytes(), +ms: U32, +rd: List<&2, Rd>, +eager: Bool, +now: Nat,
  +fs: List<&2, Fil>, +out: Bytes()
) -> L.Put(World):
  match wr:
    case Nil{}:
      match bs:
        case SNil{}:
          (World{rd, Nil{}, eager, now, fs, out}, Done{Unit{}})
        case SCon{h, r}:
          Bool.pick(L.Put(World), eager,
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
              Bool.pick(L.Put(World), Nat.is_lt(wait, U32.to_nat(ms)),
                w.tx.on(t, String.drop(SCon{h, r}, 1n+more), ms, rd, eager, Nat.add(now, wait),
                  fs, Bytes.append(out, String.take(SCon{h, r}, 1n+more))),
                (World{rd, Con{Take{Nat.sub(wait, U32.to_nat(ms)), more}, t}, eager,
                  Nat.add(now, U32.to_nat(ms)), fs, out}, Fail{(110, "timed out")}))

def w.tx.go(s: World, bs: Bytes(), +ms: U32) -> L.Put(World):
  match s:
    case World{rd, wr, eager, now, fs, out}:
      w.tx.on(wr, bs, ms, rd, eager, now, fs, out)

def w.tx(s: World, bs: Bytes(), ms: U32) -> L.Put(World):
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
# effects, for a protocol's hooks: each is a pure function from a world
# to a world.

def sim.note(~lnote: Bytes() -> Bytes() -> String, may: Maybe<&2, Bytes()>, +out: Bytes()) ->
  Bytes():
  L.flat.note(~Id, ~Id.pure, ~Id.bind, ~w.say, ~lnote, may, out)

def sim.hold(+ms: U32, s: World, +acc: Bytes()) -> L.Em<World>:
  L.send.hold(~Id, ~Id.pure, ~Id.bind, ~World, ~w.tx, ms, s, acc)

def sim.raw(
  ~lnote: Bytes() -> Bytes() -> String, +ms: U32, may: Maybe<&2, Bytes()>, bs: Bytes(),
  st: L.Em<World>
) -> L.Em<World>:
  L.send.raw(~Id, ~Id.pure, ~Id.bind, ~World, ~w.tx, ~w.say, ~lnote, ms, may, bs, st)

def sim.page(
  ~shut: Bool -> Bytes() -> Bytes(), ~fhead: List<&2, U32> -> U32 -> Bytes(),
  ~miss: Bool -> Bytes(), ~lnote: Bytes() -> Bytes() -> String,
  ~lsize: Bytes() -> Bytes() -> U32 -> String, +ms: U32, root: List<&2, U32>, path: List<&2, U32>, ct: List<&2, U32>, head: Bool,
  may: Maybe<&2, Bytes()>, sh: Bool, st: L.Em<World>
) -> L.Em<World>:
  L.send.page(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~w.tx, ~w.say, ~w.fopen, ~w.fsize,
    ~w.fread, ~w.fclose, ~shut, ~fhead, ~miss, ~lnote, ~lsize, ms, root, path, ct, head, may, sh, st)

def sim.go(
  ~shut: Bool -> Bytes() -> Bytes(), ~fhead: List<&2, U32> -> U32 -> Bytes(),
  ~miss: Bool -> Bytes(), ~lnote: Bytes() -> Bytes() -> String,
  ~lsize: Bytes() -> Bytes() -> U32 -> String, xs: List<&2, L.Seg>, +ms: U32, may: Maybe<&2, Bytes()>, sh: Bool, st: L.Em<World>
) -> L.Put(World):
  L.send.go(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~w.tx, ~w.say, ~w.fopen, ~w.fsize,
    ~w.fread, ~w.fclose, ~shut, ~fhead, ~miss, ~lnote, ~lsize, xs, ms, may, sh, st)

def sim.segs(~shut: Bool -> Bytes() -> Bytes(), ~fhead: List<&2, U32> -> U32 -> Bytes(),
  ~miss: Bool -> Bytes(), ~lnote: Bytes() -> Bytes() -> String,
  ~lsize: Bytes() -> Bytes() -> U32 -> String, s: World, xs: List<&2, L.Seg>, +ms: U32) -> L.Put(World):
  L.send.segs(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~w.tx, ~w.say, ~w.fopen, ~w.fsize,
    ~w.fread, ~w.fclose, ~shut, ~fhead, ~miss, ~lnote, ~lsize, s, xs, ms)

def sim.turn.h(~E: Data, ~P: Data, ~U: Data, ~idle: E -> U32, ~hdms: E -> U32,
  ~plan: E -> Bytes() -> P -> L.Plan<P, U>, ~big: Bytes(), +srv: E, s: World, p: P, hw: L.Hw) -> (World & L.Plan<P, U>) & L.Hw:
  L.turn.h(~Id, ~Id.pure, ~Id.bind, ~World, ~w.rx, ~w.clk, ~E, ~P, ~U, ~idle, ~hdms, ~plan, ~big, srv, s, p, hw)

def sim.left(
  ~E: Data, ~P: Data, ~U: Data, ~idle: E -> U32, ~hdms: E -> U32,
  ~plan: E -> Bytes() -> P -> L.Plan<P, U>, ~big: Bytes(), +srv: E, s: World, p: P, t0: Nat, n: U32, +el: Nat, ok: Bool
) -> (World & L.Plan<P, U>) & L.Hw:
  L.turn.left(~Id, ~Id.pure, ~Id.bind, ~World, ~w.rx, ~E, ~P, ~U, ~idle, ~hdms, ~plan, ~big, srv, s, p, t0, n, el, ok)

def sim.held(+ms: U32, s: World, acc: Bytes(), c: Cmp) -> L.Em<World>:
  L.send.held(~Id, ~Id.pure, ~Id.bind, ~World, ~w.tx, ms, s, acc, c)

def sim.flushed(m: L.Put(World)) -> L.Em<World>:
  L.send.flushed(~Id, ~Id.pure, ~Id.bind, ~World, m)

def sim.pleft(+ms: U32, f: Bytes(), left: U32, s: World, pre: Bytes(), done: Bool) ->
  L.Pump<World, Bytes()>:
  L.pump.left(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~w.tx, ~w.fclose, ms, f, left, s, pre,
    done)

def sim.psent(+ms: U32, m: L.Put(World), f: Bytes(), +left: U32) -> L.Pump<World, Bytes()>:
  L.pump.sent(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~w.tx, ~w.fclose, ms, m, f, left)

def sim.pblock(
  +ms: U32, f: Bytes(), +left: U32, s: World, pre: Bytes(), bs: Bytes(), +n: U32, empty: Bool
) -> L.Pump<World, Bytes()>:
  L.pump.block(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~w.tx, ~w.fclose, ms, f, left, s,
    pre, bs, n, empty)

def sim.pgot(
  +ms: U32, got: Bytes() & Result<&1, &1, U32 & String, Bytes()>, left: U32, s: World,
  pre: Bytes()
) -> L.Pump<World, Bytes()>:
  L.pump.got(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~w.tx, ~w.fclose, ms, got, left, s, pre)

def sim.pump(k: Nat, +ms: U32, p: L.Pump<World, Bytes()>) -> L.Em<World>:
  L.pump(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~w.tx, ~w.fread, ~w.fclose, k, ms, p)

def sim.miss(
  ~shut: Bool -> Bytes() -> Bytes(), ~miss: Bool -> Bytes(), ~lnote: Bytes() -> Bytes() -> String,
  +ms: U32, head: Bool, may: Maybe<&2, Bytes()>, sh: Bool, s: World, acc: Bytes()
) -> L.Em<World>:
  L.page.miss(~Id, ~Id.pure, ~Id.bind, ~World, ~w.tx, ~w.say, ~shut, ~miss, ~lnote, ms, head, may,
    sh, s, acc)

def sim.pstart(
  ~lsize: Bytes() -> Bytes() -> U32 -> String, +ms: U32, f: Bytes(), +n: U32, +hd: Bytes(),
  head: Bool, may: Maybe<&2, Bytes()>, s: World, acc: Bytes()
) -> L.Em<World>:
  L.page.start(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~w.tx, ~w.say, ~w.fread, ~w.fclose,
    ~lsize, ms, f, n, hd, head, may, s, acc)

def sim.psized(
  ~shut: Bool -> Bytes() -> Bytes(), ~fhead: List<&2, U32> -> U32 -> Bytes(),
  ~miss: Bool -> Bytes(), ~lnote: Bytes() -> Bytes() -> String,
  ~lsize: Bytes() -> Bytes() -> U32 -> String, +ms: U32, got: Bytes() & Result<&1, &1, U32 & String, U32>, ct: List<&2, U32>,
  head: Bool, may: Maybe<&2, Bytes()>, sh: Bool, s: World, acc: Bytes()
) -> L.Em<World>:
  L.page.sized(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~w.tx, ~w.say, ~w.fread, ~w.fclose,
    ~shut, ~fhead, ~miss, ~lnote, ~lsize, ms, got, ct, head, may, sh, s, acc)

def sim.opened(
  ~shut: Bool -> Bytes() -> Bytes(), ~fhead: List<&2, U32> -> U32 -> Bytes(),
  ~miss: Bool -> Bytes(), ~lnote: Bytes() -> Bytes() -> String,
  ~lsize: Bytes() -> Bytes() -> U32 -> String, +ms: U32, m: World & Result<&1, &1, U32 & String, Bytes()>, ct: List<&2, U32>,
  head: Bool, may: Maybe<&2, Bytes()>, sh: Bool, acc: Bytes()
) -> L.Em<World>:
  L.page.opened(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~w.tx, ~w.say, ~w.fsize, ~w.fread,
    ~w.fclose, ~shut, ~fhead, ~miss, ~lnote, ~lsize, ms, m, ct, head, may, sh, acc)

def sim.turn(~E: Data, ~P: Data, ~U: Data, ~idle: E -> U32, ~hdms: E -> U32,
  ~plan: E -> Bytes() -> P -> L.Plan<P, U>, ~big: Bytes(), +srv: E, m: L.Put(World), p: P, hw: L.Hw) ->
  (World & L.Plan<P, U>) & L.Hw:
  L.turn(~Id, ~Id.pure, ~Id.bind, ~World, ~w.rx, ~w.clk, ~E, ~P, ~U, ~idle, ~hdms, ~plan, ~big, srv, m, p, hw)

def sim.turn.up(~E: Data, ~P: Data, ~U: Data, ~idle: E -> U32, ~uplan: U -> Bytes() -> L.Plan<P, U>, +srv: E, m: L.Put(World), wr: U) -> World & L.Plan<P, U>:
  L.turn.up(~Id, ~Id.pure, ~Id.bind, ~World, ~w.rx, ~E, ~P, ~U, ~idle, ~uplan, srv, m, wr)

def sim.tick(~P: Data, ~U: Data, ~gap: U32, ~event: U32 -> Bytes(), m: L.Put(World), n: U32) -> World & L.Plan<P, U>:
  L.tick(~Id, ~Id.pure, ~Id.bind, ~World, ~w.nap, ~P, ~U, ~gap, ~event, m, n)

def sim.conn(~E: Data, ~P: Data, ~U: Data, ~idle: E -> U32, ~hdms: E -> U32,
  ~plan: E -> Bytes() -> P -> L.Plan<P, U>, ~mid: P -> Bool, ~big: Bytes(),
  ~uplan: U -> Bytes() -> L.Plan<P, U>, ~gap: U32, ~event: U32 -> Bytes(),
  ~shut: Bool -> Bytes() -> Bytes(), ~fhead: List<&2, U32> -> U32 -> Bytes(),
  ~miss: Bool -> Bytes(), ~lnote: Bytes() -> Bytes() -> String,
  ~lsize: Bytes() -> Bytes() -> U32 -> String, f: Nat, +srv: E, sph: (World & L.Plan<P, U>) & L.Hw, w: Nat) -> World:
  L.conn(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~w.rx, ~w.tx, ~w.clk, ~w.nap, ~w.say,
    ~w.fopen, ~w.fsize, ~w.fread, ~w.fclose, ~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, f, srv, sph, w)

def sim.start(~E: Data, ~P: Data, ~U: Data, ~idle: E -> U32, ~hdms: E -> U32,
  ~plan: E -> Bytes() -> P -> L.Plan<P, U>, ~mid: P -> Bool, ~big: Bytes(),
  ~uplan: U -> Bytes() -> L.Plan<P, U>, ~gap: U32, ~event: U32 -> Bytes(),
  ~shut: Bool -> Bytes() -> Bytes(), ~fhead: List<&2, U32> -> U32 -> Bytes(),
  ~miss: Bool -> Bytes(), ~lnote: Bytes() -> Bytes() -> String,
  ~lsize: Bytes() -> Bytes() -> U32 -> String, +srv: E, p0: P, s: World) -> World:
  L.conn.start(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~w.rx, ~w.tx, ~w.clk, ~w.nap,
    ~w.say, ~w.fopen, ~w.fsize, ~w.fread, ~w.fclose, ~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, srv, p0, s)

# The mute peer
# =============
#
# A peer that has stopped: every read waits out its time and answers
# nothing, every send that has bytes to move waits out its time and
# fails, and an empty send, which moves nothing, succeeds. It is the
# scripted peer with both scripts spent, not eager, with the clock left
# out: what it answers does not depend on the world, which is what lets
# a law quantify over every state the loop can be in when it stops.

def m.rx(s: World, max: U32, ms: U32) -> L.Got(World):
  (s, Done{None{}})

def m.tx(s: World, bs: Bytes(), ms: U32) -> L.Put(World):
  match bs:
    case SNil{}:
      (s, Done{Unit{}})
    case SCon{h, t}:
      (s, Fail{(110, "timed out")})

def m.nap(s: World, ms: U32) -> World:
  s

def mute.conn(~E: Data, ~P: Data, ~U: Data, ~idle: E -> U32, ~hdms: E -> U32,
  ~plan: E -> Bytes() -> P -> L.Plan<P, U>, ~mid: P -> Bool, ~big: Bytes(),
  ~uplan: U -> Bytes() -> L.Plan<P, U>, ~gap: U32, ~event: U32 -> Bytes(),
  ~shut: Bool -> Bytes() -> Bytes(), ~fhead: List<&2, U32> -> U32 -> Bytes(),
  ~miss: Bool -> Bytes(), ~lnote: Bytes() -> Bytes() -> String,
  ~lsize: Bytes() -> Bytes() -> U32 -> String, f: Nat, +srv: E, sph: (World & L.Plan<P, U>) & L.Hw, w: Nat) -> World:
  L.conn(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~m.rx, ~m.tx, ~w.clk, ~m.nap, ~w.say,
    ~w.fopen, ~w.fsize, ~w.fread, ~w.fclose, ~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, f, srv, sph, w)

def mute.turn(~E: Data, ~P: Data, ~U: Data, ~idle: E -> U32, ~hdms: E -> U32,
  ~plan: E -> Bytes() -> P -> L.Plan<P, U>, ~big: Bytes(), +srv: E, m: L.Put(World), p: P, hw: L.Hw) ->
  (World & L.Plan<P, U>) & L.Hw:
  L.turn(~Id, ~Id.pure, ~Id.bind, ~World, ~m.rx, ~w.clk, ~E, ~P, ~U, ~idle, ~hdms, ~plan, ~big, srv, m, p, hw)

def mute.segs(~shut: Bool -> Bytes() -> Bytes(), ~fhead: List<&2, U32> -> U32 -> Bytes(),
  ~miss: Bool -> Bytes(), ~lnote: Bytes() -> Bytes() -> String,
  ~lsize: Bytes() -> Bytes() -> U32 -> String, s: World, xs: List<&2, L.Seg>, +ms: U32) -> L.Put(World):
  L.send.segs(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~m.tx, ~w.say, ~w.fopen, ~w.fsize,
    ~w.fread, ~w.fclose, ~shut, ~fhead, ~miss, ~lnote, ~lsize, s, xs, ms)

def mute.turn.h(~E: Data, ~P: Data, ~U: Data, ~idle: E -> U32, ~hdms: E -> U32,
  ~plan: E -> Bytes() -> P -> L.Plan<P, U>, ~big: Bytes(), +srv: E, s: World, p: P, hw: L.Hw) -> (World & L.Plan<P, U>) & L.Hw:
  L.turn.h(~Id, ~Id.pure, ~Id.bind, ~World, ~m.rx, ~w.clk, ~E, ~P, ~U, ~idle, ~hdms, ~plan, ~big, srv, s, p, hw)

def mute.left(
  ~E: Data, ~P: Data, ~U: Data, ~idle: E -> U32, ~hdms: E -> U32,
  ~plan: E -> Bytes() -> P -> L.Plan<P, U>, ~big: Bytes(), +srv: E, s: World, p: P, t0: Nat, n: U32, +el: Nat, ok: Bool
) -> (World & L.Plan<P, U>) & L.Hw:
  L.turn.left(~Id, ~Id.pure, ~Id.bind, ~World, ~m.rx, ~E, ~P, ~U, ~idle, ~hdms, ~plan, ~big, srv, s, p, t0, n, el, ok)

def mute.turn.up(~E: Data, ~P: Data, ~U: Data, ~idle: E -> U32, ~uplan: U -> Bytes() -> L.Plan<P, U>, +srv: E, m: L.Put(World), wr: U) -> World & L.Plan<P, U>:
  L.turn.up(~Id, ~Id.pure, ~Id.bind, ~World, ~m.rx, ~E, ~P, ~U, ~idle, ~uplan, srv, m, wr)

def mute.tick(~P: Data, ~U: Data, ~gap: U32, ~event: U32 -> Bytes(), m: L.Put(World), n: U32) -> World & L.Plan<P, U>:
  L.tick(~Id, ~Id.pure, ~Id.bind, ~World, ~m.nap, ~P, ~U, ~gap, ~event, m, n)

def mute.held(+ms: U32, s: World, acc: Bytes(), c: Cmp) -> L.Em<World>:
  L.send.held(~Id, ~Id.pure, ~Id.bind, ~World, ~m.tx, ms, s, acc, c)

def mute.go(
  ~shut: Bool -> Bytes() -> Bytes(), ~fhead: List<&2, U32> -> U32 -> Bytes(),
  ~miss: Bool -> Bytes(), ~lnote: Bytes() -> Bytes() -> String,
  ~lsize: Bytes() -> Bytes() -> U32 -> String, xs: List<&2, L.Seg>, +ms: U32, may: Maybe<&2, Bytes()>, sh: Bool, st: L.Em<World>
) -> L.Put(World):
  L.send.go(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~m.tx, ~w.say, ~w.fopen, ~w.fsize,
    ~w.fread, ~w.fclose, ~shut, ~fhead, ~miss, ~lnote, ~lsize, xs, ms, may, sh, st)

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

def sim.acc.run(k: Nat, lw: Lw & Maybe<&2, L.Why>) -> Lw & L.Why:
  L.accept.run(~Id, ~Id.pure, ~Id.bind, ~Lw, ~Unit, ~Unit, ~l.lsn, ~l.sig, ~l.hand, k,
    Unit{}, lw)

def sim.acc.dead(k: Nat, l: Lw, +code: U32, soft: Bool) -> Lw & L.Why:
  sim.acc.run(k, L.accept.dead(~Id, ~Id.pure, ~Id.bind, ~Lw, ~l.sig, l, code, soft))

def sim.accept(k: Nat, l: Lw) -> Lw & L.Why:
  L.accept.run(~Id, ~Id.pure, ~Id.bind, ~Lw, ~Unit, ~Unit, ~l.lsn, ~l.sig, ~l.hand, k,
    Unit{}, (l, None{}))

# The contracts
# =============
#
# What the model assumes of each effect, as a relation on what one call
# answered. The same text stands beside each effect in bend2/base.bend;
# wire/conform.bend checks the real effects against these very defs.

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

# TCP.send_buf_poll(s, bytes, ms), to a peer that reads (each piece of
# progress within ms of the last), that stops reading, or that resets:
# the first is served however long the whole takes; the second fails
# the send with ETIMEDOUT (110 on Linux, 60 on macOS) after at least
# ms; the third fails it. took is how long the send took.
type Peer is Data:
  Reads{}
  Stops{}
  Resets{}

def etimedout(+code: U32) -> Bool:
  U32.is_eq(code, 110) || U32.is_eq(code, 60)

def tx.timed(e: U32 & String, +took: Nat, +ms: U32) -> Bool:
  (code, msg) = e
  etimedout(code) && Nat.is_le(U32.to_nat(ms), took)

def tx.ok(+ms: U32, peer: Peer, +took: Nat, r: Result<&1, &1, U32 & String, Unit>) -> Bool:
  match peer:
    case Reads{}:
      Result.is_done(&1, &1, U32 & String, Unit, r)
    case Stops{}:
      match r:
        case Done{u}:
          False{}
        case Fail{e}:
          tx.timed(e, took, ms)
    case Resets{}:
      Result.is_fail(&1, &1, U32 & String, Unit, r)

# TCP.accept_poll(l, ms): a connection, nothing (once ms have passed, or
# after it shed one arrival it had no descriptor for), or a failure --
# and a failure only for a listener that is no longer one: never with a
# code of the passing set (L.accept.soft).
def lsn.dead(e: U32 & String) -> Bool:
  (code, msg) = e
  Bool.not(L.accept.soft(code))

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

# TCP.connect_poll(host, port, ms), answering after took ms, to a peer
# that accepts, to a port nothing listens on, or to one that never
# answers (its SYNs dropped): the first is Done; the second fails with
# ECONNREFUSED (111 on Linux, 61 on macOS); the third fails with
# ETIMEDOUT after at least ms.
type Dial is Data:
  Accepts{}
  Closed{}
  Silent{}

def econnrefused(+code: U32) -> Bool:
  U32.is_eq(code, 111) || U32.is_eq(code, 61)

def cx.refused(e: U32 & String) -> Bool:
  (code, msg) = e
  econnrefused(code)

def cx.ok(+ms: U32, d: Dial, +took: Nat, r: Result<&1, &1, U32 & String, Unit>) -> Bool:
  match d:
    case Accepts{}:
      Result.is_done(&1, &1, U32 & String, Unit, r)
    case Closed{}:
      match r:
        case Done{u}:
          False{}
        case Fail{e}:
          cx.refused(e)
    case Silent{}:
      match r:
        case Done{u}:
          False{}
        case Fail{e}:
          tx.timed(e, took, ms)

# TLS.connect(addr, port, name, alpn, ca, ms) to a server whose
# certificate chains to the store and names name, to one whose
# certificate does not chain to it, to one whose certificate names
# another host, and to one that does not speak TLS: only the first is
# Done; the certificate refusals are EACCES (13); the last fails with
# anything else.
type Cert is Data:
  Trusted{}
  Untrusted{}
  Misnamed{}
  NotTls{}

def eacces(e: U32 & String) -> Bool:
  (code, msg) = e
  U32.is_eq(code, 13)

def tls.ok(c: Cert, r: Result<&1, &1, U32 & String, Unit>) -> Bool:
  match c:
    case Trusted{}:
      Result.is_done(&1, &1, U32 & String, Unit, r)
    case Untrusted{}:
      match r:
        case Done{u}:
          False{}
        case Fail{e}:
          eacces(e)
    case Misnamed{}:
      match r:
        case Done{u}:
          False{}
        case Fail{e}:
          eacces(e)
    case NotTls{}:
      match r:
        case Done{u}:
          False{}
        case Fail{e}:
          Bool.not(eacces(e))

# TCP.idle(s), on a connection where nothing waits, where a byte has
# arrived unread, or whose peer has closed: True only for the first.
type Pend is Data:
  PQuiet{}
  PByte{}
  PFin{}

def idle.ok(k: Pend, ok: Bool) -> Bool:
  match k:
    case PQuiet{}:
      ok
    case PByte{}:
      Bool.not(ok)
    case PFin{}:
      Bool.not(ok)

# What the laws speak of
# ======================

# a writer that may still take replies holds a batch below the cap; one
# that may not (a send failed, a file came up short) holds what it will
# write last
def em.fine(em: L.Em<World>) -> Bool:
  match em:
    case L.Em{s, acc, ok}:
      match ok:
        case True{}:
          U32.is_lt(U32.from_nat(Bytes.len(acc)), L.send.cap())
        case False{}:
          True{}

def pump.fine(p: L.Pump<World, Bytes()>) -> Bool:
  match p:
    case L.Going{f, left, s, pre}:
      True{}
    case L.Over{em}:
      em.fine(em)

# a head in progress has had at most head.cap() bytes since the read it
# began in
def hw.fine(hw: L.Hw) -> Bool:
  match hw:
    case L.NoHead{}:
      True{}
    case L.Begun{}:
      True{}
    case L.Since{t0, n}:
      Bool.not(U32.is_lt(L.head.cap(), n))

def hw.of(-X: Type, q: X & L.Hw) -> L.Hw:
  (sp, hw) = q
  hw

def put.done(m: L.Put(World)) -> Bool:
  (s, r) = m
  Result.is_done(&1, &1, U32 & String, Unit, r)

def why.of(r: Lw & L.Why) -> L.Why:
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
          L.accept.soft(code) && calm(t)
        case Term{}:
          False{}

# the loop ended as it may: its turns spent, a stop asked, or a code
# outside the passing set
def ok.end(why: L.Why) -> Bool:
  match why:
    case L.Spent{}:
      True{}
    case L.Asked{}:
      True{}
    case L.Dead{+code}:
      Bool.not(L.accept.soft(code))

# The bytes a list of segments puts on the wire, when the peer takes
# them all: each reply as the protocol's shut leaves it, notes adding
# nothing. A Page's bytes are the file's, which this does not model, and
# raws says a list has none.
def wire(~shut: Bool -> Bytes() -> Bytes(), xs: List<&2, L.Seg>, sh: Bool) -> Bytes():
  match xs:
    case Nil{}:
      ""
    case Con{g, t}:
      match g:
        case L.Raw{bs}:
          Bytes.append(shut(sh, bs), wire(~shut, t, False{}))
        case L.Note{bs}:
          wire(~shut, t, sh)
        case L.Shut{}:
          wire(~shut, t, True{})
        case L.Page{root, path, ct, head}:
          wire(~shut, t, False{})

def raws(xs: List<&2, L.Seg>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{g, t}:
      match g:
        case L.Raw{bs}:
          raws(t)
        case L.Note{bs}:
          raws(t)
        case L.Shut{}:
          raws(t)
        case L.Page{root, path, ct, head}:
          False{}

# a peer that takes every byte at once, and what a send to it answers
def eager(rd: List<&2, Rd>, now: Nat, fs: List<&2, Fil>, out: Bytes()) -> World:
  World{rd, Nil{}, True{}, now, fs, out}

def sent(rd: List<&2, Rd>, now: Nat, fs: List<&2, Fil>, out: Bytes()) -> L.Put(World):
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

def rx.seen(max: U32, +ms: U32, +t0: Nat, m: L.Got(World)) -> Bool:
  (s, r) = m
  rx.ok(max, ms, Nat.sub(w.now(s), t0), r)

def tx.seen(+ms: U32, peer: Peer, +t0: Nat, m: L.Put(World)) -> Bool:
  (s, r) = m
  tx.ok(ms, peer, Nat.sub(w.now(s), t0), r)

# The laws
# ========
#
# The loops in the model are pure functions, so most of these compute
# once the right thing is generalised. A value the proof cannot see (a
# send's answer, a comparison with the cap, a Bool the premise pins, a
# protocol's hook) is made a variable by a lemma quantified over it,
# with the equation that says what it was. end_is_last, stop_is_last
# and go_order compute; fail_* take the send's answer apart; the
# buffering laws walk the writer (send.hold, send.raw, and a file
# through fopen, fsize, page.start and the pump) with the comparison
# with the cap generalised; segs_wire walks send.go with the held batch,
# and the peer's appends reassociated; stall_ends shows that a turn at
# the mute peer always plans Stop (or, for a stream, plans one event
# whose send must fail), so that fuel past three turns is never used;
# accept_* walk accept.run one event at a time.

def BD(b: Bool, tc: Type, fc: Type) -> Type:
  match b:
    case True{}:
      tc
    case False{}:
      fc

def no(-g: Type, e: {False{} == True{} : Bool}) -> g:
  %e : BD(_, g, Unit)
  Unit{}

# LAW: a plan that ends the connection is the last thing it does. After
# End the loop writes its segments and answers the socket, to be
# closed, with nothing read and nothing more written; after Stop it
# does nothing at all.
law end_is_last:
  for ~E: Data
  for ~P: Data
  for ~U: Data
  for ~idle: E -> U32
  for ~hdms: E -> U32
  for ~plan: E -> Bytes() -> P -> L.Plan<P, U>
  for ~mid: P -> Bool
  for ~big: Bytes()
  for ~uplan: U -> Bytes() -> L.Plan<P, U>
  for ~gap: U32
  for ~event: U32 -> Bytes()
  for ~shut: Bool -> Bytes() -> Bytes()
  for ~fhead: List<&2, U32> -> U32 -> Bytes()
  for ~miss: Bool -> Bytes()
  for ~lnote: Bytes() -> Bytes() -> String
  for ~lsize: Bytes() -> Bytes() -> U32 -> String
  for +srv: E
  for w: World
  for out: List<&2, L.Seg>
  for hw: L.Hw
  for g: Nat
  for v: Nat
  {sim.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 1n+g, srv, ((w, L.End{out}), hw), v) ==
    L.put.s(World, sim.segs(~shut, ~fhead, ~miss, ~lnote, ~lsize, w, out, idle(srv))) : World}

def end_is_last(E, P, U, idle, hdms, plan, mid, big, uplan, gap, event, shut, fhead, miss, lnote, lsize, srv, w, out, hw, g, v):
  {==}

law stop_is_last:
  for ~E: Data
  for ~P: Data
  for ~U: Data
  for ~idle: E -> U32
  for ~hdms: E -> U32
  for ~plan: E -> Bytes() -> P -> L.Plan<P, U>
  for ~mid: P -> Bool
  for ~big: Bytes()
  for ~uplan: U -> Bytes() -> L.Plan<P, U>
  for ~gap: U32
  for ~event: U32 -> Bytes()
  for ~shut: Bool -> Bytes() -> Bytes()
  for ~fhead: List<&2, U32> -> U32 -> Bytes()
  for ~miss: Bool -> Bytes()
  for ~lnote: Bytes() -> Bytes() -> String
  for ~lsize: Bytes() -> Bytes() -> U32 -> String
  for +srv: E
  for w: World
  for hw: L.Hw
  for g: Nat
  for v: Nat
  {sim.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 1n+g, srv, ((w, L.Stop{}), hw), v) == w : World}

def stop_is_last(E, P, U, idle, hdms, plan, mid, big, uplan, gap, event, shut, fhead, miss, lnote, lsize, srv, w, hw, g, v):
  {==}

# LAW: a plan that reads on writes all its replies first. Go's segments
# go out, the next read waits for them, and the head's watch starts
# over.
law go_order:
  for ~E: Data
  for ~P: Data
  for ~U: Data
  for ~idle: E -> U32
  for ~hdms: E -> U32
  for ~plan: E -> Bytes() -> P -> L.Plan<P, U>
  for ~mid: P -> Bool
  for ~big: Bytes()
  for ~uplan: U -> Bytes() -> L.Plan<P, U>
  for ~gap: U32
  for ~event: U32 -> Bytes()
  for ~shut: Bool -> Bytes() -> Bytes()
  for ~fhead: List<&2, U32> -> U32 -> Bytes()
  for ~miss: Bool -> Bytes()
  for ~lnote: Bytes() -> Bytes() -> String
  for ~lsize: Bytes() -> Bytes() -> U32 -> String
  for +srv: E
  for w: World
  for out: List<&2, L.Seg>
  for +p2: P
  for hw: L.Hw
  for g: Nat
  for v: Nat
  {sim.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 1n+g, srv, ((w, L.Go{out, p2}), hw), v) ==
    sim.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, g, srv, sim.turn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~big, srv, sim.segs(~shut, ~fhead, ~miss, ~lnote, ~lsize, w, out, idle(srv)), p2,
      L.hw.next(mid(p2), L.NoHead{})), L.conn.waits()) : World}

def go_order(E, P, U, idle, hdms, plan, mid, big, uplan, gap, event, shut, fhead, miss, lnote, lsize, srv, w, out, p2, hw, g, v):
  {==}

# LAW: nothing is done after a send fails. Whether the send was a read's
# replies, an upgraded connection's or a stream's event, a send that
# failed or stalled is the connection's last act on its socket: no
# read, no write (the stream only finishes the sleep it was in).
law fail_go:
  for ~E: Data
  for ~P: Data
  for ~U: Data
  for ~idle: E -> U32
  for ~hdms: E -> U32
  for ~plan: E -> Bytes() -> P -> L.Plan<P, U>
  for ~mid: P -> Bool
  for ~big: Bytes()
  for ~uplan: U -> Bytes() -> L.Plan<P, U>
  for ~gap: U32
  for ~event: U32 -> Bytes()
  for ~shut: Bool -> Bytes() -> Bytes()
  for ~fhead: List<&2, U32> -> U32 -> Bytes()
  for ~miss: Bool -> Bytes()
  for ~lnote: Bytes() -> Bytes() -> String
  for ~lsize: Bytes() -> Bytes() -> U32 -> String
  for +srv: E
  for g: Nat
  for v: Nat
  for m: L.Put(World)
  for p: P
  for hw: L.Hw
  for e: {put.done(m) == False{} : Bool}
  {sim.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, g, srv, sim.turn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~big, srv, m, p, hw), v) == L.put.s(World, m) : World}

def fail_go(E, P, U, idle, hdms, plan, mid, big, uplan, gap, event, shut, fhead, miss, lnote, lsize, srv, g, v, m, p, hw, e):
  match g:
    case 0n:
      (s, r) = m
      match r:
        case Fail{x}:
          {==}
        case Done{u}:
          no({sim.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 0n, srv, sim.turn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~big, srv, (s, Done{u}), p, hw), v) == s : World},
            Equal.sym(Bool, True{}, False{}, e))
    case 1n+h:
      (s, r) = m
      match r:
        case Fail{x}:
          {==}
        case Done{u}:
          no({sim.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 1n+h, srv, sim.turn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~big, srv, (s, Done{u}), p, hw), v) == s :
            World}, Equal.sym(Bool, True{}, False{}, e))

law fail_up:
  for ~E: Data
  for ~P: Data
  for ~U: Data
  for ~idle: E -> U32
  for ~hdms: E -> U32
  for ~plan: E -> Bytes() -> P -> L.Plan<P, U>
  for ~mid: P -> Bool
  for ~big: Bytes()
  for ~uplan: U -> Bytes() -> L.Plan<P, U>
  for ~gap: U32
  for ~event: U32 -> Bytes()
  for ~shut: Bool -> Bytes() -> Bytes()
  for ~fhead: List<&2, U32> -> U32 -> Bytes()
  for ~miss: Bool -> Bytes()
  for ~lnote: Bytes() -> Bytes() -> String
  for ~lsize: Bytes() -> Bytes() -> U32 -> String
  for +srv: E
  for g: Nat
  for v: Nat
  for m: L.Put(World)
  for wr: U
  for e: {put.done(m) == False{} : Bool}
  {sim.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, g, srv, (sim.turn.up(~E, ~P, ~U, ~idle, ~uplan, srv, m, wr), L.NoHead{}), v) ==
    L.put.s(World, m) : World}

def fail_up(E, P, U, idle, hdms, plan, mid, big, uplan, gap, event, shut, fhead, miss, lnote, lsize, srv, g, v, m, wr, e):
  match g:
    case 0n:
      (s, r) = m
      match r:
        case Fail{x}:
          {==}
        case Done{u}:
          no({sim.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 0n, srv, (sim.turn.up(~E, ~P, ~U, ~idle, ~uplan, srv, (s, Done{u}), wr), L.NoHead{}),
            v) == s : World}, Equal.sym(Bool, True{}, False{}, e))
    case 1n+h:
      (s, r) = m
      match r:
        case Fail{x}:
          {==}
        case Done{u}:
          no({sim.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 1n+h, srv, (sim.turn.up(~E, ~P, ~U, ~idle, ~uplan, srv, (s, Done{u}), wr),
            L.NoHead{}), v) == s : World}, Equal.sym(Bool, True{}, False{}, e))

law fail_feed:
  for ~E: Data
  for ~P: Data
  for ~U: Data
  for ~idle: E -> U32
  for ~hdms: E -> U32
  for ~plan: E -> Bytes() -> P -> L.Plan<P, U>
  for ~mid: P -> Bool
  for ~big: Bytes()
  for ~uplan: U -> Bytes() -> L.Plan<P, U>
  for ~gap: U32
  for ~event: U32 -> Bytes()
  for ~shut: Bool -> Bytes() -> Bytes()
  for ~fhead: List<&2, U32> -> U32 -> Bytes()
  for ~miss: Bool -> Bytes()
  for ~lnote: Bytes() -> Bytes() -> String
  for ~lsize: Bytes() -> Bytes() -> U32 -> String
  for +srv: E
  for g: Nat
  for v: Nat
  for m: L.Put(World)
  for n: U32
  for e: {put.done(m) == False{} : Bool}
  {sim.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, g, srv, (sim.tick(~P, ~U, ~gap, ~event, m, n), L.NoHead{}), v) ==
    w.nap(L.put.s(World, m), gap) : World}

def fail_feed(E, P, U, idle, hdms, plan, mid, big, uplan, gap, event, shut, fhead, miss, lnote, lsize, srv, g, v, m, n, e):
  match g:
    case 0n:
      (s, r) = m
      match r:
        case Fail{x}:
          {==}
        case Done{u}:
          no({sim.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 0n, srv, (sim.tick(~P, ~U, ~gap, ~event, (s, Done{u}), n), L.NoHead{}), v) ==
            w.nap(s, gap) : World}, Equal.sym(Bool, True{}, False{}, e))
    case 1n+h:
      (s, r) = m
      match r:
        case Fail{x}:
          {==}
        case Done{u}:
          no({sim.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 1n+h, srv, (sim.tick(~P, ~U, ~gap, ~event, (s, Done{u}), n), L.NoHead{}), v) ==
            w.nap(s, gap) : World}, Equal.sym(Bool, True{}, False{}, e))

# LAW: the head deadline. A head whose time (the protocol's hdms) has
# run out is not read again: the turn ends the connection there,
# whatever the peer would have sent. (A head's time is kept across the
# reads that continue it: hw_keeps.)
law head_expires:
  for ~E: Data
  for ~P: Data
  for ~U: Data
  for ~idle: E -> U32
  for ~hdms: E -> U32
  for ~plan: E -> Bytes() -> P -> L.Plan<P, U>
  for ~big: Bytes()
  for +srv: E
  for +w: World
  for p: P
  for +t0: Nat
  for n: U32
  for e: {Nat.is_lt(Nat.sub(w.now(w), t0), U32.to_nat(hdms(srv))) == False{} : Bool}
  {sim.turn.h(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~big, srv, w, p, L.Since{t0, n}) == ((w, L.Stop{}), L.NoHead{}) :
    (World & L.Plan<P, U>) & L.Hw}

def head_expires(E, P, U, idle, hdms, plan, big, srv, w, p, t0, n, e):
  %Equal.sym(Bool, Nat.is_lt(Nat.sub(w.now(w), t0), U32.to_nat(hdms(srv))), False{}, e) :
    {sim.left(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~big, srv, w, p, t0, n, Nat.sub(w.now(w), t0), _) == ((w, L.Stop{}), L.NoHead{}) :
      (World & L.Plan<P, U>) & L.Hw}
  {==}

# LAW: bounded buffering, the head. A read that leaves a head in
# progress leaves it with at most head.cap() bytes since the read it
# began in; one that would take it past is answered with the protocol's
# big reply and the connection ends. With a read at most chunk() bytes,
# a head held is at most chunk() + head.cap().
law wl.head_sized:
  for ~E: Data
  for ~P: Data
  for ~U: Data
  for ~plan: E -> Bytes() -> P -> L.Plan<P, U>
  for ~big: Bytes()
  for +srv: E
  for w: World
  for buf: Bytes()
  for p: P
  for t0: Nat
  for +k: U32
  for over: Bool
  for e: {over == U32.is_lt(L.head.cap(), k) : Bool}
  {hw.fine(hw.of(World & L.Plan<P, U>, L.plan.sized(~E, ~P, ~U, ~plan, ~big, World, srv, w, buf, p,
    t0, k, over))) == True{} : Bool}

def wl.head_sized(E, P, U, plan, big, srv, w, buf, p, t0, k, over, e):
  match over:
    case True{}:
      {==}
    case False{}:
      %e : {Bool.not(_) == True{} : Bool}
      {==}

law head_capped:
  for ~E: Data
  for ~P: Data
  for ~U: Data
  for ~plan: E -> Bytes() -> P -> L.Plan<P, U>
  for ~big: Bytes()
  for +srv: E
  for w: World
  for may: Maybe<&1, Bytes()>
  for p: P
  for t0: Nat
  for +n: U32
  {hw.fine(hw.of(World & L.Plan<P, U>, L.plan.counted(~E, ~P, ~U, ~plan, ~big, World, srv, w, may,
    p, t0, n))) == True{} : Bool}

def head_capped(E, P, U, plan, big, srv, w, may, p, t0, n):
  match may:
    case None{}:
      {==}
    case Some{+buf}:
      wl.head_sized(~E, ~P, ~U, ~plan, ~big, srv, w, buf, p, t0,
        (n + U32.from_nat(Bytes.len(buf)) : U32),
        U32.is_lt(L.head.cap(), (n + U32.from_nat(Bytes.len(buf)) : U32)), {==})

# LAW: bounded buffering, the replies. Whatever a reply is -- a fixed
# one, a missing file, a file of any size, streamed in blocks -- and
# whatever the peer does, a writer that may still take replies leaves
# it holding a batch below send.cap(): so the most ever held unsent is
# the cap, plus the one reply (or a file's head and one page.chunk()
# block) that crossed it.
law wl.flushed_fine:
  for m: L.Put(World)
  {em.fine(sim.flushed(m)) == True{} : Bool}

def wl.flushed_fine(m):
  (s, r) = m
  match r:
    case Done{u}:
      {==}
    case Fail{e}:
      {==}

law wl.held_fine:
  for +ms: U32
  for s: World
  for +acc: Bytes()
  for c: Cmp
  for e: {c == U32.cmp(U32.from_nat(Bytes.len(acc)), L.send.cap()) : Cmp}
  {em.fine(sim.held(ms, s, acc, c)) == True{} : Bool}

def wl.held_fine(ms, s, acc, c, e):
  match c:
    case LT{}:
      %e : {Cmp.is_lt(_) == True{} : Bool}
      {==}
    case EQ{}:
      wl.flushed_fine(w.tx(s, acc, ms))
    case GT{}:
      wl.flushed_fine(w.tx(s, acc, ms))

law hold_fine:
  for +ms: U32
  for s: World
  for +acc: Bytes()
  {em.fine(sim.hold(ms, s, acc)) == True{} : Bool}

def hold_fine(ms, s, acc):
  wl.held_fine(ms, s, acc, U32.cmp(U32.from_nat(Bytes.len(acc)), L.send.cap()), {==})

law raw_fine:
  for ~lnote: Bytes() -> Bytes() -> String
  for +ms: U32
  for may: Maybe<&2, Bytes()>
  for bs: Bytes()
  for st: L.Em<World>
  {em.fine(sim.raw(~lnote, ms, may, bs, st)) == True{} : Bool}

def raw_fine(lnote, ms, may, bs, st):
  match st:
    case L.Em{s, acc, ok}:
      match ok:
        case False{}:
          {==}
        case True{}:
          hold_fine(ms, s, Bytes.append(acc, sim.note(~lnote, may, bs)))

law wl.pleft_fine:
  for +ms: U32
  for f: Bytes()
  for left: U32
  for s: World
  for pre: Bytes()
  for done: Bool
  {pump.fine(sim.pleft(ms, f, left, s, pre, done)) == True{} : Bool}

def wl.pleft_fine(ms, f, left, s, pre, done):
  match done:
    case True{}:
      hold_fine(ms, s, pre)
    case False{}:
      {==}

law wl.psent_fine:
  for +ms: U32
  for m: L.Put(World)
  for f: Bytes()
  for +left: U32
  {pump.fine(sim.psent(ms, m, f, left)) == True{} : Bool}

def wl.psent_fine(ms, m, f, left):
  (s, r) = m
  match r:
    case Fail{e}:
      {==}
    case Done{u}:
      wl.pleft_fine(ms, f, left, s, "", U32.is_zero(left))

law wl.pblock_fine:
  for +ms: U32
  for f: Bytes()
  for +left: U32
  for s: World
  for pre: Bytes()
  for bs: Bytes()
  for +n: U32
  for empty: Bool
  {pump.fine(sim.pblock(ms, f, left, s, pre, bs, n, empty)) == True{} : Bool}

def wl.pblock_fine(ms, f, left, s, pre, bs, n, empty):
  match empty:
    case True{}:
      {==}
    case False{}:
      wl.psent_fine(ms, w.tx(s, Bytes.append(pre, bs), ms), f, (left - n : U32))

law wl.pgot_fine:
  for +ms: U32
  for got: Bytes() & Result<&1, &1, U32 & String, Bytes()>
  for left: U32
  for s: World
  for pre: Bytes()
  {pump.fine(sim.pgot(ms, got, left, s, pre)) == True{} : Bool}

def wl.pgot_fine(ms, got, left, s, pre):
  (f, r) = got
  match r:
    case Fail{e}:
      {==}
    case Done{+bs}:
      wl.pblock_fine(ms, f, left, s, pre, bs, U32.from_nat(Bytes.len(bs)),
        U32.is_zero(U32.from_nat(Bytes.len(bs))))

law wl.pump_fine:
  for k: Nat
  for +ms: U32
  for p: L.Pump<World, Bytes()>
  for e: {pump.fine(p) == True{} : Bool}
  {em.fine(sim.pump(k, ms, p)) == True{} : Bool}

def wl.pump_fine(k, ms, p, e):
  match k:
    case 0n:
      match p:
        case L.Going{f, left, s, pre}:
          {==}
        case L.Over{em}:
          e
    case 1n+j:
      match p:
        case L.Over{em}:
          e
        case L.Going{+f, +left, +s, +pre}:
          wl.pump_fine(j, ms, sim.pgot(ms, w.fread(f, U32.min(L.page.chunk(), left)), left, s, pre),
            wl.pgot_fine(ms, w.fread(f, U32.min(L.page.chunk(), left)), left, s, pre))

law wl.miss_fine:
  for ~shut: Bool -> Bytes() -> Bytes()
  for ~miss: Bool -> Bytes()
  for ~lnote: Bytes() -> Bytes() -> String
  for +ms: U32
  for head: Bool
  for may: Maybe<&2, Bytes()>
  for sh: Bool
  for s: World
  for acc: Bytes()
  {em.fine(sim.miss(~shut, ~miss, ~lnote, ms, head, may, sh, s, acc)) == True{} : Bool}

def wl.miss_fine(shut, miss, lnote, ms, head, may, sh, s, acc):
  hold_fine(ms, s, Bytes.append(acc, sim.note(~lnote, may, shut(sh, miss(head)))))

law wl.pstart_fine:
  for ~lsize: Bytes() -> Bytes() -> U32 -> String
  for +ms: U32
  for +f: Bytes()
  for +n: U32
  for +hd: Bytes()
  for head: Bool
  for may: Maybe<&2, Bytes()>
  for +s: World
  for +acc: Bytes()
  {em.fine(sim.pstart(~lsize, ms, f, n, hd, head, may, s, acc)) == True{} : Bool}

def wl.pstart_fine(lsize, ms, f, n, hd, head, may, s, acc):
  match head:
    case True{}:
      hold_fine(ms, s, Bytes.append(acc, hd))
    case False{}:
      wl.pump_fine(U32.to_nat((n / L.page.chunk() + 64 : U32)), ms,
        sim.pleft(ms, f, n, s, Bytes.append(acc, hd), U32.is_zero(n)),
        wl.pleft_fine(ms, f, n, s, Bytes.append(acc, hd), U32.is_zero(n)))

law wl.psized_fine:
  for ~shut: Bool -> Bytes() -> Bytes()
  for ~fhead: List<&2, U32> -> U32 -> Bytes()
  for ~miss: Bool -> Bytes()
  for ~lnote: Bytes() -> Bytes() -> String
  for ~lsize: Bytes() -> Bytes() -> U32 -> String
  for +ms: U32
  for got: Bytes() & Result<&1, &1, U32 & String, U32>
  for ct: List<&2, U32>
  for head: Bool
  for may: Maybe<&2, Bytes()>
  for sh: Bool
  for s: World
  for acc: Bytes()
  {em.fine(sim.psized(~shut, ~fhead, ~miss, ~lnote, ~lsize, ms, got, ct, head, may, sh, s, acc)) == True{} : Bool}

def wl.psized_fine(shut, fhead, miss, lnote, lsize, ms, got, ct, head, may, sh, s, acc):
  (f, r) = got
  match r:
    case Fail{e}:
      wl.miss_fine(~shut, ~miss, ~lnote, ms, head, may, sh, s, acc)
    case Done{+n}:
      wl.pstart_fine(~lsize, ms, f, n, shut(sh, fhead(ct, n)), head, may, s, acc)

law wl.opened_fine:
  for ~shut: Bool -> Bytes() -> Bytes()
  for ~fhead: List<&2, U32> -> U32 -> Bytes()
  for ~miss: Bool -> Bytes()
  for ~lnote: Bytes() -> Bytes() -> String
  for ~lsize: Bytes() -> Bytes() -> U32 -> String
  for +ms: U32
  for m: World & Result<&1, &1, U32 & String, Bytes()>
  for ct: List<&2, U32>
  for head: Bool
  for may: Maybe<&2, Bytes()>
  for sh: Bool
  for acc: Bytes()
  {em.fine(sim.opened(~shut, ~fhead, ~miss, ~lnote, ~lsize, ms, m, ct, head, may, sh, acc)) == True{} : Bool}

def wl.opened_fine(shut, fhead, miss, lnote, lsize, ms, m, ct, head, may, sh, acc):
  (s, r) = m
  match r:
    case Fail{e}:
      wl.miss_fine(~shut, ~miss, ~lnote, ms, head, may, sh, s, acc)
    case Done{f}:
      wl.psized_fine(~shut, ~fhead, ~miss, ~lnote, ~lsize, ms, w.fsize(f), ct, head, may, sh, s, acc)

law page_fine:
  for ~shut: Bool -> Bytes() -> Bytes()
  for ~fhead: List<&2, U32> -> U32 -> Bytes()
  for ~miss: Bool -> Bytes()
  for ~lnote: Bytes() -> Bytes() -> String
  for ~lsize: Bytes() -> Bytes() -> U32 -> String
  for +ms: U32
  for root: List<&2, U32>
  for path: List<&2, U32>
  for ct: List<&2, U32>
  for head: Bool
  for may: Maybe<&2, Bytes()>
  for sh: Bool
  for st: L.Em<World>
  {em.fine(sim.page(~shut, ~fhead, ~miss, ~lnote, ~lsize, ms, root, path, ct, head, may, sh, st)) == True{} : Bool}

def page_fine(shut, fhead, miss, lnote, lsize, ms, root, path, ct, head, may, sh, st):
  match st:
    case L.Em{s, acc, ok}:
      match ok:
        case False{}:
          {==}
        case True{}:
          wl.opened_fine(~shut, ~fhead, ~miss, ~lnote, ~lsize, ms, w.fopen(s, L.text(root), L.text(path)), ct, head, may, sh, acc)

# LAW: the batch budget. After a reply of any size joins the batch,
# what stays waiting is below send.cap(): a batch at or past the cap has
# gone out.
law batch_under:
  for +k: U32
  {U32.is_lt(L.batch.keep(U32.cmp(k, L.send.cap()), k), L.send.cap()) == True{} : Bool}

# the comparison is generalised with its equation. Below the cap what
# stays is k, and the equation says k is below it; at or past it what
# stays is 0, which the checker compares with the cap.
law wl.batch_under:
  for +k: U32
  for +c: Cmp
  for e: {c == U32.cmp(k, L.send.cap()) : Cmp}
  {U32.is_lt(L.batch.keep(c, k), L.send.cap()) == True{} : Bool}

def wl.batch_under(k, c, e):
  match c:
    case LT{}:
      %e : {Cmp.is_lt(_) == True{} : Bool}
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def batch_under(k):
  wl.batch_under(k, U32.cmp(k, L.send.cap()), {==})

# LAW: the head's clock. A read that leaves no head in progress (a body,
# the next message, nothing) drops the watch, and one that leaves a head
# in progress keeps the clock it started with, so reads that each arrive
# inside the idle time never restart it.
law hw_rest:
  for +hw: L.Hw
  {L.hw.next(False{}, hw) == L.NoHead{} : L.Hw}

def hw_rest(hw):
  {==}

law hw_keeps:
  for +t0: Nat
  for +n: U32
  {L.hw.next(True{}, L.Since{t0, n}) == L.Since{t0, n} : L.Hw}

def hw_keeps(t0, n):
  {==}

# LAW: the accept loop stays up. With no stop request and every accept
# failure one of the passing set (EMFILE, ECONNABORTED, ...), the loop
# runs every turn it is given, however connections come and go.
def wl.and_l(a: Bool, b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      no({False{} == True{} : Bool}, e)

def wl.and_r(a: Bool, b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      no({b == True{} : Bool}, e)

law accept_calm:
  for k: Nat
  for +evs: List<&2, Ac>
  for +served: Nat
  for +e: {calm(evs) == True{} : Bool}
  {why.of(sim.accept(k, Lw{evs, False{}, served})) == L.Spent{} : L.Why}

def accept_calm(k, evs, served, e):
  match k:
    case 0n:
      {==}
    case 1n+j:
      match evs:
        case Nil{}:
          accept_calm(j, Nil{}, served, {==})
        case Con{ev, t}:
          match ev:
            case Come{}:
              accept_calm(j, t, 1n+served, e)
            case Idle{}:
              accept_calm(j, t, served, e)
            case Term{}:
              no({why.of(sim.accept(1n+j, Lw{Con{Term{}, t}, False{}, served})) ==
                L.Spent{} : L.Why}, e)
            case Err{+code}:
              %Equal.sym(Bool, L.accept.soft(code), True{},
                wl.and_l(L.accept.soft(code), calm(t), e)) :
                {why.of(sim.acc.dead(j, Lw{t, False{}, served}, code, _)) == L.Spent{} :
                  L.Why}
              accept_calm(j, t, served, wl.and_r(L.accept.soft(code), calm(t), e))

# a loop told why it ended answers that, whatever turns it had left
law wl.some_ends:
  for j: Nat
  for l: Lw
  for +why: L.Why
  for e: {ok.end(why) == True{} : Bool}
  {ok.end(why.of(sim.acc.run(j, (l, Some{why})))) == True{} : Bool}

def wl.some_ends(j, l, why, e):
  match j:
    case 0n:
      e
    case 1n+i:
      e

law wl.err_stopped:
  for j: Nat
  for +t: List<&2, Ac>
  for +served: Nat
  for +code: U32
  for sb: Bool
  for e: {sb == L.accept.soft(code) : Bool}
  {ok.end(why.of(sim.acc.dead(j, Lw{t, True{}, served}, code, sb))) == True{} : Bool}

def wl.err_stopped(j, t, served, code, sb, e):
  match sb:
    case True{}:
      wl.some_ends(j, Lw{t, True{}, served}, L.Asked{}, {==})
    case False{}:
      wl.some_ends(j, Lw{t, True{}, served}, L.Dead{code},
        (%e : {Bool.not(_) == True{} : Bool}
         {==}))

law wl.err_going:
  for j: Nat
  for +t: List<&2, Ac>
  for +served: Nat
  for +code: U32
  for sb: Bool
  for e: {sb == L.accept.soft(code) : Bool}
  for ih: {ok.end(why.of(sim.accept(j, Lw{t, False{}, served}))) == True{} : Bool}
  {ok.end(why.of(sim.acc.dead(j, Lw{t, False{}, served}, code, sb))) == True{} : Bool}

def wl.err_going(j, t, served, code, sb, e, ih):
  match sb:
    case True{}:
      ih
    case False{}:
      wl.some_ends(j, Lw{t, False{}, served}, L.Dead{code},
        (%e : {Bool.not(_) == True{} : Bool}
         {==}))

# LAW: ... and ends only as it may: its turns spent, a stop asked, or a
# failure outside the passing set, a listener that is no longer one.
# The model lets accept fail with any code at any time, so this assumes
# nothing of accept_poll's own sorting of them.
law accept_ends:
  for +k: Nat
  for sp: Bool
  for +evs: List<&2, Ac>
  for +served: Nat
  {ok.end(why.of(sim.accept(k, Lw{evs, sp, served}))) == True{} : Bool}

def accept_ends(k, sp, evs, served):
  match k:
    case 0n:
      {==}
    case 1n+j:
      match sp evs:
        case True{} Nil{}:
          wl.some_ends(j, Lw{Nil{}, True{}, served}, L.Asked{}, {==})
        case True{} Con{Come{}, t}:
          wl.some_ends(j, Lw{t, True{}, 1n+served}, L.Asked{}, {==})
        case True{} Con{Idle{}, t}:
          wl.some_ends(j, Lw{t, True{}, served}, L.Asked{}, {==})
        case True{} Con{Term{}, t}:
          wl.some_ends(j, Lw{t, True{}, served}, L.Asked{}, {==})
        case True{} Con{Err{+code}, t}:
          wl.err_stopped(j, t, served, code, L.accept.soft(code), {==})
        case False{} Nil{}:
          accept_ends(j, False{}, Nil{}, served)
        case False{} Con{Come{}, t}:
          accept_ends(j, False{}, t, 1n+served)
        case False{} Con{Idle{}, t}:
          accept_ends(j, False{}, t, served)
        case False{} Con{Term{}, t}:
          wl.some_ends(j, Lw{t, True{}, served}, L.Asked{}, {==})
        case False{} Con{Err{+code}, t}:
          wl.err_going(j, t, served, code, L.accept.soft(code), {==},
            accept_ends(j, False{}, t, served))

# LAW: reply order. At a peer that takes what it is sent, the replies
# go out byte for byte, in the order of their segments, after whatever
# the peer already had, and the send succeeds. (For segments that are
# not files; a file's bytes are the file's.)
def wl.app_nil(+a: Bytes()) -> {Bytes.append(a, "") == a : Bytes()}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.cong(Bytes(), Bytes(), x => SCon{h, x}, Bytes.append(t, ""), t, wl.app_nil(t))

def wl.app_assoc(+a: Bytes(), +b: Bytes(), +c: Bytes()) ->
  {Bytes.append(Bytes.append(a, b), c) == Bytes.append(a, Bytes.append(b, c)) : Bytes()}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.cong(Bytes(), Bytes(), x => SCon{h, x}, Bytes.append(Bytes.append(t, b), c),
        Bytes.append(t, Bytes.append(b, c)), wl.app_assoc(t, b, c))

# a send to a peer that takes everything puts the whole buffer on the
# wire after what was there, and succeeds
law wl.tx_eager:
  for +rd: List<&2, Rd>
  for +now: Nat
  for +fs: List<&2, Fil>
  for +out: Bytes()
  for +a: Bytes()
  for +ms: U32
  {w.tx(eager(rd, now, fs, out), a, ms) == sent(rd, now, fs, Bytes.append(out, a)) :
    L.Put(World)}

def wl.tx_eager(rd, now, fs, out, a, ms):
  match a:
    case SNil{}:
      %Equal.sym(Bytes(), Bytes.append(out, ""), out, wl.app_nil(out)) :
        {sent(rd, now, fs, out) == sent(rd, now, fs, _) : L.Put(World)}
      {==}
    case SCon{h, t}:
      {==}

law wl.note_is:
  for ~lnote: Bytes() -> Bytes() -> String
  for may: Maybe<&2, Bytes()>
  for +x: Bytes()
  {sim.note(~lnote, may, x) == x : Bytes()}

def wl.note_is(lnote, may, x):
  match may:
    case None{}:
      {==}
    case Some{n}:
      {==}

law wl.held_eager:
  for ~shut: Bool -> Bytes() -> Bytes()
  for ~fhead: List<&2, U32> -> U32 -> Bytes()
  for ~miss: Bool -> Bytes()
  for ~lnote: Bytes() -> Bytes() -> String
  for ~lsize: Bytes() -> Bytes() -> U32 -> String
  for +t: List<&2, L.Seg>
  for +ms: U32
  for +rd: List<&2, Rd>
  for +now: Nat
  for +fs: List<&2, Fil>
  for +out: Bytes()
  for +a: Bytes()
  for c: Cmp
  for ih1: {sim.go(~shut, ~fhead, ~miss, ~lnote, ~lsize, t, ms, None{}, False{}, L.Em{eager(rd, now, fs, out), a, True{}}) ==
    sent(rd, now, fs, Bytes.append(out, Bytes.append(a, wire(~shut, t, False{})))) :
    L.Put(World)}
  for ih2: {sim.go(~shut, ~fhead, ~miss, ~lnote, ~lsize, t, ms, None{}, False{},
    L.Em{eager(rd, now, fs, Bytes.append(out, a)), "", True{}}) ==
    sent(rd, now, fs, Bytes.append(Bytes.append(out, a), wire(~shut, t, False{}))) :
    L.Put(World)}
  {sim.go(~shut, ~fhead, ~miss, ~lnote, ~lsize, t, ms, None{}, False{}, sim.held(ms, eager(rd, now, fs, out), a, c)) ==
    sent(rd, now, fs, Bytes.append(out, Bytes.append(a, wire(~shut, t, False{})))) :
    L.Put(World)}

def wl.held_eager(shut, fhead, miss, lnote, lsize, t, ms, rd, now, fs, out, a, c, ih1, ih2):
  match c:
    case LT{}:
      ih1
    case EQ{}:
      %Equal.sym(L.Put(World), w.tx(eager(rd, now, fs, out), a, ms),
        sent(rd, now, fs, Bytes.append(out, a)), wl.tx_eager(rd, now, fs, out, a, ms)) :
        {sim.go(~shut, ~fhead, ~miss, ~lnote, ~lsize, t, ms, None{}, False{}, sim.flushed(_)) ==
          sent(rd, now, fs, Bytes.append(out, Bytes.append(a, wire(~shut, t, False{})))) :
          L.Put(World)}
      Equal.trans(L.Put(World),
        sim.go(~shut, ~fhead, ~miss, ~lnote, ~lsize, t, ms, None{}, False{}, L.Em{eager(rd, now, fs, Bytes.append(out, a)), "", True{}}),
        sent(rd, now, fs, Bytes.append(Bytes.append(out, a), wire(~shut, t, False{}))),
        sent(rd, now, fs, Bytes.append(out, Bytes.append(a, wire(~shut, t, False{})))),
        ih2,
        Equal.cong(Bytes(), L.Put(World), o => sent(rd, now, fs, o),
          Bytes.append(Bytes.append(out, a), wire(~shut, t, False{})),
          Bytes.append(out, Bytes.append(a, wire(~shut, t, False{}))),
          wl.app_assoc(out, a, wire(~shut, t, False{}))))
    case GT{}:
      %Equal.sym(L.Put(World), w.tx(eager(rd, now, fs, out), a, ms),
        sent(rd, now, fs, Bytes.append(out, a)), wl.tx_eager(rd, now, fs, out, a, ms)) :
        {sim.go(~shut, ~fhead, ~miss, ~lnote, ~lsize, t, ms, None{}, False{}, sim.flushed(_)) ==
          sent(rd, now, fs, Bytes.append(out, Bytes.append(a, wire(~shut, t, False{})))) :
          L.Put(World)}
      Equal.trans(L.Put(World),
        sim.go(~shut, ~fhead, ~miss, ~lnote, ~lsize, t, ms, None{}, False{}, L.Em{eager(rd, now, fs, Bytes.append(out, a)), "", True{}}),
        sent(rd, now, fs, Bytes.append(Bytes.append(out, a), wire(~shut, t, False{}))),
        sent(rd, now, fs, Bytes.append(out, Bytes.append(a, wire(~shut, t, False{})))),
        ih2,
        Equal.cong(Bytes(), L.Put(World), o => sent(rd, now, fs, o),
          Bytes.append(Bytes.append(out, a), wire(~shut, t, False{})),
          Bytes.append(out, Bytes.append(a, wire(~shut, t, False{}))),
          wl.app_assoc(out, a, wire(~shut, t, False{}))))

law wl.go_wire:
  for ~shut: Bool -> Bytes() -> Bytes()
  for ~fhead: List<&2, U32> -> U32 -> Bytes()
  for ~miss: Bool -> Bytes()
  for ~lnote: Bytes() -> Bytes() -> String
  for ~lsize: Bytes() -> Bytes() -> U32 -> String
  for +xs: List<&2, L.Seg>
  for +ms: U32
  for may: Maybe<&2, Bytes()>
  for +sh: Bool
  for +rd: List<&2, Rd>
  for +now: Nat
  for +fs: List<&2, Fil>
  for +out: Bytes()
  for +acc: Bytes()
  for +e: {raws(xs) == True{} : Bool}
  {sim.go(~shut, ~fhead, ~miss, ~lnote, ~lsize, xs, ms, may, sh, L.Em{eager(rd, now, fs, out), acc, True{}}) ==
    sent(rd, now, fs, Bytes.append(out, Bytes.append(acc, wire(~shut, xs, sh)))) :
    L.Put(World)}

def wl.go_wire(shut, fhead, miss, lnote, lsize, xs, ms, may, sh, rd, now, fs, out, acc, e):
  match xs:
    case Nil{}:
      %Equal.sym(L.Put(World), w.tx(eager(rd, now, fs, out), acc, ms),
        sent(rd, now, fs, Bytes.append(out, acc)), wl.tx_eager(rd, now, fs, out, acc, ms)) :
        {L.send.fin(~Id, ~Id.pure, ~Id.bind, ~World, _, True{}) ==
          sent(rd, now, fs, Bytes.append(out, Bytes.append(acc, ""))) : L.Put(World)}
      %Equal.sym(Bytes(), Bytes.append(acc, ""), acc, wl.app_nil(acc)) :
        {sent(rd, now, fs, Bytes.append(out, acc)) ==
          sent(rd, now, fs, Bytes.append(out, _)) : L.Put(World)}
      {==}
    case Con{+g, +t}:
      match g:
        case L.Raw{+bs}:
          %Equal.sym(Bytes(), sim.note(~lnote, may, shut(sh, bs)), shut(sh, bs),
            wl.note_is(~lnote, may, shut(sh, bs))) :
            {sim.go(~shut, ~fhead, ~miss, ~lnote, ~lsize, t, ms, None{}, False{},
              sim.hold(ms, eager(rd, now, fs, out), Bytes.append(acc, _))) ==
              sent(rd, now, fs, Bytes.append(out, Bytes.append(acc,
                Bytes.append(shut(sh, bs), wire(~shut, t, False{}))))) : L.Put(World)}
          Equal.trans(L.Put(World),
            sim.go(~shut, ~fhead, ~miss, ~lnote, ~lsize, t, ms, None{}, False{},
              sim.hold(ms, eager(rd, now, fs, out), Bytes.append(acc, shut(sh, bs)))),
            sent(rd, now, fs, Bytes.append(out, Bytes.append(Bytes.append(acc, shut(sh, bs)),
              wire(~shut, t, False{})))),
            sent(rd, now, fs, Bytes.append(out, Bytes.append(acc,
              Bytes.append(shut(sh, bs), wire(~shut, t, False{}))))),
            wl.held_eager(~shut, ~fhead, ~miss, ~lnote, ~lsize, t, ms, rd, now, fs, out, Bytes.append(acc, shut(sh, bs)),
              U32.cmp(U32.from_nat(Bytes.len(Bytes.append(acc, shut(sh, bs)))),
                L.send.cap()),
              wl.go_wire(~shut, ~fhead, ~miss, ~lnote, ~lsize, t, ms, None{}, False{}, rd, now, fs, out,
                Bytes.append(acc, shut(sh, bs)), e),
              wl.go_wire(~shut, ~fhead, ~miss, ~lnote, ~lsize, t, ms, None{}, False{}, rd, now, fs,
                Bytes.append(out, Bytes.append(acc, shut(sh, bs))), "", e)),
            Equal.cong(Bytes(), L.Put(World), o => sent(rd, now, fs, Bytes.append(out, o)),
              Bytes.append(Bytes.append(acc, shut(sh, bs)), wire(~shut, t, False{})),
              Bytes.append(acc, Bytes.append(shut(sh, bs), wire(~shut, t, False{}))),
              wl.app_assoc(acc, shut(sh, bs), wire(~shut, t, False{}))))
        case L.Note{bs}:
          wl.go_wire(~shut, ~fhead, ~miss, ~lnote, ~lsize, t, ms, Some{bs}, sh, rd, now, fs, out, acc, e)
        case L.Shut{}:
          wl.go_wire(~shut, ~fhead, ~miss, ~lnote, ~lsize, t, ms, may, True{}, rd, now, fs, out, acc, e)
        case L.Page{root, path, ct, head}:
          no({sim.go(~shut, ~fhead, ~miss, ~lnote, ~lsize, Con{L.Page{root, path, ct, head}, t}, ms, may, sh,
            L.Em{eager(rd, now, fs, out), acc, True{}}) ==
            sent(rd, now, fs, Bytes.append(out, Bytes.append(acc,
              wire(~shut, Con{L.Page{root, path, ct, head}, t}, sh)))) : L.Put(World)}, e)

law segs_wire:
  for ~shut: Bool -> Bytes() -> Bytes()
  for ~fhead: List<&2, U32> -> U32 -> Bytes()
  for ~miss: Bool -> Bytes()
  for ~lnote: Bytes() -> Bytes() -> String
  for ~lsize: Bytes() -> Bytes() -> U32 -> String
  for +xs: List<&2, L.Seg>
  for +ms: U32
  for +rd: List<&2, Rd>
  for +now: Nat
  for +fs: List<&2, Fil>
  for +out: Bytes()
  for +e: {raws(xs) == True{} : Bool}
  {sim.segs(~shut, ~fhead, ~miss, ~lnote, ~lsize, eager(rd, now, fs, out), xs, ms) ==
    sent(rd, now, fs, Bytes.append(out, wire(~shut, xs, False{}))) : L.Put(World)}

def segs_wire(shut, fhead, miss, lnote, lsize, xs, ms, rd, now, fs, out, e):
  wl.go_wire(~shut, ~fhead, ~miss, ~lnote, ~lsize, xs, ms, None{}, False{}, rd, now, fs, out, "", e)

# LAW: liveness under stall. At a peer that has stopped -- every read
# waits out its time (idle or head) and gets nothing, every send that
# has bytes to move waits out its time and fails -- the connection ends
# within three turns from any state the loop can be in: fuel past three
# changes nothing. The protocol's obligation: an event of a stream,
# framed, is never empty, so its send to a stopped peer fails.

# a turn at a stopped peer ends the connection: one more turn of fuel
# does nothing more
law wl.mute_left:
  for ~E: Data
  for ~P: Data
  for ~U: Data
  for ~idle: E -> U32
  for ~hdms: E -> U32
  for ~plan: E -> Bytes() -> P -> L.Plan<P, U>
  for ~mid: P -> Bool
  for ~big: Bytes()
  for ~uplan: U -> Bytes() -> L.Plan<P, U>
  for ~gap: U32
  for ~event: U32 -> Bytes()
  for ~shut: Bool -> Bytes() -> Bytes()
  for ~fhead: List<&2, U32> -> U32 -> Bytes()
  for ~miss: Bool -> Bytes()
  for ~lnote: Bytes() -> Bytes() -> String
  for ~lsize: Bytes() -> Bytes() -> U32 -> String
  for +srv: E
  for s: World
  for p: P
  for t0: Nat
  for n: U32
  for +el: Nat
  for ok: Bool
  for g: Nat
  for v: Nat
  {mute.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 1n+g, srv, mute.left(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~big, srv, s, p, t0, n, el, ok), v) ==
    mute.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 1n, srv, mute.left(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~big, srv, s, p, t0, n, el, ok), v) : World}

def wl.mute_left(E, P, U, idle, hdms, plan, mid, big, uplan, gap, event, shut, fhead, miss, lnote, lsize, srv, s, p, t0, n, el, ok, g, v):
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

law wl.mute_turn_h:
  for ~E: Data
  for ~P: Data
  for ~U: Data
  for ~idle: E -> U32
  for ~hdms: E -> U32
  for ~plan: E -> Bytes() -> P -> L.Plan<P, U>
  for ~mid: P -> Bool
  for ~big: Bytes()
  for ~uplan: U -> Bytes() -> L.Plan<P, U>
  for ~gap: U32
  for ~event: U32 -> Bytes()
  for ~shut: Bool -> Bytes() -> Bytes()
  for ~fhead: List<&2, U32> -> U32 -> Bytes()
  for ~miss: Bool -> Bytes()
  for ~lnote: Bytes() -> Bytes() -> String
  for ~lsize: Bytes() -> Bytes() -> U32 -> String
  for +srv: E
  for +s: World
  for p: P
  for hw: L.Hw
  for g: Nat
  for v: Nat
  {mute.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 1n+g, srv, mute.turn.h(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~big, srv, s, p, hw), v) ==
    mute.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 1n, srv, mute.turn.h(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~big, srv, s, p, hw), v) : World}

def wl.mute_turn_h(E, P, U, idle, hdms, plan, mid, big, uplan, gap, event, shut, fhead, miss, lnote, lsize, srv, s, p, hw, g, v):
  match hw:
    case L.NoHead{}:
      {==}
    case L.Begun{}:
      wl.mute_left(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, srv, s, p, w.now(s), 0, Nat.sub(w.now(s), w.now(s)),
        Nat.is_lt(Nat.sub(w.now(s), w.now(s)), U32.to_nat(hdms(srv))), g, v)
    case L.Since{+t0, n}:
      wl.mute_left(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, srv, s, p, t0, n, Nat.sub(w.now(s), t0),
        Nat.is_lt(Nat.sub(w.now(s), t0), U32.to_nat(hdms(srv))), g, v)

law wl.mute_turn:
  for ~E: Data
  for ~P: Data
  for ~U: Data
  for ~idle: E -> U32
  for ~hdms: E -> U32
  for ~plan: E -> Bytes() -> P -> L.Plan<P, U>
  for ~mid: P -> Bool
  for ~big: Bytes()
  for ~uplan: U -> Bytes() -> L.Plan<P, U>
  for ~gap: U32
  for ~event: U32 -> Bytes()
  for ~shut: Bool -> Bytes() -> Bytes()
  for ~fhead: List<&2, U32> -> U32 -> Bytes()
  for ~miss: Bool -> Bytes()
  for ~lnote: Bytes() -> Bytes() -> String
  for ~lsize: Bytes() -> Bytes() -> U32 -> String
  for +srv: E
  for m: L.Put(World)
  for p: P
  for hw: L.Hw
  for g: Nat
  for v: Nat
  {mute.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 1n+g, srv, mute.turn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~big, srv, m, p, hw), v) ==
    mute.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 1n, srv, mute.turn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~big, srv, m, p, hw), v) : World}

def wl.mute_turn(E, P, U, idle, hdms, plan, mid, big, uplan, gap, event, shut, fhead, miss, lnote, lsize, srv, m, p, hw, g, v):
  (s, r) = m
  match r:
    case Fail{e}:
      {==}
    case Done{u}:
      wl.mute_turn_h(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, srv, s, p, hw, g, v)

law wl.mute_up:
  for ~E: Data
  for ~P: Data
  for ~U: Data
  for ~idle: E -> U32
  for ~hdms: E -> U32
  for ~plan: E -> Bytes() -> P -> L.Plan<P, U>
  for ~mid: P -> Bool
  for ~big: Bytes()
  for ~uplan: U -> Bytes() -> L.Plan<P, U>
  for ~gap: U32
  for ~event: U32 -> Bytes()
  for ~shut: Bool -> Bytes() -> Bytes()
  for ~fhead: List<&2, U32> -> U32 -> Bytes()
  for ~miss: Bool -> Bytes()
  for ~lnote: Bytes() -> Bytes() -> String
  for ~lsize: Bytes() -> Bytes() -> U32 -> String
  for +srv: E
  for m: L.Put(World)
  for wr: U
  for g: Nat
  for v: Nat
  {mute.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 1n+g, srv, (mute.turn.up(~E, ~P, ~U, ~idle, ~uplan, srv, m, wr), L.NoHead{}), v) ==
    mute.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 1n, srv, (mute.turn.up(~E, ~P, ~U, ~idle, ~uplan, srv, m, wr), L.NoHead{}), v) : World}

def wl.mute_up(E, P, U, idle, hdms, plan, mid, big, uplan, gap, event, shut, fhead, miss, lnote, lsize, srv, m, wr, g, v):
  (s, r) = m
  match r:
    case Fail{e}:
      {==}
    case Done{u}:
      {==}

# a send of bytes to a stopped peer fails; of none, succeeds
law wl.mute_held:
  for ~shut: Bool -> Bytes() -> Bytes()
  for ~fhead: List<&2, U32> -> U32 -> Bytes()
  for ~miss: Bool -> Bytes()
  for ~lnote: Bytes() -> Bytes() -> String
  for ~lsize: Bytes() -> Bytes() -> U32 -> String
  for +ms: U32
  for s: World
  for h: Char
  for t: Bytes()
  for c: Cmp
  {put.done(mute.go(~shut, ~fhead, ~miss, ~lnote, ~lsize, Nil{}, ms, None{}, False{}, mute.held(ms, s, SCon{h, t}, c))) ==
    False{} : Bool}

def wl.mute_held(shut, fhead, miss, lnote, lsize, ms, s, h, t, c):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# (the bytes a Raw puts out are the protocol's shut of them)
law wl.mute_raw.at:
  for ~shut: Bool -> Bytes() -> Bytes()
  for ~fhead: List<&2, U32> -> U32 -> Bytes()
  for ~miss: Bool -> Bytes()
  for ~lnote: Bytes() -> Bytes() -> String
  for ~lsize: Bytes() -> Bytes() -> U32 -> String
  for +ms: U32
  for s: World
  for +x: Bytes()
  {put.done(mute.go(~shut, ~fhead, ~miss, ~lnote, ~lsize, Nil{}, ms, None{}, False{}, mute.held(ms, s, Bytes.append("", x),
    U32.cmp(U32.from_nat(Bytes.len(Bytes.append("", x))), L.send.cap())))) == empty(x) : Bool}

def wl.mute_raw.at(shut, fhead, miss, lnote, lsize, ms, s, x):
  match x:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      wl.mute_held(~shut, ~fhead, ~miss, ~lnote, ~lsize, ms, s, h, t, U32.cmp(U32.from_nat(Bytes.len(SCon{h, t})), L.send.cap()))

law wl.mute_raw:
  for ~shut: Bool -> Bytes() -> Bytes()
  for ~fhead: List<&2, U32> -> U32 -> Bytes()
  for ~miss: Bool -> Bytes()
  for ~lnote: Bytes() -> Bytes() -> String
  for ~lsize: Bytes() -> Bytes() -> U32 -> String
  for +ms: U32
  for s: World
  for +bs: Bytes()
  {put.done(mute.segs(~shut, ~fhead, ~miss, ~lnote, ~lsize, s, [L.Raw{bs}], ms)) == empty(shut(False{}, bs)) : Bool}

def wl.mute_raw(shut, fhead, miss, lnote, lsize, ms, s, bs):
  wl.mute_raw.at(~shut, ~fhead, ~miss, ~lnote, ~lsize, ms, s, shut(False{}, bs))

law wl.mute_tick_failed:
  for ~E: Data
  for ~P: Data
  for ~U: Data
  for ~idle: E -> U32
  for ~hdms: E -> U32
  for ~plan: E -> Bytes() -> P -> L.Plan<P, U>
  for ~mid: P -> Bool
  for ~big: Bytes()
  for ~uplan: U -> Bytes() -> L.Plan<P, U>
  for ~gap: U32
  for ~event: U32 -> Bytes()
  for ~shut: Bool -> Bytes() -> Bytes()
  for ~fhead: List<&2, U32> -> U32 -> Bytes()
  for ~miss: Bool -> Bytes()
  for ~lnote: Bytes() -> Bytes() -> String
  for ~lsize: Bytes() -> Bytes() -> U32 -> String
  for +srv: E
  for m: L.Put(World)
  for n: U32
  for g: Nat
  for v: Nat
  for e: {put.done(m) == False{} : Bool}
  {mute.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 1n+g, srv, (mute.tick(~P, ~U, ~gap, ~event, m, n), L.NoHead{}), v) ==
    mute.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 1n, srv, (mute.tick(~P, ~U, ~gap, ~event, m, n), L.NoHead{}), v) : World}

def wl.mute_tick_failed(E, P, U, idle, hdms, plan, mid, big, uplan, gap, event, shut, fhead, miss, lnote, lsize, srv, m, n, g, v, e):
  (s, r) = m
  match r:
    case Fail{x}:
      {==}
    case Done{u}:
      no({mute.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 1n+g, srv, (mute.tick(~P, ~U, ~gap, ~event, (s, Done{u}), n), L.NoHead{}), v) ==
        mute.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 1n, srv, (mute.tick(~P, ~U, ~gap, ~event, (s, Done{u}), n), L.NoHead{}), v) : World},
        Equal.sym(Bool, True{}, False{}, e))

law wl.mute_more:
  for ~E: Data
  for ~P: Data
  for ~U: Data
  for ~idle: E -> U32
  for ~hdms: E -> U32
  for ~plan: E -> Bytes() -> P -> L.Plan<P, U>
  for ~mid: P -> Bool
  for ~big: Bytes()
  for ~uplan: U -> Bytes() -> L.Plan<P, U>
  for ~gap: U32
  for ~event: U32 -> Bytes()
  for ~shut: Bool -> Bytes() -> Bytes()
  for ~fhead: List<&2, U32> -> U32 -> Bytes()
  for ~miss: Bool -> Bytes()
  for ~lnote: Bytes() -> Bytes() -> String
  for ~lsize: Bytes() -> Bytes() -> U32 -> String
  for ~event_ok: @+n: U32 -> {empty(shut(False{}, event(n))) == False{} : Bool}
  for +srv: E
  for +s: World
  for +n: U32
  for z: Bool
  for g: Nat
  for v: Nat
  {mute.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 1n+1n+g, srv, (L.plan.more(~P, ~U, ~event, World, s, n, z), L.NoHead{}), v) ==
    mute.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 1n+1n, srv, (L.plan.more(~P, ~U, ~event, World, s, n, z), L.NoHead{}), v) :
    World}

def wl.mute_more(E, P, U, idle, hdms, plan, mid, big, uplan, gap, event, shut, fhead, miss, lnote, lsize, event_ok, srv, s, n, z, g, v):
  match z:
    case True{}:
      {==}
    case False{}:
      wl.mute_tick_failed(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, srv, mute.segs(~shut, ~fhead, ~miss, ~lnote, ~lsize, s, [L.Raw{event(n)}], idle(srv)),
        (n - 1 : U32), g, L.conn.waits(),
        Equal.trans(Bool, put.done(mute.segs(~shut, ~fhead, ~miss, ~lnote, ~lsize, s, [L.Raw{event(n)}], idle(srv))),
          empty(shut(False{}, event(n))), False{},
          wl.mute_raw(~shut, ~fhead, ~miss, ~lnote, ~lsize, idle(srv), s, event(n)), event_ok(n)))

law wl.mute_tick:
  for ~E: Data
  for ~P: Data
  for ~U: Data
  for ~idle: E -> U32
  for ~hdms: E -> U32
  for ~plan: E -> Bytes() -> P -> L.Plan<P, U>
  for ~mid: P -> Bool
  for ~big: Bytes()
  for ~uplan: U -> Bytes() -> L.Plan<P, U>
  for ~gap: U32
  for ~event: U32 -> Bytes()
  for ~shut: Bool -> Bytes() -> Bytes()
  for ~fhead: List<&2, U32> -> U32 -> Bytes()
  for ~miss: Bool -> Bytes()
  for ~lnote: Bytes() -> Bytes() -> String
  for ~lsize: Bytes() -> Bytes() -> U32 -> String
  for ~event_ok: @+n: U32 -> {empty(shut(False{}, event(n))) == False{} : Bool}
  for +srv: E
  for m: L.Put(World)
  for +n: U32
  for g: Nat
  for v: Nat
  {mute.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 1n+1n+g, srv, (mute.tick(~P, ~U, ~gap, ~event, m, n), L.NoHead{}), v) ==
    mute.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 1n+1n, srv, (mute.tick(~P, ~U, ~gap, ~event, m, n), L.NoHead{}), v) : World}

def wl.mute_tick(E, P, U, idle, hdms, plan, mid, big, uplan, gap, event, shut, fhead, miss, lnote, lsize, event_ok, srv, m, n, g, v):
  (s, r) = m
  match r:
    case Fail{e}:
      {==}
    case Done{u}:
      wl.mute_more(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, ~event_ok, srv, s, n, U32.is_zero(n), g, v)

law stall_ends:
  for ~E: Data
  for ~P: Data
  for ~U: Data
  for ~idle: E -> U32
  for ~hdms: E -> U32
  for ~plan: E -> Bytes() -> P -> L.Plan<P, U>
  for ~mid: P -> Bool
  for ~big: Bytes()
  for ~uplan: U -> Bytes() -> L.Plan<P, U>
  for ~gap: U32
  for ~event: U32 -> Bytes()
  for ~shut: Bool -> Bytes() -> Bytes()
  for ~fhead: List<&2, U32> -> U32 -> Bytes()
  for ~miss: Bool -> Bytes()
  for ~lnote: Bytes() -> Bytes() -> String
  for ~lsize: Bytes() -> Bytes() -> U32 -> String
  for ~event_ok: @+n: U32 -> {empty(shut(False{}, event(n))) == False{} : Bool}
  for +srv: E
  for +w: World
  for pl: L.Plan<P, U>
  for +hw: L.Hw
  for +g: Nat
  for +v: Nat
  {mute.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 1n+1n+1n+g, srv, ((w, pl), hw), v) ==
    mute.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 1n+1n+1n, srv, ((w, pl), hw), v) : World}

def stall_ends(E, P, U, idle, hdms, plan, mid, big, uplan, gap, event, shut, fhead, miss, lnote, lsize, event_ok, srv, w, pl, hw, g, v):
  match pl:
    case L.Stop{}:
      {==}
    case L.End{out}:
      {==}
    case L.Go{+out, +p2}:
      Equal.trans(World,
        mute.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 1n+1n+g, srv, mute.turn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~big, srv, mute.segs(~shut, ~fhead, ~miss, ~lnote, ~lsize, w, out, idle(srv)), p2,
          L.hw.next(mid(p2), L.NoHead{})), L.conn.waits()),
        mute.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 1n, srv, mute.turn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~big, srv, mute.segs(~shut, ~fhead, ~miss, ~lnote, ~lsize, w, out, idle(srv)), p2,
          L.hw.next(mid(p2), L.NoHead{})), L.conn.waits()),
        mute.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 1n+1n, srv, mute.turn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~big, srv, mute.segs(~shut, ~fhead, ~miss, ~lnote, ~lsize, w, out, idle(srv)), p2,
          L.hw.next(mid(p2), L.NoHead{})), L.conn.waits()),
        wl.mute_turn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, srv, mute.segs(~shut, ~fhead, ~miss, ~lnote, ~lsize, w, out, idle(srv)), p2,
          L.hw.next(mid(p2), L.NoHead{}), 1n+g, L.conn.waits()),
        Equal.sym(World,
          mute.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 1n+1n, srv, mute.turn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~big, srv, mute.segs(~shut, ~fhead, ~miss, ~lnote, ~lsize, w, out, idle(srv)), p2,
            L.hw.next(mid(p2), L.NoHead{})), L.conn.waits()),
          mute.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 1n, srv, mute.turn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~big, srv, mute.segs(~shut, ~fhead, ~miss, ~lnote, ~lsize, w, out, idle(srv)), p2,
            L.hw.next(mid(p2), L.NoHead{})), L.conn.waits()),
          wl.mute_turn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, srv, mute.segs(~shut, ~fhead, ~miss, ~lnote, ~lsize, w, out, idle(srv)), p2,
            L.hw.next(mid(p2), L.NoHead{}), 1n, L.conn.waits())))
    case L.Wait{+p2}:
      match v:
        case 0n:
          {==}
        case 1n+u:
          Equal.trans(World,
            mute.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 1n+1n+g, srv, mute.turn.h(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~big, srv, w, p2, L.hw.next(mid(p2), hw)), u),
            mute.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 1n, srv, mute.turn.h(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~big, srv, w, p2, L.hw.next(mid(p2), hw)), u),
            mute.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 1n+1n, srv, mute.turn.h(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~big, srv, w, p2, L.hw.next(mid(p2), hw)), u),
            wl.mute_turn_h(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, srv, w, p2, L.hw.next(mid(p2), hw), 1n+g, u),
            Equal.sym(World,
              mute.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 1n+1n, srv, mute.turn.h(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~big, srv, w, p2, L.hw.next(mid(p2), hw)), u),
              mute.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 1n, srv, mute.turn.h(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~big, srv, w, p2, L.hw.next(mid(p2), hw)), u),
              wl.mute_turn_h(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, srv, w, p2, L.hw.next(mid(p2), hw), 1n, u)))
    case L.Feed{+out, +n}:
      wl.mute_tick(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, ~event_ok, srv, mute.segs(~shut, ~fhead, ~miss, ~lnote, ~lsize, w, out, idle(srv)), n, g, L.conn.waits())
    case L.Sock{+out, +wr}:
      Equal.trans(World,
        mute.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 1n+1n+g, srv, (mute.turn.up(~E, ~P, ~U, ~idle, ~uplan, srv, mute.segs(~shut, ~fhead, ~miss, ~lnote, ~lsize, w, out, idle(srv)), wr),
          L.NoHead{}), L.conn.waits()),
        mute.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 1n, srv, (mute.turn.up(~E, ~P, ~U, ~idle, ~uplan, srv, mute.segs(~shut, ~fhead, ~miss, ~lnote, ~lsize, w, out, idle(srv)), wr),
          L.NoHead{}), L.conn.waits()),
        mute.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 1n+1n, srv, (mute.turn.up(~E, ~P, ~U, ~idle, ~uplan, srv, mute.segs(~shut, ~fhead, ~miss, ~lnote, ~lsize, w, out, idle(srv)), wr),
          L.NoHead{}), L.conn.waits()),
        wl.mute_up(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, srv, mute.segs(~shut, ~fhead, ~miss, ~lnote, ~lsize, w, out, idle(srv)), wr, 1n+g, L.conn.waits()),
        Equal.sym(World,
          mute.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 1n+1n, srv, (mute.turn.up(~E, ~P, ~U, ~idle, ~uplan, srv, mute.segs(~shut, ~fhead, ~miss, ~lnote, ~lsize, w, out, idle(srv)), wr),
            L.NoHead{}), L.conn.waits()),
          mute.conn(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, 1n, srv, (mute.turn.up(~E, ~P, ~U, ~idle, ~uplan, srv, mute.segs(~shut, ~fhead, ~miss, ~lnote, ~lsize, w, out, idle(srv)), wr),
            L.NoHead{}), L.conn.waits()),
          wl.mute_up(~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, srv, mute.segs(~shut, ~fhead, ~miss, ~lnote, ~lsize, w, out, idle(srv)), wr, 1n, L.conn.waits())))
    case L.Hold{wr}:
      match v:
        case 0n:
          {==}
        case 1n+u:
          {==}

# the default event (L.no.event) keeps stall_ends' obligation
law no.event_ok:
  for +n: U32
  {empty(L.no.shut(False{}, L.no.event(n))) == False{} : Bool}

def no.event_ok(n):
  {==}

# LAW: the model keeps the contracts it assumes. A read answers nothing
# only after its time, and bytes (no more than asked, when the peer's
# fit) within it; a send to a peer that has stopped reading fails with
# ETIMEDOUT after its time, and one to a peer that reads succeeds; a
# file read takes no more than it asked for.
def wl.sub_add(+a: Nat, +b: Nat) -> {Nat.sub(Nat.add(a, b), a) == b : Nat}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+p:
      wl.sub_add(p, b)

def wl.le_refl(+n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      wl.le_refl(p)

def wl.lt_le(+a: Nat, +b: Nat, e: {Nat.is_lt(a, b) == True{} : Bool}) ->
  {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      no({True{} == True{} : Bool}, e)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      no({False{} == True{} : Bool}, e)
    case 1n+p 1n+q:
      wl.lt_le(p, q, e)

# a read that waited out its time: took exactly ms
def wl.waited(+now: Nat, +ms: U32) ->
  {Nat.is_le(U32.to_nat(ms), Nat.sub(Nat.add(now, U32.to_nat(ms)), now)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.sub(Nat.add(now, U32.to_nat(ms)), now), U32.to_nat(ms),
    wl.sub_add(now, U32.to_nat(ms))) :
    {Nat.is_le(U32.to_nat(ms), _) == True{} : Bool}
  wl.le_refl(U32.to_nat(ms))

law wl.give_model:
  for +t: List<&2, Rd>
  for +wait: Nat
  for +bs: Bytes()
  for +ms: U32
  for +wr: List<&2, Wr>
  for +eager: Bool
  for +now: Nat
  for +fs: List<&2, Fil>
  for +out: Bytes()
  for +max: U32
  for soon: Bool
  for es: {soon == Nat.is_lt(wait, U32.to_nat(ms)) : Bool}
  for ef: {U32.is_le(U32.from_nat(Bytes.len(bs)), max) == True{} : Bool}
  {rx.seen(max, ms, now, w.rx.give(t, wait, bs, ms, wr, eager, now, fs, out, soon)) ==
    True{} : Bool}

def wl.give_model(t, wait, bs, ms, wr, eager, now, fs, out, max, soon, es, ef):
  match soon:
    case True{}:
      %Equal.sym(Bool, U32.is_le(U32.from_nat(Bytes.len(bs)), max), True{}, ef) :
        {_ && Nat.is_le(Nat.sub(Nat.add(now, wait), now), U32.to_nat(ms)) == True{} : Bool}
      %Equal.sym(Nat, Nat.sub(Nat.add(now, wait), now), wait, wl.sub_add(now, wait)) :
        {Nat.is_le(_, U32.to_nat(ms)) == True{} : Bool}
      wl.lt_le(wait, U32.to_nat(ms), Equal.sym(Bool, True{}, Nat.is_lt(wait, U32.to_nat(ms)), es))
    case False{}:
      wl.waited(now, ms)

law rx_model:
  for +rd: List<&2, Rd>
  for +wr: List<&2, Wr>
  for +eager: Bool
  for +now: Nat
  for +fs: List<&2, Fil>
  for +out: Bytes()
  for +max: U32
  for +ms: U32
  for e: {fits(rd, max) == True{} : Bool}
  {rx.seen(max, ms, now, w.rx(World{rd, wr, eager, now, fs, out}, max, ms)) == True{} : Bool}

def rx_model(rd, wr, eager, now, fs, out, max, ms, e):
  match rd:
    case Nil{}:
      wl.waited(now, ms)
    case Con{ev, t}:
      match ev:
        case Hush{}:
          wl.waited(now, ms)
        case Cut{code}:
          {==}
        case Give{+wait, +bs}:
          wl.give_model(t, wait, bs, ms, wr, eager, now, fs, out, max,
            Nat.is_lt(wait, U32.to_nat(ms)), {==}, e)

law tx_stalled:
  for +rd: List<&2, Rd>
  for +now: Nat
  for +fs: List<&2, Fil>
  for +out: Bytes()
  for +h: Char
  for +t: Bytes()
  for +ms: U32
  {tx.seen(ms, Stops{}, now, w.tx(World{rd, Nil{}, False{}, now, fs, out}, SCon{h, t}, ms)) ==
    True{} : Bool}

def tx_stalled(rd, now, fs, out, h, t, ms):
  wl.waited(now, ms)

law tx_served:
  for +rd: List<&2, Rd>
  for +now: Nat
  for +fs: List<&2, Fil>
  for +out: Bytes()
  for +a: Bytes()
  for +ms: U32
  {tx.seen(ms, Reads{}, now, w.tx(eager(rd, now, fs, out), a, ms)) == True{} : Bool}

def tx_served(rd, now, fs, out, a, ms):
  %Equal.sym(L.Put(World), w.tx(eager(rd, now, fs, out), a, ms),
    sent(rd, now, fs, Bytes.append(out, a)), wl.tx_eager(rd, now, fs, out, a, ms)) :
    {tx.seen(ms, Reads{}, now, _) == True{} : Bool}
  {==}

law fread_model:
  for +f: Bytes()
  for +n: Nat
  {Nat.is_le(Bytes.len(String.take(f, n)), n) == True{} : Bool}

def fread_model(f, n):
  match f n:
    case SNil{} 0n:
      {==}
    case SNil{} 1n+q:
      {==}
    case SCon{h, t} 0n:
      {==}
    case SCon{+h, +t} 1n+p:
      %Equal.sym(Nat, String.length.go(String.take(t, p), 1n),
        1n+String.length.go(String.take(t, p), 0n), Bytes.len.shift(String.take(t, p), 0n)) :
        {Nat.is_le(_, 1n+p) == True{} : Bool}
      fread_model(t, p)
