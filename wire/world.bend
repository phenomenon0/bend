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
# (rx.ok, tx.ok, lsn.ok, fopen.ok, fread.ok, fsend.ok; cx.ok and tls.ok
# for the client's connects, idle.ok for its pool's probe), the model is
# proved to keep them (rx_model, tx_stalled, tx_served, fread_model,
# fsend_model, fsend_stalled), and
# wire/conform.bend drives each real effect through the same cases and
# checks the same relations against what it observes. That is the
# bridge; what is left trusted is that the effects keep their contract
# in the cases conform.bend does not try.
import Base
import ./loop.bend as L
import ./stream.bend as Bs

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

# File.sendfile: the len bytes of the file from off, put to the peer as
# a send of them would be; a file with fewer fails with ENODATA once
# what it had is out. The file is its bytes, and a sendfile leaves it as
# it was (its position does not move).
def w.fsend.cut(whole: Bool, r: Result<&1, &1, U32 & String, Unit>) ->
  Result<&1, &1, U32 & String, Unit>:
  match whole r:
    case True{} Done{u}:
      Done{u}
    case True{} Fail{e}:
      Fail{e}
    case False{} Done{u}:
      Fail{(61, "the file ended first")}
    case False{} Fail{e}:
      Fail{e}

def w.fsend.at(m: L.Put(World), f: Bytes(), whole: Bool) ->
  World & Bytes() & Result<&1, &1, U32 & String, Unit>:
  (s, r) = m
  (s, (f, w.fsend.cut(whole, r)))

def w.fbytes(+f: Bytes(), +off: U32, +len: U32) -> Bytes():
  String.take(String.drop(f, U32.to_nat(off)), U32.to_nat(len))

def w.fsend.bs(s: World, f: Bytes(), +bs: Bytes(), +len: Nat, +ms: U32) ->
  World & Bytes() & Result<&1, &1, U32 & String, Unit>:
  w.fsend.at(w.tx(s, bs, ms), f, Nat.is_eq(Bytes.len(bs), len))

def w.fsend.go(s: World, +f: Bytes(), +off: U32, +len: U32, +ms: U32) ->
  World & Bytes() & Result<&1, &1, U32 & String, Unit>:
  w.fsend.bs(s, f, w.fbytes(f, off, len), U32.to_nat(len), ms)

def w.fsend(s: World, f: Bytes(), off: U32, len: U32, ms: U32) ->
  World & Bytes() & Result<&1, &1, U32 & String, Unit>:
  w.fsend.go(s, f, off, len, ms)

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
  ~shut: Bool -> Bytes() -> Bytes(), ~fhead: Bytes() -> U32 -> Bytes(),
  ~miss: Bool -> Bytes(), ~lnote: Bytes() -> Bytes() -> String,
  ~lsize: Bytes() -> Bytes() -> U32 -> String, +ms: U32, root: Bytes(), path: Bytes(), ct: Bytes(), head: Bool,
  may: Maybe<&2, Bytes()>, sh: Bool, st: L.Em<World>
) -> L.Em<World>:
  L.send.page(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~w.tx, ~w.say, ~w.fopen, ~w.fsize,
    ~w.fread, ~w.fsend, ~w.fclose, ~shut, ~fhead, ~miss, ~lnote, ~lsize, ms, root, path, ct, head, may, sh, st)

def sim.go(
  ~shut: Bool -> Bytes() -> Bytes(), ~fhead: Bytes() -> U32 -> Bytes(),
  ~miss: Bool -> Bytes(), ~lnote: Bytes() -> Bytes() -> String,
  ~lsize: Bytes() -> Bytes() -> U32 -> String, xs: List<&2, L.Seg>, +ms: U32, may: Maybe<&2, Bytes()>, sh: Bool, st: L.Em<World>
) -> L.Put(World):
  L.send.go(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~w.tx, ~w.say, ~w.fopen, ~w.fsize,
    ~w.fread, ~w.fsend, ~w.fclose, ~shut, ~fhead, ~miss, ~lnote, ~lsize, xs, ms, may, sh, st)

def sim.segs(~shut: Bool -> Bytes() -> Bytes(), ~fhead: Bytes() -> U32 -> Bytes(),
  ~miss: Bool -> Bytes(), ~lnote: Bytes() -> Bytes() -> String,
  ~lsize: Bytes() -> Bytes() -> U32 -> String, s: World, xs: List<&2, L.Seg>, +ms: U32) -> L.Put(World):
  L.send.segs(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~w.tx, ~w.say, ~w.fopen, ~w.fsize,
    ~w.fread, ~w.fsend, ~w.fclose, ~shut, ~fhead, ~miss, ~lnote, ~lsize, s, xs, ms)

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

def sim.miss(
  ~shut: Bool -> Bytes() -> Bytes(), ~miss: Bool -> Bytes(), ~lnote: Bytes() -> Bytes() -> String,
  +ms: U32, head: Bool, may: Maybe<&2, Bytes()>, sh: Bool, s: World, acc: Bytes()
) -> L.Em<World>:
  L.page.miss(~Id, ~Id.pure, ~Id.bind, ~World, ~w.tx, ~w.say, ~shut, ~miss, ~lnote, ms, head, may,
    sh, s, acc)

def sim.fsent(g: World & Bytes() & Result<&1, &1, U32 & String, Unit>) -> L.Em<World>:
  L.page.fsent(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~w.fclose, g)

def sim.headed(+ms: U32, f: Bytes(), n: U32, m: L.Put(World)) -> L.Em<World>:
  L.page.headed(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~w.fsend, ~w.fclose, ms, f, n, m)

def sim.read(+ms: U32, got: Bytes() & Result<&1, &1, U32 & String, Bytes()>, +n: U32, s: World,
  pre: Bytes()) -> L.Em<World>:
  L.page.read(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~w.tx, ~w.fclose, ms, got, n, s, pre)

def sim.body(+ms: U32, f: Bytes(), +n: U32, s: World, pre: Bytes(), small: Bool) -> L.Em<World>:
  L.page.body(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~w.tx, ~w.fread, ~w.fsend, ~w.fclose, ms,
    f, n, s, pre, small)

def sim.pstart(
  ~lsize: Bytes() -> Bytes() -> U32 -> String, +ms: U32, f: Bytes(), +n: U32, +hd: Bytes(),
  head: Bool, may: Maybe<&2, Bytes()>, s: World, acc: Bytes()
) -> L.Em<World>:
  L.page.start(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~w.tx, ~w.say, ~w.fread, ~w.fsend, ~w.fclose,
    ~lsize, ms, f, n, hd, head, may, s, acc)

def sim.psized(
  ~shut: Bool -> Bytes() -> Bytes(), ~fhead: Bytes() -> U32 -> Bytes(),
  ~miss: Bool -> Bytes(), ~lnote: Bytes() -> Bytes() -> String,
  ~lsize: Bytes() -> Bytes() -> U32 -> String, +ms: U32, got: Bytes() & Result<&1, &1, U32 & String, U32>, ct: Bytes(),
  head: Bool, may: Maybe<&2, Bytes()>, sh: Bool, s: World, acc: Bytes()
) -> L.Em<World>:
  L.page.sized(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~w.tx, ~w.say, ~w.fread, ~w.fsend, ~w.fclose,
    ~shut, ~fhead, ~miss, ~lnote, ~lsize, ms, got, ct, head, may, sh, s, acc)

def sim.opened(
  ~shut: Bool -> Bytes() -> Bytes(), ~fhead: Bytes() -> U32 -> Bytes(),
  ~miss: Bool -> Bytes(), ~lnote: Bytes() -> Bytes() -> String,
  ~lsize: Bytes() -> Bytes() -> U32 -> String, +ms: U32, m: World & Result<&1, &1, U32 & String, Bytes()>, ct: Bytes(),
  head: Bool, may: Maybe<&2, Bytes()>, sh: Bool, acc: Bytes()
) -> L.Em<World>:
  L.page.opened(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~w.tx, ~w.say, ~w.fsize, ~w.fread, ~w.fsend,
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
  ~shut: Bool -> Bytes() -> Bytes(), ~fhead: Bytes() -> U32 -> Bytes(),
  ~miss: Bool -> Bytes(), ~lnote: Bytes() -> Bytes() -> String,
  ~lsize: Bytes() -> Bytes() -> U32 -> String, f: Nat, +srv: E, sph: (World & L.Plan<P, U>) & L.Hw, w: Nat) -> World:
  L.conn(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~w.rx, ~w.tx, ~w.clk, ~w.nap, ~w.say,
    ~w.fopen, ~w.fsize, ~w.fread, ~w.fsend, ~w.fclose, ~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, f, srv, sph, w)

def sim.start(~E: Data, ~P: Data, ~U: Data, ~idle: E -> U32, ~hdms: E -> U32,
  ~plan: E -> Bytes() -> P -> L.Plan<P, U>, ~mid: P -> Bool, ~big: Bytes(),
  ~uplan: U -> Bytes() -> L.Plan<P, U>, ~gap: U32, ~event: U32 -> Bytes(),
  ~shut: Bool -> Bytes() -> Bytes(), ~fhead: Bytes() -> U32 -> Bytes(),
  ~miss: Bool -> Bytes(), ~lnote: Bytes() -> Bytes() -> String,
  ~lsize: Bytes() -> Bytes() -> U32 -> String, +srv: E, p0: P, s: World) -> World:
  L.conn.start(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~w.rx, ~w.tx, ~w.clk, ~w.nap,
    ~w.say, ~w.fopen, ~w.fsize, ~w.fread, ~w.fsend, ~w.fclose, ~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, srv, p0, s)

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

def m.fsend.bs(s: World, f: Bytes(), +bs: Bytes(), +len: Nat, +ms: U32) ->
  World & Bytes() & Result<&1, &1, U32 & String, Unit>:
  w.fsend.at(m.tx(s, bs, ms), f, Nat.is_eq(Bytes.len(bs), len))

def m.fsend.go(s: World, +f: Bytes(), +off: U32, +len: U32, +ms: U32) ->
  World & Bytes() & Result<&1, &1, U32 & String, Unit>:
  m.fsend.bs(s, f, w.fbytes(f, off, len), U32.to_nat(len), ms)

def m.fsend(s: World, f: Bytes(), off: U32, len: U32, ms: U32) ->
  World & Bytes() & Result<&1, &1, U32 & String, Unit>:
  m.fsend.go(s, f, off, len, ms)

def mute.conn(~E: Data, ~P: Data, ~U: Data, ~idle: E -> U32, ~hdms: E -> U32,
  ~plan: E -> Bytes() -> P -> L.Plan<P, U>, ~mid: P -> Bool, ~big: Bytes(),
  ~uplan: U -> Bytes() -> L.Plan<P, U>, ~gap: U32, ~event: U32 -> Bytes(),
  ~shut: Bool -> Bytes() -> Bytes(), ~fhead: Bytes() -> U32 -> Bytes(),
  ~miss: Bool -> Bytes(), ~lnote: Bytes() -> Bytes() -> String,
  ~lsize: Bytes() -> Bytes() -> U32 -> String, f: Nat, +srv: E, sph: (World & L.Plan<P, U>) & L.Hw, w: Nat) -> World:
  L.conn(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~m.rx, ~m.tx, ~w.clk, ~m.nap, ~w.say,
    ~w.fopen, ~w.fsize, ~w.fread, ~m.fsend, ~w.fclose, ~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, f, srv, sph, w)

def mute.turn(~E: Data, ~P: Data, ~U: Data, ~idle: E -> U32, ~hdms: E -> U32,
  ~plan: E -> Bytes() -> P -> L.Plan<P, U>, ~big: Bytes(), +srv: E, m: L.Put(World), p: P, hw: L.Hw) ->
  (World & L.Plan<P, U>) & L.Hw:
  L.turn(~Id, ~Id.pure, ~Id.bind, ~World, ~m.rx, ~w.clk, ~E, ~P, ~U, ~idle, ~hdms, ~plan, ~big, srv, m, p, hw)

def mute.segs(~shut: Bool -> Bytes() -> Bytes(), ~fhead: Bytes() -> U32 -> Bytes(),
  ~miss: Bool -> Bytes(), ~lnote: Bytes() -> Bytes() -> String,
  ~lsize: Bytes() -> Bytes() -> U32 -> String, s: World, xs: List<&2, L.Seg>, +ms: U32) -> L.Put(World):
  L.send.segs(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~m.tx, ~w.say, ~w.fopen, ~w.fsize,
    ~w.fread, ~m.fsend, ~w.fclose, ~shut, ~fhead, ~miss, ~lnote, ~lsize, s, xs, ms)

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
  ~shut: Bool -> Bytes() -> Bytes(), ~fhead: Bytes() -> U32 -> Bytes(),
  ~miss: Bool -> Bytes(), ~lnote: Bytes() -> Bytes() -> String,
  ~lsize: Bytes() -> Bytes() -> U32 -> String, xs: List<&2, L.Seg>, +ms: U32, may: Maybe<&2, Bytes()>, sh: Bool, st: L.Em<World>
) -> L.Put(World):
  L.send.go(~Id, ~Id.pure, ~Id.bind, ~World, ~Bytes(), ~m.tx, ~w.say, ~w.fopen, ~w.fsize,
    ~w.fread, ~m.fsend, ~w.fclose, ~shut, ~fhead, ~miss, ~lnote, ~lsize, xs, ms, may, sh, st)

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

# What File.get_under answered of a file, as data: the size it gave,
# whether it held the body (and closed the file) or left the file open,
# and how many bytes the body had.
type Got is Data:
  Got{n: U32, held: Bool, len: Nat}

def fget.body(+small: U32, +size: U32, g: Got) -> Bool:
  match g:
    case Got{+n, held, +len}:
      match held:
        case True{}:
          U32.is_eq(n, size) && U32.is_lt(size, small) && Nat.is_eq(len, U32.to_nat(size))
        case False{}:
          U32.is_eq(n, size) && Nat.is_eq(len, 0n)

# File.get_under(root, path, small), with the file size bytes long: it
# opens what open_under opens (fopen.ok), and answers a regular file's
# size, with its body whole when it is under small bytes, or no body and
# the file open (at or past small, or a small file whose bytes the page
# cache does not hold, which the loop then reads as a large one). Its
# answer may be one it read up to a second before (the memo, below):
# conform.bend's fget.memo checks a changed file is seen after that.
def fget.ok(k: Name, +small: U32, +size: U32, r: Result<&1, &1, U32 & String, Got>) -> Bool:
  match k r:
    case Plain{} Done{g}:
      fget.body(small, size, g)
    case Plain{} Fail{e}:
      False{}
    case _ Done{g}:
      False{}
    case _ Fail{e}:
      True{}

# The memo
# ========
#
# File.get_under answers a small file it read less than a second before
# from memory (bend2/effs/file_open_under.c: FILE_MEMO_NS, FILE_MEMO_N).
# As a model: what it read, newest first, each by its key (the root and
# the path), the time it read it (ms) and what it answered; a lookup
# takes the newest entry for its key read less than ttl before now, and
# keeping an answer puts it first and keeps at most memo.cap() entries.
# Its laws hold for any comparison of keys that is equality (~same,
# ~same_ok): the C memo compares a key's bytes with memcmp.
type Memo is Data:
  Memo{key: Bytes(), at: Nat, got: Bytes()}

def memo.cap() -> Nat:
  256n

def memo.find.at(hit: Bool, got: Bytes(), rest: Maybe<&2, Bytes()>) -> Maybe<&2, Bytes()>:
  match hit:
    case True{}:
      Some{got}
    case False{}:
      rest

def memo.find(~same: Bytes() -> Bytes() -> Bool, ms: List<&2, Memo>, +key: Bytes(), +now: Nat, +ttl: Nat) ->
  Maybe<&2, Bytes()>:
  match ms:
    case Nil{}:
      None{}
    case Con{Memo{k, +at, got}, t}:
      memo.find.at(same(k, key) && Nat.is_lt(now, Nat.add(at, ttl)), got, memo.find(~same, t, key, now, ttl))

# the first n entries
def memo.take(ms: List<&2, Memo>, n: Nat) -> List<&2, Memo>:
  match ms n:
    case Nil{} _:
      Nil{}
    case Con{m, t} 0n:
      Nil{}
    case Con{m, t} 1n+p:
      Con{m, memo.take(t, p)}

def memo.put(ms: List<&2, Memo>, key: Bytes(), now: Nat, got: Bytes()) -> List<&2, Memo>:
  memo.take(Con{Memo{key, now, got}, ms}, memo.cap())

# the effect with its memo: the memo's answer when it holds one, else
# the file system's (fresh), which it keeps
def memo.get.at(may: Maybe<&2, Bytes()>, ms: List<&2, Memo>, key: Bytes(), now: Nat, +fresh: Bytes()) ->
  List<&2, Memo> & Bytes():
  match may:
    case Some{g}:
      (ms, g)
    case None{}:
      (memo.put(ms, key, now, fresh), fresh)

def memo.get(~same: Bytes() -> Bytes() -> Bool, +ms: List<&2, Memo>, +key: Bytes(), +now: Nat, +ttl: Nat,
  fresh: Bytes()) -> List<&2, Memo> & Bytes():
  memo.get.at(memo.find(~same, ms, key, now, ttl), ms, key, now, fresh)

def memo.kept(g: List<&2, Memo> & Bytes()) -> List<&2, Memo>:
  (ms, a) = g
  ms

def memo.ans(g: List<&2, Memo> & Bytes()) -> Bytes():
  (ms, a) = g
  a

# at most n entries
def memo.within(ms: List<&2, Memo>, n: Nat) -> Bool:
  match ms n:
    case Nil{} _:
      True{}
    case Con{m, t} 0n:
      False{}
    case Con{m, t} 1n+p:
      memo.within(t, p)

# every answer kept is what the file system (~fs) answers its key with
def memo.AG(~fs: Bytes() -> Bytes(), ms: List<&2, Memo>) -> Type:
  match ms:
    case Nil{}:
      Unit
    case Con{Memo{k, at, g}, t}:
      {g == fs(k) : Bytes()} & memo.AG(~fs, t)

# LAW: the memo is bounded: after any lookup it holds at most memo.cap()
# entries, as it did before.
law memo_bounded:
  for ~same: Bytes() -> Bytes() -> Bool
  for +ms: List<&2, Memo>
  for +key: Bytes()
  for +now: Nat
  for +ttl: Nat
  for fresh: Bytes()
  for e: {memo.within(ms, memo.cap()) == True{} : Bool}
  {memo.within(memo.kept(memo.get(~same, ms, key, now, ttl, fresh)), memo.cap()) == True{} : Bool}

def memo.take_within(ms: List<&2, Memo>, n: Nat) -> {memo.within(memo.take(ms, n), n) == True{} : Bool}:
  match ms n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      {==}
    case Con{m, t} 0n:
      {==}
    case Con{m, t} 1n+p:
      memo.take_within(t, p)

def memo.bound.at(may: Maybe<&2, Bytes()>, +ms: List<&2, Memo>, +key: Bytes(), +now: Nat, fresh: Bytes(),
  e: {memo.within(ms, memo.cap()) == True{} : Bool}) ->
  {memo.within(memo.kept(memo.get.at(may, ms, key, now, fresh)), memo.cap()) == True{} : Bool}:
  match may:
    case Some{g}:
      e
    case None{}:
      memo.take_within(Con{Memo{key, now, fresh}, ms}, memo.cap())

def memo_bounded(same, ms, key, now, ttl, fresh, e):
  memo.bound.at(memo.find(~same, ms, key, now, ttl), ms, key, now, fresh, e)

# LAW: a cached answer is what the effect answered when it read it. For
# a file system that has not changed since the memo's answers were read
# (memo.AG), the answer the memo gives any key is the file system's.
law memo_answers:
  for ~same: Bytes() -> Bytes() -> Bool
  for ~same_ok: @a: Bytes() -> @b: Bytes() -> {same(a, b) == True{} : Bool} -> {a == b : Bytes()}
  for ~fs: Bytes() -> Bytes()
  for +ms: List<&2, Memo>
  for ag: memo.AG(~fs, ms)
  for +key: Bytes()
  for +now: Nat
  for +ttl: Nat
  {memo.ans(memo.get(~same, ms, key, now, ttl, fs(key))) == fs(key) : Bytes()}

def memo.FOK(~fs: Bytes() -> Bytes(), +key: Bytes(), may: Maybe<&2, Bytes()>) -> Type:
  match may:
    case None{}:
      Unit
    case Some{g}:
      {g == fs(key) : Bytes()}

def memo.hit.at(~same: Bytes() -> Bytes() -> Bool,
  ~same_ok: @a: Bytes() -> @b: Bytes() -> {same(a, b) == True{} : Bool} -> {a == b : Bytes()},
  ~fs: Bytes() -> Bytes(), +k: Bytes(), +key: Bytes(), +got: Bytes(), lt: Bool, b: Bool,
  e1: {got == fs(k) : Bytes()}, rest: Maybe<&2, Bytes()>, ih: memo.FOK(~fs, key, rest)) ->
  {Bool.and(same(k, key), lt) == b : Bool} ->
  memo.FOK(~fs, key, memo.find.at(Bool.and(same(k, key), lt), got, rest)):
  match b:
    case True{}:
      +eb =>
        %Equal.sym(Bool, Bool.and(same(k, key), lt), True{}, eb) :
          memo.FOK(~fs, key, memo.find.at(_, got, rest))
        %same_ok(k, key, Bool.and_l(same(k, key), lt, eb)) : {got == fs(_) : Bytes()}
        e1
    case False{}:
      +eb =>
        %Equal.sym(Bool, Bool.and(same(k, key), lt), False{}, eb) :
          memo.FOK(~fs, key, memo.find.at(_, got, rest))
        ih

def memo.hit(~same: Bytes() -> Bytes() -> Bool,
  ~same_ok: @a: Bytes() -> @b: Bytes() -> {same(a, b) == True{} : Bool} -> {a == b : Bytes()},
  ~fs: Bytes() -> Bytes(), ms: List<&2, Memo>, ag: memo.AG(~fs, ms), +key: Bytes(), +now: Nat, +ttl: Nat) ->
  memo.FOK(~fs, key, memo.find(~same, ms, key, now, ttl)):
  match ms:
    case Nil{}:
      Unit{}
    case Con{Memo{+k, +at, +got}, +t}:
      (e1, ag2) = ag
      memo.hit.at(~same, ~same_ok, ~fs, k, key, got, Nat.is_lt(now, Nat.add(at, ttl)),
        Bool.and(same(k, key), Nat.is_lt(now, Nat.add(at, ttl))), e1,
        memo.find(~same, t, key, now, ttl), memo.hit(~same, ~same_ok, ~fs, t, ag2, key, now, ttl))({==})

def memo.ans.at(~fs: Bytes() -> Bytes(), may: Maybe<&2, Bytes()>, +ms: List<&2, Memo>, +key: Bytes(), +now: Nat,
  ok: memo.FOK(~fs, key, may)) -> {memo.ans(memo.get.at(may, ms, key, now, fs(key))) == fs(key) : Bytes()}:
  match may:
    case Some{g}:
      ok
    case None{}:
      {==}

def memo_answers(same, same_ok, fs, ms, ag, key, now, ttl):
  memo.ans.at(~fs, memo.find(~same, ms, key, now, ttl), ms, key, now,
    memo.hit(~same, ~same_ok, ~fs, ms, ag, key, now, ttl))

# LAW: and the memo stays so: what it keeps after a lookup is what the
# file system answers, so memo_answers holds at the next lookup too.
law memo_keeps:
  for ~same: Bytes() -> Bytes() -> Bool
  for ~fs: Bytes() -> Bytes()
  for +ms: List<&2, Memo>
  for ag: memo.AG(~fs, ms)
  for +key: Bytes()
  for +now: Nat
  for +ttl: Nat
  memo.AG(~fs, memo.kept(memo.get(~same, ms, key, now, ttl, fs(key))))

def memo.take_ag(~fs: Bytes() -> Bytes(), ms: List<&2, Memo>, n: Nat, ag: memo.AG(~fs, ms)) ->
  memo.AG(~fs, memo.take(ms, n)):
  match ms n:
    case Nil{} _:
      Unit{}
    case Con{Memo{k, at, g}, t} 0n:
      Unit{}
    case Con{Memo{k, at, g}, t} 1n+p:
      (e1, ag2) = ag
      (e1, memo.take_ag(~fs, t, p, ag2))

def memo.keep.at(~fs: Bytes() -> Bytes(), may: Maybe<&2, Bytes()>, +ms: List<&2, Memo>, +key: Bytes(),
  +now: Nat, ag: memo.AG(~fs, ms)) -> memo.AG(~fs, memo.kept(memo.get.at(may, ms, key, now, fs(key)))):
  match may:
    case Some{g}:
      ag
    case None{}:
      memo.take_ag(~fs, Con{Memo{key, now, fs(key)}, ms}, memo.cap(), ({==}, ag))

def memo_keeps(same, fs, ms, ag, key, now, ttl):
  memo.keep.at(~fs, memo.find(~same, ms, key, now, ttl), ms, key, now, ag)

# File.read_buf(f, max) with left bytes left in the file: at most max
# bytes and at most what is left, and none only at the end
def fread.ok(max: U32, +left: Nat, r: Result<&1, &1, U32 & String, Bytes()>) -> Bool:
  match r:
    case Fail{e}:
      True{}
    case Done{+bs}:
      U32.is_le(U32.from_nat(Bytes.len(bs)), max) && Nat.is_le(Bytes.len(bs), left)
        && Bool.not(Nat.is_eq(Bytes.len(bs), 0n) && Bool.not(Nat.is_eq(left, 0n)))

# File.sendfile(s, f, off, len, ms), with left bytes in the file from off,
# to a peer that reads, stops reading, or resets: the first is Done when
# the file has the len bytes, and fails with ENODATA (61 on Linux, 96 on
# macOS) when it has fewer; the second fails with ETIMEDOUT after at
# least ms; the third fails. What reaches a reading peer is the file's
# bytes from off, len of them or as many as it had (fsend_served, and
# the peer's own check in conform.c).
def enodata.is(+code: U32) -> Bool:
  U32.is_eq(code, 61) || U32.is_eq(code, 96)

def enodata(e: U32 & String) -> Bool:
  (code, msg) = e
  enodata.is(code)

def fsend.read(whole: Bool, r: Result<&1, &1, U32 & String, Unit>) -> Bool:
  match whole r:
    case True{} Done{u}:
      True{}
    case True{} Fail{e}:
      False{}
    case False{} Done{u}:
      False{}
    case False{} Fail{e}:
      enodata(e)

def fsend.ok(
  +ms: U32, peer: Peer, +took: Nat, +left: Nat, +len: Nat, r: Result<&1, &1, U32 & String, Unit>
) -> Bool:
  match peer:
    case Reads{}:
      fsend.read(Nat.is_le(len, left), r)
    case Stops{}:
      match r:
        case Done{u}:
          False{}
        case Fail{e}:
          tx.timed(e, took, ms)
    case Resets{}:
      Result.is_fail(&1, &1, U32 & String, Unit, r)

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
# through fopen, fsize, page.start and the sendfile) with the comparison
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
  for ~fhead: Bytes() -> U32 -> Bytes()
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
  for ~fhead: Bytes() -> U32 -> Bytes()
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
  for ~fhead: Bytes() -> U32 -> Bytes()
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
  for ~fhead: Bytes() -> U32 -> Bytes()
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
  for ~fhead: Bytes() -> U32 -> Bytes()
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
  for ~fhead: Bytes() -> U32 -> Bytes()
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
# one, a missing file, a file of any size, sent by the kernel -- and
# whatever the peer does, a writer that may still take replies leaves
# it holding a batch below send.cap(): so the most ever held unsent is
# the cap, plus the one reply (or a file's head) that crossed it; a
# file's body is never held at all.
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

law wl.fsent_fine:
  for g: World & Bytes() & Result<&1, &1, U32 & String, Unit>
  {em.fine(sim.fsent(g)) == True{} : Bool}

def wl.fsent_fine(g):
  (s, fr) = g
  (f, r) = fr
  match r:
    case Done{u}:
      {==}
    case Fail{e}:
      {==}

law wl.headed_fine:
  for +ms: U32
  for f: Bytes()
  for n: U32
  for m: L.Put(World)
  {em.fine(sim.headed(ms, f, n, m)) == True{} : Bool}

def wl.headed_fine(ms, f, n, m):
  (s, r) = m
  match r:
    case Fail{e}:
      {==}
    case Done{u}:
      wl.fsent_fine(w.fsend(s, f, 0, n, ms))

law wl.blk_fine:
  for m: L.Put(World)
  for whole: Bool
  {em.fine(L.page.blk(World, m, whole)) == True{} : Bool}

def wl.blk_fine(m, whole):
  (s, r) = m
  match r:
    case Done{u}:
      match whole:
        case True{}:
          {==}
        case False{}:
          {==}
    case Fail{e}:
      {==}

law wl.read_fine:
  for +ms: U32
  for got: Bytes() & Result<&1, &1, U32 & String, Bytes()>
  for +n: U32
  for s: World
  for pre: Bytes()
  {em.fine(sim.read(ms, got, n, s, pre)) == True{} : Bool}

def wl.read_fine(ms, got, n, s, pre):
  (f, r) = got
  match r:
    case Fail{e}:
      {==}
    case Done{+bs}:
      wl.blk_fine(w.tx(s, Bytes.append(pre, bs), ms), Nat.is_eq(Bytes.len(bs), U32.to_nat(n)))

law wl.body_fine:
  for +ms: U32
  for +f: Bytes()
  for +n: U32
  for +s: World
  for +pre: Bytes()
  for small: Bool
  {em.fine(sim.body(ms, f, n, s, pre, small)) == True{} : Bool}

def wl.body_fine(ms, f, n, s, pre, small):
  match small:
    case True{}:
      wl.read_fine(ms, w.fread(f, n), n, s, pre)
    case False{}:
      wl.headed_fine(ms, f, n, w.tx(s, pre, ms))

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
      wl.body_fine(ms, f, n, s, Bytes.append(acc, hd), U32.is_lt(n, L.page.small()))

law wl.psized_fine:
  for ~shut: Bool -> Bytes() -> Bytes()
  for ~fhead: Bytes() -> U32 -> Bytes()
  for ~miss: Bool -> Bytes()
  for ~lnote: Bytes() -> Bytes() -> String
  for ~lsize: Bytes() -> Bytes() -> U32 -> String
  for +ms: U32
  for got: Bytes() & Result<&1, &1, U32 & String, U32>
  for ct: Bytes()
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
  for ~fhead: Bytes() -> U32 -> Bytes()
  for ~miss: Bool -> Bytes()
  for ~lnote: Bytes() -> Bytes() -> String
  for ~lsize: Bytes() -> Bytes() -> U32 -> String
  for +ms: U32
  for m: World & Result<&1, &1, U32 & String, Bytes()>
  for ct: Bytes()
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
  for ~fhead: Bytes() -> U32 -> Bytes()
  for ~miss: Bool -> Bytes()
  for ~lnote: Bytes() -> Bytes() -> String
  for ~lsize: Bytes() -> Bytes() -> U32 -> String
  for +ms: U32
  for root: Bytes()
  for path: Bytes()
  for ct: Bytes()
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
          wl.opened_fine(~shut, ~fhead, ~miss, ~lnote, ~lsize, ms, w.fopen(s, root, path), ct, head, may, sh, acc)

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
  for ~fhead: Bytes() -> U32 -> Bytes()
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
  for ~fhead: Bytes() -> U32 -> Bytes()
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
  for ~fhead: Bytes() -> U32 -> Bytes()
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
  for ~fhead: Bytes() -> U32 -> Bytes()
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
  for ~fhead: Bytes() -> U32 -> Bytes()
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
  for ~fhead: Bytes() -> U32 -> Bytes()
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
  for ~fhead: Bytes() -> U32 -> Bytes()
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
  for ~fhead: Bytes() -> U32 -> Bytes()
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
  for ~fhead: Bytes() -> U32 -> Bytes()
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
  for ~fhead: Bytes() -> U32 -> Bytes()
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
  for ~fhead: Bytes() -> U32 -> Bytes()
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
  for ~fhead: Bytes() -> U32 -> Bytes()
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
  for ~fhead: Bytes() -> U32 -> Bytes()
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
  for ~fhead: Bytes() -> U32 -> Bytes()
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

# a sendfile to a peer that takes everything puts the file's bytes from
# off on the wire, len of them or as many as the file had, and is Done
# only when it had them all
def wl.eq_le(+s: Bytes(), +n: Nat) ->
  {Nat.is_eq(Bytes.len(String.take(s, n)), n) == Nat.is_le(n, Bytes.len(s)) : Bool}:
  match s n:
    case SNil{} 0n:
      {==}
    case SNil{} 1n+q:
      {==}
    case SCon{+h, +t} 0n:
      %Equal.sym(Nat, String.length.go(t, 1n), 1n+String.length.go(t, 0n),
        Bytes.len.shift(t, 0n)) :
        {True{} == Nat.is_le(0n, _) : Bool}
      {==}
    case SCon{+h, +t} 1n+p:
      %Equal.sym(Nat, String.length.go(String.take(t, p), 1n),
        1n+String.length.go(String.take(t, p), 0n), Bytes.len.shift(String.take(t, p), 0n)) :
        {Nat.is_eq(_, 1n+p) == Nat.is_le(1n+p, Bytes.len(SCon{h, t})) : Bool}
      %Equal.sym(Nat, String.length.go(t, 1n), 1n+String.length.go(t, 0n),
        Bytes.len.shift(t, 0n)) :
        {Nat.is_eq(Bytes.len(String.take(t, p)), p) == Nat.is_le(1n+p, _) : Bool}
      wl.eq_le(t, p)

law fsend_served:
  for +rd: List<&2, Rd>
  for +now: Nat
  for +fs: List<&2, Fil>
  for +out: Bytes()
  for +f: Bytes()
  for +off: U32
  for +len: U32
  for +ms: U32
  {w.fsend(eager(rd, now, fs, out), f, off, len, ms) ==
    (eager(rd, now, fs, Bytes.append(out, w.fbytes(f, off, len))),
      (f, w.fsend.cut(Nat.is_le(U32.to_nat(len), Bytes.len(String.drop(f, U32.to_nat(off)))),
        Done{Unit{}}))) : World & Bytes() & Result<&1, &1, U32 & String, Unit>}

def fsend_served(rd, now, fs, out, f, off, len, ms):
  %Equal.sym(L.Put(World), w.tx(eager(rd, now, fs, out), w.fbytes(f, off, len), ms),
    sent(rd, now, fs, Bytes.append(out, w.fbytes(f, off, len))),
    wl.tx_eager(rd, now, fs, out, w.fbytes(f, off, len), ms)) :
    {w.fsend.at(_, f, Nat.is_eq(Bytes.len(w.fbytes(f, off, len)), U32.to_nat(len))) ==
      (eager(rd, now, fs, Bytes.append(out, w.fbytes(f, off, len))),
        (f, w.fsend.cut(Nat.is_le(U32.to_nat(len), Bytes.len(String.drop(f, U32.to_nat(off)))),
          Done{Unit{}}))) : World & Bytes() & Result<&1, &1, U32 & String, Unit>}
  %Equal.sym(Bool, Nat.is_eq(Bytes.len(w.fbytes(f, off, len)), U32.to_nat(len)),
    Nat.is_le(U32.to_nat(len), Bytes.len(String.drop(f, U32.to_nat(off)))),
    wl.eq_le(String.drop(f, U32.to_nat(off)), U32.to_nat(len))) :
    {w.fsend.at(sent(rd, now, fs, Bytes.append(out, w.fbytes(f, off, len))), f, _) ==
      (eager(rd, now, fs, Bytes.append(out, w.fbytes(f, off, len))),
        (f, w.fsend.cut(Nat.is_le(U32.to_nat(len), Bytes.len(String.drop(f, U32.to_nat(off)))),
          Done{Unit{}}))) : World & Bytes() & Result<&1, &1, U32 & String, Unit>}
  {==}

def fsend.res(g: World & Bytes() & Result<&1, &1, U32 & String, Unit>) ->
  Result<&1, &1, U32 & String, Unit>:
  (s, fr) = g
  (f, r) = fr
  r

def wl.read_cut(whole: Bool) ->
  {fsend.read(whole, w.fsend.cut(whole, Done{Unit{}})) == True{} : Bool}:
  match whole:
    case True{}:
      {==}
    case False{}:
      {==}

law fsend_model:
  for +rd: List<&2, Rd>
  for +now: Nat
  for +fs: List<&2, Fil>
  for +out: Bytes()
  for +f: Bytes()
  for +off: U32
  for +len: U32
  for +ms: U32
  {fsend.ok(ms, Reads{}, 0n, Bytes.len(String.drop(f, U32.to_nat(off))), U32.to_nat(len),
    fsend.res(w.fsend(eager(rd, now, fs, out), f, off, len, ms))) == True{} : Bool}

def fsend_model(rd, now, fs, out, f, off, len, ms):
  %Equal.sym(World & Bytes() & Result<&1, &1, U32 & String, Unit>,
    w.fsend(eager(rd, now, fs, out), f, off, len, ms),
    (eager(rd, now, fs, Bytes.append(out, w.fbytes(f, off, len))),
      (f, w.fsend.cut(Nat.is_le(U32.to_nat(len), Bytes.len(String.drop(f, U32.to_nat(off)))),
        Done{Unit{}}))),
    fsend_served(rd, now, fs, out, f, off, len, ms)) :
    {fsend.ok(ms, Reads{}, 0n, Bytes.len(String.drop(f, U32.to_nat(off))), U32.to_nat(len),
      fsend.res(_)) == True{} : Bool}
  wl.read_cut(Nat.is_le(U32.to_nat(len), Bytes.len(String.drop(f, U32.to_nat(off)))))

# a sendfile with bytes to move, to a peer that has stopped reading,
# fails with ETIMEDOUT after its time
def wl.cut_fail(whole: Bool, -e: U32 & String) ->
  {w.fsend.cut(whole, Fail{e}) == Fail{e} : Result<&1, &1, U32 & String, Unit>}:
  match whole:
    case True{}:
      {==}
    case False{}:
      {==}

law fsend_stalled:
  for +rd: List<&2, Rd>
  for +now: Nat
  for +fs: List<&2, Fil>
  for +out: Bytes()
  for +f: Bytes()
  for +off: U32
  for +len: U32
  for +ms: U32
  for +h: Char
  for +t: Bytes()
  for e: {w.fbytes(f, off, len) == SCon{h, t} : Bytes()}
  {fsend.ok(ms, Stops{}, Nat.sub(Nat.add(now, U32.to_nat(ms)), now),
    Bytes.len(String.drop(f, U32.to_nat(off))), U32.to_nat(len),
    fsend.res(w.fsend(World{rd, Nil{}, False{}, now, fs, out}, f, off, len, ms))) == True{} : Bool}

def fsend_stalled(rd, now, fs, out, f, off, len, ms, h, t, e):
  %Equal.sym(Bytes(), w.fbytes(f, off, len), SCon{h, t}, e) :
    {fsend.ok(ms, Stops{}, Nat.sub(Nat.add(now, U32.to_nat(ms)), now),
      Bytes.len(String.drop(f, U32.to_nat(off))), U32.to_nat(len),
      fsend.res(w.fsend.bs(World{rd, Nil{}, False{}, now, fs, out}, f, _, U32.to_nat(len), ms))) ==
      True{} : Bool}
  %Equal.sym(Result<&1, &1, U32 & String, Unit>,
    w.fsend.cut(Nat.is_eq(Bytes.len(SCon{h, t}), U32.to_nat(len)), Fail{(110, "timed out")}),
    Fail{(110, "timed out")},
    wl.cut_fail(Nat.is_eq(Bytes.len(SCon{h, t}), U32.to_nat(len)), (110, "timed out"))) :
    {fsend.ok(ms, Stops{}, Nat.sub(Nat.add(now, U32.to_nat(ms)), now),
      Bytes.len(String.drop(f, U32.to_nat(off))), U32.to_nat(len), _) == True{} : Bool}
  wl.waited(now, ms)

# LAW: a file's bytes. At a peer that takes what it is sent, a Page of a
# file the root has (of fewer than 2^32 bytes, as File.size answers for
# any it sizes) puts on the wire what waited in front of it, the head
# its size framed, and then the file's own bytes, every one and nothing
# else, and leaves the writer empty and able to go on.
def wl.drop_0(+f: Bytes()) -> {String.drop(f, 0n) == f : Bytes()}:
  match f:
    case SNil{}:
      {==}
    case SCon{h, t}:
      {==}

def wl.take_all(+f: Bytes()) -> {String.take(f, Bytes.len(f)) == f : Bytes()}:
  match f:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %Equal.sym(Nat, String.length.go(t, 1n), 1n+String.length.go(t, 0n),
        Bytes.len.shift(t, 0n)) :
        {String.take(SCon{h, t}, _) == SCon{h, t} : Bytes()}
      Equal.cong(Bytes(), Bytes(), x => SCon{h, x}, String.take(t, Bytes.len(t)), t,
        wl.take_all(t))

law wl.fbytes_all:
  for +f: Bytes()
  for en: {U32.to_nat(U32.from_nat(Bytes.len(f))) == Bytes.len(f) : Nat}
  {w.fbytes(f, 0, U32.from_nat(Bytes.len(f))) == f : Bytes()}

def wl.fbytes_all(f, en):
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(Bytes.len(f))), Bytes.len(f), en) :
    {String.take(String.drop(f, 0n), _) == f : Bytes()}
  %Equal.sym(Bytes(), String.drop(f, 0n), f, wl.drop_0(f)) :
    {String.take(_, Bytes.len(f)) == f : Bytes()}
  wl.take_all(f)

law wl.fall_le:
  for +f: Bytes()
  for en: {U32.to_nat(U32.from_nat(Bytes.len(f))) == Bytes.len(f) : Nat}
  {Nat.is_le(U32.to_nat(U32.from_nat(Bytes.len(f))), Bytes.len(String.drop(f, 0n))) ==
    True{} : Bool}

def wl.fall_le(f, en):
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(Bytes.len(f))), Bytes.len(f), en) :
    {Nat.is_le(_, Bytes.len(String.drop(f, 0n))) == True{} : Bool}
  %Equal.sym(Bytes(), String.drop(f, 0n), f, wl.drop_0(f)) :
    {Nat.is_le(Bytes.len(f), Bytes.len(_)) == True{} : Bool}
  wl.le_refl(Bytes.len(f))

law wl.fsend_whole.at:
  for +rd: List<&2, Rd>
  for +now: Nat
  for +fs: List<&2, Fil>
  for +o: Bytes()
  for +f: Bytes()
  for +en: {U32.to_nat(U32.from_nat(Bytes.len(f))) == Bytes.len(f) : Nat}
  {(eager(rd, now, fs, Bytes.append(o, w.fbytes(f, 0, U32.from_nat(Bytes.len(f))))),
      (f, w.fsend.cut(Nat.is_le(U32.to_nat(U32.from_nat(Bytes.len(f))),
        Bytes.len(String.drop(f, 0n))), Done{Unit{}}))) ==
    (eager(rd, now, fs, Bytes.append(o, f)), (f, Done{Unit{}})) :
    World & Bytes() & Result<&1, &1, U32 & String, Unit>}

def wl.fsend_whole.at(rd, now, fs, o, f, en):
  %Equal.sym(Bytes(), w.fbytes(f, 0, U32.from_nat(Bytes.len(f))), f, wl.fbytes_all(f, en)) :
    {(eager(rd, now, fs, Bytes.append(o, _)),
      (f, w.fsend.cut(Nat.is_le(U32.to_nat(U32.from_nat(Bytes.len(f))),
        Bytes.len(String.drop(f, 0n))), Done{Unit{}}))) ==
      (eager(rd, now, fs, Bytes.append(o, f)), (f, Done{Unit{}})) :
      World & Bytes() & Result<&1, &1, U32 & String, Unit>}
  %Equal.sym(Bool, Nat.is_le(U32.to_nat(U32.from_nat(Bytes.len(f))),
      Bytes.len(String.drop(f, 0n))), True{}, wl.fall_le(f, en)) :
    {(eager(rd, now, fs, Bytes.append(o, f)), (f, w.fsend.cut(_, Done{Unit{}}))) ==
      (eager(rd, now, fs, Bytes.append(o, f)), (f, Done{Unit{}})) :
      World & Bytes() & Result<&1, &1, U32 & String, Unit>}
  {==}

# a sendfile of a whole file to a peer that takes everything puts the
# file on the wire after what was there, and succeeds
law wl.fsend_whole:
  for +rd: List<&2, Rd>
  for +now: Nat
  for +fs: List<&2, Fil>
  for +o: Bytes()
  for +f: Bytes()
  for +ms: U32
  for en: {U32.to_nat(U32.from_nat(Bytes.len(f))) == Bytes.len(f) : Nat}
  {w.fsend(eager(rd, now, fs, o), f, 0, U32.from_nat(Bytes.len(f)), ms) ==
    (eager(rd, now, fs, Bytes.append(o, f)), (f, Done{Unit{}})) :
    World & Bytes() & Result<&1, &1, U32 & String, Unit>}

def wl.fsend_whole(rd, now, fs, o, f, ms, en):
  Equal.trans(World & Bytes() & Result<&1, &1, U32 & String, Unit>,
    w.fsend(eager(rd, now, fs, o), f, 0, U32.from_nat(Bytes.len(f)), ms),
    (eager(rd, now, fs, Bytes.append(o, w.fbytes(f, 0, U32.from_nat(Bytes.len(f))))),
      (f, w.fsend.cut(Nat.is_le(U32.to_nat(U32.from_nat(Bytes.len(f))),
        Bytes.len(String.drop(f, 0n))), Done{Unit{}}))),
    (eager(rd, now, fs, Bytes.append(o, f)), (f, Done{Unit{}})),
    fsend_served(rd, now, fs, o, f, 0, U32.from_nat(Bytes.len(f)), ms),
    wl.fsend_whole.at(rd, now, fs, o, f, en))

law wl.headed_wire:
  for +ms: U32
  for +f: Bytes()
  for +rd: List<&2, Rd>
  for +now: Nat
  for +fs: List<&2, Fil>
  for +o: Bytes()
  for en: {U32.to_nat(U32.from_nat(Bytes.len(f))) == Bytes.len(f) : Nat}
  {sim.headed(ms, f, U32.from_nat(Bytes.len(f)), sent(rd, now, fs, o)) ==
    L.Em{eager(rd, now, fs, Bytes.append(o, f)), "", True{}} : L.Em<World>}

def wl.headed_wire(ms, f, rd, now, fs, o, en):
  %Equal.sym(World & Bytes() & Result<&1, &1, U32 & String, Unit>,
    w.fsend(eager(rd, now, fs, o), f, 0, U32.from_nat(Bytes.len(f)), ms),
    (eager(rd, now, fs, Bytes.append(o, f)), (f, Done{Unit{}})),
    wl.fsend_whole(rd, now, fs, o, f, ms, en)) :
    {sim.fsent(_) == L.Em{eager(rd, now, fs, Bytes.append(o, f)), "", True{}} : L.Em<World>}
  {==}

def wl.eq_refl(+n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      wl.eq_refl(p)

law wl.blk_eager:
  for +rd: List<&2, Rd>
  for +now: Nat
  for +fs: List<&2, Fil>
  for +out: Bytes()
  for +x: Bytes()
  for +whole: Bool
  for +ms: U32
  {L.page.blk(World, w.tx(eager(rd, now, fs, out), x, ms), whole) ==
    L.Em{eager(rd, now, fs, Bytes.append(out, x)), "", whole} : L.Em<World>}

def wl.blk_eager(rd, now, fs, out, x, whole, ms):
  %Equal.sym(L.Put(World), w.tx(eager(rd, now, fs, out), x, ms),
    sent(rd, now, fs, Bytes.append(out, x)), wl.tx_eager(rd, now, fs, out, x, ms)) :
    {L.page.blk(World, _, whole) == L.Em{eager(rd, now, fs, Bytes.append(out, x)), "", whole} :
      L.Em<World>}
  {==}

law wl.take_n:
  for +f: Bytes()
  for en: {U32.to_nat(U32.from_nat(Bytes.len(f))) == Bytes.len(f) : Nat}
  {String.take(f, U32.to_nat(U32.from_nat(Bytes.len(f)))) == f : Bytes()}

def wl.take_n(f, en):
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(Bytes.len(f))), Bytes.len(f), en) :
    {String.take(f, _) == f : Bytes()}
  wl.take_all(f)

law wl.whole_n:
  for +f: Bytes()
  for +en: {U32.to_nat(U32.from_nat(Bytes.len(f))) == Bytes.len(f) : Nat}
  {Nat.is_eq(Bytes.len(String.take(f, U32.to_nat(U32.from_nat(Bytes.len(f))))),
    U32.to_nat(U32.from_nat(Bytes.len(f)))) == True{} : Bool}

def wl.whole_n(f, en):
  %Equal.sym(Bytes(), String.take(f, U32.to_nat(U32.from_nat(Bytes.len(f)))), f, wl.take_n(f, en)) :
    {Nat.is_eq(Bytes.len(_), U32.to_nat(U32.from_nat(Bytes.len(f)))) == True{} : Bool}
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(Bytes.len(f))), Bytes.len(f), en) :
    {Nat.is_eq(Bytes.len(f), _) == True{} : Bool}
  wl.eq_refl(Bytes.len(f))

law wl.read_wire.at:
  for +f: Bytes()
  for +rd: List<&2, Rd>
  for +now: Nat
  for +fs: List<&2, Fil>
  for +out: Bytes()
  for +pre: Bytes()
  for +en: {U32.to_nat(U32.from_nat(Bytes.len(f))) == Bytes.len(f) : Nat}
  {L.Em{eager(rd, now, fs, Bytes.append(out,
      Bytes.append(pre, String.take(f, U32.to_nat(U32.from_nat(Bytes.len(f))))))), "",
      Nat.is_eq(Bytes.len(String.take(f, U32.to_nat(U32.from_nat(Bytes.len(f))))),
        U32.to_nat(U32.from_nat(Bytes.len(f))))} ==
    L.Em{eager(rd, now, fs, Bytes.append(Bytes.append(out, pre), f)), "", True{}} : L.Em<World>}

def wl.read_wire.at(f, rd, now, fs, out, pre, en):
  %Equal.sym(Bool, Nat.is_eq(Bytes.len(String.take(f, U32.to_nat(U32.from_nat(Bytes.len(f))))),
      U32.to_nat(U32.from_nat(Bytes.len(f)))), True{}, wl.whole_n(f, en)) :
    {L.Em{eager(rd, now, fs, Bytes.append(out,
      Bytes.append(pre, String.take(f, U32.to_nat(U32.from_nat(Bytes.len(f))))))), "", _} ==
      L.Em{eager(rd, now, fs, Bytes.append(Bytes.append(out, pre), f)), "", True{}} : L.Em<World>}
  %Equal.sym(Bytes(), String.take(f, U32.to_nat(U32.from_nat(Bytes.len(f)))), f, wl.take_n(f, en)) :
    {L.Em{eager(rd, now, fs, Bytes.append(out, Bytes.append(pre, _))), "", True{}} ==
      L.Em{eager(rd, now, fs, Bytes.append(Bytes.append(out, pre), f)), "", True{}} : L.Em<World>}
  Equal.cong(Bytes(), L.Em<World>, y => L.Em{eager(rd, now, fs, y), "", True{}},
    Bytes.append(out, Bytes.append(pre, f)), Bytes.append(Bytes.append(out, pre), f),
    Equal.sym(Bytes(), Bytes.append(Bytes.append(out, pre), f), Bytes.append(out, Bytes.append(pre, f)),
      wl.app_assoc(out, pre, f)))

# a small file: read whole, and on the wire with its head in one send
law wl.read_wire:
  for +ms: U32
  for +f: Bytes()
  for +rd: List<&2, Rd>
  for +now: Nat
  for +fs: List<&2, Fil>
  for +out: Bytes()
  for +pre: Bytes()
  for +en: {U32.to_nat(U32.from_nat(Bytes.len(f))) == Bytes.len(f) : Nat}
  {sim.read(ms, w.fread(f, U32.from_nat(Bytes.len(f))), U32.from_nat(Bytes.len(f)),
      eager(rd, now, fs, out), pre) ==
    L.Em{eager(rd, now, fs, Bytes.append(Bytes.append(out, pre), f)), "", True{}} : L.Em<World>}

def wl.read_wire(ms, f, rd, now, fs, out, pre, en):
  Equal.trans(L.Em<World>,
    L.page.blk(World, w.tx(eager(rd, now, fs, out),
        Bytes.append(pre, String.take(f, U32.to_nat(U32.from_nat(Bytes.len(f))))), ms),
      Nat.is_eq(Bytes.len(String.take(f, U32.to_nat(U32.from_nat(Bytes.len(f))))),
        U32.to_nat(U32.from_nat(Bytes.len(f))))),
    L.Em{eager(rd, now, fs, Bytes.append(out,
        Bytes.append(pre, String.take(f, U32.to_nat(U32.from_nat(Bytes.len(f))))))), "",
      Nat.is_eq(Bytes.len(String.take(f, U32.to_nat(U32.from_nat(Bytes.len(f))))),
        U32.to_nat(U32.from_nat(Bytes.len(f))))},
    L.Em{eager(rd, now, fs, Bytes.append(Bytes.append(out, pre), f)), "", True{}},
    wl.blk_eager(rd, now, fs, out,
      Bytes.append(pre, String.take(f, U32.to_nat(U32.from_nat(Bytes.len(f))))),
      Nat.is_eq(Bytes.len(String.take(f, U32.to_nat(U32.from_nat(Bytes.len(f))))),
        U32.to_nat(U32.from_nat(Bytes.len(f)))), ms),
    wl.read_wire.at(f, rd, now, fs, out, pre, en))

law wl.body_wire:
  for +ms: U32
  for +f: Bytes()
  for +rd: List<&2, Rd>
  for +now: Nat
  for +fs: List<&2, Fil>
  for +out: Bytes()
  for +pre: Bytes()
  for small: Bool
  for +en: {U32.to_nat(U32.from_nat(Bytes.len(f))) == Bytes.len(f) : Nat}
  {sim.body(ms, f, U32.from_nat(Bytes.len(f)), eager(rd, now, fs, out), pre, small) ==
    L.Em{eager(rd, now, fs, Bytes.append(Bytes.append(out, pre), f)), "", True{}} : L.Em<World>}

def wl.body_wire(ms, f, rd, now, fs, out, pre, small, en):
  match small:
    case True{}:
      wl.read_wire(ms, f, rd, now, fs, out, pre, en)
    case False{}:
      %Equal.sym(L.Put(World), w.tx(eager(rd, now, fs, out), pre, ms),
        sent(rd, now, fs, Bytes.append(out, pre)), wl.tx_eager(rd, now, fs, out, pre, ms)) :
        {sim.headed(ms, f, U32.from_nat(Bytes.len(f)), _) ==
          L.Em{eager(rd, now, fs, Bytes.append(Bytes.append(out, pre), f)), "", True{}} :
          L.Em<World>}
      wl.headed_wire(ms, f, rd, now, fs, Bytes.append(out, pre), en)

law page_wire:
  for ~shut: Bool -> Bytes() -> Bytes()
  for ~fhead: Bytes() -> U32 -> Bytes()
  for ~miss: Bool -> Bytes()
  for ~lnote: Bytes() -> Bytes() -> String
  for ~lsize: Bytes() -> Bytes() -> U32 -> String
  for +ms: U32
  for root: Bytes()
  for path: Bytes()
  for +ct: Bytes()
  for may: Maybe<&2, Bytes()>
  for +sh: Bool
  for +rd: List<&2, Rd>
  for +now: Nat
  for +fs: List<&2, Fil>
  for +out: Bytes()
  for +acc: Bytes()
  for +body: Bytes()
  for ef: {w.find(fs, path) == Done{body} : Result<&1, &1, U32 & String, Bytes()>}
  for +en: {U32.to_nat(U32.from_nat(Bytes.len(body))) == Bytes.len(body) : Nat}
  {sim.page(~shut, ~fhead, ~miss, ~lnote, ~lsize, ms, root, path, ct, False{}, may, sh,
      L.Em{eager(rd, now, fs, out), acc, True{}}) ==
    L.Em{eager(rd, now, fs, Bytes.append(Bytes.append(out,
      Bytes.append(acc, shut(sh, fhead(ct, U32.from_nat(Bytes.len(body)))))), body)), "",
      True{}} : L.Em<World>}

def page_wire(shut, fhead, miss, lnote, lsize, ms, root, path, ct, may, sh, rd, now, fs, out, acc,
  body, ef, en):
  %Equal.sym(Result<&1, &1, U32 & String, Bytes()>, w.find(fs, path), Done{body}, ef) :
    {sim.opened(~shut, ~fhead, ~miss, ~lnote, ~lsize, ms, (eager(rd, now, fs, out), _), ct,
        False{}, may, sh, acc) ==
      L.Em{eager(rd, now, fs, Bytes.append(Bytes.append(out,
        Bytes.append(acc, shut(sh, fhead(ct, U32.from_nat(Bytes.len(body)))))), body)), "",
        True{}} : L.Em<World>}
  wl.body_wire(ms, body, rd, now, fs, out,
    Bytes.append(acc, shut(sh, fhead(ct, U32.from_nat(Bytes.len(body))))),
    U32.is_lt(U32.from_nat(Bytes.len(body)), L.page.small()), en)

# LAW: nothing after a failed sendfile. A file's body that did not all
# go out -- the send failed or stalled, or the file came up short --
# leaves the writer unable to take more, so the connection ends with
# nothing after it; and a head that did not go out is not followed by
# its body.
law page_fail:
  for s: World
  for f: Bytes()
  for e: U32 & String
  {sim.fsent((s, (f, Fail{e}))) == L.Em{s, "", False{}} : L.Em<World>}

def page_fail(s, f, e):
  {==}

law page_head_fail:
  for +ms: U32
  for f: Bytes()
  for n: U32
  for s: World
  for e: U32 & String
  {sim.headed(ms, f, n, (s, Fail{e})) == L.Em{s, "", False{}} : L.Em<World>}

def page_head_fail(ms, f, n, s, e):
  {==}

# ... and a small file's read that came back short ends it too, after
# what the read had: a head's length is never followed by fewer bytes
# and then more
def em.ok(em: L.Em<World>) -> Bool:
  match em:
    case L.Em{s, acc, ok}:
      ok

def wl.blk_short(m: L.Put(World)) -> {em.ok(L.page.blk(World, m, False{})) == False{} : Bool}:
  (s, r) = m
  match r:
    case Done{u}:
      {==}
    case Fail{e}:
      {==}

law page_read_short:
  for +ms: U32
  for f: Bytes()
  for +bs: Bytes()
  for +n: U32
  for +s: World
  for +pre: Bytes()
  for e: {Nat.is_eq(Bytes.len(bs), U32.to_nat(n)) == False{} : Bool}
  {em.ok(sim.read(ms, (f, Done{bs}), n, s, pre)) == False{} : Bool}

def page_read_short(ms, f, bs, n, s, pre, e):
  %Equal.sym(Bool, Nat.is_eq(Bytes.len(bs), U32.to_nat(n)), False{}, e) :
    {em.ok(L.page.blk(World, w.tx(s, Bytes.append(pre, bs), ms), _)) == False{} : Bool}
  wl.blk_short(w.tx(s, Bytes.append(pre, bs), ms))

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

# The body stream in the model
# ============================
#
# wire/stream.bend's pass, pull and turn with the identity monad, the
# scripted peer, and a scripted consumer: what it takes of each offer,
# in order (past its script, all of it), what it has taken so far, and
# how many ends it has been told. The framer is any: its state, feed,
# take and look are the laws' template parameters, so the laws hold for
# every body a reader frames.
type Snk is Data:
  Snk{takes: List<&2, Nat>, got: Bytes(), fins: Nat}

def k.give.at(takes: List<&2, Nat>, +got: Bytes(), fins: Nat, +bs: Bytes()) -> Snk & Nat:
  match takes:
    case Nil{}:
      (Snk{Nil{}, Bytes.append(got, String.take(bs, Bytes.len(bs))), fins}, Bytes.len(bs))
    case Con{+n, t}:
      (Snk{t, Bytes.append(got, String.take(bs, n)), fins}, n)

def k.give.go(k: Snk, +bs: Bytes()) -> Snk & Nat:
  match k:
    case Snk{takes, +got, fins}:
      k.give.at(takes, got, fins, bs)

def k.give(k: Snk, bs: Bytes()) -> Snk & Nat:
  k.give.go(k, bs)

def k.fin(k: Snk) -> Snk:
  match k:
    case Snk{takes, got, fins}:
      Snk{takes, got, 1n+fins}

def sb.pass(~R: Data, ~look: R -> Bs.Stage, +win: Nat, bq: Bs.Bq<World, R, Snk>) ->
  Bs.Turn(World, R, Snk):
  Bs.pass(~Id, ~Id.pure, ~Id.bind, ~World, ~R, ~look, ~Snk, ~k.give, win, bq)

def sb.pull(
  ~E: Data, ~R: Data, ~feed: E -> Bytes() -> R -> R, ~take: R -> R & Bytes(),
  ~look: R -> Bs.Stage, +e: E, +win: Nat, +ms: U32, bq: Bs.Bq<World, R, Snk>
) -> Bs.Turn(World, R, Snk):
  Bs.pull(~Id, ~Id.pure, ~Id.bind, ~World, ~w.rx, ~E, ~R, ~feed, ~take, ~look, ~Snk, ~k.fin, e,
    win, ms, bq)

def sb.turn(
  ~E: Data, ~R: Data, ~feed: E -> Bytes() -> R -> R, ~take: R -> R & Bytes(),
  ~look: R -> Bs.Stage, +e: E, +win: Nat, +ms: U32, bq: Bs.Bq<World, R, Snk>
) -> Bs.Turn(World, R, Snk):
  Bs.turn(~Id, ~Id.pure, ~Id.bind, ~World, ~w.rx, ~E, ~R, ~feed, ~take, ~look, ~Snk, ~k.give,
    ~k.fin, e, win, ms, bq)

# what a turn leaves: the socket, what the consumer has taken followed by
# what the stream still holds, and the ends told
def sb.moved(-R: Data, t: Bs.Turn(World, R, Snk)) -> World & Bytes() & Nat:
  (bq, w) = t
  match bq:
    case Bs.Bq{s, r, k, held, eof}:
      match k:
        case Snk{takes, got, fins}:
          (s, (Bytes.append(got, held), fins))

def sb.fins(-R: Data, t: Bs.Turn(World, R, Snk)) -> Nat:
  (bq, w) = t
  match bq:
    case Bs.Bq{s, r, k, held, eof}:
      match k:
        case Snk{takes, got, fins}:
          fins

def sb.qs(-R: Data, q: R & Bytes()) -> R:
  (r, x) = q
  r

def sb.qb(-R: Data, q: R & Bytes()) -> Bytes():
  (r, x) = q
  x

# LAW: a pass moves bytes, and only moves them. Whatever the consumer
# takes, what it has taken followed by what the stream still holds is
# what it had taken followed by what the stream held: in order, none
# lost, none doubled; the socket is not touched and no end is told.
def wl.take_drop(+b: Bytes(), +n: Nat) ->
  {Bytes.append(String.take(b, n), String.drop(b, n)) == b : Bytes()}:
  match b n:
    case SNil{} 0n:
      {==}
    case SNil{} 1n+p:
      {==}
    case SCon{h, t} 0n:
      {==}
    case SCon{+h, +t} 1n+p:
      Equal.cong(Bytes(), Bytes(), x => SCon{h, x}, Bytes.append(String.take(t, p), String.drop(t, p)),
        t, wl.take_drop(t, p))

law wl.stall_moved:
  for -R: Data
  for s: World
  for r: R
  for takes: List<&2, Nat>
  for +got: Bytes()
  for fins: Nat
  for +held: Bytes()
  for eof: Bool
  for stalled: Bool
  {sb.moved(R, Bs.pass.stall(World, R, Snk, s, r, Snk{takes, got, fins}, held, eof, stalled)) ==
    (s, (Bytes.append(got, held), fins)) : World & Bytes() & Nat}

def wl.stall_moved(R, s, r, takes, got, fins, held, eof, stalled):
  match stalled:
    case True{}:
      {==}
    case False{}:
      {==}

# a consumer that took n of what was held: taken, then held, is as before
law wl.took_moved:
  for -R: Data
  for s: World
  for r: R
  for takes: List<&2, Nat>
  for +got: Bytes()
  for fins: Nat
  for +held: Bytes()
  for +n: Nat
  for eof: Bool
  for stalled: Bool
  {sb.moved(R, Bs.pass.stall(World, R, Snk, s, r, Snk{takes, Bytes.append(got,
    String.take(held, n)), fins}, String.drop(held, n), eof, stalled)) ==
    (s, (Bytes.append(got, held), fins)) : World & Bytes() & Nat}

def wl.took_moved(R, s, r, takes, got, fins, held, n, eof, stalled):
  Equal.trans(World & Bytes() & Nat,
    sb.moved(R, Bs.pass.stall(World, R, Snk, s, r, Snk{takes, Bytes.append(got,
      String.take(held, n)), fins}, String.drop(held, n), eof, stalled)),
    (s, (Bytes.append(Bytes.append(got, String.take(held, n)), String.drop(held, n)), fins)),
    (s, (Bytes.append(got, held), fins)),
    wl.stall_moved(R, s, r, takes, Bytes.append(got, String.take(held, n)), fins,
      String.drop(held, n), eof, stalled),
    Equal.cong(Bytes(), World & Bytes() & Nat, y => (s, (y, fins)),
      Bytes.append(Bytes.append(got, String.take(held, n)), String.drop(held, n)),
      Bytes.append(got, held),
      Equal.trans(Bytes(),
        Bytes.append(Bytes.append(got, String.take(held, n)), String.drop(held, n)),
        Bytes.append(got, Bytes.append(String.take(held, n), String.drop(held, n))),
        Bytes.append(got, held),
        wl.app_assoc(got, String.take(held, n), String.drop(held, n)),
        Equal.cong(Bytes(), Bytes(), y => Bytes.append(got, y),
          Bytes.append(String.take(held, n), String.drop(held, n)), held, wl.take_drop(held, n)))))

law stream_pass:
  for ~R: Data
  for ~look: R -> Bs.Stage
  for +win: Nat
  for s: World
  for +r: R
  for takes: List<&2, Nat>
  for +got: Bytes()
  for fins: Nat
  for +held: Bytes()
  for +eof: Bool
  {sb.moved(R, sb.pass(~R, ~look, win, Bs.Bq{s, r, Snk{takes, got, fins}, held, eof})) ==
    (s, (Bytes.append(got, held), fins)) : World & Bytes() & Nat}

def stream_pass(R, look, win, s, r, takes, got, fins, held, eof):
  match takes held:
    case Nil{} SNil{}:
      {==}
    case Con{n, t} SNil{}:
      {==}
    case Nil{} SCon{+h, +t}:
      wl.took_moved(R, s, r, Nil{}, got, fins, SCon{h, t}, Bytes.len(SCon{h, t}), eof,
        Nat.is_eq(Bytes.len(SCon{h, t}), 0n) && (Nat.is_le(win, Bytes.len(SCon{h, t}))
          || Bool.not(Bs.more(look(r), eof))))
    case Con{+n, tk} SCon{+h, +t}:
      wl.took_moved(R, s, r, tk, got, fins, SCon{h, t}, n, eof,
        Nat.is_eq(n, 0n) && (Nat.is_le(win, Bytes.len(SCon{h, t}))
          || Bool.not(Bs.more(look(r), eof))))

# LAW: a stalled consumer stops reads. With a window's worth held or
# more, a consumer that takes none of it ends the stream: the turn's
# pull never runs, the socket is not read, and nothing more is held.
law stream_stall:
  for ~E: Data
  for ~R: Data
  for ~feed: E -> Bytes() -> R -> R
  for ~take: R -> R & Bytes()
  for ~look: R -> Bs.Stage
  for +e: E
  for +win: Nat
  for +ms: U32
  for s: World
  for +r: R
  for rest: List<&2, Nat>
  for +got: Bytes()
  for fins: Nat
  for +h: Char
  for +t: Bytes()
  for +eof: Bool
  for full: {Nat.is_le(win, Bytes.len(SCon{h, t})) == True{} : Bool}
  {sb.turn(~E, ~R, ~feed, ~take, ~look, e, win, ms,
      Bs.Bq{s, r, Snk{Con{0n, rest}, got, fins}, SCon{h, t}, eof}) ==
    (Bs.Bq{s, r, Snk{rest, Bytes.append(got, ""), fins}, SCon{h, t}, eof}, Some{Bs.BStall{}}) :
    Bs.Turn(World, R, Snk)}

def stream_stall(E, R, feed, take, look, e, win, ms, s, r, rest, got, fins, h, t, eof, full):
  %Equal.sym(Bool, Nat.is_le(win, Bytes.len(SCon{h, t})), True{}, full) :
    {Bs.turn.then(~Id, ~Id.pure, ~Id.bind, ~World, ~w.rx, ~E, ~R, ~feed, ~take, ~look, ~Snk,
      ~k.fin, e, win, ms, Bs.pass.stall(World, R, Snk, s, r, Snk{rest, Bytes.append(got, ""), fins},
        SCon{h, t}, eof, _ || Bool.not(Bs.more(look(r), eof)))) ==
      (Bs.Bq{s, r, Snk{rest, Bytes.append(got, ""), fins}, SCon{h, t}, eof}, Some{Bs.BStall{}}) :
      Bs.Turn(World, R, Snk)}
  {==}

# LAW: a full window stops reads. With win bytes or more held and the
# body still coming, a pull reads nothing and holds what it held.
law stream_full:
  for ~E: Data
  for ~R: Data
  for ~feed: E -> Bytes() -> R -> R
  for ~take: R -> R & Bytes()
  for ~look: R -> Bs.Stage
  for +e: E
  for +win: Nat
  for +ms: U32
  for s: World
  for +r: R
  for k: Snk
  for +held: Bytes()
  for st: Bs.Stage
  for es: {look(r) == st : Bs.Stage}
  for em: {Bs.more(st, False{}) == True{} : Bool}
  for full: {Nat.is_lt(Bytes.len(held), win) == False{} : Bool}
  {sb.pull(~E, ~R, ~feed, ~take, ~look, e, win, ms, Bs.Bq{s, r, k, held, False{}}) ==
    (Bs.Bq{s, r, k, held, False{}}, None{}) : Bs.Turn(World, R, Snk)}

def stream_full(E, R, feed, take, look, e, win, ms, s, r, k, held, st, es, em, full):
  match st:
    case Bs.Going{}:
      %Equal.sym(Bs.Stage, look(r), Bs.Going{}, es) :
        {Bs.pull.go(~Id, ~Id.pure, ~Id.bind, ~World, ~w.rx, ~E, ~R, ~feed, ~take, ~Snk, ~k.fin,
          e, win, ms, _, False{}, s, r, k, held) == (Bs.Bq{s, r, k, held, False{}}, None{}) :
          Bs.Turn(World, R, Snk)}
      %Equal.sym(Bool, Nat.is_lt(Bytes.len(held), win), False{}, full) :
        {Bs.pull.room(~Id, ~Id.pure, ~Id.bind, ~World, ~w.rx, ~E, ~R, ~feed, ~take, ~Snk, e, ms,
          s, r, k, held, False{}, _) == (Bs.Bq{s, r, k, held, False{}}, None{}) :
          Bs.Turn(World, R, Snk)}
      {==}
    case Bs.Closing{}:
      %Equal.sym(Bs.Stage, look(r), Bs.Closing{}, es) :
        {Bs.pull.go(~Id, ~Id.pure, ~Id.bind, ~World, ~w.rx, ~E, ~R, ~feed, ~take, ~Snk, ~k.fin,
          e, win, ms, _, False{}, s, r, k, held) == (Bs.Bq{s, r, k, held, False{}}, None{}) :
          Bs.Turn(World, R, Snk)}
      %Equal.sym(Bool, Nat.is_lt(Bytes.len(held), win), False{}, full) :
        {Bs.pull.room(~Id, ~Id.pure, ~Id.bind, ~World, ~w.rx, ~E, ~R, ~feed, ~take, ~Snk, e, ms,
          s, r, k, held, False{}, _) == (Bs.Bq{s, r, k, held, False{}}, None{}) :
          Bs.Turn(World, R, Snk)}
      {==}
    case Bs.Ended{}:
      no({sb.pull(~E, ~R, ~feed, ~take, ~look, e, win, ms, Bs.Bq{s, r, k, held, False{}}) ==
        (Bs.Bq{s, r, k, held, False{}}, None{}) : Bs.Turn(World, R, Snk)}, em)
    case Bs.Refused{}:
      no({sb.pull(~E, ~R, ~feed, ~take, ~look, e, win, ms, Bs.Bq{s, r, k, held, False{}}) ==
        (Bs.Bq{s, r, k, held, False{}}, None{}) : Bs.Turn(World, R, Snk)}, em)

# LAW: a read joins the body at the end of what is held, exactly. With
# room in the window and the body still coming, a pull reads the
# peer's next bytes, feeds them to the framer, and holds what the
# framer then holds of the body after what it held before -- the bytes
# drain_reads says are the body's, in their order -- and the framer
# goes on holding none.
law wl.fed_ok:
  for -R: Data
  for s: World
  for q: R & Bytes()
  for k: Snk
  for +held: Bytes()
  for +n: Nat
  for ok: {Nat.is_le(Bytes.len(sb.qb(R, q)), n) == True{} : Bool}
  {Bs.pull.fed(World, R, Snk, s, q, k, held, False{}, n) ==
    (Bs.Bq{s, sb.qs(R, q), k, Bytes.append(held, sb.qb(R, q)), False{}}, None{}) :
    Bs.Turn(World, R, Snk)}

def wl.fed_ok(R, s, q, k, held, n, ok):
  (r, +x) = q
  %Equal.sym(Bool, Nat.is_le(Bytes.len(x), n), True{}, ok) :
    {Bs.pull.fits(World, R, Snk, s, r, k, held, x, False{}, _) ==
      (Bs.Bq{s, r, k, Bytes.append(held, x), False{}}, None{}) : Bs.Turn(World, R, Snk)}
  {==}

law wl.room_read:
  for ~E: Data
  for ~R: Data
  for ~feed: E -> Bytes() -> R -> R
  for ~take: R -> R & Bytes()
  for +e: E
  for +ms: U32
  for +r: R
  for k: Snk
  for +held: Bytes()
  for +wait: Nat
  for +h: Char
  for +t: Bytes()
  for rd: List<&2, Rd>
  for wr: List<&2, Wr>
  for eager: Bool
  for +now: Nat
  for fs: List<&2, Fil>
  for out: Bytes()
  for ew: {Nat.is_lt(wait, U32.to_nat(ms)) == True{} : Bool}
  for q: R & Bytes()
  for eq: {take(feed(e, SCon{h, t}, r)) == q : R & Bytes()}
  for ok: {Nat.is_le(Bytes.len(sb.qb(R, q)), Bytes.len(SCon{h, t})) == True{} : Bool}
  {Bs.pull.room(~Id, ~Id.pure, ~Id.bind, ~World, ~w.rx, ~E, ~R, ~feed, ~take, ~Snk, e, ms,
      World{Con{Give{wait, SCon{h, t}}, rd}, wr, eager, now, fs, out}, r, k, held, False{}, True{}) ==
    (Bs.Bq{World{rd, wr, eager, Nat.add(now, wait), fs, out}, sb.qs(R, q), k,
      Bytes.append(held, sb.qb(R, q)), False{}}, None{}) : Bs.Turn(World, R, Snk)}

def wl.room_read(E, R, feed, take, e, ms, r, k, held, wait, h, t, rd, wr, eager, now, fs, out, ew, q,
  eq, ok):
  %Equal.sym(Bool, Nat.is_lt(wait, U32.to_nat(ms)), True{}, ew) :
    {Bs.pull.got(~E, ~R, ~feed, ~take, World, Snk, e,
      w.rx.give(rd, wait, SCon{h, t}, ms, wr, eager, now, fs, out, _), r, k, held, False{}) ==
      (Bs.Bq{World{rd, wr, eager, Nat.add(now, wait), fs, out}, sb.qs(R, q), k,
        Bytes.append(held, sb.qb(R, q)), False{}}, None{}) : Bs.Turn(World, R, Snk)}
  %Equal.sym(R & Bytes(), take(feed(e, SCon{h, t}, r)), q, eq) :
    {Bs.pull.fed(World, R, Snk, World{rd, wr, eager, Nat.add(now, wait), fs, out}, _, k, held,
      False{}, Bytes.len(SCon{h, t})) ==
      (Bs.Bq{World{rd, wr, eager, Nat.add(now, wait), fs, out}, sb.qs(R, q), k,
        Bytes.append(held, sb.qb(R, q)), False{}}, None{}) : Bs.Turn(World, R, Snk)}
  wl.fed_ok(R, World{rd, wr, eager, Nat.add(now, wait), fs, out}, q, k, held,
    Bytes.len(SCon{h, t}), ok)

law stream_pull:
  for ~E: Data
  for ~R: Data
  for ~feed: E -> Bytes() -> R -> R
  for ~take: R -> R & Bytes()
  for ~look: R -> Bs.Stage
  for +e: E
  for +win: Nat
  for +ms: U32
  for +r: R
  for k: Snk
  for +held: Bytes()
  for st: Bs.Stage
  for es: {look(r) == st : Bs.Stage}
  for em: {Bs.more(st, False{}) == True{} : Bool}
  for room: {Nat.is_lt(Bytes.len(held), win) == True{} : Bool}
  for +wait: Nat
  for +h: Char
  for +t: Bytes()
  for rd: List<&2, Rd>
  for wr: List<&2, Wr>
  for eager: Bool
  for +now: Nat
  for fs: List<&2, Fil>
  for out: Bytes()
  for ew: {Nat.is_lt(wait, U32.to_nat(ms)) == True{} : Bool}
  for q: R & Bytes()
  for eq: {take(feed(e, SCon{h, t}, r)) == q : R & Bytes()}
  for ok: {Nat.is_le(Bytes.len(sb.qb(R, q)), Bytes.len(SCon{h, t})) == True{} : Bool}
  {sb.pull(~E, ~R, ~feed, ~take, ~look, e, win, ms,
      Bs.Bq{World{Con{Give{wait, SCon{h, t}}, rd}, wr, eager, now, fs, out}, r, k, held, False{}}) ==
    (Bs.Bq{World{rd, wr, eager, Nat.add(now, wait), fs, out}, sb.qs(R, q), k,
      Bytes.append(held, sb.qb(R, q)), False{}}, None{}) : Bs.Turn(World, R, Snk)}

def stream_pull(E, R, feed, take, look, e, win, ms, r, k, held, st, es, em, room, wait, h, t, rd, wr,
  eager, now, fs, out, ew, q, eq, ok):
  match st:
    case Bs.Going{}:
      %Equal.sym(Bs.Stage, look(r), Bs.Going{}, es) :
        {Bs.pull.go(~Id, ~Id.pure, ~Id.bind, ~World, ~w.rx, ~E, ~R, ~feed, ~take, ~Snk, ~k.fin,
          e, win, ms, _, False{}, World{Con{Give{wait, SCon{h, t}}, rd}, wr, eager, now, fs, out}, r,
          k, held) ==
          (Bs.Bq{World{rd, wr, eager, Nat.add(now, wait), fs, out}, sb.qs(R, q), k,
            Bytes.append(held, sb.qb(R, q)), False{}}, None{}) : Bs.Turn(World, R, Snk)}
      %Equal.sym(Bool, Nat.is_lt(Bytes.len(held), win), True{}, room) :
        {Bs.pull.room(~Id, ~Id.pure, ~Id.bind, ~World, ~w.rx, ~E, ~R, ~feed, ~take, ~Snk, e, ms,
          World{Con{Give{wait, SCon{h, t}}, rd}, wr, eager, now, fs, out}, r, k, held, False{}, _) ==
          (Bs.Bq{World{rd, wr, eager, Nat.add(now, wait), fs, out}, sb.qs(R, q), k,
            Bytes.append(held, sb.qb(R, q)), False{}}, None{}) : Bs.Turn(World, R, Snk)}
      wl.room_read(~E, ~R, ~feed, ~take, e, ms, r, k, held, wait, h, t, rd, wr, eager, now, fs, out,
        ew, q, eq, ok)
    case Bs.Closing{}:
      %Equal.sym(Bs.Stage, look(r), Bs.Closing{}, es) :
        {Bs.pull.go(~Id, ~Id.pure, ~Id.bind, ~World, ~w.rx, ~E, ~R, ~feed, ~take, ~Snk, ~k.fin,
          e, win, ms, _, False{}, World{Con{Give{wait, SCon{h, t}}, rd}, wr, eager, now, fs, out}, r,
          k, held) ==
          (Bs.Bq{World{rd, wr, eager, Nat.add(now, wait), fs, out}, sb.qs(R, q), k,
            Bytes.append(held, sb.qb(R, q)), False{}}, None{}) : Bs.Turn(World, R, Snk)}
      %Equal.sym(Bool, Nat.is_lt(Bytes.len(held), win), True{}, room) :
        {Bs.pull.room(~Id, ~Id.pure, ~Id.bind, ~World, ~w.rx, ~E, ~R, ~feed, ~take, ~Snk, e, ms,
          World{Con{Give{wait, SCon{h, t}}, rd}, wr, eager, now, fs, out}, r, k, held, False{}, _) ==
          (Bs.Bq{World{rd, wr, eager, Nat.add(now, wait), fs, out}, sb.qs(R, q), k,
            Bytes.append(held, sb.qb(R, q)), False{}}, None{}) : Bs.Turn(World, R, Snk)}
      wl.room_read(~E, ~R, ~feed, ~take, e, ms, r, k, held, wait, h, t, rd, wr, eager, now, fs, out,
        ew, q, eq, ok)
    case Bs.Ended{}:
      no({sb.pull(~E, ~R, ~feed, ~take, ~look, e, win, ms,
          Bs.Bq{World{Con{Give{wait, SCon{h, t}}, rd}, wr, eager, now, fs, out}, r, k, held, False{}}) ==
        (Bs.Bq{World{rd, wr, eager, Nat.add(now, wait), fs, out}, sb.qs(R, q), k,
          Bytes.append(held, sb.qb(R, q)), False{}}, None{}) : Bs.Turn(World, R, Snk)}, em)
    case Bs.Refused{}:
      no({sb.pull(~E, ~R, ~feed, ~take, ~look, e, win, ms,
          Bs.Bq{World{Con{Give{wait, SCon{h, t}}, rd}, wr, eager, now, fs, out}, r, k, held, False{}}) ==
        (Bs.Bq{World{rd, wr, eager, Nat.add(now, wait), fs, out}, sb.qs(R, q), k,
          Bytes.append(held, sb.qb(R, q)), False{}}, None{}) : Bs.Turn(World, R, Snk)}, em)

# LAW: the window. A read is taken only with fewer than win bytes held
# (stream_full), and adds no more body than it brought bytes (the
# pull's own check), so what a stream holds after it is under the
# window plus that read: with reads at most Bs.chunk() bytes, a stream
# never holds more than win + chunk() of a body, however large the
# body and however slow its consumer.
def wl.lt_succ(+x: Nat, +m: Nat, e: {Nat.is_le(x, m) == True{} : Bool}) ->
  {Nat.is_lt(x, 1n+m) == True{} : Bool}:
  match x m:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      no({Nat.is_lt(1n+p, 1n) == True{} : Bool}, e)
    case 1n+p 1n+q:
      wl.lt_succ(p, q, e)

def wl.le_up(+x: Nat, +m: Nat, e: {Nat.is_le(x, m) == True{} : Bool}) ->
  {Nat.is_le(x, 1n+m) == True{} : Bool}:
  wl.lt_le(x, 1n+m, wl.lt_succ(x, m, e))

def wl.le_addl(+w: Nat, +x: Nat, +n: Nat, e: {Nat.is_le(x, n) == True{} : Bool}) ->
  {Nat.is_le(x, Nat.add(w, n)) == True{} : Bool}:
  match w:
    case 0n:
      e
    case 1n+p:
      wl.le_up(x, Nat.add(p, n), wl.le_addl(p, x, n, e))

def wl.lt_add(+a: Nat, +w: Nat, +x: Nat, +n: Nat, e1: {Nat.is_lt(a, w) == True{} : Bool},
  e2: {Nat.is_le(x, n) == True{} : Bool}) -> {Nat.is_lt(Nat.add(a, x), Nat.add(w, n)) == True{} : Bool}:
  match a w:
    case 0n 0n:
      no({Nat.is_lt(x, n) == True{} : Bool}, e1)
    case 0n 1n+q:
      wl.lt_succ(x, Nat.add(q, n), wl.le_addl(q, x, n, e2))
    case 1n+p 0n:
      no({Nat.is_lt(1n+Nat.add(p, x), n) == True{} : Bool}, e1)
    case 1n+p 1n+q:
      wl.lt_add(p, q, x, n, e1, e2)

law stream_window:
  for +held: Bytes()
  for +x: Bytes()
  for +win: Nat
  for +n: Nat
  for room: {Nat.is_lt(Bytes.len(held), win) == True{} : Bool}
  for ok: {Nat.is_le(Bytes.len(x), n) == True{} : Bool}
  {Nat.is_lt(Bytes.len(Bytes.append(held, x)), Nat.add(win, n)) == True{} : Bool}

def stream_window(held, x, win, n, room, ok):
  %Equal.sym(Nat, Bytes.len(Bytes.append(held, x)), Nat.add(Bytes.len(held), Bytes.len(x)),
    Bytes.len_append(held, x)) :
    {Nat.is_lt(_, Nat.add(win, n)) == True{} : Bool}
  wl.lt_add(Bytes.len(held), win, Bytes.len(x), n, room, ok)

# LAW: the end is told once, after the last byte. A pull tells the
# consumer the body is over only when the framer says so and nothing
# is held (so after every byte was taken), and the stream ends with it;
# while bytes are held, no pull tells it, and no pass ever does
# (stream_pass).
def sb.run(
  ~E: Data, ~R: Data, ~feed: E -> Bytes() -> R -> R, ~take: R -> R & Bytes(),
  ~look: R -> Bs.Stage, +e: E, +win: Nat, +ms: U32, n: Nat, bq: Bs.Bq<World, R, Snk>
) -> Bs.Bq<World, R, Snk> & Bs.Why:
  Bs.run(~Id, ~Id.pure, ~Id.bind, ~World, ~w.rx, ~E, ~R, ~feed, ~take, ~look, ~Snk, ~k.give,
    ~k.fin, e, win, ms, n, bq)

law stream_fin_last:
  for ~E: Data
  for ~R: Data
  for ~feed: E -> Bytes() -> R -> R
  for ~take: R -> R & Bytes()
  for ~look: R -> Bs.Stage
  for +e: E
  for +win: Nat
  for +ms: U32
  for n: Nat
  for s: World
  for +r: R
  for takes: List<&2, Nat>
  for got: Bytes()
  for fins: Nat
  for +eof: Bool
  for es: {look(r) == Bs.Ended{} : Bs.Stage}
  {sb.run(~E, ~R, ~feed, ~take, ~look, e, win, ms, 1n+n, Bs.Bq{s, r, Snk{takes, got, fins}, "", eof}) ==
    (Bs.Bq{s, r, Snk{takes, got, 1n+fins}, "", eof}, Bs.BDone{}) :
    Bs.Bq<World, R, Snk> & Bs.Why}

def stream_fin_last(E, R, feed, take, look, e, win, ms, n, s, r, takes, got, fins, eof, es):
  %Equal.sym(Bs.Stage, look(r), Bs.Ended{}, es) :
    {Bs.run.next(~Id, ~Id.pure, World, R, Snk,
      Bs.pull.go(~Id, ~Id.pure, ~Id.bind, ~World, ~w.rx, ~E, ~R, ~feed, ~take, ~Snk, ~k.fin, e,
        win, ms, _, eof, s, r, Snk{takes, got, fins}, ""),
      b => Bs.run(~Id, ~Id.pure, ~Id.bind, ~World, ~w.rx, ~E, ~R, ~feed, ~take, ~look, ~Snk,
        ~k.give, ~k.fin, e, win, ms, n, b)) ==
      (Bs.Bq{s, r, Snk{takes, got, 1n+fins}, "", eof}, Bs.BDone{}) :
      Bs.Bq<World, R, Snk> & Bs.Why}
  {==}

def wl.fits_fins(-R: Data, s: World, r: R, takes: List<&2, Nat>, got: Bytes(), fins: Nat,
  +held: Bytes(), +x: Bytes(), eof: Bool, ok: Bool) ->
  {sb.fins(R, Bs.pull.fits(World, R, Snk, s, r, Snk{takes, got, fins}, held, x, eof, ok)) ==
    fins : Nat}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def wl.fed_fins(-R: Data, s: World, q: R & Bytes(), takes: List<&2, Nat>, got: Bytes(),
  fins: Nat, +held: Bytes(), eof: Bool, +n: Nat) ->
  {sb.fins(R, Bs.pull.fed(World, R, Snk, s, q, Snk{takes, got, fins}, held, eof, n)) ==
    fins : Nat}:
  (r, +x) = q
  wl.fits_fins(R, s, r, takes, got, fins, held, x, eof, Nat.is_le(Bytes.len(x), n))

def wl.bytes_fins(~E: Data, ~R: Data, ~feed: E -> Bytes() -> R -> R, ~take: R -> R & Bytes(),
  +e: E, s: World, r: R, takes: List<&2, Nat>, got: Bytes(), fins: Nat, +held: Bytes(),
  eof: Bool, empty: Bool, +bs: Bytes()) ->
  {sb.fins(R, Bs.pull.bytes(~E, ~R, ~feed, ~take, World, Snk, e, s, r, Snk{takes, got, fins},
    held, eof, empty, bs)) == fins : Nat}:
  match empty:
    case True{}:
      {==}
    case False{}:
      wl.fed_fins(R, s, take(feed(e, bs, r)), takes, got, fins, held, eof, Bytes.len(bs))

def wl.cut_fins(-R: Data, s: World, r: R, takes: List<&2, Nat>, got: Bytes(), fins: Nat,
  held: Bytes(), eof: Bool, er: U32 & String) ->
  {sb.fins(R, Bs.pull.cut(World, R, Snk, s, r, Snk{takes, got, fins}, held, eof, er)) ==
    fins : Nat}:
  (code, msg) = er
  {==}

def wl.got_fins(~E: Data, ~R: Data, ~feed: E -> Bytes() -> R -> R, ~take: R -> R & Bytes(),
  +e: E, g: L.Got(World), r: R, takes: List<&2, Nat>, got: Bytes(), fins: Nat, +held: Bytes(),
  eof: Bool) ->
  {sb.fins(R, Bs.pull.got(~E, ~R, ~feed, ~take, World, Snk, e, g, r, Snk{takes, got, fins},
    held, eof)) == fins : Nat}:
  (s, res) = g
  match res:
    case Fail{er}:
      wl.cut_fins(R, s, r, takes, got, fins, held, eof, er)
    case Done{may}:
      match may:
        case None{}:
          {==}
        case Some{+bs}:
          wl.bytes_fins(~E, ~R, ~feed, ~take, e, s, r, takes, got, fins, held, eof,
            String.is_empty(bs), bs)

def wl.room_fins(~E: Data, ~R: Data, ~feed: E -> Bytes() -> R -> R, ~take: R -> R & Bytes(),
  +e: E, +ms: U32, s: World, r: R, takes: List<&2, Nat>, got: Bytes(), fins: Nat,
  +held: Bytes(), room: Bool) ->
  {sb.fins(R, Bs.pull.room(~Id, ~Id.pure, ~Id.bind, ~World, ~w.rx, ~E, ~R, ~feed, ~take, ~Snk,
    e, ms, s, r, Snk{takes, got, fins}, held, False{}, room)) == fins : Nat}:
  match room:
    case False{}:
      {==}
    case True{}:
      wl.got_fins(~E, ~R, ~feed, ~take, e, w.rx(s, Bs.chunk(), ms), r, takes, got, fins, held,
        False{})

def wl.go_fins(~E: Data, ~R: Data, ~feed: E -> Bytes() -> R -> R, ~take: R -> R & Bytes(),
  +e: E, +win: Nat, +ms: U32, st: Bs.Stage, eof: Bool, s: World, r: R, takes: List<&2, Nat>,
  got: Bytes(), fins: Nat, +h: Char, +t: Bytes()) ->
  {sb.fins(R, Bs.pull.go(~Id, ~Id.pure, ~Id.bind, ~World, ~w.rx, ~E, ~R, ~feed, ~take, ~Snk,
    ~k.fin, e, win, ms, st, eof, s, r, Snk{takes, got, fins}, SCon{h, t})) == fins : Nat}:
  match st eof:
    case Bs.Refused{} _:
      {==}
    case Bs.Ended{} _:
      {==}
    case Bs.Closing{} True{}:
      {==}
    case Bs.Going{} True{}:
      {==}
    case Bs.Closing{} False{}:
      wl.room_fins(~E, ~R, ~feed, ~take, e, ms, s, r, takes, got, fins, SCon{h, t},
        Nat.is_lt(Bytes.len(SCon{h, t}), win))
    case Bs.Going{} False{}:
      wl.room_fins(~E, ~R, ~feed, ~take, e, ms, s, r, takes, got, fins, SCon{h, t},
        Nat.is_lt(Bytes.len(SCon{h, t}), win))

law stream_fin_held:
  for ~E: Data
  for ~R: Data
  for ~feed: E -> Bytes() -> R -> R
  for ~take: R -> R & Bytes()
  for ~look: R -> Bs.Stage
  for +e: E
  for +win: Nat
  for +ms: U32
  for s: World
  for +r: R
  for takes: List<&2, Nat>
  for got: Bytes()
  for fins: Nat
  for +h: Char
  for +t: Bytes()
  for st: Bs.Stage
  for eof: Bool
  for es: {look(r) == st : Bs.Stage}
  {sb.fins(R, sb.pull(~E, ~R, ~feed, ~take, ~look, e, win, ms,
    Bs.Bq{s, r, Snk{takes, got, fins}, SCon{h, t}, eof})) == fins : Nat}

def stream_fin_held(E, R, feed, take, look, e, win, ms, s, r, takes, got, fins, h, t, st, eof, es):
  %Equal.sym(Bs.Stage, look(r), st, es) :
    {sb.fins(R, Bs.pull.go(~Id, ~Id.pure, ~Id.bind, ~World, ~w.rx, ~E, ~R, ~feed, ~take, ~Snk,
      ~k.fin, e, win, ms, _, eof, s, r, Snk{takes, got, fins}, SCon{h, t})) == fins : Nat}
  wl.go_fins(~E, ~R, ~feed, ~take, e, win, ms, st, eof, s, r, takes, got, fins, h, t)

# LAW: a read never brings more body than it brought bytes. When the
# framer holds more body after a read than the read had bytes (no
# framer on the kit does; a faulty one might), the stream ends there,
# holding what it held, rather than grow past its window.
law wl.fed_over:
  for -R: Data
  for s: World
  for q: R & Bytes()
  for k: Snk
  for +held: Bytes()
  for +n: Nat
  for over: {Nat.is_le(Bytes.len(sb.qb(R, q)), n) == False{} : Bool}
  {Bs.pull.fed(World, R, Snk, s, q, k, held, False{}, n) ==
    (Bs.Bq{s, sb.qs(R, q), k, held, False{}}, Some{Bs.BOver{}}) : Bs.Turn(World, R, Snk)}

def wl.fed_over(R, s, q, k, held, n, over):
  (r, +x) = q
  %Equal.sym(Bool, Nat.is_le(Bytes.len(x), n), False{}, over) :
    {Bs.pull.fits(World, R, Snk, s, r, k, held, x, False{}, _) ==
      (Bs.Bq{s, r, k, held, False{}}, Some{Bs.BOver{}}) : Bs.Turn(World, R, Snk)}
  {==}

law stream_over:
  for ~E: Data
  for ~R: Data
  for ~feed: E -> Bytes() -> R -> R
  for ~take: R -> R & Bytes()
  for +e: E
  for +ms: U32
  for +r: R
  for k: Snk
  for +held: Bytes()
  for +wait: Nat
  for +h: Char
  for +t: Bytes()
  for rd: List<&2, Rd>
  for wr: List<&2, Wr>
  for eager: Bool
  for +now: Nat
  for fs: List<&2, Fil>
  for out: Bytes()
  for ew: {Nat.is_lt(wait, U32.to_nat(ms)) == True{} : Bool}
  for q: R & Bytes()
  for eq: {take(feed(e, SCon{h, t}, r)) == q : R & Bytes()}
  for over: {Nat.is_le(Bytes.len(sb.qb(R, q)), Bytes.len(SCon{h, t})) == False{} : Bool}
  {Bs.pull.room(~Id, ~Id.pure, ~Id.bind, ~World, ~w.rx, ~E, ~R, ~feed, ~take, ~Snk, e, ms,
      World{Con{Give{wait, SCon{h, t}}, rd}, wr, eager, now, fs, out}, r, k, held, False{}, True{}) ==
    (Bs.Bq{World{rd, wr, eager, Nat.add(now, wait), fs, out}, sb.qs(R, q), k, held, False{}},
      Some{Bs.BOver{}}) : Bs.Turn(World, R, Snk)}

def stream_over(E, R, feed, take, e, ms, r, k, held, wait, h, t, rd, wr, eager, now, fs, out, ew, q,
  eq, over):
  %Equal.sym(Bool, Nat.is_lt(wait, U32.to_nat(ms)), True{}, ew) :
    {Bs.pull.got(~E, ~R, ~feed, ~take, World, Snk, e,
      w.rx.give(rd, wait, SCon{h, t}, ms, wr, eager, now, fs, out, _), r, k, held, False{}) ==
      (Bs.Bq{World{rd, wr, eager, Nat.add(now, wait), fs, out}, sb.qs(R, q), k, held, False{}},
        Some{Bs.BOver{}}) : Bs.Turn(World, R, Snk)}
  %Equal.sym(R & Bytes(), take(feed(e, SCon{h, t}, r)), q, eq) :
    {Bs.pull.fed(World, R, Snk, World{rd, wr, eager, Nat.add(now, wait), fs, out}, _, k, held,
      False{}, Bytes.len(SCon{h, t})) ==
      (Bs.Bq{World{rd, wr, eager, Nat.add(now, wait), fs, out}, sb.qs(R, q), k, held, False{}},
        Some{Bs.BOver{}}) : Bs.Turn(World, R, Snk)}
  wl.fed_over(R, World{rd, wr, eager, Nat.add(now, wait), fs, out}, q, k, held,
    Bytes.len(SCon{h, t}), over)
