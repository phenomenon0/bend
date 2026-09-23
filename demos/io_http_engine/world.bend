# The engine in the world: bend-wire's model (wire/world.bend) at the
# engine's hooks.
#
# The connection loop and the accept loop are bend-wire's, written once
# over an effect interface (wire/loop.bend) and modelled once, with the
# identity monad and a scripted peer, in wire/world.bend, where the laws
# of the loops are proven for every protocol. This file instantiates
# that model at the engine's hooks (main.bend's h.* and the rest), so
# LAWS.bend can state, and PROOF.bend prove as instances, what the loops
# do to every peer when they run this engine; and it writes down what
# is the engine's own: the replies a read's requests are owed, and the
# 400 that answers a grammar that broke.
import Base
import ../../wire/loop.bend as L
import ../../wire/world.bend as WW
import ./main.bend as Eng
import ./ws.bend as Ws

# The loop in the model, at the engine's hooks
# ============================================

def sim.segs(s: WW.World, xs: List<&2, L.Seg>, +ms: U32) -> L.Put(WW.World):
  WW.sim.segs(~Eng.h.shut, ~Eng.h.fhead, ~Eng.miss, ~Eng.h.lnote, ~Eng.h.lsize, s, xs, ms)

def sim.hold(+ms: U32, s: WW.World, +acc: Bytes()) -> L.Em<WW.World>:
  WW.sim.hold(ms, s, acc)

def sim.raw(+ms: U32, may: Maybe<&2, Bytes()>, bs: Bytes(), st: L.Em<WW.World>) ->
  L.Em<WW.World>:
  WW.sim.raw(~Eng.h.lnote, ms, may, bs, st)

def sim.page(
  +ms: U32, root: List<&2, U32>, path: List<&2, U32>, ct: List<&2, U32>, head: Bool,
  may: Maybe<&2, Bytes()>, sh: Bool, st: L.Em<WW.World>
) -> L.Em<WW.World>:
  WW.sim.page(~Eng.h.shut, ~Eng.h.fhead, ~Eng.miss, ~Eng.h.lnote, ~Eng.h.lsize, ms, root, path,
    ct, head, may, sh, st)

def sim.turn.h(+srv: Eng.Srv, s: WW.World, p: Eng.P, hw: L.Hw) ->
  (WW.World & Eng.Plan()) & L.Hw:
  WW.sim.turn.h(~Eng.Srv, ~Eng.P, ~Ws.W, ~Eng.srv.idle, ~Eng.srv.head, ~Eng.h.plan,
    ~Eng.resp.big(), srv, s, p, hw)

def sim.turn(+srv: Eng.Srv, m: L.Put(WW.World), p: Eng.P, hw: L.Hw) ->
  (WW.World & Eng.Plan()) & L.Hw:
  WW.sim.turn(~Eng.Srv, ~Eng.P, ~Ws.W, ~Eng.srv.idle, ~Eng.srv.head, ~Eng.h.plan,
    ~Eng.resp.big(), srv, m, p, hw)

def sim.turn.ws(+srv: Eng.Srv, m: L.Put(WW.World), wr: Ws.W) -> WW.World & Eng.Plan():
  WW.sim.turn.up(~Eng.Srv, ~Eng.P, ~Ws.W, ~Eng.srv.idle, ~Eng.plan.ws, srv, m, wr)

def sim.tick(m: L.Put(WW.World), n: U32) -> WW.World & Eng.Plan():
  WW.sim.tick(~Eng.P, ~Ws.W, ~Eng.sse.gap(), ~Eng.sse.event, m, n)

def sim.conn(f: Nat, +srv: Eng.Srv, sph: (WW.World & Eng.Plan()) & L.Hw, w: Nat) -> WW.World:
  WW.sim.conn(~Eng.Srv, ~Eng.P, ~Ws.W, ~Eng.srv.idle, ~Eng.srv.head, ~Eng.h.plan, ~Eng.h.mid,
    ~Eng.resp.big(), ~Eng.plan.ws, ~Eng.sse.gap(), ~Eng.sse.event, ~Eng.h.shut, ~Eng.h.fhead,
    ~Eng.miss, ~Eng.h.lnote, ~Eng.h.lsize, f, srv, sph, w)

def sim.start(+srv: Eng.Srv, s: WW.World) -> WW.World:
  WW.sim.start(~Eng.Srv, ~Eng.P, ~Ws.W, ~Eng.srv.idle, ~Eng.srv.head, ~Eng.h.plan, ~Eng.h.mid,
    ~Eng.resp.big(), ~Eng.plan.ws, ~Eng.sse.gap(), ~Eng.sse.event, ~Eng.h.shut, ~Eng.h.fhead,
    ~Eng.miss, ~Eng.h.lnote, ~Eng.h.lsize, srv, Eng.p.new(), s)

def mute.conn(f: Nat, +srv: Eng.Srv, sph: (WW.World & Eng.Plan()) & L.Hw, w: Nat) -> WW.World:
  WW.mute.conn(~Eng.Srv, ~Eng.P, ~Ws.W, ~Eng.srv.idle, ~Eng.srv.head, ~Eng.h.plan, ~Eng.h.mid,
    ~Eng.resp.big(), ~Eng.plan.ws, ~Eng.sse.gap(), ~Eng.sse.event, ~Eng.h.shut, ~Eng.h.fhead,
    ~Eng.miss, ~Eng.h.lnote, ~Eng.h.lsize, f, srv, sph, w)

# the head's budget after one read, and the watch it leaves
def plan.counted(
  +srv: Eng.Srv, w: WW.World, may: Maybe<&1, Bytes()>, p: Eng.P, t0: Nat, n: U32
) -> (WW.World & Eng.Plan()) & L.Hw:
  L.plan.counted(~Eng.Srv, ~Eng.P, ~Ws.W, ~Eng.h.plan, ~Eng.resp.big(), WW.World, srv, w, may, p,
    t0, n)

def hw.of(q: (WW.World & Eng.Plan()) & L.Hw) -> L.Hw:
  WW.hw.of(WW.World & Eng.Plan(), q)

# The bytes a list of segments puts on the wire, when the peer takes
# them all: each reply as flat.shut leaves it.
def wire(xs: List<&2, L.Seg>, sh: Bool) -> Bytes():
  WW.wire(~Eng.h.shut, xs, sh)

# The engine's obligation to the loop's liveness law (stall_ends): an
# event of a stream, framed, is never empty, so its send to a peer that
# has stopped reading fails. It computes: every event begins "data: ".
def event_ok(+n: U32) -> {WW.empty(Eng.h.shut(False{}, Eng.sse.event(n))) == False{} : Bool}:
  {==}

# What is the engine's own
# ========================
#
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

def ag.o(+srv: Eng.Srv, +r: Eng.Req) -> List<&2, L.Seg>:
  Eng.ans.out(Eng.serve(srv, r))

def keeps(+srv: Eng.Srv, +r: Eng.Req) -> Bool:
  Bool.not(ag.c(srv, r) || ag.k(srv, r) || Bool.not(U32.is_zero(ag.s(srv, r))))

def all.keep(+srv: Eng.Srv, rs: List<&2, Eng.Req>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{+r, t}:
      keeps(srv, r) && all.keep(srv, t)

def owed(+srv: Eng.Srv, rs: List<&2, Eng.Req>, tail: List<&2, L.Seg>) -> List<&2, L.Seg>:
  match rs:
    case Nil{}:
      tail
    case Con{+r, t}:
      List.append(&2, L.Seg, ag.o(srv, r), owed(srv, t, tail))

# the 400 that answers a grammar that broke
def bad.reply() -> List<&2, L.Seg>:
  [L.Raw{Eng.resp.bad()}]
