# bend-wire: a pool of idle connections to one upstream.
#
# A connection an exchange left fit to carry another request (wire/
# client.bend's reuse) goes back to its upstream's pool; the next request
# to that upstream takes the newest one that is still fit, or makes a new
# one. The pool is bounded: at most cap connections wait in it, none
# older than age ms, none idle longer than idle ms. And it never hands out
# a connection with something unread on it: each is probed as it is
# taken -- a byte waiting, or the peer's FIN, and it is closed instead.
#
# Written once over the effects, as the loops are:
#
#   ~M, ~pure, ~bind   the monad
#   ~C                 a connection (Socket; in the model, a record)
#   ~probe             whether nothing waits on it: TCP.idle
#   ~close             Socket.close
#
# and instantiated with IO (take, give over sockets) and, for the laws
# below, with the identity monad and model connections that say whether
# they have bytes unread. A connection is an affine value, so one handed
# out is no longer in the pool; the laws say so of the model too, by
# name: nothing in a pool twice, and nothing handed out left in it.
import Base
import ./world.bend as W

# The pool
# ========

# a connection waiting: when it was made, and when it was last used
type Slot<a, -C: Kind(a)> is Kind(a):
  Slot{c: C, born: Nat, last: Nat}

# the bounds, and the connections waiting, newest first
type Pool<a, -C: Kind(a)> is Kind(a):
  Pool{cap: Nat, age: Nat, idle: Nat, xs: List<a, Slot<a, C>>}

def pool.new(a, -C: Kind(a), cap: Nat, age: Nat, idle: Nat) -> Pool<a, C>:
  Pool{cap, age, idle, Nil{}}

# made within age ms and used within idle ms of now
def fresh(+age: Nat, +idle: Nat, +now: Nat, +born: Nat, +last: Nat) -> Bool:
  Nat.is_lt(Nat.sub(now, born), age) && Nat.is_lt(Nat.sub(now, last), idle)

# Taking
# ------
#
# From the newest: a connection past its age or its idle time is closed;
# a fresh one is probed, and handed out if nothing waits on it, closed if
# something does; the ones older than the one handed out stay.

def take.probe(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~a: Quant, ~C: Kind(a), ~close: C -> M(Unit),
  cb: C & Bool, born: Nat, last: Nat, t: List<a, Slot<a, C>>,
  again: List<a, Slot<a, C>> -> M(List<a, Slot<a, C>> & Maybe<a, Slot<a, C>>)
) -> M(List<a, Slot<a, C>> & Maybe<a, Slot<a, C>>):
  (c, ok) = cb
  match ok:
    case True{}:
      pure(List<a, Slot<a, C>> & Maybe<a, Slot<a, C>>, (t, Some{Slot{c, born, last}}))
    case False{}:
      bind(Unit, List<a, Slot<a, C>> & Maybe<a, Slot<a, C>>, close(c), u => again(t))

def take.at(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~a: Quant, ~C: Kind(a),
  ~probe: C -> M(C & Bool), ~close: C -> M(Unit), fr: Bool, c: C, born: Nat, last: Nat,
  t: List<a, Slot<a, C>>, again: List<a, Slot<a, C>> -> M(List<a, Slot<a, C>> & Maybe<a, Slot<a, C>>)
) -> M(List<a, Slot<a, C>> & Maybe<a, Slot<a, C>>):
  match fr:
    case False{}:
      bind(Unit, List<a, Slot<a, C>> & Maybe<a, Slot<a, C>>, close(c), u => again(t))
    case True{}:
      bind(C & Bool, List<a, Slot<a, C>> & Maybe<a, Slot<a, C>>, probe(c), cb =>
        take.probe(~M, ~pure, ~bind, ~a, ~C, ~close, cb, born, last, t, again))

def take.go(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~a: Quant, ~C: Kind(a),
  ~probe: C -> M(C & Bool), ~close: C -> M(Unit), +age: Nat, +idle: Nat, +now: Nat, k: Nat,
  xs: List<a, Slot<a, C>>
) -> M(List<a, Slot<a, C>> & Maybe<a, Slot<a, C>>):
  match k:
    case 0n:
      pure(List<a, Slot<a, C>> & Maybe<a, Slot<a, C>>, (xs, None{}))
    case 1n+j:
      match xs:
        case Nil{}:
          pure(List<a, Slot<a, C>> & Maybe<a, Slot<a, C>>, (Nil{}, None{}))
        case Con{sl, t}:
          match sl:
            case Slot{c, +born, +last}:
              take.at(~M, ~pure, ~bind, ~a, ~C, ~probe, ~close, fresh(age, idle, now, born, last), c, born,
                last, t, t2 => take.go(~M, ~pure, ~bind, ~a, ~C, ~probe, ~close, age, idle, now, j, t2))

# how many wait, and the same list back
def count.put(a, -C: Kind(a), h: Slot<a, C>, r: Nat & List<a, Slot<a, C>>) -> Nat & List<a, Slot<a, C>>:
  (n, t) = r
  (1n+n, Con{h, t})

def count(a, -C: Kind(a), xs: List<a, Slot<a, C>>) -> Nat & List<a, Slot<a, C>>:
  match xs:
    case Nil{}:
      (0n, Nil{})
    case Con{h, t}:
      count.put(a, C, h, count(a, C, t))

def take.count(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~a: Quant, ~C: Kind(a),
  ~probe: C -> M(C & Bool), ~close: C -> M(Unit), +age: Nat, +idle: Nat, +now: Nat,
  nx: Nat & List<a, Slot<a, C>>
) -> M(List<a, Slot<a, C>> & Maybe<a, Slot<a, C>>):
  (n, xs) = nx
  take.go(~M, ~pure, ~bind, ~a, ~C, ~probe, ~close, age, idle, now, n, xs)

def take.back(a, -C: Kind(a), +cap: Nat, +age: Nat, +idle: Nat, r: List<a, Slot<a, C>> & Maybe<a, Slot<a, C>>) ->
  Pool<a, C> & Maybe<a, Slot<a, C>>:
  (xs, may) = r
  (Pool{cap, age, idle, xs}, may)

# the newest connection fit to use, if there is one, and the pool without
# it (and without every connection found unfit on the way)
def take(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~a: Quant, ~C: Kind(a),
  ~probe: C -> M(C & Bool), ~close: C -> M(Unit), pool: Pool<a, C>, +now: Nat
) -> M(Pool<a, C> & Maybe<a, Slot<a, C>>):
  match pool:
    case Pool{+cap, +age, +idle, xs}:
      bind(List<a, Slot<a, C>> & Maybe<a, Slot<a, C>>, Pool<a, C> & Maybe<a, Slot<a, C>>,
        take.count(~M, ~pure, ~bind, ~a, ~C, ~probe, ~close, age, idle, now, count(a, C, xs)),
        r => pure(Pool<a, C> & Maybe<a, Slot<a, C>>, take.back(a, C, cap, age, idle, r)))

# Giving back
# -----------
#
# A connection comes back with whether its exchange left it fit (client
# .bend's reuse). One that is not is closed. One that is joins the front,
# and the pool keeps at most cap: the oldest past it are closed.

def split.put(a, -C: Kind(a), h: Slot<a, C>, r: List<a, Slot<a, C>> & List<a, Slot<a, C>>) ->
  List<a, Slot<a, C>> & List<a, Slot<a, C>>:
  (a, b) = r
  (Con{h, a}, b)

# the first k, and the rest
def split(a, -C: Kind(a), k: Nat, xs: List<a, Slot<a, C>>) -> List<a, Slot<a, C>> & List<a, Slot<a, C>>:
  match k xs:
    case 0n xs:
      (Nil{}, xs)
    case 1n+j Nil{}:
      (Nil{}, Nil{})
    case 1n+j Con{h, t}:
      split.put(a, C, h, split(a, C, j, t))

def close.all(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~a: Quant, ~C: Kind(a), ~close: C -> M(Unit),
  xs: List<a, Slot<a, C>>
) -> M(Unit):
  match xs:
    case Nil{}:
      pure(Unit, Unit{})
    case Con{sl, t}:
      match sl:
        case Slot{c, born, last}:
          bind(Unit, Unit, close(c), u => close.all(~M, ~pure, ~bind, ~a, ~C, ~close, t))

def give.keep(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~a: Quant, ~C: Kind(a), ~close: C -> M(Unit),
  +cap: Nat, +age: Nat, +idle: Nat, s: Slot<a, C>, r: List<a, Slot<a, C>> & List<a, Slot<a, C>>
) -> M(Pool<a, C>):
  (keep, gone) = r
  bind(Unit, Pool<a, C>, close.all(~M, ~pure, ~bind, ~a, ~C, ~close, gone), u =>
    pure(Pool<a, C>, Pool{cap, age, idle, Con{s, keep}}))

def give.at(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~a: Quant, ~C: Kind(a), ~close: C -> M(Unit),
  +cap: Nat, +age: Nat, +idle: Nat, xs: List<a, Slot<a, C>>, ok: Bool, s: Slot<a, C>
) -> M(Pool<a, C>):
  match cap ok:
    case _ False{}:
      match s:
        case Slot{c, born, last}:
          bind(Unit, Pool<a, C>, close(c), u => pure(Pool<a, C>, Pool{cap, age, idle, xs}))
    case 0n True{}:
      match s:
        case Slot{c, born, last}:
          bind(Unit, Pool<a, C>, close(c), u => pure(Pool<a, C>, Pool{0n, age, idle, xs}))
    case 1n+k True{}:
      give.keep(~M, ~pure, ~bind, ~a, ~C, ~close, 1n+k, age, idle, s, split(a, C, k, xs))

# a connection made at born, used until now, back from an exchange that
# left it fit (ok) or not
def give(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~a: Quant, ~C: Kind(a), ~close: C -> M(Unit),
  pool: Pool<a, C>, c: C, born: Nat, now: Nat, ok: Bool
) -> M(Pool<a, C>):
  match pool:
    case Pool{+cap, +age, +idle, xs}:
      give.at(~M, ~pure, ~bind, ~a, ~C, ~close, cap, age, idle, xs, ok, Slot{c, born, now})

# The real world
# ==============

def take.io(pool: Pool<&1, Socket>, +now: Nat) -> IO(Pool<&1, Socket> & Maybe<&1, Slot<&1, Socket>>):
  take(~(A => IO(A)), ~IO.pure, ~IO.bind, ~&1, ~Socket, ~TCP.idle, ~Socket.close, pool, now)

def give.io(pool: Pool<&1, Socket>, s: Socket, born: Nat, now: Nat, ok: Bool) -> IO(Pool<&1, Socket>):
  give(~(A => IO(A)), ~IO.pure, ~IO.bind, ~&1, ~Socket, ~Socket.close, pool, s, born, now, ok)

# The model
# =========
#
# A model connection has a name, and says whether something waits
# unread on it; the probe reads that, as TCP.idle's contract (idle.ok)
# says the real one does, and closing does nothing.
type MC is Data:
  MC{id: Nat, unread: Bool}

def m.probe(c: MC) -> MC & Bool:
  match c:
    case MC{id, +unread}:
      (MC{id, unread}, Bool.not(unread))

def m.close(c: MC) -> Unit:
  Unit{}

def sim.take.go(+age: Nat, +idle: Nat, +now: Nat, k: Nat, xs: List<&2, Slot<&2, MC>>) ->
  List<&2, Slot<&2, MC>> & Maybe<&2, Slot<&2, MC>>:
  take.go(~W.Id, ~W.Id.pure, ~W.Id.bind, ~&2, ~MC, ~m.probe, ~m.close, age, idle, now, k, xs)

def sim.take(pool: Pool<&2, MC>, +now: Nat) -> Pool<&2, MC> & Maybe<&2, Slot<&2, MC>>:
  take(~W.Id, ~W.Id.pure, ~W.Id.bind, ~&2, ~MC, ~m.probe, ~m.close, pool, now)

def sim.give(pool: Pool<&2, MC>, c: MC, born: Nat, now: Nat, ok: Bool) -> Pool<&2, MC>:
  give(~W.Id, ~W.Id.pure, ~W.Id.bind, ~&2, ~MC, ~m.close, pool, c, born, now, ok)

# What the laws speak of
# ======================

def size(a, -C: Kind(a), xs: List<a, Slot<a, C>>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+size(a, C, t)

def pool.xs(a, -C: Kind(a), p: Pool<a, C>) -> List<a, Slot<a, C>>:
  match p:
    case Pool{cap, age, idle, xs}:
      xs

def pool.cap(a, -C: Kind(a), p: Pool<a, C>) -> Nat:
  match p:
    case Pool{cap, age, idle, xs}:
      cap

def sid(s: Slot<&2, MC>) -> Nat:
  match s:
    case Slot{c, born, last}:
      match c:
        case MC{id, unread}:
          id

def smem(+x: Nat, xs: List<&2, Slot<&2, MC>>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{s, t}:
      Nat.is_eq(x, sid(s)) || smem(x, t)

# no connection in a list twice, by name
def ND(xs: List<&2, Slot<&2, MC>>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{s, t}:
      {smem(sid(s), t) == False{} : Bool} & ND(t)

# what a take answered: a connection fit to use -- nothing unread on it,
# made and used within the pool's times -- or none
def Handed(+age: Nat, +idle: Nat, +now: Nat, may: Maybe<&2, Slot<&2, MC>>) -> Type:
  match may:
    case None{}:
      Unit
    case Some{s}:
      match s:
        case Slot{c, born, last}:
          match c:
            case MC{id, unread}:
              {unread == False{} : Bool} & {fresh(age, idle, now, born, last) == True{} : Bool}

# and what it left: the one handed out is not among them
def Apart(r: List<&2, Slot<&2, MC>> & Maybe<&2, Slot<&2, MC>>) -> Type:
  match r:
    case (rest, may):
      match may:
        case None{}:
          Unit
        case Some{s}:
          {smem(sid(s), rest) == False{} : Bool}

# The laws
# ========

def le.refl(a: Nat) -> {Nat.is_le(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      le.refl(p)

def le.succ(a: Nat) -> {Nat.is_le(a, 1n+a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      le.succ(p)

def le.trans(a: Nat, b: Nat, c: Nat, h1: {Nat.is_le(a, b) == True{} : Bool}, h2: {Nat.is_le(b, c) == True{} : Bool}) ->
  {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ 0n:
      {==}
    case 0n _ 1n+z:
      {==}
    case 1n+x 0n _:
      W.no({Nat.is_le(1n+x, c) == True{} : Bool}, h1)
    case 1n+x 1n+y 0n:
      W.no({Nat.is_le(1n+x, 0n) == True{} : Bool}, h2)
    case 1n+x 1n+y 1n+z:
      le.trans(x, y, z, h1, h2)

# what take.go keeps: no more than it was given; nothing twice if
# nothing was twice, and the one it hands out not among the rest; and
# that one fit to use
def TG(+age: Nat, +idle: Nat, +now: Nat, -xs: List<&2, Slot<&2, MC>>, r: List<&2, Slot<&2, MC>> & Maybe<&2, Slot<&2, MC>>) ->
  Type:
  match r:
    case (rest, may):
      {Nat.is_le(size(&2, MC, rest), size(&2, MC, xs)) == True{} : Bool} &
        ((ND(xs) -> ND(rest) & Apart((rest, may))) & Handed(age, idle, now, may))

def tg.weak.nd(-s: Slot<&2, MC>, -t: List<&2, Slot<&2, MC>>, -rest: List<&2, Slot<&2, MC>>, -may: Maybe<&2, Slot<&2, MC>>,
  f: ND(t) -> ND(rest) & Apart((rest, may)), nd: ND(Con{s, t})) -> ND(rest) & Apart((rest, may)):
  (nm, ndt) = nd
  f(ndt)

def tg.weak(+age: Nat, +idle: Nat, +now: Nat, -s: Slot<&2, MC>, +t: List<&2, Slot<&2, MC>>,
  r: List<&2, Slot<&2, MC>> & Maybe<&2, Slot<&2, MC>>, h: TG(age, idle, now, t, r)) -> TG(age, idle, now, Con{s, t}, r):
  match r:
    case (+rest, may):
      (le, g) = h
      (f, hd) = g
      (le.trans(size(&2, MC, rest), size(&2, MC, t), 1n+size(&2, MC, t), le, le.succ(size(&2, MC, t))),
        (nd => tg.weak.nd(s, t, rest, may, f, nd), hd))

def tg.hand.nd(-id: Nat, -born: Nat, -last: Nat, -t: List<&2, Slot<&2, MC>>,
  nd: ND(Con{Slot{MC{id, False{}}, born, last}, t})) ->
  ND(t) & Apart((t, Some{Slot{MC{id, False{}}, born, last}})):
  (nm, ndt) = nd
  (ndt, nm)

def tg.hand(+age: Nat, +idle: Nat, +now: Nat, +id: Nat, +born: Nat, +last: Nat, +t: List<&2, Slot<&2, MC>>,
  e: {fresh(age, idle, now, born, last) == True{} : Bool}) ->
  TG(age, idle, now, Con{Slot{MC{id, False{}}, born, last}, t}, (t, Some{Slot{MC{id, False{}}, born, last}})):
  (le.succ(size(&2, MC, t)), (nd => tg.hand.nd(id, born, last, t, nd), ({==}, e)))


def tg.at(+age: Nat, +idle: Nat, +now: Nat, +j: Nat, fr: Bool, +id: Nat, +unread: Bool, +born: Nat, +last: Nat,
  +t: List<&2, Slot<&2, MC>>, e: {fresh(age, idle, now, born, last) == fr : Bool},
  ih: @+xs2: List<&2, Slot<&2, MC>> -> TG(age, idle, now, xs2, sim.take.go(age, idle, now, j, xs2))) ->
  TG(age, idle, now, Con{Slot{MC{id, unread}, born, last}, t},
    take.at(~W.Id, ~W.Id.pure, ~W.Id.bind, ~&2, ~MC, ~m.probe, ~m.close, fr, MC{id, unread}, born, last, t,
      t2 => sim.take.go(age, idle, now, j, t2))):
  match fr:
    case False{}:
      tg.weak(age, idle, now, Slot{MC{id, unread}, born, last}, t, sim.take.go(age, idle, now, j, t), ih(t))
    case True{}:
      match unread:
        case False{}:
          tg.hand(age, idle, now, id, born, last, t, e)
        case True{}:
          tg.weak(age, idle, now, Slot{MC{id, True{}}, born, last}, t, sim.take.go(age, idle, now, j, t), ih(t))

def tg.cases(+age: Nat, +idle: Nat, +now: Nat, +j: Nat, +xs: List<&2, Slot<&2, MC>>,
  ih: @+xs2: List<&2, Slot<&2, MC>> -> TG(age, idle, now, xs2, sim.take.go(age, idle, now, j, xs2))) ->
  TG(age, idle, now, xs, sim.take.go(age, idle, now, 1n+j, xs)):
  match xs:
    case Nil{}:
      ({==}, (nd => (Unit{}, Unit{}), Unit{}))
    case Con{sl, +t}:
      match sl:
        case Slot{c, +born, +last}:
          match c:
            case MC{+id, +unread}:
              tg.at(age, idle, now, j, fresh(age, idle, now, born, last), id, unread, born, last, t, {==}, ih)

def tg.step(+age: Nat, +idle: Nat, +now: Nat, +j: Nat,
  ih: @+xs2: List<&2, Slot<&2, MC>> -> TG(age, idle, now, xs2, sim.take.go(age, idle, now, j, xs2))) ->
  @+xs: List<&2, Slot<&2, MC>> -> TG(age, idle, now, xs, sim.take.go(age, idle, now, 1n+j, xs)):
  xs => tg.cases(age, idle, now, j, xs, ih)


def tg.go(+age: Nat, +idle: Nat, +now: Nat, +k: Nat) ->
  @+xs: List<&2, Slot<&2, MC>> -> TG(age, idle, now, xs, sim.take.go(age, idle, now, k, xs)):
  match k:
    case 0n:
      xs => (le.refl(size(&2, MC, xs)), (nd => (nd, Unit{}), Unit{}))
    case 1n+j:
      tg.step(age, idle, now, j, tg.go(age, idle, now, j))

def count.is.put(-h: Slot<&2, MC>, -t: List<&2, Slot<&2, MC>>, r: Nat & List<&2, Slot<&2, MC>>,
  e: {r == (size(&2, MC, t), t) : Nat & List<&2, Slot<&2, MC>>}) ->
  {count.put(&2, MC, h, r) == (1n+size(&2, MC, t), Con{h, t}) : Nat & List<&2, Slot<&2, MC>>}:
  %Equal.sym(Nat & List<&2, Slot<&2, MC>>, r, (size(&2, MC, t), t), e) :
    {count.put(&2, MC, h, _) == (1n+size(&2, MC, t), Con{h, t}) : Nat & List<&2, Slot<&2, MC>>}
  {==}

def count.is(xs: List<&2, Slot<&2, MC>>) -> {count(&2, MC, xs) == (size(&2, MC, xs), xs) : Nat & List<&2, Slot<&2, MC>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, +t}:
      count.is.put(h, t, count(&2, MC, t), count.is(t))

# what a take answered and left, beside the list it took from
def TK(+age: Nat, +idle: Nat, +now: Nat, -xs: List<&2, Slot<&2, MC>>, r: Pool<&2, MC> & Maybe<&2, Slot<&2, MC>>) ->
  Type:
  match r:
    case (pool, may):
      match pool:
        case Pool{c, a, i, rest}:
          TG(age, idle, now, xs, (rest, may))

def tk.back(+cap: Nat, +age: Nat, +idle: Nat, +now: Nat, -xs: List<&2, Slot<&2, MC>>,
  r: List<&2, Slot<&2, MC>> & Maybe<&2, Slot<&2, MC>>, h: TG(age, idle, now, xs, r)) ->
  TK(age, idle, now, xs, take.back(&2, MC, cap, age, idle, r)):
  match r:
    case (rest, may):
      h

# LAW: a take hands out at most one connection, and a fit one: nothing
# unread on it (the probe said so), made within the pool's age and used
# within its idle time. What it leaves is no more than it had; and when
# no connection was in the pool twice, none is after, and the one handed
# out is not among those left -- it has one user.
law take_ok:
  for +cap: Nat
  for +age: Nat
  for +idle: Nat
  for +xs: List<&2, Slot<&2, MC>>
  for +now: Nat
  TK(age, idle, now, xs, sim.take(Pool{cap, age, idle, xs}, now))

def take_ok(cap, age, idle, xs, now):
  %Equal.sym(Nat & List<&2, Slot<&2, MC>>, count(&2, MC, xs), (size(&2, MC, xs), xs), count.is(xs)) :
    TK(age, idle, now, xs, take.back(&2, MC, cap, age, idle,
      take.count(~W.Id, ~W.Id.pure, ~W.Id.bind, ~&2, ~MC, ~m.probe, ~m.close, age, idle, now, _)))
  tk.back(cap, age, idle, now, xs, sim.take.go(age, idle, now, size(&2, MC, xs), xs),
    tg.go(age, idle, now, size(&2, MC, xs))(xs))

# the first k of a list: at most k of them, nothing twice if nothing was,
# and nothing the list did not hold
def fst.of(r: List<&2, Slot<&2, MC>> & List<&2, Slot<&2, MC>>) -> List<&2, Slot<&2, MC>>:
  (a, b) = r
  a

def sp.le.put(+j: Nat, -h: Slot<&2, MC>, r: List<&2, Slot<&2, MC>> & List<&2, Slot<&2, MC>>,
  ih: {Nat.is_le(size(&2, MC, fst.of(r)), j) == True{} : Bool}) ->
  {Nat.is_le(size(&2, MC, fst.of(split.put(&2, MC, h, r))), 1n+j) == True{} : Bool}:
  match r:
    case (a, b):
      ih

def sp.le(+k: Nat, +xs: List<&2, Slot<&2, MC>>) -> {Nat.is_le(size(&2, MC, fst.of(split(&2, MC, k, xs))), k) == True{} : Bool}:
  match k xs:
    case 0n _:
      {==}
    case 1n+j Nil{}:
      {==}
    case 1n+j Con{h, +t}:
      sp.le.put(j, h, split(&2, MC, j, t), sp.le(j, t))

def or.keep(a: Bool, -b: Bool, -c: Bool, e: {(a || b) == False{} : Bool}, f: {b == False{} : Bool} -> {c == False{} : Bool}) ->
  {(a || c) == False{} : Bool}:
  match a:
    case True{}:
      W.no({(True{} || c) == False{} : Bool}, Equal.sym(Bool, True{}, False{}, e))
    case False{}:
      f(e)

def sp.mem.put(+x: Nat, +h: Slot<&2, MC>, -t: List<&2, Slot<&2, MC>>, r: List<&2, Slot<&2, MC>> & List<&2, Slot<&2, MC>>,
  ih: {smem(x, t) == False{} : Bool} -> {smem(x, fst.of(r)) == False{} : Bool}) ->
  {smem(x, Con{h, t}) == False{} : Bool} -> {smem(x, fst.of(split.put(&2, MC, h, r))) == False{} : Bool}:
  match r:
    case (a, b):
      e => or.keep(Nat.is_eq(x, sid(h)), smem(x, t), smem(x, a), e, ih)

def sp.mem(+k: Nat, +xs: List<&2, Slot<&2, MC>>, +x: Nat) ->
  {smem(x, xs) == False{} : Bool} -> {smem(x, fst.of(split(&2, MC, k, xs))) == False{} : Bool}:
  match k xs:
    case 0n _:
      e => {==}
    case 1n+j Nil{}:
      e => {==}
    case 1n+j Con{+h, +t}:
      sp.mem.put(x, h, t, split(&2, MC, j, t), sp.mem(j, t, x))

def sp.nd.put(+h: Slot<&2, MC>, -t: List<&2, Slot<&2, MC>>, r: List<&2, Slot<&2, MC>> & List<&2, Slot<&2, MC>>,
  ih: ND(t) -> ND(fst.of(r)), m: {smem(sid(h), t) == False{} : Bool} -> {smem(sid(h), fst.of(r)) == False{} : Bool},
  nd: ND(Con{h, t})) -> ND(fst.of(split.put(&2, MC, h, r))):
  match r:
    case (a, b):
      (nm, ndt) = nd
      (m(nm), ih(ndt))

def sp.nd(+k: Nat, +xs: List<&2, Slot<&2, MC>>) -> ND(xs) -> ND(fst.of(split(&2, MC, k, xs))):
  match k xs:
    case 0n _:
      nd => Unit{}
    case 1n+j Nil{}:
      nd => Unit{}
    case 1n+j Con{+h, +t}:
      nd => sp.nd.put(h, t, split(&2, MC, j, t), sp.nd(j, t), sp.mem(j, t, sid(h)), nd)

def cid(c: MC) -> Nat:
  match c:
    case MC{id, unread}:
      id

# what a give leaves: no more than cap if there were no more before; and,
# when nothing was twice and the one given back was not already in, still
# nothing twice
def GV(+cap: Nat, +xs: List<&2, Slot<&2, MC>>, +c: MC, +ys: List<&2, Slot<&2, MC>>) -> Type:
  ({Nat.is_le(size(&2, MC, xs), cap) == True{} : Bool} -> {Nat.is_le(size(&2, MC, ys), cap) == True{} : Bool}) &
    (ND(xs) -> {smem(cid(c), xs) == False{} : Bool} -> ND(ys))

def gv.keep(-cap: Nat, -age: Nat, -idle: Nat, -s: Slot<&2, MC>, r: List<&2, Slot<&2, MC>> & List<&2, Slot<&2, MC>>) ->
  {pool.xs(&2, MC, give.keep(~W.Id, ~W.Id.pure, ~W.Id.bind, ~&2, ~MC, ~m.close, cap, age, idle, s, r)) ==
    Con{s, fst.of(r)} : List<&2, Slot<&2, MC>>}:
  match r:
    case (a, b):
      {==}

def gv.nd(+k: Nat, +xs: List<&2, Slot<&2, MC>>, +c: MC, -born: Nat, -now: Nat) ->
  ND(xs) -> {smem(cid(c), xs) == False{} : Bool} -> ND(Con{Slot{c, born, now}, fst.of(split(&2, MC, k, xs))}):
  match c:
    case MC{+id, unread}:
      nd => m => (sp.mem(k, xs, id)(m), sp.nd(k, xs)(nd))

def gv.at(+cap: Nat, +age: Nat, +idle: Nat, +xs: List<&2, Slot<&2, MC>>, ok: Bool, +c: MC, +born: Nat, +now: Nat) ->
  GV(cap, xs, c, pool.xs(&2, MC, give.at(~W.Id, ~W.Id.pure, ~W.Id.bind, ~&2, ~MC, ~m.close, cap, age, idle, xs, ok,
    Slot{c, born, now}))):
  match cap ok:
    case 0n False{}:
      (h => h, nd => m => nd)
    case 1n+k False{}:
      (h => h, nd => m => nd)
    case 0n True{}:
      (h => h, nd => m => nd)
    case 1n+k True{}:
      %Equal.sym(List<&2, Slot<&2, MC>>,
        pool.xs(&2, MC, give.keep(~W.Id, ~W.Id.pure, ~W.Id.bind, ~&2, ~MC, ~m.close, 1n+k, age, idle, Slot{c, born, now},
          split(&2, MC, k, xs))),
        Con{Slot{c, born, now}, fst.of(split(&2, MC, k, xs))},
        gv.keep(1n+k, age, idle, Slot{c, born, now}, split(&2, MC, k, xs))) :
        GV(1n+k, xs, c, _)
      (h => sp.le(k, xs), gv.nd(k, xs, c, born, now))

# LAW: a give keeps the pool within its cap, closing what falls past it
# (and a connection given back unfit, and any given to a pool of cap 0);
# and keeps every connection in it once.
law give_ok:
  for +cap: Nat
  for +age: Nat
  for +idle: Nat
  for +xs: List<&2, Slot<&2, MC>>
  for +c: MC
  for +born: Nat
  for +now: Nat
  for ok: Bool
  GV(cap, xs, c, pool.xs(&2, MC, sim.give(Pool{cap, age, idle, xs}, c, born, now, ok)))

def give_ok(cap, age, idle, xs, c, born, now, ok):
  gv.at(cap, age, idle, xs, ok, c, born, now)
