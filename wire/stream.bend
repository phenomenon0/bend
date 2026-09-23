# bend-wire: a body as a stream.
#
# A body delivered as it arrives, a chunk a read, to a consumer that may
# be slower than the peer -- an upstream socket in a proxy, a file, a
# planner -- with backpressure: the stream holds the chunks the consumer
# has not taken yet, and while it holds a window's worth or more it does
# not read the socket at all, so a stalled consumer stops the peer (TCP
# does the rest) and nothing grows without bound.
#
# Written once over its effects and its framer, as template parameters,
# like wire/loop.bend:
#
#   ~M, ~pure, ~bind   the monad
#   ~S, ~rx            the socket, and a timed read: TCP.poll_buf
#   ~E, ~R             the framer's context and state: a reader on the
#                      kit that frames the body (wire/http1/resp.bend
#                      for a response, or entered at a request's body)
#   ~feed              a read through the framer (feed_buf)
#   ~take              the body bytes the framer holds, and the framer
#                      holding none (the kit's take: drain_reads says
#                      the chunks taken are the framed body, whatever
#                      the cuts)
#   ~look              the framer's word on the body: more to come,
#                      whole, running to the close, or refused
#   ~K, ~give, ~fin    the consumer: give offers it every byte held and
#                      it answers how many it took, from the front, 0
#                      to all; fin tells it the body is over
#
# and instantiated with IO by a user (wire/client.bend's fetch.stream),
# and with the identity monad, the scripted peer and a scripted consumer
# in wire/world.bend, where its laws are proven for every framer: the
# held bytes stay under the window plus one read, a consumer that takes
# nothing of a full window ends the stream with no read, the bytes move
# from the framer to the held queue to the consumer in order and none
# is lost, and the end is told once, after the last byte.
import Base
import ./loop.bend as L

# The framer's word on the body
type Stage is Data:
  Going{}
  Ended{}
  Closing{}
  Refused{}

# Why a stream ended: the body ended and every byte of it was taken and
# its end told; the consumer took nothing when it had to; the framer
# refused the body; a read failed; the peer was silent past the read's
# time; the peer closed before the body ended; a read gave more body
# than it had bytes (a framer's fault, stopped rather than trusted); the
# turns ran out.
type Why is Data:
  BDone{}
  BStall{}
  BBad{}
  BCut{code: U32}
  BTime{}
  BEof{}
  BOver{}
  BFuel{}

# The stream between turns: the socket, the framer, the consumer, the
# body bytes held for the consumer, and whether the peer has closed.
type Bq<-S: Type, -R: Data, -K: Type> is Type:
  Bq{s: S, r: R, k: K, held: Bytes(), eof: Bool}

# a turn's result: the stream, and why it ended if it did
law Turn:
  for -S: Type
  for -R: Data
  for -K: Type
  Type

def Turn(S, R, K):
  Bq<S, R, K> & Maybe<&2, Why>

# the most one read takes
def chunk() -> U32:
  65536

# whether the body has more to come off the socket
def more(st: Stage, eof: Bool) -> Bool:
  match st:
    case Going{}:
      Bool.not(eof)
    case Closing{}:
      Bool.not(eof)
    case Ended{}:
      False{}
    case Refused{}:
      False{}

# The pass
# ========
#
# Every byte held is offered; the consumer takes some from the front and
# the rest stays held, in order. Taking nothing is a stall when the
# window is full, or when no more will come to wait for (the body is
# over, refused, or the peer closed): the stream ends rather than spin.

def pass.stall(
  -S: Type, -R: Data, -K: Type, s: S, r: R, k: K, held: Bytes(), eof: Bool, stalled: Bool
) -> Turn(S, R, K):
  match stalled:
    case True{}:
      (Bq{s, r, k, held, eof}, Some{BStall{}})
    case False{}:
      (Bq{s, r, k, held, eof}, None{})

def pass.took(
  ~R: Data, ~look: R -> Stage, -S: Type, -K: Type, +win: Nat, s: S, +r: R, kn: K & Nat,
  +held: Bytes(), +eof: Bool
) -> Turn(S, R, K):
  (k, +n) = kn
  pass.stall(S, R, K, s, r, k, String.drop(held, n), eof,
    Nat.is_eq(n, 0n) && (Nat.is_le(win, Bytes.len(held)) || Bool.not(more(look(r), eof))))

def pass.at(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type, ~R: Data,
  ~look: R -> Stage, ~K: Type, ~give: K -> Bytes() -> M(K & Nat), +win: Nat, s: S, +r: R, k: K,
  +held: Bytes(), +eof: Bool, empty: Bool
) -> M(Turn(S, R, K)):
  match empty:
    case True{}:
      pure(Turn(S, R, K), (Bq{s, r, k, held, eof}, None{}))
    case False{}:
      bind(K & Nat, Turn(S, R, K), give(k, held), kn =>
        pure(Turn(S, R, K), pass.took(~R, ~look, S, K, win, s, r, kn, held, eof)))

def pass(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type, ~R: Data,
  ~look: R -> Stage, ~K: Type, ~give: K -> Bytes() -> M(K & Nat), +win: Nat, bq: Bq<S, R, K>
) -> M(Turn(S, R, K)):
  match bq:
    case Bq{s, +r, k, +held, +eof}:
      pass.at(~M, ~pure, ~bind, ~S, ~R, ~look, ~K, ~give, win, s, r, k, held, eof,
        String.is_empty(held))

# The pull
# ========
#
# The socket is read only while the window has room: with win bytes or
# more held, the pull reads nothing and the next pass offers them again.
# A read's bytes go through the framer, and what it then holds of the
# body joins the held bytes at their end. The body over and every byte
# taken, the consumer is told, once, and the stream ends.

def pull.fits(
  -S: Type, -R: Data, -K: Type, s: S, r: R, k: K, +held: Bytes(), +x: Bytes(), eof: Bool, ok: Bool
) -> Turn(S, R, K):
  match ok:
    case True{}:
      (Bq{s, r, k, Bytes.append(held, x), eof}, None{})
    case False{}:
      (Bq{s, r, k, held, eof}, Some{BOver{}})

def pull.fed(
  -S: Type, -R: Data, -K: Type, s: S, q: R & Bytes(), k: K, +held: Bytes(), eof: Bool, +n: Nat
) -> Turn(S, R, K):
  (r, +x) = q
  pull.fits(S, R, K, s, r, k, held, x, eof, Nat.is_le(Bytes.len(x), n))

def pull.bytes(
  ~E: Data, ~R: Data, ~feed: E -> Bytes() -> R -> R, ~take: R -> R & Bytes(), -S: Type,
  -K: Type, +e: E, s: S, r: R, k: K, +held: Bytes(), eof: Bool, empty: Bool, +bs: Bytes()
) -> Turn(S, R, K):
  match empty:
    case True{}:
      (Bq{s, r, k, held, True{}}, None{})
    case False{}:
      pull.fed(S, R, K, s, take(feed(e, bs, r)), k, held, eof, Bytes.len(bs))

def pull.may(
  ~E: Data, ~R: Data, ~feed: E -> Bytes() -> R -> R, ~take: R -> R & Bytes(), -S: Type,
  -K: Type, +e: E, s: S, may: Maybe<&1, Bytes()>, r: R, k: K, +held: Bytes(), eof: Bool
) -> Turn(S, R, K):
  match may:
    case None{}:
      (Bq{s, r, k, held, eof}, Some{BTime{}})
    case Some{+bs}:
      pull.bytes(~E, ~R, ~feed, ~take, S, K, e, s, r, k, held, eof, String.is_empty(bs), bs)

def pull.cut(-S: Type, -R: Data, -K: Type, s: S, r: R, k: K, held: Bytes(), eof: Bool,
  er: U32 & String) -> Turn(S, R, K):
  (code, msg) = er
  (Bq{s, r, k, held, eof}, Some{BCut{code}})

def pull.got(
  ~E: Data, ~R: Data, ~feed: E -> Bytes() -> R -> R, ~take: R -> R & Bytes(), -S: Type,
  -K: Type, +e: E, g: L.Got(S), r: R, k: K, +held: Bytes(), eof: Bool
) -> Turn(S, R, K):
  (s, res) = g
  match res:
    case Fail{er}:
      pull.cut(S, R, K, s, r, k, held, eof, er)
    case Done{may}:
      pull.may(~E, ~R, ~feed, ~take, S, K, e, s, may, r, k, held, eof)

def pull.room(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~rx: S -> U32 -> U32 -> M(L.Got(S)), ~E: Data, ~R: Data, ~feed: E -> Bytes() -> R -> R,
  ~take: R -> R & Bytes(), ~K: Type, +e: E, +ms: U32, s: S, r: R, k: K, +held: Bytes(),
  eof: Bool, room: Bool
) -> M(Turn(S, R, K)):
  match room:
    case False{}:
      pure(Turn(S, R, K), (Bq{s, r, k, held, eof}, None{}))
    case True{}:
      bind(L.Got(S), Turn(S, R, K), rx(s, chunk(), ms), g =>
        pure(Turn(S, R, K), pull.got(~E, ~R, ~feed, ~take, S, K, e, g, r, k, held, eof)))

def pull.end(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type, ~R: Data, ~K: Type,
  ~fin: K -> M(K), s: S, r: R, k: K, held: Bytes(), eof: Bool, empty: Bool
) -> M(Turn(S, R, K)):
  match empty:
    case True{}:
      bind(K, Turn(S, R, K), fin(k), k2 => pure(Turn(S, R, K), (Bq{s, r, k2, held, eof},
        Some{BDone{}})))
    case False{}:
      pure(Turn(S, R, K), (Bq{s, r, k, held, eof}, None{}))

def pull.go(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~rx: S -> U32 -> U32 -> M(L.Got(S)), ~E: Data, ~R: Data, ~feed: E -> Bytes() -> R -> R,
  ~take: R -> R & Bytes(), ~K: Type, ~fin: K -> M(K), +e: E, +win: Nat, +ms: U32, st: Stage,
  eof: Bool, s: S, r: R, k: K, +held: Bytes()
) -> M(Turn(S, R, K)):
  match st eof:
    case Refused{} _:
      pure(Turn(S, R, K), (Bq{s, r, k, held, eof}, Some{BBad{}}))
    case Ended{} _:
      pull.end(~M, ~pure, ~bind, ~S, ~R, ~K, ~fin, s, r, k, held, eof, String.is_empty(held))
    case Closing{} True{}:
      pull.end(~M, ~pure, ~bind, ~S, ~R, ~K, ~fin, s, r, k, held, True{}, String.is_empty(held))
    case Going{} True{}:
      pure(Turn(S, R, K), (Bq{s, r, k, held, True{}}, Some{BEof{}}))
    case Closing{} False{}:
      pull.room(~M, ~pure, ~bind, ~S, ~rx, ~E, ~R, ~feed, ~take, ~K, e, ms, s, r, k, held,
        False{}, Nat.is_lt(Bytes.len(held), win))
    case Going{} False{}:
      pull.room(~M, ~pure, ~bind, ~S, ~rx, ~E, ~R, ~feed, ~take, ~K, e, ms, s, r, k, held,
        False{}, Nat.is_lt(Bytes.len(held), win))

def pull(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~rx: S -> U32 -> U32 -> M(L.Got(S)), ~E: Data, ~R: Data, ~feed: E -> Bytes() -> R -> R,
  ~take: R -> R & Bytes(), ~look: R -> Stage, ~K: Type, ~fin: K -> M(K), +e: E, +win: Nat,
  +ms: U32, bq: Bq<S, R, K>
) -> M(Turn(S, R, K)):
  match bq:
    case Bq{s, +r, k, +held, eof}:
      pull.go(~M, ~pure, ~bind, ~S, ~rx, ~E, ~R, ~feed, ~take, ~K, ~fin, e, win, ms, look(r), eof,
        s, r, k, held)

# The stream
# ==========

# a pass, and when it did not end the stream, a pull
def turn.then(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~rx: S -> U32 -> U32 -> M(L.Got(S)), ~E: Data, ~R: Data, ~feed: E -> Bytes() -> R -> R,
  ~take: R -> R & Bytes(), ~look: R -> Stage, ~K: Type, ~fin: K -> M(K), +e: E, +win: Nat,
  +ms: U32, t: Turn(S, R, K)
) -> M(Turn(S, R, K)):
  (bq, w) = t
  match w:
    case Some{why}:
      pure(Turn(S, R, K), (bq, Some{why}))
    case None{}:
      pull(~M, ~pure, ~bind, ~S, ~rx, ~E, ~R, ~feed, ~take, ~look, ~K, ~fin, e, win, ms, bq)

def turn(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~rx: S -> U32 -> U32 -> M(L.Got(S)), ~E: Data, ~R: Data, ~feed: E -> Bytes() -> R -> R,
  ~take: R -> R & Bytes(), ~look: R -> Stage, ~K: Type, ~give: K -> Bytes() -> M(K & Nat),
  ~fin: K -> M(K), +e: E, +win: Nat, +ms: U32, bq: Bq<S, R, K>
) -> M(Turn(S, R, K)):
  bind(Turn(S, R, K), Turn(S, R, K), pass(~M, ~pure, ~bind, ~S, ~R, ~look, ~K, ~give, win, bq),
    t => turn.then(~M, ~pure, ~bind, ~S, ~rx, ~E, ~R, ~feed, ~take, ~look, ~K, ~fin, e, win, ms,
      t))

def run.next(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A), -S: Type, -R: Data, -K: Type,
  t: Turn(S, R, K), again: Bq<S, R, K> -> M(Bq<S, R, K> & Why)
) -> M(Bq<S, R, K> & Why):
  (bq, w) = t
  match w:
    case Some{why}:
      pure(Bq<S, R, K> & Why, (bq, why))
    case None{}:
      again(bq)

# n turns at most: a stream ends by its body, its consumer, its peer or
# its fuel, never by running on
def run(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~rx: S -> U32 -> U32 -> M(L.Got(S)), ~E: Data, ~R: Data, ~feed: E -> Bytes() -> R -> R,
  ~take: R -> R & Bytes(), ~look: R -> Stage, ~K: Type, ~give: K -> Bytes() -> M(K & Nat),
  ~fin: K -> M(K), +e: E, +win: Nat, +ms: U32, n: Nat, bq: Bq<S, R, K>
) -> M(Bq<S, R, K> & Why):
  match n:
    case 0n:
      pure(Bq<S, R, K> & Why, (bq, BFuel{}))
    case 1n+j:
      bind(Turn(S, R, K), Bq<S, R, K> & Why,
        turn(~M, ~pure, ~bind, ~S, ~rx, ~E, ~R, ~feed, ~take, ~look, ~K, ~give, ~fin, e, win, ms,
          bq),
        t => run.next(~M, ~pure, S, R, K, t, b => run(~M, ~pure, ~bind, ~S, ~rx, ~E, ~R, ~feed,
          ~take, ~look, ~K, ~give, ~fin, e, win, ms, j, b)))
