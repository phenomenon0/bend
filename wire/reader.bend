# bend-wire: the reader kit.
#
# A protocol reader, as the HTTP engine found it and RESP and CSV
# confirmed: one structural walk over whatever bytes arrive, the whole
# state in one value, one byte-step function, never stopping. Written
# here once, over the protocol as template parameters, with the laws
# every such reader has proven once for all of them:
#
#   ~E: Data               what a step reads beside the state (CSV's
#                          dialect; Unit for a protocol with none)
#   ~S: Data               the reader's state
#   ~step: E -> S -> U32 -> S
#                          one byte
#   ~adv: E -> Bytes() -> S -> S & Bytes()
#                          one move of the block walk: a run of bytes the
#                          protocol takes whole (a field, a body), or one
#                          byte. one.step is the move that takes one byte.
#
# What a protocol proves about its own code, and hands in as a template
# argument, is one obligation per law that needs it:
#
#   adv_ok   a move lands where stepping its bytes one at a time lands:
#            feed_buf.last(e, adv(e, s, p)) == feed_buf.slow(e, s, p)
#            (one.step discharges it with one.step_ok)
#   absorbs  a refused state is a fixed point of the step:
#            step(e, bad(x), c) == bad(x)
#
# and what it gets for them is below: chunking never changes a read
# (feed_split, feed_buf_split, slow_split, reads_split), a refusal is
# never left (bad_feeds, bad_feeds_buf, bad_feeds_slow), the block walk
# is the byte machine (feed_buf_is_feed), and however a stream is cut
# into reads the reader reads it as the stream whole (reads_is).
import Base

# Bytes
# =====
#
# The byte helpers every reader wants, on the list of bytes the laws
# speak of: an ASCII literal, joining, reversing, comparing.

def bytes(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{Chr{c}, t}:
      Con{c, bytes(t)}

def cat(a: List<&2, U32>, b: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, a, b)

def rev(a: List<&2, U32>) -> List<&2, U32>:
  List.reverse(&2, U32, a)

def beq(a: List<&2, U32>, b: List<&2, U32>, acc: Bool) -> Bool:
  match a b:
    case Nil{} Nil{}:
      acc
    case Nil{} Con{y, u}:
      False{}
    case Con{x, t} Nil{}:
      False{}
    case Con{x, t} Con{y, u}:
      beq(t, u, acc && U32.is_eq(x, y))

def digit(+c: U32) -> Bool:
  U32.is_le(48, c) && U32.is_le(c, 57)

# The machine
# ===========

# feed: the machine over a list of bytes, one at a time. The state that
# comes out is the state to feed the next read.
def feed(~E: Data, ~S: Data, ~step: E -> S -> U32 -> S, +e: E, bs: List<&2, U32>, p: S) -> S:
  match bs:
    case Nil{}:
      p
    case Con{c, t}:
      feed(~E, ~S, ~step, e, t, step(e, p, c))

# The same walk over Bytes, a byte at a time.
def feed_buf.slow(~E: Data, ~S: Data, ~step: E -> S -> U32 -> S, +e: E, s: Bytes(), p: S) -> S:
  match s:
    case SNil{}:
      p
    case SCon{Chr{c}, t}:
      feed_buf.slow(~E, ~S, ~step, e, t, step(e, p, c))

# the rest of a walk the fuel ran out on, a byte at a time
def feed_buf.last(~E: Data, ~S: Data, ~step: E -> S -> U32 -> S, +e: E, q: S & Bytes()) -> S:
  (p, s) = q
  feed_buf.slow(~E, ~S, ~step, e, s, p)

# the move that takes one byte: the walk of a protocol with no runs
def one.step(~E: Data, ~S: Data, ~step: E -> S -> U32 -> S, e: E, s: Bytes(), p: S) ->
  S & Bytes():
  match s:
    case SNil{}:
      (p, SNil{})
    case SCon{Chr{c}, t}:
      (step(e, p, c), t)

# n bounds the moves; every move takes at least one byte, so a walk over
# n bytes never runs out
def feed_buf.go(
  ~E: Data, ~S: Data, ~step: E -> S -> U32 -> S, ~adv: E -> Bytes() -> S -> S & Bytes(),
  +e: E, n: Nat, q: S & Bytes()
) -> S:
  match n:
    case 0n:
      feed_buf.last(~E, ~S, ~step, e, q)
    case 1n+m:
      (p, s) = q
      match s:
        case SNil{}:
          p
        case SCon{h, t}:
          feed_buf.go(~E, ~S, ~step, ~adv, e, m, adv(e, SCon{h, t}, p))

# The walk a server runs on a read: one packed block, moved through by
# the protocol's own moves.
def feed_buf(
  ~E: Data, ~S: Data, ~step: E -> S -> U32 -> S, ~adv: E -> Bytes() -> S -> S & Bytes(),
  +e: E, +s: Bytes(), p: S
) -> S:
  feed_buf.go(~E, ~S, ~step, ~adv, e, Bytes.len(s), (p, s))

# the reads of a stream, each fed in turn
def reads(
  ~E: Data, ~S: Data, ~step: E -> S -> U32 -> S, ~adv: E -> Bytes() -> S -> S & Bytes(),
  +e: E, rs: List<&2, Bytes()>, p: S
) -> S:
  match rs:
    case Nil{}:
      p
    case Con{r, t}:
      reads(~E, ~S, ~step, ~adv, e, t, feed_buf(~E, ~S, ~step, ~adv, e, r, p))

# The laws
# ========

# LAW: chunking does not change the read. Feeding a chunk and then the
# next lands exactly where feeding the two joined would have, for every
# step function and every state type.
law feed_split:
  for ~E: Data
  for ~S: Data
  for ~step: E -> S -> U32 -> S
  for +e: E
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +p: S
  {feed(~E, ~S, ~step, e, List.append(&2, U32, a, b), p) ==
    feed(~E, ~S, ~step, e, b, feed(~E, ~S, ~step, e, a, p)) : S}

def feed_split(E, S, step, e, a, b, p):
  match a:
    case Nil{}:
      {==}
    case Con{c, t}:
      feed_split(~E, ~S, ~step, e, t, b, step(e, p, c))

# LAW: a refusal is never left. When every refused state (bad(x), for
# each x a refusal can carry) is a fixed point of the step, no input
# moves the reader out of one: nothing after a refused byte is read.
law bad_feeds:
  for ~E: Data
  for ~S: Data
  for ~step: E -> S -> U32 -> S
  for ~X: Data
  for ~bad: X -> S
  for ~absorbs: @+e: E -> @+x: X -> @+c: U32 -> {step(e, bad(x), c) == bad(x) : S}
  for +e: E
  for +s: List<&2, U32>
  for +x: X
  {feed(~E, ~S, ~step, e, s, bad(x)) == bad(x) : S}

def bad_feeds(E, S, step, X, bad, absorbs, e, s, x):
  match s:
    case Nil{}:
      {==}
    case Con{c, t}:
      %Equal.sym(S, step(e, bad(x), c), bad(x), absorbs(e, x, c)) :
        {feed(~E, ~S, ~step, e, t, _) == bad(x) : S}
      bad_feeds(~E, ~S, ~step, ~X, ~bad, ~absorbs, e, t, x)

# the byte-at-a-time walk over Bytes is feed on its bytes
law slow_is_feed:
  for ~E: Data
  for ~S: Data
  for ~step: E -> S -> U32 -> S
  for +e: E
  for +s: Bytes()
  for +p: S
  {feed_buf.slow(~E, ~S, ~step, e, s, p) == feed(~E, ~S, ~step, e, Bytes.to_list(s), p) : S}

def slow_is_feed(E, S, step, e, s, p):
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{c}, t}:
      slow_is_feed(~E, ~S, ~step, e, t, step(e, p, c))

# LAW: a protocol that walks a read a byte at a time (feed_buf.slow, no
# moves to prove) has the block laws with no obligation at all.
law slow_split:
  for ~E: Data
  for ~S: Data
  for ~step: E -> S -> U32 -> S
  for +e: E
  for +a: Bytes()
  for +b: Bytes()
  for +p: S
  {feed_buf.slow(~E, ~S, ~step, e, Bytes.append(a, b), p) ==
    feed_buf.slow(~E, ~S, ~step, e, b, feed_buf.slow(~E, ~S, ~step, e, a, p)) : S}

def slow_split(E, S, step, e, a, b, p):
  match a:
    case SNil{}:
      {==}
    case SCon{Chr{c}, t}:
      slow_split(~E, ~S, ~step, e, t, b, step(e, p, c))

law bad_feeds_slow:
  for ~E: Data
  for ~S: Data
  for ~step: E -> S -> U32 -> S
  for ~X: Data
  for ~bad: X -> S
  for ~absorbs: @+e: E -> @+x: X -> @+c: U32 -> {step(e, bad(x), c) == bad(x) : S}
  for +e: E
  for +s: Bytes()
  for +x: X
  {feed_buf.slow(~E, ~S, ~step, e, s, bad(x)) == bad(x) : S}

def bad_feeds_slow(E, S, step, X, bad, absorbs, e, s, x):
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{c}, t}:
      %Equal.sym(S, step(e, bad(x), c), bad(x), absorbs(e, x, c)) :
        {feed_buf.slow(~E, ~S, ~step, e, t, _) == bad(x) : S}
      bad_feeds_slow(~E, ~S, ~step, ~X, ~bad, ~absorbs, e, t, x)

# the one-byte move keeps the obligation: a protocol with no runs hands
# in one.step and one.step_ok
law one.step_ok:
  for ~E: Data
  for ~S: Data
  for ~step: E -> S -> U32 -> S
  for +e: E
  for +s: Bytes()
  for p: S
  {feed_buf.last(~E, ~S, ~step, e, one.step(~E, ~S, ~step, e, s, p)) ==
    feed_buf.slow(~E, ~S, ~step, e, s, p) : S}

def one.step_ok(E, S, step, e, s, p):
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{c}, t}:
      {==}

# the fuel never matters: however many moves are left, the walk ends
# where the byte-at-a-time walk does, given that each move does
law go_is_slow:
  for ~E: Data
  for ~S: Data
  for ~step: E -> S -> U32 -> S
  for ~adv: E -> Bytes() -> S -> S & Bytes()
  for ~adv_ok: @+e: E -> @+s: Bytes() -> @p: S ->
    {feed_buf.last(~E, ~S, ~step, e, adv(e, s, p)) == feed_buf.slow(~E, ~S, ~step, e, s, p) : S}
  for +e: E
  for n: Nat
  for q: S & Bytes()
  {feed_buf.go(~E, ~S, ~step, ~adv, e, n, q) == feed_buf.last(~E, ~S, ~step, e, q) : S}

def go_is_slow(E, S, step, adv, adv_ok, e, n, q):
  match n:
    case 0n:
      {==}
    case 1n+m:
      match q:
        case (p, SNil{}):
          {==}
        case (+p, SCon{+h, +t}):
          Equal.trans(S, feed_buf.go(~E, ~S, ~step, ~adv, e, m, adv(e, SCon{h, t}, p)),
            feed_buf.last(~E, ~S, ~step, e, adv(e, SCon{h, t}, p)),
            feed_buf.slow(~E, ~S, ~step, e, SCon{h, t}, p),
            go_is_slow(~E, ~S, ~step, ~adv, ~adv_ok, e, m, adv(e, SCon{h, t}, p)),
            adv_ok(e, SCon{h, t}, p))

# LAW: the walk a server runs is the byte machine. feed_buf moves through
# a read by the protocol's own moves, runs taken whole; for every block
# and every state it lands where feed does on the block's bytes. So
# every law of feed is a law of feed_buf.
law feed_buf_is_feed:
  for ~E: Data
  for ~S: Data
  for ~step: E -> S -> U32 -> S
  for ~adv: E -> Bytes() -> S -> S & Bytes()
  for ~adv_ok: @+e: E -> @+s: Bytes() -> @p: S ->
    {feed_buf.last(~E, ~S, ~step, e, adv(e, s, p)) == feed_buf.slow(~E, ~S, ~step, e, s, p) : S}
  for +e: E
  for +b: Bytes()
  for +p: S
  {feed_buf(~E, ~S, ~step, ~adv, e, b, p) == feed(~E, ~S, ~step, e, Bytes.to_list(b), p) : S}

def feed_buf_is_feed(E, S, step, adv, adv_ok, e, b, p):
  Equal.trans(S, feed_buf(~E, ~S, ~step, ~adv, e, b, p), feed_buf.slow(~E, ~S, ~step, e, b, p),
    feed(~E, ~S, ~step, e, Bytes.to_list(b), p),
    go_is_slow(~E, ~S, ~step, ~adv, ~adv_ok, e, Bytes.len(b), (p, b)),
    slow_is_feed(~E, ~S, ~step, e, b, p))

# LAW: and chunking does not change the read on blocks either.
law feed_buf_split:
  for ~E: Data
  for ~S: Data
  for ~step: E -> S -> U32 -> S
  for ~adv: E -> Bytes() -> S -> S & Bytes()
  for ~adv_ok: @+e: E -> @+s: Bytes() -> @p: S ->
    {feed_buf.last(~E, ~S, ~step, e, adv(e, s, p)) == feed_buf.slow(~E, ~S, ~step, e, s, p) : S}
  for +e: E
  for +a: Bytes()
  for +b: Bytes()
  for +p: S
  {feed_buf(~E, ~S, ~step, ~adv, e, Bytes.append(a, b), p) ==
    feed_buf(~E, ~S, ~step, ~adv, e, b, feed_buf(~E, ~S, ~step, ~adv, e, a, p)) : S}

def feed_buf_split(E, S, step, adv, adv_ok, e, a, b, p):
  %Equal.sym(S, feed_buf(~E, ~S, ~step, ~adv, e, Bytes.append(a, b), p),
    feed(~E, ~S, ~step, e, Bytes.to_list(Bytes.append(a, b)), p),
    feed_buf_is_feed(~E, ~S, ~step, ~adv, ~adv_ok, e, Bytes.append(a, b), p)) :
    {_ == feed_buf(~E, ~S, ~step, ~adv, e, b, feed_buf(~E, ~S, ~step, ~adv, e, a, p)) : S}
  %Equal.sym(List<&2, U32>, Bytes.to_list(Bytes.append(a, b)),
    List.append(&2, U32, Bytes.to_list(a), Bytes.to_list(b)), Bytes.to_list_append(a, b)) :
    {feed(~E, ~S, ~step, e, _, p) ==
      feed_buf(~E, ~S, ~step, ~adv, e, b, feed_buf(~E, ~S, ~step, ~adv, e, a, p)) : S}
  %Equal.sym(S, feed(~E, ~S, ~step, e, List.append(&2, U32, Bytes.to_list(a), Bytes.to_list(b)), p),
    feed(~E, ~S, ~step, e, Bytes.to_list(b), feed(~E, ~S, ~step, e, Bytes.to_list(a), p)),
    feed_split(~E, ~S, ~step, e, Bytes.to_list(a), Bytes.to_list(b), p)) :
    {_ == feed_buf(~E, ~S, ~step, ~adv, e, b, feed_buf(~E, ~S, ~step, ~adv, e, a, p)) : S}
  %feed_buf_is_feed(~E, ~S, ~step, ~adv, ~adv_ok, e, a, p) :
    {feed(~E, ~S, ~step, e, Bytes.to_list(b), _) ==
      feed_buf(~E, ~S, ~step, ~adv, e, b, feed_buf(~E, ~S, ~step, ~adv, e, a, p)) : S}
  Equal.sym(S, feed_buf(~E, ~S, ~step, ~adv, e, b, feed_buf(~E, ~S, ~step, ~adv, e, a, p)),
    feed(~E, ~S, ~step, e, Bytes.to_list(b), feed_buf(~E, ~S, ~step, ~adv, e, a, p)),
    feed_buf_is_feed(~E, ~S, ~step, ~adv, ~adv_ok, e, b, feed_buf(~E, ~S, ~step, ~adv, e, a, p)))

# LAW: a refusal is never left, on blocks.
law bad_feeds_buf:
  for ~E: Data
  for ~S: Data
  for ~step: E -> S -> U32 -> S
  for ~adv: E -> Bytes() -> S -> S & Bytes()
  for ~adv_ok: @+e: E -> @+s: Bytes() -> @p: S ->
    {feed_buf.last(~E, ~S, ~step, e, adv(e, s, p)) == feed_buf.slow(~E, ~S, ~step, e, s, p) : S}
  for ~X: Data
  for ~bad: X -> S
  for ~absorbs: @+e: E -> @+x: X -> @+c: U32 -> {step(e, bad(x), c) == bad(x) : S}
  for +e: E
  for +s: Bytes()
  for +x: X
  {feed_buf(~E, ~S, ~step, ~adv, e, s, bad(x)) == bad(x) : S}

def bad_feeds_buf(E, S, step, adv, adv_ok, X, bad, absorbs, e, s, x):
  %Equal.sym(S, feed_buf(~E, ~S, ~step, ~adv, e, s, bad(x)),
    feed(~E, ~S, ~step, e, Bytes.to_list(s), bad(x)),
    feed_buf_is_feed(~E, ~S, ~step, ~adv, ~adv_ok, e, s, bad(x))) :
    {_ == bad(x) : S}
  bad_feeds(~E, ~S, ~step, ~X, ~bad, ~absorbs, e, Bytes.to_list(s), x)

# LAW: however a stream is cut into reads, the reader fed each read in
# turn lands where feed lands on the stream whole ...
law reads_is:
  for ~E: Data
  for ~S: Data
  for ~step: E -> S -> U32 -> S
  for ~adv: E -> Bytes() -> S -> S & Bytes()
  for ~adv_ok: @+e: E -> @+s: Bytes() -> @p: S ->
    {feed_buf.last(~E, ~S, ~step, e, adv(e, s, p)) == feed_buf.slow(~E, ~S, ~step, e, s, p) : S}
  for +e: E
  for +rs: List<&2, Bytes()>
  for +p: S
  {reads(~E, ~S, ~step, ~adv, e, rs, p) ==
    feed(~E, ~S, ~step, e, Bytes.to_list(Bytes.concat(rs)), p) : S}

def reads_is(E, S, step, adv, adv_ok, e, rs, p):
  match rs:
    case Nil{}:
      {==}
    case Con{+r, +t}:
      %Equal.sym(List<&2, U32>, Bytes.to_list(Bytes.append(r, Bytes.concat(t))),
        List.append(&2, U32, Bytes.to_list(r), Bytes.to_list(Bytes.concat(t))),
        Bytes.to_list_append(r, Bytes.concat(t))) :
        {reads(~E, ~S, ~step, ~adv, e, t, feed_buf(~E, ~S, ~step, ~adv, e, r, p)) ==
          feed(~E, ~S, ~step, e, _, p) : S}
      %Equal.sym(S,
        feed(~E, ~S, ~step, e, List.append(&2, U32, Bytes.to_list(r), Bytes.to_list(Bytes.concat(t))), p),
        feed(~E, ~S, ~step, e, Bytes.to_list(Bytes.concat(t)), feed(~E, ~S, ~step, e, Bytes.to_list(r), p)),
        feed_split(~E, ~S, ~step, e, Bytes.to_list(r), Bytes.to_list(Bytes.concat(t)), p)) :
        {reads(~E, ~S, ~step, ~adv, e, t, feed_buf(~E, ~S, ~step, ~adv, e, r, p)) == _ : S}
      %feed_buf_is_feed(~E, ~S, ~step, ~adv, ~adv_ok, e, r, p) :
        {reads(~E, ~S, ~step, ~adv, e, t, feed_buf(~E, ~S, ~step, ~adv, e, r, p)) ==
          feed(~E, ~S, ~step, e, Bytes.to_list(Bytes.concat(t)), _) : S}
      reads_is(~E, ~S, ~step, ~adv, ~adv_ok, e, t, feed_buf(~E, ~S, ~step, ~adv, e, r, p))

# LAW: ... and where the walk lands on the stream whole: any list of
# reads reads as their concatenation read at once.
law reads_split:
  for ~E: Data
  for ~S: Data
  for ~step: E -> S -> U32 -> S
  for ~adv: E -> Bytes() -> S -> S & Bytes()
  for ~adv_ok: @+e: E -> @+s: Bytes() -> @p: S ->
    {feed_buf.last(~E, ~S, ~step, e, adv(e, s, p)) == feed_buf.slow(~E, ~S, ~step, e, s, p) : S}
  for +e: E
  for +rs: List<&2, Bytes()>
  for +p: S
  {reads(~E, ~S, ~step, ~adv, e, rs, p) == feed_buf(~E, ~S, ~step, ~adv, e, Bytes.concat(rs), p) : S}

def reads_split(E, S, step, adv, adv_ok, e, rs, p):
  Equal.trans(S, reads(~E, ~S, ~step, ~adv, e, rs, p),
    feed(~E, ~S, ~step, e, Bytes.to_list(Bytes.concat(rs)), p),
    feed_buf(~E, ~S, ~step, ~adv, e, Bytes.concat(rs), p),
    reads_is(~E, ~S, ~step, ~adv, ~adv_ok, e, rs, p),
    Equal.sym(S, feed_buf(~E, ~S, ~step, ~adv, e, Bytes.concat(rs), p),
      feed(~E, ~S, ~step, e, Bytes.to_list(Bytes.concat(rs)), p),
      feed_buf_is_feed(~E, ~S, ~step, ~adv, ~adv_ok, e, Bytes.concat(rs), p)))
