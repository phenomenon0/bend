# bend-wire: the connection loop and the accept loop.
#
# A server is a reader (wire/reader.bend), a planner that turns what a
# read completed into replies, and the loop that runs them against a
# socket: read within a deadline, plan, write within a deadline, read
# again, until the plan ends the connection or its fuel runs out. The
# loop is the same for every protocol, so it is written here once, and
# its laws are proven once (wire/world.bend) for every protocol that
# plugs into it.
#
# It is written over two interfaces, both as template parameters, so an
# instance is the code a protocol would have written by hand, compiled
# on its own and called directly: nothing is passed at runtime and
# nothing is looked up.
#
# The effects, instantiated with IO and the real ones in wire/effects.bend,
# and with the identity monad and a scripted peer in wire/world.bend:
#
#   ~M, ~pure, ~bind   the monad
#   ~S, ~F             the socket and the file handle
#   ~rx                a timed read: TCP.poll_buf(s, max, ms)
#   ~tx                a timed write: TCP.send_buf_poll(s, bytes, ms)
#   ~clk               the clock, in ms, beside the socket
#   ~nap               sleep, beside the socket
#   ~say               a log line
#   ~fopen ~fsize ~fread ~fsend ~fclose   a file under a root: read and
#                      sent when small, sent by the kernel when not (the
#                      real ones: File.get_under opens, fstats and reads
#                      a small file in one effect, so its size, read and
#                      close are pure; wire/effects.bend's Fh)
#
# The protocol:
#
#   ~E: Data           what serving needs (a configuration); +srv: E
#   ~P: Data           a connection's state between reads: its reader,
#                      and whatever else it keeps (RESP: its store)
#   ~U: Data           the state of an upgraded connection (HTTP: a
#                      WebSocket's frame reader; Unit when none)
#   ~idle ~hdms        the idle time and the head's time, from srv
#   ~plan              a read's bytes (never empty: the peer's FIN ends
#                      the connection before the planner is asked) and
#                      the state, to the next Plan
#   ~mid               whether a message's head is in progress, which
#                      puts the next read under the head's budget
#   ~big               the reply to a head past head.cap()
#   ~uplan             the same as ~plan, for an upgraded connection
#   ~gap ~event        a stream: the wait between events, and the n-th
#                      event from the end
#   ~shut              a reply marked as its connection's last (Shut)
#   ~fhead ~miss       a file's head, for its type and length, and the
#                      reply when it cannot be opened
#   ~lnote ~lsize      an access log line, for a reply and for a file
#
# The budgets are the loop's, and hold for every protocol: a read is at
# most chunk() bytes; a head in progress may take head.cap() bytes past
# the read it began in, and --head-ms of the clock; replies wait in one
# batch that goes out once it reaches send.cap(); every send has the
# idle time as its deadline; a connection reads at most conn.fuel()
# times, and at most conn.waits() reads in a row that finish nothing.
import Base

# The interface's answers
# =======================

# what a timed read answers, and what a send answers, beside the socket
law Got:
  for -S: Type
  Type

def Got(S):
  S & Result<&1, &1, U32 & String, Maybe<&1, Bytes()>>

law Put:
  for -S: Type
  Type

def Put(S):
  S & Result<&1, &1, U32 & String, Unit>

# One piece of a reply: bytes as they are, a file to write when the
# reply is written (the root, the path under it, as bytes that go to the
# effect as they are, what ~fhead makes its head from, and whether only
# the head is wanted), a note for the access log that the next piece
# completes, or a mark that the next reply is the connection's last.
type Seg is Data:
  Raw{bs: Bytes()}
  Page{root: Bytes(), path: Bytes(), ct: Bytes(), head: Bool}
  Note{bs: Bytes()}
  Shut{}

# What the connection does next: write these segments and read again,
# read again without writing, write them and close, write them and keep
# streaming events without reading, write them and switch to the
# upgraded reader, read on the upgraded reader, or close now.
type Plan<-P: Data, -U: Data> is Data:
  Go{out: List<&2, Seg>, p2: P}
  Wait{p2: P}
  End{out: List<&2, Seg>}
  Feed{out: List<&2, Seg>, n: U32}
  Sock{out: List<&2, Seg>, wr: U}
  Hold{wr: U}
  Stop{}

# a resolved segment, logged against the note that was waiting if there
# was one, and handed straight back: the line goes out before the
# segments after it, so the log reads in the order the requests came
def flat.note(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~say: String -> M(Unit),
  ~lnote: Bytes() -> Bytes() -> String, may: Maybe<&2, Bytes()>, +out: Bytes()
) -> M(Bytes()):
  match may:
    case None{}:
      pure(Bytes(), out)
    case Some{note}:
      bind(Unit, Bytes(), say(lnote(note, out)), u => pure(Bytes(), out))

# Writing a reply
# ===============
#
# The segments of one read's answers are written in order as they are
# produced. Fixed replies wait on one block and go out in one send with
# whatever comes next. A file goes out as its head, taken from fstat of
# the descriptor that was opened, sent with whatever waited in front of
# it, then as its body by File.sendfile: on a plain socket the kernel
# copies it from the page cache to the socket, and under TLS the effect
# writes it through the session a block at a time. Either way the
# connection holds no block of the file of its own, however large the
# file, and a pipelined batch of files holds none either. (A small file
# is read and sent with its head in one send: page.small.) The body is
# exactly the length its head promised: a sendfile or a read that comes
# up short (the file shrank) fails, and the connection ends, since
# nothing after it could be framed.

# The batch budget. Fixed replies wait in one block, and once the block
# reaches send.cap() bytes it goes out before the next reply is taken:
# a pipelined read's replies come to what the peer sent and a head per
# request, and this bounds even that. Every send has the idle time as
# its deadline, so a peer that stops reading is let go rather than
# holding its slot.
def send.cap() -> U32:
  1048576

# what stays waiting after a reply brings the block to k bytes: all of
# it below the cap, none of it (it has gone out) at or past it
def batch.keep(c: Cmp, k: U32) -> U32:
  match c:
    case LT{}:
      k
    case EQ{}:
      0
    case GT{}:
      0

# the writer: the socket, the bytes waiting, and whether everything
# promised so far has gone out. Once it has not, nothing more is written.
type Em<-S: Type> is Type:
  Em{s: S, acc: Bytes(), ok: Bool}

def send.flushed(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type, m: Put(S)
) -> M(Em<S>):
  (s, r) = m
  match r:
    case Done{u}:
      pure(Em<S>, Em{s, "", True{}})
    case Fail{e}:
      pure(Em<S>, Em{s, "", False{}})

def send.held(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~tx: S -> Bytes() -> U32 -> M(Put(S)), +ms: U32, s: S, acc: Bytes(), c: Cmp
) -> M(Em<S>):
  match c:
    case LT{}:
      pure(Em<S>, Em{s, acc, True{}})
    case EQ{}:
      bind(Put(S), Em<S>, tx(s, acc, ms), m => send.flushed(~M, ~pure, ~bind, ~S, m))
    case GT{}:
      bind(Put(S), Em<S>, tx(s, acc, ms), m => send.flushed(~M, ~pure, ~bind, ~S, m))

# a reply joins the waiting block, and a block at the cap goes out
def send.hold(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~tx: S -> Bytes() -> U32 -> M(Put(S)), +ms: U32, s: S, +acc: Bytes()
) -> M(Em<S>):
  send.held(~M, ~pure, ~bind, ~S, ~tx, ms, s, acc,
    U32.cmp(U32.from_nat(Bytes.len(acc)), send.cap()))

# a file's log line: its head and the bytes its reply holds
def log.sized(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~say: String -> M(Unit),
  ~lsize: Bytes() -> Bytes() -> U32 -> String, may: Maybe<&2, Bytes()>, +hd: Bytes(), n: U32
) -> M(Unit):
  match may:
    case None{}:
      pure(Unit, Unit{})
    case Some{note}:
      say(lsize(note, hd, n))

def page.miss(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~tx: S -> Bytes() -> U32 -> M(Put(S)), ~say: String -> M(Unit),
  ~shut: Bool -> Bytes() -> Bytes(), ~miss: Bool -> Bytes(),
  ~lnote: Bytes() -> Bytes() -> String, +ms: U32, head: Bool,
  may: Maybe<&2, Bytes()>, sh: Bool, s: S, acc: Bytes()
) -> M(Em<S>):
  bind(Bytes(), Em<S>, flat.note(~M, ~pure, ~bind, ~say, ~lnote, may, shut(sh, miss(head))), out =>
    send.hold(~M, ~pure, ~bind, ~S, ~tx, ms, s, Bytes.append(acc, out)))

# after the head, the body: all n bytes of the file by the kernel, or
# the connection ends -- a send that failed or stalled, or a file that
# came up short
def page.fsent(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type, ~F: Type,
  ~fclose: F -> M(Unit), g: S & F & Result<&1, &1, U32 & String, Unit>
) -> M(Em<S>):
  (s, fr) = g
  (f, r) = fr
  bind(Unit, Em<S>, fclose(f), u =>
    pure(Em<S>, Em{s, "", Result.is_done(&1, &1, U32 & String, Unit, r)}))

def page.headed(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type, ~F: Type,
  ~fsend: S -> F -> U32 -> U32 -> U32 -> M(S & F & Result<&1, &1, U32 & String, Unit>),
  ~fclose: F -> M(Unit), +ms: U32, f: F, n: U32, m: Put(S)
) -> M(Em<S>):
  (s, r) = m
  match r:
    case Fail{e}:
      bind(Unit, Em<S>, fclose(f), u => pure(Em<S>, Em{s, "", False{}}))
    case Done{u}:
      bind(S & F & Result<&1, &1, U32 & String, Unit>, Em<S>, fsend(s, f, 0, n, ms), g =>
        page.fsent(~M, ~pure, ~bind, ~S, ~F, ~fclose, g))

# A file under page.small() bytes is read whole, and goes out with its
# head in the one send: a second send for the body would cost a small
# file more than the copy the kernel spares. A read that comes back
# short (the file shrank) ends the connection, after what it had.
def page.small() -> U32:
  16384

def page.blk(-S: Type, m: Put(S), whole: Bool) -> Em<S>:
  (s, r) = m
  Em{s, "", Result.is_done(&1, &1, U32 & String, Unit, r) && whole}

def page.read(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type, ~F: Type,
  ~tx: S -> Bytes() -> U32 -> M(Put(S)), ~fclose: F -> M(Unit), +ms: U32,
  got: F & Result<&1, &1, U32 & String, Bytes()>, +n: U32, s: S, pre: Bytes()
) -> M(Em<S>):
  (f, r) = got
  match r:
    case Fail{e}:
      bind(Unit, Em<S>, fclose(f), u => pure(Em<S>, Em{s, "", False{}}))
    case Done{+bs}:
      bind(Unit, Em<S>, fclose(f), u =>
        bind(Put(S), Em<S>, tx(s, Bytes.append(pre, bs), ms), m =>
          pure(Em<S>, page.blk(S, m, Nat.is_eq(Bytes.len(bs), U32.to_nat(n))))))

def page.body(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type, ~F: Type,
  ~tx: S -> Bytes() -> U32 -> M(Put(S)),
  ~fread: F -> U32 -> M(F & Result<&1, &1, U32 & String, Bytes()>),
  ~fsend: S -> F -> U32 -> U32 -> U32 -> M(S & F & Result<&1, &1, U32 & String, Unit>),
  ~fclose: F -> M(Unit), +ms: U32, f: F, +n: U32, s: S, pre: Bytes(), small: Bool
) -> M(Em<S>):
  match small:
    case True{}:
      bind(F & Result<&1, &1, U32 & String, Bytes()>, Em<S>, fread(f, n), got =>
        page.read(~M, ~pure, ~bind, ~S, ~F, ~tx, ~fclose, ms, got, n, s, pre))
    case False{}:
      bind(Put(S), Em<S>, tx(s, pre, ms), m =>
        page.headed(~M, ~pure, ~bind, ~S, ~F, ~fsend, ~fclose, ms, f, n, m))

def page.start(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type, ~F: Type,
  ~tx: S -> Bytes() -> U32 -> M(Put(S)), ~say: String -> M(Unit),
  ~fread: F -> U32 -> M(F & Result<&1, &1, U32 & String, Bytes()>),
  ~fsend: S -> F -> U32 -> U32 -> U32 -> M(S & F & Result<&1, &1, U32 & String, Unit>),
  ~fclose: F -> M(Unit), ~lsize: Bytes() -> Bytes() -> U32 -> String, +ms: U32, f: F, +n: U32,
  +hd: Bytes(), head: Bool, may: Maybe<&2, Bytes()>, s: S, acc: Bytes()
) -> M(Em<S>):
  match head:
    case True{}:
      bind(Unit, Em<S>, log.sized(~M, ~pure, ~bind, ~say, ~lsize, may, hd, 0), u =>
        bind(Unit, Em<S>, fclose(f), u2 =>
          send.hold(~M, ~pure, ~bind, ~S, ~tx, ms, s, Bytes.append(acc, hd))))
    case False{}:
      bind(Unit, Em<S>, log.sized(~M, ~pure, ~bind, ~say, ~lsize, may, hd, n), u =>
        page.body(~M, ~pure, ~bind, ~S, ~F, ~tx, ~fread, ~fsend, ~fclose, ms, f, n, s,
          Bytes.append(acc, hd), U32.is_lt(n, page.small())))

def page.sized(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type, ~F: Type,
  ~tx: S -> Bytes() -> U32 -> M(Put(S)), ~say: String -> M(Unit),
  ~fread: F -> U32 -> M(F & Result<&1, &1, U32 & String, Bytes()>),
  ~fsend: S -> F -> U32 -> U32 -> U32 -> M(S & F & Result<&1, &1, U32 & String, Unit>),
  ~fclose: F -> M(Unit), ~shut: Bool -> Bytes() -> Bytes(),
  ~fhead: Bytes() -> U32 -> Bytes(), ~miss: Bool -> Bytes(),
  ~lnote: Bytes() -> Bytes() -> String, ~lsize: Bytes() -> Bytes() -> U32 -> String, +ms: U32,
  got: F & Result<&1, &1, U32 & String, U32>, ct: Bytes(), head: Bool,
  may: Maybe<&2, Bytes()>, sh: Bool, s: S, acc: Bytes()
) -> M(Em<S>):
  (f, r) = got
  match r:
    case Fail{e}:
      bind(Unit, Em<S>, fclose(f), u =>
        page.miss(~M, ~pure, ~bind, ~S, ~tx, ~say, ~shut, ~miss, ~lnote, ms, head, may, sh, s,
          acc))
    case Done{+n}:
      page.start(~M, ~pure, ~bind, ~S, ~F, ~tx, ~say, ~fread, ~fsend, ~fclose, ~lsize, ms, f, n,
        shut(sh, fhead(ct, n)), head, may, s, acc)

def page.opened(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type, ~F: Type,
  ~tx: S -> Bytes() -> U32 -> M(Put(S)), ~say: String -> M(Unit),
  ~fsize: F -> M(F & Result<&1, &1, U32 & String, U32>),
  ~fread: F -> U32 -> M(F & Result<&1, &1, U32 & String, Bytes()>),
  ~fsend: S -> F -> U32 -> U32 -> U32 -> M(S & F & Result<&1, &1, U32 & String, Unit>),
  ~fclose: F -> M(Unit), ~shut: Bool -> Bytes() -> Bytes(),
  ~fhead: Bytes() -> U32 -> Bytes(), ~miss: Bool -> Bytes(),
  ~lnote: Bytes() -> Bytes() -> String, ~lsize: Bytes() -> Bytes() -> U32 -> String, +ms: U32,
  m: S & Result<&1, &1, U32 & String, F>, ct: Bytes(), head: Bool,
  may: Maybe<&2, Bytes()>, sh: Bool, acc: Bytes()
) -> M(Em<S>):
  (s, r) = m
  match r:
    case Fail{e}:
      page.miss(~M, ~pure, ~bind, ~S, ~tx, ~say, ~shut, ~miss, ~lnote, ms, head, may, sh, s, acc)
    case Done{f}:
      bind(F & Result<&1, &1, U32 & String, U32>, Em<S>, fsize(f), got =>
        page.sized(~M, ~pure, ~bind, ~S, ~F, ~tx, ~say, ~fread, ~fsend, ~fclose, ~shut, ~fhead, ~miss,
            ~lnote, ~lsize, ms, got, ct, head, may, sh, s, acc))

def send.page(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type, ~F: Type,
  ~tx: S -> Bytes() -> U32 -> M(Put(S)), ~say: String -> M(Unit),
  ~fopen: S -> String -> String -> M(S & Result<&1, &1, U32 & String, F>),
  ~fsize: F -> M(F & Result<&1, &1, U32 & String, U32>),
  ~fread: F -> U32 -> M(F & Result<&1, &1, U32 & String, Bytes()>),
  ~fsend: S -> F -> U32 -> U32 -> U32 -> M(S & F & Result<&1, &1, U32 & String, Unit>),
  ~fclose: F -> M(Unit), ~shut: Bool -> Bytes() -> Bytes(),
  ~fhead: Bytes() -> U32 -> Bytes(), ~miss: Bool -> Bytes(),
  ~lnote: Bytes() -> Bytes() -> String, ~lsize: Bytes() -> Bytes() -> U32 -> String, +ms: U32,
  root: Bytes(), path: Bytes(), ct: Bytes(), head: Bool,
  may: Maybe<&2, Bytes()>, sh: Bool, st: Em<S>
) -> M(Em<S>):
  match st:
    case Em{s, acc, ok}:
      match ok:
        case False{}:
          pure(Em<S>, Em{s, acc, False{}})
        case True{}:
          bind(S & Result<&1, &1, U32 & String, F>, Em<S>, fopen(s, root, path), m =>
            page.opened(~M, ~pure, ~bind, ~S, ~F, ~tx, ~say, ~fsize, ~fread, ~fsend, ~fclose, ~shut,
                ~fhead, ~miss, ~lnote, ~lsize, ms, m, ct, head, may, sh, acc))

def send.raw(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~tx: S -> Bytes() -> U32 -> M(Put(S)), ~say: String -> M(Unit),
  ~lnote: Bytes() -> Bytes() -> String, +ms: U32, may: Maybe<&2, Bytes()>, bs: Bytes(),
  st: Em<S>
) -> M(Em<S>):
  match st:
    case Em{s, acc, ok}:
      match ok:
        case False{}:
          pure(Em<S>, Em{s, acc, False{}})
        case True{}:
          bind(Bytes(), Em<S>, flat.note(~M, ~pure, ~bind, ~say, ~lnote, may, bs), out =>
            send.hold(~M, ~pure, ~bind, ~S, ~tx, ms, s, Bytes.append(acc, out)))

def send.fin(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type, m: Put(S),
  ok: Bool
) -> M(Put(S)):
  (s, r) = m
  match ok:
    case True{}:
      pure(Put(S), (s, r))
    case False{}:
      pure(Put(S), (s, Fail{(5, "a file ended before the length its head promised")}))

def send.end(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~tx: S -> Bytes() -> U32 -> M(Put(S)), +ms: U32, st: Em<S>
) -> M(Put(S)):
  match st:
    case Em{s, acc, ok}:
      bind(Put(S), Put(S), tx(s, acc, ms), m => send.fin(~M, ~pure, ~bind, ~S, m, ok))

# a Shut before a reply marks the one that ends its connection
def send.go(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type, ~F: Type,
  ~tx: S -> Bytes() -> U32 -> M(Put(S)), ~say: String -> M(Unit),
  ~fopen: S -> String -> String -> M(S & Result<&1, &1, U32 & String, F>),
  ~fsize: F -> M(F & Result<&1, &1, U32 & String, U32>),
  ~fread: F -> U32 -> M(F & Result<&1, &1, U32 & String, Bytes()>),
  ~fsend: S -> F -> U32 -> U32 -> U32 -> M(S & F & Result<&1, &1, U32 & String, Unit>),
  ~fclose: F -> M(Unit), ~shut: Bool -> Bytes() -> Bytes(),
  ~fhead: Bytes() -> U32 -> Bytes(), ~miss: Bool -> Bytes(),
  ~lnote: Bytes() -> Bytes() -> String, ~lsize: Bytes() -> Bytes() -> U32 -> String,
  xs: List<&2, Seg>, +ms: U32, may: Maybe<&2, Bytes()>, sh: Bool, st: Em<S>
) -> M(Put(S)):
  match xs:
    case Nil{}:
      send.end(~M, ~pure, ~bind, ~S, ~tx, ms, st)
    case Con{g, t}:
      match g:
        case Note{bs}:
          send.go(~M, ~pure, ~bind, ~S, ~F, ~tx, ~say, ~fopen, ~fsize, ~fread, ~fsend, ~fclose, ~shut,
              ~fhead, ~miss, ~lnote, ~lsize, t, ms, Some{bs}, sh, st)
        case Shut{}:
          send.go(~M, ~pure, ~bind, ~S, ~F, ~tx, ~say, ~fopen, ~fsize, ~fread, ~fsend, ~fclose, ~shut,
              ~fhead, ~miss, ~lnote, ~lsize, t, ms, may, True{}, st)
        case Raw{bs}:
          bind(Em<S>, Put(S), send.raw(~M, ~pure, ~bind, ~S, ~tx, ~say, ~lnote, ms, may,
              shut(sh, bs), st), st2 =>
            send.go(~M, ~pure, ~bind, ~S, ~F, ~tx, ~say, ~fopen, ~fsize, ~fread, ~fsend, ~fclose, ~shut,
                ~fhead, ~miss, ~lnote, ~lsize, t, ms, None{}, False{}, st2))
        case Page{root, path, ct, head}:
          bind(Em<S>, Put(S),
            send.page(~M, ~pure, ~bind, ~S, ~F, ~tx, ~say, ~fopen, ~fsize, ~fread, ~fsend, ~fclose,
                ~shut, ~fhead, ~miss, ~lnote, ~lsize, ms, root, path, ct, head, may, sh, st),
            st2 =>
            send.go(~M, ~pure, ~bind, ~S, ~F, ~tx, ~say, ~fopen, ~fsize, ~fread, ~fsend, ~fclose, ~shut,
                ~fhead, ~miss, ~lnote, ~lsize, t, ms, None{}, False{}, st2))

# The one hook the connection loop calls: write a plan's segments to the
# socket, in order, streaming files, each send within ms of progress;
# the result fails when the socket failed, stalled, or a file came up
# short, and the connection then ends.
def send.segs(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type, ~F: Type,
  ~tx: S -> Bytes() -> U32 -> M(Put(S)), ~say: String -> M(Unit),
  ~fopen: S -> String -> String -> M(S & Result<&1, &1, U32 & String, F>),
  ~fsize: F -> M(F & Result<&1, &1, U32 & String, U32>),
  ~fread: F -> U32 -> M(F & Result<&1, &1, U32 & String, Bytes()>),
  ~fsend: S -> F -> U32 -> U32 -> U32 -> M(S & F & Result<&1, &1, U32 & String, Unit>),
  ~fclose: F -> M(Unit), ~shut: Bool -> Bytes() -> Bytes(),
  ~fhead: Bytes() -> U32 -> Bytes(), ~miss: Bool -> Bytes(),
  ~lnote: Bytes() -> Bytes() -> String, ~lsize: Bytes() -> Bytes() -> U32 -> String, s: S,
  xs: List<&2, Seg>, +ms: U32
) -> M(Put(S)):
  send.go(~M, ~pure, ~bind, ~S, ~F, ~tx, ~say, ~fopen, ~fsize, ~fread, ~fsend, ~fclose, ~shut, ~fhead,
      ~miss, ~lnote, ~lsize, xs, ms, None{}, False{}, Em{s, "", True{}})

# Reading
# =======

# the plan after one read. An empty read is the peer's FIN: nothing
# more will ever arrive, so the connection ends here rather than
# reading again (as first written the HTTP engine read again, and one
# peer that connected and closed without a byte cost most of a core in
# passes until the fuel ran out). Anything else goes to the planner.
def plan.read(
  ~E: Data, ~P: Data, ~U: Data, ~plan: E -> Bytes() -> P -> Plan<P, U>, +srv: E, buf: Bytes(),
  p: P
) -> Plan<P, U>:
  match buf:
    case SNil{}:
      Stop{}
    case SCon{b, bs}:
      plan(srv, SCon{b, bs}, p)

# what a timed read gave: bytes to plan from, the peer's silence past
# the idle time (the connection ends), or a failure (it ends)
def plan.may(
  ~E: Data, ~P: Data, ~U: Data, ~plan: E -> Bytes() -> P -> Plan<P, U>, -S: Type, +srv: E, s: S,
  may: Maybe<&1, Bytes()>, p: P
) -> S & Plan<P, U>:
  match may:
    case None{}:
      (s, Stop{})
    case Some{buf}:
      (s, plan.read(~E, ~P, ~U, ~plan, srv, buf, p))

def plan.polled(
  ~E: Data, ~P: Data, ~U: Data, ~plan: E -> Bytes() -> P -> Plan<P, U>, -S: Type, +srv: E, s: S,
  r: Result<&1, &1, U32 & String, Maybe<&1, Bytes()>>, p: P
) -> S & Plan<P, U>:
  match r:
    case Done{may}:
      plan.may(~E, ~P, ~U, ~plan, S, srv, s, may, p)
    case Fail{e}:
      (s, Stop{})

# the socket and the plan, out of one timed read
def plan.poll(
  ~E: Data, ~P: Data, ~U: Data, ~plan: E -> Bytes() -> P -> Plan<P, U>, -S: Type, +srv: E,
  m: Got(S), p: P
) -> S & Plan<P, U>:
  (s, r) = m
  plan.polled(~E, ~P, ~U, ~plan, S, srv, s, r, p)

# the most one read takes
def chunk() -> U32:
  16384

# The head being read, for its budget. NoHead{} is no head in progress
# (or a body, which the idle time alone bounds); Begun{} is a head the
# last read began, whose clock starts now; Since{t0, n} is one that began
# at t0 (the clock, ms) and has had n bytes since the read it began in.
type Hw is Data:
  NoHead{}
  Begun{}
  Since{t0: Nat, n: U32}

# read the next chunk, within the idle time, and plan from it. Splitting
# the send's socket out here is what lets the connection loop below be
# one self-recursive def.
def turn.s(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~rx: S -> U32 -> U32 -> M(Got(S)), ~E: Data, ~P: Data, ~U: Data, ~idle: E -> U32,
  ~plan: E -> Bytes() -> P -> Plan<P, U>, +srv: E, s: S, p: P
) -> M((S & Plan<P, U>) & Hw):
  bind(Got(S), (S & Plan<P, U>) & Hw, rx(s, chunk(), idle(srv)), m =>
    pure((S & Plan<P, U>) & Hw, (plan.poll(~E, ~P, ~U, ~plan, S, srv, m, p), NoHead{})))

# the watch after a read that finished no message: a head still in
# progress keeps its clock, one just begun gets one
def hw.next(mid: Bool, hw: Hw) -> Hw:
  match mid:
    case False{}:
      NoHead{}
    case True{}:
      match hw:
        case NoHead{}:
          Begun{}
        case Begun{}:
          Begun{}
        case Since{t0, n}:
          Since{t0, n}

# the most bytes a head may take after the read it began in. A read is
# at most chunk() bytes, so every head under 16 KiB is read whole and
# none past 32 KiB ever is; past it, the answer is ~big and a close.
def head.cap() -> U32:
  16384

def plan.sized(
  ~E: Data, ~P: Data, ~U: Data, ~plan: E -> Bytes() -> P -> Plan<P, U>, ~big: Bytes(), -S: Type,
  +srv: E, s: S, buf: Bytes(), p: P, t0: Nat, n: U32, over: Bool
) -> (S & Plan<P, U>) & Hw:
  match over:
    case True{}:
      ((s, End{[Shut{}, Raw{big}]}), NoHead{})
    case False{}:
      ((s, plan.read(~E, ~P, ~U, ~plan, srv, buf, p)), Since{t0, n})

def plan.counted(
  ~E: Data, ~P: Data, ~U: Data, ~plan: E -> Bytes() -> P -> Plan<P, U>, ~big: Bytes(), -S: Type,
  +srv: E, s: S, may: Maybe<&1, Bytes()>, p: P, t0: Nat, n: U32
) -> (S & Plan<P, U>) & Hw:
  match may:
    case None{}:
      ((s, Stop{}), NoHead{})
    case Some{+buf}:
      +k = (n + U32.from_nat(Bytes.len(buf)) : U32)
      plan.sized(~E, ~P, ~U, ~plan, ~big, S, srv, s, buf, p, t0, k, U32.is_lt(head.cap(), k))

def plan.headed(
  ~E: Data, ~P: Data, ~U: Data, ~plan: E -> Bytes() -> P -> Plan<P, U>, ~big: Bytes(), -S: Type,
  +srv: E, m: Got(S), p: P, t0: Nat, n: U32
) -> (S & Plan<P, U>) & Hw:
  (s, r) = m
  match r:
    case Done{may}:
      plan.counted(~E, ~P, ~U, ~plan, ~big, S, srv, s, may, p, t0, n)
    case Fail{e}:
      ((s, Stop{}), NoHead{})

# a read that continues a head waits for the idle time or for what is
# left of the head's time, whichever is less; a head out of time is
# dropped, as a silent peer is
def turn.left(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~rx: S -> U32 -> U32 -> M(Got(S)), ~E: Data, ~P: Data, ~U: Data, ~idle: E -> U32,
  ~hdms: E -> U32, ~plan: E -> Bytes() -> P -> Plan<P, U>, ~big: Bytes(), +srv: E, s: S, p: P,
  t0: Nat, n: U32, +el: Nat, ok: Bool
) -> M((S & Plan<P, U>) & Hw):
  match ok:
    case False{}:
      pure((S & Plan<P, U>) & Hw, ((s, Stop{}), NoHead{}))
    case True{}:
      bind(Got(S), (S & Plan<P, U>) & Hw,
        rx(s, chunk(), U32.min(idle(srv), U32.from_nat(Nat.sub(U32.to_nat(hdms(srv)), el)))),
        m => pure((S & Plan<P, U>) & Hw, plan.headed(~E, ~P, ~U, ~plan, ~big, S, srv, m, p, t0,
            n)))

def turn.at(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~rx: S -> U32 -> U32 -> M(Got(S)), ~E: Data, ~P: Data, ~U: Data, ~idle: E -> U32,
  ~hdms: E -> U32, ~plan: E -> Bytes() -> P -> Plan<P, U>, ~big: Bytes(), +srv: E, s: S, p: P,
  +t0: Nat, n: U32, now: Nat
) -> M((S & Plan<P, U>) & Hw):
  +el = Nat.sub(now, t0)
  turn.left(~M, ~pure, ~bind, ~S, ~rx, ~E, ~P, ~U, ~idle, ~hdms, ~plan, ~big, srv, s, p, t0, n,
    el, Nat.is_lt(el, U32.to_nat(hdms(srv))))

# the clock read at a head's first read starts its time
def turn.fresh.at(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~rx: S -> U32 -> U32 -> M(Got(S)), ~E: Data, ~P: Data, ~U: Data, ~idle: E -> U32,
  ~hdms: E -> U32, ~plan: E -> Bytes() -> P -> Plan<P, U>, ~big: Bytes(), +srv: E, s: S, p: P,
  +now: Nat
) -> M((S & Plan<P, U>) & Hw):
  turn.at(~M, ~pure, ~bind, ~S, ~rx, ~E, ~P, ~U, ~idle, ~hdms, ~plan, ~big, srv, s, p, now, 0,
    now)

def turn.fresh(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~rx: S -> U32 -> U32 -> M(Got(S)), ~E: Data, ~P: Data, ~U: Data, ~idle: E -> U32,
  ~hdms: E -> U32, ~plan: E -> Bytes() -> P -> Plan<P, U>, ~big: Bytes(), +srv: E, sn: S & Nat,
  p: P
) -> M((S & Plan<P, U>) & Hw):
  (s, now) = sn
  turn.fresh.at(~M, ~pure, ~bind, ~S, ~rx, ~E, ~P, ~U, ~idle, ~hdms, ~plan, ~big, srv, s, p, now)

def turn.since(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~rx: S -> U32 -> U32 -> M(Got(S)), ~E: Data, ~P: Data, ~U: Data, ~idle: E -> U32,
  ~hdms: E -> U32, ~plan: E -> Bytes() -> P -> Plan<P, U>, ~big: Bytes(), +srv: E, sn: S & Nat,
  p: P, t0: Nat, n: U32
) -> M((S & Plan<P, U>) & Hw):
  (s, now) = sn
  turn.at(~M, ~pure, ~bind, ~S, ~rx, ~E, ~P, ~U, ~idle, ~hdms, ~plan, ~big, srv, s, p, t0, n,
    now)

# read the next chunk for the reader, under the head's budget when a
# head is in progress
def turn.h(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~rx: S -> U32 -> U32 -> M(Got(S)), ~clk: S -> M(S & Nat), ~E: Data, ~P: Data, ~U: Data,
  ~idle: E -> U32, ~hdms: E -> U32, ~plan: E -> Bytes() -> P -> Plan<P, U>, ~big: Bytes(),
  +srv: E, s: S, p: P, hw: Hw
) -> M((S & Plan<P, U>) & Hw):
  match hw:
    case NoHead{}:
      turn.s(~M, ~pure, ~bind, ~S, ~rx, ~E, ~P, ~U, ~idle, ~plan, srv, s, p)
    case Begun{}:
      bind(S & Nat, (S & Plan<P, U>) & Hw, clk(s), sn =>
        turn.fresh(~M, ~pure, ~bind, ~S, ~rx, ~E, ~P, ~U, ~idle, ~hdms, ~plan, ~big, srv, sn, p))
    case Since{t0, n}:
      bind(S & Nat, (S & Plan<P, U>) & Hw, clk(s), sn =>
        turn.since(~M, ~pure, ~bind, ~S, ~rx, ~E, ~P, ~U, ~idle, ~hdms, ~plan, ~big, srv, sn, p,
          t0, n))

def turn(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~rx: S -> U32 -> U32 -> M(Got(S)), ~clk: S -> M(S & Nat), ~E: Data, ~P: Data, ~U: Data,
  ~idle: E -> U32, ~hdms: E -> U32, ~plan: E -> Bytes() -> P -> Plan<P, U>, ~big: Bytes(),
  +srv: E, sent: Put(S), p: P, hw: Hw
) -> M((S & Plan<P, U>) & Hw):
  (s, r) = sent
  match r:
    case Fail{e}:
      pure((S & Plan<P, U>) & Hw, ((s, Stop{}), NoHead{}))
    case Done{u}:
      turn.h(~M, ~pure, ~bind, ~S, ~rx, ~clk, ~E, ~P, ~U, ~idle, ~hdms, ~plan, ~big, srv, s, p, hw)

# An upgraded connection: its reads go to the upgraded planner, and an
# empty one, a silence past the idle time or a failure ends it.
def plan.um(
  ~P: Data, ~U: Data, ~uplan: U -> Bytes() -> Plan<P, U>, -S: Type, s: S,
  may: Maybe<&1, Bytes()>, wr: U
) -> S & Plan<P, U>:
  match may:
    case None{}:
      (s, Stop{})
    case Some{bs}:
      match bs:
        case SNil{}:
          (s, Stop{})
        case SCon{b, t}:
          (s, uplan(wr, SCon{b, t}))

def plan.ur(
  ~P: Data, ~U: Data, ~uplan: U -> Bytes() -> Plan<P, U>, -S: Type, s: S,
  r: Result<&1, &1, U32 & String, Maybe<&1, Bytes()>>, wr: U
) -> S & Plan<P, U>:
  match r:
    case Done{may}:
      plan.um(~P, ~U, ~uplan, S, s, may, wr)
    case Fail{e}:
      (s, Stop{})

def plan.up(~P: Data, ~U: Data, ~uplan: U -> Bytes() -> Plan<P, U>, -S: Type, m: Got(S), wr: U) ->
  S & Plan<P, U>:
  (s, r) = m
  plan.ur(~P, ~U, ~uplan, S, s, r, wr)

def turn.wr(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~rx: S -> U32 -> U32 -> M(Got(S)), ~E: Data, ~P: Data, ~U: Data, ~idle: E -> U32,
  ~uplan: U -> Bytes() -> Plan<P, U>, +srv: E, s: S, wr: U
) -> M(S & Plan<P, U>):
  bind(Got(S), S & Plan<P, U>, rx(s, chunk(), idle(srv)), m =>
    pure(S & Plan<P, U>, plan.up(~P, ~U, ~uplan, S, m, wr)))

# after an upgraded connection's replies: a send that failed or stalled
# ends the connection, as it does for requests. As first written (the
# HTTP engine's WebSocket) this read on whatever the send said, so a
# peer that sent pings and never read held its connection for as many
# sends as the fuel allowed, each one waiting out the idle time.
def turn.up(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~rx: S -> U32 -> U32 -> M(Got(S)), ~E: Data, ~P: Data, ~U: Data, ~idle: E -> U32,
  ~uplan: U -> Bytes() -> Plan<P, U>, +srv: E, sent: Put(S), wr: U
) -> M(S & Plan<P, U>):
  (s, r) = sent
  match r:
    case Fail{e}:
      pure(S & Plan<P, U>, (s, Stop{}))
    case Done{u}:
      turn.wr(~M, ~pure, ~bind, ~S, ~rx, ~E, ~P, ~U, ~idle, ~uplan, srv, s, wr)

# A stream: the next event, or the end of the stream. A stream
# terminates because the count runs out, the same way a connection
# does: no @unsafe, and a peer that goes quiet still cannot hold a
# computation open forever.
def plan.more(~P: Data, ~U: Data, ~event: U32 -> Bytes(), -S: Type, s: S, +n: U32, done: Bool) ->
  S & Plan<P, U>:
  match done:
    case True{}:
      (s, Stop{})
    case False{}:
      (s, Feed{[Raw{event(n)}], (n - 1 : U32)})

def plan.next(
  ~P: Data, ~U: Data, ~event: U32 -> Bytes(), -S: Type, s: S,
  r: Result<&1, &1, U32 & String, Unit>, +n: U32
) -> S & Plan<P, U>:
  match r:
    case Done{u}:
      plan.more(~P, ~U, ~event, S, s, n, U32.is_zero(n))
    case Fail{e}:
      (s, Stop{})

# wait, then plan the next event. The loop writes on its own clock and
# reads nothing, so the reader and the writer never contend for the one
# socket the connection owns.
def tick(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~nap: S -> U32 -> M(S), ~P: Data, ~U: Data, ~gap: U32, ~event: U32 -> Bytes(), sent: Put(S),
  n: U32
) -> M(S & Plan<P, U>):
  (s, r) = sent
  bind(S, S & Plan<P, U>, nap(s, gap), s2 => pure(S & Plan<P, U>, plan.next(~P, ~U, ~event, S, s2,
      r, n)))

# The connection
# ==============

# the most chunks one connection may ever ask for. It is a real bound,
# not a formality: it is what stops a peer from holding a computation
# open forever, and it is why conn needs no @unsafe.
def conn.fuel() -> Nat:
  U32.to_nat(1048576)

# the most reads in a row that may finish no message. A head arrives
# in one or two chunks; one dribbled a byte at a time, each inside the
# idle time, is not a client and is dropped after this many.
def conn.waits() -> Nat:
  64n

# The socket, out of what its last send answered.
def put.s(-S: Type, m: Put(S)) -> S:
  (s, r) = m
  s

# One connection. f is the most chunks it will ever read, so the loop
# terminates by Bend's own rule rather than by @unsafe: a peer that
# dribbles bytes forever runs the fuel out and is dropped. The loop
# answers the socket when the connection is over; the caller closes it.
# The watch rides beside the plan: a read that finishes no message
# keeps the head's clock and count, and one that finishes one starts
# them over for whatever head it left begun.
def conn(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type, ~F: Type,
  ~rx: S -> U32 -> U32 -> M(Got(S)), ~tx: S -> Bytes() -> U32 -> M(Put(S)),
  ~clk: S -> M(S & Nat), ~nap: S -> U32 -> M(S), ~say: String -> M(Unit),
  ~fopen: S -> String -> String -> M(S & Result<&1, &1, U32 & String, F>),
  ~fsize: F -> M(F & Result<&1, &1, U32 & String, U32>),
  ~fread: F -> U32 -> M(F & Result<&1, &1, U32 & String, Bytes()>),
  ~fsend: S -> F -> U32 -> U32 -> U32 -> M(S & F & Result<&1, &1, U32 & String, Unit>),
  ~fclose: F -> M(Unit), ~E: Data, ~P: Data, ~U: Data, ~idle: E -> U32, ~hdms: E -> U32,
  ~plan: E -> Bytes() -> P -> Plan<P, U>, ~mid: P -> Bool, ~big: Bytes(),
  ~uplan: U -> Bytes() -> Plan<P, U>, ~gap: U32, ~event: U32 -> Bytes(),
  ~shut: Bool -> Bytes() -> Bytes(), ~fhead: Bytes() -> U32 -> Bytes(),
  ~miss: Bool -> Bytes(), ~lnote: Bytes() -> Bytes() -> String,
  ~lsize: Bytes() -> Bytes() -> U32 -> String, f: Nat, +srv: E, sph: (S & Plan<P, U>) & Hw, w: Nat
) -> M(S):
  match f:
    case 0n:
      ((s, pl), hw) = sph
      pure(S, s)
    case 1n+g:
      ((s, pl), hw) = sph
      match pl:
        case Stop{}:
          pure(S, s)
        case End{out}:
          bind(Put(S), S, send.segs(~M, ~pure, ~bind, ~S, ~F, ~tx, ~say, ~fopen, ~fsize,
              ~fread, ~fsend, ~fclose, ~shut, ~fhead, ~miss, ~lnote, ~lsize, s, out, idle(srv)), m =>
            pure(S, put.s(S, m)))
        case Wait{+p2}:
          match w:
            case 0n:
              pure(S, s)
            case 1n+v:
              bind((S & Plan<P, U>) & Hw, S, turn.h(~M, ~pure, ~bind, ~S, ~rx, ~clk, ~E, ~P, ~U,
                  ~idle, ~hdms, ~plan, ~big, srv, s, p2, hw.next(mid(p2), hw)),
                sp2 => conn(~M, ~pure, ~bind, ~S, ~F, ~rx, ~tx, ~clk, ~nap, ~say, ~fopen, ~fsize,
                    ~fread, ~fsend, ~fclose, ~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap,
                    ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, g, srv, sp2, v))
        case Feed{out, n}:
          bind(Put(S), S, send.segs(~M, ~pure, ~bind, ~S, ~F, ~tx, ~say, ~fopen, ~fsize,
              ~fread, ~fsend, ~fclose, ~shut, ~fhead, ~miss, ~lnote, ~lsize, s, out, idle(srv)), m =>
            bind(S & Plan<P, U>, S, tick(~M, ~pure, ~bind, ~S, ~nap, ~P, ~U, ~gap, ~event, m, n),
              sp2 =>
              conn(~M, ~pure, ~bind, ~S, ~F, ~rx, ~tx, ~clk, ~nap, ~say, ~fopen, ~fsize,
                  ~fread, ~fsend, ~fclose, ~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap,
                  ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, g, srv, (sp2, NoHead{}),
                  conn.waits())))
        case Sock{out, wr}:
          bind(Put(S), S, send.segs(~M, ~pure, ~bind, ~S, ~F, ~tx, ~say, ~fopen, ~fsize,
              ~fread, ~fsend, ~fclose, ~shut, ~fhead, ~miss, ~lnote, ~lsize, s, out, idle(srv)), m =>
            bind(S & Plan<P, U>, S, turn.up(~M, ~pure, ~bind, ~S, ~rx, ~E, ~P, ~U, ~idle, ~uplan,
                srv, m, wr), sp2 =>
              conn(~M, ~pure, ~bind, ~S, ~F, ~rx, ~tx, ~clk, ~nap, ~say, ~fopen, ~fsize,
                  ~fread, ~fsend, ~fclose, ~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap,
                  ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, g, srv, (sp2, NoHead{}),
                  conn.waits())))
        case Hold{wr}:
          match w:
            case 0n:
              pure(S, s)
            case 1n+v:
              bind(S & Plan<P, U>, S, turn.wr(~M, ~pure, ~bind, ~S, ~rx, ~E, ~P, ~U, ~idle, ~uplan,
                  srv, s, wr), sp2 =>
                conn(~M, ~pure, ~bind, ~S, ~F, ~rx, ~tx, ~clk, ~nap, ~say, ~fopen, ~fsize,
                    ~fread, ~fsend, ~fclose, ~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap,
                    ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, g, srv, (sp2, NoHead{}), v))
        case Go{out, +p2}:
          bind(Put(S), S, send.segs(~M, ~pure, ~bind, ~S, ~F, ~tx, ~say, ~fopen, ~fsize,
              ~fread, ~fsend, ~fclose, ~shut, ~fhead, ~miss, ~lnote, ~lsize, s, out, idle(srv)), m =>
            bind((S & Plan<P, U>) & Hw, S, turn(~M, ~pure, ~bind, ~S, ~rx, ~clk, ~E, ~P, ~U,
                ~idle, ~hdms, ~plan, ~big, srv, m, p2, hw.next(mid(p2), NoHead{})),
              sp2 => conn(~M, ~pure, ~bind, ~S, ~F, ~rx, ~tx, ~clk, ~nap, ~say, ~fopen, ~fsize,
                  ~fread, ~fsend, ~fclose, ~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap,
                  ~event, ~shut, ~fhead, ~miss, ~lnote, ~lsize, g, srv, sp2, conn.waits())))

# A connection from its first read, with the state p0 a fresh connection
# starts in, to the socket it leaves to be closed.
def conn.start(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type, ~F: Type,
  ~rx: S -> U32 -> U32 -> M(Got(S)), ~tx: S -> Bytes() -> U32 -> M(Put(S)),
  ~clk: S -> M(S & Nat), ~nap: S -> U32 -> M(S), ~say: String -> M(Unit),
  ~fopen: S -> String -> String -> M(S & Result<&1, &1, U32 & String, F>),
  ~fsize: F -> M(F & Result<&1, &1, U32 & String, U32>),
  ~fread: F -> U32 -> M(F & Result<&1, &1, U32 & String, Bytes()>),
  ~fsend: S -> F -> U32 -> U32 -> U32 -> M(S & F & Result<&1, &1, U32 & String, Unit>),
  ~fclose: F -> M(Unit), ~E: Data, ~P: Data, ~U: Data, ~idle: E -> U32, ~hdms: E -> U32,
  ~plan: E -> Bytes() -> P -> Plan<P, U>, ~mid: P -> Bool, ~big: Bytes(),
  ~uplan: U -> Bytes() -> Plan<P, U>, ~gap: U32, ~event: U32 -> Bytes(),
  ~shut: Bool -> Bytes() -> Bytes(), ~fhead: Bytes() -> U32 -> Bytes(),
  ~miss: Bool -> Bytes(), ~lnote: Bytes() -> Bytes() -> String,
  ~lsize: Bytes() -> Bytes() -> U32 -> String, +srv: E, p0: P, s: S
) -> M(S):
  bind(Got(S), S, rx(s, chunk(), idle(srv)), m =>
    conn(~M, ~pure, ~bind, ~S, ~F, ~rx, ~tx, ~clk, ~nap, ~say, ~fopen, ~fsize, ~fread, ~fsend, ~fclose,
        ~E, ~P, ~U, ~idle, ~hdms, ~plan, ~mid, ~big, ~uplan, ~gap, ~event, ~shut, ~fhead, ~miss,
        ~lnote, ~lsize, conn.fuel(), srv, (plan.poll(~E, ~P, ~U, ~plan, S, srv, m, p0), NoHead{}),
        conn.waits()))

# Defaults
# ========
#
# The hooks of a protocol that uses less than the loop offers: no head
# to budget, no upgrade, no stream, no files, no access log. (An event
# is never sent without a Feed, but the liveness law asks every event
# to be non-empty, so the default one is a line end: world.bend's
# no.event_ok.)
def no.mid(~P: Data, p: P) -> Bool:
  False{}

def no.big() -> Bytes():
  ""

def no.gap() -> U32:
  0

def no.uplan(~P: Data, ~U: Data, u: U, bs: Bytes()) -> Plan<P, U>:
  Stop{}

def no.event(n: U32) -> Bytes():
  "\r\n"

def no.shut(sh: Bool, bs: Bytes()) -> Bytes():
  bs

def no.fhead(ct: Bytes(), n: U32) -> Bytes():
  ""

def no.miss(head: Bool) -> Bytes():
  ""

def no.lnote(note: Bytes(), out: Bytes()) -> String:
  ""

def no.lsize(note: Bytes(), hd: Bytes(), n: U32) -> String:
  ""

# The accept loop
# ===============
#
# Written over its own interface, as the connection is: ~L the
# listener, ~C what it accepts, ~N what serving needs, ~lsn one timed
# accept (TCP.accept_poll), ~sig whether a stop was asked (SIGTERM),
# ~hand the hand-off of an accepted connection. A turn ends the loop
# only for a stop request or for a listener that is no longer one; an
# accept that failed for one connection, or for a passing shortage, is
# a turn like any other.

# why the loop ended: it spent its turns, a stop was asked, or the
# listener died with this code
type Why is Data:
  Spent{}
  Asked{}
  Dead{code: U32}

# The errors accept(2) answers for one connection or for the moment
# (tcp_accept_poll.c's passing set, and EAGAIN), by their numbers on
# Linux and on macOS. The effect answers them itself, so none should
# arrive here; if one does, it is one more turn and not the end.
def accept.soft.codes() -> List<&2, U32>:
  [1, 4, 11, 12, 23, 24, 35, 42, 45, 50, 51, 53, 55, 64, 65, 71, 92, 95, 100, 101,
   102, 103, 105, 112, 113]

def accept.soft.in(+code: U32, cs: List<&2, U32>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Con{+c, t}:
      U32.is_eq(code, c) || accept.soft.in(code, t)

def accept.soft(+code: U32) -> Bool:
  accept.soft.in(code, accept.soft.codes())

# after a turn: a stop request ends the loop, anything else goes on
def accept.asked(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~L: Type, lb: L & Bool
) -> M(L & Maybe<&2, Why>):
  (l, stop) = lb
  match stop:
    case True{}:
      pure(L & Maybe<&2, Why>, (l, Some{Asked{}}))
    case False{}:
      pure(L & Maybe<&2, Why>, (l, None{}))

# A connection to serve takes a slot first, so accepting parks while the
# limit is reached and the backlog holds what arrives meanwhile. A stop
# request is looked for on every turn, an arrival or not: asked only
# when nothing arrived, it went unseen for as long as arrivals kept
# coming. The ask is a flag read, not a syscall.
def accept.on(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~L: Type, ~C: Type,
  ~N: Data, ~sig: L -> M(L & Bool), ~hand: @+env: N -> L -> C -> M(L), +env: N, l: L,
  may: Maybe<&1, C>
) -> M(L & Maybe<&2, Why>):
  match may:
    case None{}:
      bind(L & Bool, L & Maybe<&2, Why>, sig(l), lb => accept.asked(~M, ~pure, ~bind, ~L, lb))
    case Some{c}:
      bind(L, L & Maybe<&2, Why>, hand(env, l, c), l2 =>
        bind(L & Bool, L & Maybe<&2, Why>, sig(l2), lb => accept.asked(~M, ~pure, ~bind, ~L,
            lb)))

# a failure ends the loop only when the listener is no longer one
def accept.dead(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~L: Type,
  ~sig: L -> M(L & Bool), l: L, +code: U32, soft: Bool
) -> M(L & Maybe<&2, Why>):
  match soft:
    case True{}:
      bind(L & Bool, L & Maybe<&2, Why>, sig(l), lb => accept.asked(~M, ~pure, ~bind, ~L, lb))
    case False{}:
      pure(L & Maybe<&2, Why>, (l, Some{Dead{code}}))

def accept.fail.at(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~L: Type,
  ~sig: L -> M(L & Bool), l: L, +code: U32
) -> M(L & Maybe<&2, Why>):
  accept.dead(~M, ~pure, ~bind, ~L, ~sig, l, code, accept.soft(code))

def accept.fail(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~L: Type,
  ~sig: L -> M(L & Bool), l: L, e: U32 & String
) -> M(L & Maybe<&2, Why>):
  (code, msg) = e
  accept.fail.at(~M, ~pure, ~bind, ~L, ~sig, l, code)

def accept.got(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~L: Type, ~C: Type,
  ~N: Data, ~sig: L -> M(L & Bool), ~hand: @+env: N -> L -> C -> M(L), +env: N,
  m: L & Result<&1, &1, U32 & String, Maybe<&1, C>>
) -> M(L & Maybe<&2, Why>):
  (l, r) = m
  match r:
    case Done{may}:
      accept.on(~M, ~pure, ~bind, ~L, ~C, ~N, ~sig, ~hand, env, l, may)
    case Fail{e}:
      accept.fail(~M, ~pure, ~bind, ~L, ~sig, l, e)

# how often the accept loop looks up from the listener, in ms: the most
# a stop request waits before it is seen
def accept.tick() -> U32:
  250

def accept.why(w: Maybe<&2, Why>) -> Why:
  match w:
    case None{}:
      Spent{}
    case Some{why}:
      why

# k turns of the loop, or fewer if it ends: one timed accept each, and
# the hand-off of what arrived
def accept.run(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~L: Type, ~C: Type,
  ~N: Data, ~lsn: L -> U32 -> M(L & Result<&1, &1, U32 & String, Maybe<&1, C>>),
  ~sig: L -> M(L & Bool), ~hand: @+env: N -> L -> C -> M(L), k: Nat, +env: N,
  lw: L & Maybe<&2, Why>
) -> M(L & Why):
  match k:
    case 0n:
      (l, w) = lw
      pure(L & Why, (l, accept.why(w)))
    case 1n+j:
      (l, w) = lw
      match w:
        case Some{why}:
          pure(L & Why, (l, why))
        case None{}:
          bind(L & Result<&1, &1, U32 & String, Maybe<&1, C>>, L & Why, lsn(l, accept.tick()), m =>
            bind(L & Maybe<&2, Why>, L & Why, accept.got(~M, ~pure, ~bind, ~L, ~C, ~N, ~sig,
                ~hand, env, m), lw2 =>
              accept.run(~M, ~pure, ~bind, ~L, ~C, ~N, ~lsn, ~sig, ~hand, j, env, lw2)))
