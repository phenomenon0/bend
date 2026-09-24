# bend-mesh: a fork tree whose leaves are machines.
#
#   mesh JOB A N C D URL...     split JOB's range into C chunks over the workers
#   mesh JOB A N 0 D            the same job in this one process (the reference)
#
# JOB is exact (A: the seed, N: how many draws) or lost (A: increments a
# thread, N ignored: every schedule). D is each leaf's own fork depth.
#
# Every summary in demos/monoids is a small value joined associatively, and a
# leaf is a pure function of its range. So the join of the workers' answers is
# the single-process answer bit for bit, whichever machine ran which chunk --
# and three things a distributed system usually has to argue about become
# free:
#
#   retry   a worker that fails (refused, reset, timed out) gives its chunk
#           back to the queue and retires; another worker's answer for that
#           range is the same bytes, so nothing is double-counted or lost.
#   hedge   when the queue is empty, an idle worker takes a chunk that is out
#           but not back (Dean & Barroso, "The Tail at Scale": hedged
#           requests). Whichever copy lands first is kept; a later copy must
#           equal it byte for byte, and the program counts that it does.
#   split   the chunk count C changes nothing but the schedule.
#
# The board (the queue, the answers so far, the counts) is one value in a
# channel of one: a worker loop takes it, picks, and puts it back, so no two
# loops see half a change. Each worker has its own pooled client session.
import Base
import ../../net/http.bend as Http
import ../../net/client.bend as Client
import ./job.bend as J

type Got is Data:
  Got{i: U32, ws: List<&2, U32>, who: U32}

type Board is Data:
  Board{todo: List<&2, U32>, got: List<&2, Got>, hedges: U32, agree: U32, differ: U32, retries: U32}

def NONE() -> U32:
  4294967295

# -- the board --------------------------------------------------------------------------

def has(gs: List<&2, Got>, +i: U32) -> Bool:
  match gs:
    case Nil{}:
      False{}
    case Con{g, t}:
      match g:
        case Got{j, _, _}:
          U32.is_eq(j, i) || has(t, i)

def words.at(gs: List<&2, Got>, +i: U32) -> List<&2, U32>:
  match gs:
    case Nil{}:
      Nil{}
    case Con{g, t}:
      match g:
        case Got{j, ws, _}:
          Bool.pick(List<&2, U32>, U32.is_eq(j, i), ws, words.at(t, i))

def same(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, s} Con{y, t}:
      U32.is_eq(x, y) && same(s, t)
    case _ _:
      False{}

# the first chunk below c that is not back yet, or NONE
def missing(k: Nat, +gs: List<&2, Got>, +i: U32) -> U32:
  match k:
    case 0n:
      NONE()
    case 1n++q:
      Bool.pick(U32, has(gs, i), missing(q, gs, U32.inc(i)), i)

# what a free worker takes: the queue's head, else (a hedge) a chunk out but
# not back, else NONE: everything is in
def pick(+c: U32, b: Board) -> Board & U32:
  match b:
    case Board{todo, +got, +h, a, d, r}:
      match todo:
        case Con{i, rest}:
          (Board{rest, got, h, a, d, r}, i)
        case Nil{}:
          +m = missing(U32.to_nat(c), got, 0)
          (Board{Nil{}, got, U32.add(h, Bool.to_u32(U32.is_ne(m, NONE()))), a, d, r}, m)

def record.fin(+c: U32, +dup: Bool, +b: Board) -> Board & Maybe<&2, Board>:
  match b:
    case Board{_, +got, _, _, _, _}:
      (b, Bool.pick(Maybe<&2, Board>, Bool.not(dup) && U32.is_eq(missing(U32.to_nat(c), got, 0), NONE()),
        Some{b}, None{}))

# an answer for chunk i from worker w: the first is kept, a later one
# compared. If this one completed the board, the board comes back as well.
def record(+c: U32, +i: U32, +ws: List<&2, U32>, +w: U32, b: Board) -> Board & Maybe<&2, Board>:
  match b:
    case Board{todo, +got, h, +a, +d, r}:
      +dup = has(got, i)
      +eq = same(words.at(got, i), ws)
      record.fin(c, dup, Board{todo, Bool.pick(List<&2, Got>, dup, got, Got{i, ws, w} <> got), h,
        U32.add(a, Bool.to_u32(dup && eq)), U32.add(d, Bool.to_u32(dup && Bool.not(eq))), r})

# a chunk a worker could not finish goes back to the queue's front
def requeue(+i: U32, b: Board) -> Board & Unit:
  match b:
    case Board{todo, got, h, a, d, r}:
      (Board{i <> todo, got, h, a, d, U32.inc(r)}, Unit{})

def locked.put(-A: Type, +db: Chan(Board), r: Board & A) -> IO(A):
  (st, x) = r
  IO.bind(Bool, A, Chan.send(Board, db, st), ok => IO.pure(A, x))

def locked.at(-A: Type, +db: Chan(Board), f: Board -> Board & A, d: A, m: Maybe<&1, Board>) -> IO(A):
  match m:
    case Some{st}:
      locked.put(A, db, f(st))
    case None{}:
      IO.pure(A, d)

# take the board, change it by f, put it back; f's answer
def locked(-A: Type, +db: Chan(Board), f: Board -> Board & A, d: A) -> IO(A):
  IO.bind(Maybe<&1, Board>, A, Chan.recv(Board, db), m => locked.at(A, db, f, d, m))

type Plan is Data:
  Plan{kind: U32, a: U32, total: U32, chunks: U32, d: U32, workers: U32}

def Plan.workers(+p: Plan) -> U32:
  match p:
    case Plan{_, _, _, _, _, w}:
      w

def Plan.chunks(+p: Plan) -> U32:
  match p:
    case Plan{_, _, _, c, _, _}:
      c

# the answers joined in chunk order, by the job's own monoid
def fold(k: Nat, +kind: U32, +gs: List<&2, Got>, +i: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      acc
    case 1n++q:
      fold(q, kind, gs, U32.inc(i), J.join(kind, acc, words.at(gs, i)))

def per(+gs: List<&2, Got>, +w: U32) -> U32:
  match gs:
    case Nil{}:
      0
    case Con{g, t}:
      match g:
        case Got{_, _, who}:
          U32.add(Bool.to_u32(U32.is_eq(who, w)), per(t, w))

def shares(k: Nat, +gs: List<&2, Got>, +w: U32) -> String:
  match k:
    case 0n:
      ""
    case 1n++q:
      " w" ++ U32.show(w) ++ "=" ++ U32.show(per(gs, w)) ++ shares(q, gs, U32.inc(w))

def report(+p: Plan, +nw: U32, b: Board) -> IO(Unit):
  match p b:
    case Plan{+k, +a, _, +c, _, _} Board{todo, +got, h, ag, df, r}:
      +gap = missing(U32.to_nat(c), got, 0)
      do IO<Unit>:
        IO.print(Bool.pick(String, U32.is_eq(gap, NONE()),
          J.render(k, a, fold(U32.to_nat(c), k, got, 0, J.zero(k))),
          "INCOMPLETE: chunk " ++ U32.show(gap) ++ " never came back"))
        # the answer is in: end now, whatever is still out (a straggler's
        # copy is no longer needed, and its answer could only be the same)
        IO.die(Unit, Bool.to_u32(U32.is_ne(gap, NONE())), "mesh: " ++ U32.show(c)
          ++ " chunks over " ++ U32.show(nw) ++ " workers;" ++ shares(U32.to_nat(nw), got, 0)
          ++ "; hedged " ++ U32.show(h) ++ ", duplicates equal " ++ U32.show(ag) ++ ", differ "
          ++ U32.show(df) ++ ", retried " ++ U32.show(r))

def report.maybe(+p: Plan, m: Maybe<&2, Board>) -> IO(Unit):
  match m:
    case Some{b}:
      report(p, Plan.workers(p), b)
    case None{}:
      IO.pure(Unit, Unit{})

# -- a worker's loop ----------------------------------------------------------------------

def chunk.at(k: U32, a: U32, +t: U32, +l: U32, d: U32, +lo: U32) -> J.Job:
  J.Job{k, a, lo, U32.min(l, U32.sub(t, U32.min(lo, t))), d}

# chunk i of the plan: ceil(total / chunks) items from i times that
def chunk.job(+p: Plan, +i: U32) -> J.Job:
  match p:
    case Plan{k, a, +t, +c, d, _}:
      +l = U32.div(U32.add(t, U32.sub(c, 1)), c)
      chunk.at(k, a, t, l, d, U32.mul(i, l))

def ok(+r: Client.Res()) -> Bool:
  match r:
    case Done{resp}:
      U32.is_eq(Http.status(resp), 200)
    case Fail{e}:
      False{}

def words.of(r: Client.Res()) -> List<&2, U32>:
  match r:
    case Done{resp}:
      J.words(Http.resp.body(resp))
    case Fail{e}:
      Nil{}

def choose(-A: Type, b: Bool, yes: Unit -> A, no: Unit -> A) -> A:
  match b:
    case True{}:
      yes(Unit{})
    case False{}:
      no(Unit{})

def post(+ss: Client.Session, +url: Bytes(), +p: Plan, +i: U32) -> IO(Client.Res()):
  Client.fetch(ss, Client.Req{"POST", Bytes.append(url, "/leaf"), [Http.Header{"content-type", "text/plain"}],
    J.body(chunk.job(p, i))})

# take a chunk, post it, record the answer, again -- until nothing is left, or
# this worker fails once (its chunk goes back, and it retires)
def work(fuel: Nat, +p: Plan, +db: Chan(Board), +w: U32, +url: Bytes(), +ss: Client.Session) -> IO(Unit):
  match fuel:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n++q:
      IO.bind(U32, Unit, locked(U32, db, b => pick(Plan.chunks(p), b), NONE()), +i =>
        choose(IO(Unit), U32.is_eq(i, NONE()), u => IO.pure(Unit, Unit{}), u =>
          IO.bind(Client.Res(), Unit, post(ss, url, p, i), +r =>
            choose(IO(Unit), ok(r),
              u => IO.bind(Maybe<&2, Board>, Unit,
                locked(Maybe<&2, Board>, db, b => record(Plan.chunks(p), i, words.of(r), w, b), None{}),
                +m => choose(IO(Unit), Maybe.is_some(&2, Board, m), v => report.maybe(p, m),
                  v => work(q, p, db, w, url, ss))),
              u => locked(Unit, db, b => requeue(i, b), Unit{})))))

# -- the coordinator --------------------------------------------------------------------

def spawn.all(+p: Plan, +db: Chan(Board), +done: Chan(Unit), urls: List<&2, Bytes()>, +w: U32) -> IO(Unit):
  match urls:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{+url, t}:
      do IO<Unit>:
        IO.spawn(Unit, do IO<Unit>:
          +ss : Client.Session <- Client.session(Client.with.timeout(Client.opts(), 600000))
          work(65536n, p, db, w, url, ss)
          Client.close(ss)
          ok : Bool <- Chan.send(Unit, done, Unit{})
          return Unit{})
        spawn.all(p, db, done, t, U32.inc(w))

def wait(k: Nat, +done: Chan(Unit)) -> IO(Unit):
  match k:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n++q:
      IO.bind(Maybe<&1, Unit>, Unit, Chan.recv(Unit, done), m => wait(q, done))

def todo(k: Nat, +i: U32) -> List<&2, U32>:
  match k:
    case 0n:
      Nil{}
    case 1n++q:
      i <> todo(q, U32.inc(i))

def len(xs: List<&2, Bytes()>) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{x, t}:
      U32.inc(len(t))

def final.at(+p: Plan, +nw: U32, m: Maybe<&1, Board>) -> IO(Unit):
  match m:
    case Some{b}:
      report(p, nw, b)
    case None{}:
      IO.die(Unit, 1, "the board was lost")

def final(+db: Chan(Board), +p: Plan, +nw: U32) -> IO(Unit):
  IO.bind(Maybe<&1, Board>, Unit, Chan.recv(Board, db), m => final.at(p, nw, m))

def distributed(+p: Plan, +urls: List<&2, Bytes()>) -> IO(Unit):
  +nw = len(urls)
  do IO<Unit>:
    +db : Chan(Board) <- Chan.new(Board, 1)
    +done : Chan(Unit) <- Chan.new(Unit, 64)
    ok : Bool <- Chan.send(Board, db, Board{todo(U32.to_nat(Plan.chunks(p)), 0), Nil{}, 0, 0, 0, 0})
    spawn.all(p, db, done, urls, 0)
    wait(U32.to_nat(nw), done)
    final(db, p, nw)

def local(+p: Plan) -> IO(Unit):
  match p:
    case Plan{+k, +a, +t, _, +d, _}:
      IO.print(J.render(k, a, J.run(J.Job{k, a, 0, t, d})))

def arg(k: Nat, xs: List<&2, String>) -> String:
  match k:
    case 0n:
      match xs:
        case Nil{}:
          ""
        case Con{x, t}:
          x
    case 1n++q:
      match xs:
        case Nil{}:
          ""
        case Con{x, t}:
          arg(q, t)

def num(+s: String) -> U32:
  Maybe.default(&2, U32, U32.read(s), 0)

def rest(k: Nat, xs: List<&2, String>) -> List<&2, Bytes()>:
  match k:
    case 0n:
      xs
    case 1n++q:
      match xs:
        case Nil{}:
          Nil{}
        case Con{x, t}:
          rest(q, t)

def plan(+xs: List<&2, String>) -> Plan:
  +k = J.kind.of(arg(0n, xs))
  +a = num(arg(1n, xs))
  Plan{k, a, J.total(k, a, num(arg(2n, xs))), num(arg(3n, xs)), num(arg(4n, xs)), len(rest(5n, xs))}

def go(+xs: List<&2, String>) -> IO(Unit):
  +p = plan(xs)
  choose(IO(Unit), U32.is_zero(Plan.chunks(p)), u => local(p), u => distributed(p, rest(5n, xs)))

def strs(xs: List<String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{x, strs(t)}

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    go(strs(xs))
