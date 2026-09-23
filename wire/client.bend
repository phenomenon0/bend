# bend-wire: the client's connection loop.
#
# One exchange on a connection: send a request, then read the response
# through the response reader (wire/http1/resp.bend, held to RFC 9112 by
# resp_sim) until it is framed, refused, or out of time, and say whether
# the connection may carry another request. Like wire/loop.bend it is
# written once over the effects as template parameters:
#
#   ~M, ~pure, ~bind   the monad
#   ~S                 the socket
#   ~rx                a timed read: TCP.poll_buf(s, max, ms), its
#                      deadline in ms as a Nat
#   ~tx                a timed write: TCP.send_buf_poll(s, bytes, ms)
#   ~clk               the clock, in ms, beside the socket
#
# and instantiated twice: with IO and the real effects (fetch), and with
# the identity monad and world.bend's scripted peer (sim), where the
# laws below are proven.
#
# The budgets (Budget): the head -- the bytes read while a head is in
# progress, interim responses' heads included -- is capped; the body is
# capped by the reader's Ask; the whole exchange has one deadline, and
# every read and send its own step deadline, each read's cut to the time
# the exchange has left. A read takes at most chunk() bytes. What comes
# back is the framed response, or why there is none (Why).
#
# The connection may carry another request (Got's reuse) only when the
# final response did not close it -- no Connection: close, not HTTP/1.0
# without keep-alive, not a 101, not a body that ran to the close -- and
# nothing came after it: a byte past the response is a response nobody
# asked for, and the connection it came on is not one to trust.
import Base
import ./loop.bend as L
import ./effects.bend as Fx
import ./world.bend as W
import ./http1/resp.bend as R

# What an exchange spends
# =======================

# head: the most bytes read while a head is in progress; total: the
# exchange's deadline; step: each read's and send's own
type Budget is Data:
  Budget{head: U32, total: U32, step: U32}

def budget.head(b: Budget) -> U32:
  match b:
    case Budget{head, total, step}:
      head

def budget.total(b: Budget) -> U32:
  match b:
    case Budget{head, total, step}:
      total

def budget.step(b: Budget) -> U32:
  match b:
    case Budget{head, total, step}:
      step

def chunk() -> U32:
  65536

# Why there is no response: the request did not go out; a read failed;
# the deadline passed (or a read waited its step out); the head passed
# its cap; the response was refused (malformed, or framed two ways); the
# peer closed before the response was whole; the reads ran out.
type Why is Data:
  CSend{code: U32}
  CRecv{code: U32}
  CTime{}
  CHead{}
  CFrame{}
  CEof{}
  CFuel{}

# The response: the interim statuses, the final response, what came
# after it on the connection, and whether the connection may carry
# another request.
type Got is Data:
  Got{interim: List<&2, U32>, resp: R.Resp, extra: Bytes(), reuse: Bool}

def Res() -> Data:
  Result<&2, &2, Why, Got>

def Out(S: Type) -> Type:
  S & Result<&2, &2, Why, Got>

def resp.close(r: R.Resp) -> Bool:
  match r:
    case R.Resp{code, v10, close, body}:
      close

# a final response, and what came after it
def final(i: List<&2, U32>, +r: R.Resp, +rest: Bytes()) -> Result<&2, &2, Why, Got>:
  Done{Got{i, r, rest, Bool.not(resp.close(r)) && String.is_empty(rest)}}

# the peer closed: whole only if the body was one that runs to the close
def at.eof(lk: R.Look) -> Result<&2, &2, Why, Got>:
  match lk:
    case R.Look{i, end}:
      match end:
        case R.Closing{r}:
          Done{Got{i, r, "", False{}}}
        case _:
          Fail{CEof{}}

# The loop
# ========

# how long a read may wait: its step, cut to the time left
def rd.ms(+b: Budget, left: Nat) -> Nat:
  Nat.min(U32.to_nat(budget.step(b)), left)

# the reads a response may take: every one brings at least a byte, and
# the bytes are bounded by the head's cap and the body's (a chunked
# body's trailer is not, and the deadline is its bound)
def rd.fuel(+e: R.Ask, +b: Budget) -> Nat:
  Nat.add(U32.to_nat(R.ask.cap(e)), Nat.add(U32.to_nat(budget.head(b)), 1024n))

def rd.next(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A), ~S: Type, s: S, lk: R.Look, +p2: R.P,
  +hd2: Nat, again: S -> R.P -> Nat -> M(Out(S))
) -> M(Out(S)):
  match lk:
    case R.Look{i, end}:
      match end:
        case R.Refused{}:
          pure(Out(S), (s, Fail{CFrame{}}))
        case R.Final{+r, rest}:
          pure(Out(S), (s, final(i, r, rest)))
        case R.Closing{r}:
          again(s, p2, hd2)
        case R.Open{}:
          again(s, p2, hd2)

def rd.more(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A), ~S: Type, +over: Bool, s: S, +p2: R.P,
  +hd2: Nat, again: S -> R.P -> Nat -> M(Out(S))
) -> M(Out(S)):
  match over:
    case True{}:
      pure(Out(S), (s, Fail{CHead{}}))
    case False{}:
      rd.next(~M, ~pure, ~S, s, R.look(p2), p2, hd2, again)

# a read's bytes: the empty read is the peer's close; any other goes
# through the reader, and counts against the head's cap when it begins
# while a head is in progress. (The read is passed on whole, never taken
# apart and put back together: a buffer is cheaper whole, and the C
# runtime mishandles a String rebuilt as SCon{h, t} over a shared view.)
def rd.bytes(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A), ~S: Type, +e: R.Ask, +b: Budget, s: S,
  +p: R.P, +hd: Nat, empty: Bool, +bs: Bytes(), again: S -> R.P -> Nat -> M(Out(S))
) -> M(Out(S)):
  match empty:
    case True{}:
      pure(Out(S), (s, at.eof(R.look(p))))
    case False{}:
      +hd2 = Bool.pick(Nat, R.mid(p), Nat.add(hd, Bytes.len(bs)), hd)
      rd.more(~M, ~pure, ~S, Nat.is_lt(U32.to_nat(budget.head(b)), hd2), s, R.feed_buf(e, bs, p), hd2,
        again)

def rd.got(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A), ~S: Type, +e: R.Ask, +b: Budget, +p: R.P,
  +hd: Nat, g: L.Got(S), again: S -> R.P -> Nat -> M(Out(S))
) -> M(Out(S)):
  (s, r) = g
  match r:
    case Fail{er}:
      (code, msg) = er
      pure(Out(S), (s, Fail{CRecv{code}}))
    case Done{may}:
      match may:
        case None{}:
          pure(Out(S), (s, Fail{CTime{}}))
        case Some{+bs}:
          rd.bytes(~M, ~pure, ~S, e, b, s, p, hd, String.is_empty(bs), bs, again)

# a turn: at or past the deadline, the exchange ends without a read;
# before it, one read, waiting at most rd.ms
def rd.time(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~rx: S -> U32 -> Nat -> M(L.Got(S)), +e: R.Ask, +b: Budget, live: Bool, left: Nat, +p: R.P,
  +hd: Nat, s: S, again: S -> R.P -> Nat -> M(Out(S))
) -> M(Out(S)):
  match live:
    case False{}:
      pure(Out(S), (s, Fail{CTime{}}))
    case True{}:
      bind(L.Got(S), Out(S), rx(s, chunk(), rd.ms(b, left)), g =>
        rd.got(~M, ~pure, ~S, e, b, p, hd, g, again))

def rd.at(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~rx: S -> U32 -> Nat -> M(L.Got(S)), +e: R.Ask, +b: Budget, +until: Nat, +p: R.P, +hd: Nat,
  sn: S & Nat, again: S -> R.P -> Nat -> M(Out(S))
) -> M(Out(S)):
  (s, +now) = sn
  rd.time(~M, ~pure, ~bind, ~S, ~rx, e, b, Nat.is_lt(now, until), Nat.sub(until, now), p, hd, s,
    again)

# k bounds the reads; until is the exchange's deadline, on the clock
def rd.go(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~rx: S -> U32 -> Nat -> M(L.Got(S)), ~clk: S -> M(S & Nat), +e: R.Ask, +b: Budget,
  +until: Nat, k: Nat, +p: R.P, +hd: Nat, s: S
) -> M(Out(S)):
  match k:
    case 0n:
      pure(Out(S), (s, Fail{CFuel{}}))
    case 1n+j:
      bind(S & Nat, Out(S), clk(s), sn =>
        rd.at(~M, ~pure, ~bind, ~S, ~rx, e, b, until, p, hd, sn,
          s2 => p2 => hd2 => rd.go(~M, ~pure, ~bind, ~S, ~rx, ~clk, e, b, until, j, p2, hd2, s2)))

def ex.sent(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~rx: S -> U32 -> Nat -> M(L.Got(S)), ~clk: S -> M(S & Nat), +e: R.Ask, +b: Budget,
  +until: Nat, m: L.Put(S)
) -> M(Out(S)):
  (s, r) = m
  match r:
    case Fail{er}:
      (code, msg) = er
      pure(Out(S), (s, Fail{CSend{code}}))
    case Done{u}:
      rd.go(~M, ~pure, ~bind, ~S, ~rx, ~clk, e, b, until, rd.fuel(e, b), R.p.new(), 0n, s)

def ex.start(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~rx: S -> U32 -> Nat -> M(L.Got(S)), ~tx: S -> Bytes() -> U32 -> M(L.Put(S)),
  ~clk: S -> M(S & Nat), +e: R.Ask, +b: Budget, req: Bytes(), sn: S & Nat
) -> M(Out(S)):
  (s, t0) = sn
  bind(L.Put(S), Out(S), tx(s, req, budget.step(b)), m =>
    ex.sent(~M, ~pure, ~bind, ~S, ~rx, ~clk, e, b, Nat.add(t0, U32.to_nat(budget.total(b))), m))

# One exchange: the request out, the response in.
def exchange(
  ~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Type,
  ~rx: S -> U32 -> Nat -> M(L.Got(S)), ~tx: S -> Bytes() -> U32 -> M(L.Put(S)),
  ~clk: S -> M(S & Nat), +e: R.Ask, +b: Budget, req: Bytes(), s: S
) -> M(Out(S)):
  bind(S & Nat, Out(S), clk(s), sn => ex.start(~M, ~pure, ~bind, ~S, ~rx, ~tx, ~clk, e, b, req, sn))

# The real world
# ==============

def net.rx(s: Socket, max: U32, ms: Nat) -> IO(L.Got(Socket)):
  TCP.poll_buf(s, max, U32.from_nat(ms))

# One exchange over a socket, plain or TLS.
def fetch(+e: R.Ask, +b: Budget, req: Bytes(), s: Socket) -> IO(Out(Socket)):
  exchange(~(A => IO(A)), ~IO.pure, ~IO.bind, ~Socket, ~net.rx, ~TCP.send_buf_poll, ~Fx.net.now,
    e, b, req, s)

# A request head, for a client that has nothing else to say: the method
# and target, Host, and the fields given (each a whole line, CRLF and
# all); the body, if any, after it.
def request(meth: Bytes(), target: Bytes(), host: Bytes(), fields: Bytes(), body: Bytes()) -> Bytes():
  Bytes.concat([meth, " ", target, " HTTP/1.1\r\nHost: ", host, "\r\n", fields, "\r\n", body])

def why.show(w: Why) -> String:
  match w:
    case CSend{code}:
      "the request could not be sent (" ++ U32.show(code) ++ ")"
    case CRecv{code}:
      "a read failed (" ++ U32.show(code) ++ ")"
    case CTime{}:
      "the deadline passed"
    case CHead{}:
      "the head passed its cap"
    case CFrame{}:
      "the response was refused: malformed, or framed two ways"
    case CEof{}:
      "the peer closed before the response was whole"
    case CFuel{}:
      "the reads ran out"

# The model
# =========
#
# The same loop with the identity monad and world.bend's scripted peer:
# each read is the next thing the script says, and the clock moves by
# what the read waited. world.bend's read takes its deadline as a U32;
# the client's is a Nat, and cw.rx is w.rx.go with a Nat deadline, case
# for case, judged by the same contract (rx.ok, with U32.to_nat applied).

def cw.rx.give(
  t: List<&2, W.Rd>, +wait: Nat, bs: Bytes(), +ms: Nat, wr: List<&2, W.Wr>, eager: Bool, +now: Nat,
  fs: List<&2, W.Fil>, out: Bytes(), soon: Bool
) -> L.Got(W.World):
  match soon:
    case True{}:
      (W.World{t, wr, eager, Nat.add(now, wait), fs, out}, Done{Some{bs}})
    case False{}:
      (W.World{Con{W.Give{Nat.sub(wait, ms), bs}, t}, wr, eager, Nat.add(now, ms), fs, out}, Done{None{}})

def cw.rx.go(s: W.World, +ms: Nat) -> L.Got(W.World):
  match s:
    case W.World{rd, wr, eager, now, fs, out}:
      match rd:
        case Nil{}:
          (W.World{Nil{}, wr, eager, Nat.add(now, ms), fs, out}, Done{None{}})
        case Con{e, t}:
          match e:
            case W.Hush{}:
              (W.World{t, wr, eager, Nat.add(now, ms), fs, out}, Done{None{}})
            case W.Cut{code}:
              (W.World{t, wr, eager, now, fs, out}, Fail{(code, "reset")})
            case W.Give{+wait, bs}:
              cw.rx.give(t, wait, bs, ms, wr, eager, now, fs, out, Nat.is_lt(wait, ms))

def cw.rx(s: W.World, max: U32, ms: Nat) -> L.Got(W.World):
  cw.rx.go(s, ms)

def sim.go(+e: R.Ask, +b: Budget, +until: Nat, k: Nat, +p: R.P, +hd: Nat, s: W.World) -> Out(W.World):
  rd.go(~W.Id, ~W.Id.pure, ~W.Id.bind, ~W.World, ~cw.rx, ~W.w.clk, e, b, until, k, p, hd, s)

def sim.exchange(+e: R.Ask, +b: Budget, req: Bytes(), s: W.World) -> Out(W.World):
  exchange(~W.Id, ~W.Id.pure, ~W.Id.bind, ~W.World, ~cw.rx, ~W.w.tx, ~W.w.clk, e, b, req, s)

# The laws
# ========

# a connection is reused only when its response did not close it and
# nothing came after the response
def ok.reuse(r: Result<&2, &2, Why, Got>) -> Bool:
  match r:
    case Fail{w}:
      True{}
    case Done{g}:
      match g:
        case Got{i, x, extra, reuse}:
          Bool.not(reuse) || (Bool.not(resp.close(x)) && String.is_empty(extra))

def ok.of(m: Out(W.World)) -> Bool:
  (s, r) = m
  ok.reuse(r)

def ok.final.at(-i: List<&2, U32>, -r: R.Resp, c: Bool, e: Bool) ->
  {Bool.not(Bool.not(c) && e) || (Bool.not(c) && e) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      match e:
        case True{}:
          {==}
        case False{}:
          {==}

def ok.final(-i: List<&2, U32>, +r: R.Resp, +rest: Bytes()) -> {ok.reuse(final(i, r, rest)) == True{} : Bool}:
  match r:
    case R.Resp{code, v10, close, body}:
      ok.final.at(i, R.Resp{code, v10, close, body}, close, String.is_empty(rest))

def ok.eof(lk: R.Look) -> {ok.reuse(at.eof(lk)) == True{} : Bool}:
  match lk:
    case R.Look{i, end}:
      match end:
        case R.Open{}:
          {==}
        case R.Refused{}:
          {==}
        case R.Final{r, rest}:
          {==}
        case R.Closing{r}:
          {==}

# what the rest of the loop may be trusted with: any turn it takes from
# here keeps the promise
def AG(-again: W.World -> R.P -> Nat -> Out(W.World)) -> Type:
  @+s2: W.World -> @+p2: R.P -> @+hd2: Nat -> {ok.of(again(s2, p2, hd2)) == True{} : Bool}

def ok.next(s: W.World, lk: R.Look, +p2: R.P, +hd2: Nat, -again: W.World -> R.P -> Nat -> Out(W.World),
  ag: AG(again)) ->
  {ok.of(rd.next(~W.Id, ~W.Id.pure, ~W.World, s, lk, p2, hd2, again)) == True{} : Bool}:
  match lk:
    case R.Look{i, end}:
      match end:
        case R.Refused{}:
          {==}
        case R.Final{+r, rest}:
          ok.final(i, r, rest)
        case R.Closing{r}:
          ag(s, p2, hd2)
        case R.Open{}:
          ag(s, p2, hd2)

def ok.more(over: Bool, s: W.World, +p2: R.P, +hd2: Nat, -again: W.World -> R.P -> Nat -> Out(W.World),
  ag: AG(again)) ->
  {ok.of(rd.more(~W.Id, ~W.Id.pure, ~W.World, over, s, p2, hd2, again)) == True{} : Bool}:
  match over:
    case True{}:
      {==}
    case False{}:
      ok.next(s, R.look(p2), p2, hd2, again, ag)

def ok.bytes(+e: R.Ask, +b: Budget, s: W.World, +p: R.P, +hd: Nat, empty: Bool, +bs: Bytes(),
  -again: W.World -> R.P -> Nat -> Out(W.World), ag: AG(again)) ->
  {ok.of(rd.bytes(~W.Id, ~W.Id.pure, ~W.World, e, b, s, p, hd, empty, bs, again)) == True{} : Bool}:
  match empty:
    case True{}:
      ok.eof(R.look(p))
    case False{}:
      ok.more(Nat.is_lt(U32.to_nat(budget.head(b)), Bool.pick(Nat, R.mid(p), Nat.add(hd, Bytes.len(bs)), hd)), s,
        R.feed_buf(e, bs, p), Bool.pick(Nat, R.mid(p), Nat.add(hd, Bytes.len(bs)), hd), again, ag)

def ok.got(+e: R.Ask, +b: Budget, +p: R.P, +hd: Nat, g: L.Got(W.World),
  -again: W.World -> R.P -> Nat -> Out(W.World), ag: AG(again)) ->
  {ok.of(rd.got(~W.Id, ~W.Id.pure, ~W.World, e, b, p, hd, g, again)) == True{} : Bool}:
  match g:
    case (s, r):
      match r:
        case Fail{er}:
          match er:
            case (code, msg):
              {==}
        case Done{may}:
          match may:
            case None{}:
              {==}
            case Some{+bs}:
              ok.bytes(e, b, s, p, hd, String.is_empty(bs), bs, again, ag)

def ok.time(+e: R.Ask, +b: Budget, live: Bool, +left: Nat, +p: R.P, +hd: Nat, s: W.World,
  -again: W.World -> R.P -> Nat -> Out(W.World), ag: AG(again)) ->
  {ok.of(rd.time(~W.Id, ~W.Id.pure, ~W.Id.bind, ~W.World, ~cw.rx, e, b, live, left, p, hd, s, again)) == True{} :
    Bool}:
  match live:
    case False{}:
      {==}
    case True{}:
      ok.got(e, b, p, hd, cw.rx(s, chunk(), rd.ms(b, left)), again, ag)

def ok.at(+e: R.Ask, +b: Budget, +until: Nat, +j: Nat, +p: R.P, +hd: Nat, sn: W.World & Nat,
  ih: @+p: R.P -> @+hd: Nat -> @+s: W.World -> {ok.of(sim.go(e, b, until, j, p, hd, s)) == True{} : Bool}) ->
  {ok.of(rd.at(~W.Id, ~W.Id.pure, ~W.Id.bind, ~W.World, ~cw.rx, e, b, until, p, hd, sn,
    s2 => p2 => hd2 => sim.go(e, b, until, j, p2, hd2, s2))) == True{} : Bool}:
  match sn:
    case (s, +now):
      ok.time(e, b, Nat.is_lt(now, until), Nat.sub(until, now), p, hd, s,
        s2 => p2 => hd2 => sim.go(e, b, until, j, p2, hd2, s2), s2 => p2 => hd2 => ih(p2, hd2, s2))

def ok.go.step(+e: R.Ask, +b: Budget, +until: Nat, +j: Nat,
  ih: @+p: R.P -> @+hd: Nat -> @+s: W.World -> {ok.of(sim.go(e, b, until, j, p, hd, s)) == True{} : Bool}) ->
  @+p: R.P -> @+hd: Nat -> @+s: W.World -> {ok.of(sim.go(e, b, until, 1n+j, p, hd, s)) == True{} : Bool}:
  p => hd => s => ok.at(e, b, until, j, p, hd, W.w.clk(s), ih)

def ok.go(+e: R.Ask, +b: Budget, +until: Nat, +k: Nat) -> @+p: R.P -> @+hd: Nat -> @+s: W.World ->
  {ok.of(sim.go(e, b, until, k, p, hd, s)) == True{} : Bool}:
  match k:
    case 0n:
      p => hd => s => {==}
    case 1n+j:
      ok.go.step(e, b, until, j, ok.go(e, b, until, j))


def ok.sent(+e: R.Ask, +b: Budget, +until: Nat, m: L.Put(W.World)) ->
  {ok.of(ex.sent(~W.Id, ~W.Id.pure, ~W.Id.bind, ~W.World, ~cw.rx, ~W.w.clk, e, b, until, m)) == True{} : Bool}:
  match m:
    case (s, r):
      match r:
        case Fail{er}:
          match er:
            case (code, msg):
              {==}
        case Done{u}:
          ok.go(e, b, until, rd.fuel(e, b))(R.p.new(), 0n, s)

def ok.start(+e: R.Ask, +b: Budget, req: Bytes(), sn: W.World & Nat) ->
  {ok.of(ex.start(~W.Id, ~W.Id.pure, ~W.Id.bind, ~W.World, ~cw.rx, ~W.w.tx, ~W.w.clk, e, b, req, sn)) == True{} :
    Bool}:
  match sn:
    case (s, t0):
      ok.sent(e, b, Nat.add(t0, U32.to_nat(budget.total(b))), W.w.tx(s, req, budget.step(b)))

# LAW: a connection is reused only when its response did not close it.
# For every peer the script can describe -- whatever it sends, however
# it cuts it, whenever it stops, resets or goes silent -- an exchange
# that says the connection may carry another request (reuse) got a
# final response that did not close it -- no Connection: close, not
# HTTP/1.0 without keep-alive, not a 101, and not a body that ran to
# the close (R.final marks each of those close) -- and nothing came
# after it: a connection with a byte unread is never handed on.
law reuse_clean:
  for +e: R.Ask
  for +b: Budget
  for req: Bytes()
  for s: W.World
  {ok.of(sim.exchange(e, b, req, s)) == True{} : Bool}

def reuse_clean(e, b, req, s):
  ok.start(e, b, req, W.w.clk(s))

# the same for the read loop alone, from any state, any fuel
law reuse_clean.go:
  for +e: R.Ask
  for +b: Budget
  for +until: Nat
  for k: Nat
  for +p: R.P
  for +hd: Nat
  for +s: W.World
  {ok.of(sim.go(e, b, until, k, p, hd, s)) == True{} : Bool}

def reuse_clean.go(e, b, until, k, p, hd, s):
  ok.go(e, b, until, k)(p, hd, s)

# LAW: the deadline, a turn at a time. A turn taken at or past the
# exchange's deadline reads nothing: it ends the exchange with CTime and
# leaves the peer as it was.
law expires:
  for +e: R.Ask
  for +b: Budget
  for +until: Nat
  for +p: R.P
  for +hd: Nat
  for s: W.World
  for +now: Nat
  for again: W.World -> R.P -> Nat -> Out(W.World)
  for late: {Nat.is_lt(now, until) == False{} : Bool}
  {rd.at(~W.Id, ~W.Id.pure, ~W.Id.bind, ~W.World, ~cw.rx, e, b, until, p, hd, (s, now), again) ==
    (s, Fail{CTime{}}) : Out(W.World)}

def expires(e, b, until, p, hd, s, now, again, late):
  %Equal.sym(Bool, Nat.is_lt(now, until), False{}, late) :
    {rd.time(~W.Id, ~W.Id.pure, ~W.Id.bind, ~W.World, ~cw.rx, e, b, _, Nat.sub(until, now), p, hd, s, again) ==
      (s, Fail{CTime{}}) : Out(W.World)}
  {==}

# LAW: the head's budget. A read that begins while a head is in progress
# and takes the bytes read in heads past the cap ends the exchange with
# CHead, whatever the bytes were: a peer that never ends its head is
# read for head.cap bytes and one read more, and no further.
law head_capped:
  for +e: R.Ask
  for +b: Budget
  for s: W.World
  for +p: R.P
  for +hd: Nat
  for +bs: Bytes()
  for again: W.World -> R.P -> Nat -> Out(W.World)
  for inhead: {R.mid(p) == True{} : Bool}
  for over: {Nat.is_lt(U32.to_nat(budget.head(b)), Nat.add(hd, Bytes.len(bs))) == True{} : Bool}
  {rd.bytes(~W.Id, ~W.Id.pure, ~W.World, e, b, s, p, hd, False{}, bs, again) == (s, Fail{CHead{}}) : Out(W.World)}

def head_capped(e, b, s, p, hd, bs, again, inhead, over):
  %Equal.sym(Bool, R.mid(p), True{}, inhead) :
    {rd.more(~W.Id, ~W.Id.pure, ~W.World,
      Nat.is_lt(U32.to_nat(budget.head(b)), Bool.pick(Nat, _, Nat.add(hd, Bytes.len(bs)), hd)), s,
      R.feed_buf(e, bs, p), Bool.pick(Nat, _, Nat.add(hd, Bytes.len(bs)), hd), again) ==
      (s, Fail{CHead{}}) : Out(W.World)}
  %Equal.sym(Bool, Nat.is_lt(U32.to_nat(budget.head(b)), Nat.add(hd, Bytes.len(bs))), True{}, over) :
    {rd.more(~W.Id, ~W.Id.pure, ~W.World, _, s, R.feed_buf(e, bs, p), Nat.add(hd, Bytes.len(bs)), again) ==
      (s, Fail{CHead{}}) : Out(W.World)}
  {==}

# Nat, as the deadline needs it
def le.refl(a: Nat) -> {Nat.is_le(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      le.refl(p)

def le.zero(a: Nat) -> {Nat.is_le(0n, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def le.add(a: Nat, b: Nat) -> {Nat.is_le(a, Nat.add(a, b)) == True{} : Bool}:
  match a:
    case 0n:
      le.zero(b)
    case 1n+p:
      le.add(p, b)

def le.mono(a: Nat, -b: Nat, -c: Nat, h: {Nat.is_le(b, c) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(a, b), Nat.add(a, c)) == True{} : Bool}:
  match a:
    case 0n:
      h
    case 1n+p:
      le.mono(p, b, c, h)

def le.trans(a: Nat, b: Nat, c: Nat, h1: {Nat.is_le(a, b) == True{} : Bool}, h2: {Nat.is_le(b, c) == True{} : Bool}) ->
  {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      le.zero(c)
    case 1n+x 0n _:
      W.no({Nat.is_le(1n+x, c) == True{} : Bool}, h1)
    case 1n+x 1n+y 0n:
      W.no({Nat.is_le(1n+x, 0n) == True{} : Bool}, h2)
    case 1n+x 1n+y 1n+z:
      le.trans(x, y, z, h1, h2)

def lt.le(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n _:
      le.zero(b)
    case 1n+x 0n:
      W.no({Nat.is_le(1n+x, 0n) == True{} : Bool}, h)
    case 1n+x 1n+y:
      lt.le(x, y, h)

def min.le(a: Nat, b: Nat) -> {Nat.is_le(Nat.min(a, b), b) == True{} : Bool}:
  match a b:
    case 0n _:
      le.zero(b)
    case 1n+x 0n:
      {==}
    case 1n+x 1n+y:
      min.le(x, y)

def add.sub(a: Nat, u: Nat, h: {Nat.is_lt(a, u) == True{} : Bool}) -> {Nat.add(a, Nat.sub(u, a)) == u : Nat}:
  match a u:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      {==}
    case 1n+x 0n:
      W.no({Nat.add(1n+x, Nat.sub(0n, 1n+x)) == 0n : Nat}, h)
    case 1n+x 1n+y:
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(x, Nat.sub(y, x)), y, add.sub(x, y, h))


def now.of(g: L.Got(W.World)) -> Nat:
  (s, r) = g
  W.w.now(s)

# a model read waits at most its deadline
def rx.give.le(t: List<&2, W.Rd>, +wait: Nat, bs: Bytes(), +ms: Nat, wr: List<&2, W.Wr>, eager: Bool, +now: Nat,
  fs: List<&2, W.Fil>, out: Bytes(), soon: Bool, e: {Nat.is_lt(wait, ms) == soon : Bool}) ->
  {Nat.is_le(now.of(cw.rx.give(t, wait, bs, ms, wr, eager, now, fs, out, soon)), Nat.add(now, ms)) == True{} : Bool}:
  match soon:
    case True{}:
      le.mono(now, wait, ms, lt.le(wait, ms, e))
    case False{}:
      le.refl(Nat.add(now, ms))

def rx.le(s: W.World, +max: U32, +ms: Nat) ->
  {Nat.is_le(now.of(cw.rx(s, max, ms)), Nat.add(W.w.now(s), ms)) == True{} : Bool}:
  match s:
    case W.World{rd, wr, eager, +now, fs, out}:
      match rd:
        case Nil{}:
          le.refl(Nat.add(now, ms))
        case Con{ev, t}:
          match ev:
            case W.Hush{}:
              le.refl(Nat.add(now, ms))
            case W.Cut{code}:
              le.add(now, ms)
            case W.Give{+wait, bs}:
              rx.give.le(t, wait, bs, ms, wr, eager, now, fs, out, Nat.is_lt(wait, ms), {==})

# LAW: and a turn taken before the deadline reads for no longer than
# the time left: whatever the peer does -- answers late, says nothing,
# resets -- the read returns by the deadline. With expires, the reads
# of an exchange end by its deadline, each within its step.
law read_in_time:
  for +b: Budget
  for +max: U32
  for +until: Nat
  for +s: W.World
  for early: {Nat.is_lt(W.w.now(s), until) == True{} : Bool}
  {Nat.is_le(now.of(cw.rx(s, max, rd.ms(b, Nat.sub(until, W.w.now(s))))), until) == True{} : Bool}

def read_in_time(b, max, until, s, early):
  %add.sub(W.w.now(s), until, early) :
    {Nat.is_le(now.of(cw.rx(s, max, rd.ms(b, Nat.sub(until, W.w.now(s))))), _) == True{} : Bool}
  le.trans(now.of(cw.rx(s, max, rd.ms(b, Nat.sub(until, W.w.now(s))))),
    Nat.add(W.w.now(s), rd.ms(b, Nat.sub(until, W.w.now(s)))),
    Nat.add(W.w.now(s), Nat.sub(until, W.w.now(s))),
    rx.le(s, max, rd.ms(b, Nat.sub(until, W.w.now(s)))),
    le.mono(W.w.now(s), rd.ms(b, Nat.sub(until, W.w.now(s))), Nat.sub(until, W.w.now(s)),
      min.le(U32.to_nat(budget.step(b)), Nat.sub(until, W.w.now(s)))))
