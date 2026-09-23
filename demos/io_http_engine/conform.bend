# Conformance: the real effects against the contracts the model assumes.
#
# world.bend states, as relations, what the model of the socket world
# assumes of each effect the engine uses (rx.ok for TCP.poll_buf, tx.ok
# for TCP.send_buf_poll, lsn.ok for TCP.accept_poll, fopen.ok for
# File.open_under, fread.ok for File.read_buf), and LAWS.bend proves the
# model keeps them. This program drives each real effect through its
# contract's cases -- a read that waits out its time, one that parks
# and wakes, one asked for fewer bytes than came, a FIN, a reset; a
# send that crawls through a small window, one to a peer that stopped
# reading, one to a peer that reset; accepts with no descriptor left; a
# plain file, a missing one, a link, a directory, a climb; a file read
# in short blocks to its end -- and judges what it observes with those
# same defs. conform.c is the peer: it starts this program under a low
# descriptor limit, plays each case's peer in the same order, and checks
# what it sees from its side.
#
#   bend demos/io_http_engine/conform.bend -o conform
#   cc -std=c11 -O2 -Wall demos/io_http_engine/conform.c -o conform-peer
#   ./conform-peer ./conform 19120 /tmp/conform-root
import Base
import ./main.bend as Eng
import ./world.bend as W

# What a read answered, as data, so it can be judged twice
type Rx is Data:
  RFail{code: U32}
  RNone{}
  RSome{bs: Bytes()}

def rx.code(e: U32 & String) -> Rx:
  (code, msg) = e
  RFail{code}

def rx.obs(r: Result<&1, &1, U32 & String, Maybe<&1, Bytes()>>) -> Rx:
  match r:
    case Fail{e}:
      rx.code(e)
    case Done{may}:
      match may:
        case None{}:
          RNone{}
        case Some{bs}:
          RSome{bs}

def rx.back(o: Rx) -> Result<&1, &1, U32 & String, Maybe<&1, Bytes()>>:
  match o:
    case RFail{code}:
      Fail{(code, "")}
    case RNone{}:
      Done{None{}}
    case RSome{bs}:
      Done{Some{bs}}

# what a case wants beyond the contract
type Want is Data:
  WNone{}
  WBytes{bs: Bytes()}
  WFew{max: Nat}
  WEof{}
  WAny{}

def want.ok(w: Want, +o: Rx) -> Bool:
  match w:
    case WNone{}:
      match o:
        case RNone{}:
          True{}
        case RFail{c}:
          False{}
        case RSome{bs}:
          False{}
    case WBytes{want}:
      match o:
        case RSome{+bs}:
          String.eq(bs, want)
        case RNone{}:
          False{}
        case RFail{c}:
          False{}
    case WFew{+max}:
      match o:
        case RSome{+bs}:
          Nat.is_lt(0n, Bytes.len(bs)) && Nat.is_le(Bytes.len(bs), max)
        case RNone{}:
          False{}
        case RFail{c}:
          False{}
    case WEof{}:
      match o:
        case RSome{+bs}:
          Nat.is_eq(Bytes.len(bs), 0n)
        case RNone{}:
          False{}
        case RFail{c}:
          False{}
    case WAny{}:
      True{}

def rx.show(o: Rx) -> String:
  match o:
    case RFail{code}:
      "fail " ++ U32.show(code)
    case RNone{}:
      "nothing"
    case RSome{+bs}:
      Nat.show(Bytes.len(bs)) ++ " bytes"

def verdict(name: String, ok: Bool, note: String) -> IO(U32):
  match ok:
    case True{}:
      do IO<U32>:
        IO.print("PASS " ++ name ++ " (" ++ note ++ ")")
        return 0
    case False{}:
      do IO<U32>:
        IO.print("FAIL " ++ name ++ " (" ++ note ++ ")")
        return 1

def verdict.add(lf: Listener & U32, x: U32) -> Listener & U32:
  (l, f) = lf
  (l, (f + x : U32))

def ms.note(+took: Nat) -> String:
  Nat.show(took) ++ " ms"

# Accepting a case's connection
# =============================
#
# Each case's connection is acknowledged with one byte, "A", so the peer
# acts only once this side holds it, and cases cannot overtake each other.

def take.acked(l: Listener, m: Socket & Result<&1, &1, U32 & String, Unit>) ->
  IO(Listener & Socket):
  (s, r) = m
  IO.pure(Listener & Socket, (l, s))

def take.may(l: Listener, may: Maybe<&1, Socket>, again: Listener -> IO(Listener & Socket)) ->
  IO(Listener & Socket):
  match may:
    case None{}:
      again(l)
    case Some{s}:
      IO.bind(Socket & Result<&1, &1, U32 & String, Unit>, Listener & Socket,
        TCP.send_buf(s, "A"), m => take.acked(l, m))

def take.got(
  m: Listener & Result<&1, &1, U32 & String, Maybe<&1, Socket>>,
  again: Listener -> IO(Listener & Socket)
) -> IO(Listener & Socket):
  (l, r) = m
  match r:
    case Done{may}:
      take.may(l, may, again)
    case Fail{e}:
      again(l)

def take(k: Nat, l: Listener) -> IO(Listener & Socket):
  match k:
    case 0n:
      IO.die(Listener & Socket, 1, "conform: the peer never connected")
    case 1n+j:
      IO.bind(Listener & Result<&1, &1, U32 & String, Maybe<&1, Socket>>, Listener & Socket,
        TCP.accept_poll(l, 1000), m => take.got(m, l2 => take(j, l2)))

# Reads
# =====

def rx.judge(
  name: String, +max: U32, +ms: U32, +took: Nat, w: Want,
  m: Socket & Result<&1, &1, U32 & String, Maybe<&1, Bytes()>>
) -> IO(U32):
  (s, r) = m
  +o = rx.obs(r)
  do IO<U32>:
    Socket.close(s)
    verdict(name, W.rx.ok(max, ms, took, rx.back(o)) && want.ok(w, o),
      rx.show(o) ++ " after " ++ ms.note(took))

def rx.case.at(name: String, +max: U32, +ms: U32, w: Want, ls: Listener & Socket) ->
  IO(Listener & U32):
  (l, s) = ls
  do IO<Listener & U32>:
    t0 : Nat <- IO.now()
    m  : Socket & Result<&1, &1, U32 & String, Maybe<&1, Bytes()>> <- TCP.poll_buf(s, max, ms)
    t1 : Nat <- IO.now()
    x  : U32 <- rx.judge(name, max, ms, Nat.sub(t1, t0), w, m)
    return (l, x)

def rx.case(name: String, +max: U32, +ms: U32, w: Want, lf: Listener & U32) ->
  IO(Listener & U32):
  (l, f) = lf
  do IO<Listener & U32>:
    ls : Listener & Socket <- take(40n, l)
    lx : Listener & U32 <- rx.case.at(name, max, ms, w, ls)
    return verdict.add(lx, f)

# Sends
# =====

# 64 bytes doubled k times
def fill(k: Nat, +b: Bytes()) -> Bytes():
  match k:
    case 0n:
      b
    case 1n+j:
      fill(j, Bytes.append(b, b))

def big(k: Nat) -> Bytes():
  fill(k, "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef")

def tx.code(e: U32 & String) -> String:
  (code, msg) = e
  "fail " ++ U32.show(code)

def tx.show(r: Result<&1, &1, U32 & String, Unit>) -> String:
  match r:
    case Done{u}:
      "done"
    case Fail{e}:
      tx.code(e)

def tx.back(+ok: Bool, +code: U32) -> Result<&1, &1, U32 & String, Unit>:
  match ok:
    case True{}:
      Done{Unit{}}
    case False{}:
      Fail{(code, "")}

def tx.code.at(e: U32 & String) -> U32:
  (code, msg) = e
  code

def tx.code.of(r: Result<&1, &1, U32 & String, Unit>) -> U32:
  match r:
    case Done{u}:
      0
    case Fail{e}:
      tx.code.at(e)

# slow: whether the send must have outlived its deadline (a crawl that
# was served all the same)
def tx.judge(
  name: String, +ms: U32, peer: W.Peer, +slow: Bool, +took: Nat,
  m: Socket & Result<&1, &1, U32 & String, Unit>
) -> IO(U32):
  (s, r) = m
  +code = tx.code.of(r)
  do IO<U32>:
    Socket.close(s)
    verdict(name, W.tx.ok(ms, peer, took, tx.back(U32.is_zero(code), code))
      && (Bool.not(slow) || Nat.is_lt(U32.to_nat(ms), took)),
      tx.show(tx.back(U32.is_zero(code), code)) ++ " after " ++ ms.note(took))

def tx.case.at(
  name: String, k: Nat, +ms: U32, pause: U32, peer: W.Peer, +slow: Bool,
  ls: Listener & Socket
) -> IO(Listener & U32):
  (l, s) = ls
  do IO<Listener & U32>:
    IO.sleep(pause)
    t0 : Nat <- IO.now()
    m  : Socket & Result<&1, &1, U32 & String, Unit> <- TCP.send_buf_poll(s, big(k), ms)
    t1 : Nat <- IO.now()
    x  : U32 <- tx.judge(name, ms, peer, slow, Nat.sub(t1, t0), m)
    return (l, x)

def tx.case(
  name: String, k: Nat, +ms: U32, pause: U32, peer: W.Peer, +slow: Bool, lf: Listener & U32
) -> IO(Listener & U32):
  (l, f) = lf
  do IO<Listener & U32>:
    ls : Listener & Socket <- take(40n, l)
    lx : Listener & U32 <- tx.case.at(name, k, ms, pause, peer, slow, ls)
    return verdict.add(lx, f)

# Accepts with no descriptor left
# ===============================
#
# The peer opens more connections at once than this process has
# descriptors for. The loop takes what arrives and holds it; when
# descriptors run out, accept_poll must shed and answer nothing, never
# fail. What it holds it holds a while, so the peer can count what was
# shed; then everything held is let go, and the listener must still take
# the peer's last connection and carry its byte.

type Tally is Data:
  Tally{held: Nat, none: Nat, bad: Nat}

def tally.see(t: Tally, r: Result<&1, &1, U32 & String, Maybe<&1, Unit>>, +got: Bool) -> Tally:
  match t:
    case Tally{+held, +none, +bad}:
      Tally{Bool.pick(Nat, got, 1n+held, held), Bool.pick(Nat, got, none, 1n+none),
        Bool.pick(Nat, W.lsn.ok(r), bad, 1n+bad)}

def burst.got(
  t: Tally, xs: List<Socket>, m: Listener & Result<&1, &1, U32 & String, Maybe<&1, Socket>>,
  again: Listener -> Tally -> List<Socket> -> IO(Listener & (Tally & List<Socket>))
) -> IO(Listener & (Tally & List<Socket>)):
  (l, r) = m
  match r:
    case Done{may}:
      match may:
        case None{}:
          again(l, tally.see(t, Done{None{}}, False{}), xs)
        case Some{s}:
          again(l, tally.see(t, Done{Some{Unit{}}}, True{}), Con{s, xs})
    case Fail{e}:
      again(l, tally.see(t, Fail{e}, False{}), xs)

def burst(k: Nat, l: Listener, t: Tally, xs: List<Socket>) ->
  IO(Listener & (Tally & List<Socket>)):
  match k:
    case 0n:
      IO.pure(Listener & (Tally & List<Socket>), (l, (t, xs)))
    case 1n+j:
      IO.bind(Listener & Result<&1, &1, U32 & String, Maybe<&1, Socket>>,
        Listener & (Tally & List<Socket>), TCP.accept_poll(l, 50),
        m => burst.got(t, xs, m, l2 => t2 => xs2 => burst(j, l2, t2, xs2)))

def last.hit(l: Listener, s: Socket, hit: Bool, again: Listener -> IO(Listener & Bool)) ->
  IO(Listener & Bool):
  match hit:
    case True{}:
      do IO<Listener & Bool>:
        m : Socket & Result<&1, &1, U32 & String, Unit> <- TCP.send_buf(s, "ok")
        Socket.close(Pair.fst(Socket, Result<&1, &1, U32 & String, Unit>, m))
        return (l, True{})
    case False{}:
      do IO<Listener & Bool>:
        Socket.close(s)
        again(l)

# the last connection: its byte arrives, and "ok" goes back
def last.read(
  l: Listener, m: Socket & Result<&1, &1, U32 & String, Maybe<&1, Bytes()>>,
  again: Listener -> IO(Listener & Bool)
) -> IO(Listener & Bool):
  (s, r) = m
  match r:
    case Done{may}:
      match may:
        case Some{bs}:
          last.hit(l, s, String.eq(bs, "x"), again)
        case None{}:
          do IO<Listener & Bool>:
            Socket.close(s)
            again(l)
    case Fail{e}:
      do IO<Listener & Bool>:
        Socket.close(s)
        again(l)

def last.got(
  m: Listener & Result<&1, &1, U32 & String, Maybe<&1, Socket>>,
  again: Listener -> IO(Listener & Bool)
) -> IO(Listener & Bool):
  (l, r) = m
  match r:
    case Done{may}:
      match may:
        case None{}:
          again(l)
        case Some{s}:
          IO.bind(Socket & Result<&1, &1, U32 & String, Maybe<&1, Bytes()>>, Listener & Bool,
            TCP.poll_buf(s, 16, 500), m2 => last.read(l, m2, again))
    case Fail{e}:
      again(l)

def last(k: Nat, l: Listener) -> IO(Listener & Bool):
  match k:
    case 0n:
      IO.pure(Listener & Bool, (l, False{}))
    case 1n+j:
      IO.bind(Listener & Result<&1, &1, U32 & String, Maybe<&1, Socket>>, Listener & Bool,
        TCP.accept_poll(l, 250), m => last.got(m, l2 => last(j, l2)))

def shed.judge(t: Tally, lb: Listener & Bool) -> IO(Listener & U32):
  match t:
    case Tally{+held, +none, +bad}:
      (l, +ok) = lb
      do IO<Listener & U32>:
        x : U32 <- verdict("lsn.emfile", Nat.is_eq(bad, 0n) && Nat.is_lt(0n, held) && ok,
          Nat.show(held) ++ " held, " ++ Nat.show(none) ++ " nothing, " ++ Nat.show(bad)
            ++ " failures, the last one " ++ Bool.pick(String, ok, "served", "lost"))
        return (l, x)

def shed.close(l: Listener, tx: Tally & List<Socket>) -> IO(Listener & U32):
  (t, xs) = tx
  do IO<Listener & U32>:
    IO.sleep(1500)
    List.for_each(~&1, ~Socket, ~Socket.close, xs)
    lb : Listener & Bool <- last(40n, l)
    shed.judge(t, lb)

def shed.after(ltx: Listener & (Tally & List<Socket>)) -> IO(Listener & U32):
  (l, tx) = ltx
  shed.close(l, tx)

def shed(lf: Listener & U32) -> IO(Listener & U32):
  (l, f) = lf
  do IO<Listener & U32>:
    ltx : Listener & (Tally & List<Socket>) <- burst(60n, l, Tally{0n, 0n, 0n}, Nil{})
    lx  : Listener & U32 <- shed.after(ltx)
    return verdict.add(lx, f)

# Files
# =====

def open.seen(r: Result<&1, &1, U32 & String, File>) -> IO(Bool):
  match r:
    case Done{f}:
      do IO<Bool>:
        File.close(f)
        return True{}
    case Fail{e}:
      IO.pure(Bool, False{})

def open.back(+ok: Bool) -> Result<&1, &1, U32 & String, Unit>:
  match ok:
    case True{}:
      Done{Unit{}}
    case False{}:
      Fail{(2, "")}

def open.case.judge(name: String, k: W.Name, +ok: Bool) -> IO(U32):
  verdict(name, W.fopen.ok(k, open.back(ok)), Bool.pick(String, ok, "opened", "refused"))

def open.case(root: String, name: String, path: String, k: W.Name, f: U32) -> IO(U32):
  do IO<U32>:
    r  : Result<&1, &1, U32 & String, File> <- File.open_under(root, path)
    ok : Bool <- open.seen(r)
    x  : U32 <- open.case.judge(name, k, ok)
    return (f + x : U32)

def read.see(r: Result<&1, &1, U32 & String, Bytes()>) -> Maybe<&2, Nat>:
  match r:
    case Done{+bs}:
      Some{Bytes.len(bs)}
    case Fail{e}:
      None{}

def read.judge(name: String, +left: Nat, mn: Maybe<&2, Nat>) -> IO(U32):
  match mn:
    case None{}:
      verdict(name, False{}, "the read failed")
    case Some{+n}:
      verdict(name, W.fread.ok(4, left, Done{String.repeat("r", n)}),
        Nat.show(n) ++ " of " ++ Nat.show(left) ++ " left")

def read.step(
  name: String, +left: Nat, m: File & Result<&1, &1, U32 & String, Bytes()>
) -> IO(File & U32):
  (f, r) = m
  do IO<File & U32>:
    x : U32 <- read.judge(name, left, read.see(r))
    return (f, x)

def read.sum(fy: File & U32, x: U32) -> File & U32:
  (f, y) = fy
  (f, (x + y : U32))

def read.more(name: String, +left: Nat, fx: File & U32) -> IO(File & U32):
  (f, x) = fx
  do IO<File & U32>:
    m : File & Result<&1, &1, U32 & String, Bytes()> <- File.read_buf(f, 4)
    fy : File & U32 <- read.step(name, left, m)
    return read.sum(fy, x)

def read.close(fx: File & U32) -> IO(U32):
  (f, x) = fx
  do IO<U32>:
    File.close(f)
    return x

def read.file(r: Result<&1, &1, U32 & String, File>) -> IO(U32):
  match r:
    case Fail{e}:
      verdict("fread", False{}, "a.txt did not open")
    case Done{f}:
      do IO<U32>:
        a : File & U32 <- read.more("fread.head", 6n, (f, 0))
        b : File & U32 <- read.more("fread.rest", 2n, a)
        c : File & U32 <- read.more("fread.end", 0n, b)
        read.close(c)

def files(+root: String, f: U32) -> IO(U32):
  do IO<U32>:
    f1 : U32 <- open.case(root, "fopen.plain", "a.txt", W.Plain{}, f)
    f2 : U32 <- open.case(root, "fopen.absent", "missing.txt", W.Absent{}, f1)
    f3 : U32 <- open.case(root, "fopen.link", "link", W.Linked{}, f2)
    f4 : U32 <- open.case(root, "fopen.dir", "sub", W.Dir{}, f3)
    f5 : U32 <- open.case(root, "fopen.climb", "../conform-outside.txt", W.Climbs{}, f4)
    r  : Result<&1, &1, U32 & String, File> <- File.open_under(root, "a.txt")
    x  : U32 <- read.file(r)
    return (f5 + x : U32)

# The run
# =======

def finish.tell(+g: U32, ok: Bool) -> IO(Unit):
  match ok:
    case True{}:
      IO.print("conform: every effect kept its contract")
    case False{}:
      IO.die(Unit, 1, "conform: " ++ U32.show(g) ++ " cases broke a contract")

def finish.say(+g: U32) -> IO(Unit):
  finish.tell(g, U32.is_zero(g))

def finish(root: String, lf: Listener & U32) -> IO(Unit):
  (l, f) = lf
  do IO<Unit>:
    Listener.close(l)
    g : U32 <- files(root, f)
    finish.say(g)

def run(root: String, l: Listener) -> IO(Unit):
  do IO<Unit>:
    IO.print("ready")
    a : Listener & U32 <- rx.case("rx.silent", 100, 300, WNone{}, (l, 0))
    b : Listener & U32 <- rx.case("rx.wakes", 100, 2000, WBytes{"0123456789"}, a)
    c : Listener & U32 <- rx.case("rx.max", 4, 2000, WFew{4n}, b)
    d : Listener & U32 <- rx.case("rx.fin", 100, 2000, WEof{}, c)
    e : Listener & U32 <- rx.case("rx.reset", 100, 2000, WAny{}, d)
    g : Listener & U32 <- tx.case("tx.crawl", 18n, 300, 0, W.Reads{}, True{}, e)
    h : Listener & U32 <- tx.case("tx.stall", 18n, 300, 0, W.Stops{}, False{}, g)
    i : Listener & U32 <- tx.case("tx.reset", 14n, 1000, 200, W.Resets{}, False{}, h)
    j : Listener & U32 <- shed(i)
    finish(root, j)

def conform.at(root: String, may: Maybe<&2, U32>) -> IO(Unit):
  match may:
    case None{}:
      IO.die(Unit, 2, "conform: PORT is a number")
    case Some{port}:
      do IO<Unit>:
        l : Listener <- IO.try(Listener, TCP.listen(port))
        run(root, l)

def args.go(xs: List<String>) -> IO(Unit):
  match xs:
    case Con{port, rest}:
      match rest:
        case Con{root, more}:
          conform.at(root, U32.read(port))
        case Nil{}:
          IO.die(Unit, 2, "usage: conform PORT ROOT")
    case Nil{}:
      IO.die(Unit, 2, "usage: conform PORT ROOT")

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    args.go(xs)
