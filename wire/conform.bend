# Conformance: the real effects against the contracts the model assumes.
#
# world.bend states, as relations, what the model of the socket world
# assumes of each effect the loops use (rx.ok for TCP.poll_buf, tx.ok
# for TCP.send_buf_poll, lsn.ok for TCP.accept_poll, fopen.ok for
# File.open_under, fread.ok for File.read_buf), and proves the model
# keeps them (rx_model, tx_stalled, tx_served, fread_model). This program drives each real effect through its
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
#   bend wire/conform.bend -o conform
#   cc -std=c11 -O2 -Wall wire/conform.c -o conform-peer -lssl -lcrypto
#   ./conform-peer ./conform 19120 /tmp/conform-root
#
# (the peer runs ./conform PORT ROOT CA), and, out of this program, the connects: TCP.connect_poll to a peer
# that accepts, to a closed port, to one whose SYNs go unanswered
# (cx.ok), and TLS.connect to a server its pin trusts, to the same
# server against the system's store, under another name, and to one
# that does not speak TLS (tls.ok).
import Base
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

# Connects
# ========
#
# The peer listens on port + 1 and accepts; nothing listens on port + 2;
# port + 3's backlog is full, so its SYNs go unanswered; port + 4 is a
# TLS server whose certificate names localhost and is its own CA (the
# file ca), and it answers "ping" with "pong" through the session;
# port + 5 speaks plain HTTP and closes.

def cx.judge(name: String, +ms: U32, d: W.Dial, +took: Nat, +ok: Bool, +code: U32, f: U32) ->
  IO(U32):
  do IO<U32>:
    x : U32 <- verdict(name, W.cx.ok(ms, d, took, tx.back(ok, code)),
      tx.show(tx.back(ok, code)) ++ " after " ++ ms.note(took))
    return (f + x : U32)

def cx.back(name: String, +ms: U32, d: W.Dial, +took: Nat, f: U32,
  r: Result<&1, &1, U32 & String, Socket>) -> IO(U32):
  match r:
    case Done{s}:
      do IO<U32>:
        Socket.close(s)
        cx.judge(name, ms, d, took, True{}, 0, f)
    case Fail{e}:
      (code, msg) = e
      cx.judge(name, ms, d, took, False{}, code, f)

def cx.case(name: String, +port: U32, +ms: U32, d: W.Dial, f: U32) -> IO(U32):
  do IO<U32>:
    t0 : Nat <- IO.now()
    r  : Result<&1, &1, U32 & String, Socket> <- TCP.connect_poll("127.0.0.1", port, ms)
    t1 : Nat <- IO.now()
    cx.back(name, ms, d, Nat.sub(t1, t0), f, r)

# a session that came up must carry bytes both ways: "ping" out, "pong"
# back, through the wire the byte effects share
def tls.pong.is(r: Result<&1, &1, U32 & String, Maybe<&1, Bytes()>>) -> Bool:
  match r:
    case Done{may}:
      match may:
        case Some{bs}:
          String.eq(bs, "pong")
        case None{}:
          False{}
    case Fail{e}:
      False{}

def tls.pong(m: Socket & Result<&1, &1, U32 & String, Maybe<&1, Bytes()>>) -> IO(Bool):
  (s, r) = m
  do IO<Bool>:
    Socket.close(s)
    return tls.pong.is(r)

def tls.talk(m: Socket & Result<&1, &1, U32 & String, Unit>) -> IO(Bool):
  (s, r) = m
  IO.bind(Socket & Result<&1, &1, U32 & String, Maybe<&1, Bytes()>>, Bool,
    TCP.poll_buf(s, 16, 2000), tls.pong)

def tls.judge(name: String, c: W.Cert, u: Result<&1, &1, U32 & String, Unit>, +talked: Bool,
  note: String, f: U32) -> IO(U32):
  do IO<U32>:
    x : U32 <- verdict(name, W.tls.ok(c, u) && talked, note)
    return (f + x : U32)

def tls.back(name: String, c: W.Cert, f: U32, r: Result<&1, &1, U32 & String, Socket & String>) ->
  IO(U32):
  match r:
    case Done{sp}:
      (s, +proto) = sp
      do IO<U32>:
        m  : Socket & Result<&1, &1, U32 & String, Unit> <- TCP.send_buf_poll(s, "ping", 2000)
        +ok : Bool <- tls.talk(m)
        tls.judge(name, c, Done{Unit{}}, ok && String.eq(proto, "http/1.1"),
          "done, " ++ Bool.pick(String, ok, "pong came back", "no pong") ++ ", ALPN " ++ proto, f)
    case Fail{e}:
      (+code, msg) = e
      tls.judge(name, c, Fail{(code, "")}, True{}, "fail " ++ U32.show(code) ++ " (" ++ msg ++ ")", f)

def tls.case(name: String, +port: U32, name2: String, ca: String, c: W.Cert, f: U32) -> IO(U32):
  IO.bind(Result<&1, &1, U32 & String, Socket & String>, U32,
    TLS.connect("127.0.0.1", port, name2, "http/1.1", ca, 2000), r => tls.back(name, c, f, r))

# TCP.idle: port + 6 takes one byte saying what to do -- "q" nothing,
# "b" send a byte, "f" close -- and conform asks, a moment later,
# whether the connection is idle
def idle.judge(name: String, k: W.Pend, m: Socket & Bool, f: U32) -> IO(U32):
  (s, +ok) = m
  do IO<U32>:
    Socket.close(s)
    x : U32 <- verdict(name, W.idle.ok(k, ok), Bool.pick(String, ok, "idle", "not idle"))
    return (f + x : U32)

def idle.sent(name: String, k: W.Pend, m: Socket & Result<&1, &1, U32 & String, Unit>, f: U32) -> IO(U32):
  (s, r) = m
  do IO<U32>:
    IO.sleep(200)
    got : Socket & Bool <- TCP.idle(s)
    idle.judge(name, k, got, f)

def verdict.add.io(name: String, f: U32) -> IO(U32):
  do IO<U32>:
    x : U32 <- verdict(name, False{}, "no connection")
    return (f + x : U32)

def idle.case.at(name: String, cmd: String, k: W.Pend, f: U32, r: Result<&1, &1, U32 & String, Socket>) -> IO(U32):
  match r:
    case Done{s}:
      IO.bind(Socket & Result<&1, &1, U32 & String, Unit>, U32, TCP.send_buf_poll(s, cmd, 2000),
        m => idle.sent(name, k, m, f))
    case Fail{e}:
      verdict.add.io(name, f)

def idle.case(name: String, +port: U32, cmd: String, k: W.Pend, f: U32) -> IO(U32):
  IO.bind(Result<&1, &1, U32 & String, Socket>, U32, TCP.connect_poll("127.0.0.1", port, 2000),
    r => idle.case.at(name, cmd, k, f, r))

def connects(+port: U32, +ca: String, f: U32) -> IO(U32):
  do IO<U32>:
    a : U32 <- cx.case("cx.accepts", (port + 1 : U32), 2000, W.Accepts{}, f)
    b : U32 <- cx.case("cx.refused", (port + 2 : U32), 2000, W.Closed{}, a)
    c : U32 <- cx.case("cx.silent", (port + 3 : U32), 300, W.Silent{}, b)
    d : U32 <- tls.case("tls.pinned", (port + 4 : U32), "localhost", ca, W.Trusted{}, c)
    e : U32 <- tls.case("tls.untrusted", (port + 4 : U32), "localhost", "", W.Untrusted{}, d)
    g : U32 <- tls.case("tls.misnamed", (port + 4 : U32), "example.com", ca, W.Misnamed{}, e)
    h : U32 <- tls.case("tls.plain", (port + 5 : U32), "localhost", ca, W.NotTls{}, g)
    i : U32 <- idle.case("idle.quiet", (port + 6 : U32), "q", W.PQuiet{}, h)
    j : U32 <- idle.case("idle.byte", (port + 6 : U32), "b", W.PByte{}, i)
    idle.case("idle.fin", (port + 6 : U32), "f", W.PFin{}, j)

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

def finish(+port: U32, root: String, ca: String, lf: Listener & U32) -> IO(Unit):
  (l, f) = lf
  do IO<Unit>:
    Listener.close(l)
    g : U32 <- files(root, f)
    h : U32 <- connects(port, ca, g)
    finish.say(h)

def run(+port: U32, root: String, ca: String, l: Listener) -> IO(Unit):
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
    finish(port, root, ca, j)

def conform.at(root: String, ca: String, may: Maybe<&2, U32>) -> IO(Unit):
  match may:
    case None{}:
      IO.die(Unit, 2, "conform: PORT is a number")
    case Some{+port}:
      do IO<Unit>:
        l : Listener <- IO.try(Listener, TCP.listen(port))
        run(port, root, ca, l)

def args.go(xs: List<String>) -> IO(Unit):
  match xs:
    case Con{port, rest}:
      match rest:
        case Con{root, more}:
          match more:
            case Con{ca, none}:
              conform.at(root, ca, U32.read(port))
            case Nil{}:
              IO.die(Unit, 2, "usage: conform PORT ROOT CA")
        case Nil{}:
          IO.die(Unit, 2, "usage: conform PORT ROOT CA")
    case Nil{}:
      IO.die(Unit, 2, "usage: conform PORT ROOT CA")

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    args.go(xs)
