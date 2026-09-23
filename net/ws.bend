# A WebSocket client (RFC 6455), over TCP or TLS.
#
#   c : Ws.Conn <- IO.try? no: Ws.connect answers a Result with why
#   r <- Ws.connect("wss://echo.example/chat", Ws.opts())
#   (c, s) <- Ws.send_text(c, "hello")
#   (c, m) <- Ws.recv(c)             # Text{..} | Binary{..} | Closed{code, reason}
#   r <- Ws.close(c, 1000, "bye")    # the closing handshake, under a deadline
#
# connect resolves the host (DNS.resolve), dials under a deadline
# (TCP.connect_poll, or TLS.connect with SNI, ALPN http/1.1 and the
# certificate verified against the system's store or the pinned CA in
# the options), sends the opening request with a key of sixteen random
# bytes (IO.random_u32), and reads the answer's head under the same
# deadline and a cap, judged by ws_hs.bend (status 101, Upgrade,
# Connection, the Accept the key asks for, no extension, a subprotocol
# only if offered). Whatever came after the head is the first frames.
#
# Every frame the client sends is masked with a key of its own
# (ws_frame.bend's c.frame; ws_laws.bend's frame_masked and mask_inv).
# What comes back is read by the role-generalised reader at the client's
# end, and each frame goes through the assembler: fragments are joined
# under the options' cap (1009 past it), a ping is answered with a pong
# as it comes, a pong is dropped, text is held to UTF-8 (1007), and
# anything the RFC forbids (a masked frame, a reserved bit, an unknown
# opcode, a long or cut control frame, a continuation out of place)
# fails the connection with 1002: a close frame with the code goes out,
# and the error comes back (EProto). A close from the server is answered
# with its own code and handed over as Closed{code, reason}.
#
# A handle is affine: every call hands the connection back, and close
# (or drop) releases the socket. recv waits at most the options' recv_ms
# (recv_for takes its own); a recv that times out leaves the connection
# as it was.
import Base
import ../demos/io_http_engine/ws.bend as Ws
import ../demos/io_http_engine/b64.bend as B64
import ../demos/io_http_engine/sha1.bend as Sha1
import ./ws_frame.bend as F
import ./ws_hs.bend as H

# The options
# ===========

# the subprotocols to offer, in order; a CA file to trust instead of the
# system's store ("" for the store); the deadlines, in ms: the whole
# opening (connect, TLS and the handshake), a recv, and the closing
# handshake; the most bytes a message may carry; the most bytes of the
# answer's head
type Opts is Data:
  Opts{protocols: List<&2, String>, ca: String, connect_ms: U32, recv_ms: U32, close_ms: U32,
    max_msg: U32, head_max: U32}

def opts() -> Opts:
  Opts{[], "", 10000, 30000, 5000, 67108864, 16384}

def opts.protocols(o: Opts, ps: List<&2, String>) -> Opts:
  match o:
    case Opts{protocols, ca, cm, rm, xm, mm, hm}:
      Opts{ps, ca, cm, rm, xm, mm, hm}

def opts.ca(o: Opts, file: String) -> Opts:
  match o:
    case Opts{protocols, ca, cm, rm, xm, mm, hm}:
      Opts{protocols, file, cm, rm, xm, mm, hm}

def opts.timeouts(o: Opts, connect: U32, recv: U32, close: U32) -> Opts:
  match o:
    case Opts{protocols, ca, cm, rm, xm, mm, hm}:
      Opts{protocols, ca, connect, recv, close, mm, hm}

def opts.max_msg(o: Opts, n: U32) -> Opts:
  match o:
    case Opts{protocols, ca, cm, rm, xm, mm, hm}:
      Opts{protocols, ca, cm, rm, xm, n, hm}

def o.protocols(o: Opts) -> List<&2, String>:
  match o:
    case Opts{protocols, ca, cm, rm, xm, mm, hm}:
      protocols

def o.ca(o: Opts) -> String:
  match o:
    case Opts{protocols, ca, cm, rm, xm, mm, hm}:
      ca

def o.connect(o: Opts) -> U32:
  match o:
    case Opts{protocols, ca, cm, rm, xm, mm, hm}:
      cm

def o.recv(o: Opts) -> U32:
  match o:
    case Opts{protocols, ca, cm, rm, xm, mm, hm}:
      rm

def o.close(o: Opts) -> U32:
  match o:
    case Opts{protocols, ca, cm, rm, xm, mm, hm}:
      xm

def o.cap(o: Opts) -> U32:
  match o:
    case Opts{protocols, ca, cm, rm, xm, mm, hm}:
      mm

def o.head(o: Opts) -> U32:
  match o:
    case Opts{protocols, ca, cm, rm, xm, mm, hm}:
      hm

# Errors
# ======

# why there is no connection or no message: the URL; the name (code);
# the connection or TLS (code: 13, EACCES, for a certificate refused);
# a deadline; the answer's head past its cap; the handshake refused
# (why); a send or a read (code); the peer closed the TCP connection
# without a close frame (1006); the connection failed with a code this
# end sent (1002, 1007, 1009); the connection is closed; no random bytes
type Err is Data:
  EUrl{}
  EDns{code: U32}
  EConnect{code: U32}
  ETime{}
  EHead{}
  EHand{why: H.Hw}
  ESend{code: U32}
  ERecv{code: U32}
  EEof{}
  EProto{code: U32}
  EClosed{}
  ERand{code: U32}

def err.show(e: Err) -> String:
  match e:
    case EUrl{}:
      "not a ws:// or wss:// URL"
    case EDns{c}:
      "the name did not resolve (" ++ U32.show(c) ++ ")"
    case EConnect{c}:
      "no connection (" ++ U32.show(c) ++ ")"
    case ETime{}:
      "timed out"
    case EHead{}:
      "the answer's head is too long"
    case EHand{w}:
      "handshake refused: " ++ H.hw.show(w)
    case ESend{c}:
      "send failed (" ++ U32.show(c) ++ ")"
    case ERecv{c}:
      "read failed (" ++ U32.show(c) ++ ")"
    case EEof{}:
      "the peer closed the connection without a close frame (1006)"
    case EProto{c}:
      "the connection failed with " ++ U32.show(c)
    case EClosed{}:
      "the connection is closed"
    case ERand{c}:
      "no random bytes (" ++ U32.show(c) ++ ")"

# The connection
# ==============

# rd: the frame reader; q: frames read and not yet handed over; a: the
# assembler; o: the options; proto: the subprotocol agreed ("" for
# none); sent: whether this end has sent its close; shut: 0 open, 1
# closed by the closing handshake, 2 failed; peer: the server's close
# code, once it came
type St is Data:
  St{rd: Ws.W, q: List<&2, Ws.Frm>, a: F.Asm, o: Opts, proto: Bytes(), sent: Bool, shut: U32, peer: U32}

type Conn is Type:
  Conn{sock: Socket, st: St}

def st.o(s: St) -> Opts:
  match s:
    case St{rd, q, a, o, proto, sent, shut, peer}:
      o

def st.proto(s: St) -> Bytes():
  match s:
    case St{rd, q, a, o, proto, sent, shut, peer}:
      proto

def st.sent(s: St) -> Bool:
  match s:
    case St{rd, q, a, o, proto, sent, shut, peer}:
      sent

def st.shut(s: St) -> U32:
  match s:
    case St{rd, q, a, o, proto, sent, shut, peer}:
      shut

def st.mark(s: St, +sent2: Bool, +shut2: U32) -> St:
  match s:
    case St{rd, q, a, o, proto, sent, shut, peer}:
      St{rd, q, a, o, proto, sent || sent2, U32.max(shut, shut2), peer}

def st.peer(s: St, +code: U32) -> St:
  match s:
    case St{rd, q, a, o, proto, sent, shut, peer}:
      St{rd, q, a, o, proto, sent, shut, code}

def st.peer.of(s: St) -> U32:
  match s:
    case St{rd, q, a, o, proto, sent, shut, peer}:
      peer

def Out(A: Data) -> Type:
  Conn & Result<&2, &2, Err, A>

def big() -> Nat:
  U32.to_nat(4294967295)

# a deadline's time left, as a poll takes it
def left(+until: Nat, +now: Nat) -> U32:
  U32.from_nat(Nat.min(Nat.sub(until, now), 2147483647n))

# Sending
# =======

def sent(+st: St, g: Socket & Result<&1, &1, U32 & String, Unit>) -> IO(Out(Unit)):
  (s, r) = g
  match r:
    case Done{u}:
      IO.pure(Out(Unit), (Conn{s, st}, Done{Unit{}}))
    case Fail{e}:
      (code, msg) = e
      IO.pure(Out(Unit), (Conn{s, st.mark(st, False{}, 2)}, Fail{ESend{code}}))

# one frame out, masked with a fresh key from the host's entropy
def send.keyed(sock: Socket, +st: St, op: U32, fin: Bool, +body: Bytes(), g: Result<&1, &1, U32 & String, U32>) ->
  IO(Out(Unit)):
  match g:
    case Done{+m}:
      IO.bind(Socket & Result<&1, &1, U32 & String, Unit>, Out(Unit),
        TCP.send_buf_poll(sock, F.c.frame(op, fin, body, m), o.recv(st.o(st))), x => sent(st, x))
    case Fail{e}:
      (code, msg) = e
      IO.pure(Out(Unit), (Conn{sock, st}, Fail{ERand{code}}))

def send.frame(sock: Socket, +st: St, op: U32, fin: Bool, +body: Bytes()) -> IO(Out(Unit)):
  IO.bind(Result<&1, &1, U32 & String, U32>, Out(Unit), IO.random_u32(),
    g => send.keyed(sock, st, op, fin, body, g))

def send.open(sock: Socket, +st: St, op: U32, +body: Bytes(), open: Bool) -> IO(Out(Unit)):
  match open:
    case True{}:
      send.frame(sock, st, op, True{}, body)
    case False{}:
      IO.pure(Out(Unit), (Conn{sock, st}, Fail{EClosed{}}))

def send(c: Conn, op: U32, body: Bytes()) -> IO(Out(Unit)):
  match c:
    case Conn{sock, +st}:
      send.open(sock, st, op, body, U32.is_zero(st.shut(st)) && Bool.not(st.sent(st)))

# a text message: the String's UTF-8
def send_text(c: Conn, s: String) -> IO(Out(Unit)):
  send(c, 1, F.utf8.enc(s))

def send_bytes(c: Conn, b: Bytes()) -> IO(Out(Unit)):
  send(c, 2, b)

# a ping; its payload is cut to the 125 bytes a control frame carries
def ping(c: Conn, b: Bytes()) -> IO(Out(Unit)):
  send(c, 9, String.take(b, 125n))

# the subprotocol the server chose, "" for none
def protocol(c: Conn) -> Conn & Bytes():
  match c:
    case Conn{sock, +st}:
      (Conn{sock, st}, st.proto(st))

# Reading
# =======

# waiting out the peer's close of the TCP connection, after the closing
# handshake: polls of ms each, what comes is dropped, until the FIN, an
# error, a poll with nothing, or k polls
def drain.more(s: Socket, eof: Bool, again: Socket -> IO(Socket)) -> IO(Socket):
  match eof:
    case True{}:
      IO.pure(Socket, s)
    case False{}:
      again(s)

def drain.got(g: Socket & Result<&1, &1, U32 & String, Maybe<&1, Bytes()>>, again: Socket -> IO(Socket)) ->
  IO(Socket):
  (s, r) = g
  match r:
    case Fail{e}:
      IO.pure(Socket, s)
    case Done{may}:
      match may:
        case None{}:
          IO.pure(Socket, s)
        case Some{+bs}:
          drain.more(s, String.is_empty(bs), again)

def drain(k: Nat, sock: Socket, +ms: U32) -> IO(Socket):
  match k:
    case 0n:
      IO.pure(Socket, sock)
    case 1n+j:
      IO.bind(Socket & Result<&1, &1, U32 & String, Maybe<&1, Bytes()>>, Socket, TCP.poll_buf(sock, 65536, ms),
        g => drain.got(g, s => drain(j, s, ms)))

# the frames a read completed join the queue; a read that broke the
# framing leaves its good frames first and the break after them
def fed(tk: Ws.W & List<&2, Ws.Frm>, a: F.Asm, o: Opts, proto: Bytes(), sent: Bool, shut: U32, peer: U32) -> St:
  (rd, fs) = tk
  St{rd, fs, a, o, proto, sent, shut, peer}

def st.feed(s: St, bs: Bytes()) -> St:
  match s:
    case St{rd, q, a, +o, proto, sent, shut, peer}:
      fed(Ws.take(F.feed_buf(F.Cli{o.cap(o)}, bs, rd)), a, o, proto, sent, shut, peer)

def st.pop(s: St) -> St & Maybe<&2, Ws.Frm>:
  match s:
    case St{rd, q, a, o, proto, sent, shut, peer}:
      match q:
        case Nil{}:
          (St{rd, Nil{}, a, o, proto, sent, shut, peer}, None{})
        case Con{f, t}:
          (St{rd, t, a, o, proto, sent, shut, peer}, Some{f})

def st.asm(s: St, f: Ws.Frm) -> St & F.Act:
  match s:
    case St{rd, q, a, +o, proto, sent, shut, peer}:
      +x = F.asm(o.cap(o), a, f)
      (St{rd, q, F.ax.asm(x), o, proto, sent, shut, peer}, F.ax.act(x))

def st.dead.of(wb: Ws.W & Bool, q: List<&2, Ws.Frm>, a: F.Asm, o: Opts, proto: Bytes(), sent: Bool, shut: U32,
  peer: U32) -> St & Bool:
  (w, bad) = wb
  (St{w, q, a, o, proto, sent, shut, peer}, bad)

def st.dead(s: St) -> St & Bool:
  match s:
    case St{rd, q, a, o, proto, sent, shut, peer}:
      st.dead.of(Ws.dead(rd), q, a, o, proto, sent, shut, peer)

def R(A: Data) -> Type:
  IO(Out(A))

# failing the connection: a close with the code goes out (unless this
# end sent its close already), and the error comes back
def fail.sent(e: Err, g: Out(Unit)) -> R(F.Msg):
  (c, r) = g
  IO.pure(Out(F.Msg), (c, Fail{e}))

def fail.go(sock: Socket, +st: St, +code: U32, e: Err, was: Bool) -> R(F.Msg):
  match was:
    case True{}:
      IO.pure(Out(F.Msg), (Conn{sock, st.mark(st, True{}, 2)}, Fail{e}))
    case False{}:
      IO.bind(Out(Unit), Out(F.Msg), send.frame(sock, st.mark(st, True{}, 2), 8, True{}, F.close.body(code, "")),
        g => fail.sent(e, g))

def fail(sock: Socket, +st: St, +code: U32, e: Err) -> R(F.Msg):
  fail.go(sock, st, code, e, st.sent(st))

# the peer's close: answered with its code (unless this end sent its
# close first, and this is the answer), then the TCP connection waited
# out, and the close handed over
def bye.out(+code: U32, reason: Bytes(), s: Socket, +st: St) -> R(F.Msg):
  IO.bind(Socket, Out(F.Msg), drain(64n, s, o.close(st.o(st))),
    s2 => IO.pure(Out(F.Msg), (Conn{s2, st}, Done{F.Closed{code, F.utf8.dec(reason)}})))

def bye.sent(+code: U32, reason: Bytes(), g: Out(Unit)) -> R(F.Msg):
  (c, r) = g
  match c:
    case Conn{s, st}:
      bye.out(code, reason, s, st)

def bye(sock: Socket, +st: St, +code: U32, reason: Bytes(), was: Bool) -> R(F.Msg):
  match was:
    case True{}:
      bye.out(code, reason, sock, st.peer(st.mark(st, True{}, 1), code))
    case False{}:
      IO.bind(Out(Unit), Out(F.Msg),
        send.frame(sock, st.peer(st.mark(st, True{}, 1), code), 8, True{}, F.close.body(code, "")),
        g => bye.sent(code, reason, g))

def pong.sent(g: Out(Unit), again: Socket -> St -> R(F.Msg)) -> R(F.Msg):
  (c, r) = g
  match c:
    case Conn{s, st}:
      match r:
        case Done{u}:
          again(s, st)
        case Fail{e}:
          IO.pure(Out(F.Msg), (Conn{s, st}, Fail{e}))

# a ping is answered at once, with its payload; not after this end's
# close
def pong(sock: Socket, +st: St, +body: Bytes(), was: Bool, again: Socket -> St -> R(F.Msg)) -> R(F.Msg):
  match was:
    case True{}:
      again(sock, st)
    case False{}:
      IO.bind(Out(Unit), Out(F.Msg), send.frame(sock, st, 10, True{}, body), g => pong.sent(g, again))

# what a frame asked of the connection, done
def act(sock: Socket, +st: St, x: F.Act, again: Socket -> St -> R(F.Msg)) -> R(F.Msg):
  match x:
    case F.Deliver{m}:
      IO.pure(Out(F.Msg), (Conn{sock, st}, Done{m}))
    case F.Pong{body}:
      pong(sock, st, body, st.sent(st), again)
    case F.Skip{}:
      again(sock, st)
    case F.Bye{+code, reason}:
      bye(sock, st, code, reason, st.sent(st))
    case F.Refuse{+code}:
      fail(sock, st, code, EProto{code})

def got.bytes(s: Socket, +st: St, bs: Bytes(), eof: Bool, again: Socket -> St -> R(F.Msg)) -> R(F.Msg):
  match eof:
    case True{}:
      IO.pure(Out(F.Msg), (Conn{s, st.mark(st, False{}, 2)}, Fail{EEof{}}))
    case False{}:
      again(s, st.feed(st, bs))

def got(+st: St, g: Socket & Result<&1, &1, U32 & String, Maybe<&1, Bytes()>>, again: Socket -> St -> R(F.Msg)) ->
  R(F.Msg):
  (s, r) = g
  match r:
    case Fail{e}:
      (code, msg) = e
      IO.pure(Out(F.Msg), (Conn{s, st.mark(st, False{}, 2)}, Fail{ERecv{code}}))
    case Done{may}:
      match may:
        case None{}:
          IO.pure(Out(F.Msg), (Conn{s, st}, Fail{ETime{}}))
        case Some{+bs}:
          got.bytes(s, st, bs, String.is_empty(bs), again)

# nothing queued: the framing broke (1002), or one read, waiting at
# most the time left
def wait(sock: Socket, +st: St, +until: Nat, +now: Nat, live: Bool, again: Socket -> St -> R(F.Msg)) -> R(F.Msg):
  match live:
    case False{}:
      IO.pure(Out(F.Msg), (Conn{sock, st}, Fail{ETime{}}))
    case True{}:
      IO.bind(Socket & Result<&1, &1, U32 & String, Maybe<&1, Bytes()>>, Out(F.Msg),
        TCP.poll_buf(sock, 65536, left(until, now)), g => got(st, g, again))

def empty(sock: Socket, +st: St, +until: Nat, bad: Bool, again: Socket -> St -> R(F.Msg)) -> R(F.Msg):
  match bad:
    case True{}:
      fail(sock, st, 1002, EProto{1002})
    case False{}:
      IO.bind(Nat, Out(F.Msg), IO.now(), +now => wait(sock, st, until, now, Nat.is_lt(now, until), again))

def dead(sock: Socket, +until: Nat, sb: St & Bool, again: Socket -> St -> R(F.Msg)) -> R(F.Msg):
  (st, bad) = sb
  empty(sock, st, until, bad, again)

def asmd(sock: Socket, sx: St & F.Act, again: Socket -> St -> R(F.Msg)) -> R(F.Msg):
  (st, x) = sx
  act(sock, st, x, again)

def popped(sock: Socket, +until: Nat, sm: St & Maybe<&2, Ws.Frm>, again: Socket -> St -> R(F.Msg)) -> R(F.Msg):
  (st, may) = sm
  match may:
    case Some{f}:
      asmd(sock, st.asm(st, f), again)
    case None{}:
      dead(sock, until, st.dead(st), again)

def turn(sock: Socket, +st: St, +until: Nat, open: Bool, again: Socket -> St -> R(F.Msg)) -> R(F.Msg):
  match open:
    case False{}:
      IO.pure(Out(F.Msg), (Conn{sock, st}, Fail{EClosed{}}))
    case True{}:
      popped(sock, until, st.pop(st), again)

# k bounds the turns: each hands a queued frame over or reads once
def recv.go(k: Nat, sock: Socket, +st: St, +until: Nat) -> R(F.Msg):
  match k:
    case 0n:
      IO.pure(Out(F.Msg), (Conn{sock, st}, Fail{ETime{}}))
    case 1n+j:
      turn(sock, st, until, U32.is_zero(st.shut(st)), s => t => recv.go(j, s, t, until))

def recv.at(sock: Socket, +st: St, +ms: U32, +now: Nat) -> R(F.Msg):
  recv.go(big(), sock, st, Nat.add(now, U32.to_nat(ms)))

# The next message, waiting at most ms: text, binary, or the server's
# close (answered already). A ping on the way is answered, and a
# timeout leaves the connection as it was.
def recv_for(c: Conn, +ms: U32) -> R(F.Msg):
  match c:
    case Conn{sock, st}:
      IO.bind(Nat, Out(F.Msg), IO.now(), +now => recv.at(sock, st, ms, now))

def recv(c: Conn) -> R(F.Msg):
  match c:
    case Conn{sock, +st}:
      recv_for(Conn{sock, st}, o.recv(st.o(st)))

# Closing
# =======

def drop(c: Conn) -> IO(Unit):
  match c:
    case Conn{s, st}:
      Socket.close(s)

def CR() -> Type:
  IO(Result<&2, &2, Err, U32>)

def close.fail(c: Conn, e: Err) -> CR():
  IO.bind(Unit, Result<&2, &2, Err, U32>, drop(c), u => IO.pure(Result<&2, &2, Err, U32>, Fail{e}))

def close.done(c: Conn, +code: U32) -> CR():
  IO.bind(Unit, Result<&2, &2, Err, U32>, drop(c), u => IO.pure(Result<&2, &2, Err, U32>, Done{code}))

# after this end's close: the messages still coming are dropped until
# the server's close, which ends it
def close.next(g: Out(F.Msg), again: Conn -> CR()) -> CR():
  (c, r) = g
  match r:
    case Fail{e}:
      close.fail(c, e)
    case Done{m}:
      match m:
        case F.Closed{+code, reason}:
          close.done(c, code)
        case F.Text{t}:
          again(c)
        case F.Binary{b}:
          again(c)

def close.loop(k: Nat, c: Conn, +until: Nat) -> CR():
  match k:
    case 0n:
      close.fail(c, ETime{})
    case 1n+j:
      match c:
        case Conn{s, st}:
          IO.bind(Out(F.Msg), Result<&2, &2, Err, U32>, recv.go(big(), s, st, until),
            g => close.next(g, cc => close.loop(j, cc, until)))

def close.sent(g: Out(Unit), +now: Nat) -> CR():
  (c, r) = g
  match c:
    case Conn{s, +st}:
      match r:
        case Fail{e}:
          close.fail(Conn{s, st}, e)
        case Done{u}:
          close.loop(big(), Conn{s, st}, Nat.add(now, U32.to_nat(o.close(st.o(st)))))

def close.shut(c: Conn, +peer: U32, clean: Bool) -> CR():
  match clean:
    case True{}:
      close.done(c, peer)
    case False{}:
      close.fail(c, EClosed{})

def close.go(sock: Socket, +st: St, +code: U32, reason: String, +shut: U32, +now: Nat, open: Bool) -> CR():
  match open:
    case True{}:
      IO.bind(Out(Unit), Result<&2, &2, Err, U32>,
        send.frame(sock, st.mark(st, True{}, 0), 8, True{}, F.close.body(code, String.take(F.utf8.enc(reason), 123n))),
        g => close.sent(g, now))
    case False{}:
      close.shut(Conn{sock, st}, st.peer.of(st), U32.is_eq(shut, 1))

# The closing handshake: a close with the code and the reason (cut to
# the 123 bytes a close carries) goes out, what the server still sends
# is dropped until its close, the TCP connection is waited out, all
# under the options' close_ms, and the socket is released. The answer
# is the server's close code; a connection the server closed first
# answers its code at once, one that failed EClosed.
def close(c: Conn, +code: U32, reason: String) -> CR():
  match c:
    case Conn{sock, +st}:
      IO.bind(Nat, Result<&2, &2, Err, U32>, IO.now(), +now => close.go(sock, st, code, reason, st.shut(st), now, U32.is_zero(st.shut(st))))

# Opening
# =======

# the answer's head, and what came after it
type Hr is Data:
  Hr{head: Bytes(), rest: Bytes()}

def RC() -> Type:
  IO(Result<&1, &1, Err, Conn>)

def st.new(+o: Opts, proto: Bytes(), rest: Bytes()) -> St:
  st.feed(St{Ws.new(), Nil{}, F.Idle{}, o, proto, False{}, 0, 0}, rest)

def open.fail(s: Socket, e: Err) -> RC():
  IO.bind(Unit, Result<&1, &1, Err, Conn>, Socket.close(s), u => IO.pure(Result<&1, &1, Err, Conn>, Fail{e}))

def opened.judged(s: Socket, +o: Opts, rest: Bytes(), v: Result<&2, &2, H.Hw, Bytes()>) -> RC():
  match v:
    case Fail{w}:
      open.fail(s, EHand{w})
    case Done{proto}:
      IO.pure(Result<&1, &1, Err, Conn>, Done{Conn{s, st.new(o, proto, rest)}})

# the head judged: the connection, its first frames fed already
def opened(+key: Bytes(), +o: Opts, g: Socket & Result<&2, &2, Err, Hr>) -> RC():
  (s, r) = g
  match r:
    case Fail{e}:
      open.fail(s, e)
    case Done{hr}:
      match hr:
        case Hr{head, rest}:
          opened.judged(s, o, rest, H.answer(key, o.protocols(o), head))

# the answer's head, read up to its blank line under the deadline and
# the cap; what came after it is kept
def HR() -> Type:
  IO(Socket & Result<&2, &2, Err, Hr>)

def head.more(s: Socket, b2: Bytes(), over: Bool, again: Socket -> Bytes() -> HR()) -> HR():
  match over:
    case True{}:
      IO.pure(Socket & Result<&2, &2, Err, Hr>, (s, Fail{EHead{}}))
    case False{}:
      again(s, b2)

def head.cut(s: Socket, +b2: Bytes(), +cap: U32, at: Maybe<&2, Nat>, again: Socket -> Bytes() -> HR()) -> HR():
  match at:
    case Some{+i}:
      IO.pure(Socket & Result<&2, &2, Err, Hr>, (s, Done{Hr{String.take(b2, i), String.drop(b2, Nat.add(i, 4n))}}))
    case None{}:
      head.more(s, b2, Nat.is_lt(U32.to_nat(cap), Bytes.len(b2)), again)

def head.bytes(s: Socket, buf: Bytes(), +bs: Bytes(), +cap: U32, eof: Bool, again: Socket -> Bytes() -> HR()) -> HR():
  match eof:
    case True{}:
      IO.pure(Socket & Result<&2, &2, Err, Hr>, (s, Fail{EEof{}}))
    case False{}:
      +b2 = Bytes.append(buf, bs)
      head.cut(s, b2, cap, Bytes.find(b2, "\r\n\r\n"), again)

def head.got(buf: Bytes(), +cap: U32, g: Socket & Result<&1, &1, U32 & String, Maybe<&1, Bytes()>>,
  again: Socket -> Bytes() -> HR()) -> HR():
  (s, r) = g
  match r:
    case Fail{e}:
      (code, msg) = e
      IO.pure(Socket & Result<&2, &2, Err, Hr>, (s, Fail{ERecv{code}}))
    case Done{may}:
      match may:
        case None{}:
          IO.pure(Socket & Result<&2, &2, Err, Hr>, (s, Fail{ETime{}}))
        case Some{+bs}:
          head.bytes(s, buf, bs, cap, String.is_empty(bs), again)

def head.at(s: Socket, buf: Bytes(), +cap: U32, +until: Nat, +now: Nat, live: Bool, again: Socket -> Bytes() -> HR()) -> HR():
  match live:
    case False{}:
      IO.pure(Socket & Result<&2, &2, Err, Hr>, (s, Fail{ETime{}}))
    case True{}:
      IO.bind(Socket & Result<&1, &1, U32 & String, Maybe<&1, Bytes()>>, Socket & Result<&2, &2, Err, Hr>,
        TCP.poll_buf(s, 65536, left(until, now)), g => head.got(buf, cap, g, again))

def head.go(k: Nat, s: Socket, buf: Bytes(), +cap: U32, +until: Nat) -> HR():
  match k:
    case 0n:
      IO.pure(Socket & Result<&2, &2, Err, Hr>, (s, Fail{ETime{}}))
    case 1n+j:
      IO.bind(Nat, Socket & Result<&2, &2, Err, Hr>, IO.now(),
        +now => head.at(s, buf, cap, until, now, Nat.is_lt(now, until), s2 => b2 => head.go(j, s2, b2, cap, until)))

def asked(+key: Bytes(), +o: Opts, +until: Nat, g: Socket & Result<&1, &1, U32 & String, Unit>) -> RC():
  (s, r) = g
  match r:
    case Fail{e}:
      (code, msg) = e
      open.fail(s, ESend{code})
    case Done{u}:
      IO.bind(Socket & Result<&2, &2, Err, Hr>, Result<&1, &1, Err, Conn>,
        head.go(big(), s, "", o.head(o), until), h => opened(key, o, h))

# the key: sixteen bytes from the host's entropy, in base64
def RK() -> Type:
  IO(Result<&1, &1, U32 & String, List<&2, U32>>)

def rand.more(r: Result<&1, &1, U32 & String, U32>, acc: List<&2, U32>, again: List<&2, U32> -> RK()) -> RK():
  match r:
    case Fail{e}:
      IO.pure(Result<&1, &1, U32 & String, List<&2, U32>>, Fail{e})
    case Done{+w}:
      again(List.append(&2, U32, Sha1.unword(w), acc))

def rand(k: Nat, acc: List<&2, U32>) -> RK():
  match k:
    case 0n:
      IO.pure(Result<&1, &1, U32 & String, List<&2, U32>>, Done{acc})
    case 1n+j:
      IO.bind(Result<&1, &1, U32 & String, U32>, Result<&1, &1, U32 & String, List<&2, U32>>, IO.random_u32(),
        r => rand.more(r, acc, xs => rand(j, xs)))

def keyed(+u: H.Url, +o: Opts, +until: Nat, s: Socket, r: Result<&1, &1, U32 & String, List<&2, U32>>) -> RC():
  match r:
    case Fail{e}:
      (code, msg) = e
      open.fail(s, ERand{code})
    case Done{bs}:
      +key = Bytes.from_list(B64.enc(bs))
      IO.bind(Socket & Result<&1, &1, U32 & String, Unit>, Result<&1, &1, Err, Conn>,
        TCP.send_buf_poll(s, H.request(u, key, o.protocols(o)), o.connect(o)), g => asked(key, o, until, g))

def dialed(+u: H.Url, +o: Opts, +until: Nat, r: Result<&1, &1, U32 & String, Socket>) -> RC():
  match r:
    case Fail{e}:
      (code, msg) = e
      IO.pure(Result<&1, &1, Err, Conn>, Fail{EConnect{code}})
    case Done{s}:
      IO.bind(Result<&1, &1, U32 & String, List<&2, U32>>, Result<&1, &1, Err, Conn>, rand(4n, Nil{}),
        k => keyed(u, o, until, s, k))

def tls.strip(r: Result<&1, &1, U32 & String, Socket & String>) -> IO(Result<&1, &1, U32 & String, Socket>):
  match r:
    case Done{sp}:
      (s, proto) = sp
      IO.pure(Result<&1, &1, U32 & String, Socket>, Done{s})
    case Fail{e}:
      IO.pure(Result<&1, &1, U32 & String, Socket>, Fail{e})

# the connection, plain or TLS (SNI and the name checked are the URL's
# host; ALPN offers http/1.1, the protocol a WebSocket opens on)
def dial(u: H.Url, +o: Opts, addr: String) -> IO(Result<&1, &1, U32 & String, Socket>):
  match u:
    case H.Url{tls, host, +port, path}:
      match tls:
        case True{}:
          IO.bind(Result<&1, &1, U32 & String, Socket & String>, Result<&1, &1, U32 & String, Socket>,
            TLS.connect(addr, port, host, "http/1.1", o.ca(o), o.connect(o)), tls.strip)
        case False{}:
          TCP.connect_poll(addr, port, o.connect(o))

def resolved(+u: H.Url, +o: Opts, +until: Nat, r: Result<&1, &1, U32 & String, String>) -> RC():
  match r:
    case Fail{e}:
      (code, msg) = e
      IO.pure(Result<&1, &1, Err, Conn>, Fail{EDns{code}})
    case Done{addr}:
      IO.bind(Result<&1, &1, U32 & String, Socket>, Result<&1, &1, Err, Conn>, dial(u, o, addr),
        d => dialed(u, o, until, d))

def url.host(u: H.Url) -> String:
  match u:
    case H.Url{tls, host, port, path}:
      host

def connect.at(+u: H.Url, +o: Opts, +now: Nat) -> RC():
  IO.bind(Result<&1, &1, U32 & String, String>, Result<&1, &1, Err, Conn>, DNS.resolve(url.host(u)),
    r => resolved(u, o, Nat.add(now, U32.to_nat(o.connect(o))), r))

def connect.url(+o: Opts, may: Maybe<&2, H.Url>) -> RC():
  match may:
    case None{}:
      IO.pure(Result<&1, &1, Err, Conn>, Fail{EUrl{}})
    case Some{+u}:
      IO.bind(Nat, Result<&1, &1, Err, Conn>, IO.now(), +now => connect.at(u, o, now))

# Open a WebSocket to a ws:// or wss:// URL: the connection, or why not.
def connect(url: String, +o: Opts) -> RC():
  connect.url(o, H.url.parse(url))
