# bend-proxy: a reverse proxy that cannot be desynchronised.
#
#   bend demos/io_proxy/main.bend -o proxyd
#   ./proxyd --port 8080 --upstream 127.0.0.1:9000
#   ./proxyd --port 8443 --tls-cert cert.pem --tls-key key.pem \
#     --upstream example.org:443 --upstream-tls --upstream-sni example.org --ca ca.pem
#
# A client's bytes are framed by the HTTP engine's reader, held to RFC
# 9112 by frame_sim, and what goes upstream is a request rebuilt from
# what was framed (core.bend): the upstream reads exactly the requests
# the proxy read, never a boundary of its own. The response comes back
# through wire/client.bend's exchange, over a pooled keep-alive
# connection (wire/pool.bend), and goes back rebuilt the same way.
#
# Flags:
#   --port N              listen here (8080)
#   --upstream H:P        the upstream (a dotted address or a name)
#   --upstream-tls        speak TLS to it; --upstream-sni NAME the name
#                         to send and verify (H by default); --ca FILE
#                         trust only the certificates in FILE
#   --host NAME           send this Host upstream (the client's by default)
#   --idle-ms N           a client's idle time (5000)
#   --connect-ms N        a connect's deadline (3000)
#   --upstream-ms N       a response's deadline (30000)
#   --pool N              idle upstream connections kept (64)
#   --head-cap N          the most bytes of a request head (65536)
#   --max-conns N         clients at once (4096); --grace-ms N on SIGTERM
#   --shared              share the port with other copies (and --workers N,
#                         the runtime's, forks them)
#   --tls-cert F --tls-key F   serve TLS
import Base
import ../../wire/loop.bend as L
import ../../wire/effects.bend as Fx
import ../../wire/client.bend as C
import ../../wire/pool.bend as P
import ../../wire/http1/resp.bend as R
import ../io_http_engine/main.bend as Eng
import ./core.bend as X

# The peer's address, for X-Forwarded-For
def Peer.addr(s: Socket) -> IO(Socket & String):
  import "./peer.c"
  import "./peer.js"

# Configuration
# =============

# the flags as given: each --name with its value ("1" for a switch);
# a switch stands alone, any other flag takes the argument after it
type KV is Data:
  KV{k: String, v: String}

def switch(+a: String) -> Bool:
  String.eq(a, "--upstream-tls") || String.eq(a, "--shared")

def pairs.pend(+pend: String, +a: String) -> String:
  Bool.pick(String, String.is_empty(pend) && Bool.not(switch(a)), a, "")

def pairs.at(free: Bool, sw: Bool, +pend: String, +a: String, acc: List<&2, KV>) -> List<&2, KV>:
  match free sw:
    case True{} True{}:
      Con{KV{a, "1"}, acc}
    case True{} False{}:
      acc
    case False{} _:
      Con{KV{pend, a}, acc}

def pairs.acc(+pend: String, +a: String, acc: List<&2, KV>) -> List<&2, KV>:
  pairs.at(String.is_empty(pend), switch(a), pend, a, acc)

def pairs(xs: List<String>, +pend: String, acc: List<&2, KV>) -> List<&2, KV>:
  match xs:
    case Nil{}:
      acc
    case Con{+a, t}:
      pairs(t, pairs.pend(pend, a), pairs.acc(pend, a, acc))

# a flag's value, or d
def get(kvs: List<&2, KV>, +k: String, d: String) -> String:
  match kvs:
    case Nil{}:
      d
    case Con{kv, t}:
      match kv:
        case KV{a, b}:
          Bool.pick(String, String.eq(a, k), b, get(t, k, d))

def num(+s: String, d: U32) -> U32:
  Maybe.default(&2, U32, U32.read(s), d)

# What serving needs: the upstream -- its address, port, TLS and the
# name to verify, a CA file ("" for the system's) -- the Host to send
# ("" keeps the client's), the times (a client's idle, a connect's, a
# response's), the head's cap, the connection limit and the grace time,
# the scheme clients come in on, this hop's Via, and the pool of idle
# upstream connections, in a channel of one that serves as its lock.
type Srv is Data:
  Srv{addr: String, port: U32, tls: Bool, sni: String, ca: String, host: Bytes(), idle: U32, cms: U32,
    ums: U32, head: U32, conns: U32, grace: U32, proto: Bytes(), via: Bytes(), pool: Chan(P.Pool<&1, Socket>)}

def srv.idle(s: Srv) -> U32:
  match s:
    case Srv{addr, port, tls, sni, ca, host, idle, cms, ums, head, conns, grace, proto, via, pool}:
      idle

def srv.conns(s: Srv) -> U32:
  match s:
    case Srv{addr, port, tls, sni, ca, host, idle, cms, ums, head, conns, grace, proto, via, pool}:
      conns

def srv.grace(s: Srv) -> U32:
  match s:
    case Srv{addr, port, tls, sni, ca, host, idle, cms, ums, head, conns, grace, proto, via, pool}:
      grace

def srv.head(s: Srv) -> U32:
  match s:
    case Srv{addr, port, tls, sni, ca, host, idle, cms, ums, head, conns, grace, proto, via, pool}:
      head

def srv.pool(s: Srv) -> Chan(P.Pool<&1, Socket>):
  match s:
    case Srv{addr, port, tls, sni, ca, host, idle, cms, ums, head, conns, grace, proto, via, pool}:
      pool

def srv.via(s: Srv) -> Bytes():
  match s:
    case Srv{addr, port, tls, sni, ca, host, idle, cms, ums, head, conns, grace, proto, via, pool}:
      via

def srv.fwd(s: Srv, ip: Bytes()) -> X.Fwd:
  match s:
    case Srv{addr, port, tls, sni, ca, host, idle, cms, ums, head, conns, grace, proto, via, pool}:
      X.Fwd{host, proto, ip, via}

# The upstream
# ============

# The exchange reads through a socket that keeps what it read: the
# response's head is read again from those bytes (core.bend's rsp.of).
type Rec is Type:
  Rec{s: Socket, got: Bytes()}

def rec.got(got: Bytes(), g: L.Got(Socket)) -> L.Got(Rec):
  (s, r) = g
  match r:
    case Done{m}:
      match m:
        case Some{+bs}:
          (Rec{s, Bytes.append(got, bs)}, Done{Some{bs}})
        case None{}:
          (Rec{s, got}, Done{None{}})
    case Fail{e}:
      (Rec{s, got}, Fail{e})

def rec.rx(r: Rec, max: U32, ms: Nat) -> IO(L.Got(Rec)):
  match r:
    case Rec{s, got}:
      IO.bind(L.Got(Socket), L.Got(Rec), TCP.poll_buf(s, max, U32.from_nat(ms)),
        g => IO.pure(L.Got(Rec), rec.got(got, g)))

def rec.put(got: Bytes(), m: L.Put(Socket)) -> L.Put(Rec):
  (s, r) = m
  (Rec{s, got}, r)

def rec.tx(r: Rec, bs: Bytes(), ms: U32) -> IO(L.Put(Rec)):
  match r:
    case Rec{s, got}:
      IO.bind(L.Put(Socket), L.Put(Rec), TCP.send_buf_poll(s, bs, ms),
        m => IO.pure(L.Put(Rec), rec.put(got, m)))

def rec.clk(r: Rec) -> IO(Rec & Nat):
  IO.bind(Nat, Rec & Nat, IO.now(), t => IO.pure(Rec & Nat, (r, t)))

# the most body a response may bring back, buffered
def body.cap() -> U32:
  67108864

def budget(+srv: Srv) -> C.Budget:
  match srv:
    case Srv{addr, port, tls, sni, ca, host, idle, cms, +ums, head, conns, grace, proto, via, pool}:
      C.Budget{65536, ums, ums}

# What the upstream answered: a response to send back, a failure the
# client hears as 502 or 504, or a pooled connection gone stale before
# anything came back on it (tried again once, on a new one).
type Ans is Data:
  AOk{r: X.Rsp}
  AErr{status: Bytes()}
  AStale{}

def why.status(w: C.Why) -> Bytes():
  match w:
    case C.CTime{}:
      "504 Gateway Timeout"
    case _:
      "502 Bad Gateway"

# a failure on a pooled connection with nothing read is the connection's
# fault, not the request's
def stale(w: C.Why) -> Bool:
  match w:
    case C.CSend{c}:
      True{}
    case C.CRecv{c}:
      True{}
    case C.CEof{}:
      True{}
    case _:
      False{}

# the pool, taken from its channel and put back
def pool.put(+ch: Chan(P.Pool<&1, Socket>), pm: P.Pool<&1, Socket> & Maybe<&1, P.Slot<&1, Socket>>) ->
  IO(Maybe<&1, P.Slot<&1, Socket>>):
  (pool, may) = pm
  do IO<Maybe<&1, P.Slot<&1, Socket>>>:
    ok : Bool <- Chan.send(P.Pool<&1, Socket>, ch, pool)
    return may

def pool.took(+ch: Chan(P.Pool<&1, Socket>), +now: Nat, m: Maybe<&1, P.Pool<&1, Socket>>) ->
  IO(Maybe<&1, P.Slot<&1, Socket>>):
  match m:
    case Some{pool}:
      IO.bind(P.Pool<&1, Socket> & Maybe<&1, P.Slot<&1, Socket>>, Maybe<&1, P.Slot<&1, Socket>>,
        P.take.io(pool, now), pm => pool.put(ch, pm))
    case None{}:
      IO.pure(Maybe<&1, P.Slot<&1, Socket>>, None{})

def pool.take(+ch: Chan(P.Pool<&1, Socket>), +now: Nat) -> IO(Maybe<&1, P.Slot<&1, Socket>>):
  IO.bind(Maybe<&1, P.Pool<&1, Socket>>, Maybe<&1, P.Slot<&1, Socket>>, Chan.recv(P.Pool<&1, Socket>, ch),
    m => pool.took(ch, now, m))

def pool.gave(+ch: Chan(P.Pool<&1, Socket>), pool: P.Pool<&1, Socket>) -> IO(Unit):
  do IO<Unit>:
    ok : Bool <- Chan.send(P.Pool<&1, Socket>, ch, pool)
    return Unit{}

def pool.back(+ch: Chan(P.Pool<&1, Socket>), s: Socket, +born: Nat, +now: Nat, ok: Bool,
  m: Maybe<&1, P.Pool<&1, Socket>>) -> IO(Unit):
  match m:
    case Some{pool}:
      IO.bind(P.Pool<&1, Socket>, Unit, P.give.io(pool, s, born, now, ok), p2 => pool.gave(ch, p2))
    case None{}:
      Socket.close(s)

def pool.give(+ch: Chan(P.Pool<&1, Socket>), s: Socket, +born: Nat, ok: Bool) -> IO(Unit):
  do IO<Unit>:
    now : Nat <- IO.now()
    m : Maybe<&1, P.Pool<&1, Socket>> <- Chan.recv(P.Pool<&1, Socket>, ch)
    pool.back(ch, s, born, now, ok, m)

# a new connection to the upstream, under the connect deadline
def dial.tls(r: Result<&1, &1, U32 & String, Socket & String>) -> Result<&1, &1, U32 & String, Socket>:
  match r:
    case Done{sp}:
      (s, proto) = sp
      Done{s}
    case Fail{e}:
      Fail{e}

def dial(+srv: Srv) -> IO(Result<&1, &1, U32 & String, Socket>):
  match srv:
    case Srv{addr, +port, tls, sni, ca, host, idle, +cms, ums, head, conns, grace, proto, via, pool}:
      match tls:
        case True{}:
          IO.bind(Result<&1, &1, U32 & String, Socket & String>, Result<&1, &1, U32 & String, Socket>,
            TLS.connect(addr, port, sni, "http/1.1", ca, cms),
            r => IO.pure(Result<&1, &1, U32 & String, Socket>, dial.tls(r)))
        case False{}:
          TCP.connect_poll(addr, port, cms)

def dial.status(+code: U32) -> Bytes():
  Bool.pick(Bytes(), U32.is_eq(code, 110), "504 Gateway Timeout", "502 Bad Gateway")

def ex.rsp(m: Maybe<&2, X.Rsp>) -> Ans:
  match m:
    case Some{r}:
      AOk{r}
    case None{}:
      AErr{"502 Bad Gateway"}

def ex.fail(again: Bool, w: C.Why) -> Ans:
  match again:
    case True{}:
      AStale{}
    case False{}:
      AErr{why.status(w)}

# One exchange on a connection made at born; pooled says it came from
# the pool. A response goes back to the client rebuilt; the connection
# goes back to the pool if the exchange left it fit.
def ex.got(+srv: Srv, +head: Bool, +born: Nat, s: Socket, +got: Bytes(), g: C.Got) -> IO(Ans):
  match g:
    case C.Got{i, resp, extra, reuse}:
      match resp:
        case R.Resp{+code, v10, close, body}:
          do IO<Ans>:
            pool.give(srv.pool(srv), s, born, reuse)
            return ex.rsp(X.rsp.of(srv.via(srv), head, List.length(&2, U32, i), code, got, body))

def ex.res(+srv: Srv, +head: Bool, +born: Nat, pooled: Bool, s: Socket, +got: Bytes(),
  res: Result<&2, &2, C.Why, C.Got>) -> IO(Ans):
  match res:
    case Done{g}:
      ex.got(srv, head, born, s, got, g)
    case Fail{+w}:
      do IO<Ans>:
        Socket.close(s)
        return ex.fail(pooled && stale(w) && String.is_empty(got), w)

def ex.done(+srv: Srv, +head: Bool, +born: Nat, pooled: Bool, out: C.Out(Rec)) -> IO(Ans):
  (r, res) = out
  match r:
    case Rec{s, got}:
      ex.res(srv, head, born, pooled, s, got, res)

def ex.go(+srv: Srv, +head: Bool, req: Bytes(), s: Socket, +born: Nat, pooled: Bool) -> IO(Ans):
  IO.bind(C.Out(Rec), Ans,
    C.exchange(~(A => IO(A)), ~IO.pure, ~IO.bind, ~Rec, ~rec.rx, ~rec.tx, ~rec.clk,
      R.ask.new(head, body.cap()), budget(srv), req, Rec{s, ""}),
    out => ex.done(srv, head, born, pooled, out))

def ex.dialed(+srv: Srv, +head: Bool, req: Bytes(), +born: Nat, r: Result<&1, &1, U32 & String, Socket>) ->
  IO(Ans):
  match r:
    case Done{s}:
      ex.go(srv, head, req, s, born, False{})
    case Fail{e}:
      match e:
        case (+code, msg):
          IO.pure(Ans, AErr{dial.status(code)})

# on a new connection
def ex.fresh(+srv: Srv, +head: Bool, req: Bytes()) -> IO(Ans):
  do IO<Ans>:
    born : Nat <- IO.now()
    r : Result<&1, &1, U32 & String, Socket> <- dial(srv)
    ex.dialed(srv, head, req, born, r)

# a stale pooled connection is tried again once, on a new one, when the
# request may be sent twice (RFC 9110 9.2.2: an idempotent method)
def ex.again(+srv: Srv, +head: Bool, idem: Bool, +req: Bytes(), a: Ans) -> IO(Ans):
  match idem a:
    case True{} AStale{}:
      ex.fresh(srv, head, req)
    case False{} AStale{}:
      IO.pure(Ans, AErr{"502 Bad Gateway"})
    case _ AOk{r}:
      IO.pure(Ans, AOk{r})
    case _ AErr{st}:
      IO.pure(Ans, AErr{st})

def ex.slot(+srv: Srv, +head: Bool, idem: Bool, +req: Bytes(), m: Maybe<&1, P.Slot<&1, Socket>>) -> IO(Ans):
  match m:
    case Some{sl}:
      match sl:
        case P.Slot{s, +born, last}:
          IO.bind(Ans, Ans, ex.go(srv, head, req, s, born, True{}), a => ex.again(srv, head, idem, req, a))
    case None{}:
      IO.bind(Ans, Ans, ex.fresh(srv, head, req), a => ex.again(srv, head, False{}, req, a))

# a request upstream: on a pooled connection if one is fit, else a new one
def upstream(+srv: Srv, +head: Bool, idem: Bool, +req: Bytes()) -> IO(Ans):
  do IO<Ans>:
    now : Nat <- IO.now()
    m : Maybe<&1, P.Slot<&1, Socket>> <- pool.take(srv.pool(srv), now)
    ex.slot(srv, head, idem, req, m)

# RFC 9110 9.2.2
def idempotent(+m: Bytes()) -> Bool:
  Eng.bytes.eq(m, "GET") || Eng.bytes.eq(m, "HEAD") || Eng.bytes.eq(m, "PUT") || Eng.bytes.eq(m, "DELETE")
    || Eng.bytes.eq(m, "OPTIONS") || Eng.bytes.eq(m, "TRACE")

# The client
# ==========

def send.ok(m: L.Put(Socket)) -> Socket & Bool:
  (s, r) = m
  match r:
    case Done{u}:
      (s, True{})
    case Fail{e}:
      (s, False{})

def send(cs: Socket, bs: Bytes(), +ms: U32) -> IO(Socket & Bool):
  IO.bind(L.Put(Socket), Socket & Bool, TCP.send_buf_poll(cs, bs, ms), m => IO.pure(Socket & Bool, send.ok(m)))

# a reply of the proxy's own, and the connection closes
def refuse(+srv: Srv, +head: Bool, cs: Socket, +status: Bytes()) -> IO(Socket):
  IO.bind(Socket & Bool, Socket, send(cs, X.own.reply.at(head, status, Bytes.append(status, "\n")), srv.idle(srv)),
    sb => IO.pure(Socket, Pair.fst(Socket, Bool, sb)))

# after a response went back: on to the next request, unless the
# connection closes or the send failed
def sent(sb: Socket & Bool, closing: Bool, more: Socket -> IO(Socket)) -> IO(Socket):
  (s, ok) = sb
  match ok closing:
    case True{} False{}:
      more(s)
    case _ _:
      IO.pure(Socket, s)

def answer(+srv: Srv, +head: Bool, +closing: Bool, v10: Bool, a: Ans, cs: Socket, more: Socket -> IO(Socket)) ->
  IO(Socket):
  match a:
    case AOk{r}:
      IO.bind(Socket & Bool, Socket, send(cs, X.reply(Some{r}, head, closing, v10), srv.idle(srv)),
        sb => sent(sb, closing, more))
    case AErr{st}:
      refuse(srv, head, cs, st)
    case AStale{}:
      refuse(srv, head, cs, "502 Bad Gateway")

def serve.msg(+srv: Srv, mm: Maybe<&2, X.Msg>, +v10: Bool, +closing: Bool, cs: Socket, more: Socket -> IO(Socket)) ->
  IO(Socket):
  match mm:
    case Some{+msg}:
      match msg:
        case X.Msg{+hm, target, host, fs, body, framed}:
          +hd = Eng.bytes.eq(hm, "HEAD")
          IO.bind(Ans, Socket, upstream(srv, hd, idempotent(hm), X.ser(msg)),
            a => answer(srv, hd, closing, v10, a, cs, more))
    case None{}:
      refuse(srv, False{}, cs, "400 Bad Request")

def hd.v10(h: Eng.Hd) -> Bool:
  match h:
    case Eng.Hd{meth, v10, fs, cn}:
      v10

# one request: forwarded (core.bend's fwd of what the reader read),
# answered, and then more
def serve(+srv: Srv, +ip: Bytes(), +r: Eng.Req, cs: Socket, more: Socket -> IO(Socket)) -> IO(Socket):
  serve.msg(srv, X.fwd(srv.fwd(srv, ip), r), hd.v10(Eng.req.hd(r)), Eng.req.close(r) || Eng.req.ws(r), cs, more)

# a request whose head is whole and whose body is coming, asking to be
# told to send it (RFC 9110 10.1.1): told once
def expects.low(xs: List<&2, Bytes()>) -> List<&2, Bytes()>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{Eng.lows(X.trim(x)), expects.low(t)}

def expects(+p: Eng.P) -> Bool:
  X.in.names("100-continue", expects.low(X.values("expect", Eng.p.fields(p))))

def cont.send(on: Bool, cs: Socket, +ms: U32) -> IO(Socket):
  match on:
    case True{}:
      IO.bind(Socket & Bool, Socket, send(cs, "HTTP/1.1 100 Continue\r\n\r\n", ms),
        sb => IO.pure(Socket, Pair.fst(Socket, Bool, sb)))
    case False{}:
      IO.pure(Socket, cs)

def wait.at(+srv: Srv, big: Bool, body: Bool, cont: Bool, +p: Eng.P, +n: Nat, cs: Socket,
  again: Socket -> X.Scan -> Bool -> IO(Socket)) -> IO(Socket):
  match big body cont:
    case True{} _ _:
      refuse(srv, False{}, cs, "431 Request Header Fields Too Large")
    case False{} True{} False{}:
      IO.bind(Socket, Socket, cont.send(expects(p), cs, srv.idle(srv)), s2 => again(s2, X.Scan{p, n}, True{}))
    case False{} _ _:
      again(cs, X.Scan{p, n}, cont)

# waiting for more: a head past its cap is refused with 431
def wait(+srv: Srv, sc: X.Scan, cont: Bool, cs: Socket, again: Socket -> X.Scan -> Bool -> IO(Socket)) -> IO(Socket):
  match sc:
    case X.Scan{+p, +n}:
      wait.at(srv, Eng.p.head(p) && U32.is_lt(srv.head(srv), U32.from_nat(n)), Eng.p.body(p), cont, p, n, cs, again)

def tail(+srv: Srv, t: X.Tail, cont: Bool, cs: Socket, again: Socket -> X.Scan -> Bool -> IO(Socket)) -> IO(Socket):
  match t:
    case X.TWait{sc}:
      wait(srv, sc, cont, cs, again)
    case X.TBad{}:
      refuse(srv, False{}, cs, "400 Bad Request")
    case X.TUp{}:
      IO.pure(Socket, cs)

# the requests a read completed, one after another, and then its tail;
# a request completed resets the Expect check
def took(+srv: Srv, +ip: Bytes(), ts: List<&2, Eng.Req>, t: X.Tail, cont: Bool, cs: Socket,
  again: Socket -> X.Scan -> Bool -> IO(Socket)) -> IO(Socket):
  match ts:
    case Nil{}:
      tail(srv, t, cont, cs, again)
    case Con{x, rest}:
      serve(srv, ip, x, cs, s2 => took(srv, ip, rest, t, False{}, s2, again))

def scanned(+srv: Srv, +ip: Bytes(), sd: X.Scanned, cont: Bool, cs: Socket,
  again: Socket -> X.Scan -> Bool -> IO(Socket)) -> IO(Socket):
  match sd:
    case X.Scanned{ts, t}:
      took(srv, ip, ts, t, cont, cs, again)

def bytes.in(+srv: Srv, +ip: Bytes(), sc: X.Scan, cont: Bool, cs: Socket, fin: Bool, +bs: Bytes(),
  again: Socket -> X.Scan -> Bool -> IO(Socket)) -> IO(Socket):
  match fin:
    case True{}:
      IO.pure(Socket, cs)
    case False{}:
      scanned(srv, ip, X.scan(bs, sc), cont, cs, again)

# a read: a failure, the idle time out, or the peer's FIN end the
# connection; bytes go through the scan
def got(+srv: Srv, +ip: Bytes(), sc: X.Scan, cont: Bool, g: L.Got(Socket),
  again: Socket -> X.Scan -> Bool -> IO(Socket)) -> IO(Socket):
  (cs, r) = g
  match r:
    case Fail{e}:
      IO.pure(Socket, cs)
    case Done{m}:
      match m:
        case None{}:
          IO.pure(Socket, cs)
        case Some{+bs}:
          bytes.in(srv, ip, sc, cont, cs, String.is_empty(bs), bs, again)

def read(+srv: Srv, +ip: Bytes(), k: Nat, sc: X.Scan, cont: Bool, cs: Socket) -> IO(Socket):
  match k:
    case 0n:
      IO.pure(Socket, cs)
    case 1n+j:
      IO.bind(L.Got(Socket), Socket, TCP.poll_buf(cs, 65536, srv.idle(srv)),
        g => got(srv, ip, sc, cont, g, s2 => sc2 => c2 => read(srv, ip, j, sc2, c2, s2)))

def go.at(+srv: Srv, sa: Socket & String) -> IO(Socket):
  (cs, ip) = sa
  read(srv, ip, L.conn.fuel(), X.scan.new(), False{}, cs)

# one client connection
def go(+srv: Srv, cs: Socket) -> IO(Socket):
  IO.bind(Socket & String, Socket, Peer.addr(cs), sa => go.at(srv, sa))

# Starting
# ========

def listen.at(plain: Bool, shared: Bool, +port: U32, +cert: String, +key: String) ->
  IO(Result<&1, &1, U32 & String, Listener>):
  match plain shared:
    case False{} _:
      TLS.listen(port, cert, key)
    case True{} True{}:
      TCP.listen_shared(port)
    case True{} False{}:
      TCP.listen(port)

def listen(+port: U32, shared: Bool, +cert: String, +key: String) -> IO(Result<&1, &1, U32 & String, Listener>):
  listen.at(String.is_empty(cert), shared, port, cert, key)

def up.host(+up: String) -> String:
  String.take(up, Maybe.default(&2, Nat, String.find_last(up, ":"), String.length(up)))

def up.port.at(m: Maybe<&2, Nat>, +up: String, +tls: Bool) -> U32:
  match m:
    case Some{i}:
      num(String.drop(up, 1n+i), Bool.pick(U32, tls, 443, 80))
    case None{}:
      Bool.pick(U32, tls, 443, 80)

def up.port(+up: String, +tls: Bool) -> U32:
  up.port.at(String.find_last(up, ":"), up, tls)

def run(+kv: List<&2, KV>, addr: String, ch: Chan(P.Pool<&1, Socket>)) -> IO(Unit):
  +up = get(kv, "--upstream", "")
  +tls = String.eq(get(kv, "--upstream-tls", ""), "1")
  +cert = get(kv, "--tls-cert", "")
  +port = num(get(kv, "--port", "8080"), 8080)
  +srv : Srv = Srv{addr, up.port(up, tls), tls, get(kv, "--upstream-sni", up.host(up)), get(kv, "--ca", ""),
    get(kv, "--host", ""), num(get(kv, "--idle-ms", ""), 5000), num(get(kv, "--connect-ms", ""), 3000),
    num(get(kv, "--upstream-ms", ""), 30000), num(get(kv, "--head-cap", ""), 65536),
    num(get(kv, "--max-conns", ""), 4096), num(get(kv, "--grace-ms", ""), 5000),
    Bool.pick(Bytes(), String.is_empty(cert), "http", "https"), "1.1 bend-proxy", ch}
  do IO<Unit>:
    l : Listener <- IO.try(Listener, listen(port, String.eq(get(kv, "--shared", ""), "1"), cert,
      get(kv, "--tls-key", "")))
    IO.print("bend-proxy on " ++ Bool.pick(String, String.is_empty(cert), "http", "https") ++ "://127.0.0.1:"
      ++ U32.show(port) ++ " to " ++ up)
    Fx.run(~Srv, ~go, ~srv.grace, ~srv.conns, "bend-proxy", srv, l)

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    +kv : List<&2, KV> = pairs(xs, "", Nil{})
    +up : String = get(kv, "--upstream", "")
    addr : String <- IO.try(String, DNS.resolve(up.host(up)))
    +ch : Chan(P.Pool<&1, Socket>) <- Chan.new(P.Pool<&1, Socket>, 1)
    ok : Bool <- Chan.send(P.Pool<&1, Socket>, ch,
      P.pool.new(&1, Socket, U32.to_nat(num(get(kv, "--pool", ""), 64)), 60000n, 4000n))
    run(kv, addr, ch)
