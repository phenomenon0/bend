# bend-h2: an HTTP/2 server (RFC 9113, HPACK RFC 7541) on bend-wire.
#
# Why a demo of its own and not a mode of the HTTP/1 engine: wire/'s
# loop takes one protocol's hooks per connection, and an HTTP/2
# connection has nothing of an HTTP/1 one to share -- not the reader
# (frames, not a head grammar), not the state between reads (streams,
# windows, a compression table), not the replies (frames on streams).
# What the two do share is what a request means, and that is taken
# from the engine as it is: its configuration and command line, its
# route table and router, its target rules. A route answers the same
# on both.
#
# The connection is conn.bend's, a pure machine from a read's frames to
# the bytes they earn; what is this file's is the planner that runs it
# on each read, answers the requests it completed through the engine's
# routes, and hands the loop what to write.
#
#   bend demos/io_http2/main.bend -o h2d && ./h2d --port 8443
#   curl --http2-prior-knowledge http://127.0.0.1:8443/health
import Base
import ../../wire/loop.bend as L
import ../../wire/effects.bend as Fx
import ../io_http_engine/main.bend as Eng
import ./huff.bend as H
import ./hpack.bend as K
import ./conn.bend as C

# what every connection shares: the engine's server (configuration and
# route table) and the Huffman tree, built once
type Srv is Data:
  Srv{eng: Eng.Srv, root: H.Ht}

def srv.new(+c: Eng.Cfg) -> Srv:
  Srv{Eng.srv.new(c), H.tree()}

def srv.eng(s: Srv) -> Eng.Srv:
  match s:
    case Srv{e, r}:
      e

def srv.root(s: Srv) -> H.Ht:
  match s:
    case Srv{e, r}:
      r

def srv.idle(s: Srv) -> U32:
  Eng.srv.idle(srv.eng(s))

def srv.head(s: Srv) -> U32:
  Eng.srv.head(srv.eng(s))

def srv.grace(s: Srv) -> U32:
  Eng.srv.grace(srv.eng(s))

def srv.conns(s: Srv) -> U32:
  Eng.srv.conns(srv.eng(s))

# A response: a status, a type, a body.
type Rsp is Data:
  Rsp{status: Bytes(), ct: Bytes(), body: Bytes()}

# What a route answers, as the HTTP/1 engine's routes do. The event
# stream and the WebSocket are HTTP/1 upgrades and are not served here,
# nor (yet) files: a file is streamed by the loop behind its head, and
# HTTP/2 wants every block of it framed.
def act(a: Eng.Act, body: Bytes()) -> Rsp:
  match a:
    case Eng.Health{}:
      Rsp{"200", "application/json", "{\"ok\":true}"}
    case Eng.Root{}:
      Rsp{"200", "text/plain", "bend-http\n"}
    case Eng.Echo{}:
      Rsp{"200", "application/octet-stream", body}
    case Eng.Events{}:
      Rsp{"501", "text/plain", "not over http/2\n"}
    case Eng.Live{}:
      Rsp{"501", "text/plain", "not over http/2\n"}
    case Eng.Files{}:
      Rsp{"501", "text/plain", "not over http/2\n"}

def found(m: Maybe<&2, Eng.Act>, body: Bytes()) -> Rsp:
  match m:
    case None{}:
      Rsp{"404", "text/plain", "no route\n"}
    case Some{a}:
      act(a, body)

# GET, HEAD and POST are served; a target past the engine's cap is a
# 414, as it is there
def serve.go(+srv: Srv, +path: Bytes(), body: Bytes(), meth: Bool, far: Bool) -> Rsp:
  match meth far:
    case False{} _:
      Rsp{"405", "text/plain", "no method\n"}
    case True{} True{}:
      Rsp{"414", "text/plain", "target too long\n"}
    case True{} False{}:
      found(Eng.route(Eng.srv.table(srv.eng(srv)), Eng.path.of(path)), body)

def serve(+srv: Srv, +meth: Bytes(), +path: Bytes(), body: Bytes()) -> Rsp:
  serve.go(srv, path, body,
    C.beq(meth, "GET") || C.beq(meth, "HEAD") || C.beq(meth, "POST"),
    Eng.long(Eng.target.cap(), path))

def answer.rsp(+c: C.Cn, w: Bytes(), +sid: U32, r: Rsp, +head: Bool) -> C.CW:
  match r:
    case Rsp{status, ct, body}:
      C.answer(c, w, sid, status, ct, body, head)

# every request the read completed answered, oldest first
def answer.all(+srv: Srv, rs: List<&2, C.Req>, cw: C.CW) -> C.CW:
  match rs:
    case Nil{}:
      cw
    case Con{r, t}:
      match r cw:
        case C.Req{+sid, +meth, +path, body} C.CW{+c, w}:
          answer.all(srv, t, answer.rsp(c, w, sid, serve(srv, meth, path, body), C.beq(meth, "HEAD")))

# The plan after a read (wire/loop.bend's Plan): what the frames earned
# and read on; nothing to write, read on; a connection that is over,
# write and close.
def Plan() -> Data:
  L.Plan<C.Cn, Unit>

def plan.cw(cw: C.CW, dead: Bool) -> Plan():
  match cw dead:
    case C.CW{c, w} True{}:
      L.End{[L.Raw{w}]}
    case C.CW{c, SNil{}} False{}:
      L.Wait{c}
    case C.CW{c, SCon{h, t}} False{}:
      L.Go{[L.Raw{SCon{h, t}}], c}

def plan.flush(cw: C.CW, dead: Bool) -> Plan():
  match cw:
    case C.CW{+c, w}:
      plan.cw(C.flush(c, w), dead)

def plan.out(+srv: Srv, o: C.Out) -> Plan():
  match o:
    case C.Out{c, w, rq, dead}:
      plan.flush(answer.all(srv, List.reverse(&2, C.Req, rq), C.CW{c, w}), dead)

def plan(+srv: Srv, buf: Bytes(), c: C.Cn) -> Plan():
  plan.out(srv, C.read(srv.root(srv), c, buf))

def h.plan(srv: Srv, buf: Bytes(), c: C.Cn) -> Plan():
  plan(srv, buf, c)

# The hooks (wire/loop.bend names each): the planner and the budgets
# from the engine's configuration; no upgrade, no stream, no files, no
# access log.
def go(+srv: Srv, s: Socket) -> IO(Socket):
  Fx.serve(~Srv, ~C.Cn, ~Unit, ~srv.idle, ~srv.head, ~h.plan, ~L.no.mid(~C.Cn), ~L.no.big(),
    ~L.no.uplan(~C.Cn, ~Unit), ~L.no.gap(), ~L.no.event, ~L.no.shut, ~L.no.fhead, ~L.no.miss,
    ~L.no.lnote, ~L.no.lsize, srv, C.cn.new(), s)

# With a certificate the listener is a TLS listener that agrees to h2
# by ALPN (and to nothing else: a client that does not offer h2 is not
# one this server can talk to)
def listen(port: U32, shared: Bool, m: Maybe<&2, Eng.Pem>) ->
  IO(Result<&1, &1, U32 & String, Listener>):
  match m:
    case None{}:
      Eng.listen.plain(port, shared)
    case Some{pem}:
      match pem:
        case Eng.Pem{cert, key}:
          TLS.listen_alpn(port, Eng.text(cert), Eng.text(key), "h2")

def banner(+c: Eng.Cfg) -> String:
  String.append("bend-h2 on ", String.append(Eng.scheme(Eng.cfg.pem(c)),
    String.append("://127.0.0.1:", U32.show(Eng.cfg.port(c)))))

def run(+c: Eng.Cfg) -> IO(Unit):
  do IO<Unit>:
    l : Listener <- IO.try(Listener, listen(Eng.cfg.port(c), Eng.cfg.shared(c), Eng.cfg.pem(c)))
    IO.print(banner(c))
    Fx.run(~Srv, ~go, ~srv.grace, ~srv.conns, "bend-h2", srv.new(c), l)

# bend-h2 takes the HTTP/1 engine's flags: [--port N] [--root DIR]
# [--idle-ms N] [--head-ms N] [--max-conns N] [--grace-ms N] [--shared]
# [--tls-cert PEM --tls-key PEM] [--log]
def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    c  : Eng.Cfg <- Eng.args.done(Eng.args.read(xs, Eng.Args{Eng.cfg.new(), Eng.Flag{}}))
    run(c)
