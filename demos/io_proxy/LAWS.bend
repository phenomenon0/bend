# The laws of bend-proxy. What they pin is the one thing a proxy in
# front of another HTTP server must never do: let the two disagree on
# where a request ends. A proxy that forwards the bytes it was sent
# leaves every boundary to the upstream's reading of them -- and a
# request smuggled past the proxy is exactly a boundary the upstream
# draws where the proxy did not (CL.TE, TE.CL, a TE the proxy ignores and
# the upstream obeys). bend-proxy forwards no byte it was sent. It
# frames the client's stream with the HTTP engine's reader -- held to
# spec.bend's frame() by frame_sim -- and sends each request it framed
# rebuilt from what it read: the head as the reader read it, spec.bend's
# views of its lines, which the reader hands over with each request
# (the engine's hd_framed). The laws say, in order:
#
#   scan_is_spec    the proxy frames the client's stream, however it is
#                   cut into reads, as spec.bend's walk frames it, a
#                   fresh walk after each request: the same requests,
#                   heads and all, and a refusal where it refuses
#   frames_agree    and that framing is spec.bend's frame() itself
#   forward_canonical  so the bytes upstream are exactly the requests
#                   frame() framed, each rebuilt: serialize(parsed)
#   no_smuggle      and the upstream, reading them by the same spec,
#                   reads exactly those requests back, one for one
#   hop_by_hop_removed  no forwarded field is a hop's
#   rsp_reframed    the client, reading a response back by
#                   wire/http1's spec, reads the response that came
#   refused_not_forwarded  a stream refused before its first request
#                   ends sends nothing upstream
import Base
import ../../wire/reader.bend as Wr
import ../io_http_engine/main.bend as Eng
import ../io_http_engine/spec.bend as Spec
import ../io_http_engine/LAWS.bend as EL
import ../../wire/http1/resp.bend as R
import ../../wire/http1/spec.bend as RS
import ./core.bend as X

# The reference framing
# =====================
#
# spec.bend's walk, stepped a byte at a time from a fresh walk until it
# completes a request -- the request's bytes are the ones it took --
# then fresh again for the bytes after them; refused where its framing
# of the bytes so far is refused (frame()'s own end: a line already
# broken counts, not only one ended). A request that asked to upgrade
# ends the framing, as it ends spec.bend's.

def w0() -> Spec.W:
  Spec.W{Spec.MReq{Nil{}}, Nil{}, Nil{}}

type PStp is Data:
  PGo{w: Spec.W, raw: List<&2, U32>}
  PMsg{raw: List<&2, U32>, r: Eng.Req}
  PUp{raw: List<&2, U32>, r: Eng.Req}
  PBad{}

def px.req(ws: Bool, raw: List<&2, U32>, r: Eng.Req) -> PStp:
  match ws:
    case True{}:
      PUp{raw, r}
    case False{}:
      PMsg{raw, r}

def px.end(e: Spec.End, w: Spec.W, raw: List<&2, U32>) -> PStp:
  match e:
    case Spec.Refused{}:
      PBad{}
    case _:
      PGo{w, raw}

def px.out(+mode: Spec.Mode, out: List<&2, Eng.Req>, +since: List<&2, U32>, raw: List<&2, U32>) -> PStp:
  match out:
    case Con{+r, t}:
      px.req(Eng.req.ws(r), raw, r)
    case Nil{}:
      px.end(Spec.finish.end(mode, since), Spec.W{mode, Nil{}, since}, raw)

def px.of(w: Spec.W, raw: List<&2, U32>) -> PStp:
  match w:
    case Spec.W{mode, out, since}:
      px.out(mode, out, since, raw)

def px.stp(w: Spec.W, +c: U32, raw: List<&2, U32>) -> PStp:
  px.of(Spec.next(w, c), Spec.snoc(raw, c))

type PTook is Data:
  PTook{raw: List<&2, U32>, r: Eng.Req}

type PTail is Data:
  PWait{w: Spec.W, raw: List<&2, U32>}
  PRefused{}
  PUpgraded{}

type PScanned is Data:
  PScanned{took: List<&2, PTook>, tail: PTail}

def px.done(acc: List<&2, PTook>, t: PTail) -> PScanned:
  PScanned{List.reverse(&2, PTook, acc), t}

def px.go(bs: List<&2, U32>, st: PStp, acc: List<&2, PTook>) -> PScanned:
  match bs st:
    case _ PBad{}:
      px.done(acc, PRefused{})
    case _ PUp{raw, r}:
      px.done(Con{PTook{raw, r}, acc}, PUpgraded{})
    case Nil{} PGo{w, raw}:
      px.done(acc, PWait{w, raw})
    case Nil{} PMsg{raw, r}:
      px.done(Con{PTook{raw, r}, acc}, PWait{w0(), Nil{}})
    case Con{+c, t} PGo{w, raw}:
      px.go(t, px.stp(w, c, raw), acc)
    case Con{+c, t} PMsg{raw, r}:
      px.go(t, px.stp(w0(), c, Nil{}), Con{PTook{raw, r}, acc})

# a whole input, framed request by request
def frame(bs: List<&2, U32>) -> PScanned:
  px.go(bs, PGo{w0(), Nil{}}, Nil{})

# The proxy's framing, seen as the reference's
# ============================================
#
# A request the proxy took is the engine's request, its head with it;
# the scan it waits with is the reference's walk over the bytes since
# the last request, with the engine's reader fed them (the reader is
# compared to the walk only through frame_sim).

def took.reqs(ts: List<&2, PTook>) -> List<&2, Eng.Req>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{t, r}:
      match t:
        case PTook{raw, q}:
          Con{q, took.reqs(r)}

# a scan waiting agrees with a walk waiting: the reader fed the bytes
# since the last request from fresh, the walk walked over them from
# fresh
def Waits(sc: X.Scan, w: Spec.W, raw: List<&2, U32>) -> Type:
  match sc:
    case X.Scan{p, n}:
      {p == Eng.feed(raw, Eng.p.new()) : Eng.P} & {w == Spec.walk(raw, w0()) : Spec.W}

def Tails(t: X.Tail, u: PTail) -> Type:
  match t u:
    case X.TWait{sc} PWait{w, raw}:
      Waits(sc, w, raw)
    case X.TBad{} PRefused{}:
      Unit
    case X.TUp{} PUpgraded{}:
      Unit
    case _ _:
      Empty

def Scans(s: X.Scanned, f: PScanned) -> Type:
  match s f:
    case X.Scanned{ts, t} PScanned{us, u}:
      {ts == took.reqs(us) : List<&2, Eng.Req>} & Tails(t, u)

# the reads of a connection, as main.bend runs them: each through the
# scan the last one left, the requests taken in order, until a read
# ends refused or upgraded
type Conn is Data:
  Conn{took: List<&2, Eng.Req>, tail: X.Tail}

def conn.more(ts: List<&2, Eng.Req>, c: Conn) -> Conn:
  match c:
    case Conn{us, t}:
      Conn{List.append(&2, Eng.Req, ts, us), t}

def reads.at(s: X.Scanned, go: X.Scan -> Conn) -> Conn:
  match s:
    case X.Scanned{ts, t}:
      match t:
        case X.TWait{sc}:
          conn.more(ts, go(sc))
        case X.TBad{}:
          Conn{ts, X.TBad{}}
        case X.TUp{}:
          Conn{ts, X.TUp{}}

def reads.go(rs: List<&2, Bytes()>, sc: X.Scan) -> Conn:
  match rs:
    case Nil{}:
      Conn{Nil{}, X.TWait{sc}}
    case Con{+r, t}:
      reads.at(X.scan(r, sc), s2 => reads.go(t, s2))

def reads(rs: List<&2, Bytes()>) -> Conn:
  reads.go(rs, X.scan.new())

def Conns(c: Conn, f: PScanned) -> Type:
  match c:
    case Conn{ts, t}:
      Scans(X.Scanned{ts, t}, f)

# The reference framing is frame()
# --------------------------------
#
# The requests a framing took, and how its end reads against frame()'s:
# waiting where frame() ends as the walk it waits with ends, refused
# where frame() refuses, after an upgrade where frame() says upgraded.

def wend(w: Spec.W) -> Spec.End:
  match w:
    case Spec.W{m, x, s}:
      Spec.finish.end(m, s)

def is.up(e: Spec.End) -> Bool:
  match e:
    case Spec.Upgraded{b}:
      True{}
    case _:
      False{}

def Ends(u: PTail, e: Spec.End) -> Type:
  match u:
    case PWait{w, raw}:
      {wend(w) == e : Spec.End}
    case PRefused{}:
      {e == Spec.Refused{} : Spec.End}
    case PUpgraded{}:
      {is.up(e) == True{} : Bool}

def Agrees(f: PScanned, g: Spec.Frames) -> Type:
  match f g:
    case PScanned{us, u} Spec.Frames{rs, e}:
      {took.reqs(us) == rs : List<&2, Eng.Req>} & Ends(u, e)

# LAW: the framing a request at a time is frame(). For every input, the
# requests the reference framing takes, restarting after each, are
# exactly the requests spec.bend's frame() frames, in order, and the two
# end alike: frame() is refused exactly where the framing refuses,
# upgraded where it upgrades, and otherwise ends as the walk the framing
# waits with. (A walk never looks at the requests it has done, so
# restarting after one is walking on.)
law frames_agree:
  for +bs: List<&2, U32>
  Agrees(frame(bs), Spec.frame(bs))

# LAW: the proxy frames as the spec does. For every stream a client
# sends, however TCP cuts it into reads, the requests the proxy takes
# are the reference framing's -- the same requests, each with the head
# spec.bend read, in order -- and it ends where the reference ends:
# waiting on the same bytes, refused, or after an upgrade.
law scan_is_spec:
  for +rs: List<&2, Bytes()>
  Conns(reads(rs), frame(Bytes.to_list(Bytes.concat(rs))))

# Forwarding
# ==========
#
# What goes upstream for the reference framing's requests: each one
# rebuilt from its head as spec.bend read it, its target and its framed
# body (core.bend's fwd and ser, the very functions the proxy runs).

def ref.wire(+w: X.Fwd, us: List<&2, PTook>) -> Bytes():
  X.wire(w, took.reqs(us))

def conn.took(c: Conn) -> List<&2, Eng.Req>:
  match c:
    case Conn{ts, t}:
      ts

def scanned.took(f: PScanned) -> List<&2, PTook>:
  match f:
    case PScanned{us, u}:
      us

# LAW: the upstream reads frame()'s requests, rebuilt. For every stream,
# however cut, the bytes the proxy sends upstream are exactly the
# serialization of the requests the reference framing takes from the
# stream whole -- which frames_agree says are frame()'s -- each rebuilt
# from its head as spec.bend read it and its framed body, in order: no
# byte the client sent reaches the upstream but through what the spec
# read.
law forward_canonical:
  for +w: X.Fwd
  for +rs: List<&2, Bytes()>
  {X.wire(w, conn.took(reads(rs))) == ref.wire(w, scanned.took(frame(Bytes.to_list(Bytes.concat(rs))))) : Bytes()}

# LAW: a stream refused before its first request is whole sends nothing
# upstream: the refusal comes before any byte goes out.
law refused_not_forwarded:
  for +rs: List<&2, Bytes()>
  for r: {Spec.frame(Bytes.to_list(Bytes.concat(rs))) == Spec.Frames{Nil{}, Spec.Refused{}} : Spec.Frames}
  {conn.took(reads(rs)) == Nil{} : List<&2, Eng.Req>}

# Reading it back
# ===============
#
# What spec.bend reads from a request the proxy forwarded: its method,
# its target and its body, a request that neither closes nor upgrades
# (the proxy's hop is its own: no Connection, no Upgrade goes up), and
# its head: the method, HTTP/1.1, the Host and then every field the
# proxy sent, each named in lowercase with its value as it came (after
# the one space the proxy writes after the colon), and no Connection.

def sent(fs: List<&2, Wr.Field>) -> List<&2, Wr.Field>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{f, t}:
      match f:
        case Wr.Field{n, v}:
          Con{Wr.Field{Spec.lows(n), Bytes.append(" ", v)}, sent(t)}

def spec.req(m: X.Msg) -> Eng.Req:
  match m:
    case X.Msg{+meth, target, host, fs, body, framed}:
      Eng.Req{Spec.method(meth), target, body, False{}, False{}, "",
        Eng.Hd{meth, False{}, Con{Wr.Field{"host", Bytes.append(" ", host)}, sent(fs)}, Nil{}}}

def spec.reqs(ms: List<&2, X.Msg>) -> List<&2, Eng.Req>:
  match ms:
    case Nil{}:
      Nil{}
    case Con{m, t}:
      Con{spec.req(m), spec.reqs(t)}

# the requests X.wire sends, in order
def fwd.msgs.at(m: Maybe<&2, X.Msg>, rest: List<&2, X.Msg>) -> List<&2, X.Msg>:
  match m:
    case Some{x}:
      Con{x, rest}
    case None{}:
      Nil{}

def fwd.msgs(+w: X.Fwd, ts: List<&2, Eng.Req>) -> List<&2, X.Msg>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{t, r}:
      fwd.msgs.at(X.fwd(w, t), fwd.msgs(w, r))

# LAW: nothing is smuggled. Whatever requests the proxy took, the bytes
# it sends upstream, framed by spec.bend's frame() -- the upstream's
# reading, if it reads HTTP/1.1 as the RFC does -- are exactly one
# request for each one it forwarded, in order, each with the method,
# target, body and fields it was sent with, and nothing after the last:
# no request boundary the upstream could draw that the proxy did not.
law no_smuggle:
  for +w: X.Fwd
  for +ts: List<&2, Eng.Req>
  {Spec.frame(Bytes.to_list(X.wire(w, ts))) == Spec.Frames{spec.reqs(fwd.msgs(w, ts)), Spec.Open{Nil{}}} : Spec.Frames}

# The hop's fields
# ================

def own5(+n: Bytes()) -> Bool:
  Eng.bytes.eq(n, "host") || Eng.bytes.eq(n, "x-forwarded-for") || Eng.bytes.eq(n, "x-forwarded-proto")
    || Eng.bytes.eq(n, "x-forwarded-host") || Eng.bytes.eq(n, "via")

def is.via(+n: Bytes()) -> Bool:
  Eng.bytes.eq(n, "via")

# the hop-by-hop fields, as RFC 9110 7.6.1 lists them, spelled out here
# and not taken from core.bend: Connection, and every field it names,
# Keep-Alive, Proxy-Connection, TE, Transfer-Encoding, Upgrade, Trailer
def hop.fixed(+n: Bytes()) -> Bool:
  Eng.bytes.eq(n, "connection") || Eng.bytes.eq(n, "keep-alive") || Eng.bytes.eq(n, "proxy-connection")
    || Eng.bytes.eq(n, "te") || Eng.bytes.eq(n, "transfer-encoding") || Eng.bytes.eq(n, "upgrade")
    || Eng.bytes.eq(n, "trailer")

def named(+n: Bytes(), ns: List<&2, Bytes()>) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case Con{x, t}:
      Eng.bytes.eq(n, x) || named(n, t)

def hop(+ns: List<&2, Bytes()>, +n: Bytes()) -> Bool:
  hop.fixed(n) || named(n, ns)

# no field is a hop's, save the ones this proxy writes for its own hop
def clean(~mine: @+n: Bytes() -> Bool, +ns: List<&2, Bytes()>, fs: List<&2, Wr.Field>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case Con{f, t}:
      match f:
        case Wr.Field{+n, v}:
          (mine(n) || Bool.not(hop(ns, n))) && clean(~mine, ns, t)

def msg.fields(m: X.Msg) -> List<&2, Wr.Field>:
  match m:
    case X.Msg{meth, target, host, fs, body, framed}:
      fs

def hd.conn(h: Eng.Hd) -> List<&2, Bytes()>:
  match h:
    case Eng.Hd{meth, v10, fs, cn}:
      cn

# LAW: no hop-by-hop field is forwarded. Whatever head the client's
# request came with, the request that goes upstream carries none of
# Connection, Keep-Alive, Proxy-Connection, TE, Transfer-Encoding,
# Upgrade, Trailer, nor any field the client's Connection named (every
# member of every Connection, as the reader split them) -- but for the
# four this proxy writes itself (X-Forwarded-For, -Proto, -Host, Via),
# whatever a Connection said of them (and Host, which has a line of its
# own).
law hop_by_hop_removed:
  for +w: X.Fwd
  for +hd: Eng.Hd
  for target: Bytes()
  for body: Bytes()
  {clean(~own5, hd.conn(hd), msg.fields(X.msg.of(w, hd, target, body))) == True{} : Bool}

# LAW: and none is sent back: a response carries none of the upstream's
# hop-by-hop fields, nor any its Connection named, but the Via it adds.
law hop_by_hop_removed_rsp:
  for +via: Bytes()
  for +ns: List<&2, Bytes()>
  for +len: Bool
  for +fs: List<&2, Wr.Field>
  {clean(~is.via, ns, List.append(&2, Wr.Field, X.rends(ns, len, fs), [Wr.Field{"via", via}])) == True{} : Bool}

# The response read back
# ======================

# what the client reads: the one final response, with the upstream's
# status and body (none where the framing says there is none), closing
# exactly when the proxy closes, and nothing after it; where the proxy
# had no response it could send, its own 502, closing
def rlook(m: Maybe<&2, X.Rsp>, +head: Bool, +code: U32, body: Bytes(), +closing: Bool) -> R.Look:
  match m:
    case Some{r}:
      R.Look{Nil{}, R.Final{R.Resp{code, False{}, closing, Bool.pick(Bytes(), X.rbodyless(head, code), "", body)}, ""}}
    case None{}:
      R.Look{Nil{}, R.Final{R.Resp{502, False{}, True{}, Bool.pick(Bytes(), head, "", "502 Bad Gateway\n")}, ""}}

# LAW: a response goes back as exactly the response that came. Whatever
# the exchange read from the upstream (the interim heads and the final
# one's bytes, the status and the body the reader framed), the bytes the
# proxy sends the client, read by wire/http1/spec.bend's response() --
# how a client that reads HTTP/1.1 as the RFC does frames them -- are
# one final response: the upstream's status and body, the connection's
# fate as the proxy decided it, and not a byte more. A client can never
# see a response boundary the proxy did not send.
law rsp_reframed:
  for +via: Bytes()
  for +head: Bool
  for +k: Nat
  for +code: U32
  for +got: Bytes()
  for +body: Bytes()
  for +closing: Bool
  for +v10: Bool
  {RS.response(X.rask(head), Bytes.to_list(X.reply(X.rsp.of(via, head, k, code, got, body), head, closing, v10))) ==
    rlook(X.rsp.of(via, head, k, code, got, body), head, code, body, closing) : R.Look}
