# The laws of bend-proxy. What they pin is the one thing a proxy in
# front of another HTTP server must never do: let the two disagree on
# where a request ends. A proxy that forwards the bytes it was sent
# leaves every boundary to the upstream's reading of them -- and a
# request smuggled past the proxy is exactly a boundary the upstream
# draws where the proxy did not (CL.TE, TE.CL, a TE the proxy ignores and
# the upstream obeys). bend-proxy forwards no byte it was sent. It
# frames the client's stream with the HTTP engine's reader -- held to
# spec.bend's frame() by frame_sim -- and sends each request it framed
# rebuilt from what it read. The laws say, in order:
#
#   scan_is_spec    the proxy frames the client's stream, however it is
#                   cut into reads, as spec.bend's walk frames it, a
#                   fresh walk after each request: the same requests,
#                   with the same bytes, and a refusal where it refuses
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
# A request the proxy took is its bytes, as a list, and the engine's
# request; the scan it waits with is the reference's walk over the same
# bytes, with the engine's reader fed them (the reader is compared to
# the walk only through frame_sim).

def took.of(t: X.Took) -> PTook:
  match t:
    case X.Took{raw, r}:
      PTook{Bytes.to_list(raw), r}

def tooks.of(ts: List<&2, X.Took>) -> List<&2, PTook>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{t, r}:
      Con{took.of(t), tooks.of(r)}

# a scan waiting agrees with a walk waiting: the same bytes, the reader
# fed them from fresh, the walk walked over them from fresh
def Waits(sc: X.Scan, w: Spec.W, raw: List<&2, U32>) -> Type:
  match sc:
    case X.Scan{p, b}:
      {Bytes.to_list(b) == raw : List<&2, U32>} & {p == Eng.feed(raw, Eng.p.new()) : Eng.P}
        & {w == Spec.walk(raw, w0()) : Spec.W}

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
      {tooks.of(ts) == us : List<&2, PTook>} & Tails(t, u)

# the reads of a connection, as main.bend runs them: each through the
# scan the last one left, the requests taken in order, until a read
# ends refused or upgraded
type Conn is Data:
  Conn{took: List<&2, X.Took>, tail: X.Tail}

def conn.more(ts: List<&2, X.Took>, c: Conn) -> Conn:
  match c:
    case Conn{us, t}:
      Conn{List.append(&2, X.Took, ts, us), t}

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

def took.reqs(ts: List<&2, PTook>) -> List<&2, Eng.Req>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{t, r}:
      match t:
        case PTook{raw, q}:
          Con{q, took.reqs(r)}

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
# are the reference framing's -- the same bytes for each, the same
# request read from them, in order -- and it ends where the reference
# ends: waiting on the same bytes, refused, or after an upgrade.
law scan_is_spec:
  for +rs: List<&2, Bytes()>
  Conns(reads(rs), frame(Bytes.to_list(Bytes.concat(rs))))
