# bend-net: the client.
#
#   r : Result<&2, &2, Client.NetError, Http.Response> <- Client.get("https://example.com/")
#
# A request goes to its URL's origin over a pooled connection (at most 8
# idle per origin, 32 origins, each probed before it is used again; wire/
# pool.bend) or a new one: the name resolved (DNS.resolve), the
# connection made under the connect deadline (TCP.connect_poll, or
# TLS.connect with SNI, ALPN http/1.1 and the certificate verified
# against the system's store or a pinned CA -- never not verified). The
# exchange is wire/client.bend's: the request out, the response read
# through the reader resp_sim holds to RFC 9112 under a head cap, a body
# cap and the exchange's deadline, refused rather than guessed at when it
# is framed two ways. A connection goes back to the pool only when its
# response did not close it and nothing came after it (net/LAWS.bend's
# pool_clean, from wire/client.bend's reuse_clean).
#
# Redirects (301, 302, 303, 307, 308 with a Location) are followed, at
# most 10 (redirect_cap): 303, and 301 or 302 after a POST, go on as GET
# without the body; 307 and 308 keep the method and the body. The
# credentials (Authorization, Cookie, Proxy-Authorization) go only to the
# origin the first request went to (redirect_creds). A gzip body
# (Content-Encoding: gzip) is decoded under the body cap. A request is
# sent again only when a pooled connection turned out stale before
# anything came back on it, and only when its method is idempotent.
import Base
import ../wire/reader.bend as Wr
import ../wire/loop.bend as L
import ../wire/effects.bend as Fx
import ../wire/client.bend as C
import ../wire/pool.bend as P
import ../wire/world.bend as W
import ../wire/http1/resp.bend as R
import ../demos/io_http_engine/main.bend as Eng
import ../demos/io_proxy/core.bend as X
import ../power/gzip.bend as G
import ./http.bend as Http

# Errors
# ======

type NetError is Data:
  Timeout{}
  Refused{}
  Dns{msg: Bytes()}
  Tls{msg: Bytes()}
  Protocol{msg: Bytes()}
  TooLarge{}
  Closed{}
  BadUrl{msg: Bytes()}
  TooManyRedirects{}
  Io{code: U32, msg: Bytes()}

def error.show(e: NetError) -> String:
  match e:
    case Timeout{}:
      "timeout"
    case Refused{}:
      "connection refused"
    case Dns{m}:
      "dns: " ++ m
    case Tls{m}:
      "tls: " ++ m
    case Protocol{m}:
      "protocol: " ++ m
    case TooLarge{}:
      "too large"
    case Closed{}:
      "connection closed"
    case BadUrl{m}:
      "bad url: " ++ m
    case TooManyRedirects{}:
      "too many redirects"
    case Io{c, m}:
      "io: " ++ m ++ " (" ++ U32.show(c) ++ ")"

def Res() -> Data:
  Result<&2, &2, NetError, Http.Response>

# URLs
# ====
#
# An absolute http or https URL, read the way the URL standard reads one
# for a special scheme, less what this client refuses: the scheme in any
# case; tabs and line ends anywhere dropped, and spaces and controls at
# either end; a backslash read as a slash; no user or password (refused:
# a URL is no place for them); the host a name of letters, digits, '-'
# and '.', lowercased, or a dotted address (IPv6 is refused); a port of
# 1 to 65535 digits' worth, the scheme's own when absent or empty; the
# path's dot segments (and %2e) resolved, "/" when there is none; a byte
# the path or query may not carry (a control, a space, ", <, >, `, {, }
# and past 0x7E) percent-encoded; the fragment dropped. LAWS.bend holds
# parse and resolve to the vectors listed there.

type Url is Data:
  Url{tls: Bool, host: Bytes(), port: U32, target: Bytes()}

def url.tls(u: Url) -> Bool:
  match u:
    case Url{t, h, p, g}:
      t

def url.host(u: Url) -> Bytes():
  match u:
    case Url{t, h, p, g}:
      h

def url.port(u: Url) -> U32:
  match u:
    case Url{t, h, p, g}:
      p

def url.target(u: Url) -> Bytes():
  match u:
    case Url{t, h, p, g}:
      g

def dport(tls: Bool) -> U32:
  Bool.pick(U32, tls, 443, 80)

# scheme://host[:port], the port only when it is not the scheme's
def authority(+u: Url) -> Bytes():
  match u:
    case Url{+t, h, +p, g}:
      Bool.pick(Bytes(), U32.is_eq(p, dport(t)), h, Bytes.concat([h, ":", U32.show(p)]))

def origin(+u: Url) -> Bytes():
  match u:
    case Url{+t, h, +p, g}:
      Bytes.concat([Bool.pick(Bytes(), t, "https://", "http://"), h, ":", U32.show(p)])

def url.show(+u: Url) -> Bytes():
  match u:
    case Url{+t, h, p, g}:
      Bytes.concat([Bool.pick(Bytes(), t, "https://", "http://"), authority(Url{t, h, p, ""}), g])

# the input cleaned: tab, LF and CR dropped, a backslash a slash, and
# spaces and controls cut from both ends
def clean.at(drop: Bool, +c: U32, out: Bytes()) -> Bytes():
  match drop:
    case True{}:
      out
    case False{}:
      Bytes.push(out, Bool.pick(U32, U32.is_eq(c, 92), 47, c))

def clean.put(+c: U32, out: Bytes()) -> Bytes():
  clean.at(U32.is_eq(c, 9) || U32.is_eq(c, 10) || U32.is_eq(c, 13), c, out)

def clean.go(s: Bytes(), out: Bytes()) -> Bytes():
  match s:
    case SNil{}:
      out
    case SCon{Chr{+c}, t}:
      clean.go(t, clean.put(c, out))

def edge(+c: U32) -> Bool:
  U32.is_le(c, 32)

def trim.lead.at(cut: Bool, +c: U32, t: Bytes(), go: Bytes() -> Bytes()) -> Bytes():
  match cut:
    case True{}:
      go(t)
    case False{}:
      SCon{Chr{c}, t}

def trim.lead(k: Nat, s: Bytes()) -> Bytes():
  match k:
    case 0n:
      s
    case 1n+j:
      match s:
        case SNil{}:
          ""
        case SCon{Chr{+c}, t}:
          trim.lead.at(edge(c), c, t, r => trim.lead(j, r))

def trim.end(+s: Bytes(), k: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+(+j):
      Bool.pick(Nat, edge(Bytes.get(s, j)), trim.end(s, j), 1n+j)

def input(+s: Bytes()) -> Bytes():
  +t = trim.lead(Bytes.len(s), s)
  clean.go(String.take(t, trim.end(t, Bytes.len(t))), "")

def lower.all(s: Bytes()) -> Bytes():
  Eng.lows(s)

# the index of the first of two bytes at or after i, or the end
def first2(+s: Bytes(), +x: U32, +y: U32) -> Nat:
  Nat.min(Bytes.find_byte(s, 0n, x), Bytes.find_byte(s, 0n, y))

def first3(+s: Bytes(), +x: U32, +y: U32, +z: U32) -> Nat:
  Nat.min(first2(s, x, y), Bytes.find_byte(s, 0n, z))

# a host: a name's bytes, lowercased, or refused
def host.byte(+c: U32) -> Bool:
  (U32.is_le(97, c) && U32.is_le(c, 122)) || (U32.is_le(48, c) && U32.is_le(c, 57)) || U32.is_eq(c, 45)
    || U32.is_eq(c, 46)

def host.ok(s: Bytes()) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{Chr{+c}, t}:
      host.byte(c) && host.ok(t)

def port.at(ok: Bool, +c: U32, +acc: U32, go: U32 -> Maybe<&2, U32>) -> Maybe<&2, U32>:
  match ok:
    case True{}:
      go(((acc * 10 : U32) + (c - 48 : U32) : U32))
    case False{}:
      None{}

def port.dig(s: Bytes(), +acc: U32) -> Maybe<&2, U32>:
  match s:
    case SNil{}:
      Some{acc}
    case SCon{Chr{+c}, t}:
      port.at(U32.is_le(48, c) && U32.is_le(c, 57) && U32.is_lt(acc, 6554), c, acc, a => port.dig(t, a))

def port.range(m: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match m:
    case None{}:
      None{}
    case Some{+p}:
      Bool.pick(Maybe<&2, U32>, U32.is_le(1, p) && U32.is_le(p, 65535), Some{p}, None{})

def port.at.of(empty: Bool, +tls: Bool, +s: Bytes()) -> Maybe<&2, U32>:
  match empty:
    case True{}:
      Some{dport(tls)}
    case False{}:
      port.range(port.dig(s, 0))

def port.of(+tls: Bool, +s: Bytes()) -> Maybe<&2, U32>:
  port.at.of(String.is_empty(s), tls, s)

# s cut at every byte x
def split.at(cut: Bool, +s: Bytes(), +i: Nat, go: Bytes() -> List<&2, Bytes()>) -> List<&2, Bytes()>:
  match cut:
    case True{}:
      Con{String.take(s, i), go(String.drop(s, 1n+i))}
    case False{}:
      [s]

def split.go(k: Nat, +s: Bytes(), +x: U32) -> List<&2, Bytes()>:
  match k:
    case 0n:
      [s]
    case 1n+j:
      +i = Bytes.find_byte(s, 0n, x)
      split.at(Nat.is_lt(i, Bytes.len(s)), s, i, t => split.go(j, t, x))

def split(+s: Bytes(), +x: U32) -> List<&2, Bytes()>:
  split.go(Bytes.len(s), s, x)

# Paths: segments, dot segments resolved (RFC 3986 5.2.4 as the URL
# standard does it: "." and "%2e" are dots, a ".." drops the segment
# before it and never climbs past the root, and a last "." or ".."
# leaves the path ending in "/")
def dot1(+s: Bytes()) -> Bool:
  String.eq(s, ".") || String.eq(lower.all(s), "%2e")

def dot2(+s: Bytes()) -> Bool:
  String.eq(s, "..") || String.eq(lower.all(s), ".%2e") || String.eq(lower.all(s), "%2e.")
    || String.eq(lower.all(s), "%2e%2e")

def pop(st: List<&2, Bytes()>) -> List<&2, Bytes()>:
  match st:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      t

# the stack of segments (newest first) after one more, and whether the
# path now ends in a directory
def dots.at(two: Bool, one: Bool, +s: Bytes(), st: List<&2, Bytes()>) -> List<&2, Bytes()> & Bool:
  match two one:
    case True{} _:
      (pop(st), True{})
    case False{} True{}:
      (st, True{})
    case False{} False{}:
      (Con{s, st}, False{})

def dots.one(+s: Bytes(), st: List<&2, Bytes()>) -> List<&2, Bytes()> & Bool:
  dots.at(dot2(s), dot1(s), s, st)

def dots.go(xs: List<&2, Bytes()>, st: List<&2, Bytes()> & Bool) -> List<&2, Bytes()> & Bool:
  match xs:
    case Nil{}:
      st
    case Con{+x, t}:
      (stk, d) = st
      dots.go(t, dots.one(x, stk))

def dots.join(xs: List<&2, Bytes()>, acc: Bytes()) -> Bytes():
  match xs:
    case Nil{}:
      acc
    case Con{x, t}:
      dots.join(t, Bytes.concat(["/", x, acc]))

def dots.out(r: List<&2, Bytes()> & Bool) -> Bytes():
  (st, dir) = r
  +p = dots.join(st, "")
  Bytes.append(p, Bool.pick(Bytes(), dir || String.is_empty(p), "/", ""))

# a path beginning with '/', its dot segments resolved
def dots(+p: Bytes()) -> Bytes():
  dots.out(dots.go(split(String.drop(p, 1n), 47), (Nil{}, False{})))

# the bytes a path or a query may not carry, percent-encoded
def esc.path(+c: U32) -> Bool:
  U32.is_le(c, 32) || U32.is_le(127, c) || U32.is_eq(c, 34) || U32.is_eq(c, 60) || U32.is_eq(c, 62)
    || U32.is_eq(c, 96) || U32.is_eq(c, 123) || U32.is_eq(c, 125)

def esc.query(+c: U32) -> Bool:
  U32.is_le(c, 32) || U32.is_le(127, c) || U32.is_eq(c, 34) || U32.is_eq(c, 60) || U32.is_eq(c, 62)

def esc.put(e: Bool, +c: U32, out: Bytes()) -> Bytes():
  match e:
    case True{}:
      Bytes.push(Bytes.push(Bytes.push(out, 37), Http.hex.dig(U32.shrn(U32.and(c, 255), 4n))), Http.hex.dig(U32.and(c, 15)))
    case False{}:
      Bytes.push(out, c)

def esc.go(+q: Bool, s: Bytes(), out: Bytes()) -> Bytes():
  match s:
    case SNil{}:
      out
    case SCon{Chr{+c}, t}:
      esc.go(q, t, esc.put(Bool.pick(Bool, q, esc.query(c), esc.path(c)), c, out))

# the target: the path (dots resolved) and the query, the fragment gone
def target.of(+rest: Bytes()) -> Bytes():
  +rq = String.take(rest, Bytes.find_byte(rest, 0n, 35))
  +q = Bytes.find_byte(rq, 0n, 63)
  +path = String.take(rq, q)
  Bytes.append(esc.go(False{}, dots(Bool.pick(Bytes(), String.is_empty(path), "/", path)), ""),
    Bool.pick(Bytes(), Nat.is_lt(q, Bytes.len(rq)), Bytes.append("?", esc.go(True{}, String.drop(rq, 1n+q), "")), ""))

type Parsed is Data:
  Parsed{url: Maybe<&2, Url>, why: Bytes()}

def url.made(user: Bool, v6: Bool, port: Maybe<&2, U32>, +tls: Bool, +host: Bytes(), +rest: Bytes()) ->
  Result<&2, &2, Bytes(), Url>:
  match user v6 port:
    case True{} _ _:
      Fail{"credentials in a URL"}
    case False{} True{} _:
      Fail{"IPv6 addresses are not supported"}
    case False{} False{} None{}:
      Fail{"bad port"}
    case False{} False{} Some{p}:
      Bool.pick(Result<&2, &2, Bytes(), Url>, String.is_empty(host) || Bool.not(host.ok(host)), Fail{"bad host"},
        Done{Url{tls, host, p, target.of(rest)}})

def url.auth(+tls: Bool, +auth: Bytes(), +rest: Bytes()) -> Result<&2, &2, Bytes(), Url>:
  +c = Bytes.find_byte(auth, 0n, 58)
  +host = lower.all(String.take(auth, c))
  +ps = String.drop(auth, 1n+c)
  url.made(Nat.is_lt(Bytes.find_byte(auth, 0n, 64), Bytes.len(auth)), U32.is_eq(Bytes.get(auth, 0n), 91),
    port.of(tls, ps), tls, host, rest)

def url.after(+tls: Bool, +s: Bytes()) -> Result<&2, &2, Bytes(), Url>:
  +a = first3(s, 47, 63, 35)
  url.auth(tls, String.take(s, a), String.drop(s, a))

def url.scheme(https: Bool, http: Bool, +s: Bytes()) -> Result<&2, &2, Bytes(), Url>:
  match https http:
    case True{} _:
      url.after(True{}, String.drop(s, 8n))
    case False{} True{}:
      url.after(False{}, String.drop(s, 7n))
    case False{} False{}:
      Fail{"not an http or https URL"}

def url.clean(+s: Bytes()) -> Result<&2, &2, Bytes(), Url>:
  +low = lower.all(String.take(s, 8n))
  url.scheme(Bytes.starts_with(low, "https://"), Bytes.starts_with(low, "http://"), s)

# an absolute URL, or why it is refused
def parse(s: Bytes()) -> Result<&2, &2, Bytes(), Url>:
  url.clean(input(s))

def rslash(+s: Bytes(), k: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+(+j):
      Bool.pick(Nat, U32.is_eq(Bytes.get(s, j), 47), 1n+j, rslash(s, j))

# a Location against the URL it came from: absolute, scheme-relative,
# path-absolute, a query, or a path relative to the base's directory
def dir.of(+t: Bytes()) -> Bytes():
  +p = String.take(t, first2(t, 63, 35))
  String.take(p, rslash(p, Bytes.len(p)))

def resolve.pick(abs: Bool, net: Bool, root: Bool, qry: Bool, none: Bool, +pre: Bytes(), +auth: Bytes(), +t: Bytes(),
  +l: Bytes()) -> Result<&2, &2, Bytes(), Url>:
  match abs net root qry none:
    case True{} _ _ _ _:
      url.clean(l)
    case False{} True{} _ _ _:
      url.clean(Bytes.append(String.take(pre, Nat.sub(Bytes.len(pre), 2n)), l))
    case False{} False{} True{} _ _:
      url.clean(Bytes.concat([pre, auth, l]))
    case False{} False{} False{} True{} _:
      url.clean(Bytes.concat([pre, auth, String.take(t, first2(t, 63, 35)), l]))
    case False{} False{} False{} False{} True{}:
      url.clean(Bytes.concat([pre, auth, t]))
    case False{} False{} False{} False{} False{}:
      url.clean(Bytes.concat([pre, auth, dir.of(t), l]))

def resolve.go(base: Url, +l: Bytes()) -> Result<&2, &2, Bytes(), Url>:
  match base:
    case Url{+tls, +host, +port, +t}:
      +c0 = Bytes.get(l, 0n)
      +c1 = Bytes.get(l, 1n)
      +auth = authority(Url{tls, host, port, ""})
      +pre = Bool.pick(Bytes(), tls, "https://", "http://")
      resolve.pick(Nat.is_lt(Bytes.find_byte(l, 0n, 58), first3(l, 47, 63, 35)), U32.is_eq(c0, 47) && U32.is_eq(c1, 47),
        U32.is_eq(c0, 47), U32.is_eq(c0, 63), String.is_empty(l), pre, auth, t, l)

def resolve(base: Url, l: Bytes()) -> Result<&2, &2, Bytes(), Url>:
  resolve.go(base, input(l))

# Requests
# ========

# what a caller asks: a method, an absolute URL, header fields and a body
type Req is Data:
  Req{method: Bytes(), url: Bytes(), headers: List<&2, Http.Header>, body: Bytes()}

def req(method: Bytes(), url: Bytes()) -> Req:
  Req{method, url, Nil{}, ""}

def req.header(r: Req, n: Bytes(), v: Bytes()) -> Req:
  match r:
    case Req{m, u, hs, b}:
      Req{m, u, Http.set(hs, n, v), b}

def req.body(r: Req, b: Bytes()) -> Req:
  match r:
    case Req{m, u, hs, old}:
      Req{m, u, hs, b}

# a request on its way: its URL read, its fields' names lowercased
type IReq is Data:
  IReq{method: Bytes(), url: Url, headers: List<&2, Http.Header>, body: Bytes()}

def ireq.url(r: IReq) -> Url:
  match r:
    case IReq{m, u, hs, b}:
      u

def ireq.method(r: IReq) -> Bytes():
  match r:
    case IReq{m, u, hs, b}:
      m

def ireq.headers(r: IReq) -> List<&2, Http.Header>:
  match r:
    case IReq{m, u, hs, b}:
      hs

def lows(hs: List<&2, Http.Header>) -> List<&2, Http.Header>:
  match hs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      match h:
        case Http.Header{n, v}:
          Con{Http.Header{Eng.lows(n), v}, lows(t)}

# The credentials: the fields that say who is asking, and go to no
# origin but the one they were given for
def cred(+n: Bytes()) -> Bool:
  String.eq(n, "authorization") || String.eq(n, "cookie") || String.eq(n, "proxy-authorization")

def no.creds(hs: List<&2, Http.Header>) -> Bool:
  match hs:
    case Nil{}:
      True{}
    case Con{h, t}:
      match h:
        case Http.Header{+n, v}:
          Bool.not(cred(n)) && no.creds(t)

# the fields a redirect carries on: none of the credentials when it goes
# to another origin than the first request's (strip), and none of the
# body's when the body is dropped (body)
def keep.put(k: Bool, h: Http.Header, rest: List<&2, Http.Header>) -> List<&2, Http.Header>:
  match k:
    case True{}:
      Con{h, rest}
    case False{}:
      rest

def keep(+strip: Bool, +body: Bool, hs: List<&2, Http.Header>) -> List<&2, Http.Header>:
  match hs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      match h:
        case Http.Header{+n, v}:
          keep.put(Bool.not(strip && cred(n)) && Bool.not(body && (String.eq(n, "content-type")
            || String.eq(n, "content-length"))), Http.Header{n, v}, keep(strip, body, t))

# Redirects
# =========
#
# follow: the request a response sends the client on to, if it does. A
# 301, 302, 303, 307 or 308 with a Location that resolves against the
# request's URL: 303 goes on as GET (HEAD as HEAD), 301 and 302 turn a
# POST into a GET, and a GET carries no body; 307 and 308 keep the
# method and the body. The credentials go on only to orig, the origin
# of the first request.
def redirecting(+s: U32) -> Bool:
  U32.is_eq(s, 301) || U32.is_eq(s, 302) || U32.is_eq(s, 303) || U32.is_eq(s, 307) || U32.is_eq(s, 308)

def method.next(+s: U32, +m: Bytes()) -> Bytes():
  Bool.pick(Bytes(), (U32.is_eq(s, 303) && Bool.not(String.eq(m, "HEAD")))
    || ((U32.is_eq(s, 301) || U32.is_eq(s, 302)) && String.eq(m, "POST")), "GET", m)

def follow.to(+orig: Bytes(), +m: Bytes(), +m2: Bytes(), hs: List<&2, Http.Header>, body: Bytes(), +u2: Url) -> IReq:
  +strip = Bool.not(String.eq(origin(u2), orig))
  +dropped = Bool.not(String.eq(m, m2))
  IReq{m2, u2, keep(strip, dropped, hs), Bool.pick(Bytes(), dropped, "", body)}

def follow.at(+orig: Bytes(), +s: U32, r: Result<&2, &2, Bytes(), Url>, rq: IReq) -> Maybe<&2, IReq>:
  match r:
    case Fail{e}:
      None{}
    case Done{u2}:
      match rq:
        case IReq{+m, u, hs, body}:
          Some{follow.to(orig, m, method.next(s, m), hs, body, u2)}

def follow.loc(+orig: Bytes(), +s: U32, loc: Maybe<&2, Bytes()>, rq: IReq) -> Maybe<&2, IReq>:
  match loc:
    case None{}:
      None{}
    case Some{l}:
      match rq:
        case IReq{m, +u, hs, body}:
          follow.at(orig, s, resolve(u, l), IReq{m, u, hs, body})

def follow.go(+orig: Bytes(), rq: IReq, redir: Bool, +s: U32, loc: Maybe<&2, Bytes()>) -> Maybe<&2, IReq>:
  match redir:
    case True{}:
      follow.loc(orig, s, loc, rq)
    case False{}:
      None{}

def follow(+orig: Bytes(), rq: IReq, r: Http.Response) -> Maybe<&2, IReq>:
  match r:
    case Http.Response{+s, hs, b}:
      follow.go(orig, rq, redirecting(s), s, Http.get(hs, "location"))

def chain.next(~M: Type -> Type, ~pure: @-A: Type -> A -> M(A), ~S: Type, m: Maybe<&2, IReq>, resp: Http.Response,
  s: S, again: S -> IReq -> M(S & Res())) -> M(S & Res()):
  match m:
    case None{}:
      pure(S & Res(), (s, Done{resp}))
    case Some{rq2}:
      again(s, rq2)

# the chain: send, and follow what redirects, at most k times more; a
# redirect past the last is TooManyRedirects. Written over the monad and
# the send, as wire's loops are: IO and the network in send below, and
# LAWS.bend's scripted peer for redirect_cap and redirect_creds.
def chain.on(~M: Type -> Type, ~pure: @-A: Type -> A -> M(A), ~S: Type, +orig: Bytes(), rq: IReq,
  sr: S & Res(), again: S -> IReq -> M(S & Res())) -> M(S & Res()):
  (s, r) = sr
  match r:
    case Fail{e}:
      pure(S & Res(), (s, Fail{e}))
    case Done{+resp}:
      chain.next(~M, ~pure, ~S, follow(orig, rq, resp), resp, s, again)

def chain(~M: Type -> Type, ~pure: @-A: Type -> A -> M(A),
  ~bind: @-A: Type -> @-B: Type -> M(A) -> (A -> M(B)) -> M(B), ~S: Data, ~send: @+s: S -> IReq -> M(S & Res()),
  k: Nat, +orig: Bytes(), +rq: IReq, s: S) -> M(S & Res()):
  match k:
    case 0n:
      bind(S & Res(), S & Res(), send(s, rq), sr =>
        chain.on(~M, ~pure, ~S, orig, rq, sr, s2 => rq2 => pure(S & Res(), (s2, Fail{TooManyRedirects{}}))))
    case 1n+j:
      bind(S & Res(), S & Res(), send(s, rq), sr =>
        chain.on(~M, ~pure, ~S, orig, rq, sr, s2 => rq2 => chain(~M, ~pure, ~bind, ~S, ~send, j, orig, rq2, s2)))

# Options
# =======

# connect: a connection's deadline; timeout: an exchange's (the
# request out, the whole response in); max_body: the most a body may be
# (past it, TooLarge); redirects: the most followed; ca: a PEM file of
# the CAs to trust ("" for the system's); gzip: ask for gzip and decode it
type Opts is Data:
  Opts{connect: U32, timeout: U32, max_body: U32, redirects: Nat, ca: String, gzip: Bool}

def opts() -> Opts:
  Opts{10000, 30000, 10485760, 10n, "", True{}}

def opts.connect(o: Opts) -> U32:
  match o:
    case Opts{c, t, mb, rd, ca, gz}:
      c

def opts.timeout(o: Opts) -> U32:
  match o:
    case Opts{c, t, mb, rd, ca, gz}:
      t

def opts.max_body(o: Opts) -> U32:
  match o:
    case Opts{c, t, mb, rd, ca, gz}:
      mb

def opts.redirects(o: Opts) -> Nat:
  match o:
    case Opts{c, t, mb, rd, ca, gz}:
      rd

def opts.ca(o: Opts) -> String:
  match o:
    case Opts{c, t, mb, rd, ca, gz}:
      ca

def opts.gzip(o: Opts) -> Bool:
  match o:
    case Opts{c, t, mb, rd, ca, gz}:
      gz

def with.connect(o: Opts, ms: U32) -> Opts:
  match o:
    case Opts{c, t, mb, rd, ca, gz}:
      Opts{ms, t, mb, rd, ca, gz}

def with.timeout(o: Opts, ms: U32) -> Opts:
  match o:
    case Opts{c, t, mb, rd, ca, gz}:
      Opts{c, ms, mb, rd, ca, gz}

def with.max_body(o: Opts, n: U32) -> Opts:
  match o:
    case Opts{c, t, mb, rd, ca, gz}:
      Opts{c, t, n, rd, ca, gz}

def with.redirects(o: Opts, n: Nat) -> Opts:
  match o:
    case Opts{c, t, mb, rd, ca, gz}:
      Opts{c, t, mb, n, ca, gz}

def with.ca(o: Opts, file: String) -> Opts:
  match o:
    case Opts{c, t, mb, rd, ca, gz}:
      Opts{c, t, mb, rd, file, gz}

def with.gzip(o: Opts, on: Bool) -> Opts:
  match o:
    case Opts{c, t, mb, rd, ca, gz}:
      Opts{c, t, mb, rd, ca, on}

# The pools
# =========
#
# A session's idle connections, a pool (wire/pool.bend) per origin, in
# a channel of one that serves as their lock.
type Kp is Type:
  Kp{key: Bytes(), pool: P.Pool<&1, Socket>}

def Pools() -> Type:
  List<&1, Kp>

type Session is Data:
  Session{opts: Opts, pools: Chan(Pools())}

def session(o: Opts) -> IO(Session):
  do IO<Session>:
    +ch : Chan(Pools()) <- Chan.new(Pools(), 1)
    ok : Bool <- Chan.send(Pools(), ch, Nil{})
    return Session{o, ch}

def s.opts(s: Session) -> Opts:
  match s:
    case Session{o, ch}:
      o

def s.pools(s: Session) -> Chan(Pools()):
  match s:
    case Session{o, ch}:
      ch

def pool.cap() -> Nat:
  8n

def pools.cap() -> Nat:
  32n

def pools.cons(kp: Kp, r: P.Pool<&1, Socket> & Pools()) -> P.Pool<&1, Socket> & Pools():
  (p, t) = r
  (p, Con{kp, t})

def pools.step(eq: Bool, +k: Bytes(), pool: P.Pool<&1, Socket>, r: Maybe<&1, P.Pool<&1, Socket>> & Pools()) ->
  Maybe<&1, P.Pool<&1, Socket>> & Pools():
  match eq:
    case True{}:
      (m, rest) = r
      (Some{pool}, rest)
    case False{}:
      (m, rest) = r
      (m, Con{Kp{k, pool}, rest})

# the pool for key, out of the list, if it has one (the keys are distinct)
def pools.find(ps: Pools(), +key: Bytes()) -> Maybe<&1, P.Pool<&1, Socket>> & Pools():
  match ps:
    case Nil{}:
      (None{}, Nil{})
    case Con{kp, t}:
      match kp:
        case Kp{+k, pool}:
          pools.step(String.eq(k, key), k, pool, pools.find(t, key))

def pools.new(r: Maybe<&1, P.Pool<&1, Socket>> & Pools()) -> P.Pool<&1, Socket> & Pools():
  (m, rest) = r
  match m:
    case Some{p}:
      (p, rest)
    case None{}:
      (P.pool.new(&1, Socket, pool.cap(), 60000n, 4000n), rest)

# the pool for key, out of the list (a new one if there is none)
def pools.out(ps: Pools(), +key: Bytes()) -> P.Pool<&1, Socket> & Pools():
  pools.new(pools.find(ps, key))

def pools.close(ps: Pools()) -> IO(Unit):
  match ps:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{kp, t}:
      match kp:
        case Kp{k, pool}:
          IO.bind(Unit, Unit, P.close.all(~(A => IO(A)), ~IO.pure, ~IO.bind, ~&1, ~Socket, ~Socket.close,
            P.pool.xs(&1, Socket, pool)), u => pools.close(t))

# at most pools.cap() origins: the ones past it closed
def pools.trim(k: Nat, ps: Pools()) -> IO(Pools()):
  match k ps:
    case _ Nil{}:
      IO.pure(Pools(), Nil{})
    case 0n Con{h, t}:
      IO.bind(Unit, Pools(), pools.close(Con{h, t}), u => IO.pure(Pools(), Nil{}))
    case 1n+j Con{h, t}:
      IO.bind(Pools(), Pools(), pools.trim(j, t), r => IO.pure(Pools(), Con{h, r}))

def took.put(+ch: Chan(Pools()), +key: Bytes(), rest: Pools(), pm: P.Pool<&1, Socket> & Maybe<&1, P.Slot<&1, Socket>>) ->
  IO(Maybe<&1, P.Slot<&1, Socket>>):
  (pool, may) = pm
  do IO<Maybe<&1, P.Slot<&1, Socket>>>:
    ok : Bool <- Chan.send(Pools(), ch, Con{Kp{key, pool}, rest})
    return may

def took.of(+ch: Chan(Pools()), +key: Bytes(), +now: Nat, pr: P.Pool<&1, Socket> & Pools()) ->
  IO(Maybe<&1, P.Slot<&1, Socket>>):
  (pool, rest) = pr
  IO.bind(P.Pool<&1, Socket> & Maybe<&1, P.Slot<&1, Socket>>, Maybe<&1, P.Slot<&1, Socket>>, P.take.io(pool, now),
    pm => took.put(ch, key, rest, pm))

def took(+ch: Chan(Pools()), +key: Bytes(), +now: Nat, m: Maybe<&1, Pools()>) -> IO(Maybe<&1, P.Slot<&1, Socket>>):
  match m:
    case Some{ps}:
      took.of(ch, key, now, pools.out(ps, key))
    case None{}:
      IO.pure(Maybe<&1, P.Slot<&1, Socket>>, None{})

# a connection to key's origin, fit to use, if the pool has one
def pool.take(+ch: Chan(Pools()), +key: Bytes()) -> IO(Maybe<&1, P.Slot<&1, Socket>>):
  do IO<Maybe<&1, P.Slot<&1, Socket>>>:
    +now : Nat <- IO.now()
    m : Maybe<&1, Pools()> <- Chan.recv(Pools(), ch)
    took(ch, key, now, m)

def gave(+ch: Chan(Pools()), +key: Bytes(), rest: Pools(), pool: P.Pool<&1, Socket>) -> IO(Unit):
  do IO<Unit>:
    ps : Pools() <- pools.trim(pools.cap(), Con{Kp{key, pool}, rest})
    ok : Bool <- Chan.send(Pools(), ch, ps)
    return Unit{}

def give.of(+ch: Chan(Pools()), +key: Bytes(), s: Socket, +born: Nat, +now: Nat, ok: Bool,
  pr: P.Pool<&1, Socket> & Pools()) -> IO(Unit):
  (pool, rest) = pr
  IO.bind(P.Pool<&1, Socket>, Unit, P.give.io(pool, s, born, now, ok), p2 => gave(ch, key, rest, p2))

def give.at(+ch: Chan(Pools()), +key: Bytes(), s: Socket, +born: Nat, +now: Nat, ok: Bool, m: Maybe<&1, Pools()>) ->
  IO(Unit):
  match m:
    case Some{ps}:
      give.of(ch, key, s, born, now, ok, pools.out(ps, key))
    case None{}:
      Socket.close(s)

# a connection back to key's pool, kept if ok (the pool closes it if not)
def pool.give(+ch: Chan(Pools()), +key: Bytes(), s: Socket, +born: Nat, ok: Bool) -> IO(Unit):
  do IO<Unit>:
    +now : Nat <- IO.now()
    m : Maybe<&1, Pools()> <- Chan.recv(Pools(), ch)
    give.at(ch, key, s, born, now, ok, m)

def close.at(+ch: Chan(Pools()), m: Maybe<&1, Pools()>) -> IO(Unit):
  match m:
    case Some{ps}:
      IO.bind(Unit, Unit, pools.close(ps), u => IO.bind(Bool, Unit, Chan.send(Pools(), ch, Nil{}), ok => IO.pure(Unit, Unit{})))
    case None{}:
      IO.pure(Unit, Unit{})

# The exchange
# ============

# every idle connection the session holds, closed
def close(s: Session) -> IO(Unit):
  match s:
    case Session{o, +ch}:
      do IO<Unit>:
        m : Maybe<&1, Pools()> <- Chan.recv(Pools(), ch)
        close.at(ch, m)

# The socket the exchange reads through keeps the head's bytes it read
# (the first head.cap of them), so the final response's head is read
# again from them for its fields (bend-proxy's rfinal and fields.of).
type Rec is Type:
  Rec{s: Socket, got: Bytes()}

def head.cap() -> U32:
  65536

def rec.keep(+got: Bytes(), +bs: Bytes()) -> Bytes():
  Bool.pick(Bytes(), Nat.is_lt(Bytes.len(got), U32.to_nat(head.cap())), Bytes.append(got, bs), got)

def rec.got(+got: Bytes(), g: L.Got(Socket)) -> L.Got(Rec):
  (s, r) = g
  match r:
    case Done{m}:
      match m:
        case Some{+bs}:
          (Rec{s, rec.keep(got, bs)}, Done{Some{bs}})
        case None{}:
          (Rec{s, got}, Done{None{}})
    case Fail{e}:
      (Rec{s, got}, Fail{e})

def rec.rx(r: Rec, max: U32, ms: Nat) -> IO(L.Got(Rec)):
  match r:
    case Rec{s, +got}:
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

# Whether a connection goes back to its pool after an exchange: only
# when the exchange ended in a response that did not close it and
# nothing came after it -- wire/client.bend's reuse, which reuse_clean
# says of every peer (net/LAWS.bend's pool_clean).
def fit(r: Result<&2, &2, C.Why, C.Got>) -> Bool:
  match r:
    case Done{g}:
      match g:
        case C.Got{i, x, extra, reuse}:
          reuse
    case Fail{w}:
      False{}

# the bytes of a request: the request line, Host, the client's fields,
# the caller's (but the ones the client writes), the length, the body
def own.field(+n: Bytes()) -> Bool:
  String.eq(n, "host") || String.eq(n, "content-length") || String.eq(n, "transfer-encoding")
    || String.eq(n, "connection") || String.eq(n, "te") || String.eq(n, "upgrade") || String.eq(n, "trailer")
    || String.eq(n, "keep-alive")

def token.byte(+c: U32) -> Bool:
  (U32.is_le(97, c) && U32.is_le(c, 122)) || (U32.is_le(65, c) && U32.is_le(c, 90))
    || (U32.is_le(48, c) && U32.is_le(c, 57)) || U32.is_eq(c, 45) || U32.is_eq(c, 95) || U32.is_eq(c, 46)
    || U32.is_eq(c, 33) || U32.is_eq(c, 35) || U32.is_eq(c, 36) || U32.is_eq(c, 37) || U32.is_eq(c, 38)
    || U32.is_eq(c, 39) || U32.is_eq(c, 42) || U32.is_eq(c, 43) || U32.is_eq(c, 94) || U32.is_eq(c, 96)
    || U32.is_eq(c, 124) || U32.is_eq(c, 126)

def token(s: Bytes()) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{Chr{+c}, t}:
      token.byte(c) && token(t)

# a field the request may carry: a token name, and a value of space,
# tab and visible ASCII (no line end, so no field can end the head)
def field.ok(+n: Bytes(), +v: Bytes()) -> Bool:
  Bool.not(String.is_empty(n)) && token(n) && X.all.in(v, 32, 127)

def fields.at(own: Bool, ok: Bool, +n: Bytes(), +v: Bytes(), acc: Bytes(), go: Bytes() -> Maybe<&2, Bytes()>) ->
  Maybe<&2, Bytes()>:
  match own ok:
    case True{} _:
      go(acc)
    case False{} True{}:
      go(Bytes.concat([acc, n, ": ", v, "\r\n"]))
    case False{} False{}:
      None{}

def fields.put(fs: List<&2, Http.Header>, acc: Bytes()) -> Maybe<&2, Bytes()>:
  match fs:
    case Nil{}:
      Some{acc}
    case Con{h, t}:
      match h:
        case Http.Header{+n, +v}:
          fields.at(own.field(n), field.ok(n, v), n, v, acc, a => fields.put(t, a))

def has.body(+m: Bytes(), +b: Bytes()) -> Bool:
  Bool.not(String.is_empty(b)) || String.eq(m, "POST") || String.eq(m, "PUT") || String.eq(m, "PATCH")

def wire.at(ok: Bool, head: Maybe<&2, Bytes()>, len: Bytes(), b: Bytes()) -> Maybe<&2, Bytes()>:
  match ok head:
    case True{} Some{h}:
      Some{Bytes.concat([h, len, "\r\n", b])}
    case _ _:
      None{}

def wire.of(+o: Opts, +m: Bytes(), u: Url, +hs: List<&2, Http.Header>, +b: Bytes()) -> Maybe<&2, Bytes()>:
  match u:
    case Url{+t, +h, +p, g}:
      wire.at(token(m) && Bool.not(String.is_empty(m)),
        fields.put(hs, Bytes.concat([m, " ", g, " HTTP/1.1\r\nhost: ", authority(Url{t, h, p, ""}), "\r\n",
          Bool.pick(Bytes(), Http.has(hs, "user-agent"), "", "user-agent: bend-net/1\r\n"),
          Bool.pick(Bytes(), opts.gzip(o) && Bool.not(Http.has(hs, "accept-encoding")), "accept-encoding: gzip\r\n", "")])),
        Bool.pick(Bytes(), has.body(m, b), Bytes.concat(["content-length: ", Nat.show(Bytes.len(b)), "\r\n"]), ""), b)

# The response: its status, its fields (read again from the final head's
# bytes, but the ones the framing used up), and its body, decoded when
# it came gzipped and the session asked for that
def framing.field(+n: Bytes()) -> Bool:
  String.eq(n, "transfer-encoding") || String.eq(n, "connection") || String.eq(n, "keep-alive")

def fields.of(fs: List<&2, Wr.Field>, +gz: Bool) -> List<&2, Http.Header>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{f, t}:
      match f:
        case Wr.Field{+n, v}:
          keep.put(Bool.not(framing.field(n) || (gz && (String.eq(n, "content-encoding") || String.eq(n, "content-length")))),
            Http.Header{n, v}, fields.of(t, gz))

def head.fields(+h: Bytes()) -> List<&2, Wr.Field>:
  +e = Bytes.find_byte(h, 0n, 13)
  Maybe.default(&2, List<&2, Wr.Field>, X.fields.of(X.rlines(String.drop(h, Nat.add(e, 2n)))), Nil{})

def gz.is(+fs: List<&2, Wr.Field>) -> Bool:
  X.in.names("gzip", X.members(X.first(X.values("content-encoding", fs), "")))


def body.gz(+code: U32, fs: List<&2, Wr.Field>, r: Result<&2, &2, G.Err, Bytes()>) -> Res():
  match r:
    case Done{b}:
      Done{Http.Response{code, fields.of(fs, True{}), Http.BBody{b}}}
    case Fail{e}:
      match e:
        case G.Err{at, why}:
          Fail{Protocol{Bytes.append("gzip: ", G.why.show(why))}}

def body.of(zip: Bool, +cap: U32, +code: U32, fs: List<&2, Wr.Field>, body: Bytes()) -> Res():
  match zip:
    case False{}:
      Done{Http.Response{code, fields.of(fs, False{}), Http.BBody{body}}}
    case True{}:
      body.gz(code, fs, G.gunzip(U32.to_nat(cap), body))

def resp.at(+o: Opts, +code: U32, +fs: List<&2, Wr.Field>, body: Bytes()) -> Res():
  body.of(opts.gzip(o) && gz.is(fs), opts.max_body(o), code, fs, body)

def resp.of(+o: Opts, +k: Nat, +got: Bytes(), r: R.Resp) -> Res():
  match r:
    case R.Resp{+code, v10, close, body}:
      resp.at(o, code, head.fields(X.rfinal(k, got)), body)

# what an exchange that failed was: the deadline, the head past its cap,
# a body past the cap (a refusal after as many bytes, or a length that
# said so), a response refused, a connection cut
def len.num(+v: Bytes()) -> Maybe<&2, U32>:
  U32.read(X.trim(v))

def len.over.at(+cap: U32, m: Maybe<&2, U32>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{+n}:
      U32.is_lt(cap, n)

def len.over(+o: Opts, +got: Bytes()) -> Bool:
  len.over.at(opts.max_body(o), len.num(X.first(X.values("content-length", head.fields(X.rfinal(0n, got))), "")))

def why.of(+o: Opts, +got: Bytes(), w: C.Why) -> NetError:
  match w:
    case C.CTime{}:
      Timeout{}
    case C.CHead{}:
      TooLarge{}
    case C.CFrame{}:
      Bool.pick(NetError, len.over(o, got) || Nat.is_lt(U32.to_nat(opts.max_body(o)), Bytes.len(got)), TooLarge{},
        Protocol{"the response was malformed, or framed two ways"})
    case C.CEof{}:
      Closed{}
    case C.CRecv{c}:
      Closed{}
    case C.CSend{c}:
      Closed{}
    case C.CFuel{}:
      Protocol{"the response took too many reads"}
    case C.CStall{}:
      Protocol{"stalled"}

# a failure on a pooled connection with nothing read is the connection's
# fault (it went stale), not the request's
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

# RFC 9110 9.2.2
def idempotent(+m: Bytes()) -> Bool:
  String.eq(m, "GET") || String.eq(m, "HEAD") || String.eq(m, "PUT") || String.eq(m, "DELETE")
    || String.eq(m, "OPTIONS") || String.eq(m, "TRACE")

# Connecting
# ==========

def dial.err(+code: U32, msg: String) -> NetError:
  Bool.pick(NetError, U32.is_eq(code, 110) || U32.is_eq(code, 60), Timeout{},
    Bool.pick(NetError, U32.is_eq(code, 111) || U32.is_eq(code, 61), Refused{}, Io{code, msg}))

def tls.err(+code: U32, msg: String) -> NetError:
  Bool.pick(NetError, U32.is_eq(code, 110) || U32.is_eq(code, 60), Timeout{},
    Bool.pick(NetError, U32.is_eq(code, 111) || U32.is_eq(code, 61), Refused{}, Tls{msg}))

def dial.tcp(r: Result<&1, &1, U32 & String, Socket>) -> Result<&1, &1, NetError, Socket>:
  match r:
    case Done{s}:
      Done{s}
    case Fail{e}:
      (+code, msg) = e
      Fail{dial.err(code, msg)}

def dial.tls(r: Result<&1, &1, U32 & String, Socket & String>) -> Result<&1, &1, NetError, Socket>:
  match r:
    case Done{sp}:
      (s, proto) = sp
      Done{s}
    case Fail{e}:
      (+code, msg) = e
      Fail{tls.err(code, msg)}

def dial.on(tls: Bool, +o: Opts, addr: String, host: String, +port: U32) -> IO(Result<&1, &1, NetError, Socket>):
  match tls:
    case True{}:
      IO.bind(Result<&1, &1, U32 & String, Socket & String>, Result<&1, &1, NetError, Socket>,
        TLS.connect(addr, port, host, "http/1.1", opts.ca(o), opts.connect(o)),
        r2 => IO.pure(Result<&1, &1, NetError, Socket>, dial.tls(r2)))
    case False{}:
      IO.bind(Result<&1, &1, U32 & String, Socket>, Result<&1, &1, NetError, Socket>,
        TCP.connect_poll(addr, port, opts.connect(o)), r2 => IO.pure(Result<&1, &1, NetError, Socket>, dial.tcp(r2)))

def dial.addr(+o: Opts, r: Result<&1, &1, U32 & String, String>, u: Url) -> IO(Result<&1, &1, NetError, Socket>):
  match r:
    case Fail{e}:
      (code, msg) = e
      IO.pure(Result<&1, &1, NetError, Socket>, Fail{Dns{msg}})
    case Done{addr}:
      match u:
        case Url{tls, host, port, t}:
          dial.on(tls, o, addr, host, port)

# a new connection to the URL's origin
def dial(+o: Opts, +u: Url) -> IO(Result<&1, &1, NetError, Socket>):
  IO.bind(Result<&1, &1, U32 & String, String>, Result<&1, &1, NetError, Socket>, DNS.resolve(url.host(u)),
    r => dial.addr(o, r, u))

# One exchange on a connection made at born: the connection goes back
# to the pool if the exchange left it fit (else it is closed); again
# says a failure that finds it stale, with nothing read, may be sent
# again (a pooled connection, an idempotent method), which Stale says.
type Try is Data:
  TRes{r: Res()}
  TStale{}

def ex.fail(again: Bool, +o: Opts, +got: Bytes(), w: C.Why) -> Try:
  match again:
    case True{}:
      TStale{}
    case False{}:
      TRes{Fail{why.of(o, got, w)}}

def ex.res(+ss: Session, +key: Bytes(), +born: Nat, again: Bool, s: Socket, +got: Bytes(), ok: Bool,
  r: Result<&2, &2, C.Why, C.Got>) -> IO(Try):
  match r:
    case Done{g}:
      match g:
        case C.Got{i, resp, extra, reuse}:
          IO.bind(Unit, Try, pool.give(s.pools(ss), key, s, born, ok),
            u => IO.pure(Try, TRes{resp.of(s.opts(ss), List.length(&2, U32, i), got, resp)}))
    case Fail{+w}:
      IO.bind(Unit, Try, Socket.close(s), u => IO.pure(Try, ex.fail(again && stale(w), s.opts(ss), got, w)))

def ex.done(+ss: Session, +key: Bytes(), +born: Nat, again: Bool, out: C.Out(Rec)) -> IO(Try):
  (rc, +r) = out
  match rc:
    case Rec{s, +got}:
      ex.res(ss, key, born, again && String.is_empty(got), s, got, fit(r), r)

def budget(+o: Opts) -> C.Budget:
  C.Budget{head.cap(), opts.timeout(o), opts.timeout(o)}

def ex.go(+ss: Session, +key: Bytes(), wire: Bytes(), +head: Bool, s: Socket, +born: Nat, again: Bool) -> IO(Try):
  IO.bind(C.Out(Rec), Try,
    C.exchange(~(A => IO(A)), ~IO.pure, ~IO.bind, ~Rec, ~rec.rx, ~rec.tx, ~rec.clk,
      R.ask.new(head, opts.max_body(s.opts(ss))), budget(s.opts(ss)), wire, Rec{s, ""}),
    out => ex.done(ss, key, born, again, out))

def try.res(t: Try) -> Res():
  match t:
    case TRes{r}:
      r
    case TStale{}:
      Fail{Closed{}}

def ex.dialed(+ss: Session, +key: Bytes(), wire: Bytes(), +head: Bool, +born: Nat, r: Result<&1, &1, NetError, Socket>) ->
  IO(Res()):
  match r:
    case Done{s}:
      IO.bind(Try, Res(), ex.go(ss, key, wire, head, s, born, False{}), t => IO.pure(Res(), try.res(t)))
    case Fail{e}:
      IO.pure(Res(), Fail{e})

# the exchange on a new connection
def ex.fresh(+ss: Session, +u: Url, +key: Bytes(), wire: Bytes(), +head: Bool) -> IO(Res()):
  do IO<Res()>:
    +born : Nat <- IO.now()
    r : Result<&1, &1, NetError, Socket> <- dial(s.opts(ss), u)
    ex.dialed(ss, key, wire, head, born, r)

def ex.then(+ss: Session, +u: Url, +key: Bytes(), +wire: Bytes(), +head: Bool, t: Try) -> IO(Res()):
  match t:
    case TRes{r}:
      IO.pure(Res(), r)
    case TStale{}:
      ex.fresh(ss, u, key, wire, head)

# on a pooled connection if the pool has one fit to use, else a new one
def ex.slot(+ss: Session, +u: Url, +key: Bytes(), +wire: Bytes(), +head: Bool, idem: Bool,
  m: Maybe<&1, P.Slot<&1, Socket>>) -> IO(Res()):
  match m:
    case Some{sl}:
      match sl:
        case P.Slot{s, +born, last}:
          IO.bind(Try, Res(), ex.go(ss, key, wire, head, s, born, idem), t => ex.then(ss, u, key, wire, head, t))
    case None{}:
      ex.fresh(ss, u, key, wire, head)

def send.key(+ss: Session, +m: Bytes(), +u: Url, +wire: Bytes(), +key: Bytes()) -> IO(Session & Res()):
  do IO<Session & Res()>:
    m2 : Maybe<&1, P.Slot<&1, Socket>> <- pool.take(s.pools(ss), key)
    r : Res() <- ex.slot(ss, u, key, wire, String.eq(m, "HEAD"), idempotent(m), m2)
    return (ss, r)

def send.wire(+ss: Session, +m: Bytes(), +u: Url, w: Maybe<&2, Bytes()>) -> IO(Session & Res()):
  match w:
    case None{}:
      IO.pure(Session & Res(), (ss, Fail{Protocol{"the request's method or a field is malformed"}}))
    case Some{+wire}:
      send.key(ss, m, u, wire, origin(u))

# One request, one response, over the pool: the IO send of the chain
def send.one(+ss: Session, rq: IReq) -> IO(Session & Res()):
  match rq:
    case IReq{+m, +u, hs, +b}:
      send.wire(ss, m, u, wire.of(s.opts(ss), m, u, hs, b))

# The API
# =======

def ireq.at(m: Bytes(), p: Result<&2, &2, Bytes(), Url>, hs: List<&2, Http.Header>, b: Bytes()) ->
  Result<&2, &2, NetError, IReq>:
  match p:
    case Done{u}:
      Done{IReq{m, u, lows(hs), b}}
    case Fail{e}:
      Fail{BadUrl{e}}

def ireq.of(r: Req) -> Result<&2, &2, NetError, IReq>:
  match r:
    case Req{m, u, hs, b}:
      ireq.at(m, parse(u), hs, b)

def fetch.at(+ss: Session, r: Result<&2, &2, NetError, IReq>) -> IO(Res()):
  match r:
    case Fail{e}:
      IO.pure(Res(), Fail{e})
    case Done{+rq}:
      IO.bind(Session & Res(), Res(),
        chain(~(A => IO(A)), ~IO.pure, ~IO.bind, ~Session, ~send.one, opts.redirects(s.opts(ss)),
          origin(ireq.url(rq)), rq, ss),
        sr => IO.pure(Res(), Pair.snd(Session, Res(), sr)))

# a request on the session's connections
def fetch(+ss: Session, r: Req) -> IO(Res()):
  fetch.at(ss, ireq.of(r))

# a request on a session of its own, closed after
def request(r: Req, o: Opts) -> IO(Res()):
  do IO<Res()>:
    +ss : Session <- session(o)
    +res : Res() <- fetch(ss, r)
    close(ss)
    return res

def get(url: Bytes()) -> IO(Res()):
  request(req("GET", url), opts())

def post(url: Bytes(), ctype: Bytes(), body: Bytes()) -> IO(Res()):
  request(Req{"POST", url, [Http.Header{"content-type", ctype}], body}, opts())
