# bend-net: URLs, as the client (net/client.bend) reads them, and any
# other part of net/ that dials one (net/ws.bend's ws:// and wss:// read
# the same way through parse.ws).
#
#   Url.parse("HTTP://Example.com:8080/a/./b/../c?q#f")   http://example.com:8080/a/c?q
#   Url.resolve(base, "../x")                              a Location against its request
#
# An absolute URL, read the way the URL standard reads one for a
# special scheme, less what bend-net refuses: the scheme in any
# case; tabs and line ends anywhere dropped, and spaces and controls at
# either end; a backslash read as a slash; no user or password (refused:
# a URL is no place for them); the host a name of letters, digits, '-',
# '_' and '.', lowercased, or a dotted address (IPv6 is refused); a port of
# 1 to 65535 digits' worth, the scheme's own when absent or empty; the
# path's dot segments (and %2e) resolved, "/" when there is none; a byte
# the path or query may not carry (a control, a space, ", <, >, `, {, }
# and past 0x7E) percent-encoded; the fragment dropped. LAWS.bend holds
# parse and resolve to the vectors listed there.
import Base
import ../demos/io_http_engine/main.bend as Eng

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
    || U32.is_eq(c, 46) || U32.is_eq(c, 95)

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

def hexd(+v: U32) -> U32:
  Bool.pick(U32, U32.is_lt(v, 10), (v + 48 : U32), (v + 55 : U32))

# the bytes a path or a query may not carry, percent-encoded
def esc.path(+c: U32) -> Bool:
  U32.is_le(c, 32) || U32.is_le(127, c) || U32.is_eq(c, 34) || U32.is_eq(c, 60) || U32.is_eq(c, 62)
    || U32.is_eq(c, 96) || U32.is_eq(c, 123) || U32.is_eq(c, 125)

def esc.query(+c: U32) -> Bool:
  U32.is_le(c, 32) || U32.is_le(127, c) || U32.is_eq(c, 34) || U32.is_eq(c, 60) || U32.is_eq(c, 62)

def esc.put(e: Bool, +c: U32, out: Bytes()) -> Bytes():
  match e:
    case True{}:
      Bytes.push(Bytes.push(Bytes.push(out, 37), hexd(U32.shrn(U32.and(c, 255), 4n))), hexd(U32.and(c, 15)))
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

def url.scheme(secure: Bool, plain: Bool, +n: Nat, +s: Bytes()) -> Result<&2, &2, Bytes(), Url>:
  match secure plain:
    case True{} _:
      url.after(True{}, String.drop(s, 1n+n))
    case False{} True{}:
      url.after(False{}, String.drop(s, n))
    case False{} False{}:
      Fail{"not a URL of this scheme"}

# the scheme: http:// or https:// (ws:// or wss:// when ws)
def url.of(ws: Bool, +low: Bytes(), +s: Bytes()) -> Result<&2, &2, Bytes(), Url>:
  match ws:
    case False{}:
      url.scheme(Bytes.starts_with(low, "https://"), Bytes.starts_with(low, "http://"), 7n, s)
    case True{}:
      url.scheme(Bytes.starts_with(low, "wss://"), Bytes.starts_with(low, "ws://"), 5n, s)

def url.clean(+s: Bytes()) -> Result<&2, &2, Bytes(), Url>:
  url.of(False{}, lower.all(String.take(s, 8n)), s)

# an absolute http or https URL, or why it is refused
def parse(s: Bytes()) -> Result<&2, &2, Bytes(), Url>:
  url.clean(input(s))

# an absolute ws or wss URL, read the same way (tls says wss)
def parse.ws(s: Bytes()) -> Result<&2, &2, Bytes(), Url>:
  +t = input(s)
  url.of(True{}, lower.all(String.take(t, 8n)), t)

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

