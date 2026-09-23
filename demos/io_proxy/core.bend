# bend-proxy's core: what the proxy reads from a client, what it sends
# upstream, and what it sends back -- all of it pure, so the laws speak of
# the very functions the server runs.
#
# A client's stream is framed by the HTTP engine's reader
# (demos/io_http_engine, held to spec.bend's frame() by frame_sim), fed
# each read whole by its block walk (feed_buf, the byte machine by
# feed_buf_is_feed). Each request it completes carries its head as
# spec.bend's views read it (the method's bytes, the field lines it
# passes on, each name lowercased and its value as it came, and the
# members of every Connection: hd_framed), and the proxy forwards a
# request it builds from that -- never the bytes that came: the request
# line rebuilt, the fields re-emitted one per line, the hop-by-hop ones
# gone, one Host, one Content-Length counted from the framed body. The
# response comes back through wire/client.bend (wire/http1/resp.bend's
# reader, held to wire/http1/spec.bend) and goes out the same way:
# rebuilt, never passed through.
import Base
import ../../wire/reader.bend as Wr
import ../io_http_engine/main.bend as Eng
import ../io_http_engine/spec.bend as Spec
import ../../wire/http1/resp.bend as R
import ../../wire/http1/spec.bend as RS

# Scanning requests
# =================
#
# The reader the requests are read by, and a bound on how much of a
# head it may be holding: the bytes read since the last read that
# completed a request (a head in progress began in that read or after).
type Scan is Data:
  Scan{p: Eng.P, n: Nat}

def scan.new() -> Scan:
  Scan{Eng.p.new(), 0n}

# How a read ends: waiting for more (the scan to go on with), refused,
# or after a request that asked to upgrade (the connection's last).
type Tail is Data:
  TWait{s: Scan}
  TBad{}
  TUp{}

type Scanned is Data:
  Scanned{took: List<&2, Eng.Req>, tail: Tail}

def tail.of(st: Eng.St, pd: Eng.Pend, +n: Nat) -> Tail:
  match st:
    case Eng.Bad{}:
      TBad{}
    case Eng.Rest{bs}:
      TUp{}
    case _:
      TWait{Scan{Eng.P{st, pd, Nil{}}, n}}

# the bytes of a head so far: the read's, when it completed a request,
# else the ones before too
def head.n(out: List<&2, Eng.Req>, +n: Nat, +k: Nat) -> List<&2, Eng.Req> & Nat:
  match out:
    case Nil{}:
      (Nil{}, Nat.add(n, k))
    case Con{r, t}:
      (Con{r, t}, k)

def scan.took(st: Eng.St, pd: Eng.Pend, on: List<&2, Eng.Req> & Nat) -> Scanned:
  (out, +n) = on
  Scanned{List.reverse(&2, Eng.Req, out), tail.of(st, pd, n)}

def scan.fed(p: Eng.P, +n: Nat, +k: Nat) -> Scanned:
  match p:
    case Eng.P{st, pd, out}:
      scan.took(st, pd, head.n(out, n, k))

# a read, from where the last one left the reader: the requests it
# completed, oldest first, and how it ends; the reader goes on holding
# none of them
def scan(+s: Bytes(), sc: Scan) -> Scanned:
  match sc:
    case Scan{p, +n}:
      scan.fed(Eng.feed_buf(s, p), n, Bytes.len(s))

# The fields a hop owns
# =====================
#
# Hop-by-hop fields (RFC 9110 7.6.1) belong to one connection and are
# never forwarded: Connection and every field it names, and Keep-Alive,
# Proxy-Connection, TE, Transfer-Encoding, Upgrade and Trailer whether
# it names them or not.
def hop.fixed(+n: Bytes()) -> Bool:
  Eng.bytes.eq(n, "connection") || Eng.bytes.eq(n, "keep-alive") || Eng.bytes.eq(n, "proxy-connection")
    || Eng.bytes.eq(n, "te") || Eng.bytes.eq(n, "transfer-encoding") || Eng.bytes.eq(n, "upgrade")
    || Eng.bytes.eq(n, "trailer")

def in.names(+n: Bytes(), ns: List<&2, Bytes()>) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case Con{x, t}:
      Eng.bytes.eq(n, x) || in.names(n, t)

def hop(+ns: List<&2, Bytes()>, +n: Bytes()) -> Bool:
  hop.fixed(n) || in.names(n, ns)

# The request forwarded
# =====================
#
# What the proxy sends upstream: the method and target as they were
# read, the Host, the fields it chose -- the end-to-end fields in the
# order they came, then X-Forwarded-For, -Proto, -Host and Via -- and the
# body the reader framed, with a Content-Length counted from it when the
# request had a body's framing (a length or a coding) or has a body.
type Msg is Data:
  Msg{meth: Bytes(), target: Bytes(), host: Bytes(), fields: List<&2, Wr.Field>, body: Bytes(), framed: Bool}

def full(s: Bytes()) -> Bool:
  Bool.not(String.is_empty(s))

# What the proxy adds: the Host to send ("" keeps the client's), the
# scheme the client came in on, the client's address, and this hop's
# name for Via.
type Fwd is Data:
  Fwd{host: Bytes(), proto: Bytes(), ip: Bytes(), via: Bytes()}

# the fields forwarded as they came: not a hop's, not one the proxy
# writes itself (Host, Content-Length, Expect, the X-Forwarded ones),
# and none spec.bend's framing reads (field() names them all, so a
# forwarded field is always FOther to the next hop)
def own(+n: Bytes()) -> Bool:
  Eng.bytes.eq(n, "expect") || Eng.bytes.eq(n, "x-forwarded-for") || Eng.bytes.eq(n, "x-forwarded-proto")
    || Eng.bytes.eq(n, "x-forwarded-host")

def is.other(f: Eng.Fld) -> Bool:
  match f:
    case Eng.FOther{}:
      True{}
    case _:
      False{}

def keeps(+ns: List<&2, Bytes()>, +n: Bytes()) -> Bool:
  is.other(Eng.fld.of(n)) && Bool.not(hop(ns, n)) && Bool.not(own(n))

def ends.put(k: Bool, f: Wr.Field, r: List<&2, Wr.Field>) -> List<&2, Wr.Field>:
  match k:
    case True{}:
      Con{f, r}
    case False{}:
      r

def ends(+ns: List<&2, Bytes()>, fs: List<&2, Wr.Field>) -> List<&2, Wr.Field>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{f, t}:
      match f:
        case Wr.Field{+n, v}:
          ends.put(keeps(ns, n), Wr.Field{n, v}, ends(ns, t))

def values.put(k: Bool, v: Bytes(), r: List<&2, Bytes()>) -> List<&2, Bytes()>:
  match k:
    case True{}:
      Con{v, r}
    case False{}:
      r

# the values of every field named n, in order
def values(+n: Bytes(), fs: List<&2, Wr.Field>) -> List<&2, Bytes()>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{f, t}:
      match f:
        case Wr.Field{+m, v}:
          values.put(Eng.bytes.eq(n, m), v, values(n, t))

def join.more(t: List<&2, Bytes()>, x: Bytes()) -> Bytes():
  match t:
    case Nil{}:
      x
    case Con{y, u}:
      Bytes.concat([x, ", ", join.more(u, y)])

def join(xs: List<&2, Bytes()>) -> Bytes():
  match xs:
    case Nil{}:
      ""
    case Con{x, t}:
      join.more(t, x)

def first(xs: List<&2, Bytes()>, d: Bytes()) -> Bytes():
  match xs:
    case Nil{}:
      d
    case Con{x, t}:
      x

# the Host sent: the configured one, else the client's
def host.pick(+cfg: Bytes(), got: Bytes()) -> Bytes():
  Bool.pick(Bytes(), String.is_empty(cfg), got, cfg)

def has(xs: List<&2, Bytes()>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, t}:
      True{}

# a value's whitespace at either end cut (RFC 9110 5.5: no part of it)
def ows(+c: U32) -> Bool:
  U32.is_eq(c, 32) || U32.is_eq(c, 9)

# the value after its leading whitespace: cut says the byte before x
# (prev) was whitespace
def trim.lead(x: Bytes(), cut: Bool, +prev: U32) -> Bytes():
  match x cut:
    case _ False{}:
      SCon{Chr{prev}, x}
    case SNil{} True{}:
      SNil{}
    case SCon{Chr{+c}, t} True{}:
      trim.lead(t, ows(c), c)

# how many bytes to keep of s so that its last is no whitespace: ws
# says the byte at k is whitespace
def trim.end(k: Nat, +s: Bytes(), ws: Bool) -> Nat:
  match k ws:
    case _ False{}:
      1n+k
    case 0n True{}:
      0n
    case 1n+(+j) True{}:
      trim.end(j, s, ows(Bytes.get(s, j)))

def trim.cut(n: Nat, +s: Bytes()) -> Bytes():
  match n:
    case 0n:
      ""
    case 1n+(+j):
      String.take(s, trim.end(j, s, ows(Bytes.get(s, j))))

def trim(s: Bytes()) -> Bytes():
  +t = trim.lead(s, True{}, 0)
  trim.cut(Bytes.len(t), t)

def trims(fs: List<&2, Wr.Field>) -> List<&2, Wr.Field>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{f, t}:
      match f:
        case Wr.Field{n, v}:
          Con{Wr.Field{n, trim(v)}, trims(t)}

# a request's framing: whether it carries a body's length whatever its
# body (every method but GET and HEAD, which go up with none when empty)
def framed(+meth: Bytes()) -> Bool:
  Bool.not(Eng.bytes.eq(meth, "GET") || Eng.bytes.eq(meth, "HEAD"))

# what a request's head said, as the reader read it, and its target and
# body: the request to send
def msg.of(+w: Fwd, hd: Eng.Hd, target: Bytes(), body: Bytes()) -> Msg:
  match w hd:
    case Fwd{host, proto, +ip, via} Eng.Hd{+meth, v10, fs0, +cn}:
      +fs = trims(fs0)
      +got = first(values("host", fs), "")
      +xff = values("x-forwarded-for", fs)
      Msg{meth, target, host.pick(host, got),
        List.append(&2, Wr.Field, ends(cn, fs),
          [Wr.Field{"x-forwarded-for", join(List.append(&2, Bytes(), xff, [ip]))},
           Wr.Field{"x-forwarded-proto", proto},
           Wr.Field{"x-forwarded-host", got},
           Wr.Field{"via", via}]),
        body, framed(meth)}

# Writing it
# ----------

# a field line, and the lines of a head, each ended by CR LF
def fl.ser(f: Wr.Field) -> Bytes():
  match f:
    case Wr.Field{n, v}:
      Bytes.append(n, Bytes.append(": ", v))

def fls.ser(fs: List<&2, Wr.Field>) -> Bytes():
  match fs:
    case Nil{}:
      ""
    case Con{f, t}:
      Bytes.append(fl.ser(f), Bytes.append("\r\n", fls.ser(t)))

# a length is sent when the request had a body's framing or has a body
def clen.on(framed: Bool, body: Bytes()) -> Bool:
  framed || full(body)

def clf.at(on: Bool, +body: Bytes()) -> List<&2, Wr.Field>:
  match on:
    case True{}:
      [Wr.Field{"content-length", Nat.show(Bytes.len(body))}]
    case False{}:
      Nil{}

# the fields that go upstream: Host, the rest, the length
def allf(host: Bytes(), fs: List<&2, Wr.Field>, +framed: Bool, +body: Bytes()) -> List<&2, Wr.Field>:
  Con{Wr.Field{"host", host}, List.append(&2, Wr.Field, fs, clf.at(clen.on(framed, body), body))}

def rl.ser(meth: Bytes(), target: Bytes()) -> Bytes():
  Bytes.append(meth, Bytes.append(" ", Bytes.append(target, " HTTP/1.1")))

# the bytes that go upstream: the request line rebuilt, a field a line,
# the blank line, the body
def ser(m: Msg) -> Bytes():
  match m:
    case Msg{meth, target, host, fs, +body, +framed}:
      Bytes.append(rl.ser(meth, target),
        Bytes.append("\r\n", Bytes.append(fls.ser(allf(host, fs, framed, body)), Bytes.append("\r\n", body))))

# What the upstream's framing needs of a request to read back exactly
# it (LAWS.bend's no_smuggle), checked before it goes: a method of token
# bytes, a target with no space or control, field names of token bytes
# that no framing reads (spec.bend's field() calls every one FOther, so
# none is a length, a coding, a Connection, an Upgrade, a key or a
# Host), values with no line end or control, and a Content-Length that
# spec.bend reads back as the body's length. A request the reader took
# always passes (its bytes came through the same grammar); a check that
# failed would send the client a 502 rather than the upstream a request.
# every byte one the token holds, a byte at a time
def ok.each(+t: Spec.Tok, s: Bytes()) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{Chr{+c}, r}:
      Spec.allows(t, Eng.cls(c)) && ok.each(t, r)

# every byte of s in [lo, hi), by the buffer's own scan
def all.in(+s: Bytes(), lo: U32, hi: U32) -> Bool:
  Nat.is_eq(Bytes.span(s, 0n, lo, hi), Bytes.len(s))

# a range of bytes each token holds, taken at once: a method's capitals,
# a target's visible ASCII, a name's small letters, a value's space and
# visible ASCII (the common case); the rest is checked a byte at a time
def ok.fast(t: Spec.Tok, +s: Bytes()) -> Bool:
  match t:
    case Spec.TMeth{}:
      all.in(s, 65, 91)
    case Spec.TTarget{}:
      all.in(s, 33, 127)
    case Spec.TName{}:
      all.in(s, 97, 123)
    case Spec.TVal{}:
      all.in(s, 32, 127)
    case _:
      False{}

def ok.all.at(fast: Bool, +t: Spec.Tok, s: Bytes()) -> Bool:
  match fast:
    case True{}:
      True{}
    case False{}:
      ok.each(t, s)

def ok.all(+t: Spec.Tok, +s: Bytes()) -> Bool:
  ok.all.at(ok.fast(t, s), t, s)

def ok.field(f: Wr.Field) -> Bool:
  match f:
    case Wr.Field{+n, +v}:
      full(n) && ok.all(Spec.TName{}, n) && is.other(Eng.fld.of(Eng.lows(n))) && ok.all(Spec.TVal{}, v)

def ok.fields(fs: List<&2, Wr.Field>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case Con{f, t}:
      ok.field(f) && ok.fields(t)

def same(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      b
    case False{}:
      Bool.not(b)

# the length spec.bend reads from a Content-Length's value: the one the
# body has, zero exactly when it is empty
def ok.len.at(v: Spec.FLine, +body: Bytes()) -> Bool:
  match v:
    case Spec.FVal{val}:
      match val:
        case Spec.VLen{+n, ws}:
          same(U32.is_zero(n), String.is_empty(body)) && Nat.is_eq(U32.to_nat(n), Bytes.len(body))
        case _:
          False{}
    case _:
      False{}

def ok.len.on(on: Bool, +body: Bytes()) -> Bool:
  match on:
    case False{}:
      String.is_empty(body)
    case True{}:
      +d = Nat.show(Bytes.len(body))
      ok.all(Spec.TVal{}, d) && ok.len.at(Spec.len.view(Spec.span(Spec.TOws{}, Con{32, Bytes.to_list(d)})), body)

def valid(m: Msg) -> Bool:
  match m:
    case Msg{+meth, +target, +host, fs, +body, +framed}:
      full(meth) && ok.all(Spec.TMeth{}, meth) && full(target) && ok.all(Spec.TTarget{}, target)
        && ok.all(Spec.TVal{}, host) && ok.fields(fs) && ok.len.on(clen.on(framed, body), body)

# What goes upstream for the requests taken: each one rebuilt from its
# head, its target and its framed body, and checked; one that fails the
# check (never, for a request the reader took) goes nowhere, and neither
# does any after it.
def checked(+m: Msg) -> Maybe<&2, Msg>:
  Bool.pick(Maybe<&2, Msg>, valid(m), Some{m}, None{})

def fwd(+w: Fwd, r: Eng.Req) -> Maybe<&2, Msg>:
  match r:
    case Eng.Req{meth, path, body, close, ws, key, hd}:
      checked(msg.of(w, hd, path, body))

def wire.at(m: Maybe<&2, Msg>, rest: Bytes()) -> Bytes():
  match m:
    case Some{x}:
      Bytes.append(ser(x), rest)
    case None{}:
      ""

def wire(+w: Fwd, ts: List<&2, Eng.Req>) -> Bytes():
  match ts:
    case Nil{}:
      ""
    case Con{t, r}:
      wire.at(fwd(w, t), wire(w, r))

# The response sent back
# ======================
#
# What came back is read from the bytes the exchange read, which the
# response reader framed (so every line ends in CR LF, the status line
# is HTTP/1.x, three digits and a reason, and every field line is a name
# of token bytes, a colon and a value): the interim responses' heads
# skipped (the reader counted them), the final one's lines cut at their
# CR LFs with the buffer's own scans, never a byte at a time.

# where the first blank line (CR LF CR LF) begins, or the end
def blank(+s: Bytes()) -> Nat:
  Maybe.default(&2, Nat, String.find(s, "\r\n\r\n"), Bytes.len(s))

# the final head after k interim ones, up to its blank line
def rfinal(k: Nat, +s: Bytes()) -> Bytes():
  match k:
    case 0n:
      String.take(s, blank(s))
    case 1n+j:
      rfinal(j, String.drop(s, Nat.add(blank(s), 4n)))

# a status line's code and reason
type Stat is Data:
  Stat{code: Bytes(), why: Bytes()}

# after "HTTP/1.x ": three digits, and the reason after a space
def status.of(+line: Bytes()) -> Maybe<&2, Stat>:
  +n = Bytes.len(line)
  Bool.pick(Maybe<&2, Stat>, Nat.is_lt(n, 12n), None{},
    Bool.pick(Maybe<&2, Stat>, Nat.is_eq(n, 12n) || U32.is_eq(Bytes.get(line, 12n), 32),
      Some{Stat{String.slice(line, 9n, 12n), String.drop(line, 13n)}}, None{}))

# a field line: its name, lowercased, and its value, trimmed
def field.cut(+line: Bytes(), +i: Nat) -> Maybe<&2, Wr.Field>:
  Bool.pick(Maybe<&2, Wr.Field>, Nat.is_lt(i, Bytes.len(line)),
    Some{Wr.Field{String.to_lower(String.take(line, i)), trim(String.drop(line, 1n+i))}}, None{})

def field.of(+line: Bytes()) -> Maybe<&2, Wr.Field>:
  field.cut(line, Bytes.find_byte(line, 0n, 58))

def fields.put(f: Maybe<&2, Wr.Field>, r: Maybe<&2, List<&2, Wr.Field>>) -> Maybe<&2, List<&2, Wr.Field>>:
  match f r:
    case Some{x} Some{xs}:
      Some{Con{x, xs}}
    case _ _:
      None{}

def fields.of(ls: List<&2, Bytes()>) -> Maybe<&2, List<&2, Wr.Field>>:
  match ls:
    case Nil{}:
      Some{Nil{}}
    case Con{+l, t}:
      fields.put(field.of(l), fields.of(t))

# a buffer cut at every byte x, the pieces in order (k bounds the cuts;
# the byte after x, the LF of a CR LF, is skipped with it when skip is 2)
def cut.at(k: Nat, found: Bool, +s: Bytes(), +i: Nat, +x: U32, +skip: Nat) -> List<&2, Bytes()>:
  match k found:
    case 0n _:
      [s]
    case _ False{}:
      [s]
    case 1n+j True{}:
      +t = String.drop(s, Nat.add(i, skip))
      Con{String.take(s, i), cut.at(j, Nat.is_lt(Bytes.find_byte(t, 0n, x), Bytes.len(t)), t,
        Bytes.find_byte(t, 0n, x), x, skip)}

def cut(+s: Bytes(), +x: U32, +skip: Nat) -> List<&2, Bytes()>:
  +i = Bytes.find_byte(s, 0n, x)
  cut.at(Bytes.len(s), Nat.is_lt(i, Bytes.len(s)), s, i, x, skip)

# the field lines after the status line (none when it is alone)
def rlines.at(e: Bool, +rest: Bytes()) -> List<&2, Bytes()>:
  match e:
    case True{}:
      Nil{}
    case False{}:
      cut(rest, 13, 2n)

def rlines(+rest: Bytes()) -> List<&2, Bytes()>:
  rlines.at(String.is_empty(rest), rest)

# a list's members (RFC 9110 5.6.1): split at commas, each trimmed and
# lowercased, the empty ones dropped
def mem.keep.at(e: Bool, +m: Bytes(), ms: List<&2, Bytes()>) -> List<&2, Bytes()>:
  match e:
    case True{}:
      ms
    case False{}:
      Con{String.to_lower(m), ms}

def mem.keep(+m: Bytes(), ms: List<&2, Bytes()>) -> List<&2, Bytes()>:
  mem.keep.at(String.is_empty(m), m, ms)

def mem.go(xs: List<&2, Bytes()>) -> List<&2, Bytes()>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      mem.keep(trim(x), mem.go(t))

def members(+v: Bytes()) -> List<&2, Bytes()>:
  mem.go(cut(v, 44, 1n))

# every name a Connection field names
def conn.names.at(yes: Bool, +v: Bytes(), rest: List<&2, Bytes()>) -> List<&2, Bytes()>:
  match yes:
    case True{}:
      List.append(&2, Bytes(), members(v), rest)
    case False{}:
      rest

def conn.names(fs: List<&2, Wr.Field>) -> List<&2, Bytes()>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{f, t}:
      match f:
        case Wr.Field{+n, +v}:
          conn.names.at(Eng.bytes.eq(n, "connection"), v, conn.names(t))

# the fields a response carries on: not a hop's, not its framing (the
# proxy frames it again), not Content-Length unless len (the laws of
# hop_by_hop_removed_rsp hold either way; the proxy passes False and
# sends a length of its own)
def rkeeps(+ns: List<&2, Bytes()>, +len: Bool, +n: Bytes()) -> Bool:
  Bool.not(hop(ns, n)) && (len || Bool.not(Eng.bytes.eq(n, "content-length")))

def rends(+ns: List<&2, Bytes()>, +len: Bool, fs: List<&2, Wr.Field>) -> List<&2, Wr.Field>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{f, t}:
      match f:
        case Wr.Field{+n, v}:
          ends.put(rkeeps(ns, len, n), Wr.Field{n, v}, rends(ns, len, t))

# What the final response's head said: the status's three digits and
# its reason, the end-to-end fields (the Via added), and the upstream's
# Content-Length ("" for none), which a response to HEAD carries on.
type RHead is Data:
  RHead{code: Bytes(), why: Bytes(), fields: List<&2, Wr.Field>, hlen: Bytes()}

def rhead.mk(+via: Bytes(), cw: Stat, +xs: List<&2, Wr.Field>) -> RHead:
  match cw:
    case Stat{code, why}:
      RHead{code, why, List.append(&2, Wr.Field, rends(conn.names(xs), False{}, xs), [Wr.Field{"via", via}]),
        first(values("content-length", xs), "")}

def rhead.at(+via: Bytes(), st: Maybe<&2, Stat>, fs: Maybe<&2, List<&2, Wr.Field>>) -> Maybe<&2, RHead>:
  match st fs:
    case Some{cw} Some{xs}:
      Some{rhead.mk(via, cw, xs)}
    case _ _:
      None{}

# the final head's status line and field lines, read
def rhead.of(+via: Bytes(), +h: Bytes()) -> Maybe<&2, RHead>:
  +e = Bytes.find_byte(h, 0n, 13)
  rhead.at(via, status.of(String.take(h, e)), fields.of(rlines(String.drop(h, Nat.add(e, 2n)))))

# A response, as the proxy sends it: the code and reason, the fields,
# the Content-Length it sends ("" for none), the body, and whether it
# has none by its framing: an answer to HEAD, a 204, a 304 (RFC 9112
# 6.3; a 1xx is never final here, and a 101 is refused).
type Rsp is Data:
  Rsp{code: Bytes(), why: Bytes(), fields: List<&2, Wr.Field>, clen: Bytes(), body: Bytes(), bodyless: Bool}

def rbodyless(+head: Bool, +code: U32) -> Bool:
  head || U32.is_eq(code, 204) || U32.is_eq(code, 304)

# the length sent: the body's; for HEAD the upstream's, what a GET
# would have sent; for 204 and 304 none
def rclen(+head: Bool, bodyless: Bool, hlen: Bytes(), +body: Bytes()) -> Bytes():
  match bodyless:
    case False{}:
      Nat.show(Bytes.len(body))
    case True{}:
      Bool.pick(Bytes(), head, hlen, "")

def rsp.fin(+head: Bool, +code: U32, h: RHead, +body: Bytes()) -> Rsp:
  match h:
    case RHead{cd, why, fs, hlen}:
      +bl = rbodyless(head, code)
      Rsp{cd, why, fs, rclen(head, bl, hlen, body), body, bl}

# What the client's reading (wire/http1/spec.bend's response(), with
# the reader's largest body cap) needs of a response to read back
# exactly it (LAWS.bend's rsp_reframed): a code of three digits, 200 to
# 599, the one the reader read; a reason and values with no line end or
# control; field names of token bytes that its framing never reads (so
# none is a length, a coding or a Connection); and a Content-Length it
# reads as the body's length, under the cap. A response that fails goes
# back as a 502, never as bytes a client could frame otherwise.
def rask(head: Bool) -> R.Ask:
  R.Ask{head, 268435455}

def rok.each(+t: RS.Tok, s: Bytes()) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{Chr{+c}, r}:
      RS.allows(t, R.cls(c)) && rok.each(t, r)

# as for a request: a name's small letters and a value's space and
# visible ASCII at once
def rok.fast(t: RS.Tok, +s: Bytes()) -> Bool:
  match t:
    case RS.TName{}:
      all.in(s, 97, 123)
    case RS.TVal{}:
      all.in(s, 32, 127)
    case _:
      False{}

def rok.all.at(fast: Bool, +t: RS.Tok, s: Bytes()) -> Bool:
  match fast:
    case True{}:
      True{}
    case False{}:
      rok.each(t, s)

def rok.all(+t: RS.Tok, +s: Bytes()) -> Bool:
  rok.all.at(rok.fast(t, s), t, s)

def ris.other(f: RS.Fld) -> Bool:
  match f:
    case RS.FOther{}:
      True{}
    case _:
      False{}

def rok.field(f: Wr.Field) -> Bool:
  match f:
    case Wr.Field{+n, +v}:
      full(n) && rok.all(RS.TName{}, n) && ris.other(RS.field(RS.lows(Bytes.to_list(n)))) && rok.all(RS.TVal{}, v)

def rok.fields(fs: List<&2, Wr.Field>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case Con{f, t}:
      rok.field(f) && rok.fields(t)

def rok.code(+cd: Bytes(), +code: U32) -> Bool:
  rok.all(RS.TDig{}, cd) && RS.code.whole(Bytes.to_list(cd)) && U32.is_eq(RS.num(Bytes.to_list(cd)), code)
    && Bool.not(U32.is_lt(code, 200)) && Bool.not(U32.is_eq(code, 101))

def rok.len.at(v: RS.FLine, +bodyless: Bool, +body: Bytes()) -> Bool:
  match v:
    case RS.FVal{val}:
      match val:
        case RS.VLen{+n, ws}:
          Bool.not(U32.is_lt(268435455, n)) && (bodyless ||
            (same(U32.is_zero(n), String.is_empty(body)) && Nat.is_eq(U32.to_nat(n), Bytes.len(body))))
        case _:
          False{}
    case _:
      False{}

def rok.len(+head: Bool, +bodyless: Bool, clen: Bytes(), +body: Bytes()) -> Bool:
  match clen:
    case SNil{}:
      bodyless
    case SCon{c, t}:
      +d : Bytes() = SCon{c, t}
      rok.all(RS.TVal{}, d) && rok.len.at(RS.len.view(rask(head), RS.span(RS.TOws{}, Con{32, Bytes.to_list(d)})), bodyless, body)

def rvalid(+head: Bool, +code: U32, r: Rsp) -> Bool:
  match r:
    case Rsp{+cd, +why, fs, +clen, +body, +bodyless}:
      rok.code(cd, code) && rok.all(RS.TVal{}, why) && rok.fields(fs) && rok.len(head, bodyless, clen, body)

def rcheck(+head: Bool, +code: U32, +r: Rsp) -> Maybe<&2, Rsp>:
  Bool.pick(Maybe<&2, Rsp>, rvalid(head, code, r), Some{r}, None{})

def rsp.at(+head: Bool, +code: U32, mh: Maybe<&2, RHead>, +body: Bytes()) -> Maybe<&2, Rsp>:
  match mh:
    case Some{h}:
      rcheck(head, code, rsp.fin(head, code, h, body))
    case None{}:
      None{}

# the response to send back, from what the exchange read: the bytes of
# k interim heads and the final one's (got), the status and body the
# reader read; head says the request was HEAD
def rsp.of(+via: Bytes(), +head: Bool, +k: Nat, +code: U32, +got: Bytes(), +body: Bytes()) -> Maybe<&2, Rsp>:
  rsp.at(head, code, rhead.of(via, rfinal(k, got)), body)

# the bytes that go back: the status line rebuilt, a field a line, the
# length, the connection's fate (conn: a Connection value, or "" for
# none), the blank line, and the body unless the framing says none
def rclf(clen: Bytes()) -> List<&2, Wr.Field>:
  match clen:
    case SNil{}:
      Nil{}
    case SCon{c, t}:
      [Wr.Field{"content-length", SCon{c, t}}]

def rconf(+conn: Bytes()) -> List<&2, Wr.Field>:
  Bool.pick(List<&2, Wr.Field>, String.is_empty(conn), Nil{}, [Wr.Field{"connection", conn}])

def rall(fs: List<&2, Wr.Field>, clen: Bytes(), +conn: Bytes()) -> List<&2, Wr.Field>:
  List.append(&2, Wr.Field, fs, List.append(&2, Wr.Field, rclf(clen), rconf(conn)))

def sl.ser(code: Bytes(), why: Bytes()) -> Bytes():
  Bytes.append("HTTP/1.1 ", Bytes.append(code, Bytes.append(" ", why)))

def rser(r: Rsp, +conn: Bytes()) -> Bytes():
  match r:
    case Rsp{code, why, fs, clen, +body, +bodyless}:
      Bytes.append(sl.ser(code, why),
        Bytes.append("\r\n", Bytes.append(fls.ser(rall(fs, clen, conn)),
          Bytes.append("\r\n", Bool.pick(Bytes(), bodyless, "", body)))))

# the Connection a response goes back with: close when the connection
# ends after it; keep-alive to an HTTP/1.0 client that stays
def conn.val(closing: Bool, v10: Bool) -> Bytes():
  match closing:
    case True{}:
      "close"
    case False{}:
      Bool.pick(Bytes(), v10, "keep-alive", "")

# A reply of the proxy's own, when there is no response to send back:
# 400 for a request it refused, 431 for a head past its cap, 502 when
# the upstream could not be reached or answered with nothing it could
# frame, 504 when the upstream ran out its deadline. It closes.
# (to HEAD, the length said and no body)
def own.reply.at(+head: Bool, status: Bytes(), +body: Bytes()) -> Bytes():
  Bytes.concat(["HTTP/1.1 ", status, "\r\ncontent-type: text/plain\r\ncontent-length: ",
    Nat.show(Bytes.len(body)), "\r\nconnection: close\r\n\r\n", Bool.pick(Bytes(), head, "", body)])

def own.reply(status: Bytes(), +body: Bytes()) -> Bytes():
  own.reply.at(False{}, status, body)

# what goes back for a request forwarded: the response rebuilt, or, when
# there is none the proxy can send, its own 502
def reply(m: Maybe<&2, Rsp>, +head: Bool, +closing: Bool, +v10: Bool) -> Bytes():
  match m:
    case Some{r}:
      rser(r, conn.val(closing, v10))
    case None{}:
      own.reply.at(head, "502 Bad Gateway", "502 Bad Gateway\n")
