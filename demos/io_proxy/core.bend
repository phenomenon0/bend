# bend-proxy's core: what the proxy reads from a client, what it sends
# upstream, and what it sends back -- all of it pure, so the laws speak of
# the very functions the server runs.
#
# A request is framed by the HTTP engine's reader (demos/io_http_engine,
# held to spec.bend's frame() by frame_sim), stepped a byte at a time from
# a fresh reader until it completes one: the bytes it took are the
# request's, exactly, and a fresh reader takes the bytes after them. Its
# head is read again from those bytes by spec.bend's own views (the
# request line split at its spaces, a field line at its colon, the name
# lowercased, the value trimmed), and the proxy forwards a request it
# builds from what was read -- never the bytes that came: the request
# line rebuilt, the fields re-emitted one per line, the hop-by-hop ones
# gone, one Host, one Content-Length counted from the framed body. The
# response comes back through wire/client.bend (wire/http1/resp.bend's
# reader, held to wire/http1/spec.bend) and goes out the same way:
# rebuilt, never passed through.
import Base
import ../../wire/reader.bend as Wr
import ../io_http_engine/main.bend as Eng
import ../io_http_engine/spec.bend as Spec

# Scanning requests
# =================
#
# The reader since the last request completed, and the bytes it took.
type Scan is Data:
  Scan{p: Eng.P, raw: Bytes()}

def scan.new() -> Scan:
  Scan{Eng.p.new(), ""}

# What one byte left: still reading (the reader, the bytes so far); a
# request completed on it (its bytes, and the request); one that asked
# to upgrade completed on it; or the reader refused.
type Stp is Data:
  SGo{p: Eng.P, raw: Bytes()}
  SMsg{raw: Bytes(), r: Eng.Req}
  SUp{raw: Bytes(), r: Eng.Req}
  SBad{}

def stp.req(ws: Bool, raw: Bytes(), r: Eng.Req) -> Stp:
  match ws:
    case True{}:
      SUp{raw, r}
    case False{}:
      SMsg{raw, r}

def stp.st(st: Eng.St, pd: Eng.Pend, raw: Bytes()) -> Stp:
  match st:
    case Eng.Bad{}:
      SBad{}
    case _:
      SGo{Eng.P{st, pd, Nil{}}, raw}

def stp.out(st: Eng.St, pd: Eng.Pend, out: List<&2, Eng.Req>, raw: Bytes()) -> Stp:
  match out:
    case Con{+r, t}:
      stp.req(Eng.req.ws(r), raw, r)
    case Nil{}:
      stp.st(st, pd, raw)

def stp.of(p: Eng.P, raw: Bytes()) -> Stp:
  match p:
    case Eng.P{st, pd, out}:
      stp.out(st, pd, out, raw)

# one byte, stepped by the engine's reader
def stp(p: Eng.P, +c: U32, raw: Bytes()) -> Stp:
  stp.of(Eng.step(p, c), Bytes.push(raw, c))

# A request taken: its bytes, and what the reader read.
type Took is Data:
  Took{raw: Bytes(), r: Eng.Req}

# How a read ends: waiting for more (the scan to go on with), refused,
# or after a request that asked to upgrade (the connection's last).
type Tail is Data:
  TWait{s: Scan}
  TBad{}
  TUp{}

type Scanned is Data:
  Scanned{took: List<&2, Took>, tail: Tail}

def done(acc: List<&2, Took>, t: Tail) -> Scanned:
  Scanned{List.reverse(&2, Took, acc), t}

# the bytes of a read, a byte at a time; a completed request is taken,
# and a fresh reader takes the byte after it
def scan.go(+s: Bytes(), st: Stp, acc: List<&2, Took>) -> Scanned:
  match s st:
    case _ SBad{}:
      done(acc, TBad{})
    case _ SUp{raw, r}:
      done(Con{Took{raw, r}, acc}, TUp{})
    case SNil{} SGo{p, raw}:
      done(acc, TWait{Scan{p, raw}})
    case SNil{} SMsg{raw, r}:
      done(Con{Took{raw, r}, acc}, TWait{scan.new()})
    case SCon{Chr{c}, t} SGo{p, raw}:
      scan.go(t, stp(p, c, raw), acc)
    case SCon{Chr{c}, t} SMsg{raw, r}:
      scan.go(t, stp(Eng.p.new(), c, ""), Con{Took{raw, r}, acc})

# a read, from where the last one left the scan
def scan(+s: Bytes(), sc: Scan) -> Scanned:
  match sc:
    case Scan{p, raw}:
      scan.go(s, SGo{p, raw}, Nil{})

# Reading a head again
# ====================
#
# The lines of a head, from a request's bytes: the empty lines before
# its request line skipped (RFC 9112 2.2), then every line up to the
# empty one that ends the head. The reader took these bytes, so every
# line ends in CR LF and neither comes anywhere else in the head: a CR
# ends a line and an LF is passed over.
type HL is Data:
  HL{started: Bool, cur: List<&2, U32>, lines: List<&2, List<&2, U32>>}
  HDone{lines: List<&2, List<&2, U32>>}

def hl.cr(started: Bool, cur: List<&2, U32>, lines: List<&2, List<&2, U32>>) -> HL:
  match started cur:
    case True{} Nil{}:
      HDone{lines}
    case False{} Nil{}:
      HL{False{}, Nil{}, lines}
    case _ Con{h, t}:
      HL{True{}, Nil{}, Con{List.reverse(&2, U32, Con{h, t}), lines}}

def hl.at(cr: Bool, lf: Bool, started: Bool, cur: List<&2, U32>, lines: List<&2, List<&2, U32>>,
  c: U32) -> HL:
  match cr lf:
    case True{} _:
      hl.cr(started, cur, lines)
    case False{} True{}:
      HL{started, cur, lines}
    case False{} False{}:
      HL{started, Con{c, cur}, lines}

def hl.step(h: HL, +c: U32) -> HL:
  match h:
    case HL{started, cur, lines}:
      hl.at(U32.is_eq(c, 13), U32.is_eq(c, 10), started, cur, lines, c)
    case HDone{lines}:
      HDone{lines}

def hl.walk(+s: Bytes(), h: HL) -> List<&2, List<&2, U32>>:
  match s h:
    case _ HDone{lines}:
      List.reverse(&2, List<&2, U32>, lines)
    case SNil{} HL{started, cur, lines}:
      List.reverse(&2, List<&2, U32>, lines)
    case SCon{Chr{c}, t} HL{started, cur, lines}:
      hl.walk(t, hl.step(HL{started, cur, lines}, c))

def lines(+s: Bytes()) -> List<&2, List<&2, U32>>:
  hl.walk(s, HL{False{}, Nil{}, Nil{}})

# The views, fast
# ---------------
#
# spec.bend's own views of a line -- span, the request line, trim --
# with the engine's classes in place of the reference's (cls_every
# says they agree on every U32, and LAWS.bend that these are those).

def fspan(+t: Spec.Tok, bs: List<&2, U32>) -> Spec.Span:
  match bs:
    case Nil{}:
      Spec.Span{Nil{}, Spec.SEnd{}}
    case Con{+c, +rest}:
      +k = Eng.cls(c)
      Spec.span.pick(Spec.allows(t, k), k, c, rest, fspan(t, rest))

def fver(m: List<&2, U32>, t: List<&2, U32>, sp: Spec.Span) -> Spec.RLine:
  match sp:
    case Spec.Span{v, Spec.SEnd{}}:
      Spec.RVer{m, t, v}
    case Spec.Span{v, Spec.SAt{k, c, rest}}:
      Spec.RBad{}

def ftarget.sp(m: List<&2, U32>, t: List<&2, U32>, rest: List<&2, U32>) -> Spec.RLine:
  match t:
    case Nil{}:
      Spec.RBad{}
    case Con{h, r}:
      fver(m, Con{h, r}, fspan(Spec.TVer{}, rest))

def ftarget(m: List<&2, U32>, sp: Spec.Span) -> Spec.RLine:
  match sp:
    case Spec.Span{t, Spec.SEnd{}}:
      Spec.RTarget{m, t}
    case Spec.Span{t, Spec.SAt{Eng.KSp{}, c, rest}}:
      ftarget.sp(m, t, rest)
    case Spec.Span{t, Spec.SAt{k, c, rest}}:
      Spec.RBad{}

def fmeth(sp: Spec.Span) -> Spec.RLine:
  match sp:
    case Spec.Span{Nil{}, s}:
      Spec.RBad{}
    case Spec.Span{Con{h, r}, Spec.SEnd{}}:
      Spec.RMeth{Con{h, r}}
    case Spec.Span{Con{h, r}, Spec.SAt{Eng.KSp{}, c, rest}}:
      ftarget(Con{h, r}, fspan(Spec.TTarget{}, rest))
    case Spec.Span{m, Spec.SAt{k, c, rest}}:
      Spec.RBad{}

# spec.bend's req.view: a request line split at its spaces
def fview(x: List<&2, U32>) -> Spec.RLine:
  match x:
    case Nil{}:
      Spec.RNone{}
    case Con{c, t}:
      fmeth(fspan(Spec.TMeth{}, Con{c, t}))

def ftrim.lead(x: List<&2, U32>) -> List<&2, U32>:
  match x:
    case Nil{}:
      Nil{}
    case Con{+c, +t}:
      Spec.trim.lead.pick(Spec.ows(Eng.cls(c)), c, t, ftrim.lead(t))

def ftrim.end(x: List<&2, U32>) -> List<&2, U32>:
  match x:
    case Nil{}:
      Nil{}
    case Con{+c, t}:
      Spec.trim.end.pick(Spec.ows(Eng.cls(c)), c, ftrim.end(t))

# spec.bend's trim: whitespace at either end of a value cut
def ftrim(x: List<&2, U32>) -> List<&2, U32>:
  ftrim.end(ftrim.lead(x))

# A field as it was framed: its name lowercased, its value with the
# whitespace at either end cut (RFC 9110 5.5).
type Field is Data:
  Field{name: Bytes(), value: Bytes()}

# a field line split as spec.bend's field.view splits it: a name of
# token bytes and a colon at once
def field.at(sp: Spec.Span) -> Maybe<&2, Field>:
  match sp:
    case Spec.Span{Con{h, t}, Spec.SAt{Eng.KCo{}, c, v}}:
      Some{Field{Eng.lows(Bytes.from_list(Con{h, t})), Bytes.from_list(ftrim(v))}}
    case _:
      None{}

def field.of(line: List<&2, U32>) -> Maybe<&2, Field>:
  field.at(fspan(Spec.TName{}, line))

def fields.put(f: Maybe<&2, Field>, r: Maybe<&2, List<&2, Field>>) -> Maybe<&2, List<&2, Field>>:
  match f r:
    case Some{x} Some{xs}:
      Some{Con{x, xs}}
    case _ _:
      None{}

def fields.of(ls: List<&2, List<&2, U32>>) -> Maybe<&2, List<&2, Field>>:
  match ls:
    case Nil{}:
      Some{Nil{}}
    case Con{l, t}:
      fields.put(field.of(l), fields.of(t))

# A request's head, as it was framed: its method, its target, whether it
# was HTTP/1.0, and its fields in order.
type Head is Data:
  Head{meth: Bytes(), target: Bytes(), v10: Bool, fields: List<&2, Field>}

def head.at(r: Spec.RLine, fs: Maybe<&2, List<&2, Field>>) -> Maybe<&2, Head>:
  match r fs:
    case Spec.RVer{m, t, +v} Some{xs}:
      Some{Head{Bytes.from_list(m), Bytes.from_list(t), Eng.bytes.eq(Bytes.from_list(v), "HTTP/1.0"), xs}}
    case _ _:
      None{}

def head.lines(ls: List<&2, List<&2, U32>>) -> Maybe<&2, Head>:
  match ls:
    case Nil{}:
      None{}
    case Con{l, t}:
      head.at(fview(l), fields.of(t))

# the head of a request, read from its bytes
def head.of(+raw: Bytes()) -> Maybe<&2, Head>:
  head.lines(lines(raw))

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

# a list's members (RFC 9110 5.6.1): split at commas, each trimmed and
# lowercased, the empty ones dropped
def mem.put(m: List<&2, U32>, ms: List<&2, Bytes()>) -> List<&2, Bytes()>:
  match m:
    case Nil{}:
      ms
    case Con{h, t}:
      Con{Eng.lows(Bytes.from_list(Con{h, t})), ms}

def mem.at(comma: Bool, c: U32, cur: List<&2, U32>, ms: List<&2, Bytes()>) ->
  List<&2, U32> & List<&2, Bytes()>:
  match comma:
    case True{}:
      (Nil{}, mem.put(ftrim(List.reverse(&2, U32, cur)), ms))
    case False{}:
      (Con{c, cur}, ms)

def mem.go(v: List<&2, U32>, cm: List<&2, U32> & List<&2, Bytes()>) -> List<&2, Bytes()>:
  match v:
    case Nil{}:
      (cur, ms) = cm
      mem.put(ftrim(List.reverse(&2, U32, cur)), ms)
    case Con{+c, t}:
      (cur, ms) = cm
      mem.go(t, mem.at(U32.is_eq(c, 44), c, cur, ms))

def members(v: Bytes()) -> List<&2, Bytes()>:
  mem.go(Bytes.to_list(v), (Nil{}, Nil{}))

# every name a Connection field names
def conn.names.at(yes: Bool, v: Bytes(), rest: List<&2, Bytes()>) -> List<&2, Bytes()>:
  match yes:
    case True{}:
      List.append(&2, Bytes(), members(v), rest)
    case False{}:
      rest

def conn.names(fs: List<&2, Field>) -> List<&2, Bytes()>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{f, t}:
      match f:
        case Field{+n, v}:
          conn.names.at(Eng.bytes.eq(n, "connection"), v, conn.names(t))

# The request forwarded
# =====================
#
# What the proxy sends upstream: the method and target as they were
# read, the Host, the fields it chose -- the end-to-end fields in the
# order they came, then X-Forwarded-For, -Proto, -Host and Via -- and the
# body the reader framed, with a Content-Length counted from it when the
# request had a body's framing (a length or a coding) or has a body.
type Msg is Data:
  Msg{meth: Bytes(), target: Bytes(), host: Bytes(), fields: List<&2, Field>, body: Bytes(), framed: Bool}

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

def ends.put(k: Bool, f: Field, r: List<&2, Field>) -> List<&2, Field>:
  match k:
    case True{}:
      Con{f, r}
    case False{}:
      r

def ends(+ns: List<&2, Bytes()>, fs: List<&2, Field>) -> List<&2, Field>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{f, t}:
      match f:
        case Field{+n, v}:
          ends.put(keeps(ns, n), Field{n, v}, ends(ns, t))

def values.put(k: Bool, v: Bytes(), r: List<&2, Bytes()>) -> List<&2, Bytes()>:
  match k:
    case True{}:
      Con{v, r}
    case False{}:
      r

# the values of every field named n, in order
def values(+n: Bytes(), fs: List<&2, Field>) -> List<&2, Bytes()>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{f, t}:
      match f:
        case Field{+m, v}:
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

# a request's framing: whether its head had a length or a coding
def framed(+fs: List<&2, Field>) -> Bool:
  has(values("content-length", fs)) || has(values("transfer-encoding", fs))

def msg.of(+w: Fwd, h: Head, body: Bytes()) -> Msg:
  match w h:
    case Fwd{host, proto, +ip, via} Head{meth, target, v10, +fs}:
      +got = first(values("host", fs), "")
      +xff = values("x-forwarded-for", fs)
      Msg{meth, target, host.pick(host, got),
        List.append(&2, Field, ends(conn.names(fs), fs),
          [Field{"x-forwarded-for", join(List.append(&2, Bytes(), xff, [ip]))},
           Field{"x-forwarded-proto", proto},
           Field{"x-forwarded-host", got},
           Field{"via", via}]),
        body, framed(fs)}

# Writing it
# ----------

# a field line, and the lines of a head, each ended by CR LF
def fl.ser(f: Field) -> Bytes():
  match f:
    case Field{n, v}:
      Bytes.append(n, Bytes.append(": ", v))

def fls.ser(fs: List<&2, Field>) -> Bytes():
  match fs:
    case Nil{}:
      ""
    case Con{f, t}:
      Bytes.append(fl.ser(f), Bytes.append("\r\n", fls.ser(t)))

# a length is sent when the request had a body's framing or has a body
def clen.on(framed: Bool, body: Bytes()) -> Bool:
  framed || full(body)

def clf.at(on: Bool, +body: Bytes()) -> List<&2, Field>:
  match on:
    case True{}:
      [Field{"content-length", Nat.show(Bytes.len(body))}]
    case False{}:
      Nil{}

# the fields that go upstream: Host, the rest, the length
def allf(host: Bytes(), fs: List<&2, Field>, +framed: Bool, +body: Bytes()) -> List<&2, Field>:
  Con{Field{"host", host}, List.append(&2, Field, fs, clf.at(clen.on(framed, body), body))}

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
def ok.all(+t: Spec.Tok, s: Bytes()) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{Chr{+c}, r}:
      Spec.allows(t, Eng.cls(c)) && ok.all(t, r)

def ok.field(f: Field) -> Bool:
  match f:
    case Field{+n, +v}:
      full(n) && ok.all(Spec.TName{}, n) && is.other(Eng.fld.of(Eng.lows(n))) && ok.all(Spec.TVal{}, v)

def ok.fields(fs: List<&2, Field>) -> Bool:
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

# What goes upstream for the requests taken: each one's head read again
# from its bytes and the request rebuilt from it and the framed body; a
# request whose head does not read again (never, for bytes the reader
# took) goes nowhere, and neither does any after it.
def checked(+m: Msg) -> Maybe<&2, Msg>:
  Bool.pick(Maybe<&2, Msg>, valid(m), Some{m}, None{})

def fwd.at(+w: Fwd, m: Maybe<&2, Head>, r: Eng.Req) -> Maybe<&2, Msg>:
  match m r:
    case Some{h} Eng.Req{meth, path, body, close, ws, key}:
      checked(msg.of(w, h, body))
    case None{} _:
      None{}

def fwd(+w: Fwd, t: Took) -> Maybe<&2, Msg>:
  match t:
    case Took{+raw, r}:
      fwd.at(w, head.of(raw), r)

def wire.at(m: Maybe<&2, Msg>, rest: Bytes()) -> Bytes():
  match m:
    case Some{x}:
      Bytes.append(ser(x), rest)
    case None{}:
      ""

def wire(+w: Fwd, ts: List<&2, Took>) -> Bytes():
  match ts:
    case Nil{}:
      ""
    case Con{t, r}:
      wire.at(fwd(w, t), wire(w, r))

# The response sent back
# ======================
#
# What came back is read from the bytes the exchange read: the interim
# responses' heads skipped (the reader counted them), the final one's
# lines taken as a request's are. The status line is HTTP/1.x, a space,
# three digits, and the reason after a space if there is one.

# the lines of the head after k heads
type RL is Data:
  RL{k: Nat, h: HL}
  RDone{lines: List<&2, List<&2, U32>>}

def rl.next(h: HL, k: Nat) -> RL:
  match h k:
    case HDone{lines} 0n:
      RDone{List.reverse(&2, List<&2, U32>, lines)}
    case HDone{lines} 1n+j:
      RL{j, HL{False{}, Nil{}, Nil{}}}
    case HL{s, c, l} _:
      RL{k, HL{s, c, l}}

def rl.walk(+s: Bytes(), r: RL) -> List<&2, List<&2, U32>>:
  match s r:
    case _ RDone{lines}:
      lines
    case SNil{} RL{k, h}:
      Nil{}
    case SCon{Chr{c}, t} RL{k, h}:
      rl.walk(t, rl.next(hl.step(h, c), k))

def rlines(k: Nat, +s: Bytes()) -> List<&2, List<&2, U32>>:
  rl.walk(s, RL{k, HL{False{}, Nil{}, Nil{}}})

# A response, as the proxy sends it: the status's three digits and its
# reason, the end-to-end fields, the body, and whether it has none by
# its framing (a response to HEAD, 1xx, 204, 304: RFC 9112 6.3).
type Rsp is Data:
  Rsp{code: Bytes(), why: Bytes(), fields: List<&2, Field>, body: Bytes(), bodyless: Bool}

# a status line's code and reason
type Stat is Data:
  Stat{code: Bytes(), why: Bytes()}

# after "HTTP/1.x ": three digits, and the reason after a space
def status.why(r: List<&2, U32>) -> Maybe<&2, Bytes()>:
  match r:
    case Nil{}:
      Some{""}
    case Con{+sp, w}:
      Bool.pick(Maybe<&2, Bytes()>, U32.is_eq(sp, 32), Some{Bytes.from_list(w)}, None{})

def status.pair(code: Bytes(), w: Maybe<&2, Bytes()>) -> Maybe<&2, Stat>:
  match w:
    case Some{x}:
      Some{Stat{code, x}}
    case None{}:
      None{}

def status.code(d: List<&2, U32>) -> Maybe<&2, Stat>:
  match d:
    case Con{a, Con{b, Con{c, r}}}:
      status.pair(Bytes.from_list([a, b, c]), status.why(r))
    case _:
      None{}

def status.of(line: List<&2, U32>) -> Maybe<&2, Stat>:
  status.code(List.drop(&2, U32, line, 9n))

# the fields a response carries on: not a hop's, not its framing (the
# proxy frames it again), not Content-Length unless the response has no
# body by its framing and answers HEAD (where it says what GET would
# have sent, and nothing follows it)
def rkeeps(+ns: List<&2, Bytes()>, +len: Bool, +n: Bytes()) -> Bool:
  Bool.not(hop(ns, n)) && (len || Bool.not(Eng.bytes.eq(n, "content-length")))

def rends(+ns: List<&2, Bytes()>, +len: Bool, fs: List<&2, Field>) -> List<&2, Field>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{f, t}:
      match f:
        case Field{+n, v}:
          ends.put(rkeeps(ns, len, n), Field{n, v}, rends(ns, len, t))

def rsp.mk(+via: Bytes(), +head: Bool, +bodyless: Bool, cw: Stat, +xs: List<&2, Field>,
  body: Bytes()) -> Rsp:
  match cw:
    case Stat{code, why}:
      Rsp{code, why, List.append(&2, Field, rends(conn.names(xs), head && bodyless, xs), [Field{"via", via}]),
        body, bodyless}

def rsp.at(+via: Bytes(), +head: Bool, +bodyless: Bool, st: Maybe<&2, Stat>,
  fs: Maybe<&2, List<&2, Field>>, body: Bytes()) -> Maybe<&2, Rsp>:
  match st fs:
    case Some{cw} Some{xs}:
      Some{rsp.mk(via, head, bodyless, cw, xs, body)}
    case _ _:
      None{}

def rsp.lines(+via: Bytes(), +head: Bool, +bodyless: Bool, ls: List<&2, List<&2, U32>>, body: Bytes()) ->
  Maybe<&2, Rsp>:
  match ls:
    case Nil{}:
      None{}
    case Con{l, t}:
      rsp.at(via, head, bodyless, status.of(l), fields.of(t), body)

# the response to send back, from the bytes the exchange read: k interim
# heads, then the final one; head says the request was HEAD and code is
# the status the reader read
def rsp.of(+via: Bytes(), +head: Bool, +k: Nat, +code: U32, +got: Bytes(), body: Bytes()) -> Maybe<&2, Rsp>:
  rsp.lines(via, head, head || U32.is_lt(code, 200) || U32.is_eq(code, 204) || U32.is_eq(code, 304),
    rlines(k, got), body)

# the bytes that go back: the status line rebuilt, a field a line, the
# length counted from the body unless the framing says there is none,
# and the connection's fate (conn: a Connection value, or "" for none)
def rclf(bodyless: Bool, +body: Bytes()) -> List<&2, Field>:
  match bodyless:
    case True{}:
      Nil{}
    case False{}:
      [Field{"content-length", Nat.show(Bytes.len(body))}]

def rconf(+conn: Bytes()) -> List<&2, Field>:
  Bool.pick(List<&2, Field>, String.is_empty(conn), Nil{}, [Field{"connection", conn}])

# the fields that go back: the upstream's end-to-end ones, the length,
# the connection's fate
def rall(fs: List<&2, Field>, +bodyless: Bool, +body: Bytes(), +conn: Bytes()) -> List<&2, Field>:
  List.append(&2, Field, fs, List.append(&2, Field, rclf(bodyless, body), rconf(conn)))

def sl.ser(code: Bytes(), why: Bytes()) -> Bytes():
  Bytes.append("HTTP/1.1 ", Bytes.append(code, Bytes.append(" ", why)))

def rser(r: Rsp, +conn: Bytes()) -> Bytes():
  match r:
    case Rsp{code, why, fs, +body, +bodyless}:
      Bytes.append(sl.ser(code, why),
        Bytes.append("\r\n", Bytes.append(fls.ser(rall(fs, bodyless, body, conn)),
          Bytes.append("\r\n", Bool.pick(Bytes(), bodyless, "", body)))))

# A reply of the proxy's own, when there is no response to send back:
# 400 for a request it refused, 431 for a head past its cap, 502 when
# the upstream could not be reached or answered with nothing it could
# frame, 504 when the upstream ran out its deadline. It closes.
def own.reply(status: Bytes(), +body: Bytes()) -> Bytes():
  Bytes.concat(["HTTP/1.1 ", status, "\r\ncontent-type: text/plain\r\ncontent-length: ",
    Nat.show(Bytes.len(body)), "\r\nconnection: close\r\n\r\n", body])
