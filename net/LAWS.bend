# The laws of bend-net. Each is a promise a user of net/ gets for
# nothing, stated over the functions the server and the client run:
#
#   handler_framed  a handler is only ever handed a request that
#                   spec.bend's frame() framed, however TCP cut the
#                   stream: the requests the server's scan takes out of
#                   a connection's reads are, adapted as this file
#                   spells out, exactly frame()'s of the stream whole
#   respond_framed  every response the server writes, read back the way
#                   RFC 9112 reads one (wire/http1/spec.bend), is one
#                   final response: the handler's status and body -- no
#                   body on HEAD, 204 or 304, and its length the body's
#                   -- closing exactly when the server closes, and not a
#                   byte more; or, when the handler's could not be
#                   written (a field with a line end, a 1xx), the 500
#   route_first     the router picks the first route that matches with
#                   the method, and a 405's Allow lists exactly the
#                   methods the routes matching the path hold, each once
#   pool_clean      the client gives a connection back to its pool only
#                   when its response did not close it and nothing came
#                   after it, for every peer (from wire/client.bend's
#                   reuse_clean)
#   redirect_cap    a chain allowed k redirects sends at most k + 1
#                   requests, whatever the answers
#   redirect_creds  and never sends a credential (Authorization, Cookie,
#                   Proxy-Authorization) to an origin other than the
#                   first request's
#   stream_body     a streamed body's chunks, as a handler reads them,
#                   are the body RFC 9112's framing (wire/http1/spec.bend)
#                   finds in the stream, however TCP cut it
#   stream_bounded  between reads a streamed body holds no more than the
#                   read that brought it: the chunk it hands on and what
#                   came after the body, nothing of the body before it
#   stream_next     the connection goes on after a streamed body only
#                   once the framing says it ended, with exactly the
#                   bytes after it: an undrained body is never read as a
#                   request
#   pour_chunked    a response written as it is made, its length unknown,
#                   read back by wire/http1's spec, is one final response
#                   whose body is the writes joined, closing as the server
#                   closes, nothing after it (or the 500)
#   pour_length     and with a declared length the writes come to, the same
#   pour_capped     a declared length is never written past
#   pour_quiet      after a failure, nothing more is written
#   pour_bounded    a write goes out as itself and at most 120 bytes of
#                   framing: nothing of a body is held between writes
#
# and the vectors: percent-encoding's round trip over every byte, the
# query, URLs and Locations as the URL standard reads them (and where
# bend-net refuses), the router's patterns, and the response check.
import Base
import ../wire/reader.bend as Wr
import ../wire/client.bend as C
import ../wire/world.bend as W
import ../wire/http1/resp.bend as R
import ../wire/http1/spec.bend as RS
import ../demos/io_http_engine/main.bend as Eng
import ../demos/io_http_engine/spec.bend as Spec
import ../demos/io_proxy/core.bend as X
import ../demos/io_proxy/LAWS.bend as PL
import ./http.bend as Http
import ./url.bend as U
import ./server.bend as Server
import ./client.bend as Client
import ./stream.bend as Stream

# A handler sees what the RFC framed
# ==================================

# the connection's reads, as the server's loop takes them: each through
# the server's scan from where the last one left it, until one ends
# refused or after an upgrade
def reads.go(rs: List<&2, Bytes()>, sc: X.Scan) -> PL.Conn:
  match rs:
    case Nil{}:
      PL.Conn{Nil{}, X.TWait{sc}}
    case Con{+r, t}:
      PL.reads.at(Server.scan(r, sc), s2 => reads.go(t, s2))

def reads(rs: List<&2, Bytes()>) -> PL.Conn:
  reads.go(rs, X.scan.new())

# what a handler is handed for a request the reader framed, spelled out:
# the method's bytes, the target before its first '?' and after it,
# every field the reader passed on (the Host and each it does not act
# on) with its value trimmed of the whitespace at its ends, the body,
# the peer's address, and no params yet
def spec.fields(fs: List<&2, Wr.Field>) -> List<&2, Http.Header>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{f, t}:
      match f:
        case Wr.Field{n, v}:
          Con{Http.Header{n, X.trim(v)}, spec.fields(t)}

def spec.req.at(+ip: Bytes(), +t: Bytes(), +q: Nat, hd: Eng.Hd, body: Bytes()) -> Http.Request:
  match hd:
    case Eng.Hd{m, v10, fs, cn}:
      Http.Request{m, String.take(t, q), String.drop(t, 1n+q), spec.fields(fs), body, ip, Nil{}}

def spec.req(+ip: Bytes(), r: Eng.Req) -> Http.Request:
  match r:
    case Eng.Req{meth, +t, body, close, ws, key, hd}:
      spec.req.at(ip, t, Bytes.find_byte(t, 0n, 63), hd, body)

def spec.reqs(+ip: Bytes(), rs: List<&2, Eng.Req>) -> List<&2, Http.Request>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      Con{spec.req(ip, r), spec.reqs(ip, t)}

# what the server hands its handler, in order
def handed(+ip: Bytes(), rs: List<&2, Eng.Req>) -> List<&2, Http.Request>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      Con{Http.req.of(ip, r), handed(ip, t)}

def framed(f: Spec.Frames) -> List<&2, Eng.Req>:
  match f:
    case Spec.Frames{rs, e}:
      rs

# LAW: a handler is only handed what the RFC framed. For every stream a
# client sends, however TCP cuts it into reads, the requests the server
# hands its handler -- the ones its scan takes from the reads, in order,
# adapted -- are exactly the requests spec.bend's frame() finds in the
# stream whole, adapted as spelled out above. No request the reader and
# the RFC disagree on ever reaches a handler.
law handler_framed:
  for +ip: Bytes()
  for +rs: List<&2, Bytes()>
  {handed(ip, PL.conn.took(reads(rs))) == spec.reqs(ip, framed(Spec.frame(Bytes.to_list(Bytes.concat(rs))))) :
    List<&2, Http.Request>}

# Every response is framed
# ========================

# what a client reads back: the one final response, with the handler's
# status and its body (none where the framing says none), closing
# exactly when the server closes, and nothing after it; or the 500
def sent(+head: Bool, +closing: Bool, +code: U32, ok: Bool, body: Bytes()) -> R.Look:
  match ok:
    case True{}:
      R.Look{Nil{}, R.Final{R.Resp{code, False{}, closing, Bool.pick(Bytes(), X.rbodyless(head, code), "", body)}, ""}}
    case False{}:
      R.Look{Nil{}, R.Final{R.Resp{500, False{}, closing, Bool.pick(Bytes(), X.rbodyless(head, 500), "",
        Http.e500.body())}, ""}}

# LAW: a response goes out as exactly one response. Whatever status,
# fields and body a handler answers with, to whichever request (HEAD or
# not, HTTP/1.0 or not) and whether or not the connection ends after
# it, the bytes the server writes, read by wire/http1/spec.bend's
# response() -- how a client that reads HTTP/1.1 as the RFC does frames
# them -- are one final response: the handler's status and body, or the
# server's 500 when the handler's did not pass the check (Http.enc.check),
# closing as the server decided, and not a byte more. A handler cannot
# split a response, smuggle one, or send a body a HEAD said it would not.
law respond_framed:
  for +head: Bool
  for +closing: Bool
  for +v10: Bool
  for +code: U32
  for +hs: List<&2, Http.Header>
  for +body: Bytes()
  {RS.response(X.rask(head), Bytes.to_list(Http.write(head, closing, v10, code, hs, body))) ==
    sent(head, closing, code, Http.enc.check(head, code, Http.rhead(code, hs, body), body), body) : R.Look}

# the check passes the responses handlers write, and fails the ones that
# would not frame: a field whose value ends the line, a 1xx, a status
# past 599 (each then goes out as the 500)
def check.of(+head: Bool, r: Http.Response) -> Bool:
  match r:
    case Http.Response{+code, hs, b}:
      match b:
        case Http.BBody{+bs}:
          Http.enc.check(head, code, Http.rhead(code, hs, bs), bs)
        case Http.BFile{root, p}:
          False{}

law check_vectors:
  {[check.of(False{}, Http.text(200, "Hello, world!\n")), check.of(True{}, Http.text(200, "Hello, world!\n")),
    check.of(False{}, Http.json(201, "{\"id\":1}")), check.of(False{}, Http.redirect(302, "/next")),
    check.of(False{}, Http.Response{204, Nil{}, Http.BBody{""}}),
    check.of(False{}, Http.with.header(Http.plain(404), "X-Trace", "a b")),
    check.of(False{}, Http.with.header(Http.text(200, "x"), "set-cookie", "a=1\r\nx-evil: 1")),
    check.of(False{}, Http.text(101, "")), check.of(False{}, Http.text(600, "x")),
    check.of(False{}, Http.with.header(Http.text(200, "x"), "bad name", "v"))]
    == [True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}, False{}] : List<&2, Bool>}

# The router
# ==========

def spec.mem(+m: Bytes(), ms: List<&2, Bytes()>) -> Bool:
  match ms:
    case Nil{}:
      False{}
    case Con{x, t}:
      String.eq(m, x) || spec.mem(m, t)

def spec.hit.at(mm: Maybe<&2, List<&2, Http.Header>>, has: Bool, +i: Nat, rest: Maybe<&2, Server.Pick>) ->
  Maybe<&2, Server.Pick>:
  match mm has:
    case Some{ps} True{}:
      Some{Server.Hit{i, ps}}
    case _ _:
      rest

# the first route, counting from i, whose pattern matches the path's
# segments and whose methods hold m, with its params
def spec.hit(pats: List<&2, Server.Pat>, +m: Bytes(), +xs: List<&2, Bytes()>, +i: Nat) -> Maybe<&2, Server.Pick>:
  match pats:
    case Nil{}:
      None{}
    case Con{p, t}:
      match p:
        case Server.Pat{+ms, +pat}:
          spec.hit.at(Server.matches(pat, xs), spec.mem(m, ms), i, spec.hit(t, m, xs, 1n+i))

def spec.allow.at(mm: Maybe<&2, List<&2, Http.Header>>, ms: List<&2, Bytes()>, rest: List<&2, Bytes()>) ->
  List<&2, Bytes()>:
  match mm:
    case Some{ps}:
      List.append(&2, Bytes(), ms, rest)
    case None{}:
      rest

# every method of every route whose pattern matches, in order
def spec.allow(pats: List<&2, Server.Pat>, +xs: List<&2, Bytes()>) -> List<&2, Bytes()>:
  match pats:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      match p:
        case Server.Pat{ms, +pat}:
          spec.allow.at(Server.matches(pat, xs), ms, spec.allow(t, xs))

def spec.nub.at(has: Bool, +x: Bytes(), +seen: List<&2, Bytes()>, go: List<&2, Bytes()> -> List<&2, Bytes()>) ->
  List<&2, Bytes()>:
  match has:
    case True{}:
      go(seen)
    case False{}:
      Con{x, go(List.append(&2, Bytes(), seen, [x]))}

# each once, the first time it comes, after the ones already seen
def spec.nub.go(xs: List<&2, Bytes()>, +seen: List<&2, Bytes()>) -> List<&2, Bytes()>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, t}:
      spec.nub.at(spec.mem(x, seen), x, seen, sn => spec.nub.go(t, sn))

def spec.nub(xs: List<&2, Bytes()>) -> List<&2, Bytes()>:
  spec.nub.go(xs, Nil{})

def spec.pick.end(h: Maybe<&2, Server.Pick>, allow: List<&2, Bytes()>) -> Server.Pick:
  match h:
    case Some{x}:
      x
    case None{}:
      match allow:
        case Nil{}:
          Server.NoRoute{}
        case Con{a, t}:
          Server.NoMethod{Con{a, t}}

def spec.pick(+pats: List<&2, Server.Pat>, +m: Bytes(), +path: Bytes()) -> Server.Pick:
  spec.pick.end(spec.hit(pats, m, Server.segs(path), 0n), spec.nub(spec.allow(pats, Server.segs(path))))

# LAW: the first route wins, and a 405 says exactly what would have
# worked. For every table and every request, the router's choice is the
# first route whose pattern matches the path and whose methods hold the
# request's (with the params its pattern bound); failing that, when some
# patterns match, a 405 whose Allow is every method of every route that
# matches the path, each once, in the order the table has them; else a
# 404.
law route_first:
  for +pats: List<&2, Server.Pat>
  for +m: Bytes()
  for +path: Bytes()
  {Server.pick(pats, m, path) == spec.pick(pats, m, path) : Server.Pick}

# what patterns match, closed: literals, :params (percent-decoded), a
# last * for the rest; a trailing slash is a segment of its own
def table() -> List<&2, Server.Pat>:
  [Server.Pat{["GET", "HEAD"], "/"}, Server.Pat{["GET", "HEAD"], "/users/:id"},
   Server.Pat{["DELETE"], "/users/:id"}, Server.Pat{["POST"], "/users"},
   Server.Pat{["GET", "HEAD"], "/files/*"}, Server.Pat{["PUT"], "/a/:x/b/:y"}]

law route_vectors:
  {[Server.pick(table(), "GET", "/"), Server.pick(table(), "GET", "/users/7"),
    Server.pick(table(), "DELETE", "/users/a%20b"), Server.pick(table(), "PATCH", "/users/7"),
    Server.pick(table(), "GET", "/users/"), Server.pick(table(), "GET", "/files/x/y.css"),
    Server.pick(table(), "GET", "/files/"), Server.pick(table(), "PUT", "/a/1/b/2"),
    Server.pick(table(), "GET", "/nope"), Server.pick(table(), "GET", "/users")]
    == [Server.Hit{0n, Nil{}}, Server.Hit{1n, [Http.Header{"id", "7"}]}, Server.Hit{2n, [Http.Header{"id", "a b"}]},
        Server.NoMethod{["GET", "HEAD", "DELETE"]}, Server.NoRoute{}, Server.Hit{4n, [Http.Header{"*", "x/y.css"}]},
        Server.Hit{4n, [Http.Header{"*", ""}]}, Server.Hit{5n, [Http.Header{"x", "1"}, Http.Header{"y", "2"}]},
        Server.NoRoute{}, Server.NoMethod{["POST"]}] : List<&2, Server.Pick>}

# The pool
# ========

# a connection given back to the pool (fit) is one whose response did
# not close it, with nothing after the response
def kept.ok(r: Result<&2, &2, C.Why, C.Got>) -> Bool:
  match r:
    case Fail{w}:
      True{}
    case Done{g}:
      match g:
        case C.Got{+i, +x, +extra, +reuse}:
          Bool.not(Client.fit(Done{C.Got{i, x, extra, reuse}})) || (Bool.not(C.resp.close(x)) && String.is_empty(extra))

def kept(m: C.Out(W.World)) -> Bool:
  (s, r) = m
  kept.ok(r)

# LAW: the pool is never handed a connection it must not reuse. For
# every peer the script can describe -- whatever it sends, however it
# cuts it, whenever it stops, resets or goes silent -- the client puts a
# connection back in its pool only when the exchange ended in a final
# response that did not close it (no Connection: close, not HTTP/1.0
# without keep-alive, not a 101, not a body that ran to the close) and
# nothing came after it.
law pool_clean:
  for +e: R.Ask
  for +b: C.Budget
  for +req: Bytes()
  for +s: W.World
  {kept(C.sim.exchange(e, b, req, s)) == True{} : Bool}

# Redirects
# =========

# the credentials, spelled out here: they say who is asking
def spec.cred(+n: Bytes()) -> Bool:
  String.eq(n, "authorization") || String.eq(n, "cookie") || String.eq(n, "proxy-authorization")

def spec.no.creds(hs: List<&2, Http.Header>) -> Bool:
  match hs:
    case Nil{}:
      True{}
    case Con{h, t}:
      match h:
        case Http.Header{+n, v}:
          Bool.not(spec.cred(n)) && spec.no.creds(t)

# a request is clean for orig when it goes to orig, or carries no
# credential (the client lowercases every name as a request comes in)
def clean(+orig: Bytes(), r: Client.IReq) -> Bool:
  match r:
    case Client.IReq{m, u, hs, b}:
      String.eq(U.origin(u), orig) || spec.no.creds(hs)

# A scripted peer: the answers it gives, one per request, in order (a
# request past the last is answered Closed); a count of the requests it
# may still take, and whether one more came; the first request's origin,
# and whether a request that was not clean for it came.
type Script is Data:
  Script{ans: List<&2, Client.Res()>, left: Nat, over: Bool, orig: Bytes(), leak: Bool}

def sc.tick(left: Nat, over: Bool) -> Nat & Bool:
  match left:
    case 0n:
      (0n, True{})
    case 1n+j:
      (j, over)

def sc.pop(ans: List<&2, Client.Res()>, lo: Nat & Bool, orig: Bytes(), leak: Bool) -> Script & Client.Res():
  match ans:
    case Nil{}:
      (left, over) = lo
      (Script{Nil{}, left, over, orig, leak}, Fail{Client.Closed{}})
    case Con{r, t}:
      (left, over) = lo
      (Script{t, left, over, orig, leak}, r)

def sc.send(+s: Script, rq: Client.IReq) -> W.Id(Script & Client.Res()):
  match s:
    case Script{ans, left, over, +orig, leak}:
      sc.pop(ans, sc.tick(left, over), orig, leak || Bool.not(clean(orig, rq)))

def sim.chain(k: Nat, +orig: Bytes(), +rq: Client.IReq, s: Script) -> Script & Client.Res():
  Client.chain(~W.Id, ~W.Id.pure, ~W.Id.bind, ~Script, ~sc.send, k, orig, rq, s)

def sc.over(s: Script) -> Bool:
  match s:
    case Script{ans, left, over, orig, leak}:
      over

def sc.leak(s: Script) -> Bool:
  match s:
    case Script{ans, left, over, orig, leak}:
      leak

# LAW: redirects end. A chain allowed k redirects (Client.chain, the one
# the client runs over IO) sends at most k + 1 requests, whatever the
# peer answers: a peer that takes k + 1 is never asked for one more.
law redirect_cap:
  for k: Nat
  for +orig: Bytes()
  for +rq: Client.IReq
  for ans: List<&2, Client.Res()>
  {sc.over(Pair.fst(Script, Client.Res(), sim.chain(k, orig, rq, Script{ans, 1n+k, False{}, orig, False{}}))) ==
    False{} : Bool}

# LAW: credentials stay with their origin. Whatever the peer answers
# -- any status, any Location, to any origin, any number of times --
# every request the chain sends is clean for the first request's
# origin: a credential goes on to that origin and to no other, even
# after a redirect away and back.
law redirect_creds:
  for k: Nat
  for +orig: Bytes()
  for +rq: Client.IReq
  for ans: List<&2, Client.Res()>
  for c: {clean(orig, rq) == True{} : Bool}
  {sc.leak(Pair.fst(Script, Client.Res(), sim.chain(k, orig, rq, Script{ans, 1n+k, False{}, orig, False{}}))) ==
    False{} : Bool}

# Vectors
# =======

def upto(k: Nat, +i: U32) -> List<&2, U32>:
  match k:
    case 0n:
      Nil{}
    case 1n+j:
      Con{i, upto(j, (i + 1 : U32))}

# every byte, 0 to 255, in order
def all.bytes() -> Bytes():
  Bytes.from_list(upto(256n, 0))

# pct.decode undoes pct.encode, over every byte
law pct_round_trip:
  {Http.pct.decode(Http.pct.encode(all.bytes())) == all.bytes() : Bytes()}

law pct_vectors:
  {[Http.pct.encode("a b/c?d=_-.~"), Http.pct.decode("a%20b"), Http.pct.decode("%41%62%2f"), Http.pct.decode("%zz%4"),
    Http.pct.decode("100%"), Http.pct.decode("a+b"), Http.form.decode("a+b%2B"), Http.pct.decode("%E2%82%ac")]
    == ["a%20b%2Fc%3Fd%3D_-.~", "a b", "Ab/", "%zz%4", "100%", "a+b", "a b+", Bytes.from_list([226, 130, 172])] :
    List<&2, Bytes()>}

law query_vectors:
  {Http.query.pairs("a=1&b=&c&&d=x%20y+z&e=%3D=") ==
    [Http.Header{"a", "1"}, Http.Header{"b", ""}, Http.Header{"c", ""}, Http.Header{"d", "x y z"},
     Http.Header{"e", "=="}] : List<&2, Http.Header>}

def url.of(r: Result<&2, &2, Bytes(), U.Url>) -> Bytes():
  match r:
    case Done{u}:
      U.url.show(u)
    case Fail{m}:
      Bytes.append("refused: ", m)

# the URL standard's reading of each, or bend-net's refusal: of a user
# or password, a port past 65535 or of 0, a scheme but http and https
# (ws and wss by parse.ws, read as http and https), IPv6, and an empty
# host (the standard would skip the third slash of http:///x)
law url_vectors:
  {[url.of(U.parse("http://Example.COM/a/./b/../c?x=1 2#frag")), url.of(U.parse("  HTTPS://h:8443  ")),
    url.of(U.parse("http://h:80/")), url.of(U.parse("https://h:443/p")), url.of(U.parse("http://h:/x")),
    url.of(U.parse("http://h\\a\\b")), url.of(U.parse("http://h/%2e%2E/x")), url.of(U.parse("http://h?q")),
    url.of(U.parse("http://h/a/..")), url.of(U.parse("http://h/../../x")), url.of(U.parse("http://h/a b<c>")),
    url.of(U.parse("http://h\t/x\n")), url.of(U.parse("http://u:p@h/")), url.of(U.parse("http://h:99999/")),
    url.of(U.parse("http://h:0/")), url.of(U.parse("ftp://h/")), url.of(U.parse("http://[::1]/")),
    url.of(U.parse("http:///x")), url.of(U.parse("http://h_x/")), url.of(U.parse.ws("wss://h/chat")),
    url.of(U.parse.ws("WS://h:81"))]
    == ["http://example.com/a/c?x=1%202", "https://h:8443/", "http://h/", "https://h/p", "http://h/x",
        "http://h/a/b", "http://h/x", "http://h/?q", "http://h/", "http://h/x", "http://h/a%20b%3Cc%3E",
        "http://h/x", "refused: credentials in a URL", "refused: bad port", "refused: bad port",
        "refused: not a URL of this scheme", "refused: IPv6 addresses are not supported", "refused: bad host",
        "http://h_x/", "https://h/chat", "http://h:81/"] : List<&2, Bytes()>}

def base() -> U.Url:
  U.Url{False{}, "h", 80, "/a/b?q"}

# a Location against the URL it came from
law resolve_vectors:
  {[url.of(U.resolve(base(), "c")), url.of(U.resolve(base(), "/x")), url.of(U.resolve(base(), "//o:81/y")),
    url.of(U.resolve(base(), "?z")), url.of(U.resolve(base(), "../../../d")), url.of(U.resolve(base(), "https://t/")),
    url.of(U.resolve(base(), "")), url.of(U.resolve(base(), "./")), url.of(U.resolve(base(), "c#f")),
    url.of(U.resolve(base(), "mailto:x@y"))]
    == ["http://h/a/c", "http://h/x", "http://o:81/y", "http://h/a/b?z", "http://h/d", "https://t/", "http://h/a/b?q",
        "http://h/a/", "http://h/a/c", "refused: not a URL of this scheme"] : List<&2, Bytes()>}

# Streamed bodies
# ===============
#
# A stream route's body is read by wire/http1's reader entered at the
# body (Stream.entry), a read at a time (Stream.step: fed, and the body
# bytes taken), as net/stream.bend's Stream.read runs it; Stream.drain
# is a body's reads in turn, the chunks handed on joined. The reference
# is wire/http1/spec.bend's walk of RFC 9112's framing -- written line
# by line from the RFC, and the reader held to it by resp_sim --
# entered at the same place: a body of n bytes counted off, or a
# chunked body under the budget, from its first byte.

def spec.mode(+e: R.Ask, f: Stream.Frame) -> RS.Mode:
  match f:
    case Stream.FLen{n}:
      match n:
        case 0n:
          RS.MDone{RS.resp(R.body.head(), Nil{}, False{}), Nil{}}
        case 1n+q:
          RS.MBody{R.body.head(), q, Nil{}}
    case Stream.FChunked{}:
      RS.MChunk{R.body.head(), R.ASize0{}, 0, Nil{}, R.ask.cap(e)}

# what the RFC's framing reads of a body's bytes, from its first
def spec.body(+e: R.Ask, f: Stream.Frame, bs: List<&2, U32>) -> R.Look:
  RS.finish(e, RS.walk(e, bs, RS.W{spec.mode(e, f), Nil{}}))

# a body, framed as f, read by the reads rs: the reader after the last,
# and the chunks handed on, joined
def streamed(+e: R.Ask, +f: Stream.Frame, rs: List<&2, Bytes()>) -> R.P & Bytes():
  Stream.drain(e, rs, Stream.entry(e, f), "")

# LAW: a streamed body is the body the RFC frames. For every framing a
# head announces and every stream, however TCP cuts it into reads, the
# chunks a handler is handed, joined in order, put back in front of what
# the reader still holds, read exactly as RFC 9112's framing reads the
# stream whole: when it ends, the chunks joined are its body, byte for
# byte -- none lost, doubled, reordered or made up -- and what follows
# is what follows it; refused, or not yet ended, the same.
law stream_body:
  for +e: R.Ask
  for +f: Stream.Frame
  for +rs: List<&2, Bytes()>
  {R.look(R.give(Wr.drain.b(R.P, streamed(e, f, rs)), Wr.drain.s(R.P, streamed(e, f, rs)))) ==
    spec.body(e, f, Bytes.to_list(Bytes.concat(rs))) : R.Look}

# what a reader holds, spelled out: the body bytes a take would hand on,
# and the bytes that came after the body
def spec.after(p: R.P) -> Bytes():
  match p:
    case R.P{st, out}:
      match st:
        case R.Fin{r, x}:
          x
        case _:
          ""

def spec.hold(+p: R.P, +x: Bytes()) -> Nat:
  Nat.add(Bytes.len(x), Nat.add(Bytes.len(Wr.drain.b(R.P, R.take(p))), Bytes.len(spec.after(p))))

# LAW: a streamed body costs one read. Whatever the reader's state and
# whatever a read brings, once the read is kept (Stream.fits, which
# Stream.read asks of every read, refusing the body otherwise) what the
# Body holds after it -- the chunk it hands on, the body bytes the reader
# still holds, the bytes after the body -- is at most that read, and the
# reader holds no byte of the body at all. A read is at most
# Stream.chunk() bytes (TCP.poll_buf's contract, rx.ok), so a connection
# streaming a body holds at most that and its head, however large the
# body: the bound wire/stream.bend's stream_window gives a window of one.
law stream_bounded:
  for +e: R.Ask
  for +bs: Bytes()
  for +p: R.P
  for ok: {Stream.fits(Wr.drain.s(R.P, Stream.step(e, bs, p)), Wr.drain.b(R.P, Stream.step(e, bs, p)),
    Bytes.len(bs)) == True{} : Bool}
  {Nat.is_le(spec.hold(Wr.drain.s(R.P, Stream.step(e, bs, p)), Wr.drain.b(R.P, Stream.step(e, bs, p))),
    Bytes.len(bs)) == True{} : Bool}

# what the RFC says follows a body: the bytes after it once it ended;
# nothing while it has not, or when it was refused
def spec.next(l: R.Look) -> Maybe<&2, Bytes()>:
  match l:
    case R.Look{i, end}:
      match end:
        case R.Final{r, rest}:
          Some{rest}
        case _:
          None{}

# LAW: an undrained body is never a request. After a streamed request --
# the handler read all of its body, some, or none, and the server drained
# what it could -- the connection goes on (Stream.next) only when RFC
# 9112's framing says the body has ended, and then with exactly the bytes
# it puts after the body; while the body has not ended, or was refused,
# it goes on with nothing, and closes. No byte of a body is ever read as
# the head of the next request, whatever the handler did.
law stream_next:
  for +e: R.Ask
  for +f: Stream.Frame
  for +rs: List<&2, Bytes()>
  {Stream.next(Wr.drain.s(R.P, streamed(e, f, rs))) == spec.next(spec.body(e, f, Bytes.to_list(Bytes.concat(rs)))) :
    Maybe<&2, Bytes()>}

# Streamed response bodies
# ========================
#
# A response a handler writes as it goes (net/stream.bend's Stream.pour)
# is written by a pure writer the IO runs: Stream.opening, the head and
# the writer the body starts in; Stream.emit, the bytes a write goes out
# as, and the writer after it; Stream.close, the bytes that end the body.
# Stream.poured is a whole response as the server writes it, for every
# list of writes: its head, each write's bytes, the end. The reference
# is wire/http1/spec.bend's response(), as for respond_framed: how a
# client that reads HTTP/1.1 as RFC 9112 does frames the bytes.

# A reader's budget, as spec.bend's walk spends it on a chunked body: each
# digit of a chunk's size costs one and must leave more than the size read
# so far; a chunk's data costs its size; the last chunk's digit, one.
def dig.step(g: R.Go, +n: U32, +left: U32, go: U32 -> U32 -> Bool) -> Bool:
  match g:
    case R.GDigit{+d}:
      Bool.not(U32.is_le(left, (n * 16 + d : U32))) && go((n * 16 + d : U32), (left - 1 : U32))
    case _:
      False{}

# a size line's digits, from at with the size so far n: each a digit, and
# each paid for
def dig.ok(ds: List<&2, U32>, at: R.At, +n: U32, +left: U32) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{+c, t}:
      dig.step(R.chunk.step(at, R.xk.of(R.cls(c), c)), n, left, n2 => l2 => dig.ok(t, R.ASize{}, n2, l2))

def dig.val.step(g: R.Go, +n: U32, go: U32 -> U32) -> U32:
  match g:
    case R.GDigit{+d}:
      go((n * 16 + d : U32))
    case _:
      n

# the size a line's digits say
def dig.val(ds: List<&2, U32>, at: R.At, +n: U32) -> U32:
  match ds:
    case Nil{}:
      n
    case Con{+c, t}:
      dig.val.step(R.chunk.step(at, R.xk.of(R.cls(c), c)), n, n2 => dig.val(t, R.ASize{}, n2))

# the budget after a line's digits
def dig.left(ds: List<&2, U32>, +left: U32) -> U32:
  match ds:
    case Nil{}:
      left
    case Con{c, t}:
      dig.left(t, (left - 1 : U32))

# the size line of a chunk of 2^j bytes
def chunk.ds(+j: Nat) -> List<&2, U32>:
  Bytes.to_list(Stream.chunk.hex(j))

# a chunk of 2^j bytes: its size line paid for, and the budget after it
# and its data
def chunk.ok(+j: Nat, +left: U32) -> Bool:
  dig.ok(chunk.ds(j), R.ASize0{}, 0, left)

def chunk.left(+j: Nat, +left: U32) -> U32:
  (dig.left(chunk.ds(j), left) - dig.val(chunk.ds(j), R.ASize0{}, 0) : U32)

def ok.at(fit: Bool, +j: Nat, +n: Nat, +left: U32, go: Nat -> U32 -> Bool) -> Bool:
  match fit:
    case True{}:
      chunk.ok(j, left) && go(Nat.sub(n, Stream.chunk.size(j)), chunk.left(j, left))
    case False{}:
      go(n, left)

# a write of n bytes, cut as Stream.chunks.go cuts it: every chunk paid for
def ok.go(j: Nat, +n: Nat, +left: U32) -> Bool:
  match j:
    case 0n:
      ok.at(Nat.is_ge(n, Stream.chunk.size(0n)), 0n, n, left, n2 => l => True{})
    case 1n+(+i):
      ok.at(Nat.is_ge(n, Stream.chunk.size(1n+i)), 1n+i, n, left, n2 => l => ok.go(i, n2, l))

def left.at(fit: Bool, +j: Nat, +n: Nat, +left: U32, go: Nat -> U32 -> U32) -> U32:
  match fit:
    case True{}:
      go(Nat.sub(n, Stream.chunk.size(j)), chunk.left(j, left))
    case False{}:
      go(n, left)

# and the budget after it
def left.go(j: Nat, +n: Nat, +left: U32) -> U32:
  match j:
    case 0n:
      left.at(Nat.is_ge(n, Stream.chunk.size(0n)), 0n, n, left, n2 => l => l)
    case 1n+(+i):
      left.at(Nat.is_ge(n, Stream.chunk.size(1n+i)), 1n+i, n, left, n2 => l => left.go(i, n2, l))

# whether a reader's budget, left, covers a chunked body of the writes
# ws: every write's chunks, then the last chunk (a budget of 256 MiB, a
# client's, covers any body a little under it)
def fits(ws: List<&2, Bytes()>, +left: U32) -> Bool:
  match ws:
    case Nil{}:
      dig.ok([48], R.ASize0{}, 0, left)
    case Con{+x, t}:
      ok.go(14n, Bytes.len(x), left) && fits(t, left.go(14n, Bytes.len(x), left))

# every write at most what one emit frames (Stream.write cuts them so)
def small(ws: List<&2, Bytes()>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{x, t}:
      Nat.is_le(Bytes.len(x), Stream.emit.max()) && small(t)

# the check a head passes to go out as it is (else the 500 goes)
def pour.ok(+code: U32, h: X.RHead) -> Bool:
  match h:
    case X.RHead{+cd, +why, fs, hl}:
      Stream.rhd.ok(cd, code, why, fs)

def pour.ok.len(+code: U32, h: X.RHead, +n: Nat) -> Bool:
  match h:
    case X.RHead{+cd, +why, fs, hl}:
      Stream.len.check(False{}, code, cd, why, fs, Bool.pick(Bytes(), U32.is_eq(code, 204) || U32.is_eq(code, 304), "",
        Nat.show(n)), n)

# LAW: a response written as it is made is one response. Whatever status
# and fields a handler answers with, and whatever writes its producer
# makes -- of any sizes, empty ones too -- the bytes the server writes
# for a body of unknown length (chunked), read by wire/http1/spec.bend's
# response(), are exactly one final response: the handler's status, its
# body the writes joined in order (none for a 204 or 304), closing as the
# server decided, and nothing after it; or the 500 when the head could
# not be written as it was. For every body the reader's budget covers.
law pour_chunked:
  for +closing: Bool
  for +code: U32
  for +hs: List<&2, Http.Header>
  for +ws: List<&2, Bytes()>
  for sm: {small(ws) == True{} : Bool}
  for fit: {fits(ws, R.ask.cap(X.rask(False{}))) == True{} : Bool}
  {RS.response(X.rask(False{}), Bytes.to_list(Stream.poured(False{}, closing, False{}, code, hs, None{}, ws))) ==
    sent(False{}, closing, code, pour.ok(code, Http.rhead(code, hs, "")), Bytes.concat(ws)) : R.Look}

# LAW: a declared length is a Content-Length, and a producer whose writes
# come to it writes exactly one response: to any request, HTTP/1.0 or
# not, closing or not, the head and the writes read back as the one final
# response with the handler's status and the writes joined as its body.
law pour_length:
  for +closing: Bool
  for +v10: Bool
  for +code: U32
  for +hs: List<&2, Http.Header>
  for +n: Nat
  for +ws: List<&2, Bytes()>
  for hn: {Nat.is_eq(Bytes.len(Bytes.concat(ws)), n) == True{} : Bool}
  {RS.response(X.rask(False{}), Bytes.to_list(Stream.poured(False{}, closing, v10, code, hs, Some{n}, ws))) ==
    sent(False{}, closing, code, pour.ok.len(code, Http.rhead(code, hs, ""), n), Bytes.concat(ws)) : R.Look}

# LAW: a declared length is never written past. Whatever the writes --
# more than declared, fewer, one too long -- the bytes a body of n bytes
# goes out as are at most n: a write that would pass it goes out not at
# all (and the connection closes after the response).
law pour_capped:
  for +n: Nat
  for +ws: List<&2, Bytes()>
  {Nat.is_le(Bytes.len(Stream.emits(ws, Stream.Sent{Stream.MLen{n}, None{}})), n) == True{} : Bool}

# LAW: after a failure, nothing more is written. Once a writer has failed
# -- the peer gone, a send stalled, a write past the length, the head
# refused -- no write sends a byte, and neither does the body's end.
law pour_quiet:
  for m: Stream.Mode
  for e: Stream.Err
  for ws: List<&2, Bytes()>
  {Stream.emits(ws, Stream.Sent{m, Some{e}}) == "" : Bytes()}

# LAW: a write costs itself and a fixed framing. Whatever the writer's
# state and whatever a write brings, what goes out for it is at most the
# write and 120 bytes (fifteen chunks at most, each with a size line and
# two line ends of eight bytes at most): the writer keeps no byte of one
# write for later, so what a connection holds for a body is one write,
# however long the body.
law pour_bounded:
  for st: Stream.Sent
  for +x: Bytes()
  {Nat.is_le(Bytes.len(Pair.snd(Stream.Sent, Bytes(), Stream.emit(st, x))), Nat.add(Bytes.len(x), 120n)) == True{} : Bool}

# what goes out, closed: chunked, a length, HTTP/1.0 to the close, HEAD,
# a write past a length, and the budget a small body takes
law pour_vectors:
  {[Stream.poured(False{}, False{}, False{}, 200, [Http.Header{"content-type", "text/csv"}], None{}, ["a,b\n", "", "c,d\n"]),
    Stream.poured(False{}, True{}, False{}, 200, [], Some{3n}, ["ab", "c"]),
    Stream.poured(False{}, False{}, True{}, 200, [], None{}, ["ab", "c"]),
    Stream.poured(True{}, False{}, False{}, 200, [], None{}, ["ab", "c"]),
    Stream.poured(False{}, False{}, False{}, 200, [], Some{2n}, ["a", "bc", "d"]),
    Stream.chunks("0123456789")]
    == ["HTTP/1.1 200 OK\r\ncontent-type: text/csv\r\ntransfer-encoding: chunked\r\n\r\n4\r\na,b\n\r\n4\r\nc,d\n\r\n0\r\n\r\n",
        "HTTP/1.1 200 OK\r\ncontent-length: 3\r\nconnection: close\r\n\r\nabc",
        "HTTP/1.1 200 OK\r\nconnection: close\r\n\r\nabc",
        "HTTP/1.1 200 OK\r\ntransfer-encoding: chunked\r\n\r\n",
        "HTTP/1.1 200 OK\r\ncontent-length: 2\r\n\r\na",
        "8\r\n01234567\r\n2\r\n89\r\n"] : List<&2, Bytes()>}

law fits_vectors:
  {[fits(["hello", "", "world\n"], R.ask.cap(X.rask(False{}))), fits(["hello"], 4), fits(["hello"], 12)]
    == [True{}, False{}, True{}] : List<&2, Bool>}
