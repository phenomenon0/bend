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
