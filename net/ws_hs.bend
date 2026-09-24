# WebSocket (RFC 6455) client handshake: the URL, the opening request,
# and the judge of the server's answer.
#
# The URL parser takes ws:// and wss:// only, and is local to ws until
# net/ has one URL type (a note for that unification: this one has no
# userinfo, no IPv6 literal, no fragment, and refuses each).
#
# The answer is judged strictly (RFC 6455 4.1, the client's checks): a
# status line HTTP/1.1 101; exactly one Upgrade, its value websocket
# (any case); a Connection with the token upgrade (any case, in any
# list, in any of its lines); exactly one Sec-WebSocket-Accept, the
# base64 of the SHA-1 of the key joined to the GUID (the engine's own
# Ws.accept), byte for byte; no Sec-WebSocket-Extensions (none was
# offered); and a Sec-WebSocket-Protocol only if it is one of those
# offered, once. Anything else is refused, with why (Hw).
import Base
import ../demos/io_http_engine/ws.bend as Ws

# The URL
# =======

type Url is Data:
  Url{tls: Bool, host: String, port: U32, path: String}

# s cut at its first c: what is before it, and what is after it if c
# is there
def cut.pick(hit: Bool, x: U32, t: String, r: String & Maybe<&2, String>) ->
  String & Maybe<&2, String>:
  match hit:
    case True{}:
      ("", Some{t})
    case False{}:
      (a, b) = r
      (SCon{Chr{x}, a}, b)

def cut(s: String, +c: U32) -> String & Maybe<&2, String>:
  match s:
    case SNil{}:
      ("", None{})
    case SCon{Chr{+x}, +t}:
      cut.pick(U32.is_eq(x, c), x, t, cut(t, c))

def url.port.ok(n: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match n:
    case None{}:
      None{}
    case Some{+p}:
      Bool.pick(Maybe<&2, U32>, U32.is_lt(0, p) && U32.is_lt(p, 65536), Some{p}, None{})

def url.port(tls: Bool, may: Maybe<&2, String>) -> Maybe<&2, U32>:
  match may:
    case None{}:
      Some{Bool.pick(U32, tls, 443, 80)}
    case Some{+p}:
      Bool.pick(Maybe<&2, U32>, String.is_digit(p), url.port.ok(U32.read(p)), None{})

def url.make(+tls: Bool, +host: String, path: String, port: Maybe<&2, U32>) -> Maybe<&2, Url>:
  match port:
    case None{}:
      None{}
    case Some{n}:
      Bool.pick(Maybe<&2, Url>, String.is_empty(host), None{}, Some{Url{tls, host, n, path}})

def url.host(+tls: Bool, auth: String & Maybe<&2, String>, path: String) -> Maybe<&2, Url>:
  (host, port) = auth
  url.make(tls, host, path, url.port(tls, port))

# the authority and the resource: a path from its '/', with its query
def url.rest(+tls: Bool, r: String & Maybe<&2, String>) -> Maybe<&2, Url>:
  (auth, path) = r
  url.host(tls, cut(auth, 58), "/" ++ Maybe.default(&2, String, path, ""))

def url.slash(p: Maybe<&2, String>) -> Maybe<&2, String>:
  match p:
    case None{}:
      None{}
    case Some{x}:
      Some{"/" ++ x}

def url.split.q(+a2: String, q: Maybe<&2, String>, p: Maybe<&2, String>) -> String & Maybe<&2, String>:
  match q:
    case None{}:
      (a2, p)
    case Some{qs}:
      (a2, Some{"?" ++ qs ++ Maybe.default(&2, String, url.slash(p), "")})

def url.split.b(aq: String & Maybe<&2, String>, p: Maybe<&2, String>) -> String & Maybe<&2, String>:
  (a2, q) = aq
  url.split.q(a2, q, p)

def url.split.c(ap: String & Maybe<&2, String>) -> String & Maybe<&2, String>:
  (a, p) = ap
  url.split.b(cut(a, 63), p)

# the authority, and the rest: a '?' before any '/' starts a query on
# the root path
def url.split(+s: String) -> String & Maybe<&2, String>:
  url.split.c(cut(s, 47))

def url.scheme(wss: Bool, ws: Bool, +s: String) -> Maybe<&2, Url>:
  match wss ws:
    case True{} _:
      url.rest(True{}, url.split(String.drop(s, 6n)))
    case False{} True{}:
      url.rest(False{}, url.split(String.drop(s, 5n)))
    case False{} False{}:
      None{}

# ws://host[:port][/path][?query] and wss://; no userinfo ('@'), no
# fragment ('#'), no space or control byte
def url.clean(+s: String) -> Bool:
  Bool.not(String.contains(s, "@") || String.contains(s, "#") || String.contains(s, " ")
    || String.contains(s, "\t") || String.contains(s, "\r") || String.contains(s, "\n"))

def url.parse(+s: String) -> Maybe<&2, Url>:
  Bool.pick(Maybe<&2, Url>, url.clean(s),
    url.scheme(String.starts_with(s, "wss://"), String.starts_with(s, "ws://"), s), None{})

# the Host field: the port only when it is not the scheme's own
def url.authority(u: Url) -> String:
  match u:
    case Url{tls, +host, +port, path}:
      Bool.pick(String, U32.is_eq(port, Bool.pick(U32, tls, 443, 80)), host, host ++ ":" ++ U32.show(port))

# The opening request
# ===================

def protos(ps: List<&2, String>) -> String:
  String.join(ps, ", ")

def protos.line(+ps: List<&2, String>) -> String:
  Bool.pick(String, List.is_empty(&2, String, ps), "",
    "Sec-WebSocket-Protocol: " ++ protos(ps) ++ "\r\n")

# GET the resource, upgraded: the key is the base64 of sixteen random
# bytes; the version is 13; the subprotocols offered, if any, in order
def request(+u: Url, key: String, +ps: List<&2, String>) -> Bytes():
  match u:
    case Url{tls, host, port, path}:
      "GET " ++ path ++ " HTTP/1.1\r\nHost: " ++ url.authority(u)
        ++ "\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Key: " ++ key
        ++ "\r\nSec-WebSocket-Version: 13\r\n" ++ protos.line(ps) ++ "\r\n"

# the Sec-WebSocket-Accept a key must be answered with
def expect(key: Bytes()) -> Bytes():
  Bytes.from_list(Ws.accept(Bytes.to_list(key)))

# The answer
# ==========

# why a handshake failed: the URL; the name or the connection (code);
# the deadline; the head past its cap; the peer closed first; the head
# not HTTP/1.1 or not framed; a status not 101; the Upgrade, the
# Connection, the Accept, an extension, a subprotocol not as asked
type Hw is Data:
  HMalformed{}
  HStatus{code: U32}
  HUpgrade{}
  HConnection{}
  HAccept{}
  HExtension{}
  HProtocol{}

# the fields that matter, folded over the head: the Upgrade fields and
# whether each said websocket, whether a Connection had upgrade, the
# Accept values, whether an extension came, the subprotocols named, and
# whether any line was not a field
type Hs is Data:
  Hs{up: U32, upok: Bool, conn: Bool, acc: List<&2, Bytes()>, ext: Bool, proto: List<&2, Bytes()>, bad: Bool}

def hs.new() -> Hs:
  Hs{0, True{}, False{}, Nil{}, False{}, Nil{}, False{}}

# the ASCII letters lowered, no other byte touched
def low.b(+c: U32) -> U32:
  Bool.pick(U32, U32.is_le(65, c) && U32.is_le(c, 90), (c + 32 : U32), c)

def low(s: Bytes()) -> Bytes():
  match s:
    case SNil{}:
      SNil{}
    case SCon{Chr{c}, t}:
      SCon{Chr{low.b(c)}, low(t)}

def ows(+c: U32) -> Bool:
  U32.is_eq(c, 32) || U32.is_eq(c, 9)

def trim.cons(+c: U32, keep: Bool, rest: Bytes()) -> Bytes():
  match keep:
    case True{}:
      SCon{Chr{c}, rest}
    case False{}:
      rest

# the bytes from the first that is not a space or a tab
def trim.l(s: Bytes(), +keep: Bool) -> Bytes():
  match s:
    case SNil{}:
      SNil{}
    case SCon{Chr{+c}, t}:
      +k = keep || Bool.not(ows(c))
      trim.cons(c, k, trim.l(t, k))

# a value without the whitespace at either end (RFC 9110 5.5)
def trim(s: Bytes()) -> Bytes():
  String.reverse(trim.l(String.reverse(trim.l(s, False{})), False{}))

# a list's members, split at commas and trimmed; the comma walk keeps
# the member so far reversed
type Tk is Data:
  Tk{cur: Bytes(), acc: List<&2, Bytes()>}

def tk.at(cur: Bytes(), acc: List<&2, Bytes()>, c: U32, comma: Bool) -> Tk:
  match comma:
    case True{}:
      Tk{SNil{}, Con{trim(String.reverse(cur)), acc}}
    case False{}:
      Tk{SCon{Chr{c}, cur}, acc}

def tk.step(k: Tk, +c: U32) -> Tk:
  match k:
    case Tk{cur, acc}:
      tk.at(cur, acc, c, U32.is_eq(c, 44))

def tk.end(k: Tk) -> List<&2, Bytes()>:
  match k:
    case Tk{cur, acc}:
      Con{trim(String.reverse(cur)), acc}

def toks.go(s: Bytes(), k: Tk) -> Tk:
  match s:
    case SNil{}:
      k
    case SCon{Chr{c}, t}:
      toks.go(t, tk.step(k, c))

def toks(s: Bytes()) -> List<&2, Bytes()>:
  tk.end(toks.go(s, Tk{SNil{}, Nil{}}))

def has(xs: List<&2, Bytes()>, +x: Bytes()) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      String.eq(h, x) || has(t, x)

def has.str(xs: List<&2, String>, +x: Bytes()) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      String.eq(h, x) || has.str(t, x)

# one field: its name lowered, its value trimmed
def hs.field(name: Bytes(), +v: Bytes(), h: Hs) -> Hs:
  match h:
    case Hs{+up, upok, conn, +acc, ext, +proto, bad}:
      +n = low(name)
      Hs{Bool.pick(U32, String.eq(n, "upgrade"), (up + 1 : U32), up),
        upok && (Bool.not(String.eq(n, "upgrade")) || String.eq(low(v), "websocket")),
        conn || (String.eq(n, "connection") && has(toks(low(v)), "upgrade")),
        Bool.pick(List<&2, Bytes()>, String.eq(n, "sec-websocket-accept"), Con{v, acc}, acc),
        ext || String.eq(n, "sec-websocket-extensions"),
        Bool.pick(List<&2, Bytes()>, String.eq(n, "sec-websocket-protocol"), List.append(&2, Bytes(), toks(v), proto), proto),
        bad}

def hs.broken(h: Hs) -> Hs:
  match h:
    case Hs{up, upok, conn, acc, ext, proto, bad}:
      Hs{up, upok, conn, acc, ext, proto, True{}}

# a field name is one or more token bytes (RFC 9110 5.6.2): no space,
# no control, no separator; a line with none before its colon, or with
# no colon, or folded, is not a field
def tchar(+c: U32) -> Bool:
  U32.is_lt(32, c) && U32.is_lt(c, 127) && Bool.not(U32.is_eq(c, 58) || U32.is_eq(c, 34)
    || U32.is_eq(c, 40) || U32.is_eq(c, 41) || U32.is_eq(c, 44) || U32.is_eq(c, 47)
    || U32.is_eq(c, 59) || U32.is_eq(c, 60) || U32.is_eq(c, 61) || U32.is_eq(c, 62)
    || U32.is_eq(c, 63) || U32.is_eq(c, 64) || U32.is_eq(c, 91) || U32.is_eq(c, 92)
    || U32.is_eq(c, 93) || U32.is_eq(c, 123) || U32.is_eq(c, 125))

def token(s: Bytes()) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{Chr{c}, t}:
      tchar(c) && token(t)

# a value holds no control byte but the tab
def vchar(s: Bytes()) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{Chr{+c}, t}:
      (U32.is_eq(c, 9) || (U32.is_le(32, c) && Bool.not(U32.is_eq(c, 127)))) && vchar(t)

def hs.cut(+name: Bytes(), rest: Maybe<&2, Bytes()>, +h: Hs) -> Hs:
  match rest:
    case None{}:
      hs.broken(h)
    case Some{+v}:
      Bool.pick(Hs, Bool.not(String.is_empty(name)) && token(name) && vchar(v), hs.field(name, trim(v), h),
        hs.broken(h))

def hs.split(nr: Bytes() & Maybe<&2, Bytes()>, h: Hs) -> Hs:
  (name, rest) = nr
  hs.cut(name, rest, h)

def hs.line(l: Bytes(), h: Hs) -> Hs:
  hs.split(cut(l, 58), h)

def hs.lines(ls: List<&2, Bytes()>, h: Hs) -> Hs:
  match ls:
    case Nil{}:
      h
    case Con{l, t}:
      hs.lines(t, hs.line(l, h))

# The head as lines: cut at CR LF, the line so far reversed; a bare CR
# or LF breaks it
type Ln is Data:
  Ln{cur: Bytes(), ls: List<&2, Bytes()>, cr: Bool, bad: Bool}

def ln.at(cur: Bytes(), ls: List<&2, Bytes()>, cr: Bool, bad: Bool, +c: U32, isc: Bool, isl: Bool) -> Ln:
  match cr isc isl:
    case True{} _ True{}:
      Ln{SNil{}, Con{String.reverse(cur), ls}, False{}, bad}
    case True{} _ False{}:
      Ln{cur, ls, False{}, True{}}
    case False{} True{} _:
      Ln{cur, ls, True{}, bad}
    case False{} False{} True{}:
      Ln{cur, ls, False{}, True{}}
    case False{} False{} False{}:
      Ln{SCon{Chr{c}, cur}, ls, False{}, bad}

def ln.step(l: Ln, +c: U32) -> Ln:
  match l:
    case Ln{cur, ls, cr, bad}:
      ln.at(cur, ls, cr, bad, c, U32.is_eq(c, 13), U32.is_eq(c, 10))

def ln.go(s: Bytes(), l: Ln) -> Ln:
  match s:
    case SNil{}:
      l
    case SCon{Chr{c}, t}:
      ln.go(t, ln.step(l, c))

# the lines of a head (its blank line already cut off), first first,
# and whether it broke
def ln.end(l: Ln) -> List<&2, Bytes()> & Bool:
  match l:
    case Ln{cur, ls, cr, bad}:
      (List.reverse(&2, Bytes(), Con{String.reverse(cur), ls}), bad || cr)

def lines(s: Bytes()) -> List<&2, Bytes()> & Bool:
  ln.end(ln.go(s, Ln{SNil{}, Nil{}, False{}, False{}}))

# the status line: HTTP/1.1, a space, three digits, then the end or a
# space and a reason; the code, or 0 for a line that is not one
def dig(+c: U32) -> Bool:
  U32.is_le(48, c) && U32.is_le(c, 57)

def status.of(+a: U32, +b: U32, +c: U32, ok: Bool) -> U32:
  Bool.pick(U32, ok && dig(a) && dig(b) && dig(c),
    ((((a - 48 : U32) * 100 : U32) + ((b - 48 : U32) * 10 : U32) : U32) + (c - 48 : U32) : U32), 0)

def status.tail(+a: U32, +b: U32, +c: U32, t: Bytes()) -> U32:
  match t:
    case SNil{}:
      status.of(a, b, c, True{})
    case SCon{Chr{+s}, u}:
      status.of(a, b, c, U32.is_eq(s, 32) && vchar(u))

def status.code(s: Bytes()) -> U32:
  match s:
    case SCon{Chr{+a}, t}:
      match t:
        case SCon{Chr{+b}, u}:
          match u:
            case SCon{Chr{+c}, v}:
              status.tail(a, b, c, v)
            case SNil{}:
              0
        case SNil{}:
          0
    case SNil{}:
      0

def status(+l: Bytes()) -> U32:
  Bool.pick(U32, String.starts_with(l, "HTTP/1.1 "), status.code(String.drop(l, 9n)), 0)

# The judge
# =========

# the subprotocol the server chose: none, or one it was offered, once
def j.proto(offered: List<&2, String>, got: List<&2, Bytes()>) -> Result<&2, &2, Hw, Bytes()>:
  match got:
    case Nil{}:
      Done{""}
    case Con{+p, t}:
      Bool.pick(Result<&2, &2, Hw, Bytes()>, List.is_empty(&2, Bytes(), t) && has.str(offered, p),
        Done{p}, Fail{HProtocol{}})

def j.ext(offered: List<&2, String>, proto: List<&2, Bytes()>, ext: Bool) -> Result<&2, &2, Hw, Bytes()>:
  match ext:
    case True{}:
      Fail{HExtension{}}
    case False{}:
      j.proto(offered, proto)

# the Accept, when it came once: the handshake goes on exactly when it
# is the one the key asks for (hs_accept)
def j.acc1(offered: List<&2, String>, proto: List<&2, Bytes()>, ext: Bool, same: Bool) ->
  Result<&2, &2, Hw, Bytes()>:
  match same:
    case True{}:
      j.ext(offered, proto, ext)
    case False{}:
      Fail{HAccept{}}

def j.acc(+want: Bytes(), offered: List<&2, String>, acc: List<&2, Bytes()>, ext: Bool, proto: List<&2, Bytes()>) ->
  Result<&2, &2, Hw, Bytes()>:
  match acc:
    case Nil{}:
      Fail{HAccept{}}
    case Con{a, t}:
      match t:
        case Nil{}:
          j.acc1(offered, proto, ext, String.eq(a, want))
        case Con{b, u}:
          Fail{HAccept{}}

def j.up.go(
  +want: Bytes(), offered: List<&2, String>, up: Bool, conn: Bool,
  acc: List<&2, Bytes()>, ext: Bool, proto: List<&2, Bytes()>
) -> Result<&2, &2, Hw, Bytes()>:
  match up conn:
    case False{} _:
      Fail{HUpgrade{}}
    case True{} False{}:
      Fail{HConnection{}}
    case True{} True{}:
      j.acc(want, offered, acc, ext, proto)

def j.up(
  +want: Bytes(), offered: List<&2, String>, +up: U32, upok: Bool, conn: Bool,
  acc: List<&2, Bytes()>, ext: Bool, proto: List<&2, Bytes()>
) -> Result<&2, &2, Hw, Bytes()>:
  j.up.go(want, offered, U32.is_eq(up, 1) && upok, conn, acc, ext, proto)

def j.st(
  +want: Bytes(), offered: List<&2, String>, +status: U32, up: U32, upok: Bool, conn: Bool,
  acc: List<&2, Bytes()>, ext: Bool, proto: List<&2, Bytes()>, sw: Bool
) -> Result<&2, &2, Hw, Bytes()>:
  match sw:
    case False{}:
      Fail{HStatus{status}}
    case True{}:
      j.up(want, offered, up, upok, conn, acc, ext, proto)

def j.go(
  +want: Bytes(), offered: List<&2, String>, +status: U32, up: U32, upok: Bool, conn: Bool,
  acc: List<&2, Bytes()>, ext: Bool, proto: List<&2, Bytes()>, bad: Bool
) -> Result<&2, &2, Hw, Bytes()>:
  match bad:
    case True{}:
      Fail{HMalformed{}}
    case False{}:
      j.st(want, offered, status, up, upok, conn, acc, ext, proto, U32.is_eq(status, 101))

# the verdict on a head already read into its fields, in the order the
# RFC gives the checks: the subprotocol chosen, or why not
def judge(+want: Bytes(), offered: List<&2, String>, +status: U32, h: Hs) -> Result<&2, &2, Hw, Bytes()>:
  match h:
    case Hs{up, upok, conn, acc, ext, proto, bad}:
      j.go(want, offered, status, up, upok, conn, acc, ext, proto, bad)

def answer.go(+want: Bytes(), offered: List<&2, String>, lb: List<&2, Bytes()> & Bool) -> Result<&2, &2, Hw, Bytes()>:
  (ls, bad) = lb
  match ls:
    case Nil{}:
      Fail{HMalformed{}}
    case Con{+l, t}:
      judge(want, offered, status(l),
        hs.lines(t, Bool.pick(Hs, bad, hs.broken(hs.new()), hs.new())))

# The server's head (up to its blank line, not including it), judged for
# the key sent and the subprotocols offered.
def answer(key: Bytes(), offered: List<&2, String>, head: Bytes()) -> Result<&2, &2, Hw, Bytes()>:
  answer.go(expect(key), offered, lines(head))

def hw.show(w: Hw) -> String:
  match w:
    case HMalformed{}:
      "the answer is not an HTTP/1.1 head"
    case HStatus{c}:
      "status " ++ U32.show(c) ++ ", not 101"
    case HUpgrade{}:
      "no Upgrade: websocket"
    case HConnection{}:
      "no Connection: Upgrade"
    case HAccept{}:
      "Sec-WebSocket-Accept is not the key's"
    case HExtension{}:
      "an extension nobody asked for"
    case HProtocol{}:
      "a subprotocol nobody offered"

# whether a verdict lets the connection go on
def ok(r: Result<&2, &2, Hw, Bytes()>) -> Bool:
  match r:
    case Done{p}:
      True{}
    case Fail{w}:
      False{}

# The server's end
# ================
#
# RFC 6455 4.2 as net/ws_server.bend answers an opening request. The
# engine's reader (demos/io_http_engine) has read the head already:
# asked is whether it was an HTTP/1.1 request with Upgrade: websocket, a
# Connection naming upgrade, a Sec-WebSocket-Key, and no
# Sec-WebSocket-Version but 13 (the engine reads a missing one as 13);
# key is the key as it came, trimmed. The request is answered:
#
#   not asked                  426 Upgrade Required (it may ask again)
#   asked, not GET, or a key
#   that is not sixteen bytes
#   in base64                  400
#   asked, GET, the key good   101, the Accept its key earns, and the
#                              subprotocol chosen when it is one the
#                              client offered; no extension, whatever
#                              was offered (permessage-deflate is
#                              declined by not naming it, RFC 7692 5)

# A key is sixteen random bytes in base64: 22 characters of the alphabet
# and "==", 24 in all (RFC 6455 4.1; the engine's key.ok).
def key.b64(+c: U32) -> Bool:
  (U32.is_le(65, c) && U32.is_le(c, 90)) || (U32.is_le(97, c) && U32.is_le(c, 122))
    || (U32.is_le(48, c) && U32.is_le(c, 57)) || U32.is_eq(c, 43) || U32.is_eq(c, 47)

def key.at(+i: U32, +c: U32) -> Bool:
  (U32.is_lt(i, 22) && key.b64(c)) || (U32.is_le(22, i) && U32.is_eq(c, 61))

def key.go(bs: Bytes(), +i: U32, ok: Bool) -> Bool:
  match bs:
    case SNil{}:
      ok && U32.is_eq(i, 24)
    case SCon{Chr{+c}, t}:
      key.go(t, (i + 1 : U32), ok && key.at(i, c))

def key.ok(key: Bytes()) -> Bool:
  key.go(key, 0, True{})

# the server's verdict: the 101's head, or the status that refuses
type Sv is Data:
  SOk{head: Bytes()}
  SNo{status: U32}

# the subprotocol the answer names: the one chosen, when the client
# offered it; else none
def s.chosen(+proto: Bytes(), offered: List<&2, Bytes()>) -> Bytes():
  Bool.pick(Bytes(), has(offered, proto) && Bool.not(String.is_empty(proto)), proto, "")

def s.proto.line(+p: Bytes()) -> Bytes():
  Bool.pick(Bytes(), String.is_empty(p), "", "Sec-WebSocket-Protocol: " ++ p ++ "\r\n")

# the 101 (RFC 6455 4.2.2 5): the status line, Upgrade, Connection, the
# Accept, the subprotocol if one, and the blank line
def s.head(+key: Bytes(), +p: Bytes()) -> Bytes():
  "HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: "
    ++ expect(key) ++ "\r\n" ++ s.proto.line(p) ++ "\r\n"

# the refusal, if any: none for a GET that asked with a good key; else
# an ask that did not come is 426, and one that came broken (not a GET,
# a key not a key) is 400
def s.check.at(+asked: Bool, ok: Bool) -> Maybe<&2, U32>:
  match ok:
    case True{}:
      None{}
    case False{}:
      Some{Bool.pick(U32, asked, 400, 426)}

def s.check(+get: Bool, +asked: Bool, +key: Bytes()) -> Maybe<&2, U32>:
  s.check.at(asked, get && asked && key.ok(key))

def s.answer.at(+key: Bytes(), offered: List<&2, Bytes()>, +proto: Bytes(), no: Maybe<&2, U32>) -> Sv:
  match no:
    case Some{c}:
      SNo{c}
    case None{}:
      SOk{s.head(key, s.chosen(proto, offered))}

# The answer to an opening request: get is whether its method is GET,
# asked and key what the engine read, offered the subprotocols it
# offered, proto the one the handler chose ("" for none).
def s.answer(+get: Bool, +asked: Bool, +key: Bytes(), offered: List<&2, Bytes()>, +proto: Bytes()) -> Sv:
  s.answer.at(key, offered, proto, s.check(get, asked, key))

# whether a verdict refuses, with 400 or 426
def s.refused(v: Sv) -> Bool:
  match v:
    case SOk{h}:
      False{}
    case SNo{+c}:
      U32.is_eq(c, 400) || U32.is_eq(c, 426)

# the subprotocols a request offered: every Sec-WebSocket-Protocol
# field's list (vs, the fields' values in order), in order, the empty
# members dropped
def s.offered(vs: List<&2, Bytes()>) -> List<&2, Bytes()>:
  match vs:
    case Nil{}:
      Nil{}
    case Con{v, t}:
      List.append(&2, Bytes(), List.filter(~Bytes(), ~(x => Bool.not(String.is_empty(x))), List.reverse(&2, Bytes(), toks(v))),
        s.offered(t))
