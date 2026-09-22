# The laws of the HTTP engine. The human states them; PROOF.bend must
# prove them. They pin the three things a byte-at-a-time protocol
# reader has to get right, and the one optimisation that would
# otherwise be a comment nobody checks.
import Base
import ./main.bend as Eng
import ./sha1.bend as Sha1
import ./b64.bend as B64
import ./ws.bend as Ws
import ./spec.bend as Spec

# LAW: chunking does not change the parse. Feeding a chunk and then
# another one lands exactly where feeding the two joined would have.
# This is the property that makes the reader safe against however TCP
# decides to split a message: a head cut in the middle of a field name,
# a body cut mid-byte, or three requests arriving in one segment all
# parse the same as the whole stream. It is also what lets the engine
# keep no buffer of its own.
law feed_split:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +p: Eng.P
  {Eng.feed(List.append(&2, U32, a, b), p) ==
    Eng.feed(b, Eng.feed(a, p)) : Eng.P}

# LAW: a broken grammar stays broken. No byte moves the reader out of
# Bad{}, so once a message has been refused nothing later in the stream
# can revive it. Without this a smuggled request could follow a refused
# one on the same connection and be served.
law bad_absorbs:
  for +c: U32
  for +pd: Eng.Pend
  for +out: List<&2, Eng.Req>
  {Eng.step(Eng.P{Eng.Bad{}, pd, out}, c) ==
    Eng.P{Eng.Bad{}, pd, out} : Eng.P}

# LAW: and it stays broken for a whole chunk, not just one byte.
law bad_feeds:
  for +s: List<&2, U32>
  for +pd: Eng.Pend
  for +out: List<&2, Eng.Req>
  {Eng.feed(s, Eng.P{Eng.Bad{}, pd, out}) ==
    Eng.P{Eng.Bad{}, pd, out} : Eng.P}

# Framing
# =======
#
# spec.bend is the reference: RFC 9110's character sets and field
# names, written the obvious way. These laws hold the reader to it --
# over every byte, every name, every message state -- and then pin the
# vectors requests are smuggled with, run through the real reader.

# LAW: the reader's classes are the RFC's, byte for byte, all 256 of
# them; and so is its lowercasing. Every law below that speaks of a
# byte's class speaks of these.
law cls_is_spec:
  {Spec.cls.eng(Spec.all()) == Spec.cls.ref(Spec.all()) : List<&2, Eng.Cls>}

law lower_is_spec:
  {Spec.lower.eng(Spec.all()) == Spec.lower.ref(Spec.all()) : List<&2, U32>}

# LAW: a field is known by its bytes. For every name the reader can
# hold, the field it takes that name for is the reference's: the one
# spelled with exactly those bytes, or none. No other name is ever a
# Content-Length or a Transfer-Encoding, whatever it hashes to.
law field_by_bytes:
  for +k: List<&2, U32>
  {Eng.fld.of(k) == Spec.field(k) : Eng.Fld}

# LAW: a Transfer-Encoding is refused at its colon, whatever message it
# is in and whatever came before it.
law te_refused:
  for +k: List<&2, U32>
  for +pd: Eng.Pend
  for +out: List<&2, Eng.Req>
  for e: {Spec.eq(k, Spec.name("transfer-encoding")) == True{} : Bool}
  {Eng.step(Eng.P{Eng.InN{k}, pd, out}, 58) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}

# LAW: a name is a token and ends at its colon. Any other byte in it --
# a space or a tab before the colon, a CR with no colon, a bare LF, a
# control -- is refused, in every message.
law name_refuses:
  for +c: U32
  for +n: List<&2, U32>
  for +pd: Eng.Pend
  for +out: List<&2, Eng.Req>
  for e: {Spec.in.name(Eng.cls(c)) == False{} : Bool}
  {Eng.step(Eng.P{Eng.InN{n}, pd, out}, c) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}

# LAW: a field line starts with a token byte, or is the blank line. A
# line folded onto the one before it starts with a space or a tab, and
# is refused; so is a bare LF there.
law line_refuses:
  for +c: U32
  for +pd: Eng.Pend
  for +out: List<&2, Eng.Req>
  for e: {Spec.in.line(Eng.cls(c)) == False{} : Bool}
  {Eng.step(Eng.P{Eng.Lin{}, pd, out}, c) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}

# LAW: a Content-Length is digits, then whitespace, then its CR. A sign,
# a comma, a letter, a control is refused where it stands, whatever the
# digits so far, in every message.
law clen_refuses:
  for +c: U32
  for +v: U32
  for +pd: Eng.Pend
  for +out: List<&2, Eng.Req>
  for e: {Spec.in.clen(Eng.cls(c)) == False{} : Bool}
  {Eng.step(Eng.P{Eng.InL{v}, pd, out}, c) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}

# LAW: and a second Content-Length that disagrees with the first is
# refused as it closes (RFC 9112 6.3), whatever else the message says.
law clen_disagree:
  for +v: U32
  for +w: U32
  for +m: Eng.Meth
  for +path: List<&2, U32>
  for +cl: Bool
  for +h: Eng.Hosts
  for +ws: Eng.Up
  for +out: List<&2, Eng.Req>
  for e: {U32.is_eq(w, v) == False{} : Bool}
  {Eng.step(Eng.P{Eng.InL{w}, Eng.Pend{m, path, Eng.Has{v}, cl, h, ws}, out}, 13) ==
    Eng.P{Eng.Bad{}, Eng.Pend{m, path, Eng.Has{v}, cl, h, ws}, out} : Eng.P}

# LAW: the target carries no control, tab or line end: a CR, LF or NUL
# in it is refused, so none reaches a route or the log.
law target_refuses:
  for +c: U32
  for +p: List<&2, U32>
  for +pd: Eng.Pend
  for +out: List<&2, Eng.Req>
  for e: {Spec.in.target(Eng.cls(c)) == False{} : Bool}
  {Eng.step(Eng.P{Eng.InT{p}, pd, out}, c) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}

# LAW: a value carries no bare LF and no control: in any field this
# engine does not act on, and in Connection, where it would otherwise
# end a line the next hop reads differently.
law value_refuses:
  for +c: U32
  for +pd: Eng.Pend
  for +out: List<&2, Eng.Req>
  for e: {Spec.in.value(Eng.cls(c)) == False{} : Bool}
  {Eng.step(Eng.P{Eng.InLx{}, pd, out}, c) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}

law conn_refuses:
  for +c: U32
  for +t: List<&2, U32>
  for +a: Bool
  for +b: Bool
  for +pd: Eng.Pend
  for +out: List<&2, Eng.Req>
  for e: {Spec.in.value(Eng.cls(c)) == False{} : Bool}
  {Eng.step(Eng.P{Eng.InLc{t, a, b}, pd, out}, c) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}

# LAW: a head without exactly one Host is refused at its blank line
# (RFC 9112 3.2), whatever else it carried.
law host_once:
  for +m: Eng.Meth
  for +path: List<&2, U32>
  for +l: Eng.Cl
  for +cl: Bool
  for +h: Eng.Hosts
  for +ws: Eng.Up
  for +out: List<&2, Eng.Req>
  for e: {Spec.one(h) == False{} : Bool}
  {Eng.step(Eng.P{Eng.CrL{}, Eng.Pend{m, path, l, cl, h, ws}, out}, 10) ==
    Eng.P{Eng.Bad{}, Eng.Pend{m, path, l, cl, h, ws}, out} : Eng.P}

# LAW: after a request that asked to upgrade, nothing is read as HTTP:
# every byte is kept, in order, for the frame reader, and no message
# is completed.
law rest_feeds:
  for +s: List<&2, U32>
  for +bs: List<&2, U32>
  for +pd: Eng.Pend
  for +out: List<&2, Eng.Req>
  {Eng.feed(s, Eng.P{Eng.Rest{bs}, pd, out}) ==
    Eng.P{Eng.Rest{List.reverse.go(&2, U32, s, bs)}, pd, out} : Eng.P}

# LAW: the vectors. Each is a whole input run through the real reader
# from a fresh state -- the messages it completed, and whether it
# refused -- and feed_split carries each one to every way TCP could
# have cut it. First what is served as it should be.
law parse_get:
  {Eng.parse(Eng.bytes("GET /health HTTP/1.1\r\nHost: x\r\n\r\n")) ==
    ([Eng.Req{Eng.MGet{}, Eng.bytes("/health"), Nil{}, False{}, False{}, Nil{}}], False{}) :
    List<&2, Eng.Req> & Bool}

law parse_body:
  {Eng.parse(Eng.bytes("GET /echo HTTP/1.1\r\nhost: x\r\nCoNtEnT-LeNgTh:\t5 \r\n\r\nhello")) ==
    ([Eng.Req{Eng.MGet{}, Eng.bytes("/echo"), Eng.bytes("hello"), False{}, False{}, Nil{}}], False{}) :
    List<&2, Eng.Req> & Bool}

# a name that hashes as Content-Length did is not one: the bytes after
# its head are the next request, not its body
law parse_hash_twin:
  {Eng.parse(Eng.bytes("GET /echo HTTP/1.1\r\nHost: x\r\nx-v5fged: 5\r\n\r\nhelloGET / HTTP/1.1\r\nHost: x\r\n\r\n")) ==
    ([Eng.Req{Eng.MGet{}, Eng.bytes("/echo"), Nil{}, False{}, False{}, Nil{}},
      Eng.Req{Eng.MOther{}, Eng.bytes("/"), Nil{}, False{}, False{}, Nil{}}], False{}) :
    List<&2, Eng.Req> & Bool}

# two lengths that agree are one length; empty lines before a request
# line are skipped; close anywhere in a Connection list closes
law parse_agree:
  {Eng.parse(Eng.bytes("\r\n\r\nHEAD /echo HTTP/1.1\r\nHost: x\r\nContent-Length: 2\r\nConnection: keep-alive, CLOSE\r\ncontent-length: 2\r\n\r\nhi")) ==
    ([Eng.Req{Eng.MHead{}, Eng.bytes("/echo"), Eng.bytes("hi"), True{}, False{}, Nil{}}], False{}) :
    List<&2, Eng.Req> & Bool}

# the upgrade a browser asks for, Connection a list; what follows it is
# kept for the frame reader
law parse_upgrade:
  {Eng.parse(Eng.bytes("GET /ws HTTP/1.1\r\nHost: x\r\nUpgrade: websocket\r\nConnection: keep-alive, Upgrade\r\nSec-WebSocket-Key: k\r\n\r\nGET / HTTP/1.1\r\n\r\n")) ==
    ([Eng.Req{Eng.MGet{}, Eng.bytes("/ws"), Nil{}, False{}, True{}, Eng.bytes("k")}], False{}) :
    List<&2, Eng.Req> & Bool}

law rest_upgrade:
  {Eng.p.rest(Eng.feed(Eng.cat(Eng.bytes("GET /ws HTTP/1.1\r\nHost: x\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Key: k\r\n\r\n"), [129, 128]), Eng.p.new())) ==
    [129, 128] : List<&2, U32>}

# LAW: and what is refused. None of these completes a message: each is
# how a request is smuggled past a reader that frames it another way.
law refuse_space_colon:
  {Eng.parse(Eng.bytes("GET /echo HTTP/1.1\r\nHost: x\r\nContent-Length : 5\r\n\r\nhello")) ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

law refuse_te_space_colon:
  {Eng.parse(Eng.bytes("GET /echo HTTP/1.1\r\nHost: x\r\nTransfer-Encoding : chunked\r\nContent-Length: 5\r\n\r\nhello")) ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

law refuse_te:
  {Eng.parse(Eng.bytes("GET /echo HTTP/1.1\r\nHost: x\r\nContent-Length: 5\r\nTRANSFER-encoding: chunked\r\n\r\n0\r\n\r\n")) ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

law refuse_two_lengths:
  {Eng.parse(Eng.bytes("GET /echo HTTP/1.1\r\nHost: x\r\nContent-Length: 3\r\nContent-Length: 5\r\n\r\nabcde")) ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

law refuse_wrap:
  {Eng.parse(Eng.bytes("GET /echo HTTP/1.1\r\nHost: x\r\nContent-Length: 4294967301\r\n\r\nhello")) ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

law refuse_past_cap:
  {Eng.parse(Eng.bytes("GET /echo HTTP/1.1\r\nHost: x\r\nContent-Length: 1048577\r\n")) ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

law refuse_not_digits:
  {Eng.parse(Eng.bytes("GET /echo HTTP/1.1\r\nHost: x\r\nContent-Length: 5x\r\n\r\nhello")) ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

law refuse_list:
  {Eng.parse(Eng.bytes("GET /echo HTTP/1.1\r\nHost: x\r\nContent-Length: 5, 5\r\n\r\nhello")) ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

law refuse_fold:
  {Eng.parse(Eng.bytes("GET /echo HTTP/1.1\r\nHost: x\r\nX: a\r\n Content-Length: 5\r\n\r\nhello")) ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

law refuse_bare_lf:
  {Eng.parse(Eng.bytes("GET /echo HTTP/1.1\r\nHost: x\r\nX: a\nContent-Length: 5\r\n\r\nhello")) ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

law refuse_no_colon:
  {Eng.parse(Eng.bytes("GET /echo HTTP/1.1\r\nHost: x\r\nFoo\r\nContent-Length: 5\r\n\r\nhello")) ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

law refuse_target_cr:
  {Eng.parse(Eng.bytes("GET /a\rb HTTP/1.1\r\nHost: x\r\n\r\n")) ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

law refuse_no_host:
  {Eng.parse(Eng.bytes("GET /health HTTP/1.1\r\n\r\n")) == (Nil{}, True{}) :
    List<&2, Eng.Req> & Bool}

law refuse_two_hosts:
  {Eng.parse(Eng.bytes("GET /health HTTP/1.1\r\nHost: a\r\nhost: a\r\n\r\n")) ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

law refuse_version:
  {Eng.parse(Eng.bytes("GET /health HTTP/1.0\r\nHost: x\r\n\r\n")) ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

# a refusal does not take back the message completed before it: its
# reply is owed, and goes out before the 400
law refuse_after_one:
  {Eng.parse(Eng.bytes("GET / HTTP/1.1\r\nHost: x\r\n\r\nGET / HTTP/1.1\r\nHost : x\r\n\r\n")) ==
    ([Eng.Req{Eng.MGet{}, Eng.bytes("/"), Nil{}, False{}, False{}, Nil{}}], True{}) :
    List<&2, Eng.Req> & Bool}

# LAW: a query is no part of the path a target routes by.
law path_query:
  {Eng.path.of(Eng.bytes("/health?x=/a?b")) == Eng.bytes("/health") : List<&2, U32>}

# LAW: the reply that ends a connection says so, and is otherwise the
# reply it was.
law health_closing:
  {Eng.closing(Eng.resp.health()) ==
    "HTTP/1.1 200 OK\r\ncontent-type: application/json\r\ncontent-length: 11\r\nconnection: close\r\n\r\n{\"ok\":true}" :
    Bytes()}

# LAW: the replies the engine keeps ready are the replies it would have
# built. Writing a fixed reply out by hand is worth roughly a third of
# the cost of serving a request, and it is exactly the kind of shortcut
# that rots: these five say the shortcut is the same bytes, so the
# checker refuses the engine if anyone edits one without the other.
law health_is_built:
  {Eng.resp.health() ==
    Eng.reply("200 OK", "application/json", "{\"ok\":true}") :
    Bytes()}

law root_is_built:
  {Eng.resp.root() ==
    Eng.reply("200 OK", "text/plain", "bend-http\n") :
    Bytes()}

law missing_is_built:
  {Eng.resp.missing() ==
    Eng.reply("404 Not Found", "text/plain", "no route\n") :
    Bytes()}

law method_is_built:
  {Eng.resp.method() ==
    Eng.reply.allow("405 Method Not Allowed", "text/plain", "no method\n") :
    Bytes()}

law bad_is_built:
  {Eng.resp.bad() ==
    Eng.closing(Eng.reply("400 Bad Request", "text/plain", "bad request\n")) :
    Bytes()}

# LAW: HEAD is GET's head. The scanner that cuts a reply at its blank
# line and the builder that writes a head from a length agree, byte for
# byte, on the replies the engine keeps ready.
law head_of_health:
  {Eng.head.of(Eng.resp.health()) ==
    Eng.reply.n.head("200 OK", Eng.bytes("application/json"), 11) :
    Bytes()}

law head_of_missing:
  {Eng.head.of(Eng.resp.missing()) ==
    Eng.reply.n.head("404 Not Found", Eng.bytes("text/plain"), 9) :
    Bytes()}

# LAW: the default table answers what the engine has always answered;
# with a root, the fixed routes still win and everything else is a file
# under it, "/" included.
law route_health:
  {Eng.route(Eng.routes(Eng.cfg.new()), Eng.bytes("/health")) ==
    Some{Eng.Health{}} : Maybe<&2, Eng.Act>}

law route_root:
  {Eng.route(Eng.routes(Eng.cfg.new()), Eng.bytes("/")) ==
    Some{Eng.Root{}} : Maybe<&2, Eng.Act>}

law route_echo:
  {Eng.route(Eng.routes(Eng.cfg.new()), Eng.bytes("/echo")) ==
    Some{Eng.Echo{}} : Maybe<&2, Eng.Act>}

law route_events:
  {Eng.route(Eng.routes(Eng.cfg.new()), Eng.bytes("/events")) ==
    Some{Eng.Events{}} : Maybe<&2, Eng.Act>}

law route_missing:
  {Eng.route(Eng.routes(Eng.cfg.new()), Eng.bytes("/nope")) ==
    None{} : Maybe<&2, Eng.Act>}

law route_files:
  {Eng.route(Eng.routes(Eng.cfg.set_root(Eng.cfg.new(), Eng.bytes("www"))),
    Eng.bytes("/css/site.css")) == Some{Eng.Files{}} : Maybe<&2, Eng.Act>}

law route_files_index:
  {Eng.route(Eng.routes(Eng.cfg.set_root(Eng.cfg.new(), Eng.bytes("www"))),
    Eng.bytes("/")) == Some{Eng.Files{}} : Maybe<&2, Eng.Act>}

law route_files_fixed:
  {Eng.route(Eng.routes(Eng.cfg.set_root(Eng.cfg.new(), Eng.bytes("www"))),
    Eng.bytes("/health")) == Some{Eng.Health{}} : Maybe<&2, Eng.Act>}

# LAW: no two entries of either table claim one path.
law routes_distinct:
  {Eng.distinct(Eng.routes(Eng.cfg.new())) == True{} : Bool}

law routes_distinct_root:
  {Eng.distinct(Eng.routes(Eng.cfg.set_root(Eng.cfg.new(), Eng.bytes("www")))) ==
    True{} : Bool}

# LAW: an empty table routes nothing, whatever is asked.
law route_empty:
  for +path: List<&2, U32>
  {Eng.route(Nil{}, path) == None{} : Maybe<&2, Eng.Act>}

# LAW: a request cannot name a file outside the root. The four pins
# fix the normaliser on the paths that matter, including the one that
# climbs from under a real directory.
law norm_climb:
  {Eng.norm(Eng.segs(Eng.bytes("/../etc/passwd"))) == None{} :
    Maybe<&2, List<&2, List<&2, U32>>>}

law norm_deep_climb:
  {Eng.norm(Eng.segs(Eng.bytes("/a/b/../../../x"))) == None{} :
    Maybe<&2, List<&2, List<&2, U32>>>}

law norm_dots:
  {Eng.norm(Eng.segs(Eng.bytes("/a/./b/../c/"))) ==
    Some{[Eng.bytes("a"), Eng.bytes("c")]} : Maybe<&2, List<&2, List<&2, U32>>>}

law norm_flat:
  {Eng.norm(Eng.segs(Eng.bytes("/sub/../a.txt"))) ==
    Some{[Eng.bytes("a.txt")]} : Maybe<&2, List<&2, List<&2, U32>>>}

# LAW: whatever follows it, a climb from the root is refused, not
# clamped: a clamped path is a path someone will probe.
law norm_climb_refused:
  for +ss: List<&2, List<&2, U32>>
  {Eng.norm(Con{[46, 46], ss}) == None{} : Maybe<&2, List<&2, List<&2, U32>>>}

# LAW: a climb right after a name cancels it, whatever follows.
law norm_climb_cancels:
  for +s: List<&2, U32>
  for +ss: List<&2, List<&2, U32>>
  for e: {Eng.piece(s) == Eng.Name{} : Eng.Piece}
  {Eng.norm(Con{s, Con{[46, 46], ss}}) == Eng.norm(ss) :
    Maybe<&2, List<&2, List<&2, U32>>>}

# What a file under the root may be named by, stated here on its own:
# every segment has bytes, each printable ASCII (33..126, so no NUL, no
# control byte, no space) and neither '/' nor '\'; and it is not a
# dotfile (a first byte of '.'), or, when dotfiles are served (dot), it
# is still neither "." nor "..".
def seg_byte(+c: U32) -> Bool:
  U32.is_le(33, c) && U32.is_le(c, 126) && Bool.not(U32.is_eq(c, 47))
    && Bool.not(U32.is_eq(c, 92))

def seg_bytes(bs: List<&2, U32>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{+c, t}:
      seg_byte(c) && seg_bytes(t)

def seg_lead(dot: Bool, +c: U32, +s: List<&2, U32>) -> Bool:
  match dot:
    case True{}:
      Bool.not(Eng.beq(s, [46], True{}) || Eng.beq(s, [46, 46], True{}))
    case False{}:
      Bool.not(U32.is_eq(c, 46))

def seg_ok(dot: Bool, s: List<&2, U32>) -> Bool:
  match s:
    case Nil{}:
      False{}
    case Con{+c, +t}:
      seg_lead(dot, c, Con{c, t}) && seg_bytes(Con{c, t})

def segs_ok(+dot: Bool, ss: List<&2, List<&2, U32>>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case Con{s, t}:
      seg_ok(dot, s) && segs_ok(dot, t)

def safe(+dot: Bool, may: Maybe<&2, List<&2, List<&2, U32>>>) -> Bool:
  match may:
    case None{}:
      True{}
    case Some{ss}:
      segs_ok(dot, ss)

# LAW: for every request target, the path a file is opened by is
# refused (a 404) or made only of segments the rule above allows, with
# dotfiles served or not. No "..", ".", empty segment, separator, NUL,
# control byte or dotfile ever reaches the file system.
law path_safe:
  for +dot: Bool
  for +t: List<&2, U32>
  {safe(dot, Eng.fnames.of(dot, t)) == True{} : Bool}

# LAW: a request target holding a control byte anywhere (below 32, or
# DEL) is never clean, so it never names a file.
law clean_refuses_control:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +c: U32
  for e: {(U32.is_lt(c, 32) || U32.is_eq(c, 127)) == True{} : Bool}
  {Eng.clean(List.append(&2, U32, a, Con{c, b})) == False{} : Bool}

# LAW: and one that is not clean names nothing, whatever it normalises to.
law unclean_names_nothing:
  for +dot: Bool
  for +t: List<&2, U32>
  for e: {Eng.clean(t) == False{} : Bool}
  {Eng.fnames.of(dot, t) == None{} : Maybe<&2, List<&2, List<&2, U32>>>}

# LAW: what the guard refuses, pinned: a dotfile, one under a real
# directory, a backslash, a NUL, and "..." (a name, so a dotfile);
# and a plain nested file passes.
law fnames_dotfile:
  {Eng.fnames.of(False{}, Eng.bytes("/.env")) == None{} :
    Maybe<&2, List<&2, List<&2, U32>>>}

law fnames_dotdir:
  {Eng.fnames.of(False{}, Eng.bytes("/a/.git/config")) == None{} :
    Maybe<&2, List<&2, List<&2, U32>>>}

law fnames_backslash:
  {Eng.fnames.of(True{}, Eng.bytes("/a\\..\\b")) == None{} :
    Maybe<&2, List<&2, List<&2, U32>>>}

law fnames_nul:
  {Eng.fnames.of(True{}, [47, 97, 0, 98]) == None{} :
    Maybe<&2, List<&2, List<&2, U32>>>}

law fnames_dots:
  {Eng.fnames.of(False{}, Eng.bytes("/...")) == None{} :
    Maybe<&2, List<&2, List<&2, U32>>>}

law fnames_plain:
  {Eng.fnames.of(False{}, Eng.bytes("/sub/b.css")) ==
    Some{[Eng.bytes("sub"), Eng.bytes("b.css")]} : Maybe<&2, List<&2, List<&2, U32>>>}

# LAW: SHA-1 is SHA-1. The three vectors of RFC 3174, computed by the
# checker through a Bend that shifts one bit at a time.
law sha1_empty:
  {Sha1.hash(Nil{}) ==
    [218, 57, 163, 238, 94, 107, 75, 13, 50, 85, 191, 239, 149, 96, 24, 144, 175, 216, 7, 9] : List<&2, U32>}

law sha1_abc:
  {Sha1.hash(Eng.bytes("abc")) ==
    [169, 153, 62, 54, 71, 6, 129, 106, 186, 62, 37, 113, 120, 80, 194, 108, 156, 208, 216, 157] : List<&2, U32>}

law sha1_two_blocks:
  {Sha1.hash(Eng.bytes("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")) ==
    [132, 152, 62, 68, 28, 59, 210, 110, 186, 174, 74, 161, 249, 81, 41, 229, 229, 70, 112, 241] : List<&2, U32>}

# LAW: base64 is base64: the seven vectors of RFC 4648.
law b64_empty:
  {B64.enc(Nil{}) == Nil{} : List<&2, U32>}

law b64_f:
  {B64.enc(Eng.bytes("f")) == Eng.bytes("Zg==") : List<&2, U32>}

law b64_fo:
  {B64.enc(Eng.bytes("fo")) == Eng.bytes("Zm8=") : List<&2, U32>}

law b64_foo:
  {B64.enc(Eng.bytes("foo")) == Eng.bytes("Zm9v") : List<&2, U32>}

law b64_foob:
  {B64.enc(Eng.bytes("foob")) == Eng.bytes("Zm9vYg==") : List<&2, U32>}

law b64_fooba:
  {B64.enc(Eng.bytes("fooba")) == Eng.bytes("Zm9vYmE=") : List<&2, U32>}

law b64_foobar:
  {B64.enc(Eng.bytes("foobar")) == Eng.bytes("Zm9vYmFy") : List<&2, U32>}

# LAW: the WebSocket accept key of RFC 6455's own example, computed by
# the engine's own Ws.accept: the nonce joined to Ws.guid(), hashed,
# encoded.
law ws_accept:
  {Ws.accept(Eng.bytes("dGhlIHNhbXBsZSBub25jZQ==")) ==
    Eng.bytes("s3pPLMBiTxaQ9kYGzzhZRbK+xOo=") : List<&2, U32>}

# LAW: chunking does not change the frame parse, as for requests: a
# frame split across reads lands where the whole would have.
law ws_feed_split:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +w: Ws.W
  {Ws.feed(List.append(&2, U32, a, b), w) == Ws.feed(b, Ws.feed(a, w)) : Ws.W}

# LAW: broken framing stays broken for the rest of the connection.
law ws_bad_absorbs:
  for +c: U32
  for +out: List<&2, Ws.Frm>
  {Ws.step(Ws.W{Ws.Bad{}, out}, c) == Ws.W{Ws.Bad{}, out} : Ws.W}

law ws_bad_feeds:
  for +s: List<&2, U32>
  for +out: List<&2, Ws.Frm>
  {Ws.feed(s, Ws.W{Ws.Bad{}, out}) == Ws.W{Ws.Bad{}, out} : Ws.W}

# LAW: the reader a connection runs walks a byte buffer, and it is the
# list reader above on that buffer's bytes, for every buffer and state.
law ws_feed_buf:
  for +b: Bytes()
  for +w: Ws.W
  {Ws.feed_buf(b, w) == Ws.feed(Bytes.to_list(b), w) : Ws.W}

# LAW: so chunking does not change the parse on buffers either.
law ws_feed_buf_split:
  for +a: Bytes()
  for +b: Bytes()
  for +w: Ws.W
  {Ws.feed_buf(Bytes.append(a, b), w) == Ws.feed_buf(b, Ws.feed_buf(a, w)) : Ws.W}

law ws_bad_feeds_buf:
  for +s: Bytes()
  for +out: List<&2, Ws.Frm>
  {Ws.feed_buf(s, Ws.W{Ws.Bad{}, out}) == Ws.W{Ws.Bad{}, out} : Ws.W}

# LAW: a masked client frame reads back as its opcode and its bytes:
# "hi" as text under the mask 1 2 3 4, and an empty ping; the same on
# the buffer path, whole and cut after the mask.
law ws_read_text:
  {Ws.take(Ws.feed([129, 130, 1, 2, 3, 4, 105, 107], Ws.new())) ==
    (Ws.W{Ws.Op{}, Nil{}}, [Ws.Frm{1, "hi"}]) : Ws.W & List<&2, Ws.Frm>}

law ws_read_ping:
  {Ws.take(Ws.feed([137, 128, 9, 9, 9, 9], Ws.new())) ==
    (Ws.W{Ws.Op{}, Nil{}}, [Ws.Frm{9, ""}]) : Ws.W & List<&2, Ws.Frm>}

law ws_read_text_buf:
  {Ws.take(Ws.feed_buf(Bytes.from_list([129, 130, 1, 2, 3, 4, 105, 107]), Ws.new())) ==
    (Ws.W{Ws.Op{}, Nil{}}, [Ws.Frm{1, "hi"}]) : Ws.W & List<&2, Ws.Frm>}

law ws_read_text_buf_cut:
  {Ws.take(Ws.feed_buf(Bytes.from_list([105, 107]),
    Ws.feed_buf(Bytes.from_list([129, 130, 1, 2, 3, 4]), Ws.new()))) ==
    (Ws.W{Ws.Op{}, Nil{}}, [Ws.Frm{1, "hi"}]) : Ws.W & List<&2, Ws.Frm>}

law ws_read_ping_buf:
  {Ws.take(Ws.feed_buf(Bytes.from_list([137, 128, 9, 9, 9, 9]), Ws.new())) ==
    (Ws.W{Ws.Op{}, Nil{}}, [Ws.Frm{9, ""}]) : Ws.W & List<&2, Ws.Frm>}

# LAW: an unmasked client frame, a fragment, and a reserved bit are each
# refused at the byte that shows them, on both paths.
law ws_unmasked_is_bad:
  {Ws.dead(Ws.feed([129, 2], Ws.new())) ==
    (Ws.W{Ws.Bad{}, Nil{}}, True{}) : Ws.W & Bool}

law ws_fragment_is_bad:
  {Ws.dead(Ws.feed([1], Ws.new())) == (Ws.W{Ws.Bad{}, Nil{}}, True{}) : Ws.W & Bool}

law ws_reserved_is_bad:
  {Ws.dead(Ws.feed([193], Ws.new())) == (Ws.W{Ws.Bad{}, Nil{}}, True{}) : Ws.W & Bool}

law ws_unmasked_is_bad_buf:
  {Ws.dead(Ws.feed_buf(Bytes.from_list([129, 2]), Ws.new())) ==
    (Ws.W{Ws.Bad{}, Nil{}}, True{}) : Ws.W & Bool}

law ws_fragment_is_bad_buf:
  {Ws.dead(Ws.feed_buf(Bytes.from_list([1]), Ws.new())) ==
    (Ws.W{Ws.Bad{}, Nil{}}, True{}) : Ws.W & Bool}

law ws_reserved_is_bad_buf:
  {Ws.dead(Ws.feed_buf(Bytes.from_list([193]), Ws.new())) ==
    (Ws.W{Ws.Bad{}, Nil{}}, True{}) : Ws.W & Bool}

# LAW: what the server writes, one block: a short frame, the two-byte
# length past 125, a close code.
law ws_frame_short:
  {Ws.frame(1, "hi") == Bytes.from_list([129, 2, 104, 105]) : Bytes()}

law ws_len_two_bytes:
  {Ws.len.bytes(300) == [126, 1, 44] : List<&2, U32>}

law ws_close_code:
  {Ws.close.frame(1002) == Bytes.from_list([136, 2, 3, 234]) : Bytes()}

# LAW: the batch budget. After a reply of any size joins the batch of
# pages being written, what stays waiting is below send.cap(): a batch
# at or past the cap has gone out. So the most a pipelined read ever
# holds unsent is the cap plus the one reply that crossed it.
law batch_under:
  for +k: U32
  {U32.is_lt(Eng.batch.keep(U32.cmp(k, Eng.send.cap()), k), Eng.send.cap()) ==
    True{} : Bool}

# LAW: the target cap, at its edge: a target of exactly k bytes is not
# past k, and one byte more is, whatever the bytes are.
law long_at:
  for +bs: List<&2, U32>
  {Eng.long(List.length(&2, U32, bs), bs) == False{} : Bool}

law long_past:
  for +bs: List<&2, U32>
  for +c: U32
  {Eng.long(List.length(&2, U32, bs), Con{c, bs}) == True{} : Bool}

# LAW: the head's clock. A read that leaves no head in progress (a body,
# the next request, nothing) drops the watch, and one that leaves a head
# in progress keeps the clock it started with, so reads that each arrive
# inside the idle time never restart it.
law hw_rest:
  for +hw: Eng.Hw
  {Eng.hw.next(False{}, hw) == Eng.NoHead{} : Eng.Hw}

law hw_keeps:
  for +t0: Nat
  for +n: U32
  {Eng.hw.next(True{}, Eng.Since{t0, n}) == Eng.Since{t0, n} : Eng.Hw}

# LAW: RFC 6455's example key has the shape a key must have; one a
# character short, one with a character outside base64, and one without
# its padding do not.
law key_rfc:
  {Eng.key.ok(Eng.bytes("dGhlIHNhbXBsZSBub25jZQ=="), 0, True{}) == True{} : Bool}

law key_short:
  {Eng.key.ok(Eng.bytes("dGhlIHNhbXBsZSBub25jZQ="), 0, True{}) == False{} : Bool}

law key_alphabet:
  {Eng.key.ok(Eng.bytes("dGhlIHNhbXBsZSBub25jZ.=="), 0, True{}) == False{} : Bool}

law key_padding:
  {Eng.key.ok(Eng.bytes("dGhlIHNhbXBsZSBub25jZQAA"), 0, True{}) == False{} : Bool}

# LAW: an upgrade that names version 13 asks to upgrade, and one that
# names another does not, whatever else it carried
law parse_version_13:
  {Eng.parse(Eng.bytes("GET /ws HTTP/1.1\r\nHost: x\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Key: k\r\nSec-WebSocket-Version: 13\r\n\r\n")) ==
    ([Eng.Req{Eng.MGet{}, Eng.bytes("/ws"), Nil{}, False{}, True{}, Eng.bytes("k")}], False{}) :
    List<&2, Eng.Req> & Bool}

law parse_version_other:
  {Eng.parse(Eng.bytes("GET /ws HTTP/1.1\r\nHost: x\r\nSec-WebSocket-Version: 8\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Key: k\r\n\r\n")) ==
    ([Eng.Req{Eng.MGet{}, Eng.bytes("/ws"), Nil{}, False{}, False{}, Eng.bytes("k")}], False{}) :
    List<&2, Eng.Req> & Bool}
