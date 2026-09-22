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

# LAW: the walk a connection runs is the reader above. feed_buf takes a
# read as one packed block and cuts whole runs out of it -- a target, a
# body, a value it skips -- where feed steps a byte at a time; for every
# block and every reader state the two land in the same place. So every
# law of feed is a law of the engine.
law feed_buf_is_feed:
  for +b: Bytes()
  for +p: Eng.P
  {Eng.feed_buf(b, p) == Eng.feed(Bytes.to_list(b), p) : Eng.P}

# LAW: and chunking does not change the parse on blocks either.
law feed_buf_split:
  for +a: Bytes()
  for +b: Bytes()
  for +p: Eng.P
  {Eng.feed_buf(Bytes.append(a, b), p) == Eng.feed_buf(b, Eng.feed_buf(a, p)) : Eng.P}

law bad_feeds_buf:
  for +s: Bytes()
  for +pd: Eng.Pend
  for +out: List<&2, Eng.Req>
  {Eng.feed_buf(s, Eng.P{Eng.Bad{}, pd, out}) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}

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

# a name is lowercased whole where it closes, and that lowering is the
# reference's on every byte too
law lows_is_spec:
  {Eng.lows(Bytes.from_list(Spec.all())) == Spec.lows(Bytes.from_list(Spec.all())) : Bytes()}

# LAW: a field is known by its bytes. For every name the reader can
# look up, the field it takes that name for is the reference's: the one
# spelled with exactly those bytes, or none. No other name is ever a
# Content-Length or a Transfer-Encoding, whatever it hashes to.
law field_by_bytes:
  for +k: Bytes()
  {Eng.fld.of(k) == Spec.field(k) : Eng.Fld}

# LAW: a Transfer-Encoding is refused at its colon, in whatever case it
# was written, whatever message it is in and whatever came before it.
law te_refused:
  for +k: Bytes()
  for +pd: Eng.Pend
  for +out: List<&2, Eng.Req>
  for e: {Spec.eq(Eng.lows(k), Spec.name("transfer-encoding")) == True{} : Bool}
  {Eng.step(Eng.P{Eng.InN{k}, pd, out}, 58) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}

# LAW: a name is a token and ends at its colon. Any other byte in it --
# a space or a tab before the colon, a CR with no colon, a bare LF, a
# control -- is refused, in every message.
law name_refuses:
  for +c: U32
  for +n: Bytes()
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
  for +path: Bytes()
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
  for +p: Bytes()
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
  for +t: Bytes()
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
  for +path: Bytes()
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
  for +s: Bytes()
  for +bs: Bytes()
  for +pd: Eng.Pend
  for +out: List<&2, Eng.Req>
  {Eng.feed_buf(s, Eng.P{Eng.Rest{bs}, pd, out}) ==
    Eng.P{Eng.Rest{Bytes.append(bs, s)}, pd, out} : Eng.P}

# LAW: the vectors. Each is a whole input run through the real reader
# from a fresh state -- the messages it completed, and whether it
# refused -- and feed_split carries each one to every way TCP could
# have cut it. First what is served as it should be.
law parse_get:
  {Eng.parse("GET /health HTTP/1.1\r\nHost: x\r\n\r\n") ==
    ([Eng.Req{Eng.MGet{}, "/health", "", False{}, False{}, ""}], False{}) :
    List<&2, Eng.Req> & Bool}

law parse_body:
  {Eng.parse("GET /echo HTTP/1.1\r\nhost: x\r\nCoNtEnT-LeNgTh:\t5 \r\n\r\nhello") ==
    ([Eng.Req{Eng.MGet{}, "/echo", "hello", False{}, False{}, ""}], False{}) :
    List<&2, Eng.Req> & Bool}

# a name that hashes as Content-Length did is not one: the bytes after
# its head are the next request, not its body
law parse_hash_twin:
  {Eng.parse("GET /echo HTTP/1.1\r\nHost: x\r\nx-v5fged: 5\r\n\r\nhelloGET / HTTP/1.1\r\nHost: x\r\n\r\n") ==
    ([Eng.Req{Eng.MGet{}, "/echo", "", False{}, False{}, ""},
      Eng.Req{Eng.MOther{}, "/", "", False{}, False{}, ""}], False{}) :
    List<&2, Eng.Req> & Bool}

# two lengths that agree are one length; empty lines before a request
# line are skipped; close anywhere in a Connection list closes
law parse_agree:
  {Eng.parse("\r\n\r\nHEAD /echo HTTP/1.1\r\nHost: x\r\nContent-Length: 2\r\nConnection: keep-alive, CLOSE\r\ncontent-length: 2\r\n\r\nhi") ==
    ([Eng.Req{Eng.MHead{}, "/echo", "hi", True{}, False{}, ""}], False{}) :
    List<&2, Eng.Req> & Bool}

# the upgrade a browser asks for, Connection a list; what follows it is
# kept for the frame reader
law parse_upgrade:
  {Eng.parse("GET /ws HTTP/1.1\r\nHost: x\r\nUpgrade: websocket\r\nConnection: keep-alive, Upgrade\r\nSec-WebSocket-Key: k\r\n\r\nGET / HTTP/1.1\r\n\r\n") ==
    ([Eng.Req{Eng.MGet{}, "/ws", "", False{}, True{}, "k"}], False{}) :
    List<&2, Eng.Req> & Bool}

law rest_upgrade:
  {Eng.p.rest(Eng.feed_buf(Bytes.append("GET /ws HTTP/1.1\r\nHost: x\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Key: k\r\n\r\n", Bytes.from_list([129, 128])), Eng.p.new())) ==
    Bytes.from_list([129, 128]) : Bytes()}

# LAW: and what is refused. None of these completes a message: each is
# how a request is smuggled past a reader that frames it another way.
law refuse_space_colon:
  {Eng.parse("GET /echo HTTP/1.1\r\nHost: x\r\nContent-Length : 5\r\n\r\nhello") ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

law refuse_te_space_colon:
  {Eng.parse("GET /echo HTTP/1.1\r\nHost: x\r\nTransfer-Encoding : chunked\r\nContent-Length: 5\r\n\r\nhello") ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

law refuse_te:
  {Eng.parse("GET /echo HTTP/1.1\r\nHost: x\r\nContent-Length: 5\r\nTRANSFER-encoding: chunked\r\n\r\n0\r\n\r\n") ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

law refuse_two_lengths:
  {Eng.parse("GET /echo HTTP/1.1\r\nHost: x\r\nContent-Length: 3\r\nContent-Length: 5\r\n\r\nabcde") ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

law refuse_wrap:
  {Eng.parse("GET /echo HTTP/1.1\r\nHost: x\r\nContent-Length: 4294967301\r\n\r\nhello") ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

law refuse_past_cap:
  {Eng.parse("GET /echo HTTP/1.1\r\nHost: x\r\nContent-Length: 1048577\r\n") ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

law refuse_not_digits:
  {Eng.parse("GET /echo HTTP/1.1\r\nHost: x\r\nContent-Length: 5x\r\n\r\nhello") ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

law refuse_list:
  {Eng.parse("GET /echo HTTP/1.1\r\nHost: x\r\nContent-Length: 5, 5\r\n\r\nhello") ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

law refuse_fold:
  {Eng.parse("GET /echo HTTP/1.1\r\nHost: x\r\nX: a\r\n Content-Length: 5\r\n\r\nhello") ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

law refuse_bare_lf:
  {Eng.parse("GET /echo HTTP/1.1\r\nHost: x\r\nX: a\nContent-Length: 5\r\n\r\nhello") ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

law refuse_no_colon:
  {Eng.parse("GET /echo HTTP/1.1\r\nHost: x\r\nFoo\r\nContent-Length: 5\r\n\r\nhello") ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

law refuse_target_cr:
  {Eng.parse("GET /a\rb HTTP/1.1\r\nHost: x\r\n\r\n") ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

law refuse_no_host:
  {Eng.parse("GET /health HTTP/1.1\r\n\r\n") == (Nil{}, True{}) :
    List<&2, Eng.Req> & Bool}

law refuse_two_hosts:
  {Eng.parse("GET /health HTTP/1.1\r\nHost: a\r\nhost: a\r\n\r\n") ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

law refuse_version:
  {Eng.parse("GET /health HTTP/1.0\r\nHost: x\r\n\r\n") ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

# a refusal does not take back the message completed before it: its
# reply is owed, and goes out before the 400
law refuse_after_one:
  {Eng.parse("GET / HTTP/1.1\r\nHost: x\r\n\r\nGET / HTTP/1.1\r\nHost : x\r\n\r\n") ==
    ([Eng.Req{Eng.MGet{}, "/", "", False{}, False{}, ""}], True{}) :
    List<&2, Eng.Req> & Bool}

# LAW: a query is no part of the path a target routes by.
law path_query:
  {Eng.path.of("/health?x=/a?b") == "/health" : Bytes()}

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
  {Eng.route(Eng.routes(Eng.cfg.new()), "/health") ==
    Some{Eng.Health{}} : Maybe<&2, Eng.Act>}

law route_root:
  {Eng.route(Eng.routes(Eng.cfg.new()), "/") ==
    Some{Eng.Root{}} : Maybe<&2, Eng.Act>}

law route_echo:
  {Eng.route(Eng.routes(Eng.cfg.new()), "/echo") ==
    Some{Eng.Echo{}} : Maybe<&2, Eng.Act>}

law route_events:
  {Eng.route(Eng.routes(Eng.cfg.new()), "/events") ==
    Some{Eng.Events{}} : Maybe<&2, Eng.Act>}

law route_missing:
  {Eng.route(Eng.routes(Eng.cfg.new()), "/nope") ==
    None{} : Maybe<&2, Eng.Act>}

law route_files:
  {Eng.route(Eng.routes(Eng.cfg.set_root(Eng.cfg.new(), Eng.bytes("www"))),
    "/css/site.css") == Some{Eng.Files{}} : Maybe<&2, Eng.Act>}

law route_files_index:
  {Eng.route(Eng.routes(Eng.cfg.set_root(Eng.cfg.new(), Eng.bytes("www"))),
    "/") == Some{Eng.Files{}} : Maybe<&2, Eng.Act>}

law route_files_fixed:
  {Eng.route(Eng.routes(Eng.cfg.set_root(Eng.cfg.new(), Eng.bytes("www"))),
    "/health") == Some{Eng.Health{}} : Maybe<&2, Eng.Act>}

# LAW: no two entries of either table claim one path.
law routes_distinct:
  {Eng.distinct(Eng.routes(Eng.cfg.new())) == True{} : Bool}

law routes_distinct_root:
  {Eng.distinct(Eng.routes(Eng.cfg.set_root(Eng.cfg.new(), Eng.bytes("www")))) ==
    True{} : Bool}

# LAW: an empty table routes nothing, whatever is asked.
law route_empty:
  for +path: Bytes()
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

# LAW: a control frame announcing more than 125 bytes is refused at its
# length byte (a ping with the 126 marker), and a length in more bytes
# than it needed is refused at its last byte: 125 in the two-byte form,
# 65535 in the eight-byte one. The least lengths each form may carry
# are read.
law ws_control_long_is_bad:
  {Ws.dead(Ws.feed([137, 254], Ws.new())) ==
    (Ws.W{Ws.Bad{}, Nil{}}, True{}) : Ws.W & Bool}

law ws_short_126_is_bad:
  {Ws.dead(Ws.feed([130, 254, 0, 125], Ws.new())) ==
    (Ws.W{Ws.Bad{}, Nil{}}, True{}) : Ws.W & Bool}

law ws_short_127_is_bad:
  {Ws.dead(Ws.feed([130, 255, 0, 0, 0, 0, 0, 0, 255, 255], Ws.new())) ==
    (Ws.W{Ws.Bad{}, Nil{}}, True{}) : Ws.W & Bool}

law ws_len_126_least:
  {Ws.feed([130, 254, 0, 126], Ws.new()) == Ws.W{Ws.Msk{2, 126, 4, 0}, Nil{}} : Ws.W}

law ws_len_127_least:
  {Ws.feed([130, 255, 0, 0, 0, 0, 0, 1, 0, 0], Ws.new()) ==
    Ws.W{Ws.Msk{2, 65536, 4, 0}, Nil{}} : Ws.W}

# LAW: what the server writes, one block: a short frame, the two-byte
# length past 125, a close code.
law ws_frame_short:
  {Ws.frame(1, "hi") == Bytes.from_list([129, 2, 104, 105]) : Bytes()}

law ws_len_two_bytes:
  {Ws.len.bytes(300) == [126, 1, 44] : List<&2, U32>}

law ws_close_code:
  {Ws.close.frame(1002) == Bytes.from_list([136, 2, 3, 234]) : Bytes()}

# The close codes a peer may send, stated here on their own: 1000-1003,
# 1007-1014, 3000-4999.
def ws_code_ok(+c: U32) -> Bool:
  (U32.is_le(1000, c) && U32.is_le(c, 1003)) || (U32.is_le(1007, c) && U32.is_le(c, 1014))
    || (U32.is_le(3000, c) && U32.is_le(c, 4999))

def ws_code_by(ref: Bool, +c: U32) -> Bool:
  match ref:
    case True{}:
      ws_code_ok(c)
    case False{}:
      Ws.close.code.ok(c)

def ws_codes(+ref: Bool, cs: List<&2, U32>) -> List<&2, Bool>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{+c, t}:
      Con{ws_code_by(ref, c), ws_codes(ref, t)}

# every edge of the rule, and what it says of each
def ws_code_edges() -> List<&2, U32>:
  [0, 999, 1000, 1003, 1004, 1005, 1006, 1007, 1011, 1014, 1015, 1016, 2999, 3000,
   4999, 5000, 65535]

def ws_code_want() -> List<&2, Bool>:
  [False{}, False{}, True{}, True{}, False{}, False{}, False{}, True{}, True{}, True{},
   False{}, False{}, False{}, True{}, True{}, False{}, False{}]

# LAW: the engine's close codes and the rule above say the same of every
# edge of it.
law ws_close_codes:
  {ws_codes(False{}, ws_code_edges()) == ws_code_want() : List<&2, Bool>}

law ws_close_codes_rule:
  {ws_codes(True{}, ws_code_edges()) == ws_code_want() : List<&2, Bool>}

# LAW: a close is answered with its code when a peer may send it, with
# 1002 when not (1005, which is never sent) or when the payload is one
# byte, and with 1007 when its reason is not UTF-8; a close ends the
# connection either way.
law ws_close_echo:
  {Ws.reply([Ws.Frm{8, Bytes.from_list([3, 232, 111, 107])}], False{}) ==
    Ws.Rep{Ws.frame(8, Bytes.from_list([3, 232])), True{}} : Ws.Rep}

law ws_close_reserved:
  {Ws.reply([Ws.Frm{8, Bytes.from_list([3, 237])}], False{}) ==
    Ws.Rep{Ws.close.frame(1002), True{}} : Ws.Rep}

law ws_close_one_byte:
  {Ws.reply([Ws.Frm{8, Bytes.from_list([3])}], False{}) ==
    Ws.Rep{Ws.close.frame(1002), True{}} : Ws.Rep}

law ws_close_bad_reason:
  {Ws.reply([Ws.Frm{8, Bytes.from_list([3, 232, 255])}], False{}) ==
    Ws.Rep{Ws.close.frame(1007), True{}} : Ws.Rep}

# LAW: a text frame that is not UTF-8 is answered with 1007 and ends the
# connection, after the frames before it and with nothing after; binary
# is not read as text.
law ws_text_bad:
  {Ws.reply([Ws.Frm{1, "a"}, Ws.Frm{1, Bytes.from_list([192, 175])}, Ws.Frm{1, "b"}],
    False{}) ==
    Ws.Rep{Bytes.append(Ws.frame(1, "a"), Ws.close.frame(1007)), True{}} : Ws.Rep}

law ws_binary_any:
  {Ws.reply([Ws.Frm{2, Bytes.from_list([192, 175])}], False{}) ==
    Ws.Rep{Ws.frame(2, Bytes.from_list([192, 175])), False{}} : Ws.Rep}

# A reference for UTF-8, written the other way round from ws.bend's:
# decode each character, then ask whether it is a scalar value (at most
# 10FFFF, no surrogate) its length was needed for. need bytes to go, cp
# the value so far, min the least value that many bytes may carry.
def u8_lead_ok(+b: U32) -> Bool:
  U32.is_lt(b, 128) || (U32.is_le(192, b) && U32.is_le(b, 247))

def u8_len(one: Bool, two: Bool, three: Bool) -> Nat:
  match one two three:
    case True{} _ _:
      0n
    case False{} True{} _:
      1n
    case False{} False{} True{}:
      2n
    case False{} False{} False{}:
      3n

def u8_lead_n(+b: U32) -> Nat:
  u8_len(U32.is_lt(b, 128), U32.is_lt(b, 224), U32.is_lt(b, 240))

def u8_bits(+b: U32, n: Nat) -> U32:
  match n:
    case 0n:
      b
    case 1n:
      U32.and(b, 31)
    case 2n:
      U32.and(b, 15)
    case 1n+1n+1n+p:
      U32.and(b, 7)

def u8_lead_bits(+b: U32) -> U32:
  u8_bits(b, u8_lead_n(b))

def u8_min(n: Nat) -> U32:
  match n:
    case 0n:
      0
    case 1n:
      128
    case 2n:
      2048
    case 1n+1n+1n+p:
      65536

def u8_lead_min(+b: U32) -> U32:
  u8_min(u8_lead_n(b))

def u8_scalar(+cp: U32, +min: U32) -> Bool:
  U32.is_le(min, cp) && U32.is_le(cp, 1114111)
    && Bool.not(U32.is_le(55296, cp) && U32.is_le(cp, 57343))

def u8_done(n: Nat, +cp: U32, +min: U32) -> Bool:
  match n:
    case 0n:
      u8_scalar(cp, min)
    case 1n+p:
      True{}

def u8_ref(xs: List<&2, U32>, +need: Nat, +cp: U32, +min: U32) -> Bool:
  match xs need:
    case Nil{} 0n:
      True{}
    case Nil{} 1n+p:
      False{}
    case Con{+b, t} 0n:
      u8_lead_ok(b) && u8_ref(t, u8_lead_n(b), u8_lead_bits(b), u8_lead_min(b))
    case Con{+b, t} 1n+p:
      +cp2 = ((cp * 64 : U32) + U32.and(b, 63) : U32)
      U32.is_eq(U32.and(b, 192), 128) && u8_done(p, cp2, min) && u8_ref(t, p, cp2, min)

def u8_by(ref: Bool, v: List<&2, U32>) -> Bool:
  match ref:
    case True{}:
      u8_ref(v, 0n, 0, 0)
    case False{}:
      Ws.utf8(Bytes.from_list(v))

def u8_all(+ref: Bool, vs: List<&2, List<&2, U32>>) -> List<&2, Bool>:
  match vs:
    case Nil{}:
      Nil{}
    case Con{v, t}:
      Con{u8_by(ref, v), u8_all(ref, t)}

# the empty text, ASCII, Greek, an emoji, U+FFFF, U+10FFFF and a euro
# sign between letters are UTF-8; overlong forms in two, three and four
# bytes, a surrogate, a code point past 10FFFF, a character cut short, a
# lone continuation byte, FF, and a stray continuation after a character
# are not
def u8_vecs() -> List<&2, List<&2, U32>>:
  [[], [104, 105], [206, 186, 225, 189, 185, 207, 131, 206, 188, 206, 181],
   [240, 159, 152, 128], [239, 191, 191], [244, 143, 191, 191], [104, 226, 130, 172, 105],
   [192, 175], [224, 128, 175], [240, 128, 128, 175], [237, 160, 128],
   [244, 144, 128, 128], [226, 130], [128], [255], [206, 186, 128]]

def u8_want() -> List<&2, Bool>:
  [True{}, True{}, True{}, True{}, True{}, True{}, True{},
   False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]

# LAW: the validator and the reference say the same of every vector, and
# it is what the vectors are.
law ws_utf8_vectors:
  {u8_all(False{}, u8_vecs()) == u8_want() : List<&2, Bool>}

law ws_utf8_reference:
  {u8_all(True{}, u8_vecs()) == u8_want() : List<&2, Bool>}

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
  for +bs: Bytes()
  {Eng.long(Bytes.len(bs), bs) == False{} : Bool}

law long_past:
  for +bs: Bytes()
  for +c: U32
  {Eng.long(Bytes.len(bs), SCon{Chr{c}, bs}) == True{} : Bool}

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
  {Eng.parse("GET /ws HTTP/1.1\r\nHost: x\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Key: k\r\nSec-WebSocket-Version: 13\r\n\r\n") ==
    ([Eng.Req{Eng.MGet{}, "/ws", "", False{}, True{}, "k"}], False{}) :
    List<&2, Eng.Req> & Bool}

law parse_version_other:
  {Eng.parse("GET /ws HTTP/1.1\r\nHost: x\r\nSec-WebSocket-Version: 8\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Key: k\r\n\r\n") ==
    ([Eng.Req{Eng.MGet{}, "/ws", "", False{}, False{}, "k"}], False{}) :
    List<&2, Eng.Req> & Bool}
