# The laws of the HTTP engine. The human states them; PROOF.bend must
# prove them. They pin the three things a byte-at-a-time protocol
# reader has to get right, and the one optimisation that would
# otherwise be a comment nobody checks.
import Base
import ./main.bend as Eng
import ./sha1.bend as Sha1
import ./b64.bend as B64
import ./ws.bend as Ws

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
    Eng.reply("400 Bad Request", "text/plain", "bad request\n") :
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

# LAW: the WebSocket accept key of RFC 6455's own example, the two
# composed: the client's nonce joined to the GUID, hashed, encoded.
law ws_accept:
  {B64.enc(Sha1.hash(Eng.bytes("dGhlIHNhbXBsZSBub25jZQ==258EAFA5-E914-47DA-95CA-C5AB0DC85B11"))) ==
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

# LAW: a masked client frame reads back as its opcode and its bytes:
# "hi" as text under the mask 1 2 3 4, and an empty ping.
law ws_read_text:
  {Ws.take(Ws.feed([129, 130, 1, 2, 3, 4, 105, 107], Ws.new())) ==
    (Ws.W{Ws.Op{}, Nil{}}, [Ws.Frm{1, Eng.bytes("hi")}]) : Ws.W & List<&2, Ws.Frm>}

law ws_read_ping:
  {Ws.take(Ws.feed([137, 128, 9, 9, 9, 9], Ws.new())) ==
    (Ws.W{Ws.Op{}, Nil{}}, [Ws.Frm{9, Nil{}}]) : Ws.W & List<&2, Ws.Frm>}

# LAW: an unmasked client frame, a fragment, and a reserved bit are each
# refused at the byte that shows them.
law ws_unmasked_is_bad:
  {Ws.dead(Ws.feed([129, 2], Ws.new())) ==
    (Ws.W{Ws.Bad{}, Nil{}}, True{}) : Ws.W & Bool}

law ws_fragment_is_bad:
  {Ws.dead(Ws.feed([1], Ws.new())) == (Ws.W{Ws.Bad{}, Nil{}}, True{}) : Ws.W & Bool}

law ws_reserved_is_bad:
  {Ws.dead(Ws.feed([193], Ws.new())) == (Ws.W{Ws.Bad{}, Nil{}}, True{}) : Ws.W & Bool}

# LAW: what the server writes: a short frame, and the two-byte length
# past 125.
law ws_frame_short:
  {Ws.frame(1, Eng.bytes("hi")) == [129, 2, 104, 105] : List<&2, U32>}

law ws_len_two_bytes:
  {Ws.len.bytes(300) == [126, 1, 44] : List<&2, U32>}

law ws_close_code:
  {Ws.close.frame(1002) == [136, 2, 3, 234] : List<&2, U32>}
