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
    Eng.reply("200 OK", "application/json", Eng.bytes("{\"ok\":true}")) :
    List<&2, U32>}

law root_is_built:
  {Eng.resp.root() ==
    Eng.reply("200 OK", "text/plain", Eng.bytes("bend-http\n")) :
    List<&2, U32>}

law missing_is_built:
  {Eng.resp.missing() ==
    Eng.reply("404 Not Found", "text/plain", Eng.bytes("no route\n")) :
    List<&2, U32>}

law method_is_built:
  {Eng.resp.method() ==
    Eng.reply.allow("405 Method Not Allowed", "text/plain", Eng.bytes("no method\n")) :
    List<&2, U32>}

law bad_is_built:
  {Eng.resp.bad() ==
    Eng.reply("400 Bad Request", "text/plain", Eng.bytes("bad request\n")) :
    List<&2, U32>}

# LAW: HEAD is GET's head. The scanner that cuts a reply at its blank
# line and the builder that writes a head from a length agree, byte for
# byte, on the replies the engine keeps ready.
law head_of_health:
  {Eng.head.of(Eng.resp.health()) ==
    Eng.reply.n.head("200 OK", Eng.bytes("application/json"), 11) :
    List<&2, U32>}

law head_of_missing:
  {Eng.head.of(Eng.resp.missing()) ==
    Eng.reply.n.head("404 Not Found", Eng.bytes("text/plain"), 9) :
    List<&2, U32>}

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

# LAW: a request cannot name a file outside the root. These pin the
# normaliser on the paths that matter, including the one that climbs
# from under a real directory; they are pins, not a proof over every
# path -- that proof needs a lemma over classified segments and is the
# next one to write.
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
