# The laws of the WebSocket client and server (net/ws.bend, net/ws_server.bend
# and their parts). The human states them; ws_proof.bend proves them, and
# `bend net/ws_proof.bend` is the gate.
import Base
import ../demos/io_http_engine/ws.bend as Ws
import ./ws_frame.bend as F
import ./ws_hs.bend as H
import ../demos/io_http_engine/sha1.bend as Sha1
import ../demos/io_http_engine/b64.bend as B64

# The reader, at either end
# =========================

# LAW: at a server's end the role-generalised reader IS the engine's:
# one byte, and so any bytes from any state, on either path. Every law
# of demos/io_http_engine/LAWS.bend about Ws.feed is a law of F.feed at
# Srv.
law role_srv_step:
  for +w: Ws.W
  for +b: U32
  {F.step(F.Srv{}, w, b) == Ws.step(w, b) : Ws.W}

law role_srv:
  for +bs: List<&2, U32>
  for +w: Ws.W
  {F.feed(F.Srv{}, bs, w) == Ws.feed(bs, w) : Ws.W}

law role_srv_buf:
  for +b: Bytes()
  for +w: Ws.W
  {F.feed_buf(F.Srv{}, b, w) == Ws.feed_buf(b, w) : Ws.W}

# LAW: chunking does not change the read, at either end: a frame split
# across reads lands where the whole would have, on the list and on the
# buffer, and the buffer walk is the list walk on its bytes.
law feed_split:
  for +r: F.Role
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +w: Ws.W
  {F.feed(r, List.append(&2, U32, a, b), w) == F.feed(r, b, F.feed(r, a, w)) : Ws.W}

law feed_buf:
  for +r: F.Role
  for +b: Bytes()
  for +w: Ws.W
  {F.feed_buf(r, b, w) == F.feed(r, Bytes.to_list(b), w) : Ws.W}

law feed_buf_split:
  for +r: F.Role
  for +a: Bytes()
  for +b: Bytes()
  for +w: Ws.W
  {F.feed_buf(r, Bytes.append(a, b), w) == F.feed_buf(r, b, F.feed_buf(r, a, w)) : Ws.W}

# LAW: a broken framing stays broken, whatever follows.
law bad_feeds_buf:
  for +r: F.Role
  for +s: Bytes()
  for +out: List<&2, Ws.Frm>
  {F.feed_buf(r, s, Ws.W{Ws.Bad{}, out}) == Ws.W{Ws.Bad{}, out} : Ws.W}

# The client's refusals
# =====================

# LAW: a frame from the server with the mask bit set breaks the framing
# at that byte, whatever its opcode and length (RFC 6455 5.1: the
# client fails the connection, with 1002).
law masked_refused:
  for +cap: U32
  for +op: U32
  for +out: List<&2, Ws.Frm>
  for +b: U32
  for h: {U32.and(b, 128) == 128 : U32}
  {F.step(F.Cli{cap}, Ws.W{Ws.Len{op}, out}, b) == Ws.W{Ws.Bad{}, out} : Ws.W}

# LAW: a control frame announcing more than 125 bytes (the two markers
# included) breaks the framing at its length byte, masked or not.
law control_long_refused:
  for +cap: U32
  for +op: U32
  for +out: List<&2, Ws.Frm>
  for +b: U32
  for h: {F.c.ctl(op) && U32.is_lt(125, U32.and(b, 127)) == True{} : Bool}
  {F.step(F.Cli{cap}, Ws.W{Ws.Len{op}, out}, b) == Ws.W{Ws.Bad{}, out} : Ws.W}

# LAW: a reserved bit (no extension was agreed) breaks it at the first
# byte.
law reserved_refused:
  for +cap: U32
  for +out: List<&2, Ws.Frm>
  for +b: U32
  for h: {U32.is_zero(U32.and(b, 112)) == False{} : Bool}
  {F.step(F.Cli{cap}, Ws.W{Ws.Op{}, out}, b) == Ws.W{Ws.Bad{}, out} : Ws.W}

# LAW: a text message that is not UTF-8 fails the connection with 1007,
# whatever its bytes, whole or as the last of its fragments.
law text_bad_1007:
  for +cap: U32
  for +body: Bytes()
  for h: {Ws.utf8(body) == False{} : Bool}
  {F.asm(cap, F.Idle{}, Ws.Frm{1, body}) == F.Ax{F.Idle{}, F.Refuse{1007}} : F.Ax}

# LAW: a continuation with no message to continue, and a new message
# before the last fragment of the one in progress, fail it with 1002.
law orphan_continuation:
  for +cap: U32
  for +fin: Bool
  for +body: Bytes()
  {F.asm(cap, F.Idle{}, Ws.Frm{Bool.pick(U32, fin, 0, 16), body}) == F.Ax{F.Idle{}, F.Refuse{1002}} : F.Ax}

law interleaved_message:
  for +cap: U32
  for +fop: U32
  for +acc: Bytes()
  for +n: U32
  for +ut: Ws.Ut
  for +bin: Bool
  for +body: Bytes()
  {F.asm(cap, F.Frag{fop, acc, n, ut}, Ws.Frm{Bool.pick(U32, bin, 2, 1), body}) ==
    F.Ax{F.Idle{}, F.Refuse{1002}} : F.Ax}

# LAW: a frame past the cap fails the connection with 1009; a ping is
# answered with a pong of its payload, and neither disturbs a message
# in progress.
law too_big_1009:
  for +cap: U32
  for +a: F.Asm
  {F.asm(cap, a, Ws.Frm{F.big.op(), ""}) == F.Ax{a, F.Refuse{1009}} : F.Ax}

law ping_pong:
  for +cap: U32
  for +a: F.Asm
  for +body: Bytes()
  {F.asm(cap, a, Ws.Frm{9, body}) == F.Ax{a, F.Pong{body}} : F.Ax}

# Masking
# =======

# LAW: masking is its own inverse: the payload unmasked with the key it
# was masked with is the payload, for every payload and key.
law mask_inv:
  for +p: Bytes()
  for +m: U32
  {F.mask(F.mask(p, m), m) == p : Bytes()}

# LAW: every frame the client writes is masked: its second byte has the
# mask bit, whatever its opcode, payload and key; and it is its head
# then its payload under the key, which mask_inv unmasks.
law frame_masked:
  for +op: U32
  for +fin: Bool
  for +p: Bytes()
  for +m: U32
  {U32.and(Bytes.get(F.c.frame(op, fin, p, m), 1n), 128) == 128 : U32}

law frame_payload:
  for +op: U32
  for +fin: Bool
  for +p: Bytes()
  for +m: U32
  {F.c.frame(op, fin, p, m) ==
    Bytes.append(F.c.head(op, fin, U32.from_nat(Bytes.len(p)), m), F.mask(p, m)) : Bytes()}

# LAW: RFC 6455 5.7's masked "Hello", byte for byte (key 37 fa 21 3d).
law frame_rfc:
  {Bytes.to_list(F.c.frame(1, True{}, "Hello", 939139389)) ==
    [129, 133, 55, 250, 33, 61, 127, 159, 77, 81, 88] : List<&2, U32>}

# LAW: the engine's own server reader reads the client's frames back as
# the opcode and the payload: text, binary and ping, empty, short, and
# past 125 (the two-byte length).
law engine_reads_client:
  {Ws.take(Ws.feed_buf(Bytes.concat([F.c.frame(1, True{}, "Hello", 939139389),
    F.c.frame(2, True{}, "", 4294967295), F.c.frame(9, True{}, "ping", 16909060),
    F.c.frame(1, True{}, String.repeat("yz", 63n), 305419896)]), Ws.new())) ==
    (Ws.W{Ws.Op{}, Nil{}}, [Ws.Frm{1, "Hello"}, Ws.Frm{2, ""}, Ws.Frm{9, "ping"},
      Ws.Frm{1, String.repeat("yz", 63n)}])
    : Ws.W & List<&2, Ws.Frm>}

# The session, on the RFC's frames
# ================================

# LAW: RFC 6455 5.7's unmasked frames as a client reads them: a text
# "Hello", the same in two fragments, an unmasked ping, 256 bytes of
# binary in the two-byte length; and a masked one refused with 1002.
law session_rfc:
  {F.session(65536, Bytes.concat([Bytes.from_list([129, 5]), "Hello",
    Bytes.from_list([1, 3]), "Hel", Bytes.from_list([128, 2]), "lo",
    Bytes.from_list([137, 5]), "Hello",
    Bytes.from_list([130, 126, 1, 0]), String.repeat("b", 256n)])) ==
    [F.Deliver{F.Text{"Hello"}}, F.Skip{}, F.Deliver{F.Text{"Hello"}}, F.Pong{"Hello"},
      F.Deliver{F.Binary{String.repeat("b", 256n)}}] : List<&2, F.Act>}

law session_masked:
  {F.session(65536, Bytes.from_list([129, 133, 55, 250, 33, 61, 127, 159, 77, 81, 88])) ==
    [F.Refuse{1002}] : List<&2, F.Act>}

# LAW: a ping between two fragments is answered and the message still
# comes whole; a pong is nothing; a fragmented text split inside a
# character is read whole.
law session_interleaved:
  {F.session(65536, Bytes.from_list([1, 2, 104, 195, 137, 0, 138, 0, 128, 3, 169, 108, 111])) ==
    [F.Skip{}, F.Pong{""}, F.Skip{}, F.Deliver{F.Text{"h\u{e9}lo"}}] : List<&2, F.Act>}

# LAW: text that is not UTF-8 is 1007, whole or cut (an overlong form,
# a surrogate, a character cut short at the end); past the cap is 1009,
# on the length and on the fragments joined; a control frame that is
# long or cut is 1002; a reserved bit is 1002.
law session_refusals:
  {[F.session(65536, Bytes.from_list([129, 2, 192, 175])),
    F.session(65536, Bytes.from_list([129, 3, 237, 160, 128])),
    F.session(65536, Bytes.from_list([1, 1, 206, 128, 0])),
    F.session(4, Bytes.from_list([130, 5, 1, 2, 3, 4, 5])),
    F.session(4, Bytes.from_list([2, 3, 1, 2, 3, 128, 2, 4, 5])),
    F.session(65536, Bytes.from_list([137, 126, 0, 126])),
    F.session(65536, Bytes.from_list([9, 0])),
    F.session(65536, Bytes.from_list([193, 0])),
    F.session(65536, Bytes.from_list([131, 0]))] ==
    [[F.Refuse{1007}], [F.Refuse{1007}], [F.Skip{}, F.Refuse{1007}], [F.Refuse{1009}, F.Refuse{1002}],
     [F.Skip{}, F.Refuse{1009}], [F.Refuse{1002}], [F.Refuse{1002}], [F.Refuse{1002}], [F.Refuse{1002}]]
    : List<&2, List<&2, F.Act>>}

# LAW: a close is read with its code and reason; none is 1005; one
# byte, a code no peer may send (1005, 1006, 1015, 999, 2000, 5000) is
# 1002; a reason that is not UTF-8 is 1007.
law session_close:
  {[F.session(65536, Bytes.from_list([136, 5, 3, 232, 98, 121, 101])),
    F.session(65536, Bytes.from_list([136, 0])),
    F.session(65536, Bytes.from_list([136, 1, 3])),
    F.session(65536, Bytes.from_list([136, 2, 3, 237])),
    F.session(65536, Bytes.from_list([136, 2, 3, 238])),
    F.session(65536, Bytes.from_list([136, 2, 3, 247])),
    F.session(65536, Bytes.from_list([136, 2, 3, 231])),
    F.session(65536, Bytes.from_list([136, 2, 7, 208])),
    F.session(65536, Bytes.from_list([136, 2, 19, 136])),
    F.session(65536, Bytes.from_list([136, 3, 15, 160, 255])),
    F.session(65536, Bytes.from_list([136, 2, 15, 160]))] ==
    [[F.Bye{1000, "bye"}], [F.Bye{1005, ""}], [F.Refuse{1002}], [F.Refuse{1002}], [F.Refuse{1002}],
     [F.Refuse{1002}], [F.Refuse{1002}], [F.Refuse{1002}], [F.Refuse{1002}], [F.Refuse{1007}],
     [F.Bye{4000, ""}]] : List<&2, List<&2, F.Act>>}

# UTF-8
# =====

# LAW: text goes out as its UTF-8 and comes back as itself: one, two,
# three and four byte characters.
law utf8_vectors:
  {(Bytes.to_list(F.utf8.enc("a\u{e9}\u{20ac}\u{1d11e}")),
    F.utf8.dec(F.utf8.enc("a\u{e9}\u{20ac}\u{1d11e}"))) ==
    ([97, 195, 169, 226, 130, 172, 240, 157, 132, 158], "a\u{e9}\u{20ac}\u{1d11e}")
    : List<&2, U32> & String}

# The handshake
# =============

# LAW: the client goes on exactly when Sec-WebSocket-Accept is the one
# its key asks for: for every key and every value that came, once, in an
# answer that is otherwise as the RFC asks.
law hs_accept:
  for +key: Bytes()
  for +a: Bytes()
  for +offered: List<&2, String>
  {H.ok(H.judge(H.expect(key), offered, 101, H.Hs{1, True{}, True{}, [a], False{}, [], False{}})) ==
    String.eq(a, H.expect(key)) : Bool}

# LAW: RFC 6455 1.3's example, as a client reads the answer: accepted;
# and refused with a byte of the Accept changed, the Upgrade missing,
# another status, no Connection: Upgrade, two Accepts, an extension, a
# subprotocol not offered, a folded line; names and the tokens in any
# case, Connection as a list; a subprotocol offered is chosen.
law hs_rfc:
  {[H.answer("dGhlIHNhbXBsZSBub25jZQ==", [], "HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: s3pPLMBiTxaQ9kYGzzhZRbK+xOo="),
    H.answer("dGhlIHNhbXBsZSBub25jZQ==", [], "HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: s3pPLMBiTxaQ9kYGzzhZRbK+xOo"),
    H.answer("dGhlIHNhbXBsZSBub25jZQ==", [], "HTTP/1.1 101 Switching Protocols\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: s3pPLMBiTxaQ9kYGzzhZRbK+xOo="),
    H.answer("dGhlIHNhbXBsZSBub25jZQ==", [], "HTTP/1.1 200 OK\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: s3pPLMBiTxaQ9kYGzzhZRbK+xOo="),
    H.answer("dGhlIHNhbXBsZSBub25jZQ==", [], "HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: keep-alive\r\nSec-WebSocket-Accept: s3pPLMBiTxaQ9kYGzzhZRbK+xOo="),
    H.answer("dGhlIHNhbXBsZSBub25jZQ==", [], "HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: s3pPLMBiTxaQ9kYGzzhZRbK+xOo=\r\nSec-WebSocket-Accept: s3pPLMBiTxaQ9kYGzzhZRbK+xOo="),
    H.answer("dGhlIHNhbXBsZSBub25jZQ==", [], "HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: s3pPLMBiTxaQ9kYGzzhZRbK+xOo=\r\nSec-WebSocket-Extensions: permessage-deflate"),
    H.answer("dGhlIHNhbXBsZSBub25jZQ==", ["chat"], "HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: s3pPLMBiTxaQ9kYGzzhZRbK+xOo=\r\nSec-WebSocket-Protocol: superchat"),
    H.answer("dGhlIHNhbXBsZSBub25jZQ==", [], "HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n Sec-WebSocket-Accept: s3pPLMBiTxaQ9kYGzzhZRbK+xOo="),
    H.answer("dGhlIHNhbXBsZSBub25jZQ==", ["superchat", "chat"], "HTTP/1.1 101 Switching Protocols\r\nupgrade: WebSocket\r\nCONNECTION: keep-alive, UPGRADE\r\nsec-websocket-accept:s3pPLMBiTxaQ9kYGzzhZRbK+xOo=  \r\nSec-WebSocket-Protocol: chat")] ==
    [Done{""}, Fail{H.HAccept{}}, Fail{H.HUpgrade{}}, Fail{H.HStatus{200}}, Fail{H.HConnection{}},
     Fail{H.HAccept{}}, Fail{H.HExtension{}}, Fail{H.HProtocol{}}, Fail{H.HMalformed{}}, Done{"chat"}]
    : List<&2, Result<&2, &2, H.Hw, Bytes()>>}

# LAW: the opening request, byte for byte, for a URL with a port, a path
# and a query, and a subprotocol offered.
law hs_request:
  {H.request(H.Url{False{}, "example.com", 8080, "/chat?room=1"}, "dGhlIHNhbXBsZSBub25jZQ==", ["chat"]) ==
    "GET /chat?room=1 HTTP/1.1\r\nHost: example.com:8080\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==\r\nSec-WebSocket-Version: 13\r\nSec-WebSocket-Protocol: chat\r\n\r\n"
    : Bytes()}

# LAW: the URLs a client takes, and those it refuses.
law url_vectors:
  {[H.url.parse("ws://example.com"), H.url.parse("wss://example.com/a/b?c=d"),
    H.url.parse("ws://127.0.0.1:9001/runCase?case=1&agent=bend"), H.url.parse("wss://h?x"),
    H.url.parse("http://example.com/"), H.url.parse("ws://u@example.com/"), H.url.parse("ws://example.com/#f"),
    H.url.parse("ws://:80/"), H.url.parse("ws://h:0/"), H.url.parse("ws://h:65536/"), H.url.parse("ws://h:8x/")] ==
    [Some{H.Url{False{}, "example.com", 80, "/"}}, Some{H.Url{True{}, "example.com", 443, "/a/b?c=d"}},
     Some{H.Url{False{}, "127.0.0.1", 9001, "/runCase?case=1&agent=bend"}}, Some{H.Url{True{}, "h", 443, "/?x"}},
     None{}, None{}, None{}, None{}, None{}, None{}, None{}]
    : List<&2, Maybe<&2, H.Url>>}

# LAW: IP-literal URLs (RFC 3986 3.2.2): the IPv6 address kept in its
# brackets and written as RFC 5952 does (net/addr.bend); refused: a
# bracket not closed, a byte after it that is not ':', a zone ID (RFC
# 6874), a port of 0.
law url_v6_vectors:
  {[H.url.parse("ws://[::1]/"), H.url.parse("wss://[0:0:0:0:0:0:0:1]:9001/a?b"), H.url.parse("ws://[2001:DB8::1]:80"),
    H.url.parse("ws://[::ffff:127.0.0.1]:81/"), H.url.parse("ws://[::1"), H.url.parse("ws://[::1]x/"),
    H.url.parse("ws://[fe80::1%25eth0]/"), H.url.parse("ws://[::1]:0/"), H.url.parse("ws://[1.2.3.4]/")] ==
    [Some{H.Url{False{}, "[::1]", 80, "/"}}, Some{H.Url{True{}, "[::1]", 9001, "/a?b"}},
     Some{H.Url{False{}, "[2001:db8::1]", 80, "/"}}, Some{H.Url{False{}, "[::ffff:127.0.0.1]", 81, "/"}},
     None{}, None{}, None{}, None{}, None{}]
    : List<&2, Maybe<&2, H.Url>>}

def v6.req(m: Maybe<&2, H.Url>) -> Bytes():
  match m:
    case Some{u}:
      H.request(u, "dGhlIHNhbXBsZSBub25jZQ==", Nil{})
    case None{}:
      ""

# LAW: the opening request to an IP-literal: its Host field is the
# address in its brackets, canonical, the port when it is not the
# scheme's (RFC 6455 4.1, RFC 9110 7.2).
law hs_request_v6:
  {[v6.req(H.url.parse("ws://[0:0::1]:9001/chat")), v6.req(H.url.parse("wss://[2001:DB8::1]/"))] ==
    ["GET /chat HTTP/1.1\r\nHost: [::1]:9001\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==\r\nSec-WebSocket-Version: 13\r\n\r\n",
     "GET / HTTP/1.1\r\nHost: [2001:db8::1]\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==\r\nSec-WebSocket-Version: 13\r\n\r\n"]
    : List<&2, Bytes()>}

# The server's end
# ================
#
# net/ws_server.bend's connections: the Serv reader, the frames a server
# writes, the session a handler sees, the closing, and the opening
# handshake.

# LAW: an unmasked frame from the client breaks the framing at its
# length byte, whatever its opcode and length (RFC 6455 5.1: the server
# fails the connection, with 1002).
law srv_unmasked_refused:
  for +cap: U32
  for +op: U32
  for +out: List<&2, Ws.Frm>
  for +b: U32
  for h: {U32.and(b, 128) == 0 : U32}
  {F.step(F.Serv{cap}, Ws.W{Ws.Len{op}, out}, b) == Ws.W{Ws.Bad{}, out} : Ws.W}

# LAW: no frame the server writes is masked: its second byte's mask bit
# is clear, whatever its opcode, payload and FIN.
law srv_frame_unmasked:
  for +op: U32
  for +fin: Bool
  for +p: Bytes()
  {U32.and(Bytes.get(F.s.frame(op, fin, p), 1n), 128) == 0 : U32}

# LAW: RFC 6455 5.7's unmasked "Hello" and the head of its 256-byte
# binary, byte for byte; and a client reads the server's frames back: a
# text, the same in two fragments, a ping.
law srv_frame_rfc:
  {(Bytes.to_list(F.s.frame(1, True{}, "Hello")),
    Bytes.to_list(String.take(F.s.frame(2, True{}, String.repeat("b", 256n)), 4n)),
    F.session(65536, Bytes.concat([F.s.frame(1, True{}, "Hello"), F.s.frame(1, False{}, "Hel"),
      F.s.frame(0, True{}, "lo"), F.s.frame(9, True{}, "hi")]))) ==
    ([129, 5, 72, 101, 108, 108, 111], [130, 126, 1, 0],
     [F.Deliver{F.Text{"Hello"}}, F.Skip{}, F.Deliver{F.Text{"Hello"}}, F.Pong{"hi"}])
    : List<&2, U32> & List<&2, U32> & List<&2, F.Act>}

# LAW: what the handler receives does not depend on how the input was
# cut into reads. For every cap and every list of reads, the acts the
# connection takes reading them one by one (each fed to the reader from
# where the last left it, its frames assembled with the assembler as
# the last left it, the framing checked at the end) are the spec's: the
# frames of the whole input, reassembled in one go, and a 1002 if the
# framing broke.
law srv_reads:
  for +cap: U32
  for +rs: List<&2, Bytes()>
  {F.s.reads(cap, rs) == F.s.session(cap, Bytes.concat(rs)) : List<&2, F.Act>}

# LAW: the session a server reads, on RFC 6455 5.7's masked frames: a
# text "Hello" (key 37 fa 21 3d), the same in two masked fragments with
# a masked ping between them, an empty masked binary; an unmasked
# "Hello" is 1002, and so is a reserved bit; a message past the cap is
# 1009, on the length and on the fragments joined; text not UTF-8 is
# 1007; a close is read with its code.
law srv_session_rfc:
  {[F.s.session(65536, Bytes.concat([F.c.frame(1, True{}, "Hello", 939139389), F.c.frame(1, False{}, "Hel", 1),
      F.c.frame(9, True{}, "", 2), F.c.frame(0, True{}, "lo", 3), F.c.frame(2, True{}, "", 4)])),
    F.s.session(65536, Bytes.from_list([129, 5, 72, 101, 108, 108, 111])),
    F.s.session(65536, Bytes.concat([Bytes.from_list([193]), String.drop(F.c.frame(1, True{}, "", 5), 1n)])),
    F.s.session(4, F.c.frame(2, True{}, "12345", 6)),
    F.s.session(4, Bytes.concat([F.c.frame(2, False{}, "123", 7), F.c.frame(0, True{}, "45", 8)])),
    F.s.session(65536, F.c.frame(1, True{}, Bytes.from_list([192, 175]), 9)),
    F.s.session(65536, F.c.frame(8, True{}, Bytes.from_list([3, 232, 98, 121, 101]), 10))] ==
    [[F.Deliver{F.Text{"Hello"}}, F.Skip{}, F.Pong{""}, F.Deliver{F.Text{"Hello"}}, F.Deliver{F.Binary{""}}],
     [F.Refuse{1002}], [F.Refuse{1002}], [F.Refuse{1009}, F.Refuse{1002}], [F.Skip{}, F.Refuse{1009}],
     [F.Refuse{1007}], [F.Bye{1000, "bye"}]]
    : List<&2, List<&2, F.Act>>}

# LAW: the client's close is answered once. Whatever the acts, the
# server writes at most one close frame, and none once its own close
# went out (the handler closed first, or SIGTERM's 1001): the peer's
# close is then the answer, not a thing to answer.
law srv_close_once:
  for +sent: Bool
  for +xs: List<&2, F.Act>
  {Nat.is_le(F.closes(F.s.writes(sent, xs)), 1n) == True{} : Bool}

law srv_close_after:
  for +xs: List<&2, F.Act>
  {F.closes(F.s.writes(True{}, xs)) == 0n : Nat}

# LAW: a client's close is answered with its code, and nothing is
# written after it: a ping behind it gets no pong.
law srv_close_vector:
  {F.s.writes(False{}, [F.Pong{"a"}, F.Bye{1000, "bye"}, F.Pong{"b"}, F.Refuse{1002}]) ==
    [F.WPong{"a"}, F.WClose{1000}] : List<&2, F.Wr>}

# LAW: the opening handshake (RFC 6455 4.2.2). Every request that asked
# well -- a GET that asked to upgrade, Sec-WebSocket-Version: 13 (asked:
# the engine reads no other as asking, its upgrade_needs_13), with a key
# of sixteen bytes in base64 -- is answered with the 101: its status line, Upgrade:
# websocket, Connection: Upgrade, the Accept that is the base64 of the
# SHA-1 of the key joined to the GUID, the subprotocol line for the one
# chosen (srv_hs_proto: one the client offered, or none), the blank
# line.
law srv_hs_valid:
  for +key: Bytes()
  for +offered: List<&2, Bytes()>
  for +proto: Bytes()
  for h: {H.key.ok(key) == True{} : Bool}
  {H.s.answer(True{}, True{}, key, offered, proto) ==
    H.SOk{"HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: "
      ++ Bytes.from_list(B64.enc(Sha1.hash(List.append(&2, U32, Bytes.to_list(key),
        Ws.ascii("258EAFA5-E914-47DA-95CA-C5AB0DC85B11"))))) ++ "\r\n"
      ++ H.s.proto.line(H.s.chosen(proto, offered)) ++ "\r\n"} : H.Sv}

# LAW: the answer never names a subprotocol the client did not offer.
law srv_hs_proto:
  for +proto: Bytes()
  for +offered: List<&2, Bytes()>
  for h: {H.has(offered, proto) == False{} : Bool}
  {H.s.chosen(proto, offered) == "" : Bytes()}

# LAW: a request that did not ask -- no Upgrade, or a version that is
# not 13, or none (RFC 6455 4.4) -- is a 426, whatever its method and
# key: the refusal names version 13 (ws_server's refusal), and the client
# may ask again.
law srv_hs_version:
  for +get: Bool
  for +key: Bytes()
  for +offered: List<&2, Bytes()>
  for +proto: Bytes()
  {H.s.answer(get, False{}, key, offered, proto) == H.SNo{426} : H.Sv}

# LAW: every other request is refused, with 400 or 426: one that asked
# with another method than GET (a HEAD, a POST: net/server.bend hands the
# route every method of a request that asked) or a key not a key, 400.
law srv_hs_refused:
  for +get: Bool
  for +asked: Bool
  for +key: Bytes()
  for +offered: List<&2, Bytes()>
  for +proto: Bytes()
  for h: {get && asked && H.key.ok(key) == False{} : Bool}
  {H.s.refused(H.s.answer(get, asked, key, offered, proto)) == True{} : Bool}

# LAW: RFC 6455 1.3's example, as the server answers it and the client
# (ws_hs.bend's judge) reads that answer back; and the refusals: not
# asked, 426; a POST, a key cut short, a key with no padding, a key with
# a byte out of the alphabet, 400; a subprotocol not offered, left out.
law srv_hs_vectors:
  {[H.s.answer(True{}, True{}, "dGhlIHNhbXBsZSBub25jZQ==", ["superchat", "chat"], "chat"),
    H.s.answer(True{}, False{}, "dGhlIHNhbXBsZSBub25jZQ==", [], ""),
    H.s.answer(False{}, True{}, "dGhlIHNhbXBsZSBub25jZQ==", [], ""),
    H.s.answer(True{}, True{}, "dGhlIHNhbXBsZSBub25jZQ=", [], ""),
    H.s.answer(True{}, True{}, "dGhlIHNhbXBsZSBub25jZQAA", [], ""),
    H.s.answer(True{}, True{}, "dGhlIHNhbXBsZSBub25jZ!==", [], ""),
    H.s.answer(True{}, True{}, "dGhlIHNhbXBsZSBub25jZQ==", ["chat"], "superchat")] ==
    [H.SOk{"HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: s3pPLMBiTxaQ9kYGzzhZRbK+xOo=\r\nSec-WebSocket-Protocol: chat\r\n\r\n"},
     H.SNo{426}, H.SNo{400}, H.SNo{400}, H.SNo{400}, H.SNo{400},
     H.SOk{"HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: s3pPLMBiTxaQ9kYGzzhZRbK+xOo=\r\n\r\n"}]
    : List<&2, H.Sv>}

law srv_hs_client_reads:
  {H.answer("dGhlIHNhbXBsZSBub25jZQ==", ["superchat", "chat"],
    "HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: s3pPLMBiTxaQ9kYGzzhZRbK+xOo=\r\nSec-WebSocket-Protocol: chat")
    == Done{"chat"} : Result<&2, &2, H.Hw, Bytes()>}

# LAW: the subprotocols a request offered, from every field, in order.
law srv_offered:
  {H.s.offered(["chat, superchat", " v2.bend ", ""]) == ["chat", "superchat", "v2.bend"] : List<&2, Bytes()>}
