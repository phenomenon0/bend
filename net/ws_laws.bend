# The laws of the WebSocket client (net/ws.bend and its parts). The
# human states them; ws_proof.bend proves them, and
# `bend net/ws_proof.bend` is the gate.
import Base
import ../demos/io_http_engine/ws.bend as Ws
import ./ws_frame.bend as F
import ./ws_hs.bend as H

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
