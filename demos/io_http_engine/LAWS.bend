# The laws of the HTTP engine. The human states them; PROOF.bend must
# prove them. They pin the three things a byte-at-a-time protocol
# reader has to get right, and the one optimisation that would
# otherwise be a comment nobody checks.
import Base
import ../../wire/reader.bend as Wr
import ../../wire/loop.bend as L
import ../../wire/world.bend as WW
import ./main.bend as Eng
import ./sha1.bend as Sha1
import ./b64.bend as B64
import ./ws.bend as Ws
import ./spec.bend as Spec
import ./world.bend as W

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

# LAW: the one transfer coding is chunked, exactly. A Transfer-Encoding
# whose value is anything else when lowercased -- another coding, a
# list ("chunked, identity"), "xchunked", "chunked " with whitespace
# after it -- is refused where its line ends, in every message.
law te_chunked_only:
  for +v: Bytes()
  for +pd: Eng.Pend
  for +out: List<&2, Eng.Req>
  for e: {Spec.eq(Eng.lows(v), "chunked") == False{} : Bool}
  {Eng.step(Eng.P{Eng.InLe{v}, pd, out}, 13) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}

# LAW: and it is named once: a Transfer-Encoding after one that said
# chunked is refused where its line ends, whatever it says (chunked is
# applied once, and last: RFC 9112 7).
law te_once:
  for +v: Bytes()
  for +m: Eng.Meth
  for +path: Bytes()
  for +l: Eng.Cl
  for +cl: Bool
  for +h: Eng.Hosts
  for +ws: Eng.Up
  for +v10: Bool
  for +ka: Bool
  for +out: List<&2, Eng.Req>
  {Eng.step(Eng.P{Eng.InLe{v}, Eng.Pend{m, path, l, cl, h, ws, Eng.Fx{v10, ka, True{}}}, out}, 13) ==
    Eng.P{Eng.Bad{}, Eng.Pend{m, path, l, cl, h, ws, Eng.Fx{v10, ka, True{}}}, out} : Eng.P}

# LAW: a head that framed its body two ways -- a Transfer-Encoding and a
# Content-Length, in either order -- is refused at its blank line
# (RFC 9112 6.3), whatever else it carried.
law te_cl_refused:
  for +m: Eng.Meth
  for +path: Bytes()
  for +v: U32
  for +cl: Bool
  for +h: Eng.Hosts
  for +ws: Eng.Up
  for +v10: Bool
  for +ka: Bool
  for +out: List<&2, Eng.Req>
  {Eng.step(Eng.P{Eng.CrL{}, Eng.Pend{m, path, Eng.Has{v}, cl, h, ws, Eng.Fx{v10, ka, True{}}}, out}, 10) ==
    Eng.P{Eng.Bad{}, Eng.Pend{m, path, Eng.Has{v}, cl, h, ws, Eng.Fx{v10, ka, True{}}}, out} : Eng.P}

# LAW: and so is an HTTP/1.0 head with a Transfer-Encoding (RFC 9112
# 6.1: faulty framing), whatever else it carried.
law te_10_refused:
  for +m: Eng.Meth
  for +path: Bytes()
  for +l: Eng.Cl
  for +cl: Bool
  for +h: Eng.Hosts
  for +ws: Eng.Up
  for +ka: Bool
  for +out: List<&2, Eng.Req>
  {Eng.step(Eng.P{Eng.CrL{}, Eng.Pend{m, path, l, cl, h, ws, Eng.Fx{True{}, ka, True{}}}, out}, 10) ==
    Eng.P{Eng.Bad{}, Eng.Pend{m, path, l, cl, h, ws, Eng.Fx{True{}, ka, True{}}}, out} : Eng.P}

# LAW: a chunk-size is refused at the digit that takes it past what the
# body's budget has left: for every size so far, every budget, every
# body so far and every message, a HEXDIG (as the reference reads one)
# that makes the size at least the budget is refused where it stands.
# The size so far is below the budget, which is at most body.cap(), so
# sixteen times it plus a digit never wraps.
law chunk_size_capped:
  for +c: U32
  for +d: U32
  for +n: U32
  for +b: Bytes()
  for +left: U32
  for +pd: Eng.Pend
  for +out: List<&2, Eng.Req>
  for e: {Spec.xk.of(Spec.cls(c), c) == Eng.XHex{d} : Eng.XK}
  for f: {U32.is_le(left, (n * 16 + d : U32)) == True{} : Bool}
  {Eng.step(Eng.P{Eng.Chk{Eng.CSize{}, n, b, left}, pd, out}, c) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}

# LAW: and every other byte of a chunk line the budget pays for -- an
# extension's, its whitespace, a ";" -- is refused where the budget
# can no longer hold it and the chunk's data, wherever in the line it
# is: an extension is never longer than the body may be.
law chunk_ext_capped:
  for +c: U32
  for +pos: Eng.ChPos
  for +to: Eng.ChPos
  for +n: U32
  for +b: Bytes()
  for +left: U32
  for +pd: Eng.Pend
  for +out: List<&2, Eng.Req>
  for e: {Eng.chk.next(pos, Spec.xk.of(Spec.cls(c), c)) == Eng.MvTo{to, True{}} : Eng.Mv}
  for f: {U32.is_le(left, n) == True{} : Bool}
  {Eng.step(Eng.P{Eng.Chk{pos, n, b, left}, pd, out}, c) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}

# LAW: a chunk line, its data's end and a trailer line each end in CR LF:
# a bare LF anywhere in a chunked body's framing but right after its CR
# is refused, whatever the size, the body so far or the budget.
def lf.due(pos: Eng.ChPos) -> Bool:
  match pos:
    case Eng.CLf{}:
      True{}
    case Eng.CDataLf{}:
      True{}
    case Eng.CTLf{}:
      True{}
    case Eng.CEnd{}:
      True{}
    case _:
      False{}

law chunk_bare_lf:
  for +pos: Eng.ChPos
  for +n: U32
  for +b: Bytes()
  for +left: U32
  for +pd: Eng.Pend
  for +out: List<&2, Eng.Req>
  for e: {lf.due(pos) == False{} : Bool}
  {Eng.step(Eng.P{Eng.Chk{pos, n, b, left}, pd, out}, 10) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}

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
  for +fx: Eng.Fx
  for +out: List<&2, Eng.Req>
  for e: {U32.is_eq(w, v) == False{} : Bool}
  {Eng.step(Eng.P{Eng.InL{w}, Eng.Pend{m, path, Eng.Has{v}, cl, h, ws, fx}, out}, 13) ==
    Eng.P{Eng.Bad{}, Eng.Pend{m, path, Eng.Has{v}, cl, h, ws, fx}, out} : Eng.P}

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
  for +k: Bool
  for +pd: Eng.Pend
  for +out: List<&2, Eng.Req>
  for e: {Spec.in.value(Eng.cls(c)) == False{} : Bool}
  {Eng.step(Eng.P{Eng.InLc{t, a, b, k}, pd, out}, c) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}

# LAW: an HTTP/1.1 head without exactly one Host, and an HTTP/1.0 head
# with more than one, is refused at its blank line (RFC 9112 3.2),
# whatever else it carried.
law host_once:
  for +m: Eng.Meth
  for +path: Bytes()
  for +l: Eng.Cl
  for +cl: Bool
  for +h: Eng.Hosts
  for +ws: Eng.Up
  for +v10: Bool
  for +ka: Bool
  for +te: Bool
  for +out: List<&2, Eng.Req>
  for e: {Spec.hosts.fit(v10, h) == False{} : Bool}
  {Eng.step(Eng.P{Eng.CrL{}, Eng.Pend{m, path, l, cl, h, ws, Eng.Fx{v10, ka, te}}, out}, 10) ==
    Eng.P{Eng.Bad{}, Eng.Pend{m, path, l, cl, h, ws, Eng.Fx{v10, ka, te}}, out} : Eng.P}

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

# HTTP/1.0: no Host needed; it closes after its reply unless it asked to
# keep alive, and close still wins over keep-alive; an Upgrade in it is
# not one (RFC 9110 7.8)
law parse_10:
  {Eng.parse("GET /health HTTP/1.0\r\n\r\n") ==
    ([Eng.Req{Eng.MGet{}, "/health", "", True{}, False{}, ""}], False{}) :
    List<&2, Eng.Req> & Bool}

law parse_10_keepalive:
  {Eng.parse("GET /health HTTP/1.0\r\nHost: x\r\nConnection: Keep-Alive\r\n\r\nHEAD / HTTP/1.0\r\nConnection: keep-alive, close\r\n\r\n") ==
    ([Eng.Req{Eng.MGet{}, "/health", "", False{}, False{}, ""},
      Eng.Req{Eng.MHead{}, "/", "", True{}, False{}, ""}], False{}) :
    List<&2, Eng.Req> & Bool}

law parse_10_upgrade:
  {Eng.parse("GET /ws HTTP/1.0\r\nUpgrade: websocket\r\nConnection: keep-alive, Upgrade\r\nSec-WebSocket-Key: k\r\n\r\nGET / HTTP/1.1\r\nHost: x\r\n\r\n") ==
    ([Eng.Req{Eng.MGet{}, "/ws", "", False{}, False{}, "k"},
      Eng.Req{Eng.MGet{}, "/", "", False{}, False{}, ""}], False{}) :
    List<&2, Eng.Req> & Bool}

# a chunked body, decoded: chunks joined, extensions and the trailer
# read by their grammar and dropped, the next request after it
law parse_chunked:
  {Eng.parse("GET /echo HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\nGET / HTTP/1.1\r\nHost: x\r\n\r\n") ==
    ([Eng.Req{Eng.MGet{}, "/echo", "hello", False{}, False{}, ""},
      Eng.Req{Eng.MGet{}, "/", "", False{}, False{}, ""}], False{}) :
    List<&2, Eng.Req> & Bool}

law parse_chunked_ext:
  {Eng.parse("GET /echo HTTP/1.1\r\nHost: x\r\ntransfer-encoding: CHUNKED\r\n\r\n5 ;a=b; c = \"q\\\"x\"\r\nhello\r\nA;z\r\n, world!!!\r\n000;x\r\nX-T: y\r\nZ:\r\n\r\n") ==
    ([Eng.Req{Eng.MGet{}, "/echo", "hello, world!!!", False{}, False{}, ""}], False{}) :
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

# CL.TE: a length, then a coding; and TE.CL, the other way round
law refuse_te:
  {Eng.parse("GET /echo HTTP/1.1\r\nHost: x\r\nContent-Length: 5\r\nTRANSFER-encoding: chunked\r\n\r\n0\r\n\r\n") ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

law refuse_te_cl:
  {Eng.parse("GET /echo HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\nContent-Length: 3\r\n\r\n8\r\nSMUGGLED\r\n0\r\n\r\n") ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

# TE.TE: the coding dressed up so one reader takes it and another does
# not, and two of them
law refuse_te_space:
  {Eng.parse("GET /echo HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked \r\n\r\n0\r\n\r\n") ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

law refuse_te_xchunked:
  {Eng.parse("GET /echo HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: xchunked\r\n\r\n0\r\n\r\n") ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

law refuse_te_list:
  {Eng.parse("GET /echo HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked, identity\r\n\r\n0\r\n\r\n") ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

law refuse_te_te:
  {Eng.parse("GET /echo HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\nTransfer-Encoding: identity\r\n\r\n0\r\n\r\n") ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

law refuse_te_twice:
  {Eng.parse("GET /echo HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\ntransfer-encoding: chunked\r\n\r\n0\r\n\r\n") ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

law refuse_te_10:
  {Eng.parse("GET /echo HTTP/1.0\r\nTransfer-Encoding: chunked\r\n\r\n0\r\n\r\n") ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

# a chunked body's framing broken: a bare LF after a size, data not
# followed by its CRLF, whitespace before a size line's CR, a line with
# no size, a size past the cap and one that would wrap, a folded
# trailer line
law refuse_chunk_bare_lf:
  {Eng.parse("GET /echo HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n5\nhello\r\n0\r\n\r\n") ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

law refuse_chunk_data_lf:
  {Eng.parse("GET /echo HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\n0\r\n\r\n") ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

law refuse_chunk_long:
  {Eng.parse("GET /echo HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n3\r\nhello\r\n0\r\n\r\n") ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

law refuse_chunk_ws:
  {Eng.parse("GET /echo HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n5 \r\nhello\r\n0\r\n\r\n") ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

law refuse_chunk_no_size:
  {Eng.parse("GET /echo HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n;a=b\r\n\r\n") ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

law refuse_chunk_past_cap:
  {Eng.parse("GET /echo HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n100000") ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

law refuse_chunk_wrap:
  {Eng.parse("GET /echo HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n100000005\r\nhello\r\n0\r\n\r\n") ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

law refuse_chunk_ext:
  {Eng.parse("GET /echo HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n5;a=\"b\r\nhello\r\n0\r\n\r\n") ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

law refuse_trailer_fold:
  {Eng.parse("GET /echo HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n0\r\nX: a\r\n b\r\n\r\n") ==
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
  {Eng.parse("GET /health HTTP/1.2\r\nHost: x\r\n\r\n") ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

law refuse_10_two_hosts:
  {Eng.parse("GET /health HTTP/1.0\r\nHost: a\r\nHost: a\r\n\r\n") ==
    (Nil{}, True{}) : List<&2, Eng.Req> & Bool}

# a refusal does not take back the message completed before it: its
# reply is owed, and goes out before the 400
law refuse_after_one:
  {Eng.parse("GET / HTTP/1.1\r\nHost: x\r\n\r\nGET / HTTP/1.1\r\nHost : x\r\n\r\n") ==
    ([Eng.Req{Eng.MGet{}, "/", "", False{}, False{}, ""}], True{}) :
    List<&2, Eng.Req> & Bool}

# Framing, whole
# ==============
#
# The laws above hold the reader to the RFC one rule and one vector at
# a time. These hold it to spec.bend's frame() -- a reading of a whole
# input written from RFC 9112 a line at a time, sharing no code with
# the reader -- for every input at once.

# LAW: the reader's classes and lowercasing are the reference's on every
# U32, not only on the 256 bytes cls_is_spec runs.
law cls_every:
  for +c: U32
  {Eng.cls(c) == Spec.cls(c) : Eng.Cls}

law lower_every:
  for +c: U32
  {Eng.lower(c) == Spec.lower(c) : U32}

# The reader seen from outside: the requests it has completed, oldest
# first, and whether it is reading, has refused, or has handed what
# follows an upgrade to the frame reader.
type Look is Data:
  Reading{}
  Refusing{}
  Handing{}

def look.st(st: Eng.St) -> Look:
  match st:
    case Eng.Bad{}:
      Refusing{}
    case Eng.Rest{b}:
      Handing{}
    case _:
      Reading{}

def look(p: Eng.P) -> List<&2, Eng.Req> & Look:
  match p:
    case Eng.P{st, pd, out}:
      (List.reverse(&2, Eng.Req, out), look.st(st))

# A reader agrees with a framing when it has completed exactly the
# framing's requests, in order, and then: where the framing is open, it
# is still reading and is exactly the state a fresh reader holding those
# requests reaches on the bytes since the last of them; where the
# framing refuses, it has refused; where the last request upgraded, it
# holds exactly the bytes that followed that request.
def agree.end(-p: Eng.P, +rs: List<&2, Eng.Req>, e: Spec.End) -> Type:
  match e:
    case Spec.Open{rest}:
      {look(p) == (rs, Reading{}) : List<&2, Eng.Req> & Look} &
        {p == Eng.feed(rest, Eng.P{Eng.Pre{}, Eng.pend.new(), List.reverse(&2, Eng.Req, rs)}) : Eng.P}
    case Spec.Refused{}:
      {look(p) == (rs, Refusing{}) : List<&2, Eng.Req> & Look}
    case Spec.Upgraded{b}:
      {p == Eng.P{Eng.Rest{b}, Eng.pend.new(), List.reverse(&2, Eng.Req, rs)} : Eng.P}

def agree(-p: Eng.P, f: Spec.Frames) -> Type:
  match f:
    case Spec.Frames{rs, e}:
      agree.end(p, rs, e)

# LAW: the reader is the framing. For every input, a fresh reader fed it
# agrees with frame() of it: the same requests at the same byte
# boundaries, a refusal exactly where the framing refuses, and nothing
# but the framing's own leftover in its pending state.
law frame_sim:
  for +bs: List<&2, U32>
  agree(Eng.feed(bs, Eng.p.new()), Spec.frame(bs))

# LAW: the same for the walk the server runs, over one read ...
law frame_sim_buf:
  for +b: Bytes()
  agree(Eng.feed_buf(b, Eng.p.new()), Spec.frame(Bytes.to_list(b)))

# ... and over a connection's reads however TCP cut them: the reader
# fed each read in turn agrees with frame() of them all, joined.
# (the reader kit's walk over a list of reads, wire/reader.bend)
def reads(rs: List<&2, Bytes()>, p: Eng.P) -> Eng.P:
  Wr.reads(~Unit, ~Eng.P, ~Eng.wstep, ~Eng.wadv, Unit{}, rs, p)

law frame_sim_reads:
  for +rs: List<&2, Bytes()>
  agree(reads(rs, Eng.p.new()), Spec.frame(Bytes.to_list(Bytes.concat(rs))))

# every byte a read of its own
def each(s: Bytes()) -> List<&2, Bytes()>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{c, t}:
      Con{SCon{c, SNil{}}, each(t)}

# the same body cut at every awkward place a read could end: inside the
# size, inside a CRLF, inside an extension, inside the trailer
law chunk_cuts:
  {look(reads(["GET /echo HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n1", "0;e", "xt=\"a\\", "\"b\"\r", "\n0123456789abcdef\r", "\n0\r\nX-", "Tr: v", "\r", "\n\r", "\n"],
    Eng.p.new())) ==
    ([Eng.Req{Eng.MGet{}, "/echo", "0123456789abcdef", False{}, False{}, ""}], Reading{}) :
    List<&2, Eng.Req> & Look}

law chunk_bytes:
  {look(reads(each("GET /echo HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n3;a=\"\\\"\"\r\nabc\r\n0\r\nT: v\r\n\r\n"),
    Eng.p.new())) ==
    ([Eng.Req{Eng.MGet{}, "/echo", "abc", False{}, False{}, ""}], Reading{}) :
    List<&2, Eng.Req> & Look}


# LAW: and frame() itself, on three vectors: a request served with the
# next one begun, one that upgrades, and a folded line refused.
law frame_get:
  {Spec.frame(Eng.bytes("GET /health HTTP/1.1\r\nHost: x\r\n\r\nGET /ec")) ==
    Spec.Frames{[Eng.Req{Eng.MGet{}, "/health", "", False{}, False{}, ""}],
      Spec.Open{Eng.bytes("GET /ec")}} : Spec.Frames}

law frame_upgrade:
  {Spec.frame(Eng.bytes("GET /ws HTTP/1.1\r\nHost: x\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Key: k\r\n\r\nab")) ==
    Spec.Frames{[Eng.Req{Eng.MGet{}, "/ws", "", False{}, True{}, "k"}], Spec.Upgraded{"ab"}} : Spec.Frames}

law frame_refuse_fold:
  {Spec.frame(Eng.bytes("GET / HTTP/1.1\r\nHost: x\r\n Content-Length: 5\r\n\r\nhello")) ==
    Spec.Frames{Nil{}, Spec.Refused{}} : Spec.Frames}

law frame_chunked:
  {Spec.frame(Eng.bytes("GET /echo HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n2;x=y\r\nhi\r\n0\r\nT: v\r\n\r\nGET /")) ==
    Spec.Frames{[Eng.Req{Eng.MGet{}, "/echo", "hi", False{}, False{}, ""}],
      Spec.Open{Eng.bytes("GET /")}} : Spec.Frames}

law frame_10:
  {Spec.frame(Eng.bytes("GET / HTTP/1.0\r\n\r\n")) ==
    Spec.Frames{[Eng.Req{Eng.MGet{}, "/", "", True{}, False{}, ""}], Spec.Open{Nil{}}} : Spec.Frames}

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
  {U32.is_lt(L.batch.keep(U32.cmp(k, L.send.cap()), k), L.send.cap()) ==
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
  for +hw: L.Hw
  {L.hw.next(False{}, hw) == L.NoHead{} : L.Hw}

law hw_keeps:
  for +t0: Nat
  for +n: U32
  {L.hw.next(True{}, L.Since{t0, n}) == L.Since{t0, n} : L.Hw}

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

# LAW: whitespace at either end of a field value is no part of it (RFC
# 9110 5.5), so a key and a version padded with it read as the key and
# as 13; whitespace inside a value stays in it, so "1 3" is not 13
law parse_ows_trimmed:
  {Eng.parse("GET /ws HTTP/1.1\r\nHost: x\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Key: k \t\r\nSec-WebSocket-Version: \t13 \r\n\r\n") ==
    ([Eng.Req{Eng.MGet{}, "/ws", "", False{}, True{}, "k"}], False{}) :
    List<&2, Eng.Req> & Bool}

law parse_version_inner:
  {Eng.parse("GET /ws HTTP/1.1\r\nHost: x\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Key: k\r\nSec-WebSocket-Version: 1 3\r\n\r\n") ==
    ([Eng.Req{Eng.MGet{}, "/ws", "", False{}, False{}, "k"}], False{}) :
    List<&2, Eng.Req> & Bool}

# The world
# =========
#
# The connection loop and the accept loop, run in bend-wire's pure
# model of the socket world (wire/world.bend) at the engine's hooks
# (world.bend): the same defs the server runs, with the identity monad
# and a scripted peer in place of IO and the effects. These laws hold
# for every peer the script can describe and every state the loop can
# be in; each is wire/world.bend's law, proven there for every
# protocol, at this engine's hooks. What they assume of each effect is
# its contract (wire/world.bend), which the last laws below show the
# model keeps and wire/conform.bend checks the real effects keep.

# LAW: a plan that ends the connection is the last thing it does. After
# End the loop writes its segments and answers the socket, to be
# closed, with nothing read and nothing more written; after Stop it
# does nothing at all.
law end_is_last:
  for +srv: Eng.Srv
  for w: WW.World
  for out: List<&2, L.Seg>
  for hw: L.Hw
  for g: Nat
  for v: Nat
  {W.sim.conn(1n+g, srv, ((w, L.End{out}), hw), v) ==
    L.put.s(WW.World, W.sim.segs(w, out, Eng.srv.idle(srv))) : WW.World}

law stop_is_last:
  for +srv: Eng.Srv
  for w: WW.World
  for hw: L.Hw
  for g: Nat
  for v: Nat
  {W.sim.conn(1n+g, srv, ((w, L.Stop{}), hw), v) == w : WW.World}

# LAW: a plan that reads on writes all its replies first. Go's segments
# go out, the next read waits for them, and the head's watch starts
# over.
law go_order:
  for +srv: Eng.Srv
  for w: WW.World
  for out: List<&2, L.Seg>
  for +p2: Eng.P
  for hw: L.Hw
  for g: Nat
  for v: Nat
  {W.sim.conn(1n+g, srv, ((w, L.Go{out, p2}), hw), v) ==
    W.sim.conn(g, srv, W.sim.turn(srv, W.sim.segs(w, out, Eng.srv.idle(srv)), p2,
      L.hw.next(Eng.p.head(p2), L.NoHead{})), L.conn.waits()) : WW.World}

# LAW: reply order. At a peer that takes what it is sent, the replies
# go out byte for byte, in the order of their segments, after whatever
# the peer already had, and the send succeeds. (For segments that are
# not files; a file's bytes are the file's.)
law segs_wire:
  for +xs: List<&2, L.Seg>
  for +ms: U32
  for +rd: List<&2, WW.Rd>
  for +now: Nat
  for +fs: List<&2, WW.Fil>
  for +out: Bytes()
  for +e: {WW.raws(xs) == True{} : Bool}
  {W.sim.segs(WW.eager(rd, now, fs, out), xs, ms) ==
    WW.sent(rd, now, fs, Bytes.append(out, W.wire(xs, False{}))) : L.Put(WW.World)}

# LAW: nothing is done after a send fails. Whether the send was a read's
# replies, a WebSocket's frames or a stream's event, a send that failed
# or stalled is the connection's last act on its socket: no read, no
# write (the stream only finishes the sleep it was in).
law fail_go:
  for +srv: Eng.Srv
  for g: Nat
  for v: Nat
  for m: L.Put(WW.World)
  for p: Eng.P
  for hw: L.Hw
  for e: {WW.put.done(m) == False{} : Bool}
  {W.sim.conn(g, srv, W.sim.turn(srv, m, p, hw), v) == L.put.s(WW.World, m) : WW.World}

law fail_ws:
  for +srv: Eng.Srv
  for g: Nat
  for v: Nat
  for m: L.Put(WW.World)
  for wr: Ws.W
  for e: {WW.put.done(m) == False{} : Bool}
  {W.sim.conn(g, srv, (W.sim.turn.ws(srv, m, wr), L.NoHead{}), v) ==
    L.put.s(WW.World, m) : WW.World}

law fail_feed:
  for +srv: Eng.Srv
  for g: Nat
  for v: Nat
  for m: L.Put(WW.World)
  for n: U32
  for e: {WW.put.done(m) == False{} : Bool}
  {W.sim.conn(g, srv, (W.sim.tick(m, n), L.NoHead{}), v) ==
    WW.w.nap(L.put.s(WW.World, m), Eng.sse.gap()) : WW.World}

# LAW: a refusal. When the requests a read completed all keep the
# connection and the grammar then broke, the plan is to write every
# reply those requests are owed, in their order, then the 400, and to
# end; and the connection does exactly that: its last act is writing
# them, and it reads nothing more, so no request after the refusal is
# ever consumed. (send.segs takes no read effect, so it cannot read.)
law refuse_plan:
  for +srv: Eng.Srv
  for +rs: List<&2, Eng.Req>
  for +q: Eng.P
  for +e: {W.all.keep(srv, rs) == True{} : Bool}
  {Eng.plan.take(srv, (q, rs), True{}) == L.End{W.owed(srv, rs, W.bad.reply())} : Eng.Plan()}

law refuse_conn:
  for +srv: Eng.Srv
  for w: WW.World
  for +q: Eng.P
  for +rs: List<&2, Eng.Req>
  for hw: L.Hw
  for g: Nat
  for v: Nat
  for +e: {W.all.keep(srv, rs) == True{} : Bool}
  {W.sim.conn(1n+g, srv, ((w, Eng.plan.take(srv, (q, rs), True{})), hw), v) ==
    L.put.s(WW.World, W.sim.segs(w, W.owed(srv, rs, W.bad.reply()), Eng.srv.idle(srv))) :
    WW.World}

# LAW: bounded buffering, the replies. Whatever a reply is -- a fixed
# one, a missing file, a file of any size, sent by the kernel -- and
# whatever the peer does, a writer that may still take replies leaves
# it holding a batch below send.cap(): so the most ever held unsent is
# the cap, plus the one reply (or a file's head) that crossed it; a
# file's body is never held at all.
law hold_fine:
  for +ms: U32
  for s: WW.World
  for +acc: Bytes()
  {WW.em.fine(W.sim.hold(ms, s, acc)) == True{} : Bool}

law raw_fine:
  for +ms: U32
  for may: Maybe<&2, Bytes()>
  for bs: Bytes()
  for st: L.Em<WW.World>
  {WW.em.fine(W.sim.raw(ms, may, bs, st)) == True{} : Bool}

law page_fine:
  for +ms: U32
  for root: List<&2, U32>
  for path: List<&2, U32>
  for ct: List<&2, U32>
  for head: Bool
  for may: Maybe<&2, Bytes()>
  for sh: Bool
  for st: L.Em<WW.World>
  {WW.em.fine(W.sim.page(ms, root, path, ct, head, may, sh, st)) == True{} : Bool}

# LAW: a file's bytes. At a peer that takes what it is sent, a GET of a
# file the root has (under 4 GiB) puts on the wire what waited in front
# of it, the file's head, and then the file's own bytes, every one and
# nothing else, by sendfile; and a sendfile or a head that did not go
# out ends the connection with nothing after it.
law page_wire:
  for +ms: U32
  for root: List<&2, U32>
  for path: List<&2, U32>
  for +ct: List<&2, U32>
  for may: Maybe<&2, Bytes()>
  for +sh: Bool
  for +rd: List<&2, WW.Rd>
  for +now: Nat
  for +fs: List<&2, WW.Fil>
  for +out: Bytes()
  for +acc: Bytes()
  for +body: Bytes()
  for ef: {WW.w.find(fs, L.text(path)) == Done{body} : Result<&1, &1, U32 & String, Bytes()>}
  for en: {U32.to_nat(U32.from_nat(Bytes.len(body))) == Bytes.len(body) : Nat}
  {W.sim.page(ms, root, path, ct, False{}, may, sh, L.Em{WW.eager(rd, now, fs, out), acc, True{}}) ==
    L.Em{WW.eager(rd, now, fs, Bytes.append(Bytes.append(out,
      Bytes.append(acc, Eng.h.shut(sh, Eng.h.fhead(ct, U32.from_nat(Bytes.len(body)))))), body)),
      "", True{}} : L.Em<WW.World>}

law page_fail:
  for s: WW.World
  for f: Bytes()
  for e: U32 & String
  {WW.sim.fsent((s, (f, Fail{e}))) == L.Em{s, "", False{}} : L.Em<WW.World>}

law page_head_fail:
  for +ms: U32
  for f: Bytes()
  for n: U32
  for s: WW.World
  for e: U32 & String
  {WW.sim.headed(ms, f, n, (s, Fail{e})) == L.Em{s, "", False{}} : L.Em<WW.World>}

# LAW: bounded buffering, the head. A read that leaves a head in
# progress leaves it with at most head.cap() bytes since the read it
# began in; one that would take it past is answered with a 431 and the
# connection ends. With a read at most chunk() bytes, a head held is at
# most chunk() + head.cap(); a body, body.cap() (the reader's). A
# chunked body keeps the same two bounds: its data, its chunk lines and
# their extensions are paid from one budget of body.cap() (only the data
# is held; chunk_size_capped, chunk_ext_capped), and its trailer is a
# head's field lines again, read under this cap and dropped.
law head_capped:
  for +srv: Eng.Srv
  for w: WW.World
  for may: Maybe<&1, Bytes()>
  for p: Eng.P
  for t0: Nat
  for +n: U32
  {WW.hw.fine(W.hw.of(W.plan.counted(srv, w, may, p, t0, n))) == True{} : Bool}

# LAW: the head deadline. A head whose time (--head-ms) has run out is
# not read again: the turn ends the connection there, whatever the peer
# would have sent. (A head's time is kept across the reads that
# continue it: hw_keeps.)
law head_expires:
  for +srv: Eng.Srv
  for +w: WW.World
  for p: Eng.P
  for +t0: Nat
  for n: U32
  for e: {Nat.is_lt(Nat.sub(WW.w.now(w), t0), U32.to_nat(Eng.srv.head(srv))) == False{} : Bool}
  {W.sim.turn.h(srv, w, p, L.Since{t0, n}) == ((w, L.Stop{}), L.NoHead{}) :
    (WW.World & Eng.Plan()) & L.Hw}

# LAW: liveness under stall. At a peer that has stopped -- every read
# waits out its time (idle or head) and gets nothing, every send that
# has bytes to move waits out its time and fails -- the connection ends
# within three turns from any state the loop can be in: fuel past three
# changes nothing.
law stall_ends:
  for +srv: Eng.Srv
  for +w: WW.World
  for pl: Eng.Plan()
  for +hw: L.Hw
  for +g: Nat
  for +v: Nat
  {W.mute.conn(1n+1n+1n+g, srv, ((w, pl), hw), v) ==
    W.mute.conn(1n+1n+1n, srv, ((w, pl), hw), v) : WW.World}

# LAW: the accept loop stays up. With no stop request and every accept
# failure one of the passing set (EMFILE, ECONNABORTED, ...), the loop
# runs every turn it is given, however connections come and go.
law accept_calm:
  for k: Nat
  for +evs: List<&2, WW.Ac>
  for +served: Nat
  for +e: {WW.calm(evs) == True{} : Bool}
  {WW.why.of(WW.sim.accept(k, WW.Lw{evs, False{}, served})) == L.Spent{} : L.Why}

# LAW: ... and ends only as it may: its turns spent, a stop asked, or a
# failure outside the passing set, a listener that is no longer one.
# The model lets accept fail with any code at any time, so this assumes
# nothing of accept_poll's own sorting of them.
law accept_ends:
  for +k: Nat
  for sp: Bool
  for +evs: List<&2, WW.Ac>
  for +served: Nat
  {WW.ok.end(WW.why.of(WW.sim.accept(k, WW.Lw{evs, sp, served}))) == True{} : Bool}

# LAW: the model keeps the contracts it assumes. A read answers nothing
# only after its time, and bytes (no more than asked, when the peer's
# fit) within it; a send to a peer that has stopped reading fails with
# ETIMEDOUT after its time, and one to a peer that reads succeeds; a
# file read takes no more than it asked for.
law rx_model:
  for +rd: List<&2, WW.Rd>
  for +wr: List<&2, WW.Wr>
  for +eager: Bool
  for +now: Nat
  for +fs: List<&2, WW.Fil>
  for +out: Bytes()
  for +max: U32
  for +ms: U32
  for e: {WW.fits(rd, max) == True{} : Bool}
  {WW.rx.seen(max, ms, now, WW.w.rx(WW.World{rd, wr, eager, now, fs, out}, max, ms)) ==
    True{} : Bool}

law tx_stalled:
  for +rd: List<&2, WW.Rd>
  for +now: Nat
  for +fs: List<&2, WW.Fil>
  for +out: Bytes()
  for +h: Char
  for +t: Bytes()
  for +ms: U32
  {WW.tx.seen(ms, WW.Stops{}, now, WW.w.tx(WW.World{rd, Nil{}, False{}, now, fs, out}, SCon{h, t}, ms)) ==
    True{} : Bool}

law tx_served:
  for +rd: List<&2, WW.Rd>
  for +now: Nat
  for +fs: List<&2, WW.Fil>
  for +out: Bytes()
  for +a: Bytes()
  for +ms: U32
  {WW.tx.seen(ms, WW.Reads{}, now, WW.w.tx(WW.eager(rd, now, fs, out), a, ms)) == True{} : Bool}

law fread_model:
  for +f: Bytes()
  for +n: Nat
  {Nat.is_le(Bytes.len(String.take(f, n)), n) == True{} : Bool}

law fsend_model:
  for +rd: List<&2, WW.Rd>
  for +now: Nat
  for +fs: List<&2, WW.Fil>
  for +out: Bytes()
  for +f: Bytes()
  for +off: U32
  for +len: U32
  for +ms: U32
  {WW.fsend.ok(ms, WW.Reads{}, 0n, Bytes.len(String.drop(f, U32.to_nat(off))), U32.to_nat(len),
    WW.fsend.res(WW.w.fsend(WW.eager(rd, now, fs, out), f, off, len, ms))) == True{} : Bool}

law fsend_stalled:
  for +rd: List<&2, WW.Rd>
  for +now: Nat
  for +fs: List<&2, WW.Fil>
  for +out: Bytes()
  for +f: Bytes()
  for +off: U32
  for +len: U32
  for +ms: U32
  for +h: Char
  for +t: Bytes()
  for e: {WW.w.fbytes(f, off, len) == SCon{h, t} : Bytes()}
  {WW.fsend.ok(ms, WW.Stops{}, Nat.sub(Nat.add(now, U32.to_nat(ms)), now),
    Bytes.len(String.drop(f, U32.to_nat(off))), U32.to_nat(len),
    WW.fsend.res(WW.w.fsend(WW.World{rd, Nil{}, False{}, now, fs, out}, f, off, len, ms))) ==
    True{} : Bool}
