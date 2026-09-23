# The laws of the response reader. The human states them; PROOF.bend
# proves them. The kit's laws hold it to itself -- chunking never
# changes a read, a refusal is never left, the block walk is the byte
# machine -- resp_sim holds it to spec.bend for every input, and the
# vectors pin what the spec says of the responses that matter: the ones
# a proxy must frame as the next hop does, and the ones it must refuse.
import Base
import ../reader.bend as Wr
import ./resp.bend as R
import ./spec.bend as S

# The reader kit
# ==============

# LAW: chunking does not change the read: a response cut anywhere reads
# as the response whole.
law feed_split:
  for +e: R.Ask
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +p: R.P
  {R.feed(e, List.append(&2, U32, a, b), p) == R.feed(e, b, R.feed(e, a, p)) : R.P}

# LAW: a refusal is never left: nothing after a refused byte is read, so
# nothing the peer sends after a malformed head can be taken for a
# response.
law bad_absorbs:
  for +e: R.Ask
  for +c: U32
  for +out: List<&2, U32>
  {R.step(e, R.P{R.Bad{}, out}, c) == R.P{R.Bad{}, out} : R.P}

law bad_feeds:
  for +e: R.Ask
  for +s: List<&2, U32>
  for +out: List<&2, U32>
  {R.feed(e, s, R.P{R.Bad{}, out}) == R.P{R.Bad{}, out} : R.P}

# LAW: the walk a client runs on a read is the byte machine: bodies are
# taken as runs, and land where stepping their bytes does.
law feed_buf_is_feed:
  for +e: R.Ask
  for +b: Bytes()
  for +p: R.P
  {R.feed_buf(e, b, p) == R.feed(e, Bytes.to_list(b), p) : R.P}

law feed_buf_split:
  for +e: R.Ask
  for +a: Bytes()
  for +b: Bytes()
  for +p: R.P
  {R.feed_buf(e, Bytes.append(a, b), p) == R.feed_buf(e, b, R.feed_buf(e, a, p)) : R.P}

law bad_feeds_buf:
  for +e: R.Ask
  for +s: Bytes()
  for +out: List<&2, U32>
  {R.feed_buf(e, s, R.P{R.Bad{}, out}) == R.P{R.Bad{}, out} : R.P}

# LAW: however TCP cut the response into reads, the reader fed each in
# turn is the reader fed them joined.
law reads_split:
  for +e: R.Ask
  for +rs: List<&2, Bytes()>
  for +p: R.P
  {R.reads(e, rs, p) == R.feed_buf(e, Bytes.concat(rs), p) : R.P}

# The classes
# ===========

# LAW: the classes the reader and the spec share are the RFC's, byte for
# byte, all 256 of them; and so is lowercasing.
law cls_rfc:
  {S.cls.eng(S.all()) == S.cls.ref(S.all()) : List<&2, R.Cls>}

law lower_rfc:
  {S.lower.eng(S.all()) == S.lower.ref(S.all()) : List<&2, U32>}

# The framing
# ===========

# LAW: the reader is the framing. For every context (HEAD or not, every
# cap) and every input, a fresh reader fed it reads what RFC 9112's
# framing, written plainly in spec.bend, reads: the same interim
# statuses, and the same end -- still reading, refused, the same final
# response with the same bytes after it, or the same body running to
# the close. On every input means on every prefix of every input: the
# two agree byte by byte, not only at the end.
law resp_sim:
  for +e: R.Ask
  for +bs: List<&2, U32>
  {R.look(R.feed(e, bs, R.p.new())) == S.response(e, bs) : R.Look}

# LAW: the same for the walk the client runs on one read ...
law resp_sim_buf:
  for +e: R.Ask
  for +b: Bytes()
  {R.look(R.feed_buf(e, b, R.p.new())) == S.response(e, Bytes.to_list(b)) : R.Look}

# ... and over a connection's reads however TCP cut them.
law resp_sim_reads:
  for +e: R.Ask
  for +rs: List<&2, Bytes()>
  {R.look(R.reads(e, rs, R.p.new())) == S.response(e, Bytes.to_list(Bytes.concat(rs))) : R.Look}

# The vectors
# ===========
#
# Each is a whole input run through the real reader, from a fresh state,
# as the client runs it; resp_sim says the spec reads each the same.

def A() -> R.Ask:
  R.Ask{False{}, 1024}

def H() -> R.Ask:
  R.Ask{True{}, 1024}

def rd(+e: R.Ask, +s: Bytes()) -> R.Look:
  R.look(R.feed_buf(e, s, R.p.new()))

# every byte a read of its own
def each(s: Bytes()) -> List<&2, Bytes()>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{c, t}:
      Con{SCon{c, SNil{}}, each(t)}

# LAW: the same chunked response cut at every awkward place a read
# could end -- inside the status, a name, the size, a CRLF, an
# extension's quoted-string, the trailer -- and a byte at a time
law cuts:
  {R.look(R.reads(A(), ["HTTP/1.1 2", "00 OK\r", "\nTransfer-Enc", "oding: chunked\r\n\r\n1", "0;e", "xt=\"a\\",
    "\"b\"\r", "\n0123456789abcdef\r", "\n0\r\nX-", "Tr: v", "\r", "\n\r", "\n"], R.p.new())) ==
    R.Look{[], R.Final{R.Resp{200, False{}, False{}, "0123456789abcdef"}, ""}} : R.Look}

law cuts_bytes:
  {R.look(R.reads(A(), each("HTTP/1.1 100 Go\r\n\r\nHTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n3;a=\"\\\"\"\r\nabc\r\n0\r\nT: v\r\n\r\n"),
    R.p.new())) ==
    R.Look{[100], R.Final{R.Resp{200, False{}, False{}, "abc"}, ""}} : R.Look}

# LAW: what is framed as the next hop frames it.
# the interim responses, then the final one: 100 and 103 are heard and skipped
law v_interim:
  {rd(A(), "HTTP/1.1 100 Continue\r\n\r\nHTTP/1.1 103 Early Hints\r\nLink: </s.css>; rel=preload\r\n\r\nHTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nhi") ==
    R.Look{[100, 103], R.Final{R.Resp{200, False{}, False{}, "hi"}, ""}} : R.Look}

# a 204's Content-Length frames nothing: the bytes after its head are not its body
law v_204_len:
  {rd(A(), "HTTP/1.1 204 No Content\r\nContent-Length: 5\r\n\r\nHTTP/1.1 200 OK\r\n") ==
    R.Look{[], R.Final{R.Resp{204, False{}, False{}, ""}, "HTTP/1.1 200 OK\r\n"}} : R.Look}

# nor does a 304's Transfer-Encoding
law v_304:
  {rd(A(), "HTTP/1.1 304 Not Modified\r\nETag: \"x\"\r\nTransfer-Encoding: chunked\r\n\r\n") ==
    R.Look{[], R.Final{R.Resp{304, False{}, False{}, ""}, ""}} : R.Look}

# a response to HEAD has no body, whatever its length says
law v_head:
  {rd(H(), "HTTP/1.1 200 OK\r\nContent-Length: 12\r\n\r\n") ==
    R.Look{[], R.Final{R.Resp{200, False{}, False{}, ""}, ""}} : R.Look}

# or its coding
law v_head_chunked:
  {rd(H(), "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n") ==
    R.Look{[], R.Final{R.Resp{200, False{}, False{}, ""}, ""}} : R.Look}

# a chunked body, decoded: extensions (a token, a quoted-string with an escape, BWS before the ";") and the trailer read and dropped
law v_chunked:
  {rd(A(), "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n4;a=b;c=\"d\\\"e\"\r\nWiki\r\n5 ; x\r\npedia\r\n0;last\r\nExpires: never\r\nX-T: v\r\n\r\n") ==
    R.Look{[], R.Final{R.Resp{200, False{}, False{}, "Wikipedia"}, ""}} : R.Look}

# no length and no coding: the body runs to the close, and the connection ends with it
law v_close:
  {rd(A(), "HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\n\r\nsome body") ==
    R.Look{[], R.Closing{R.Resp{200, False{}, True{}, "some body"}}} : R.Look}

# HTTP/1.0 keeps the connection only when it says keep-alive
law v_10_keepalive:
  {rd(A(), "HTTP/1.0 200 OK\r\nConnection: Keep-Alive\r\nContent-Length: 2\r\n\r\nok") ==
    R.Look{[], R.Final{R.Resp{200, True{}, False{}, "ok"}, ""}} : R.Look}

law v_10_close:
  {rd(A(), "HTTP/1.0 200 OK\r\nContent-Length: 2\r\n\r\nok") ==
    R.Look{[], R.Final{R.Resp{200, True{}, True{}, "ok"}, ""}} : R.Look}

# close anywhere in a Connection list, in any case, closes
law v_conn_close:
  {rd(A(), "HTTP/1.1 200 OK\r\nConnection: upgrade, CLOSE\r\nContent-Length: 0\r\n\r\n") ==
    R.Look{[], R.Final{R.Resp{200, False{}, True{}, ""}, ""}} : R.Look}

# a 101 is final and ends HTTP on the connection: what follows is kept, not read
law v_101:
  {rd(A(), "HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n\r\nframes") ==
    R.Look{[], R.Final{R.Resp{101, False{}, True{}, ""}, "frames"}} : R.Look}

# a status line may end after its code
law v_no_reason:
  {rd(A(), "HTTP/1.1 204\r\n\r\n") ==
    R.Look{[], R.Final{R.Resp{204, False{}, False{}, ""}, ""}} : R.Look}

# what follows the final response is kept apart from it, never read into it
law v_after:
  {rd(A(), "HTTP/1.1 200 OK\r\nContent-Length: 1\r\n\r\nxHTTP/1.1 200 OK\r\n") ==
    R.Look{[], R.Final{R.Resp{200, False{}, False{}, "x"}, "HTTP/1.1 200 OK\r\n"}} : R.Look}

# a body that runs to the close, held under the cap
law v_close_cap:
  {rd(R.Ask{False{}, 4}, "HTTP/1.1 200 OK\r\n\r\nabcd") ==
    R.Look{[], R.Closing{R.Resp{200, False{}, True{}, "abcd"}}} : R.Look}

# LAW: and what is refused. None of these completes a response: each is
# how a response is split, or a request smuggled behind one, by a
# reader that frames it another way.
# CL.TE and TE.CL: two framings are how a response is split (RFC 9112 6.3.3)
law r_cl_te:
  {rd(A(), "HTTP/1.1 200 OK\r\nContent-Length: 3\r\nTransfer-Encoding: chunked\r\n\r\n") == R.Look{[], R.Refused{}} : R.Look}

law r_te_cl:
  {rd(A(), "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\nContent-Length: 3\r\n\r\n") == R.Look{[], R.Refused{}} : R.Look}

# a coding in HTTP/1.0 is faulty framing (6.1)
law r_te_10:
  {rd(A(), "HTTP/1.0 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n") == R.Look{[], R.Refused{}} : R.Look}

# TE.TE: a coding this reader does not decode, a list, chunked dressed up, and chunked twice
law r_te_list:
  {rd(A(), "HTTP/1.1 200 OK\r\nTransfer-Encoding: gzip, chunked\r\n\r\n") == R.Look{[], R.Refused{}} : R.Look}

law r_te_space:
  {rd(A(), "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked \r\n\r\n") == R.Look{[], R.Refused{}} : R.Look}

law r_te_twice:
  {rd(A(), "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\nTransfer-Encoding: chunked\r\n\r\n") == R.Look{[], R.Refused{}} : R.Look}

# obs-fold: a line that starts with whitespace (5.2)
law r_fold:
  {rd(A(), "HTTP/1.1 200 OK\r\nX-A: a\r\n b\r\nContent-Length: 0\r\n\r\n") == R.Look{[], R.Refused{}} : R.Look}

# bare LF, after the status line and after a field line, and a bare CR (2.2)
law r_lf_status:
  {rd(A(), "HTTP/1.1 200 OK\nContent-Length: 0\r\n\r\n") == R.Look{[], R.Refused{}} : R.Look}

law r_lf_field:
  {rd(A(), "HTTP/1.1 200 OK\r\nContent-Length: 0\n\r\n") == R.Look{[], R.Refused{}} : R.Look}

law r_cr:
  {rd(A(), "HTTP/1.1 200 OK\r\nX: a\rb\r\n\r\n") == R.Look{[], R.Refused{}} : R.Look}

# CL.CL: a length that is a list, two lengths that disagree, a sign, none
law r_cl_list:
  {rd(A(), "HTTP/1.1 200 OK\r\nContent-Length: 5, 5\r\n\r\nhello") == R.Look{[], R.Refused{}} : R.Look}

law r_cl_two:
  {rd(A(), "HTTP/1.1 200 OK\r\nContent-Length: 5\r\nContent-Length: 6\r\n\r\nhello!") == R.Look{[], R.Refused{}} : R.Look}

law r_cl_sign:
  {rd(A(), "HTTP/1.1 200 OK\r\nContent-Length: +5\r\n\r\nhello") == R.Look{[], R.Refused{}} : R.Look}

law r_cl_empty:
  {rd(A(), "HTTP/1.1 200 OK\r\nContent-Length: \r\n\r\n") == R.Look{[], R.Refused{}} : R.Look}

# a space before the colon (5.1)
law r_space_colon:
  {rd(A(), "HTTP/1.1 200 OK\r\nContent-Length : 5\r\n\r\nhello") == R.Look{[], R.Refused{}} : R.Look}

# invalid status lines: two or four digits, a code below 100 or past 599, another version, a lowercase one, two spaces, a control in the reason
law r_status_short:
  {rd(A(), "HTTP/1.1 20 OK\r\n\r\n") == R.Look{[], R.Refused{}} : R.Look}

law r_status_long:
  {rd(A(), "HTTP/1.1 2000 OK\r\n\r\n") == R.Look{[], R.Refused{}} : R.Look}

law r_status_low:
  {rd(A(), "HTTP/1.1 099 Low\r\n\r\n") == R.Look{[], R.Refused{}} : R.Look}

law r_status_high:
  {rd(A(), "HTTP/1.1 600 High\r\n\r\n") == R.Look{[], R.Refused{}} : R.Look}

law r_version:
  {rd(A(), "HTTP/2 200 OK\r\n\r\n") == R.Look{[], R.Refused{}} : R.Look}

law r_version_case:
  {rd(A(), "http/1.1 200 OK\r\n\r\n") == R.Look{[], R.Refused{}} : R.Look}

law r_two_sp:
  {rd(A(), "HTTP/1.1  200 OK\r\n\r\n") == R.Look{[], R.Refused{}} : R.Look}

law r_reason_ctl:
  {rd(A(), "HTTP/1.1 200 O\u{1}K\r\n\r\n") == R.Look{[], R.Refused{}} : R.Look}

# a control in a value
law r_value_nul:
  {rd(A(), "HTTP/1.1 200 OK\r\nX: a\u{0}b\r\n\r\n") == R.Look{[], R.Refused{}} : R.Look}

# past the cap: a length, a chunk, a body that runs to the close
law r_cap_len:
  {rd(A(), "HTTP/1.1 200 OK\r\nContent-Length: 1025\r\n\r\n") == R.Look{[], R.Refused{}} : R.Look}

law r_cap_chunk:
  {rd(A(), "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n401\r\n") == R.Look{[], R.Refused{}} : R.Look}

law r_cap_close:
  {rd(R.Ask{False{}, 4}, "HTTP/1.1 200 OK\r\n\r\nabcde") == R.Look{[], R.Refused{}} : R.Look}
