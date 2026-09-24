# io_http_engine

An HTTP/1.1 engine in Bend (HTTP/1.0 too, and chunked request bodies):
a streaming request parser, a router and a server, with the parser's laws, and the connection and accept loops'
laws against a model of the socket world, proved by the stock checker.
No host language in the path — the socket is Bend's own effect.

    bend demos/io_http_engine/PROOF.bend        # the gate: laws hold
    python3 demos/io_http_engine/mutants.py     # and refuse nine broken loops, six broken framings
    bend demos/io_http_engine/main.bend -o httpd
    ./httpd --port 8080 --root www --idle-ms 10000 --max-conns 1024 --grace-ms 5000
    ./httpd --shared & ./httpd --shared &          # one port, one copy per core
    ./httpd --tls-cert cert.pem --tls-key key.pem  # https, ALPN, TLS 1.2+
    curl -i http://127.0.0.1:8080/health

The binary is the server: it links libc and libm and nothing else, and
needs no bend where it runs. Three runtime changes on this branch made
it possible, each measured below: TCP that carries bytes, a scheduler
whose pass costs what is ready rather than what is waiting, and a
listen backlog that is not sixteen.

## Bytes, not text

`TCP.recv` hands back a `String`, and a `String` is built by `io_str`,
which decodes the bytes as UTF-8. On a socket that is not a cost, it is
a corruption: every byte that is not valid UTF-8 becomes U+FFFD, three
bytes out for one byte in. Send eight arbitrary bytes to an engine
built on it and eighteen come back while Content-Length still says
eight — a reply that is longer than it announced, which on a
keep-alive connection desynchronises the stream rather than merely
mangling one body. `TCP.send` has the same hole outbound.

So this engine does not read text. `bend2/effs/tcp_recv_bytes.{c,js}`
and `tcp_send_bytes.{c,js}` carry `List<&2, U32>`, one cell per byte,
which is what `File.read_bytes` and `File.write_bytes` have always done
for files; `base.bend` declares them beside `TCP.recv` and `TCP.send`.
Nothing there is new machinery — it is the byte pair files have and
sockets did not.

`check.c`'s byte round trip is the one case that catches this: the
engine as first written passes every other case and fails that one.

## What it is

The reader is one walk over whatever bytes the socket hands over. Its
whole state rides in one `P` node, so a head split across three recvs
parses exactly like a head that arrived whole, and a chunk holding
three pipelined requests yields three requests in that one walk. It
keeps no buffer of its own and never re-scans.

A read is `Bytes`, one packed block (`TCP.poll_buf`), and `feed_buf`
walks it where it lies: an uncons of a block nothing else holds
advances it in place. Where a state reads a run of bytes without a
transition -- a method, a target, a version, a field name, a key, a
value it skips, a body -- the run is counted and cut from the read
whole, so the target, the body and the key of a request that arrived in
one read are views of it, not bytes rebuilt; every other byte is one
step of the machine. `feed` is the same machine a byte at a time over a
list, the reference `feed_buf` is proved equal to. The runs are found
by `Bytes.span` where they lie: a skipped value with its spaces is one
span of [32, 127), a name is spans of lowercase letters with the class
test on the byte between them, and only a name as long as one the
engine knows is lowercased and looked up. A move goes on from where the
one before it landed, so one move takes a field line whole. Each of
these is proven to land where stepping its bytes does (`lem.rx.in`,
`lem.nm`, `lem.adv`, `fld_name`), on base's U32 order lemmas.

That shape is not a workaround. Bend's loops cannot exit early — a
recursive call has to shrink a matched argument — so a machine that
stopped at the blank line would still have to walk the rest of the
buffer rebuilding a dead state. So the machine never stops: completing
a message emits it and rolls straight into the next one, which is what
a pipelining parser should do anyway.

Every byte is first classed as the RFC's grammar sees it (a space, a
tab, a line end, a colon, a comma, a digit, a token byte, any other
visible byte, a control), and every state has a row only for the
classes it can carry. A field name is kept as its bytes, lowercased at
its colon, and looked up there in a table of the names this engine
acts on by comparing those bytes, block against block: it once went by a 32-bit
FNV-1a hash of them, and `x-v5fged` hashed to Content-Length's value
and was framed as one. The value scanner is chosen by the field: a
Content-Length accumulates digits, Connection and Upgrade are read as
comma lists of tokens, and every other value takes the scanner that
does no work per byte.

What it accepts is deliberately small, because a framing disagreement
is how requests get smuggled. HTTP/1.1 with exactly one Host, or
HTTP/1.0 with at most one. A body framed one way: a Content-Length, all
digits (refused at the digit that crosses the body cap, so it cannot
wrap) and the same wherever it is repeated; or a Transfer-Encoding
whose value is `chunked`, exactly (case aside), once, and nothing else
-- `chunked `, `xchunked`, `chunked, identity`, a second
Transfer-Encoding, one with a Content-Length in either order (CL.TE,
TE.CL), and one in HTTP/1.0 (RFC 9112 6.1: faulty framing) are each a
`400` that closes. Any other coding is refused the same way rather than
with a 501: it is a framing this reader will not guess at. A space
before a colon, a folded line, a line with no colon, a bare LF, a
control byte in a value or in the target are each a `400`. Empty lines
before a request line are skipped (RFC 9112 2.2), and a query is no
part of the path a request routes by. `Bad{}` is never left.

A chunked body is read by RFC 9112 7.1's grammar, a byte at a time, as
the table of it: a size in hex (either case, leading zeros allowed),
extensions (`;name`, `;name=token`, `;name="quoted \" string"`, with
the BWS the grammar allows around `;` and `=`) read and dropped, CRLF
after every line and after every chunk's data (a bare LF is refused),
the last chunk, and a trailer whose lines are read by the head's own
field-line grammar and dropped. It is bounded by one budget of
`body.cap()`: every byte of a chunk line before its CR and every byte
of data is paid from it, and a byte that would leave less than the
chunk still needs is refused where it stands -- so a size is refused at
the digit that takes it past what is left (and never wraps), an
extension can never outgrow the body, and a body decodes to at most
1 MiB. Only the decoded bytes are held; the trailer is a head's field
lines again and runs under the head's budget (`--head-ms`, 16 KiB). A
chunk's data is cut from a read whole, as a Content-Length body is, and
`/echo` answers the decoded body with a Content-Length.

HTTP/1.0 is answered with an HTTP/1.1 status line (RFC 9112 2.5 lets a
server) and, unless it asked to keep alive (`Connection: keep-alive`,
and no `close`), with `connection: close`, after which nothing more is
read (RFC 9112 9.3). An Upgrade in an HTTP/1.0 request is not one (RFC
9110 7.8), so `/ws` answers it with the 426.

What a read's requests earn goes out in order, and a request that ends
what the connection reads is the last one served from it: after a
`Connection: close` (anywhere in its list), a `/events` stream or a
`101`, nothing further is answered as HTTP. A broken grammar later in a
read still sends the replies owed before it, then the `400`, then
closes. The reply that ends a connection says `connection: close`.
After a `101` the bytes that followed the upgrade in the same read go
to the frame reader, and their replies leave with the `101`.

`conn` is bounded by fuel rather than `@unsafe`, so a peer that dribbles
bytes forever runs it out and is dropped. The accept loop is the one
`@unsafe` def, as in `demos/io_http_server`.

## Configuration, routes, files

The binary reads its arguments with the same shape as it reads a
request: a state fed one argument at a time, a step that does not
recurse, and a refusal (`IO.die`) for anything it does not know.
`--port N`, `--root DIR`, `--idle-ms N`, `--head-ms N`, `--max-conns
N`, `--grace-ms N`, `--shared` and `--log` are the settings.

The route table is data: a list of `Route{path, prefix, act}` built
once from the configuration and shared by every connection, walked
first match wins. Without a root it is `/health`, `/echo`, `/events`
and `/`; with one, `/` becomes a prefix route to `Files{}` and every
path the fixed routes leave is a file under the root, `/` itself being
`index.html`. Because the table is a value, LAWS.bend pins what it
answers and that no two entries claim one path, and the checker
refuses the build when someone adds a route that shadows another.

A file's name is the request path (`fnames.of`): its bytes refused if
any is a control byte, split on `/`, normalised (`.` dropped, `..`
climbing, a climb out of the root refused rather than clamped, because
a clamped path is a path someone will probe), and then every segment
checked again for what may reach the file system: some bytes, all
printable ASCII other than `/` and `\`, and no dotfile, so `/.env` and
`/.git/config` are a 404. Percent escapes are not decoded, so an
escaped `..` names a file that does not exist rather than a climb.

A path of plain names -- a `/`, then names of printable bytes, none
empty and none starting with a `.` -- is how almost every request asks,
and it is read where it lies: one walk over its bytes (`fast`) says it
is one, the file is the path after its `/` (a view of the target), and
the type is the bytes after its last `.`. Any other path goes through
`fnames.of`'s byte lists. `page_is_spec` says the two are one function
of the target, for every target, so `path_safe` and every law of
`fnames.of` is a law of the code that runs.

The name is opened by `File.get_under(root, path, small)`
(`bend2/effs/file_open_under.{c,js}`), which is `File.open_under` and
its `fstat` in one effect, and for a file under `small` (16 KiB) its
read and close too: a small file is one effect, and the loop's size,
read and close of it cost none. On Linux 5.6 and later the path is
resolved in one `openat2` under `RESOLVE_BENEATH | RESOLVE_NO_SYMLINKS`,
after the walk's own refusals by shape (an empty, `.` or `..` part);
elsewhere, or where a sandbox refuses `openat2`, it is an `openat` per
component with `O_NOFOLLOW`. Either way a symbolic link anywhere under
the root, to a file or to a directory, is refused rather than followed
out of it, and the end must be a regular file, so a directory or a FIFO
is a miss. The root itself is the operator's and is opened as given;
its descriptor is kept for up to a second, so a root swapped by a
deploy is seen within one. `wire/conform.bend` drives both ways through
a file, a missing one, a link, a link to a directory, a directory, a
climb and a dotfile (which the effect opens: refusing it is the
engine's).

What `File.get_under` read of a small file it keeps, per thread, by
root and path, and answers again for a second without a syscall, as
nginx's `open_file_cache` answers within its valid time; past the
second the file is opened again, and its bytes are kept when its inode,
size and mtime are unchanged and read again when not. It holds at most
256 files under 16 KiB (4 MiB a thread), and never a refusal.
`wire/world.bend` models it and proves it bounded (`memo_bounded`) and
its answers the file system's when they were read (`memo_answers`,
`memo_keeps`); conform's `fget.memo` rewrites a file it holds and sees
the new size after the second.

The type comes from the extension, by a table whose rows keep the head
a 200 of that type starts with; `file_head_is_built` says it is the
head `mime.pre` builds from the type's name, and that a request asking
nothing of the file gets all of it after the head `cond.bend`'s
`hd.full.is` spells out piece by piece.

### Conditional and range requests

A file's reply is decided by `cond.bend` from the request's fields and
the size and mtime the open file reports (RFC 9110 8.8, 13, 14): the
loop's `~fhead` hook returns the head and which of the file's bytes
follow it (`L.Fr{hd, off, len}`), and the loop sends that part by
sendfile from `off`, or, for a small file, slices it out of the bytes
it read, the head in the same send.

- Validators: every 200, 206 and 304 carries `last-modified` (the
  mtime as an IMF-fixdate) and `etag`, nginx's `"<mtime hex>-<size
  hex>"`, so a cache that holds one of nginx's tags keeps matching. It
  is sent strong, as nginx sends it, but it is a weak validator in
  truth (two writes in one second at one size share it): If-None-Match
  compares it weakly, If-Match and If-Range strongly (RFC 9110 8.8.3).
- Preconditions, in RFC 9110 13.2.2's order: If-Match (412 unless it
  names the tag, or `*`), else If-Unmodified-Since (412 if the file
  changed after it); If-None-Match (304 if it names the tag, or `*`),
  else If-Modified-Since (304 if the file has not changed since). A 304
  is the status line, `last-modified`, `etag` and `connection`, and no
  byte of the file. A date is read in any of the three forms RFC 9110
  5.6.7 asks a recipient to accept; one that does not read is as if the
  field were absent.
- Range: one `bytes=` range-spec the file satisfies is a 206 of exactly
  those bytes with `content-range: bytes a-b/n`; none satisfiable is a
  416 with `content-range: bytes */n`; a Range that is not RFC 9110
  14.1.1's grammar is ignored; If-Range lets it through only when it is
  the file's tag (strongly) or exactly its Last-Modified. A 200 of a
  file says `accept-ranges: bytes`. An empty file ignores Range.

The laws (LAWS.bend, "Conditional and range requests") are proven for
every size and mtime: `date_round_trip` (date.read of date.fmt is the
time back, for every year IMF-fixdate's four digits hold), the calendar
by vectors (1994, the leap days of 2000 and 2024, 2100 not being one,
the epoch, the last 32-bit second), the three date forms, the heads byte
for byte (`head_vectors`) and built in place equal to their pieces
(`same_head_is_built`, `part_head_is_built`), `not_modified_no_body`,
`inm_over_ims`, `tag_hit_not_modified`, `ims_echo` (a client that sends
back the Last-Modified it got gets a 304), the unreadable dates ignored,
`part_in_file` (every range served is in the file, so Content-Range
never names a byte the file lacks), the range forms and vectors, and
`range_wire`: in the world model, a GET the fields decide is the range
a to b puts on the wire the 206 head naming it and then exactly the
file's bytes a to b. `mutants.py` breaks each of these (a body after a
304, a Content-Length on it, If-Modified-Since read despite
If-None-Match, a range one byte too long, Content-Range off by one, the
weekday a day late, every fourth year a leap year, ...) and each is
refused.

Where it differs from nginx (1.24, `sendfile on`, defaults), with the
same files, compared status line and header names on 62 requests:

| request | nginx | here | why |
|---|---|---|---|
| If-Modified-Since later than the mtime | 200 | 304 | nginx's default `if_modified_since exact`; RFC 9110 13.1.3 says "earlier or equal" |
| If-None-Match matching, If-Modified-Since earlier | 200 | 304 | RFC 9110 13.1.3: with If-None-Match present, If-Modified-Since is not evaluated |
| If-Unmodified-Since that is not a date | 412 | 200 | RFC 9110 13.1.4: an invalid date is ignored |
| `bytes=5-3`, `bytes=abc` | 416 | 200 | RFC 9110 14.2: a Range that does not parse is ignored |
| `bytes=0 - 5` | 206 | 200 | whitespace inside a range-spec is not the grammar |
| `bytes=0-1,` | 416 | 206 | an empty list element is allowed (RFC 9110 5.6.1) |
| `bytes=0-1,5-6` | 206 multipart/byteranges | 200 | no multipart replies here; RFC 9110 14.2 lets a server ignore Range |
| 412, 416 bodies | HTML, `Requested Range Not Satisfiable` | a line of text/plain, `Range Not Satisfiable` | RFC 9110's reason phrase |
| `.txt` | application/octet-stream | text/plain | the engine's type table (as before) |
| `server`, `date` | sent | not sent | as before |

Everything else agrees: the status, the header set of the 200, 206, 304,
412 and 416 (the 206 without `accept-ranges`, the 304 with only the
validators and `connection`, as nginx sends them), the Content-Range and
the bytes.

On one core, against nginx with one worker (`sendfile on`, no
`open_file_cache`) under `wrk -t2 -c32` on loopback, a 4 KiB file went
from 20.5k to 40.8k req/s (nginx 37.4k): the one effect and the path
kept as bytes 25.8k, the memo 33.7k, the path read where it lies 39-41k.
At `-c256` it is 41.3k against 37.5k, and a 1 MiB file 2.35k against
1.69k.

A reply is a list of segments: bytes as they are, or a file to write
when the reply is written. Fixed routes stay pure and cost what they
cost before; only a file route puts IO on the path, and only for its
own request, so a pipelined batch mixing both still answers in order.
`send.segs` writes them in order: fixed replies wait on one block and
go out with whatever comes next; a file goes out as its head, sized by
`fstat` of the descriptor it opened, then in blocks of at most 64 KiB,
each read only after the socket took the one before. A file costs one
block however large it is and however many of them a pipelined batch
asks for: 32 clients fetching a 4 MiB file at once, or 100 pipelined
GETs of a 1 MiB file, leave the server's peak resident set at 5.4 MB,
where reading whole files first reached 200 MB and 350 MB (2.9 GB when
a byte was a list cell); the pipelined batch also went from 335 to
1,365 MB/s on loopback.
The body is exactly the length its head promised: a short read is read
on, and a file that ends early (it shrank while being written) ends the
connection, since nothing after it could be framed.

`HEAD` answers with the head of what `GET` would have sent, cut at the
blank line by a scanner rather than rebuilt, so the two can never
disagree about a length or a type; LAWS.bend says the scanner and the
head builder agree on the fixed replies. A `405` names the methods that
would have worked.

## Time and size

Every read has a deadline. `TCP.poll_buf` is `TCP.poll` carrying
a `Bytes` (`bend2/effs/tcp_poll_buf.{c,js}`, declared beside it): a recv
is tried before any park, so a socket with data waiting costs no pass;
one with nothing parks on the socket and on the clock, whichever fires
first. A peer silent for `--idle-ms` (10 s by default), mid-head or
between requests, is dropped; one that pauses for less keeps its
connection. `tests/io/tcp_poll_bytes.bend` and `tcp_recv_bytes.bend`
pin the two byte effects the way `tcp_poll.bend` pins the text one.

A read that finishes no message is a wait, not a write, and a
connection gets sixty-four of them in a row: a head arrives in one or
two chunks, and one dribbled a byte at a time inside the idle time is
not a client. That budget is a `Nat` beside the fuel, so the loop still
terminates by Bend's own rule. The same change stopped the engine
sending an empty reply after every partial head, a syscall per chunk it
never needed.

A head that announces a body past 1 MiB is refused as it completes,
before a byte of the body is read, so an announced length is never a
way to make the engine allocate. It is refused as `Bad{}`, a `400` and
a close, which keeps the parser's absorbing state the one the laws
already cover.

The idle time bounds each wait; nothing in it bounded a head, which a
peer could dribble a byte per wait for sixty-four waits, ten minutes a
slot. So a head has budgets of its own. Its clock starts at the read
that begins it and `--head-ms` (10 s by default) ends it: each read
that continues it waits for the idle time or what is left of the
head's time, whichever is less, and one out of time is dropped as a
silent peer is. Its bytes are counted after the read it began in, and
past 16 KiB it is a `431` and a close, so every head under 16 KiB is
read and none past 32 KiB is. The watch rides beside the plan in the
connection loop (`Hw`: no head, a head just begun, a head since t0
with n bytes) and costs nothing on a read that ends at a message
boundary. A request target past 8 KiB is a `414`. `LAWS.bend` says the
target cap holds at its edge for any bytes, and that a head in
progress keeps the clock it started with.

Every send has a deadline too. `TCP.send_buf_poll`
(`bend2/effs/tcp_send_buf_poll.{c,js}`, declared beside `TCP.send_buf`)
is the send with the idle time as the longest it may go without
progress; each write that moves bytes starts the wait over. A peer
that asks for a file and never reads used to hold its slot, and its
computation, for good; now it is let go after the idle time.

Replies that wait in one block for the send, the fixed ones, go out
once the block reaches 1 MiB, before the next reply is taken, in order
and unchanged; files already go out a block at a time. `batch_under`
in `LAWS.bend` says what stays waiting is always below the cap, so a
pipelined read holds at most the cap and the one reply that crossed it.

## TLS

`--tls-cert` and `--tls-key` make the listener a TLS listener, and
**nothing else in the server changes**. The effects that carry bytes --
`TCP.recv_bytes`, `TCP.send_bytes`, `TCP.poll_bytes`, `TCP.accept`,
`Socket.close` -- go through an `IoWire` in `bend2/comp.ts`, four
function pointers that are NULL for a plain socket and cost one branch
the processor predicts. `bend2/effs/tls_listen.c` installs an
implementation of it over OpenSSL and nothing above knows the
difference: the engine's connection loop, the parser, the router and
the WebSocket framing are the same code on both wires.

A TLS read may need to write and a write may need to read, so the wire
answers with the direction the socket has to become ready in, and the
loop parks on that rather than on the operation. The handshake is not
done at accept: it runs inside the first read or write, driven by the
same park, so a slow or hostile handshake costs a parked computation
rather than a blocked server, and the connection's idle deadline
already covers it. A closing socket sends its `close_notify` first, so
a peer can tell an orderly end from a cut connection; one whose session
failed sends nothing more. Every `SSL_*` call starts from a clear error
queue and errno, so one connection's error is never read as another's.
Renegotiation is off, a peer's missing `close_notify` is an end rather
than an error, idle sessions give their buffers back, and TLS 1.2 is
held to ECDHE with AEAD ciphers. A socket whose session could not be
made is refused rather than served in the clear, and `Listener.close`
takes the listener's context with it.

ALPN advertises `http/1.1` (h2 goes in front of it when there is an h2
to agree to). Minimum version is TLS 1.2; here it negotiates TLS 1.3.

`check.c` built with `-DCHECK_TLS` swaps its own socket calls for a
session and runs **the same cases over the encrypted wire** (97 with
`--files --ws --log --root`): one suite, two transports. All pass on
both, the 256-byte binary round trip and the chunked bodies included. TLS costs about a tenth at
pipeline 8 (77,368 against 85,853 req/s through the same client) and
nothing measurable at pipeline 1, where the client is the ceiling.

A program that never imports the effect never includes
`<openssl/ssl.h>`, and `bend2/main.ts` links `-lssl -lcrypto` only for
the ones that do -- the same content-driven rule it already used for
X11 and ALSA. The plain binary still links libc and libm alone.

## WebSocket

`/ws` is a WebSocket echo. The request reader learned the three headers
the upgrade needs -- `Upgrade` by the hash of its value, `Connection:
Upgrade` beside `Connection: close`, `Sec-WebSocket-Key` as the bytes
it came in -- and a message that carried all three becomes a `101`
whose accept key is `base64(sha1(key ++ GUID))`, computed by the Bend
in `sha1.bend` and `b64.bend` once per handshake. After the `101` the
connection reads frames instead of requests. A key that is not 24
characters of base64 (22 and `==`) is a `400` before it is hashed, and
a `Sec-WebSocket-Version` other than 13 gets the `426`, naming 13. The
key and the version are read without the whitespace at either end
(RFC 9110 5.5): a padded key upgrades and ` 13 ` is 13, while `1 3`,
whose space is inside the value, is not. Until the whole-input law
below was written the reader kept a key's trailing whitespace, so a
valid padded upgrade got a 400, and dropped every space in a version.

`ws.bend` is the frame reader and writer (RFC 6455). The reader has the
request reader's shape, one structural walk with its state in one node,
and the same chunking law: `ws_feed_split` says a frame split across
reads parses where the whole would have, proved by the same induction.
What it accepts is deliberately small: client frames are masked or the
connection is failed with 1002, as the RFC requires; fragments and
reserved bits are refused; a payload past 1 MiB is refused at the byte
that announces it, before an eight-byte length could wrap; a control
frame past 125 bytes and a length in more bytes than it needed are
refused. Text and binary come back as they came, a ping is answered
with a pong, a close with a close and the end of the connection. A
close code no peer may send (0-999, 1004-1006, 1015-2999, past 4999)
is answered 1002, and text or a close reason that is not UTF-8 is
answered 1007: the validator is a walk over the payload with the next
continuation byte's range in its state, so an overlong form, a
surrogate and a code point past 10FFFF are each refused at their byte.

The reader has two entries over one machine: `Ws.feed` walks a list,
and is the spec; `Ws.feed_buf` walks a `Bytes` by uncons, which moves
an unshared buffer's view in place, and is what a connection reading
`TCP.poll_buf` calls. `ws_feed_buf` says the two are one function of
the bytes, for every buffer and state; `ws_feed_buf_split` follows from
it, `ws_feed_split` and `Bytes.to_list_append`. The mask is one word
turned a byte left per payload byte, a payload is one block (prepended
into, reversed once), and a reply is one block: frame heads written in
front of the payloads, a read's replies appended in place.

Over 1 MB of masked 1000-byte frames the reader went from 235 ms (a
four-cell mask list rebuilt per byte, a list per payload) to 37 ms on a
list already built and 67 ms on `Bytes`; an uncons costs more than a
cons cell, but a connection that reads `Bytes` would pay 82 ms to walk
the list reader over `Bytes.to_list`, and 85 ms through `Bytes.get`
by index. Reading and answering the same stream went from 250 ms to
98 ms.

The laws pin a masked text frame and an empty ping reading back on
both paths, whole and cut after the mask; the refusals; the least
length each extended form reads; the bytes the writer produces for a
short frame, a two-byte length and a close code; the close codes at
every edge against the rule stated on its own; the close and text
replies; and sixteen UTF-8 vectors on which the validator and a
decode-then-check reference in LAWS.bend both say what they are.

`check.c` under `--ws` does the handshake with RFC 6455's own key and
expects the RFC's accept value, then the echo, the pong, a 300-byte
binary frame with its two-byte length, a frame split across two writes,
the close, the unmasked frame, and the `426` a plain `GET /ws` earns;
then, each on its own connection, a 126-byte ping and lengths in the
wrong form (1002), eleven reserved or out-of-range close codes (1002)
and six valid ones (echoed), an overlong form, a surrogate and a cut
character in text and a bad close reason (1007), and UTF-8 text in
three and four bytes echoed.

## The log

`--log` writes one line per request to stderr and nowhere else: what
was asked, the status it got, and how many bytes went back.

    GET /health 200 106
    GET /nope 404 104
    ? /echo 405 133
    HEAD /a.txt 200 103

No timestamp, and no effect for one: whatever supervises the process
already stamps and collects what it writes, and a clock effect that
exists to duplicate that would not have earned its place. The method
is a hash by the time a reply exists, so the two this engine serves
are named and anything else is `?`.

A log line is a `Note` segment the router puts before the reply's
segments; `send.segs`, which already resolves segments in IO, prints
it against the bytes the next segment resolves to. So a pipelined batch
logs in the order its requests arrived, a file logs its head and the
length that head promised, and a `HEAD` logs the head it actually sent. It is off
by default because a line per request is a syscall per request:
69,819 req/s becomes 52,187 with it on.

## Many, and stopping

The connection limit is a channel. `Chan.new(Unit, n)` has room for n
slots; a connection takes one (`Chan.send`) before it is served and
gives it back (`Chan.recv`) when it ends; when every slot is taken the
accept loop parks on the send, and the kernel's backlog holds what
arrives meanwhile. No counter, no lock, no new effect: the semaphore
the runtime already had, used as one. `--max-conns` sets it, 1024 by
default.

Stopping is `SIGTERM`. The accept loop reads through `TCP.accept_poll`
(`TCP.accept` with a deadline, `bend2/effs/tcp_accept_poll.{c,js}`),
so every 250 ms of no arrivals it looks up, and after every arrival
too, and asks `IO.signal_pending(15)` (`bend2/effs/signal_pending.{c,js}`:
the first ask installs a handler that only sets a flag, with
`SA_RESTART` so no effect in flight is failed by the signal). The
first ask is made at startup: asked only when arrivals paused, a
server under steady load never saw the signal, and one loaded from
boot had no handler and died without draining. On a stop it closes the
listener, so new connections are refused at once; the ones open finish
what they are doing; and the process ends when every slot has come
back -- the loop refills the semaphore -- or when `--grace-ms` is up,
whichever is first. Two effects, both the size of the ones beside them,
and both generic: any long-running Bend program that has to be stopped
by its supervisor needs exactly these.

Only a listener that is no longer one ends the loop. `accept(2)` also
fails for one connection (reset before it was taken, a network error
handed over with it) and for a passing shortage; those are retried.
Out of descriptors, the connection at the head of the queue is taken
on a spare descriptor and closed, so it leaves the backlog instead of
waking the loop forever; out of buffers or memory, the loop steps back
20 ms. Before, 1017 idle connections against `ulimit -n 1024` stopped
the server for good. Accepted sockets are non-blocking and
close-on-exec from birth (`accept4`) and have Nagle off.

## The laws

`feed_split` is the one that matters: `feed(a ++ b, p)` equals
`feed(b, feed(a, p))`. Chunking does not change the parse, however TCP
decides to split a message. It is also what licenses keeping no buffer.

`feed_buf_is_feed` says the walk the engine runs is `feed` on the
read's bytes, for every read and every reader state: the runs it cuts,
the bodies it takes at their length and the values it skips land where
stepping their bytes one at a time would have. So every law of `feed`
is a law of the engine, and `feed_buf_split` is `feed_split` on
blocks. Each piece of the walk was checked by breaking it -- a target
run that swallows its space, a skipped value that runs over its CR, a
body cut one byte short, the bytes after an upgrade dropped, a name
entered from the wrong state, a name taken for the first field it is
compared with -- and the checker refuses every one.

`bad_absorbs` and `bad_feeds` say no byte moves the reader out of
`Bad{}` — without them a smuggled request could follow a refused one on
the same connection and be served.

The framing laws hold the reader to `spec.bend`, a reference written
from RFC 9110's character sets and field names the obvious way.
`cls_is_spec` and `lower_is_spec` say the reader classes and lowercases
all 256 bytes as the reference does. `field_by_bytes` says, for every
name, that the field the reader takes it for is the table entry spelled
with exactly its bytes, or none. Then, for every message state:
`te_chunked_only` (a Transfer-Encoding whose value is not exactly
chunked is refused at its CR), `te_once` (so is a second one),
`te_cl_refused` and `te_10_refused` (a head framed two ways, or a
Transfer-Encoding in HTTP/1.0, is refused at its blank line),
`chunk_size_capped` (a HEXDIG that takes the size past the budget is
refused where it stands, whatever the size so far), `chunk_ext_capped`
(so is any other byte of a chunk line the budget can no longer pay
for), `chunk_bare_lf` (a LF anywhere in a chunked body's framing but
right after its CR is refused), `name_refuses`,
`line_refuses`, `clen_refuses`, `target_refuses`, `value_refuses` and
`conn_refuses` (each part of a head refuses every byte class the grammar
has no place for there: a space before a colon, a fold, a sign in a
length, a control in the target), `clen_disagree` (two lengths that
differ are refused), `host_once` (one Host in HTTP/1.1, at most one in
HTTP/1.0) and `rest_feeds` (after an upgrade
nothing is read as HTTP: the rest of the read is kept whole for the
frame reader). `lows_is_spec` says a name is lowercased at its colon
as the reference lowercases each of its bytes. Fifty-two closed laws run the real reader
on the smuggling inputs -- CL.TE, TE.CL, TE.TE dressed four ways, a
chunked body broken seven ways -- and on HTTP/1.0 with and without
keep-alive and chunked bodies with extensions and trailers, one of them
cut at every awkward place a read could end (inside the size, an
extension, a CRLF, the trailer) and one fed a byte per read;
`feed_split` carries each to every chunking.
Every one of the review's mutations of the reader -- a target refused,
a Transfer-Encoding accepted, a body one byte short, a non-digit length
accepted, a name constant changed -- and six more of the same kind
(a fold, a disagreeing length or a missing Host accepted, a space
before a colon, a length that wraps, names matched by their first byte)
is rejected by the checker.

### The reader is the framing

Those laws hold the reader to the RFC one rule at a time; none says
the rules add up. `frame_sim` does, for every input at once. `spec.bend`
has a second reference, `frame()`: a whole input read the way RFC 9112
writes it, sharing no code with the reader. It gathers a line's bytes
to its CR LF and reads the line whole -- a request line split at its
spaces into a method, a target and `HTTP/1.1` or `HTTP/1.0`, a field
line split at its colon into a name and a value read by what the name
is (a length as a decimal, a list at its commas and whitespace, a key
or a version trimmed of OWS, a coding as it came) -- judges a head at
its empty line (its Hosts, its one framing) and counts a body off by
its length, or reads a chunked body by RFC 9112 7.1's grammar, which is
regular and is written as its table: where in the grammar a byte
arrives (`ASize`, `AName`, `AQuoted`, `ATrail`, ... one per rule) and
where it takes the body. A line the input stops inside is read as far
as it goes. It says which requests the
input holds, oldest first, and how it ends: `Open` with the bytes since
the last request, `Refused`, or `Upgraded` with what followed.

    law frame_sim:
      for +bs: List<&2, U32>
      agree(Eng.feed(bs, Eng.p.new()), Spec.frame(bs))

`agree` says the reader fed `bs` from fresh has completed exactly the
requests `frame(bs)` finds, field for field and in order, and then: if
the framing is open, the reader has not refused and *is*, state for
state, a fresh reader holding those requests fed the bytes since the
last one -- so it restarts exactly where the RFC says a request ends;
if the framing refuses, the reader has refused; if the last request
upgraded, the reader holds exactly the bytes that followed it.
`frame_sim_buf` carries it to `feed_buf`, the walk the server runs,
and `frame_sim_reads` to a connection's reads fed one after another
however TCP cut them. `cls_every` and `lower_every` say the reader and
the reference class and lowercase every U32 alike, not only the 256
bytes.

Each request carries its head for whoever passes it on (`Eng.req.hd`,
an `Eng.Hd{meth, v10, fields, conn}`): the method's bytes, whether it
is HTTP/1.0, every field the reader passes on (the Host and each one it
does not act on) as a `Wr.Field{name, value}` of `wire/reader.bend`,
the name lowercased and the value as it came between the colon and the
line's end, whitespace and all, in the order they came, and the members
of every Connection, lowercased. `hd_framed` says these are `frame()`'s
heads, read by `spec.bend`'s views of the lines. (A head still in
progress: `Eng.p.fields(p)`, newest first.)

The proof is a simulation. `REL` says where the reader is given where
`frame()`'s walk is -- inside a line, a line-start reader fed the line
so far; at a line's CR, the state after it with pending fields that
look like the spec's head; in a body, the same count and bytes; after
an upgrade, the same bytes; refused, Bad -- and, while open, that the
reader is a fresh one fed the bytes since the last request. `STEP`
moves both by one byte and keeps `REL`; `END` reads the agreement off
it; induction on the input does the rest. Inside a line, `line.req`
and `line.field` prove that the reader's state after any line prefix
is the one the spec's view of that prefix names, token by token: a
span of bytes a token may hold is one the reader stays on (`RS`), and
the byte that stops it is stepped as the spec reads it. PV compares
the reader's pending fields with the spec's head, forgetting only how
the reader stores "no upgrade field seen"; it carries what the request
line and the framing fields said (HTTP/1.0, keep-alive, chunked), and
the head's end, a Transfer-Encoding's CR and an emitted request's
`close` are each decided through it, so the two sides' decisions are
one decision. In a chunked body `REL` holds the reader at the spec's
place in the grammar with the same size, body so far and budget:
`at.eng` and `go.eng` name the reader's place and move for each of the
spec's, `tbl` says the two tables agree row by row (228 rows, each a
computation), and `xk.is` that both sides tell the same bytes apart. The
budget's arithmetic is the same U32 terms on both sides, so a case on
each comparison is all it needs. It is about 6,300 lines of PROOF.bend,
2,300 of them the generated byte bridges.

It binds both sides. With every rule-by-rule framing law deleted and
only `frame_sim` and what its proof uses kept, each of these breaks is
refused, and on the input named the reader and `frame()` disagree:

| broken | where the proof stops | input | reader | frame() |
|---|---|---|---|---|
| obs-fold accepted | `line.field.first` | a line after `X: a` starting with a space | 1 request | refused |
| body one byte short | `HEAD.z` | `Content-Length: 2`, `hi` | body `h` | body `hi` |
| a CL list accepted | `DIG.k` | `Content-Length: 5, 5` | 1 request | refused |
| names matched on a prefix | `scan_is` | `Content-Lengthx: 5`, `hello` | body `hello` | no body |
| a lone CR before a request | `STEP.blank.k` | `\rGET / ...` | 1 request | refused |
| upgrade leftover dropped | `STEP.up` | an upgrade, then `ab` | keeps nothing | keeps `ab` |
| spec: two lengths that differ | `CR.clen.l` | `Content-Length: 3`, `: 5` | refused | 1 request |
| spec: no Host | `HEAD.l` | `GET / HTTP/1.1`, empty line | refused | 1 request |

`mutants.py` keeps six more of these standing, each run against a
scratch copy that keeps only `frame_sim`'s family (186 laws and their
proofs removed) and checks clean before it is broken:

| broken | where the proof stops |
|---|---|
| TE.CL: a Transfer-Encoding with a Content-Length read as chunked | `bok` |
| a chunk-size that wraps: no digit checked against the budget | `APPLY` |
| a bare LF ending a chunk line | `tbl` |
| TE.TE: anything that starts `chunked` is chunked | `te.ok.eq` |
| HTTP/1.0 kept alive without asking | `s.req` |
| spec: a chunk's data may end in a bare LF | `tbl` |

What it does not say. The walk is over bytes; `frame_sim` says nothing
of what the routes, the files or the frame reader then do with the
requests, and nothing of time (`--head-ms`, `--idle-ms`) or of the
limits the server enforces outside the reader (`--head` for a long
head, the 414 for a long target). `frame()` is the RFC for the part of
HTTP/1.1 and HTTP/1.0 this engine accepts, and where the RFC lets a
server choose, it chose what the engine does: a bare LF or CR is
refused, not read as a line end; a coding but chunked, whitespace
after `chunked`, a Content-Length list, a length past 1 MiB and a fold
are refused with the same 400; a chunked body's lines and data share
one budget of 1 MiB; and a line
the input stops inside is refused when a byte arrives that its token
cannot hold (a control in a target, a letter in a length, a digit that
takes a length past the cap), while a version, a field's name, a
second length and the Host count are judged whole, at their CR, colon
or empty line -- which is where the engine judges them. Those are
choices written into the reference and stated there, not derived.

The five `*_is_built` laws each say one written-out reply is byte for
byte what `reply()` returns for the arguments named beside it. Those
replies are literal byte arrays, because building a 106-byte reply out
of nine pieces cost more per request than parsing the request that
asked for it; nobody should read the numbers, and nobody has to, since
the checker refuses the engine the moment an edit makes one false.

`sha1.bend` and `b64.bend` are SHA-1 (RFC 3174) and base64 (RFC 4648)
in Bend, written for the reader rather than the clock (every shift is
a single-bit shift repeated) because they run once per WebSocket
handshake. Their test vectors are laws: the three SHA-1 vectors, the
seven base64 vectors, and RFC 6455's own accept-key example with the
two composed, all computed by the checker in about ten seconds; a
digest with one byte changed is rejected with both digests printed.

The route laws pin what the default table answers and what a table
with a root answers (`/health` still, `/` and everything else to the
files), that neither table has two entries for one path, and that an
empty table routes nothing. The two HEAD laws say the scanner that cuts
a reply at its blank line agrees, byte for byte, with the builder that
writes a head from a length. Four normaliser laws pin the paths that
matter: a climb from the root, a climb from under a real directory,
dots, and a climb that stays inside; two more hold for every path
after the first segment: a climb from the root is refused whatever
follows, and a climb right after a name cancels it. `path_safe` holds
for every request target: what `fnames.of` hands to the file system is
refused, or segments that keep a rule LAWS.bend states on its own (some
bytes, printable ASCII, no `/` or `\`, no dotfile or, with dotfiles
served, never `.` or `..`). `clean_refuses_control` says a target with
a control byte anywhere is never clean, and `unclean_names_nothing`
that an unclean target names no file.

Each law was checked by breaking it: a clamped climb, a clean()
that lets everything through, the segment guard removed, dotfiles
served, DEL forgotten as a control byte, a one-digit content-length, a
linefeed that escapes `Bad{}`, a `feed` that drops state at a chunk
boundary, a head one byte long, a climb claimed to resolve, and a
duplicate route are all rejected, with the two terms printed.

## The world

Every critical bug the review found was in the effects the connection
loop runs, not in anything a law spoke of: an accept loop that died on
EMFILE, a send with no deadline, buffering with no bound, SIGTERM
unseen. They were fixed and tested. This is how they became theorems.

The loops are written once, and since bend-wire (`wire/`) they are the
library's, not the engine's: `wire/loop.bend` holds them for every
protocol, `wire/world.bend` the model below and the laws, proven there
once over the protocol's hooks, and `wire/effects.bend` the real
instance. The engine hands the loop its planner and hooks (`main.bend`,
"The hooks"), `world.bend` here is the model at those hooks, and each
law below is wire's, stated for the engine and proven as an instance.
`conn`, `turn`, `send.segs` and everything
under them, and the accept loop's `accept.run`, take the monad and each
effect as template parameters: `~M`, `~pure`, `~bind`, the socket and
file types, `~rx` (`TCP.poll_buf`), `~tx` (`TCP.send_buf_poll`), `~clk`,
`~nap`, `~say`, `~fopen`, `~fsize`, `~fread`, `~fclose`; for the accept
loop `~lsn` (`TCP.accept_poll`), `~sig` and `~hand`. `start` and
`accept` instantiate them with `IO` and the effects themselves. A
template is substituted at compile time, so the server runs what it ran
before: callgrind counts 46,672 instructions per request at pipeline 8
against 46,711 before, and 54,058 against 54,093 at pipeline 1. The loop
answers the socket instead of closing it, so the caller closes it and
gives the slot back; `send.segs` takes no read effect, so it cannot
read; the `@unsafe` accept only starts `accept.run` again when its 2^20
turns are spent.

`world.bend` instantiates the same defs with the identity monad and a
pure world. The socket is the world: every effect already hands its
handle back, so the handle can carry a scripted peer -- reads that
arrive after a wait, stay silent or fail; sends it takes a piece at a
time, stalls on or resets; whether it takes everything once its script
is spent -- with a clock, the files under the root and every byte the
peer has taken. A mute peer (it has stopped: every read waits out its
time, every send with bytes to move fails) and a scripted listener
(arrivals, quiet ticks, failures with any code, a SIGTERM) complete it.

For every script and every state the loop can be in, `LAWS.bend` says:

- `end_is_last`, `stop_is_last`: a plan that ends the connection is its
  last act. After `End` the loop writes the segments and answers the
  socket, with nothing read and nothing more written; after `Stop`,
  nothing at all.
- `go_order`, `segs_wire`: a plan that reads on writes all its replies
  first, and at a peer that takes them they go out byte for byte, in
  the order of their segments, after whatever it already had.
- `fail_go`, `fail_ws`, `fail_feed`: a send that failed or stalled is
  the connection's last act on its socket, whether it carried a read's
  replies, a WebSocket's frames or a stream's event.
- `refuse_plan`, `refuse_conn`: when the requests a read completed all
  keep the connection and the grammar then broke, the connection writes
  every reply they are owed, in order, then the `400`, and ends; it
  reads nothing more, so no request after the refusal is consumed.
- `hold_fine`, `raw_fine`, `page_fine`: a writer that may still take
  replies holds a batch below `send.cap()` after any reply -- fixed, a
  missing file, a file of any size streamed in blocks -- whatever the
  peer does. So what is held unsent is at most the cap and one reply,
  or a file's head and one `page.chunk()` block.
- `head_capped`: a read that leaves a head in progress leaves it at
  most `head.cap()` bytes past the read it began in; past that it is a
  `431` and the end. With reads of at most `chunk()` bytes, a head held
  is at most `chunk()` + `head.cap()`, and a body at most `body.cap()`
  (the reader's cap). Held in all: 16 + 16 KiB of head, 1 MiB of body, 1
  MiB of batch, one reply.
- `head_expires`: a head whose `--head-ms` has run out is not read
  again; the turn ends the connection whatever the peer would send.
- `stall_ends`: at the mute peer the connection ends within three turns
  from any state: fuel past three changes nothing. Each of those turns
  lasts at most its deadline, by the contracts below.
- `accept_calm`, `accept_ends`: with no stop request and every accept
  failure one of the passing set (EMFILE, ECONNABORTED, ...), the accept
  loop runs every turn it is given; it ends only for a stop request or
  a code outside that set. The model lets accept fail with any code at
  any time, so this assumes nothing of `accept_poll`'s own sorting.
- `rx_model`, `tx_stalled`, `tx_served`, `fread_model`: the model keeps
  the contracts it assumes.

Each effect's contract is written beside it in `bend2/base.bend` and, as
a relation on what one call answers, in `world.bend` (`rx.ok`, `tx.ok`,
`lsn.ok`, `fopen.ok`, `fread.ok`). `wire/conform.bend` is the bridge to C: it
drives the real effects through their contracts' cases and judges what
they answer with those same relations, while `wire/conform.c` plays the peer
(silent, 100 ms late, ten bytes to a read of four, a FIN, a reset, a
16 KiB window it drains every 2 ms, a reader that stops, a reset before
a send, 80 connections at once against 48 descriptors) and checks its
own side: all 16 MiB of the crawl arrived though the send outlived its
300 ms deadline six times over, the stall gave up short, and 40 of the
80 were shed while the listener went on to serve the last. 17 and 5
cases pass, on each run in CI.

`mutants.py` breaks the loop (now `wire/loop.bend`) nine ways -- no head deadline, no batch
cap, a reply after close, a queued reply skipped on refusal, the accept
loop out on EMFILE, a reply before the batch it follows, a WebSocket
that reads on after its send failed, a silent peer waited on again, an
emptied file's head left uncapped -- and `PROOF.bend` refuses every
one, in CI too. It then breaks the framing six ways against `frame_sim`
alone (above, "The reader is the framing"): fifteen of fifteen killed.

Three of those nine were bugs, found by writing the proofs: `turn.ws`
read on after a failed send, so a peer that sent pings and never read
held its connection for the whole fuel; `pump.left` left an emptied
file's head in the batch without the cap's test, so a pipelined read of
empty files grew it by a head each; and the accept loop ended on any
accept failure, trusting `accept_poll` to have absorbed the passing
ones. What stays trusted: the effects themselves, in the cases
`conform` does not try; the parser's own bound on a body; `IO.bind`,
`IO.pure` and the event loop that runs them; and that the template
substitution the compiler does is the one the checker saw.

## The control and the checks

`control.c` is the same engine written the way a C server is written:
one epoll loop, the same modes, the same byte-at-a-time transitions,
the same routes, byte-identical replies, the same policy. `fuzz.c`
holds it to that: the same bytes, cut at the same random points and
sent with a pause between the cuts, go to both, and what comes back
has to be identical, closes included -- one to four messages a round,
valid or mutated in the ways a reader has to survive (a truncation, a
byte flipped, HTTP/1.0 with and without keep-alive, a version that is
neither, a length that is not all digits or is past the cap, fields in
odd case, bodies of arbitrary bytes, chunked bodies -- sizes in either
case with leading zeros, extensions with tokens, quoted strings and
BWS, trailers -- and each of those broken, and the Transfer-Encoding
smuggling vectors: with a length either way round, `chunked `,
`xchunked`, `chunked, identity`, two of them). A control broken in any
of four ways the engine is not (TE.CL accepted, HTTP/1.0 kept alive
unasked, a chunk's data ended by a bare LF, anything starting `chunked`
taken as chunked) shows a difference within 300 rounds. Its first run
found two faults, both in the C:
the control closed the moment it had parsed `Connection: close`,
before the head had ended, and its 400 dropped its body when the
broken message had been a HEAD. With those fixed it runs thousands of
rounds without a difference. `check.c`
runs its behavioural cases against either: forty-nine for any server
(chunked bodies decoded, cut at awkward places and with extensions and
a trailer; HTTP/1.0 closed, and kept open when it asks; twenty-five
framing vectors refused, TE.CL, CL.TE and TE.TE among them), the last
of which reads the server's CPU when given its pid; nine more
for static files when the server was started with `--root` on the
fixture directory and the check with `--files`; eight more with
`--root=DIR`, the server's root, where the check writes its own
fixtures: a symbolic link to `/etc/passwd` and one to `/etc`, a
dotfile, a 4 MiB file served byte for byte, the same to 32 clients at
once and a 1 MiB one to 100 pipelined GETs with the server's `VmHWM`
under 20 MB, and a file that shrinks mid-reply; five more for time and
size when the server was started with `--idle-ms MS` and the check with
`--idle=MS`; one for the limit with `--max-conns N` and `--conns=N`;
one for the log with `--log` and `--log=FILE`; twenty-two for WebSocket
with `--ws`; seven for the budgets with `--guard`, against a server
under `ulimit -n 64` with `--idle-ms 1000 --head-ms 1500` (600
pipelined GETs of a 100 KB file under a `VmHWM` of 40 MB, a peer that
never reads let go, a dribbled head dropped at its time, a `431`, a
`414`, 80 idle peers against 64 descriptors, and SIGTERM under a storm
of arrivals, which ends the server); and one, last, for stopping, with
`--term`, which sends the server SIGTERM and watches it refuse, finish
and go. `load.c` drives either;
`ramp.c` opens connections in blocks and never closes them; `sched.c`
is the scheduler's two halves measured in isolation.

    cc -std=c11 -O3 control.c -o control && ./control 8081
    cc -std=c11 -O3 check.c -o check && ./check 8080 $(pgrep -x httpd) --files --idle=400
    cc -std=c11 -O3 -DCHECK_TLS check.c -o check-tls -lssl -lcrypto
    cc -std=c11 -O3 load.c -o load && LOAD_SPIN=1 ./load 8080 32 5 8 /health
    cc -std=c11 -O2 ramp.c -o ramp && ./ramp 8080 /events
    cc -std=c11 -O2 fuzz.c -o fuzz && ./fuzz 8080 8081 2000
    ./prof.sh ../../httpd 40                   # where the time goes

## Streaming, and what it found in the runtime

`/events` is an event stream: the head goes out once, then one event at
a time on the engine's own clock, with nothing further read from the
peer. It is the shape that holds a connection open — an agent session,
a token stream, a live feed. The reader and the writer never contend
for the socket, because a stream stops reading; the event count is what
makes the loop terminate without `@unsafe`.

Holding concurrent live streams, one event per second each, on the
server as it stands (`--max-conns 20000`, since the default limit of
1024 is what stops the eleventh hundred connection and is supposed
to):

| live streams | RSS | per stream | CPU over 6 s |
|---|---|---|---|
| 1,000 | 3.3 MB | 0.31 KB | 0.10 s |
| 5,000 | 4.8 MB | 0.37 KB | 0.52 s |
| 10,000 | 6.8 MB | 0.37 KB | 0.99 s |

Memory is flat per stream and about an order of magnitude under what
the kernel spends on the socket itself. On that axis there is no
headroom left for anyone, in any language.

Holding them was not free until the fourteenth check existed. The
first holding numbers on this branch showed a fixed 2.8 s of CPU per
6 s whatever the stream count, and an idle server with no connections
burned the same. `strace -tt` showed one descriptor in a loop of
`recvfrom() = 0`: a peer that connected and closed without a byte (the
readiness probe in the measurement scripts). `TCP.recv_bytes` handed
back the empty chunk correctly; `plan.chunk` fed it to the parser,
got the same state back, and read again, a million times, until the
fuel ran out. An empty chunk is now `Stop{}`. Nothing in the runtime
was at fault -- the stock poll loop spun the same way -- and the check
that would have caught it now runs against both servers.

Establishing them was the problem. Adding connections in blocks, never
closing any, the wall time for each block against the live set it was
added to, on the runtime as this branch found it:

| live after | block wall | per connection |
|---|---|---|
| 500 | 1.04s | 2.1 ms |
| 1,000 | 2.04s | 4.1 ms |
| 2,000 | 11.27s | 11.3 ms |
| 4,000 | 61.43s | **30.7 ms** |
| 8,000 | not within 150s | — |

`io_wait` did work proportional to every parked computation on each
pass: it malloced a `pollfd` array sized by the live count, walked the
park list to fill it and to find the soonest deadline, polled, then
walked the list again to dispatch. Accepting a connection needs a
pass, so accepting n connections cost O(n^2). Holding them needs
almost no passes, which is why holding was free and arriving was not.

`bend2/comp.ts` on this branch does what every event loop has done
for twenty years: on Linux a descriptor waiter is registered with
epoll once, a deadline waiter sits in a binary min-heap, and a pass
costs what is ready. An activation can be in both at once — that is
what `TCP.poll` is — so it carries its heap slot and whichever fires
first takes it out of the other. Everywhere else the poll loop is
untouched under `#else`. The same ramp against the same engine on that
runtime:

| live after | scheduler | scheduler + backlog |
|---|---|---|
| 500 | 2.07 ms | 23 µs |
| 1,000 | **21 µs** | 23 µs |
| 2,000 | 3.08 ms | 21 µs |
| 4,000 | 3.07 ms | 21 µs |
| 8,000 | 1.30 ms | **28 µs** |

The middle column still has whole seconds in it — block walls of
1.03s, 3.08s, 6.13s — and whole seconds are SYN retransmit timers.
Every stream ticks once a second and they were all born in the same
second, so thousands of timers fire in one burst; while the loop sends
that burst the accept queue overflows, the kernel drops SYNs, and one
`connect()` sleeps for a second. The queue overflowed because
`bend2/effs/tcp_listen.c` said `listen(fd, 16)`. It now says
`SOMAXCONN`, which is what `control.c` has always done in spirit, and
the right column is what that one constant is worth.

## Measured

One 4-core Xeon at 2.8 GHz. The engine is built the way `bend -o`
builds everything, clang 18 at `-std=c11 -O3`; the C twins with `cc`
(gcc 13) at `-std=c11 -O3`. Medians of three runs.

### How to measure a server on loopback

A closed-loop client that sleeps between replies charges every reply
with the cost of waking it, and charges it to the *server's* `send`:
on loopback the wake-up runs in the sender's context. The slower the
server, the more its client sleeps, the more each send costs it -- a
loop that punishes exactly the server being measured. Split by
`/proc`, one engine process under a sleeping client spent 8.8 µs of
user time and **17.0 µs of system time** per request; the C control,
fast enough to keep the same client awake, spent 1.0 and 4.6. With
`LOAD_SPIN=1` the client never sleeps, a send costs a send, and the
engine's system time falls to 6.7 µs. Every number below is measured
that way; the numbers this README carried before were not, and
understated the engine by half at pipeline 1. The multi-process table
is only measurable this way at all: two engines kept a sleeping client
awake, which made each of them look faster than one alone.

### One process

| 32 keep-alive conns, `--threads 1` | Bend | C control | C over Bend |
|---|---|---|---|
| pipeline 1 | 80,052 req/s | 155,162 req/s | 1.9x |
| pipeline 8 | 128,028 req/s | 852,207 req/s | 6.7x |
| per request at pipeline 1 | 6.1 µs user + 6.7 µs sys | 1.1 µs user + 5.0 µs sys | |
| peak RSS under load | **3.5 MB** | 5.8 MB | |

WebSocket cost the request path about a tenth when it landed, and the
obvious culprit -- `Pend`, the node the parser rebuilds at every header
that closes, widened from five fields to eight -- turned out not to be
it. Narrowing it back (to six, with the upgrade state a sum whose
ordinary value carries no fields) changed nothing measurable, and nor
did a throwaway build with the upgrade's two parser states removed
entirely. The cost is spread thinly across everything the feature
widened. The profile below is where the work actually was.

The two depths fail differently, and forty stack samples under load at
pipeline 1 said why: every one of them was in a syscall or the loop
around it -- twenty in `send`, ten in `epoll_ctl`, nine in `recv`, one
in `epoll_wait` -- and **none in the parser**. At pipeline 1 this
server is a syscall machine, and a quarter of its syscalls were the
`epoll_ctl` pair that `io_wait_on` did on every park and `io_fire`
undid on every wake -- which the C control does not pay, because its
descriptors are registered once and stay registered.

Now Bend's are too. A waiter goes into the poller with
`EPOLLONESHOT`, the kernel disarms it as it fires, and the next park
is one `MOD` instead of an `ADD` and a `DEL`; `io_reg` is a byte per
descriptor saying whether the poller is believed to hold it, and every
call takes the other operation when the first is refused, so a
descriptor closed and its number reused corrects itself. Under load
the engine now makes 22,793 `sendto`, 23,159 `recvfrom` and **380**
`epoll_ctl` in three seconds -- one per sixty requests rather than one
per request, because a read that finds its bytes already waiting never
parks at all. That is the control's own syscall profile, and it is
worth 13% at pipeline 1 (68,924 and 70,779 req/s became 77,245 and
80,052) and nothing at pipeline 8, where the syscalls were already
amortised eight ways.

At pipeline 8 the kernel is amortised eight ways, the compute is all
that is left, and the gap widens to the compute gap: about 6 µs of
Bend against 1 µs of C. That is the parse, the reply and the plan, and
it is the engine's own to answer.

That answer was the reader's input. Read as `List<&2, U32>`, a cell
per byte, and walked a cell at a time, a request cost a list built by
the effect, a cell dropped per byte, and a walk of a static list per
punctuation byte to class it; the profile at pipeline 8 was a third
`term_drop` and reference-count traffic. On `Bytes` -- the read one
block, the tokens cut from it, names compared block against block, the
classes by ranges -- the same box (4-core VM, `--threads 1`, 32
connections, server and client pinned to their own cores, medians of
three) went from 53,256 to 75,149 req/s at pipeline 1 and from 92,499
to 191,538 at pipeline 8. What is left on top of the profile is the
walk itself: the runtime's uncons, and the drops of the views it cuts.

Guessing at either is a waste. Narrowing `Pend` from eight fields to
six -- the widening WebSocket had caused, which looked like the
obvious cost -- changed nothing measurable (69,466 against 70,154 at
pipeline 1), and neither did removing the two parser states the
upgrade added (122,976 against 124,145 at pipeline 8). The cost
WebSocket added is spread thinly across everything it widened, and the
cost worth chasing is the one the profile actually points at.

### One port, several processes

`--shared` sets `SO_REUSEPORT` (`TCP.listen_shared`, beside
`TCP.listen`, which keeps refusing a port already taken). N copies of
the single-threaded engine on one port, the kernel dealing the
connections out, against N copies of the control, 64 connections, the
client never sleeping. The fourth core is the client's, so N stops at
three; at pipeline 1 the client itself is the ceiling from two
processes on.

| processes | Bend, pipeline 1 | Bend, pipeline 8 | C control, pipeline 8 |
|---|---|---|---|
| 1 | 72,417 req/s | 117,386 req/s | 802,303 req/s |
| 2 | 142,667 | 248,014 | 1,218,663 |
| 3 | 129,761 (client-bound) | **384,762** | 938,430 (client-bound) |

The engine scales linearly with processes until the client runs out:
3.4x at three. That is the multi-core story for this server, and it
cost one flag and one effect. Runtime threads would be the harder road
to the same place.

The runtime is not the variable here. The same engine built on
canonical Bend 2.0.25, run back to back with this one under the same
load at `--threads 1`, came out within noise of it at both pipeline
depths (40,197 against 40,832 at pipeline 1, before the EOF fix
below, on both).

The engine is fastest at `--threads 1`: Bend's fork-join wins on pure
computation, but the IO loop does not yet turn threads into throughput.
For a server that is the process-per-core question, not a thread one.

And the engine, not the runtime, is where about a tenth went recently.
Built at the commit that brought the byte pair and again at this one,
both with the EOF fix, on one runtime, back to back at `--threads 1`:
47,858 → 42,935 req/s at pipeline 1 (a second run of the older engine
gave 45,433) and 110,415 → 105,276 at pipeline 8. What `/events` added
to the connection loop sits on every request's path; taking it off is
the next engine change, ahead of reply construction.

The gap to C is not where it looks either. Measured by substitution on
an earlier host, recv plus a 90-byte walk plus send ran within 1.10x of
the whole C server, so the effects themselves are nearly free; the rest
is the parse, the reply, and now the plan.

## Notes

What this branch changes in the runtime, and the evidence:

- `bend2/comp.ts`: `io_wait` on Linux is epoll plus a deadline heap,
  with the poll loop kept byte for byte under `#else`. `tests/io` on
  the stock runtime and on this one fail the identical set of files in
  both lanes — 71 of 91 native, 85 of 109 interpreted, before and
  after; `tcp_poll`, `udp_poll` and the channel and sleep tests
  exercise the dual wait.
- `bend2/effs/tcp_recv_bytes.*`, `tcp_send_bytes.*`: the byte pair,
  declared in `base.bend` beside `TCP.recv` and `TCP.send`.
- `bend2/effs/tcp_listen.*`: the backlog.

The engine itself builds unchanged on Bend 2.0.5 and on canonical
2.0.25 given the byte pair; the scheduler ports to 2.0.25 the same way
and was checked there against `tests/io` with the same result.
