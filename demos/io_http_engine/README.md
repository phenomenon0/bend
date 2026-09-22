# io_http_engine

An HTTP/1.1 engine in Bend: a streaming request parser, a router and a
server, with the parser's laws proved by the stock checker. No host
language in the path — the socket is Bend's own effect.

    bend demos/io_http_engine/PROOF.bend        # the gate: laws hold
    bend demos/io_http_engine/main.bend -o httpd && ./httpd
    curl -i http://127.0.0.1:8080/health

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
sockets did not, and it belongs upstream rather than in a demo.

`check.c`'s last case is the one that catches this, and it is the only
one that does: the engine as first written passes twelve of thirteen
and fails that one.

## What it is

The reader is one structural walk over whatever bytes the socket hands
over. Its whole state rides in one `P` node, so a head split across
three recvs parses exactly like a head that arrived whole, and a chunk
holding three pipelined requests yields three requests in that one
walk. It keeps no buffer of its own and never re-scans.

That shape is not a workaround. Bend's loops cannot exit early — a
recursive call has to shrink a matched argument — so a machine that
stopped at the blank line would still have to walk the rest of the
buffer rebuilding a dead state. So the machine never stops: completing
a message emits it and rolls straight into the next one, which is what
a pipelining parser should do anyway.

Field names are recognised by their FNV-1a hash, folded byte by byte as
the name is read, so a name is never built, stored or compared as
bytes. At the colon the value scanner is chosen by that hash: a
Content-Length value accumulates a decimal, a Connection value a hash,
and every other value takes the scanner that does no work per byte.

What it accepts is deliberately small, because a framing disagreement
is how requests get smuggled: HTTP/1.1 only, Content-Length only, that
length all digits, and no Transfer-Encoding at all. `Bad{}` is never
left.

`conn` is bounded by fuel rather than `@unsafe`, so a peer that dribbles
bytes forever runs it out and is dropped. The accept loop is the one
`@unsafe` def, as in `demos/io_http_server`.

## The laws

`feed_split` is the one that matters: `feed(a ++ b, p)` equals
`feed(b, feed(a, p))`. Chunking does not change the parse, however TCP
decides to split a message. It is also what licenses keeping no buffer.

`bad_absorbs` and `bad_feeds` say no byte moves the reader out of
`Bad{}` — without them a smuggled request could follow a refused one on
the same connection and be served.

The five `*_is_built` laws each say one written-out reply is byte for
byte what `reply()` returns for the arguments named beside it. Those
replies are literal byte arrays, because building a 106-byte reply out
of nine pieces cost more per request than parsing the request that
asked for it; nobody should read the numbers, and nobody has to, since
the checker refuses the engine the moment an edit makes one false.

Each was checked by breaking it: a one-digit content-length, a linefeed
that escapes `Bad{}`, and a `feed` that drops state at a chunk boundary
are all rejected, with the two terms printed.

## The control and the checks

`control.c` is the same engine written the way a C server is written:
one epoll loop, the same modes, the same byte-at-a-time transitions,
the same routes, byte-identical replies, the same policy. `check.c`
runs thirteen behavioural cases against either. `load.c` drives either.

    cc -std=c11 -O3 control.c -o control && ./control 8081
    cc -std=c11 -O3 check.c -o check && ./check 8080 && ./check 8081
    cc -std=c11 -O3 load.c -o load && ./load 8080 32 5 8 /health

## Measured

One 5-core Xeon 8573C, clang 18, `-O3`, medians of five. Checked on
Bend 2.0.5 (this checkout) and on canonical Bend 2.0.25; the numbers
below are 2.0.25. `bench/runtime/http` is the parser with no IO at all:
2,097,152 request heads, about 420 MB, generated and parsed, against a
C twin that produces the same checksum.

| pure parser, 2^21 requests | time | vs C |
|---|---|---|
| C, one core | 1.121s | 1.00x |
| Bend, `--threads 1` | 4.408s | 3.93x |
| Bend, `--threads 4` | 1.139s | **1.02x** |

Resident memory is 11.2 MB for every row. Subtracting the generator,
which both languages run identically, the parse alone is 1.45x C on one
core and 2.2x **faster** than C on four.

| server, 32 keep-alive conns | Bend | C control | C/Bend |
|---|---|---|---|
| pipeline 1 | 61,988 req/s | 180,612 req/s | 2.91x |
| pipeline 8 | 109,075 req/s | 413,109 req/s | 3.79x |
| RSS under load | **2.9 MB** | 5.7 MB | 0.51x |

Two things in there are worth knowing before optimising anything.

The engine is fastest at `--threads 1`; two and four threads cost about
20%. Bend's fork-join wins on pure computation — the same parser gets
3.9x from four threads above — but the IO loop does not currently turn
threads into throughput.

And the gap is not where it looks. Measured by substitution on one run:
recv plus a 90-byte walk plus send runs within **1.10x** of the whole C
server, so the effects themselves are nearly free. Parsing adds 4.4 µs
per request. Reply construction was the largest single term until the
fixed replies became literals, and it is still what to attack next.

## Notes

`bench/runtime/http` has no `_pin_` row yet, so the perf gate shows it
without a ratio until someone runs `--pin`.
