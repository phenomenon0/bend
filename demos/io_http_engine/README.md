# io_http_engine

An HTTP/1.1 engine in Bend: a streaming request parser, a router and a
server, with the parser's laws proved by the stock checker. No host
language anywhere in the path — `TCP.listen`, `TCP.accept`, `TCP.recv`
and `TCP.send` are Bend's own effects.

    bend demos/io_http_engine/PROOF.bend        # the gate: laws hold
    bend demos/io_http_engine/main.bend -o httpd && ./httpd
    curl -i http://127.0.0.1:8080/health

## What it is

`main.bend` is the engine. The reader is one structural walk over
whatever bytes a socket hands over. Its whole state rides in one `P`
node, so a head split across three recvs parses exactly like a head
that arrived whole, and a chunk holding three pipelined requests yields
three requests in that one walk. It keeps no buffer of its own and
never re-scans.

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

`LAWS.bend` states four things and `PROOF.bend` proves them.

`feed_split` is the one that matters: `feed(a ++ b, p)` equals
`feed(b, feed(a, p))`. Chunking does not change the parse, however TCP
decides to split a message. It is also what licenses keeping no buffer.

`bad_absorbs` and `bad_feeds` say no byte moves the reader out of
`Bad{}` — without them a smuggled request could follow a refused one on
the same connection and be served.

The five `*_is_built` laws say each written-out reply is byte for byte
what `reply()` would have returned. Writing fixed replies out by hand
is worth about a third of the cost of serving a request, and it is
exactly the kind of shortcut that rots; here the checker refuses the
engine if anyone edits one without the other.

Each was checked by breaking it: a one-digit content-length, a linefeed
that escapes `Bad{}`, and a `feed` that drops state at a chunk boundary
are all rejected, with the two terms printed.

## The control

`control.c` is the same engine written the way a C server is written:
one epoll loop, the same ten modes, the same byte-at-a-time
transitions, the same routes, byte-identical replies, the same policy.
`load.c` drives either of them. Both servers pass the same twelve
behavioural checks, including pipelining, a head split across three
writes, and the Transfer-Encoding and HTTP/1.0 refusals.

    cc -std=c11 -O3 control.c -o control && ./control 8081
    cc -std=c11 -O3 load.c -o load && ./load 8080 32 5 8 /health

## Measured

On one 5-core Xeon 8573C, clang 18, `-O3`. `bench/runtime/http` is the
pure parser without any IO: 2,097,152 request heads, about 420 MB,
generated and parsed, against a C twin that produces the same checksum.

| pure parser, 2^21 requests | time | vs C |
|---|---|---|
| C, one core | 1.111s | 1.00x |
| Bend, `--threads 1` | 4.192s | 3.77x |
| Bend, `--threads 2` | 2.193s | 1.97x |
| Bend, `--threads 4` | 1.157s | **1.04x** |

Resident memory is 11.2 MB for every row. Subtracting the generator,
which both languages run identically, the parse alone is 1.45x C on one
core and 2.2x **faster** than C on four.

| server, 32 keep-alive conns | Bend | C control | C/Bend |
|---|---|---|---|
| pipeline 1 | 47,836 req/s | 165,877 req/s | 3.47x |
| pipeline 2 | 63,971 req/s | 286,264 req/s | 4.47x |
| pipeline 8 | 107,881 req/s | 426,579 req/s | 3.95x |
| RSS under load | **2.9 MB** | 9.9 MB | 0.30x |

Two things in there are worth knowing before optimising anything.

The engine is fastest at `--threads 1`; two and four threads cost about
20%. Bend's fork-join wins on pure computation — the same parser gets
3.6x from four threads above — but the IO loop does not currently turn
threads into throughput.

And the gap is not where it looks. Measured by substitution on the same
run: recv plus a 90-byte walk plus send runs within **1.10x** of the
whole C server, so the effects themselves are nearly free. Parsing adds
4.4 µs per request. Building the reply added 20 µs — more than three
times the parse — until the fixed replies were written out, which is
what the `*_is_built` laws are guarding. Reply construction out of many
`++` pieces, not the parser and not the runtime, is the thing to attack
next.

## Notes

`bench/runtime/http` has no `_pin_` row yet, so the perf gate shows it
without a ratio until someone runs `--pin`.
