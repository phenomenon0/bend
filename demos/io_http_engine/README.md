# io_http_engine

An HTTP/1.1 engine in Bend: a streaming request parser, a router and a
server, with the parser's laws proved by the stock checker. No host
language in the path — the socket is Bend's own effect.

    bend demos/io_http_engine/PROOF.bend        # the gate: laws hold
    bend demos/io_http_engine/main.bend -o httpd
    ./httpd --port 8080 --root www --idle-ms 10000 --max-conns 1024 --grace-ms 5000
    ./httpd --shared & ./httpd --shared &          # one port, one copy per core
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

## Configuration, routes, files

The binary reads its arguments with the same shape as it reads a
request: a state fed one argument at a time, a step that does not
recurse, and a refusal (`IO.die`) for anything it does not know.
`--port N`, `--root DIR`, `--idle-ms N`, `--max-conns N`, `--grace-ms
N`, `--shared` and `--log` are the settings.

The route table is data: a list of `Route{path, prefix, act}` built
once from the configuration and shared by every connection, walked
first match wins. Without a root it is `/health`, `/echo`, `/events`
and `/`; with one, `/` becomes a prefix route to `Files{}` and every
path the fixed routes leave is a file under the root, `/` itself being
`index.html`. Because the table is a value, LAWS.bend pins what it
answers and that no two entries claim one path, and the checker
refuses the build when someone adds a route that shadows another.

A file's name is the request path split on `/`, normalised (`.`
dropped, `..` climbing, a climb out of the root refused rather than
clamped, because a clamped path is a path someone will probe), and
gated to printable ASCII. Percent escapes are not decoded, so an
escaped `..` names a file that does not exist rather than a climb. The
type comes from the extension; a directory opens and then refuses to
be read, which is a miss; a file past 4 MiB is refused rather than
loaded, until pages are written in pieces.

A reply is a list of segments: bytes as they are, or a page to read
when the reply is written. Fixed routes stay pure and cost what they
cost before; only a file route puts IO on the path, and only for its
own request, so a pipelined batch mixing both still answers in order.

`HEAD` answers with the head of what `GET` would have sent, cut at the
blank line by a scanner rather than rebuilt, so the two can never
disagree about a length or a type; LAWS.bend says the scanner and the
head builder agree on the fixed replies. A `405` names the methods that
would have worked.

## Time and size

Every read has a deadline. `TCP.poll_bytes` is `TCP.poll` carrying
bytes (`bend2/effs/tcp_poll_bytes.{c,js}`, declared beside it): a recv
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

## WebSocket

`/ws` is a WebSocket echo. The request reader learned the three headers
the upgrade needs -- `Upgrade` by the hash of its value, `Connection:
Upgrade` beside `Connection: close`, `Sec-WebSocket-Key` as the bytes
it came in -- and a message that carried all three becomes a `101`
whose accept key is `base64(sha1(key ++ GUID))`, computed by the Bend
in `sha1.bend` and `b64.bend` once per handshake. After the `101` the
connection reads frames instead of requests.

`ws.bend` is the frame reader and writer (RFC 6455). The reader has the
request reader's shape, one structural walk with its state in one node,
and the same chunking law: `ws_feed_split` says a frame split across
reads parses where the whole would have, proved by the same induction.
What it accepts is deliberately small: client frames are masked or the
connection is failed with 1002, as the RFC requires; fragments and
reserved bits are refused; a payload past 1 MiB is refused at the byte
that announces it, before an eight-byte length could wrap. Text and
binary come back as they came, a ping is answered with a pong, a close
with a close and the end of the connection. The laws pin a masked text
frame and an empty ping reading back, the three refusals, and the
bytes the writer produces for a short frame, a two-byte length and a
close code.

`check.c` under `--ws` does the handshake with RFC 6455's own key and
expects the RFC's accept value, then the echo, the pong, a 300-byte
binary frame with its two-byte length, a frame split across two writes,
the close, the unmasked frame, and the `426` a plain `GET /ws` earns.

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
segments; `flat`, which already resolves segments in IO, prints it
against the bytes the next segment resolves to. So a pipelined batch
logs in the order its requests arrived, a file logs the size it
actually read, and a `HEAD` logs the head it actually sent. It is off
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
so every 250 ms of no arrivals it looks up and asks
`IO.signal_pending(15)` (`bend2/effs/signal_pending.{c,js}`: the first
ask installs a handler that only sets a flag, with `SA_RESTART` so no
effect in flight is failed by the signal). On a stop it closes the
listener, so new connections are refused at once; the ones open finish
what they are doing; and the process ends when every slot has come
back -- the loop refills the semaphore -- or when `--grace-ms` is up,
whichever is first. Two effects, both the size of the ones beside them,
and both generic: any long-running Bend program that has to be stopped
by its supervisor needs exactly these.

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
writes a head from a length. The four normaliser laws pin the paths
that matter: a climb from the root, a climb from under a real
directory, dots, and a climb that stays inside. Those four are pins,
not a proof over every path; that proof needs a lemma over classified
segments and is the next one to write.

Each law was checked by breaking it: a one-digit content-length, a
linefeed that escapes `Bad{}`, a `feed` that drops state at a chunk
boundary, a head one byte long, a climb claimed to resolve, and a
duplicate route are all rejected, with the two terms printed.

## The control and the checks

`control.c` is the same engine written the way a C server is written:
one epoll loop, the same modes, the same byte-at-a-time transitions,
the same routes, byte-identical replies, the same policy. `fuzz.c`
holds it to that: the same bytes, cut at the same random points and
sent with a pause between the cuts, go to both, and what comes back
has to be identical, closes included -- one to four messages a round,
valid or mutated in the ways a reader has to survive (a truncation, a
byte flipped, a version that is not 1.1, a Transfer-Encoding, a length
that is not all digits or is past the cap, fields in odd case, bodies
of arbitrary bytes). Its first run found two faults, both in the C:
the control closed the moment it had parsed `Connection: close`,
before the head had ended, and its 400 dropped its body when the
broken message had been a HEAD. With those fixed it runs thousands of
rounds without a difference. `check.c`
runs its behavioural cases against either: fifteen for any server,
the last of which reads the server's CPU when given its pid; nine more
for static files when the server was started with `--root` on the
fixture directory and the check with `--files`; five more for time and
size when the server was started with `--idle-ms MS` and the check with
`--idle=MS`; one for the limit with `--max-conns N` and `--conns=N`;
one for the log with `--log` and `--log=FILE`; eight for WebSocket
with `--ws`; and one, last, for stopping, with
`--term`, which sends the server SIGTERM and watches it refuse, finish
and go. `load.c` drives either;
`ramp.c` opens connections in blocks and never closes them; `sched.c`
is the scheduler's two halves measured in isolation.

    cc -std=c11 -O3 control.c -o control && ./control 8081
    cc -std=c11 -O3 check.c -o check && ./check 8080 $(pgrep -x httpd) --files --idle=400
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
