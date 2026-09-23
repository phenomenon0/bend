# bend-wire

A protocol server in Bend is three things: a reader that walks whatever
bytes a read hands it, a planner that turns what a read completed into
replies, and a loop that runs them against a socket under deadlines and
budgets. The first two are the protocol's. The loop, and the laws every
such reader and every such loop has, are this library's, written once
and proven once, polymorphically: a law here holds for every protocol
that plugs into it, and a protocol states it for its own code as a
one-line instance.

    wire/reader.bend    the reader kit: feed, feed_buf and their laws
    wire/loop.bend      the connection loop, the writer, the accept loop
    wire/world.bend     a pure model of the socket world, the effects'
                        contracts, and the loops' laws in it
    wire/effects.bend   the loops over IO and the real effects: serve,
                        run (a connection limit, SIGTERM, a grace time)
    wire/conform.bend   the real effects judged by the contracts, with
    wire/conform.c      conform.c as the peer
    wire/http1/         HTTP/1.1 responses: the reader (resp.bend), RFC
                        9112's framing as its spec (spec.bend), resp_sim
                        and the vectors (LAWS.bend, PROOF.bend), mutants.py
    wire/client.bend    the client's exchange: a request out, a response
                        in, under budgets, and whether to reuse; its laws
    wire/pool.bend      idle connections to an upstream, bounded, probed
                        as they are taken; its laws
    wire/stream.bend    a body as a stream: chunks handed to a consumer
                        as they arrive, under a window; its laws are in
                        world.bend

Its users: `demos/io_http_engine` (HTTP/1.1, WebSocket, SSE, files),
`demos/io_resp` (RESP, below) and `power/csv.bend` (the reader kit only).

## The reader

A reader is a byte-step machine, handed in as template arguments:

    ~E: Data                    what a step reads beside the state (CSV's
                                dialect; Unit when there is none)
    ~S: Data                    the state
    ~step: E -> S -> U32 -> S   one byte
    ~adv: E -> Bytes() -> S -> S & Bytes()
                                one move of the block walk: a run the
                                protocol takes whole, or one byte
                                (Wr.one.step takes one byte)

`Wr.feed` walks a list of bytes, `Wr.feed_buf.slow` a block a byte at a
time, `Wr.feed_buf` a block by the protocol's moves (the run-cutting fast
path), and `Wr.reads` a stream's reads in turn.

**Obligations**, each proved by the protocol and handed in as a template
argument:

| obligation | statement | who |
|---|---|---|
| `adv_ok` | `feed_buf.last(e, adv(e, s, p)) == feed_buf.slow(e, s, p)` | a protocol with runs (HTTP's `lem.adv`, CSV's); `Wr.one.step_ok` for one byte a move |
| `absorbs` | `step(e, bad(x), c) == bad(x)` for the refused states `bad(x)` | every protocol; usually `{==}` |

**Laws you get**: `feed_split` (chunking never changes a read),
`bad_feeds`, `bad_feeds_buf`, `bad_feeds_slow` (a refusal is never
left), `slow_is_feed`, `go_is_slow`, `feed_buf_is_feed` (the block walk
is the byte machine), `feed_buf_split`, `slow_split` (chunking, on
blocks), `reads_is` and `reads_split` (any list of reads reads as their
concatenation).

**Taking a body as it comes.** A reader that frames a body can hand it
on as it arrives: `~take` answers the body bytes the state holds and
the state without them, `~give` puts bytes back in front, `~open` says
the head is behind. `Wr.drain` is a stream read that way, each read
fed and then taken. For seven obligations (an open state stays open
and steps the same with bytes put back in front, a state not open
holds none, take and give are inverse, give of nothing is nothing and
of two joined the two in turn) the kit proves `drain_reads`: the
chunks taken, joined in order, put back in front of what the reader
still holds, are the reader fed the stream whole, however it was cut.
`wire/http1/resp.bend` proves them (`R.take`, `R.give`, `R.open`).

## The loop

A server hands `wire/loop.bend` its hooks (the names are the loop's
template parameters):

| hook | what |
|---|---|
| `~E: Data`, `+srv: E` | what serving needs (a configuration) |
| `~P: Data`, `p0: P` | a connection's state between reads, and a fresh one's |
| `~U: Data` | an upgraded connection's state (Unit when none) |
| `~idle`, `~hdms` | the idle time and a head's time, from `srv` |
| `~plan: E -> Bytes() -> P -> Plan<P, U>` | a read's bytes (never empty: the peer's FIN ends the connection first) to what next |
| `~mid: P -> Bool` | a head is in progress: the next read is under its budget |
| `~big` | the reply to a head past `head.cap()` |
| `~uplan` | `~plan` for an upgraded connection |
| `~gap`, `~event` | a stream: the wait between events, and the n-th |
| `~shut`, `~fhead`, `~miss` | a reply marked last, a file's head, a missing file |
| `~lnote`, `~lsize` | access log lines |

`L.no.*` are the hooks of a protocol that uses less: no head budget, no
upgrade, no stream, no files, no log. A `Plan` is `Go{out, p2}` (write,
read again), `Wait{p2}` (read again), `End{out}` (write, close),
`Feed{out, n}` (write, stream n events), `Sock{out, u}`/`Hold{u}`
(upgrade), or `Stop{}`. The replies are `Seg`s: `Raw{bytes}`, `Page{...}`
(a file, by sendfile), `Note{...}` (a log line), `Shut{}`.

The budgets are the loop's: a read takes at most `chunk()` bytes; a head
in progress at most `head.cap()` bytes past the read it began in, and
`hdms(srv)` of the clock; replies wait in one batch that goes out at
`send.cap()`; every send has `idle(srv)` as its deadline; a connection
reads at most `conn.fuel()` times, and at most `conn.waits()` times in a
row without finishing anything.

**The one obligation**: `event_ok`, an event is never empty once framed,
`empty(shut(False{}, event(n))) == False{}` (HTTP's computes;
`WW.no.event_ok` is the default's).

**Laws you get** (`wire/world.bend`, for every hook): `end_is_last` and
`stop_is_last` (an ending plan is the last act), `go_order` (replies go
out before the next read), `fail_go`, `fail_up`, `fail_feed` (nothing
after a failed send), `segs_wire` (replies reach a reading peer byte for
byte, in order), `hold_fine`, `raw_fine`, `page_fine`, `batch_under`
(the batch stays under its cap), `head_capped`, `head_expires`,
`hw_rest`, `hw_keeps` (the head's budget and deadline), `stall_ends` (a
stopped peer is let go within three turns, from any state),
`accept_calm` and `accept_ends` (the accept loop stays up, and ends
only as it may), `page_wire` (a file's reply puts on the wire what
waited, its head, and then the file's own bytes, every one and nothing
else, by sendfile or, for a small file, by one read), `page_fail`,
`page_head_fail` and `page_read_short` (a sendfile, a head or a small
file's read that did not all go out ends the writer); and of the model
against the effects' contracts, `rx_model`, `tx_stalled`, `tx_served`, `fread_model`,
`fsend_model` (a sendfile to a reading peer puts the file's bytes from
its offset on the wire and is Done only when the file had them all),
`fsend_stalled`. `conform.bend` checks the real effects keep the same
contracts.

**Files.** A `Page`'s body goes out by `File.sendfile(sock, file, off,
len, ms)`: on a plain socket the kernel copies it from the page cache
to the socket (Linux and macOS sendfile), under TLS the effect writes it
through the session a 64 KiB block at a time; either way the
connection holds none of the file itself. A file under `page.small()`
(16 KiB) is read whole instead and goes out with its head in one send,
which costs a small file less than a second send would. A body that
comes up short (the file shrank) fails, ending the connection
(`page_fail`, `page_read_short`). One core, `wrk -t2 -c32`, against
nginx with one worker and sendfile on: 4 KiB about 20k req/s to
nginx's 37k (as before), 1 MiB 1.9-2.6k req/s to nginx's 1.7k (1.4-1.6k
before).

## Bodies as streams

`wire/stream.bend` delivers a body a read at a time to a consumer that
may be slower than the peer -- an upstream socket, a file, a planner --
with backpressure. It is written over its effects and its framer like
the loop: `~rx` the timed read; `~feed`, `~take`, `~look` the framer (a
reader on the kit with the kit's take, and its word on the body: more to
come, whole, running to the close, refused); `~give` and `~fin` the
consumer (offered every byte held, it answers how many it took from the
front; told once that the body is over). A turn is a pass (offer what is
held) and a pull (read, feed, take, hold): the socket is read only while
fewer than `win` bytes are held.

**Laws** (`wire/world.bend`, for every framer, with a scripted peer and
a scripted consumer): `stream_pass` (a pass only moves bytes: what the
consumer took followed by what is held is what it was, the socket
untouched, no end told), `stream_stall` (a consumer that takes none of
a full window ends the stream with no read), `stream_full` (a full
window is never read into), `stream_pull` (a read's body joins the end
of what is held, exactly the bytes the framer took), `stream_over` (a
read that would bring more body than bytes ends the stream instead),
`stream_window` (so what is held stays under the window plus one read),
`stream_fin_held` and `stream_fin_last` (the end is told only with
nothing held and the body over, once, and the stream ends with it).
With the kit's `drain_reads` they say the chunks a consumer is handed,
in order, are the body the reader frames, whatever the cuts.
`client_mutants.py` breaks the stream eight ways, each refused.

The client streams a response with `fetch.stream` (the head capped as
`fetch` caps it, the body to the consumer); `demos/io_http_client
--stream` fetches a 100 MB file from nginx in 10 MB of RSS, where
gathering a 15 MB one takes 35 MB. For a request body, a server hands
the stream a reader entered at the body (`R.body.len`, `R.body.chunked`):
`demos/io_sink` takes 100 MB uploads, by length or chunked, at the
speed nginx discards them, its peak RSS 3 MB after 200 MB.

## A protocol on the kit: RESP

`demos/io_resp` is the worked example. Its reader (`resp.bend`) is a
step function over one state node, with the stack of arrays it is
inside:

    def wstep(u: Unit, r: Rd, c: U32) -> Rd:
      step(r, c)

    def wadv(u: Unit, s: Bytes(), r: Rd) -> Rd & Bytes():
      Wr.one.step(~Unit, ~Rd, ~wstep, u, s, r)

    def feed_buf(+s: Bytes(), r: Rd) -> Rd:
      Wr.feed_buf(~Unit, ~Rd, ~wstep, ~wadv, Unit{}, s, r)

and its chunking laws are the kit's, one line each (`PROOF.bend`):

    def Laws.feed_split(a, b, r):
      Wr.feed_split(~Unit, ~R.Rd, ~R.wstep, Unit{}, a, b, r)

    def Laws.feed_buf_is_feed(b, r):
      Wr.feed_buf_is_feed(~Unit, ~R.Rd, ~R.wstep, ~R.wadv,
        ~Wr.one.step_ok(~Unit, ~R.Rd, ~R.wstep), Unit{}, b, r)

The server (`main.bend`) is its planner -- a read's bytes through the
reader, the finished values through the commands, the replies as one
`Raw` -- and the hooks:

    def plan(cfg: Cfg, buf: Bytes(), c: Conn) -> Plan():
      match c:
        case Conn{r, kv}:
          plan.took(kv, R.take(R.feed_buf(buf, r)))

    def go(+cfg: Cfg, s: Socket) -> IO(Socket):
      Fx.serve(~Cfg, ~Conn, ~Unit, ~idle, ~idle, ~plan, ~L.no.mid(~Conn), ~L.no.big(),
        ~L.no.uplan(~Conn, ~Unit), ~L.no.gap(), ~L.no.event, ~L.no.shut, ~L.no.fhead,
        ~L.no.miss, ~L.no.lnote, ~L.no.lsize, cfg, conn.new(), s)

    def main() -> IO(Unit):
      ...
      Fx.run(~Cfg, ~go, ~grace, ~conns, "bend-resp", Cfg{300000, 3000, 1024}, l)

and it has the loop's laws at its hooks, each a one-line instance
(`LAWS.bend` states `end_is_last`, `go_order`, `fail_go`, `segs_wire`,
`stall_ends`), besides its own (`refuse_ends`: a refused stream is
answered with what its values earned, then the error, and the
connection ends).

**What it cost.** Before bend-wire, RESP's server was 147 lines (121 of
code) of connection-loop shape copied from the HTTP engine: a plan type,
a read and a send each unwrapped by hand, a fuelled loop, an accept loop,
with no head or batch budget, no connection limit, no SIGTERM and no
laws. On the kit it is 102 lines (69 of code): the planner is 36 lines
of code, the rest a configuration record and the hooks. It gets the
loop's budgets, the connection limit, graceful stopping and the loop's
laws for nothing. The measure the HTTP engine's HANDOFF set -- an hour
rather than an afternoon -- is honest only in lines: the protocol-
specific part of the server went from 121 lines of code, all of them
loop shape, to 36 of planner. What the rebuild did cost was Bend's
rules on shape, not the loop's: two scrutinees out of binder order, and
the checker unfolding a literal idle time (below).

**One thing to know.** A law at a protocol's hooks is re-checked with
the hooks filled in, so a hook that computes to a large number -- an
idle time written as a literal `300000` -- makes the checker unfold
`U32.to_nat` of it. Keep budgets in `srv` (RESP's `Cfg`), where the
checker sees a variable.

## The client

The other side of the wire. A client connects (`TCP.connect_poll`, or
`TLS.connect`: SNI, ALPN, the certificate verified against the system's
store or a pinned CA, the name checked; `DNS.resolve` for a name), and
`wire/client.bend` runs one exchange on the connection: the request out
under the step deadline, the response read through `wire/http1`'s
reader until it is framed, refused, or out of time, under a head cap, a
body cap (the reader's `Ask`) and the exchange's deadline, each read's
wait cut to the time left. What comes back is the framed response or
why there is none (`Why`), and whether the connection may carry another
request: only when the response did not close it (Connection: close,
HTTP/1.0 without keep-alive, a 101, a body that ran to the close) and
nothing came after it.

**The response reader** (`wire/http1/resp.bend`) is a reader on the kit,
with the request's method as its context (a response to HEAD has no
body) and the body's cap. It accepts the status line of HTTP/1.1 or
HTTP/1.0 with a code from 100 to 599, field lines by the same strict
grammar as the engine's requests, and frames the body by RFC 9112 6.3:
HEAD, 1xx, 204 and 304 have none (a 1xx other than 101 is interim and
the final response follows), chunked is decoded by 7.1's grammar,
extensions and trailers dropped, a Content-Length is counted off, and
anything else runs to the close. It refuses a Transfer-Encoding beside
a Content-Length, one in HTTP/1.0, any coding but chunked or chunked
twice, a length list or two that disagree, obs-fold, a bare LF, a
malformed status line. **resp_sim** holds it to `spec.bend`, the
framing written line by line from the RFC: for every context and every
input the two read the same interim statuses and the same end, and the
kit carries that to every way TCP cuts the input (`resp_sim_reads`).
`mutants.py` breaks the reader twenty-seven ways, each refused by
resp_sim alone.

**The client's laws** (`wire/client.bend`, in `world.bend`'s model):
`reuse_clean` (a connection is reused only when its response did not
close it and nothing came after it, for every peer the script can
describe), `expires` (a turn
at or past the deadline reads nothing), `read_in_time` (a turn before
it returns by it, whatever the peer does), `head_capped`.

**The pool's laws** (`wire/pool.bend`, over model connections that say
whether bytes wait unread on them): `take_ok` (a take hands out at most
one connection, one with nothing unread, fresh by the pool's age and
idle time, and leaves it out of the pool; the pool only shrinks) and
`give_ok` (a give keeps the pool within its cap and every connection in
it once). `client_mutants.py` breaks the client and the pool nine
ways, each refused by these laws. `TCP.idle` is the probe, and `conform.bend` checks its
contract (`idle.ok`) with the connects' (`cx.ok`, `tls.ok`).

`demos/io_http_client` is a command-line client on all of it; its
`check.sh` runs it against the HTTP engine, plain and over TLS, and
against nginx.
