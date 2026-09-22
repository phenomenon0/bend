# Three bugs in Bend's runtime, found by building a server on it

Everything below is against `bendlang/bend` as it ships on `main`
(checked again at `db06f02f`), reproduced on Linux x86_64 with
clang 18. Each fix is a branch off canon's current `main`, one bug
each, with its own test where a test is possible:

    fix/socket-bytes      the byte pair, with tests/io/tcp_recv_bytes.bend
    fix/listen-backlog    one line, both twins
    fix/epoll-scheduler   the poller, with the select loop kept under #else

Every one was run against canon's own `tests/io` in both lanes, beside
a run of `main` on the same box, and **each fails the identical set of
files as `main`** and none regresses anything canon passes. Judged as
the gate judges (expected errors and `exit N` lines count as output),
`main` passes 110 of 116 files; the byte branch 112 of 117 (it brings a
test); the other two 112 of 116. What fails on Linux is the four audio
tests (no ALSA headers) and two tests that order millisecond sleeps,
which flake under load. An earlier count here, 89/116 and 72/98, came
from a harness that compared stdout only and so failed every test that
expects an error.

---

## 1. `TCP.recv` and `TCP.send` corrupt every byte that is not UTF-8

**Where** `bend2/effs/tcp_recv.c`, `bend2/effs/tcp_send.c`

`tcp_recv.c` builds its result with `io_str`, which decodes the bytes
as UTF-8:

```c
Term r = w->code ? io_fail(e, w->code, NULL)
  : io_done(e, io_str(e, w->data, w->size));
```

`tcp_send.c` reverses that with `io_cstr`, which re-encodes. So a
socket carrying anything that is not valid UTF-8 -- a PNG, a protobuf,
a TLS record, a WebSocket frame, a gzip body -- loses it: each
ill-formed byte becomes U+FFFD, three bytes out for one byte in.

**Why it is worse than "binary is not supported".** The corruption
changes the *length*. A server that reads 8 arbitrary bytes and echoes
them back with `content-length: 8` writes 12 bytes on the wire (the two
bytes that are not UTF-8 become three each). On a keep-alive connection
the peer then reads the next reply's first four bytes as the tail of this one, and every message after it is framed
against the wrong boundary. That is response splitting by accident: it
is the bug class HTTP framing rules exist to prevent, and it is
reachable by any peer who sends a byte over 0x7F.

**Reproduce** an echo server on `TCP.recv`/`TCP.send`, then

```
printf 'GET /echo HTTP/1.1\r\nHost: x\r\ncontent-length: 8\r\n\r\n\x01\x80\xfe\x02\x03\x04\x05\x06' | nc 127.0.0.1 8080 | xxd
```

The body comes back 12 bytes long under a `content-length: 8`:
`01 efbfbd efbfbd 02 03 04 05 06`.

**Fix** the byte pair that files have already had for as long as
`File.read_bytes` and `File.write_bytes` have existed: carry
`List<&2, U32>`, one cell per byte, and decode nowhere. Attached as
PR 1. It is four small files and two declarations, and it adds
nothing the language did not already have a precedent for -- the
inconsistency is that sockets were left out.

---

## 2. `io_wait` costs what is waiting, so accepting n connections costs O(n^2)

**Where** `bend2/comp.ts`, `static void io_wait(Env e)`

Every pass allocates a descriptor set sized by the highest live
descriptor, walks the whole park list to fill it and to find the
soonest deadline, selects, then walks the whole list again to
dispatch:

```c
for (IoAct* a = io_park.head; a != NULL; a = a->next) { ... }   // size it
u8* set[2] = { io_mem(calloc(2, len)), NULL };
for (IoAct* a = io_park.head; a != NULL; a = a->next) { ... }   // fill it
...
while (todo.head != NULL) { ... }                               // and again
```

Accepting one connection needs one pass, so accepting n needs n passes
and each costs O(n). Holding connections needs almost no passes, which
is why holding is free and arriving is not -- and why this does not
show up until something tries to *establish* a lot of connections.

**Measured** with `demos/io_http_engine/ramp.c` from the attached
branch: connections opened in blocks, never closed, timed against the
live set they were added to.

| live after | per connection |
|---|---|
| 500 | 2.1 ms |
| 1,000 | 4.1 ms |
| 2,000 | 11.3 ms |
| 4,000 | **30.7 ms** |
| 8,000 | did not finish in 150 s |

Those are the HTTP server's numbers, and its ramp also ran into the
backlog of 16 below (SYN retransmits add 1 s and 3 s stalls). A minimal
server that accepts and parks, with a client that waits for each
accept, shows the curve alone, total time to hold n connections:

| live | canon `main` | `fix/epoll-scheduler` |
|---|---|---|
| 1,000 | 0.15 s | 0.06 s |
| 4,000 | 1.49 s | 0.28 s |
| 8,000 | 4.29 s | 0.49 s |
| 16,000 | 31.4 s | 1.78 s |

Quadratic, but not "never finishes". The branch fixes the C twin on
Linux only: macOS keeps `select`, and the JS lane's loop in `comp.ts`
is still quadratic (51.7 s at 16,000).

**Fix** the one everyone else made twenty years ago: on Linux,
register a descriptor with epoll once and keep it registered
(`EPOLLONESHOT`, re-armed in place), and keep deadlines in a binary
min-heap. A pass then costs what is ready, and a wake costs no syscall
at all: under load at pipeline 1 a server makes 380 `epoll_ctl` per
22,793 requests rather than one per request, worth about 13% of its
throughput. The select loop is kept byte for byte under `#else` for
every other platform.
The same ramp on it is flat at 21-29 us per connection out to 8,000
held, and `tests/io` fails the identical set of files before and
after, in both lanes.

An activation can wait on a descriptor *and* a deadline at once --
that is what `TCP.poll` is -- so the patch carries a heap index in
`IoAct` and whichever fires first takes it out of the other. That is
the only subtlety in it.

---

## 3. The listen backlog is 16

**Where** `bend2/effs/tcp_listen.c` (and `tcp_listen.js`)

```c
if (bound < 0 || listen(fd, 16) < 0
```

Sixteen is the depth of the queue the kernel holds for connections
that completed their handshake but have not been accepted yet. A
server that is briefly busy -- and a single-threaded event loop
sending a burst is briefly busy on purpose -- overflows it, the kernel
drops the SYNs, and the peers that sent them wait for a retransmit.

**Measured** with the scheduler fixed, the connection ramp still had
whole seconds in it: block walls of 1.03 s, 3.08 s and 6.13 s, which
are the 1 s and 3 s SYN retransmit timers and nothing else. With
`SOMAXCONN` in place of the 16, the same ramp is flat at 21-29 us per
connection and the seconds are gone.

**Fix** `SOMAXCONN`, which the kernel clamps to its own limit anyway.
One constant, in both twins, on its own branch.

---

## A fourth, withdrawn: a name collision that looked like a loop

**Not reproduced.** A dozen reductions on this branch and on canon
report or check in seconds, and the shipped engine already has the
pattern (`pem.cert(pem, p)` with `pem` live) and checks in 3 s. The
likeliest cause: `bend main.bend` without `--check-only` or `-o` checks
the file and then *runs* the server, which never returns. What follows
is the original note, kept for the record.

Twice now, and worth saying even unreduced. When a def namespace
shares its name with something live in scope -- defs `tls.cert` and
`tls.key` called where a binder `tls` is live, later defs `plan.*`
called where a binder `close` is live and `plan.close` is one of them
-- the checker did not report an error. It ran for minutes without
finishing. Renaming the namespace made it check in seconds, both
times.

Every other name collision in this work reported cleanly and at once
("this name is a def or a consumed binder"), so this looks like a path
that loops rather than one that reports. It cost two debugging
detours, and it is the one thing here that is a checker bug rather
than a runtime one. I will reduce it to a file if that helps.
