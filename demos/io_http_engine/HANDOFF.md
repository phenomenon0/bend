# Where this stands

Written at the end of the session that built it, so that whoever picks
it up next -- a person, or me with no memory of today -- can see the
state without reading the history.

## The repositories, and what is where

Everything lives in `phenomenon0/bend`. Nothing is on `bendlang/bend`.

| branch | base | what it is |
|---|---|---|
| `omen-http` | the `omen` fork line (2.0.21) | **the live line.** The server, the runtime it needs, the tests, the tools, this note |
| `claude/bend-http-experimental-2hue8o` | `main` (2.0.5) | the early engine, kept as a record. Stale: the later work needs effects 2.0.5 does not have |
| `fix/socket-bytes` | canon `main` (`db06f02f`) | upstream fix 1 |
| `fix/listen-backlog` | canon `main` | upstream fix 2 |
| `fix/epoll-scheduler` | canon `main` | upstream fix 3 |

The three `fix/*` branches are **for `bendlang/bend`, not for this
fork**. They are cut from canon's current `main`, one bug each, and
pushed here only so they survive. No pull request has been opened
anywhere: that is a decision waiting on the repository's owner.

Each was run against canon's own `tests/io`, in both lanes, beside a
run of `main` on the same box:

| tree | files passing | failing files |
|---|---|---|
| canon `main` | 110 / 116 | -- |
| `fix/socket-bytes` | 112 / 117 | identical to `main` |
| `fix/listen-backlog` | 112 / 116 | identical to `main` |
| `fix/epoll-scheduler` | 112 / 116 | identical to `main` |

Judged as the gate judges. The failures are the four audio tests (no
ALSA headers on Linux) and two sleep-ordered tests that flake under
load; the 110/112 split between runs is those flakes.

The byte branch is one higher in each lane because it brings a test
with it. The other two change no test's outcome. The failing files are
the same set on every tree, so none of the three regresses anything
canon already passes.

## What works, and how it is checked

`demos/io_http_engine` is an HTTP/1.1 server (HTTP/1.0 too, closed
unless it asks to keep alive; chunked request bodies, decoded under the
body cap, with every Transfer-Encoding smuggling shape refused):
keep-alive, pipelining, static files, SSE, WebSocket, TLS, an access log, a connection limit,
timeouts, graceful shutdown, and a shared port for running one copy per
core. A 1.6 MB binary, linked against libc, libm, libssl and libcrypto. `demos/io_resp` is a RESP reader written to
test whether the approach generalises (see **What is unfinished**).

    bend demos/io_http_engine/PROOF.bend          # 197 laws
    bend demos/io_http_engine/main.bend -o httpd
    ./httpd --port 8080 --root www --tls-cert cert.pem --tls-key key.pem

Four gates, and it is worth knowing what each one is for, because they
catch different things and three of them have caught real bugs:

- **`PROOF.bend`** -- 197 laws, re-checked by a second, independent
  kernel (`kernel/`). The headline is `frame_sim`: for every input, cut
  into reads any way, the reader frames exactly what `Spec.frame` (RFC
  9112, written apart) frames. The laws of the world (`world.bend`)
  prove the loops' order, budgets and deadlines against a pure model of
  the sockets. `frame_sim` covers HTTP/1.0 and chunked bodies too:
  the spec reads RFC 9112 7.1 as the table of its grammar, and the
  proof holds the reader to it row by row. The count below is from
  before those. 23 are theorems
  quantified over all inputs (chunking never changes a parse; a refused message is never
  revived; a field is known by its bytes, and every framing ambiguity
  a request is smuggled with is refused in every message state; no
  request target opens a path outside the root, a dotfile or a name
  with a control byte), and two more cover all 256 bytes by exhaustion;
  70 are closed instances -- RFC vectors, smuggling vectors run through
  the reader, route tables,
  specific paths, literals proved equal to their builder -- which are
  test vectors the compiler recomputes and so cannot rot.
- **`world.bend`, `conform.bend`, `mutants.py`** -- the connection
  and accept loops are written over an effect interface and run, in
  `world.bend`, against a scripted peer; their safety properties (the
  last act, reply order, refusal, the buffers' bounds, the head's
  deadline, a stopped peer let go, the accept loop staying up) are
  laws in `PROOF.bend`. `conform` checks the real effects keep the
  contracts the model assumes; `mutants.py` checks the laws refuse
  nine broken loops, and `frame_sim` alone (every rule-by-rule law
  removed in a scratch copy) six broken framings: TE.CL, a wrapping
  chunk-size, a bare LF in chunk framing, `chunked, identity`, HTTP/1.0
  kept alive unasked, and a spec mutant. README, "The world".
- **`check.c`** -- 49 behavioural cases over a socket for any server
  (97 with files, WebSocket and the log), plus the connection limit and
  stopping. Built with `-DCHECK_TLS` it swaps its own socket calls for
  a TLS session and **runs the same cases over the encrypted wire**.
  All pass on both.
- **`fuzz.c`** -- the same random bytes, cut at the same random points,
  into the engine and into `control.c`, demanding byte-identical
  answers including closes, now with HTTP/1.0 and chunked streams in
  its generator. Thousands of rounds clean. It found two real faults on
  its first run, both in the C twin.
- **`prof.sh`** -- gdb stack sampling under load. It is a gate in the
  sense that it settles arguments: it is the only reason the right
  thing got optimised.

`.github/workflows/http.yml` runs the laws, the build, every check mode
plain and over TLS, 500 fuzz rounds and a shared-port smoke, and keeps
the binary.

## The numbers, and how to reproduce them

One 4-core Xeon at 2.8 GHz, `--threads 1`, 32 keep-alive connections,
medians of three.

| | Bend | C control |
|---|---|---|
| pipeline 1 | 80,052 req/s | 155,162 |
| pipeline 8 | 128,028 req/s | 852,207 |
| peak RSS under load | 3.5 MB | 5.8 MB |
| 10,000 live SSE streams | 6.8 MB, 0.37 KB each, 1.07 s CPU per 6 s | |
| arriving, to 8,000 held | 23-25 us per connection, flat | |
| three processes, `--shared`, pipeline 8 | 385k req/s | |

**Measure with `LOAD_SPIN=1` or the numbers are wrong.** A client that
sleeps between replies charges the wake-up to the *server's* `send` on
loopback, and the slower the server the more its client sleeps -- a
loop that punishes exactly what it measures. That artefact understated
this server by half for most of its development. `load.c` takes
`LOAD_SPIN=1` to never sleep.

## What is unfinished, and what it cost

**`demos/io_resp` works.** `PROOF.bend` there checks 23 laws, including
the nested arrays that HTTP never needed, and CI now runs it.
`main.bend --check-only` passes in about a second, and the built server
answers PING, SET and GET. The earlier "hangs the checker" was `bend
main.bend` without `--check-only`: it checks, then runs the server.

**`bend-wire` is extracted** (`wire/`, its README). The reader kit
(`wire/reader.bend`) holds feed, feed_buf and their laws -- chunking,
refusal, the block walk is the byte machine, any cut into reads --
proven once for every step function and state type; HTTP, its
WebSocket reader, RESP and CSV state them as one-line instances and
prove only their obligations (a move lands where its bytes stepped one
at a time do; a refused state is a fixed point). The connection loop,
the writer, the budgets, the accept loop and the model of the world are
`wire/loop.bend` and `wire/world.bend`, with the world's laws proven
there over the protocol's hooks; this engine's world laws are those
laws at its hooks, and `mutants.py` breaks `wire/loop.bend`. RESP's
server went from 121 lines of loop shape to a 36-line planner and its
hooks.

**Not done at all:** HTTP/2 (needs TLS, which now exists, then HPACK
with round-trip laws and `h2spec` as the gate); `TCP.send_vec`, which does not earn its place
until replies are flat buffers.

## The upstream bugs

`UPSTREAM.md` beside this file states three, each with the measurement
that found it and a branch that fixes it. In short: sockets corrupt
every byte over 0x7F *and change the length while doing it*, which is a
framing bug and not a missing feature; the poller's pass costs what is
waiting, so accepting n connections costs O(n^2) and 8,000 does not
finish in 150 seconds (the HTTP ramp; a minimal server holds 8,000 in
4.3 s and 16,000 in 31 s, quadratic all the same); and the listen
backlog is 16.

A fourth, a name collision that seemed to loop the checker, did not
reproduce and is withdrawn in `UPSTREAM.md`.

## What I would do next, in order

1. **Open the three upstream pull requests**, byte pair first and
   alone -- it is a correctness bug, it is small, it has a test, and it
   unblocks every non-text protocol.
2. **Reduce the checker hang** to a minimal file and file it.
3. ~~Extract `bend-wire`~~ (done: `wire/`). Still open: propose
   `foldl_split` to canon's `base.bend`, where a theorem about
   `List.foldl` belongs.
4. Then HTTP/2, on top of the TLS that now exists.

## Three things that are easy to get wrong here

- **A stale process ruins a measurement.** Twice, numbers were taken
  against a server that was still running from a previous test, and
  once a runaway `bun` from the checker hang skewed everything for an
  hour. Check with `pgrep` before trusting a number.
- **`pkill -f <pattern>` matches its own shell** and kills the script
  running it. Use `pkill -x <exact-name>`.
- **The connection limit is 1024 by default**, so a ramp or a
  stream-holding test past that needs `--max-conns 20000`. Two
  measurements in this work "failed" until that was noticed; the
  feature was working.
