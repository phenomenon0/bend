# bench/net -- what a request costs, counted

wrk on a shared, loaded box moves by a fifth from run to run, so it
cannot see a 2% regression, or tell which commit made one. This harness
counts instead: the instructions the server executes per request
(callgrind) and the syscalls it makes per request (strace), for a fixed
set of requests. The counts repeat to within a few thousandths of a
percent from run to run, whatever else the box is doing.

    python3 bench/net/netperf.py                   # every bench against the pin
    python3 bench/net/netperf.py --only net_hello  # one
    python3 bench/net/netperf.py --reps 5          # and the spread of five runs
    python3 bench/net/netperf.py --wrk 5           # and wrk's req/s, as a hint
    python3 bench/net/netperf.py --pin             # write the medians of three

## How

Each bench starts its server alone (`--threads 1`) under callgrind and
drives it with one client, one keep-alive connection, one request at a
time; each request is sent only once the server sleeps in its poller
again (read from `/proc/PID/task/*/syscall`), so every request takes the
same path through the server: the read that finds nothing, the wait,
the wake, the read, the write. It does this twice, with 100 requests and
with 600, and divides the difference by 500: the server's start, its
first connection and its shutdown are in both runs and cancel. Syscalls
are counted the same way under `strace -f -c`.

| bench | server | request |
| --- | --- | --- |
| engine_health | `demos/io_http_engine` | `GET /health` |
| engine_file_4k | the engine, `--root` | a 4 KiB text file |
| engine_file_1m | the engine, `--root` | a 1 MiB file (sendfile) |
| engine_gzip_hit | the engine, `--root --gzip` | the 4 KiB file, `accept-encoding: gzip` (kept compressed after the first) |
| engine_304 | the engine, `--root` | the 4 KiB file, `if-none-match` its entity-tag |
| engine_206 | the engine, `--root` | the 4 KiB file, `range: bytes=100-199` |
| net_hello | `net/examples/hello.bend` | `GET /` |
| net_json | `net/examples/json_api.bend` | `GET /notes/1` (one note posted first) |
| h2_health | `demos/io_http2` (h2c) | `GET /health`, one stream at a time |

The programs are built into `--bin DIR` (a temporary directory by
default; a binary already there is kept, so `--bin` also measures a
build made elsewhere). The callgrind files stay there (`cg.100.out`,
`cg.600.out`): `callgrind_annotate` on the pair shows where a request's
instructions go.

## The pins

`_pin_/HW.txt` holds the instructions and syscalls per request of each
bench (`--hw NAME`, `linux_x86_64` by default). A count includes libc's
(its memcpy and memchr are picked for the CPU at load time) and is the
code clang emitted, so a pin belongs to one machine and one toolchain;
its first line names them. A bench fails at 2% over its instruction pin
or 0.1 syscalls a request over its syscall pin; a count under its pin is
news, and `--pin` records it.

Uses ports 26000-26099 and kills every process it starts. Needs
valgrind, strace, bun, clang, and Python's h2 package for h2_health.
