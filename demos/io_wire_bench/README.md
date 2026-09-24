# The wire bench: a byte list against Bytes

Two copies of one HTTP-shaped server. Each reads what a connection
sent, cuts every whole head at CR LF CR LF, answers `GET /health` with
a JSON reply built out of pieces (and anything else with a 404), and
sends the replies of one read in one send. The only difference is the
wire's unit:

- `list.bend`: `List<&2, U32>`, one cell per byte, through
  `TCP.recv_bytes` / `TCP.send_bytes`, the way the engine is written.
- `buf.bend`: `Bytes()`, one packed block, through `TCP.recv_buf` /
  `TCP.send_buf`, with `Bytes.find`, `Bytes.slice`, `Bytes.starts_with`
  and `Bytes.concat` where the list side walks cells.

    sh demos/io_wire_bench/run.sh 5 2 3   # secs, server core, client core

It builds both, pins each server (`--threads 1`) to one core and the
engine's `load.c` (`LOAD_SPIN=1`, 32 connections) to another, and
prints pipeline 1 and 8 and the server's peak RSS.

## What it measured

A 4-core Xeon, load average 2-3 from other work, medians of three 5 s
runs. A request is 83 bytes and a reply 106, so 189 wire bytes per
request; ns/byte is server-core time per wire byte (the server core is
saturated), syscalls included.

| | list p1 | Bytes p1 | list p8 | Bytes p8 |
|---|---|---|---|---|
| req/s | 58,916 | 174,894 | 63,766 | 635,587 |
| ns per wire byte | 89.8 | 30.3 | 83.0 | 8.3 |
| peak RSS | 2.8 MB | 2.5 MB | | |

The C control (`../io_http_engine/control.c`) on the same cores:
222,553 p1, 1,151,331 p8.

Heap per byte, apart from sockets: a 16 MiB file read whole and held
(`File.read_bytes` against `File.read_buf`, `--threads 1`), peak RSS
less the 16 MiB read buffer and a 2.4 MB idle runtime:

| | peak RSS | heap per byte | time |
|---|---|---|---|
| `List<&2, U32>` | 396 MB | 23.0 B | 334 ms |
| `Bytes()` | 35 MB | 1.0 B | 24 ms |

The list's 23 bytes are a cons cell (two 8-byte words) plus the heap's
size classes; the block's one byte is its 1-byte cells. Nothing else
in the program changed.
