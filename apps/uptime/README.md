# bend-uptime

A small self-hosted uptime monitor (a mini Uptime Kuma) written in Bend
on `net/`, the way a user of the library would write it. Monitors come
from a JSON config and the API, each is probed on its interval, results
go to an NDJSON log that is replayed at start, a JSON API and a
WebSocket feed serve a static dashboard, and up/down transitions POST to
a webhook.

```bash
bend apps/uptime/main.bend -o uptime            # about 80 s: see FRICTION.md
./uptime --config monitors.json --state data/uptime --port 8080 --host 127.0.0.1
open http://127.0.0.1:8080/
```

```json
{"webhook": "http://127.0.0.1:9000/hook",
 "monitors": [{"name": "api", "url": "https://example.com/health", "interval_ms": 30000,
               "timeout_ms": 5000, "expect": 200, "body": "ok"}]}
```

`interval_ms` (200 to 86400000, default 60000), `timeout_ms` (50 to 60000,
at most the interval, default 5000), `expect` (100 to 599, default 200)
and `body` (a substring the body must hold, default none) are optional.
A name is 1 to 64 of `A-Z a-z 0-9 . _ -` (it goes in a path).

Flags: `--config`, `--state` (a path prefix; its directory must exist:
Bend has no mkdir), `--web` (the dashboard's directory, default
`apps/uptime/web`), `--webhook` (wins over the config's), and every
`Server.args` flag (`--port --host --idle-ms ...`).

## The API

| | |
| --- | --- |
| `GET /api/monitors` | every monitor: its spec, `state` (`up`, `down`, `pending`), `last` probe, `uptime_24h` (a percentage with two decimals, null before a probe), `checks_24h` |
| `GET /api/monitors/:name/history?limit=` | its probes, newest first (`limit` 1 to 500, default 50; at most the last 500 to 1000 are kept) |
| `POST /api/monitors` | a monitor added: 201; 400 `{"errors": [...]}` with every reason; 409 when the name is taken |
| `DELETE /api/monitors/:name` | 204, or 404 |
| `GET /live` | a WebSocket: every probe as JSON text as it lands |
| `GET /health` | `{"ok":true}` |
| `GET /*` | the dashboard (`web/`) |

A probe is `{"name","t" (ms since the epoch),"at" (ISO 8601),"up","ms"
(latency),"code" (0: no response),"err" ("" when up; "timeout",
"connection refused", "status 503, expected 200", "body lacks ..."),
"lag" (ms it started past its slot)}`. The webhook gets `{"event": "up" |
"down", "name", "url", "probe"}` on an up to down or down to up turn
(not on the first probe), tried three times a second apart until a 2xx.

## How it works

    clock.bend  Clock.wall (a foreign effect: clock.c, clock.js) and ISO dates
    model.bend  the types, their JSON both ways, the checks, the store's pure updates
    env.bend    what is shared: the store behind a channel of one, the hub, the logs
    files.bend  whole-file reads, the logs replayed a MiB and a line at a time
    probe.bend  a loop per monitor, the webhook
    api.bend    the routes, the live feed, the middleware
    main.bend   flags, config, replay, start
    web/        index.html, app.js, app.css
    check.py    the checks and the soak

**Concurrency.** `IO.spawn` starts a computation and the runtime's one
event loop interleaves all of them with the server's connections, each
parked on its socket, sleep or channel. So each monitor has its own loop
and probes run concurrently: a slow target holds only its own loop. No
monitor waits for another. A loop keeps slots on the monotonic clock
(`due`, `due + interval`, ...), skips the slots a slow probe overran,
sleeps in slices of 250 ms so SIGTERM ends it quickly, and ends when its
monitor is deleted. Each loop has its own pooled `Client.session`,
because a session's options carry the timeout (connect and exchange are
both the monitor's `timeout_ms`; redirects are not followed).

**State.** The store is a `Chan(Store)` of one, used as a lock, as in
`net/examples/json_api.bend`. Each monitor keeps its last 500 to 1000
probes and 25 hourly buckets of (up, all). The 24 h uptime is the sum of
the current hour's bucket and the 23 before it.

**Persistence.** `<state>.results.ndjson` gets every probe and
`<state>.monitors.ndjson` every add and delete from the API. At start
the config's monitors are the store, the ops are replayed over them (so
a deleted config monitor stays deleted), and the results rebuild each
monitor's state, history and buckets. The logs are never rotated.

**Shutdown.** SIGTERM: the server closes its listener and lets its
connections go, the dashboards get 1001, and every probe loop sees
`IO.signal_seen(15)` within 250 ms, closes its session and ends.

## Measured (Linux, 4 cores, shared with other jobs)

`python3 apps/uptime/check.py --bin ./uptime` passes 13 / 13: the API,
states (refused, timeout, status, body), the live push, both webhook
turns and the retry, history, POST's refusals, DELETE, the dashboard's
headers, SIGTERM (exit 0 in 0.27 s) and a restart that keeps it all.

| | native | JS lane (`bend main.bend`) |
| --- | --- | --- |
| startup to `/health` | instant | 16.8 s (check and emit each run) |
| 50 monitors at 1 s, 240 s | 12,050 probes of 12,001; CPU 1.2% of a core | 6,797 in 120 s (it kept probing after SIGTERM); CPU 10.7% |
| RSS | 7.1 MB, 8.5 MB after 240 s | 760 MB (bun, the checker in-process) |
| 50 monitors at 200 ms, 420 s (2,100 probes each) | 104,864 probes of 105,004; CPU 5.4%; RSS 7.1 to 12.3 MB, flat from 200 s (the history cap) | |
| start lag past the slot | p50 3 ms, p99 11 ms, max 30 ms (1 s); max 65 ms (200 ms) | p50 25 ms, p99 168 ms, max 586 ms |
| gap between probes, 1 s | p1 992, p50 1000, p99 1008, max 1029 ms | p1 869, p99 1146, max 1936 ms |
| restart with the log | 12.6 MB, 113,688 lines: 13.5 s before the fix below; 100,000 lines: 19.1 s, then 3.9 s | 7,475 lines: 24.8 s |
| SIGTERM | exit 0 in 0.27 s | ignored (a runtime bug: FRICTION.md) |

Build: check 4.8 s, the C emitted in 24 s, the binary in 78 s (3.6 MB,
from 4.7 MB of C). The dashboard was not opened in a browser here (none
on the machine); `app.js` is checked for syntax only.

`check.py --soak SECS [--every MS] [--monitors N]` reproduces the table.
