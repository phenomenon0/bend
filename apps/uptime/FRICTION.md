# FRICTION: building bend-uptime on net/

What it was like to write a real app on `net/` as a user: 1,292 lines of
Bend in 171 defs, a foreign effect, 3 dashboard files and a check
script. It works (13 / 13 checks native, 12 / 13 on the JS lane; 13 / 13 on both
since the fixes noted under 1 to 3). The
list is ranked by what it cost: wrong behaviour first, then hours, then
annoyance. Each entry: what I tried, what happened, the workaround, and
what should change.

The net/ items (5, 7, 9, 10, and 8 in part) are fixed in c4904803 and
the app rewritten on the new API: 1,248 lines of Bend in 165 defs
before, 1,130 in 154 after (118 fewer; api.bend 182 to 129, model.bend
483 to 417, main.bend 138 to 131, env.bend 94 to 102 for the shared
client session). check.py: 13 / 13 native and on the JS lane.

## 1. `Bool.pick` evaluates both arms, and it is the only `if`

**Tried.** Bend has no `if`; `Bool.pick(A, c, a, b)` is what the library
itself uses everywhere, so the replay picked the results or the ops
parser with it:
`Bool.pick(M.Store, U32.is_eq(kind, 0), results.apply.at(st, parse.line(line)), ops.apply.at(st, parse.line(line)))`.

**What happened.** Both arms run. Every log line was parsed twice and
run through the monitor checks for nothing. A restart with 100,000 log
lines took **19.1 s**. The same code with a `match` on a helper's `Bool`
parameter takes **3.9 s**. Nothing warns. It also forces `+` onto every
variable both arms mention: `t (consumed more than once)` came up six
times in `model.bend` for values only one arm uses (`hours.sum`,
`without`, `find`, `hours.add`, `hist.push`, `cfg.one`).
`hist.push` would have copied 500 probes on every probe.

**Workaround.** A helper def per branch point that matches on its `Bool`
parameter (`apply.kind`, `apply.some`, `hist.cut`, `wait.slice`, ...).

**Change.** An `if c: ... else: ...` statement that lowers to a `match`
(lazy, and each arm checked for affinity on its own). Failing that, make
`Bool.pick` a template (`~a`, `~b`) so only the chosen arm is built, and
say in GUIDE.md that it is strict until then.

**Fixed** in 5a4e4019 (and 2f49eddb). The compiled lanes (C, JS, and the
interpreter's IO programs, which run as JS) lift a `Bool.pick` whose arms
are not both cheap into a def of its own that matches on the condition,
the helper written above, so only the chosen arm runs and the other's
values drop with its match arm; the checker's view is unchanged (the `+`
it asks for stays). A pure `main` in the interpreter was lazy already.
`tests/base/bool_pick_lazy.bend` and `tests/io/bool_pick_lazy.bend` pick
past a loop that never ends. The replay, 100,000 lines (11 MB), 4-core
Linux box under a load of about 12: the `Bool.pick` line above 8.1 and
8.5 s before, 2.3 and 2.1 s after; the `match` helper 2.2 s either way.

## 2. The JS lane ignores SIGTERM, for every net/ program

**Tried.** `check.py --js`: `bun bend2/main.ts apps/uptime/main.bend -- ...`,
then SIGTERM.

**What happened.** The process never stops. The server never prints
`bend-net: stopping`. The probe loops kept probing: a 120 s soak logged
6,797 probes of 6,000 because the JS process ran on for the 15 s after
TERM until it was killed. `net/examples/hello.bend` and
`chat_server.bend` behave the same (`still running after 10 s`). The
cause is in `comp.ts`: `io_run` is a synchronous `for (;;)` that blocks
in `io_wait` (poll through FFI) and never returns to bun's event loop,
so the `process.on("SIGTERM")` that `effs/signal_pending.js` installs
can never run.

**Workaround.** None in the app. check.py reports it as the one failure
on the JS lane.

**Change.** In `signal_pending.js`, catch the signal through FFI (a
`sigaction` that sets a flag in shared memory, or `signalfd` polled
beside the sockets), or have `io_wait` yield to the event loop
(`await`) between polls. `net/check.py` should run its SIGTERM case on
the JS lane too.

**Fixed** in ce884a5d. `effs/signal_pending.js` now catches the signal in
C, as the C lane does: bun:ffi's `cc` builds a handler that counts, the
first time a signal is asked for (`process.on` stays the fallback where
cc cannot build). Nothing runs on the request path. `bun hello.js` exits
0 in 0.8 s after SIGTERM with `bend-net: stopping` (was still running 10 s
later); wrk on it (one connection, eight 8 s runs on a loaded box) gives
a median of 322 us of server CPU a request before, 295 after, within the
noise. `tests/io/signal_self.bend` sends the process its own signals
mid-run. `check.py --js`: 13 / 13, SIGTERM exit 0 in 0.36 s.

## 3. No wall clock, no dates

**Tried.** Every probe needs a timestamp that survives a restart, for
the log, for the 24 h window and for "last checked".

**What happened.** `IO.now()` is `CLOCK_MONOTONIC` (ms since boot in C,
`performance.now()` in JS). Base has no epoch time and no date
formatting. (One way out without foreign code: write a file and read
back its mtime from `File.get_under`, in seconds.)

**Workaround.** A foreign effect, `Clock.wall` (`clock.c`: `clock_gettime(CLOCK_REALTIME)`,
`clock.js`: `Date.now()`), per guide/EFFECTS.md. That works, but
EFFECTS.md says the C side "tracks the exact compiler version ... no ABI
promise", so an ordinary app now carries runtime internals (`Term`,
`io_eff`, `CID_CLOCK_WALL`). The ISO 8601 dates are Hinnant's
`civil_from_days` by hand (`clock.bend`, 30 lines).

**Change.** `IO.wall() -> IO(Nat)` (ms since the epoch) in Base, beside
`IO.now`. Also `Time.iso(ms) -> String` and `Time.parse_iso`. And say in
GUIDE.md that `IO.now` is monotonic.

**Fixed** in c8a52987. `IO.wall() -> IO(Nat)` (ms since the epoch) is in
Base beside `IO.now`, which the guide now calls monotonic, and
`bend2/time.bend` (`import ../../bend2/time.bend as Time`) has
`Time.iso(secs)`, `Time.iso.ms(ms)`, `Time.http(secs)` (IMF-fixdate) and
`Time.date` / `Time.day`, on the engine's proven calendar. `clock.c`,
`clock.js` and `clock.bend` are gone; the app is no longer flagged for
foreign code (`start.all`). No `Time.parse_iso` yet.

## 4. The match and let rules turn every branch into a def

**Tried.** Ordinary functional code: destructure a call's result, match
on a computed value, let-bind before a match, two functions calling each
other.

**What happened.** Each is refused. 171 defs for 1,292 lines. About a
third exist only to satisfy these rules.
- `(t, s) = record.in(ms, name, p)` gives
  `a parameter or field scrutinee (a match cannot scrutinize a computed value: give it its own def)`.
  It is a let, not a match: the message names the rule, not the line's
  form.
- A `(st, carry) = sc` before `match empty:` gives
  `a match on a parameter or field (this name is a def or a consumed binder: give the value its own def)`.
  Here `empty` is a parameter, so the message is wrong for this case. The
  real rule ("a let may not precede a match on a parameter") is in
  GUIDE.md, but the error does not say it.
- Using a def above its definition gives `expected : a defined name /
  observed : wrote.why`, the same message as a typo. This hit four
  times. GUIDE.md says only that templates must be declared above.
- Mutual recursion (`cfg.monitors` and `cfg.go`) gives the same "a
  defined name" message. Every loop that needs a helper becomes CPS by
  hand: `probe.loop` passes `nx => probe.loop(k, ...)` down to
  `probe.step` to `probe.run`, `slurp.go` passes `ff => a => slurp.go(k, ff, a)`,
  and so on.
- A `+` on a `Nat` pattern is `1n+(+k)`. I found it in `net/url.bend`;
  GUIDE.md does not have it.

**Change.** Allow a destructuring let of any expression (desugar to a
fresh def). Allow let before match. Resolve names in any order within a
file. Give each case its own error message: "defined below its use",
"mutual recursion is not allowed: pass a continuation", "let before
match". Put the `1n+(+k)` form in the syntax reference.

## 5. Middleware and `static` do not compose with WebSocket routes

**Tried.** `~Server.logged(~Server.secured(~Server.recovered(~app)))`
around the whole app, as the guide shows.

**What happened.** A WebSocket route means `WsServer.serve.with(~E, ~routes, env, cfg)`,
which is `Server.serve.routes`: it takes a route table, not a handler,
so there is no place to wrap. `Server.static(prefix, root)` builds its
handler inside, so it cannot be wrapped either, and a dashboard served
by it gets no log line and no security headers.

**Workaround.** Each route wrapped by hand, `+r => mw(r, list(e, r))`
with `mw = logged.around(r, secured.around(recovered.around(io)))` (the
lambda must take `+r` because `logged.around` reads it twice). For the
files, the undocumented `Server.static.at(root, r)` under
`Server.get("/*", ...)`.

**Change.** `Server.wrap(~mw, routes)`, which maps a
`Handler -> Handler` template over every `Route` (and leaves `Sock` routes
alone). Or give `serve.routes` an `~around` parameter. Document
`static.at`, or add `Server.static.with(~mw, prefix, root)`.

**Fixed** in c4904803. `Server.wrap(~mw, routes)` takes a middleware's
`.around` form (or several nested) and puts it around every route of a
table: plain routes, `Server.static`, and the Sock routes too (a
`WsServer.ws` accept logged as its 101, a `Stream.get` pour's head given
the middleware's fields). `~Server.logged.around` passes as it is.
`Server.static` is wrapped like any route, so `static.at` is no longer
needed (it is documented, in guide/net/SERVING.md, for a route of your
own). `wrap_pats` in net/LAWS.bend: a wrapped table keeps every route's
methods and pattern. api.bend's routes went from seven hand-wrapped
lines, two wrapper defs and the `Res`/`recovered` plumbing to one
`Server.wrap(~mw, [...])` and a two-line `mw`.

## 6. Persistence: no seek, rename, mkdir or fsync; replay is slow

**Tried.** An append-only NDJSON log, replayed at start. A tail-only
read for big logs. Compaction by writing a snapshot and renaming it into
place.

**What happened.**
- No `mkdir`: `--state` is a path prefix whose directory must exist.
- No `rename` or `fsync`: no atomic snapshot and no rotation, so the log
  grows forever (1.47 MB for 240 s of 50 monitors at 1 s: about 530 MB
  a day).
- No seek for `File.read_buf`. `File.read_at` takes a `U32` offset (4 GiB
  at most) and answers `List<&2, U32>` (a cell per byte), so reading only
  the tail is not practical.
- Replay speed, measured on 100,000 synthetic lines (11 MB): read 50 ms,
  `String.split_on` 143 ms, `Json.parse` 1,259 ms (12.6 us a line), and
  the store updates the rest: 3.9 s in all, about 26,000 lines a second.
  A day of 50 monitors at 1 s is 4.3 M lines, about 165 s before
  `/health` answers.

**Workaround.** Two logs (ops apart from results, so the small one can
be read whole). The whole results log is replayed, a MiB at a time,
with the cut line carried between chunks. The pure fold keeps memory
flat.

**Change.** `File.rename`, `Dir.make`, `File.sync`, `File.seek(f, Nat)`
and `File.read_buf_at(f, off: Nat, max)` answering `Bytes()`. With those
an app can snapshot and truncate. A line reader (`File.lines`) would
help too, or `File.fold_lines` beside `File.fold_text`.

## 7. The client's timeout belongs to the session, not the request

**Tried.** One pooled session for all probes, each probe with its
monitor's `timeout_ms`.

**What happened.** `Client.fetch(ss, req)` takes no options, and
`Client.Req` has no timeout. The timeout is `Client.opts` fixed at
`Client.session(o)`.

**Workaround.** One session per monitor (`probe.start`), so pooling
happens only within a monitor. The timeouts are exact: the 1.5 s
`/slow` target at a 500 ms timeout is cut as `timeout` (check.py
asserts under 1.2 s).

**Change.** `Client.fetch.with(ss, req, opts)`, or
`Client.req.timeout(r, ms)` that the exchange honours, beside the
session's default.

**Fixed** in c4904803. `Client.fetch.with(ss, req, o => ...)`: the
request's options are made from the session's (connect, timeout,
max_body, redirects, gzip; `ca` stays the session's, whose pooled
connections were verified under it). It is `fetch` on the same pool with
other options, so `pool_clean`, `redirect_cap` and `redirect_creds` hold
as proven. The app now keeps one session, in its `Env`, and each probe
passes its monitor's timeout (`probe.opts`); `start` went from a session
per monitor (6 lines, and a `Client.close` on each way out of the loop)
to 2 lines. The 1.5 s target is still cut at 500 ms as `timeout`.

## 8. A WebSocket handler cannot wait on its socket and a channel at once

**Tried.** Push each probe to every dashboard the moment it lands.

**What happened.** The Hub's model is polling: a member loops on
`Ws.recv_for(c, slice)` and calls `WsServer.relay(me, c)` between
slices. A push waits up to one slice (100 ms here, 50 ms in
chat_server), and each open dashboard wakes the loop 10 times a second
even when nothing happens. `publish` appends to each inbox with
`List.append` (O(inbox) per message, 1,024 at most). A dashboard only
listens, but it still needs the full `heard`/`talk` loop copied from
chat_server (35 lines).

**Workaround.** The chat_server loop, copied, with 100 ms slices.

**Change.** `WsServer.broadcast(hub)`: a route that only pushes the
hub's messages and returns on close. Underneath, a
`Ws.recv_or(c, chan, ms)` that parks on both. Make the inbox a queue.

**Half fixed** in c4904803. `WsServer.broadcast(hub, c)` is the listener:
`WsServer.accept("", c => WsServer.broadcast(E.hub(e), c))` joins the
room, relays what is published, and leaves when the client closes, so
the 35 copied lines (`heard`, `talk`, `member`) are gone. It still waits
in slices of 50 ms: `Ws.recv_or` is not cheap. `IO.within` (effs/within.c)
races one act against a deadline and lets the loser run on, its answer
dropped; racing a `Chan.recv` that way would take a message and drop
it. What it takes: an effect that parks one computation on a socket's
readability (TLS's buffered bytes counted) and a channel's value at once,
and on either wake withdraws the other wait (the channel's waiter queue
and the fd's park both need a removal), in C and in JS; then
`Ws.recv_or` splits the frame reader into "wait" and "read". The inbox
is still a list.

## 9. JSON ergonomics

**Tried.** Read typed fields from a config, a request and a log line,
and write numbers that are not `U32`.

**What happened.**
- `Json.num` takes only a `U32`. An epoch-ms `Nat` needs `J.Num{Nat.show(t)}`,
  reaching into power/json_value's constructor. A percentage with two
  decimals (99.95) is fixed-point formatting by hand (`percent`): there
  is no `Json.f64` with a precision (`F64.from_nat` and a division give
  the shortest round-trip text, not two places).
- There are no typed getters. I wrote `field.str`, `field.num` (missing
  vs wrong type vs out of range), `flag.of` and `u32.of`: 60 lines.
  `Json.get.str` silently answers a number's text for a string field.
- Reading a `Nat` back means
  `Maybe.bind(&2, Bytes(), Nat, Json.get.str(j, "t"), Nat.read)`.
- Validation with every reason (not the first) is hand-rolled: `errs.one`
  and `val` over a `Result` per field.

**Change.** `Json.nat`, `Json.dec(n, places)`, and
`Json.get.u32/nat/bool/arr/obj(j, key) -> Result<&2, &2, Bytes(), A>`
with messages like "interval_ms must be a number". Also a small
`Check` applicative that collects every failure.

**Fixed** in c4904803. `Json.get.str/u32/nat/i64/f64/bool/arr/obj(j, path)`
answer `Json.Got(A)` (`Result<&2, &2, Bytes(), A>`): the value, or
"name is required", "timeout_ms must be a number", "expect must be a
whole number from 0 to 4294967295". `get.str` no longer takes a number.
A path is keys and array indexes joined by `.` (`"monitors.0.name"`).
`Json.or(U32, j, "interval_ms", 60000, Json.get.u32)` defaults a missing
field only; `Json.fails` keeps every reason (the `Check`, as a fold);
`Json.errors(400, whys)` is the `{"errors": [...]}` response; `Json.nat`
and `Json.dec(n, places)` write numbers. Vectors for each in
net/LAWS.bend, and seven mutants of the getters, all refused. model.bend
lost `field.str`, `field.num`, `field.num.read`, `errs.one`, `flag.of`,
`nat` and the hand-formatted `percent` (483 to 417 lines); api.bend lost
`strs` and `errors`; reading a `Nat` back is `Json.get.nat(j, "t")`.
net/examples/signup.bend shows a 400 with every reason.

## 10. Flags: the list is consumed by each read

**Tried.** `--config`, `--state`, `--web` and `--webhook`, plus
`Server.args`.

**What happened.** `Server.flag(xs, ...)` takes `xs: List<String>` (`&1`)
and consumes it, so `main` calls `IO.args()` five times (a1 to a5).
NETWORKING.md does say so ("ask `IO.args()` once for each"). Unknown
flags pass silently, there is no `--help`, and a mistyped `--prot 80`
serves on 8080.

**Change.** Take `List<&2, String>` (the list is `Data`; the library's
own `strs` converts it), or add `Flags.of(xs) -> Flags` (Data) with
`Flags.str/u32/bool` and a check that refuses flags it never read.

**Fixed** in c4904803. `Server.argv(own)` asks `IO.args()` once and
answers `List<&2, String>`, which `Server.flag`, `flag.num`, `flag.on` and
`Server.args` read by reference. `own` declares the program's flags as a
usage line does (`["--config FILE", "--state PREFIX", "--web DIR",
"--webhook URL"]`; a value named `N` must be a number). An unknown flag,
a flag without its value, a number that is not one or a stray word ends
the program, exit 2, with the reason and the usage line:
`./uptime --prot 80` says `unknown flag --prot` and `usage: [--config
FILE] ... [--port N] ...`. `argv_vectors` and four mutants in net/. main
went from five `IO.args()` to one line.

## 11. Quantities: `&1` and `&2` lists, `+` everywhere

**What happened.** `List.map` is only for `List<&1, A>`:
`List.map(~Bytes(), ~J.Json, ~Json.str, whys)` gives
`expected : List<&1, String> / observed : List<&2, String>`, and every
JSON list is `&2`. I wrote `strs`, `probes.json`, `mons.json` and
`prefixed` by hand. WsServer's routes are `List<&1, Server.Route>`, while
json_api's are `List<Server.Route>`. The two spellings of the same type
make copying between examples a guess. Every `Data` parameter used
twice needs a `+`; the errors are clear (`x (consumed more than once)`),
but they come one at a time, a check run (1 to 11 s) per `+`.

**Change.** `List.map` generic in the quantity, like `List.length`. The
checker could report every missing `+` in a def at once, and suggest
the `+`.

## 12. U32 against Nat

**What happened.** Durations are `U32` in the client and in `IO.sleep`,
but `IO.now` answers a `Nat`. Latency is
`U32.from_nat(Nat.min(Nat.sub(t1, t0), 4294967295n))` (a `ms.between`
helper). A Nat literal stops at `4294967295n`: testing
`iso(951782400000n)` gives
`expected : a nat literal up to 4294967295n (got 951782400000n)`, so a
test date is `Nat.mul(951782400n, 1000n)`. `Json.num` is `U32` only
(see 9).

**Change.** Nat literals to 2^48 (the runtime's own bound), and
`IO.sleep`, the timeouts and `Json.num` taking `Nat` or overloaded.

## 13. Compile and check times

Measured on a 4-core Linux box shared with other jobs (the second number
is under a load average of about 11):
- `--check-only`: 4.8 s (11.2 s).
- `-o uptime.c`: 24 s (55 s). The C is 4.7 MB, 177,151 lines.
- `-o uptime`: 78 s (118 s). The binary is 3.6 MB.
- The JS lane (`bend main.bend`): 16.8 s from start to `/health`,
  because it checks and emits on every run, and 760 MB RSS for the
  checker in-process.
- For comparison, `net/examples/json_api.bend -o`: 35 s.

A one-line change costs a minute and a half before it can be run.
There is no incremental build and no cache of the library's C. The
edit-and-check loop (4 to 11 s) is fine. The edit-and-run loop is not.

**Change.** Cache the emitted C per module (net/ and wire/ do not
change between my builds), or a `-O0` debug build. The JS lane could
cache the emitted JS by content hash.

## 14. `secured` forbids the inline dashboard

**What happened.** The brief wanted one HTML+JS file.
`Server.secured` sets `default-src 'self'`, which refuses inline
`<script>` and `<style>`. `net/examples/chat_server.bend` serves an
inline-script page, but it does not use `secured`, and nothing says the
two don't mix.

**Workaround.** `index.html`, `app.js`, `app.css`. The WebSocket falls
under `connect-src` via `'self'`, which covers `ws:` to the same host in
current browsers (not in older Safari).

**Change.** A sentence in NETWORKING.md, and `Server.secured.with(csp)`
so an app can allow a hash or `connect-src ws:`.

## 15. Shutdown of your own computations is up to you, and undocumented

**What happened.** NETWORKING.md says what SIGTERM does to connections.
It says nothing about computations the app spawned. They keep the
process alive ("the program ends when every computation is done",
GUIDE.md), so each probe loop must poll `IO.signal_seen(15)` itself.
Its difference from `signal_pending` (which the server's accept loop
consumes) is explained only in `effs/signal_pending.c`. I did not test
whether `grace` (5 s) cuts a loop that never looks. Loops that sleep
must sleep in slices, or shutdown waits out the longest interval.

**Workaround.** Every loop checks `IO.signal_seen(15)` and sleeps at
most 250 ms at a time. Native: exit 0 in 0.27 s.

**Change.** `IO.sleep_or_term(ms) -> IO(Bool)`, or `Server.stopping()`,
and a paragraph in NETWORKING.md: "background work beside the server".

## 16. Docs gaps (things NETWORKING.md did not tell me)

- That `IO.spawn` and `IO.fork` exist and are the way to run work beside
  `serve`. Concurrency is in GUIDE.md, not in the networking guide,
  where a server app needs it.
- `Server.static.at`: needed to wrap static files (5).
- That a `Chan(File)` of one is the way to share a log between
  computations, since a `File` is affine and an env must be `Data`.
- That `recovered` catches only a `Fail` the handler returns. There are
  no exceptions, so "recovered" does not mean what it means in other
  frameworks.
- That `Client.fetch` has no per-request options (7).
- That a `WsServer.serve.with` app cannot take the whole-app middleware
  shown in the same guide (5).
- `Bool.pick` is strict (1, now fixed), `IO.now` is monotonic (3, now said), `List.map` is
  `&1` only (11).

Since c4904803 the networking guide is a tour (`bend guide networking`)
and pages under guide/net/. They cover `IO.spawn` beside the server and
SIGTERM for your own loops, a `Chan(File)` shared as a lock, that
`recovered` catches only a `Fail` (no exceptions), that `secured`'s CSP
refuses inline scripts (14), `Server.static.at`, `Client.fetch.with` and
`Server.wrap` over WebSocket routes.
- Where a file's own IO effects may live, and that an app with foreign
  code is flagged in every check: `All terms check, but 2 defs rely on
  unsafe or foreign code: start.all, main`. `start.all` only calls
  `P.start` (which spawns), so why it is named is unclear.

## 17. Smaller things

- `Map` is keyed by `String` and hands itself back from `get` and
  `has`. For 50 monitors, a `List<&2, Mon>` with linear search was
  simpler. Every lookup is O(n) with `String.eq`.
- An accessor per field (`spec.name`, `spec.url`, ... 15 defs of
  4 lines) because there is no field syntax. Records want `s.name`.
- `Server.flag`'s default for `--web` is relative to the process's cwd,
  and there is no way to find the binary's own directory.
- `WsServer.accept("", run)`: an empty string means no subprotocol. A
  `Maybe` would say it.
- `Http.Response{204, Nil{}, Http.BBody{""}}` for a 204: there is no
  `Http.empty(status)`.

## What worked well

- **Concurrency is real.** A loop per monitor with `IO.spawn` on the one
  event loop, and 50 monitors at 1 s cost 1.2% of a core. The start of
  each probe lags its slot by p99 11 ms, and the gap between probes is
  1000 ms at p50 (p1 992, p99 1008). Sequential probing was never
  needed.
- **The client's limits hold.** A refused port is `connection refused`
  in 1 ms. A 1.5 s target at a 500 ms timeout is cut as `timeout`.
  `NetError` by kind made the `err` field free. Pooling per session
  works.
- **Memory is flat.** RSS goes from 7.1 to 12.3 MB and stays there once
  the history cap is reached (2,100 probes per monitor at 200 ms).
- **SIGTERM** (native) is clean: 1001 to the dashboards, the loops end,
  exit 0 in 0.27 s.
- **The Hub** needed no changes. `Json.body` and `Json.refused` made the
  400s easy.
- **Error messages** always point at the right line with the context's
  types. Most were fixed in one edit once I knew the rule.
- Once it checked, the first native run passed all 13 checks: the
  checker let no logic bug through. (check.py's own config bug, a
  timeout over the interval, was caught by the app's validation.)

## Where apps/ should live

`apps/` is not in AGENTS.md's map, and `gates/repo.ts` now allows
`apps/uptime/*`. The alternatives:
- `demos/uptime/`: `demos/` is "one dir per demo", but its caps (4,000
  ttok for `.md`, 8,000 for `.py`) are too small for FRICTION.md and
  check.py, and a demo is a showcase, not a user's app with a test and
  a report.
- `net/examples/`: holds single files, so no.

I propose keeping `apps/<name>/` as a new top-level dir: "applications
built on the libraries as a user would, each with its check.py and its
FRICTION.md". That means a line in AGENTS.md and REPO_MAP.md (not made
here), and a gate that builds each app and runs its `check.py`, as
`net/check.py` does for the examples.
