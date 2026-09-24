# UPSTREAM: what we found that canon's `main` also has

The living list of every bug, pathology and limitation this project hit
that is also in upstream Bend (`bendlang/bend`, remote `canon`), with a
repro for each and the branch that fixes it, if any.

- **Verified against** canon `main` at `95317d95` (2026-09-24, "A name is
  words joined by dots...", #1042, one commit past 2.0.27's `d3790917`),
  on Linux x86_64 (4 cores), clang 18, bun 1.3.11, on 2026-09-24.
- **Re-verify** with `upstream/verify.sh <canon-checkout> [item...]`, for
  example `git worktree add --detach /tmp/canon canon/main` then
  `upstream/verify.sh /tmp/canon`. It runs every repro in `upstream/` in
  the lanes that apply and prints `REPRO`, `FIXED` or `SKIP` per item and
  lane (about three minutes; ports 29601-29613). Point it at a fix branch to
  see the item turn `FIXED`. For a NOT-REPRO or OURS item, `FIXED` on
  canon is the expected answer.
- **Lanes.** `interp` is `bend F.bend`: a pure `main` runs in the
  checker's normalizer, but an IO `main` runs the JS runtime in-process
  (`Comp.io_run`), so for IO programs interp and JS share one runtime.
  `js` is `bend F.bend -o F.js; bun F.js`, `c` is `bend F.bend -o F; ./F`.
- **Upkeep.** When canon moves: fetch, rerun verify.sh, update the commit
  above and every row whose answer changed; a new find gets the next U
  number, a repro in `upstream/` and a case in verify.sh.
- **Classes.** BUG: wrong behaviour, reproduces on canon. PERF: right
  answer, pathological cost. LIMITATION: by design or missing, worth
  raising. NOT-REPRO: claimed, not on canon. OURS: only on our branch.

## Summary

| # | title | class | lanes | sev | fix | repro |
|---|---|---|---|---|---|---|
| U01 | TCP.recv/send decode and re-encode UTF-8: binary bytes become U+FFFD, lengths change | BUG | interp js c | high | fix/socket-bytes-v2 (= upstream/01-tcp-bytes) | upstream/tcp_bytes.bend + peer.py echo |
| U02 | TCP.listen's backlog is 16: bursts lose SYNs, 1 s / 3 s stalls | BUG | interp js c | med | fix/listen-backlog-v2 (= upstream/02-listen-backlog) | upstream/listen_backlog.bend + peer.py burst |
| U03 | the IO loop's select walks every waiter per pass: n arrivals cost O(n^2) | PERF | js c | high | fix/epoll-v2 (= upstream/03-epoll): descriptors only; timers stay O(n) | upstream/io_fd_waiters.bend, io_waiters.bend |
| U04 | Nat.min / Nat.max are unary recursions in every lane: stack overflow on big Nats | BUG | js c | med | upstream/04-nat-min-max | upstream/nat_min_max.bend |
| U05 | File.write UTF-8-encodes bytes >= 0x80 | OURS | - | - | (ours: File.write_buf) | upstream/file_write_text.bend |
| U06 | Bool.pick (Base's only `if`) evaluates both arms | PERF | js c, interp for IO mains (a pure main is lazy) | med | none | upstream/bool_pick.bend, bool_pick_pure.bend |
| U07 | JS lane ignores SIGTERM | OURS | - | - | (ours) | upstream/sigterm.bend |
| U08 | a match over IO.OP with a default arm: JS throws `[object Object]` where C takes the default | BUG | js; interp prints a stuck term | low | none | upstream/io_op_default.bend |
| U09 | a def used above its definition gets the typo's error | NOT-REPRO | - | - | canon's message differs since d3790917 | upstream/def_order.bend, def_typo.bend |
| U10 | Nat literal of 100000n in a proof overflows the checker; literals stop at 2^32-1 | LIMITATION | check | med | none | upstream/nat_literal_proof.bend, nat_literal_cap.bend |
| U11 | a check that relies on @unsafe or foreign code exits 0 | LIMITATION | check | med | none (WONTFIX #776, #805; suggest `--strict`) | upstream/unsafe_exit.bend |
| U12 | IO.signal_pending clears on read | OURS | - | - | (ours: IO.signal_seen) | none (Base has no signal effect) |
| U13 | accept() on EMFILE is indistinguishable from a dead listener | NOT-REPRO | - | - | canon hands back `Fail 24` and the listener | upstream/accept_emfile.bend + peer.py hold |
| U14 | canon's own tests on Linux: two sleep-order tests flake; audio needs ALSA | BUG (tests) | interp js | low | none | verify.sh U14 (canon's tests/io) |
| U15 | comp.ts and bend.ts sit within 2.2% and 0.6% of their ttok caps | LIMITATION (process) | - | low | none | verify.sh U15 |
| U16 | a pure main counts Nats in unary: epoch-sized numbers (1.7e9) are unusable | PERF | interp (pure main) | med | none | upstream/interp_nat_epoch.bend, interp_nat_mul.bend |
| U17 | TCP.listen binds 0.0.0.0 and takes no address: no loopback-only server | LIMITATION | interp js c | med | upstream/05-listen-on | verify.sh U17 (Base's signature) |
| U18 | TCP.connect takes dotted IPv4 only (no names, no resolver) and has no deadline | LIMITATION | interp js c | med | upstream/06-connect-poll-dns | upstream/connect_name.bend |
| F01 | no wall clock: IO.now is monotonic | LIMITATION | all | med | none | verify.sh F01 |
| F02 | no rename, fsync, seek, remove or mkdir | LIMITATION | all | med | none | verify.sh F02 |
| F03 | File.read_at takes a U32 offset and answers a List cell per byte | LIMITATION | all | low | none | verify.sh F03 |
| F04 | no mutual recursion, even with both laws declared first | LIMITATION | check | low | none | upstream/mutual.bend |
| F05 | List.map takes List<&1, A> only (length, folds, for_each are generic) | LIMITATION | check | low | none | upstream/list_map_quant.bend |
| F06 | a destructuring let of a call is refused, with the match rule's message | LIMITATION | check | low | none | upstream/let_computed.bend |
| F07 | only Base imports by name: a second standard module needs a bend.ts change | LIMITATION | check | low | none | upstream/import_name.bend |

Verified on canon `95317d95`: every U/F row above reads REPRO except
U05, U07, U09, U12, U13 (FIXED: not on canon), U06p (a pure main's pick
is lazy, as it should be) and U14's tls_close and marshal (they pass on
canon). Against the fix branches: U01 FIXED on
fix/socket-bytes-v2, U02 on fix/listen-backlog-v2, U04 on
upstream/04-nat-min-max, U03 (descriptors) on fix/epoll-v2 in both
lanes, while U03t (timers) stays REPRO there.

---

## U01. `TCP.recv` and `TCP.send` corrupt every byte that is not UTF-8

**Class** BUG, high. **Lanes** interp, JS, C. **Fix** `fix/socket-bytes-v2`.

**Where** (canon `95317d95`) `bend2/effs/tcp_recv.c:6` builds the result
with `io_str`, which decodes UTF-8 (`comp.ts:5607`); `tcp_poll.c:22` the
same; `tcp_send.c:23` re-encodes with `io_cstr`. The JS twins go through
`io_text` / `TextDecoder` (`comp.ts:6290`) and `TextEncoder` (6286).

**Repro** `upstream/tcp_bytes.bend` accepts one peer on 29601, reads once
and echoes; `python3 upstream/peer.py echo 29601` sends `01 80 fe 02`.

**Observed** `01efbfbdefbfbd02` in all three lanes. **Expected**
`0180fe02`.

Each ill-formed byte becomes U+FFFD, three bytes out for one in, so the
corruption changes the *length*: an echo of 8 arbitrary bytes under
`content-length: 8` writes 12, and on a keep-alive connection the peer
reads the next reply's first bytes as this one's tail. That is response
splitting by accident, reachable by any peer that sends a byte over
0x7F. A PNG, a protobuf, a TLS record, a WebSocket frame or a gzip body
cannot cross a Bend socket.

**Fix** the byte pair files already have (`File.read_bytes`,
`File.write_bytes`): `TCP.recv_bytes`, `TCP.send_bytes`,
`TCP.poll_bytes` over `List<&2, U32>`, decoding nowhere. On the branch,
`upstream/tcp_bytes_fixed.bend` (the same echo over the byte pair)
answers `0180fe02` in every lane; verify.sh switches to it when Base
has `TCP.recv_bytes`.

## U02. The listen backlog is 16

**Class** BUG, med. **Lanes** all. **Fix** `fix/listen-backlog-v2`.

**Where** `bend2/effs/tcp_listen.c:17` `listen(fd, 16)`;
`tcp_listen.js:18` `sys.listen(fd, 16)`.

**Repro** `upstream/listen_backlog.bend` listens on 29602 and accepts
nothing for 3 s; `peer.py burst 29602 64` opens 64 connections at once
and counts the handshakes the kernel completed within 1 s.

**Observed** `completed 17 of 65` in every lane (the backlog, plus one).
**Expected** all 65 (`SOMAXCONN` is 4096 here). On the branch: 65 of 65.

A single-threaded loop that is briefly busy overflows 16 at once; the
kernel drops the SYNs and the peers wait for the retransmit. Measured on
the HTTP engine with the loop fixed: connection ramps with walls of
1.03 s, 3.08 s and 6.13 s (the SYN timers and nothing else), flat at
21-29 us per connection with `SOMAXCONN`.

**Fix** `SOMAXCONN` (4096; the kernel clamps it), both twins.

## U03. A pass through the IO loop costs what waits, not what fired

**Class** PERF, high. **Lanes** JS, C. **Fix** `fix/epoll-v2` for
descriptor waiters; none for timers.

**Where** C `comp.ts:5738` `io_wait`: every pass sizes a descriptor set
by the highest live fd, walks the park list to fill it and find the
soonest deadline, `select`s, and walks the whole list again to
dispatch. JS `comp.ts:6311`, the same shape.

**Repro** `upstream/io_fd_waiters.bend` times 2000 zero sleeps (a pass
each) alone, then beside 4000 clients parked in `TCP.recv` (port 29603;
accepts one client at a time so U02 does not interfere).
`upstream/io_waiters.bend` does the same beside 20000 parked sleepers.

**Observed** (C) alone 1 ms, beside 4000 descriptors 1048-1704 ms
(ratio ~500); beside 20000 timers 1056 ms. JS: 32 ms vs 2067 ms; 40 ms
vs 1136 ms. **Expected** a ratio near 1.

On `fix/epoll-v2`: descriptors flat in both lanes (1 ms vs 1 ms in C,
38 ms vs 14 ms in JS), but timers still O(parked) per pass (C 2 ms vs
695 ms), because it keeps deadlines on the park list. Our own branch
(`959a64e0`, "epoll and a deadline heap") is flat for both in C, and
still quadratic in JS for both.

Measured earlier with `demos/io_http_engine/ramp.c` (connections opened
and held): 2.1 ms per connection at 500 live, 4.1 at 1,000, 11.3 at
2,000, 30.7 at 4,000, and 8,000 did not finish in 150 s (that ramp also
hit U02). A minimal accept-and-park server: 0.15 / 1.49 / 4.29 / 31.4 s
to hold 1k / 4k / 8k / 16k on canon against 0.06 / 0.28 / 0.49 / 1.78 s
with an epoll loop.

**Fix** register each fd with the kernel's poller once (epoll on Linux,
kqueue on macOS, `EPOLLONESHOT` re-armed in place), as `fix/epoll-v2`
does in both lanes, and keep deadlines in a min-heap (not yet on the
branch; `TCP.poll` waits on both, so each side must take the waiter out
of the other).

## U04. `Nat.min` and `Nat.max` are unary recursions in every lane

**Class** BUG, med. **Lanes** JS, C. **Fix** `upstream/04-nat-min-max`.

**Where** `bend2/base.bend:617` and `:626` recurse one successor at a
time (`1n+Nat.min(ap, bp)`, not a tail call); `comp.ts:182` `OPERATIONS`
has native `nat_add`, `nat_sub`, `nat_mul`, `nat_is_lt`, but no
`nat_min`/`nat_max`.

**Repro** `upstream/nat_min_max.bend`: `Nat.min(2^40, 2^40+1)`.

**Observed** JS `RangeError: Maximum call stack size exceeded`, C
`bend: memory fault (machine stack overflow?)`; JS already overflows at
`Nat.min(100000n, 100001n)`. **Expected** `"1099511627776
1099511627777"`, which the branch prints in both lanes.

**Fix** two `OPERATIONS` rows, `($0 < $1 ? $0 : $1)` and the converse.

## U06. `Bool.pick` evaluates both arms

**Class** PERF, med. **Lanes** C, JS, and interp when `main` is IO (the
in-process JS runtime); a pure main (the checker's normalizer) is lazy.
**Fix** none.

**Where** `bend2/base.bend:473`: `Bool.pick(-A, c, a, b)` is an ordinary
def, and it is the only `if` Base offers.

**Repro** `upstream/bool_pick.bend` (IO main): the condition comes from
`IO.args()`, the arm not taken is a 10^8-step loop clang cannot fold,
and the same choice written as a `match` on the `Bool` is timed beside
it. `upstream/bool_pick_pure.bend` (pure main, interp only):
`Bool.pick(U32, True{}, 1, deep(10000000n))`.

**Observed** pick against match: C 25 ms / 0 ms, JS 20.5 s / 1 ms,
interp 14.7 s / 1 ms, all `eager`. The pure main prints `1` at once
(lazy). Scaling the loop scales C's pick linearly (50 / 501 / 990 ms at
2*10^8, 2*10^9, 4*10^9 steps), the same as calling the arm alone. (A plain
counting loop is not a test of this: clang folds it into a closed form,
which made C look lazy in a first try.) **Expected** the pick to cost
what the match costs.

WONTFIX #775 says compiled lanes are strict ("same value, different
cost"). Because `Bool.pick` is the library's `if`, the cost is paid on
every branch (our uptime app: 19.1 s against 3.9 s for the same
restart), and an arm that cannot finish (JS: a deep recursion) kills
the program. Strictness also forces a `+` on every variable both arms
mention.

**Fix** an `if c: ... else: ...` that lowers to a `match`, or make
`Bool.pick`'s arms templates (`~a`, `~b`) so only the chosen arm is
built; at least say in GUIDE.md that it is strict on JS.

## U08. A match over `IO.OP` with a default arm throws on the JS lane

**Class** BUG, low. **Lanes** JS (interp prints a stuck term). **Fix** none.

**Where** `comp.ts:3254-3256` (`js_match`): a foreign request reaching
a match over `IO.OP` is thrown (`throw $t`), before any arm, default or
not; for a pure main nothing catches it (`io_run`'s catch at
`comp.ts:6397` covers IO mains only).

**Repro** `upstream/io_op_default.bend`: run `IO.print("hi")` by hand to
its `IO.OP` (a foreign request) and match `Emit{value}` / `_`.

**Observed** C `70`; JS `[object Object]`, exit 1; interp
`U32.add(70, got(IO.print("hi", U32, x => Emit{5})))`, exit 0 (a
foreign def has no body to normalize). **Expected** `70` in every lane.

**Fix** in `js_match`, throw only when the match has no default arm
(what C does), and give the throw a message.

## U10. Big Nat literals: the checker overflows, the parser caps at 2^32

**Class** LIMITATION, med. **Lanes** check. **Fix** none.

**Where** `bend2/bend.ts:2340` refuses a literal past `4294967295n`,
though the runtime holds a Nat to 2^48-1 (WONTFIX #779); a literal in a
proof is compared by unfolding to successors, and `main.ts:821` turns
the `RangeError` into "the machine stack overflowed (a deep recursion,
or a literal too large to expand)".

**Repro** `upstream/nat_literal_proof.bend` proves
`{Nat.add(50000n, 50000n) == 100000n : Nat}` by `{==}`: stack
overflow (40000n still checks). `upstream/nat_literal_cap.bend`:
`1099511627776n` is refused; it must be spelt
`Nat.mul(1048576n, 1048576n)`.

**Fix** compare literals and native Nat arithmetic without unfolding
(the checker knows `Nat.add` on two literals is a literal), and allow
literals to 2^48-1.

## U11. A check that relies on `@unsafe` or foreign code exits 0

**Class** LIMITATION, med. **Lanes** check. **Fix** none.

**Where** `bend2/main.ts:690` (`cli_report`) prints the verdict (`:722`)
and returns; the process exits 0. WONTFIX.txt (#776, #805): "read the note,
not the exit code".

**Repro** `upstream/unsafe_exit.bend` "proves" `0n == 1n` with an
`@unsafe` recursion that never ends; `bend unsafe_exit.bend
--check-only` prints `All terms check, but 1 def relies on unsafe or
foreign code: - zero_is_one` and exits **0**.

A CI step that gates on the exit code (`bend F --check-only && ...`)
is fooled: a false theorem passes. **Suggest** an opt-in `--strict`
(exit 2 when anything relies on a promise), which leaves the WONTFIX
default alone. verify.sh uses `--strict` if main.ts ever has it.

## U13. `TCP.accept` out of descriptors (NOT-REPRO)

**Where** `bend2/effs/tcp_accept.c:18`: any errno but EAGAIN is
`io_fail(code)`, with the listener handed back beside it.

**Repro** `upstream/accept_emfile.bend` under `ulimit -n 256`, with
`peer.py hold 29613 400`. **Observed** `accepted 244, then Fail 24: Too
many open files` (C: 250) in every lane: EMFILE is its own errno, and the
listener still works. There is no "dead listener" case: the handle is
affine, and closing it consumes it.

**Related, upstream, low** canon's own `demos/io_http_server/main.bend:37`
does `IO.pass(Socket, r)` on every accept, so one EMFILE halts the whole
server: a peer that opens enough connections stops it. And `TCP.accept`
has no deadline (`upstream/09-accept-poll` adds `TCP.accept_poll`).

## U14. canon's own tests on Linux

`gates/test.ts` run locally (same probes; network tests moved into our
port range) on `tests/io`: 111 of 117 pass.

- **Audio (3 tests, both compiled lanes)** `audio_only_close`, `_open`,
  `_write`: `alsa/asoundlib.h` not found. The JS lane fails too, because
  the gate builds `-o t.js -o t` in one command and one failure fails
  both. LIMITATION of the box (needs `libasound2-dev`), low.
- **Sleep order (2 tests)** `spawn_sleep` and `fork_join` order
  computations by sleeps 10-20 ms apart. On an idle box, ten runs each:
  C 10/10; JS 8/10 for both; interp 10/10 and 7/10. Under load they
  fail more. BUG (test flake), low. The JS `io_wait` (`comp.ts:6328`)
  dispatches every due waiter in park order, not deadline order, once a
  pass comes late, which fits; a direct repro of that did not trigger,
  so the cause is not confirmed. **Fix** space the sleeps 100 ms apart,
  or order due timers by deadline.
- `tls_connect_close`, `http_url_parse` and `marshal_char_scalar` pass
  on canon (NOT-REPRO); the first and last fail on our branch only (see
  OURS below).
- `readback_sugars`: passes (a function-valued main is check-only).

## U15. comp.ts and bend.ts sit at their ttok caps (process)

**Class** LIMITATION, low. **Where** `gates/repo.ts:42-43`.

The gate counts with `ttok`, whose default model is `gpt-3.5-turbo`
(`ttok/cli.py:14`), that is **cl100k_base**. `ttok` downloads that table
on first use, which this box's proxy refuses, so the counts here are
js-tiktoken's cl100k_base, the same encoding (o200k gives within 0.2%):

| file | canon cl100k | cap | headroom |
|---|---|---|---|
| bend2/comp.ts | 62,602 | 64,000 | 2.2% |
| bend2/bend.ts | 43,761 | 44,000 | 0.5% |
| bend2/base.bend | 25,375 | 32,000 | 21% |
| bend2/main.ts | 9,683 | 10,000 | 3.2% |

So canon's own gate is green under cl100k: the claim that canon's
files exceed their caps is NOT-REPRO. They exceed them on **our**
branch (see OURS). But the headroom is thin: `fix/epoll-v2` alone takes
comp.ts to 63,075 (98.6%), and commit `26659268` had to shed 2.8k
tokens to get comp.ts under 64k, so nearly any runtime fix in comp.ts
arrives with a cap raise. **Suggest** move the IO loop into
`effs/`-style sources, as the channel runtime was, or give the runtime
its own cap.

## U16. A pure main counts Nats in unary

**Class** PERF, med. **Lanes** interp (pure main). **Fix** none.

`bend F.bend` normalizes a pure main with the checker, where a Nat is
successors and `Nat.add`/`Nat.mul`/`Nat.div` are Base's recursions
(`base.bend:545`, `:563`); the compiled lanes run them natively.
`upstream/interp_nat_epoch.bend`, `Nat.div(Nat.add(1700000000n, 60n),
60n)` (an epoch time in minutes): JS and C `28333334n` at once; interp
runs past 20 s at ~125% CPU with RSS growing ~70 MB/s. So epoch-sized
numbers are unusable in a pure main. `upstream/interp_nat_mul.bend`
(`Nat.mul(1048576n, 1048576n)`): interp "the machine stack overflowed".
It is PERF rather than a design limit: the IO-main path (the JS
runtime) and both compiled lanes already use native Nats, and so could
the normalizer on closed literals.

## U17. `TCP.listen` binds every interface

**Class** LIMITATION, med. **Fix** `upstream/05-listen-on`
(`TCP.listen_on(host, port)`, `TCP.listen_shared`).

`base.bend:280` `TCP.listen(port: U32)`; `tcp_listen.c:12` binds
`0.0.0.0`. A Bend server cannot listen on loopback only, so a local
admin or debug port is exposed on every interface.

## U18. `TCP.connect` takes dotted IPv4 only, with no deadline

**Class** LIMITATION, med. **Fix** `upstream/06-connect-poll-dns`
(`DNS.resolve`, `TCP.connect_poll`).

`comp.ts:5456` `io_sys_addr` is `inet_pton(AF_INET, ...)`, and Base has
no resolver: `upstream/connect_name.bend`, `TCP.connect("localhost",
29605)`, answers `Fail 22: Invalid argument` in every lane (expected:
connection refused). A connect to a black hole waits the kernel's ~75 s
(no timeout argument).

## F01-F06. From apps/uptime/FRICTION.md, checked on canon

- **F01 no wall clock.** `IO.now` (`base.bend:203`) is `io_tick()` in C
  (`effs/now.c:5`, monotonic) and `performance.now()` in JS. No epoch
  time, no dates; apps need a foreign effect. Also `IO.now` answers a
  `Nat` while `IO.sleep` takes a `U32`. Suggest `IO.wall() -> IO(Nat)`.
- **F02 no rename, fsync, seek, remove, mkdir.** Base's File surface is
  open, read, read_bytes, read_at, size, write, write_bytes, close
  (`base.bend:241-278`): no atomic snapshot, no rotation, no truncate.
- **F03 File.read_at** (`base.bend:256`) takes a `U32` offset (4 GiB)
  and answers `List<&2, U32>`, a heap cell per byte.
- **F04 no mutual recursion.** `upstream/mutual.bend`: `even`/`odd`
  with both laws declared first is refused ("a filled definition (an
  unfilled law is a dead claim ...)"); loops become CPS by hand. Base
  itself has a carve-out (WONTFIX #793); user files do not.
- **F05 List.map is &1 only** (`base.bend:797`), while `List.length`,
  `foldl`, `foldr` and `for_each` take any quantity:
  `upstream/list_map_quant.bend` is refused with `expected : List<&1,
  U32> / observed : List<&2, U32>`.
- **F06 destructuring a call.** `upstream/let_computed.bend`:
  `(a, b) = two(1)` is refused with the match rule's text, "a parameter
  or field scrutinee (a match cannot scrutinize a computed value: give
  it its own def)" (`bend.ts:2788`), though the line is a let.

- **F07 no second standard module.** `bend.ts:1095-1099` accepts
  `import Base` or `import <path>.bend as <Name>` (relative, or a hub
  `name@version/` path). `upstream/import_name.bend`, `import Time`, is
  refused ("expected : an import ('import Base', or 'import <path> as
  <Name>')"). A `bend2/time.bend` beside base.bend could only be
  imported by a path relative to the user's file, so the standard
  library is one file under one cap (U15), and growing it (a clock, a
  date type) needs a bend.ts change for `import <Name>`.

Not upstream: the rest of FRICTION.md is about our `net/` (middleware,
`Client.fetch` timeouts, `Json.num`, flags, the Hub), and its SIGTERM
items are U07 and U12 below.

---

## Not upstream: ours

- **U05 `File.write` and bytes >= 0x80.** Canon's `File.write` takes a
  `String` of code points and writes their UTF-8
  (`effs/file_write.c:24`), which is right for text, and
  `File.write_bytes` writes bytes as they are:
  `upstream/file_write_text.bend` reads back `194 128 195 169` and
  `128 233` in every lane, on canon and on ours. The corruption we hit
  is our `Bytes()` (a String whose characters are bytes) going through
  `File.write`; `File.write_buf` is our answer.
- **U07 JS ignores SIGTERM.** Canon has no signal effect at all; the
  default action ends a JS-lane IO program at once
  (`upstream/sigterm.bend`: every lane gone 100 ms after TERM, status
  143). On our branch the first `IO.signal_pending` installs
  `process.on("SIGTERM")`, which cannot run while `io_run` blocks in
  `select`, so the program runs on (a 5 s loop ran to its end after a
  TERM at 1.5 s).
- **U12 `IO.signal_pending` clears on read.** Ours
  (`effs/signal_pending.*`); `IO.signal_seen` is our fix.
- **Our gate is red on caps.** Under cl100k (U15) our comp.ts is 97,390
  of its 85,100, base.bend 62,905 of 48,928 and bend.ts 43,328 of 43,000
  (our older bend.ts against our older 43k cap; canon's is 44k).
- **Two canon tests fail on our branch only.** `io/tls_connect_close`
  expects "a defined name" for `TLS.connect`, which our branch defines
  (with another type); `io/marshal_char_scalar` expects the JS lane to
  refuse the surrogate 55296 as a Char, and ours prints nothing and
  exits 0 (the packed-string runtime).

## Not reproduced

- **U09 def order vs typo.** Canon tells them apart: a def used above
  its definition gets "expected : a filled definition (an unfilled law
  is a dead claim: live code cannot use it)", a misspelt name "expected
  : a defined name" (`bend.ts:3405`, `:3393`;
  `upstream/def_order.bend`, `def_typo.bend`). Canon has had this since
  at least `d3790917`; our branch's older checker still says "a
  defined name" for both. Residual, low: the message speaks of a law
  the user never wrote; "defined below its use" would say it.
- **U13** above.
- **Withdrawn earlier: a def namespace that shares a name with a live
  binder (`tls.cert` with `tls` in scope) seemed to make the checker
  loop.** Not reproduced: a dozen reductions check in seconds, and the
  shipped engine has the pattern. The likely cause was `bend main.bend`
  without `--check-only` checking and then running a server.
