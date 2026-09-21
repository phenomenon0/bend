# gemv lane — the F32 GEMV honesty bench (opus 5, 2026-09-20)

Branch `lane-gemv`, worktree `bend-work-gemv`, off `omen` `5513be61` (the
native-U64 port). New: `tests/power/bench/gemv.bend`,
`tests/power/bench/gemv_par.bend`, `tests/power/bench/twin_gemv.c`,
`tests/power/bench/twin_gemv_par.c`, `tests/power/bench/run_gemv.sh`. One
line changed in nothing else: `bend2/` untouched, `power/` untouched, no
existing bench or test edited. Nothing pushed.

The question the lane exists to answer: **can a flat `Array<F32>`
matrix-vector product — the skeleton of a decode step — land within 2x of its
C twin on one thread, and fork near-linearly on sixteen?** A no is worth as
much as a yes; what follows is the measurement and, more usefully, what the
measurement does and does not say.

## Where the files are, and why not `bench/`

The brief said `bench/gemv.bend`. `gates/repo.ts` allows exactly
`bench/nbench[a-z_]*.(bend|c)` at the top of `bench/` — everything else there
must be `bench/{runtime,checker}/<name>/main.*` with a `_pin_` row. A
`bench/gemv.bend` fails the repo gate, and a `bench/runtime/gemv/` would claim
a pin on 48 minis this lane has no business writing.

`tests/power/bench/` is where every measured C twin in this repo already
lives, it is allow-listed (`tests/power/...`, 16,000 ttok), and its `run.sh`
*is* POWER.md's protocol: a row is only timed once the twin, the Bend binary
at `--threads 1` and the same binary at `--threads 16` print the same
checksum, then medians of three. Putting `gemv` there gets the protocol for
free and puts the row next to `knn`, which is the row it should be read
against. `run_gemv.sh` wraps that with what this lane adds: the machine line,
the interpret lane, and the reference build the twin is not allowed to be.

`bun gates/repo.ts` — **PASS: 55 / 55**.

## Verdict

**Yes on the first question, no on the second — and the third number is the
one that matters.**

A flat `Array<F32>` matrix-vector product lands at **1.1x its C twin on one
thread**, which is inside the 2x the lane was opened to test and lands
alongside `knn` at 1.2x — the row this one was put next to on purpose. Out of
cache, at 4096 x 4096, it moves to **1.4x**. Still inside.

It does **not** fork near-linearly. `gemv_par` reaches **3.5x on sixteen
threads**, and the thread curve below says that is not a sixteen-thread result
at all: it is a *four*-thread result — 1.9x at two, 3.3x at four, and flat from
eight on, on a machine with eight physical cores. A knee at 8-to-16 would be
SMT running out, which is the expected and boring answer. This knee is at four,
so it is not core count, and it is not the answer the bench was expecting.

The number that frames both: the honest twin — strictly ordered and scalar,
because that is what Bend emits — is itself **13x slower than the same C file
at `-march=native -ffast-math`**. So "1.1x of C" is 1.1x of a C that is 13x off
what this hardware does with this loop. Bend has no way to ask for
reassociation today. That gap, and not the 1.1x, is the finding.

## What the bench is

`gemv.bend` — one 512 x 512 weight matrix as a flat `Array<F32>`, and **512
successive decode steps** against it. Each step hashes a fresh length-512
activation, takes the matrix-vector product row by row, writes the length-512
result out and reads it back into the checksum. **134,217,728 multiply-adds**
through one flat block.

The row dot product is `power/knn.bend`'s `ip`, not a copy of it. `Knn.Flat`
already *is* this layout — n rows of d floats row-major in one flat
`Array<F32>`, one owner, an index loop with no allocation inside it — so the
bench calls it rather than restating it. A second hand-typed copy of the same
loop would measure the same thing while being free to drift from it.

The result vector is materialized rather than folded on the fly, because that
is the shape under question: a decode step writes activations the next op
reads. It is a fresh block each step, allocated and dropped; the C twin writes
one static array 512 times. The asymmetry runs against Bend, and is left in.

`gemv_par.bend` — the same weights taken to **8,192 x 512**, cut into 2^6 row
blocks of 128 rows, 128 decode steps: **536,870,912 multiply-adds**, four
times the sequential bench, cut 64 ways. The row block is the unit because an
`Array` has one owner and no two lanes can read one matrix — and because
row-blocking is how a GEMV actually shards: every row is independent, the
activation is broadcast, nothing is reduced across shards.

`gemv_par.bend` **imports** `gemv.bend` instead of duplicating its helpers,
which is a deliberate break with the other fourteen `_par` twins in that
directory. A bench whose whole point is a ratio between two rows should not be
able to drift between them; there is exactly one copy of the code that calls
`ip`.

### The degeneracy probe

POWER.md's rule — *a bench whose shards repeat is unmeasured until probed* —
so the generators were counted rather than assumed:

- `gemv`: **512 distinct step checksums of 512.** The activation hashes start
  2^30 past the weights' and advance by k each step; no step repeats.
- `gemv_par`: **64 distinct leaf checksums of 64.** Shard s hashes its weights
  from `s << 16`, and the 64 ranges tile `[0, 4194304)` exactly — disjoint, no
  two shards draw the same rows. The activations are deliberately *identical*
  across shards, which is what a broadcast is, so the leaves differ only by the
  weights, which is the thing being sharded.

### What the twin is, and what it is not

`twin_gemv.c` is the same hash, the same floats, the same dot product in the
same order, the same result read back in the same order and the same mixer,
compiled `-O3`. Its inner loop is **strictly ordered and scalar** — without
`-ffast-math` clang will not reassociate a float reduction — and the product
is its own statement so that `-ffp-contract`, whose default is per-statement,
cannot fuse it into an FMA and round once where Bend rounds twice.

That is not a handicap invented for this bench. It is what Bend emits, and
provably so on both counts: `bend2/comp.ts` puts `#pragma clang fp
contract(off)` at the head of every emitted translation unit, and
`bend2/main.ts` builds it with `-std=c11 -O3 -lpthread -lm` — **no `-march`,
no fast-math**. Both sides are baseline x86-64 scalar by construction.

It is also not what a C programmer would ship. The last block of
`run_gemv.sh` measures the same file under the permissions Bend cannot give,
and that gap is the finding this lane exists for.

## The numbers

Ryzen 7 7700X (8 cores / 16 threads), Linux 6.17.12, clang 21.1.7, bun 1.3.4,
bend 2.0.21, `--gpu off`, medians of three, seconds, under
`/tmp/bend-bench.lock`. Every row's twin, 1T run and 16T run agreed on the
checksum before any of it was timed — `gemv` on `1655347755`, `gemv_par` on
`646920195`.

    bench             C  bend-1T bend-16T    1T/C  1T/16T
    gemv           0.07     0.08     0.08    1.1x    1.0x
    gemv_par       0.29     0.32     0.09    1.1x    3.5x

`gemv`'s two Bend columns are the same run twice — there is no fork in that
file — and they agree, which is the cheapest available check that `--threads`
does not change a sequential answer. `gemv_par` at 16T is **3.2x faster than
the single-threaded C twin** of the same work, which is the only column in
which Bend beats C here, and it beats it by forking rather than by compiling
better.

### The window these were taken in

POWER.md's table was taken with "nothing else on the machine (load 1.8 at
start)". That was not on offer. A sibling lane's `run.sh` has been wedged for
three and a half hours inside a single `clang-21` compiling `text_par.c`,
pinning one hardware thread that is not coming back, and a second lane compiles
a 1,300-line Bend program in a loop. The one-minute load average never came
down: it read **7.0 through the take**.

So the gate here is not the load average. Load1 is a one-minute EWMA and lags a
real window by minutes — gating on it is what hung the previous attempt at
these numbers for sixty-six minutes and then produced a floor instead of a
reading. The gate is the instantaneous busy-thread count out of `/proc/stat`,
sampled over three seconds. The rows above were taken inside a window measured
at **2.03 of 16 threads busy and re-measured at 2.20 as the last median
landed** — about fourteen of sixteen threads idle throughout, while load1 read
7.0. A take whose two readings straddle the threshold is discarded and retaken;
two were, before this one.

The split that makes that possible: **building and checksum-verification happen
outside the window, the clock inside it.** Neither compilation nor checksum
agreement needs a quiet machine, and both are the slow part; the timing itself
is about fifteen seconds. `run_gemv.sh` does all of it in one pass, which is
right on a quiet machine and cannot finish inside a window on this one. The
commands being timed are the same either way.

### The thread curve

`gemv_par`, 64 row blocks, medians of three, same protocol:

    threads   seconds   speedup
        1T      0.33       1.0x
        2T      0.17       1.9x
        4T      0.10       3.3x
        8T      0.09       3.7x
       16T      0.09       3.7x

Near-perfect to two threads, good to four, **flat from eight**. The wall
arrives at four threads and it is not core count. The first place to look is
allocation: each of the 64 shards builds its own 256 KB weight block, and every
one of its 128 steps allocates a fresh activation and a fresh result and drops
both. That is a lot of traffic through one allocator, and the sequential row —
which does the same per-step allocation and scales fine because nothing
contends — would not show it. This lane measured the curve; it did not diagnose
it, and the diagnosis is worth its own lane.

### Out of cache

The same code at 4096 x 4096 over 8 steps: 67 MB of weights, past every cache
on this part, and the same 134 million multiply-adds as the sequential row, so
the two are directly comparable.

    probe                      C  bend-1T   1T/C
    4096 x 4096, 8 steps    0.11     0.16    1.4x

The ratio moves the **wrong way**. Going to RAM is supposed to flatten a
language gap — if both sides are waiting on the same memory, neither's codegen
matters much. Instead both slow down for the identical work and Bend slows down
more: C by 1.6x, Bend by 2.0x. Whatever Bend is paying per element, it is not
hidden by a cache miss. And a real decode step lives much nearer this row than
the in-cache one, so 1.4x is the more honest number of the two to carry
forward. It is still inside 2x.

### What the twin is not allowed to be

    build                                 seconds   checksum
    twin, strictly ordered and scalar        0.07   1655347755
    same file, -march=native -ffast-math     0.01   2727284501

**13x**, and a different checksum — which is the point rather than a defect.
Reassociation is exactly what the second build was given permission to do, and
it rounds differently for having done it; a twin that took that permission
would be comparing Bend against a different arithmetic. But `bend2/comp.ts`
emits `#pragma clang fp contract(off)` at the head of every translation unit
and `bend2/main.ts` builds with no `-march` and no fast-math, so there is no
flag a Bend user can pass to reach that second row.

This is the frame for every other number in this report. Bend is at 1.1x of a C
that is at 13x of the machine.

## The F64 re-check

`power/fft.bend:17-33` records F64 dying in the compiled lanes, and
`docs/omen/f64-drop-c-backend.md` carries the derivation and the smallest
reproducer. Upstream rebuilt the array subsystem across 2.0.18-2.0.21, so the
question is whether the sync fixed it. Both documented reproducers were run
verbatim on this tree (`bend 2.0.21` + the native-U64 port, `5513be61`):

| probe | interpret | JS | C `--threads 1` | C `--threads 16` |
|---|---|---|---|---|
| build 8 `F64` slots, read slot 3, drop the array | `12291` | `12291` | `bend: memory fault` | `bend: memory fault` |
| build 8 `F64` slots, never read, drop the array | `7` | `7` | `bend: memory fault` | `bend: memory fault` |

**Not fixed.** `Array<F64>` still puts a raw double in a slot the C runtime
walks as a `Term`, and dropping it still frees a block that was never
allocated. The array-subsystem work in 2.0.18-2.0.21 did not touch `lay_arr`'s
choice to route anything wider than `w32` into the Term-walked block.

One thing did change, and it changed for the better: **the failure mode.** The
doc records the read probe printing `1` — a silent wrong answer — and the sink
probe reporting `out of memory`. Both now take a hard `memory fault` on this
tree. A crash is strictly better than a wrong number, but it is not a fix, and
the workaround in POWER.md stands unchanged: **F32 or fixed-point U32 in
arrays, `match` rather than `Bool.pick` at F64.**

This is also why `gemv.bend` is F32 and not F64, and why it can drop a result
vector every step without care: an `F32` cell is `w32`, takes the packed
block, and is never walked as a `Term`.

## A gotcha found on the way: the interpreter does not reduce F32

`bench/*.bend` files in this repo have `main() -> U32`, and the interpreter
prints that as a *normalized term*. F32 primitives do not reduce there:

    def main() -> U32: F32.bits(F32.add(1.0, 2.0))
    $ bun bend2/main.ts f32.bend
    F32.bits(F32.add(1.0, 2.0))

So a float-heavy bench `main` is a symbolic tree the interpreter never
finishes folding — the first attempt at an interpret lane here ran for two
minutes on an 8 x 8 matrix before being killed, which reads exactly like an
infinite loop and is not one. Routing the same call through `IO.print` +
`U32.show` forces it:

    IO.print(U32.show(F32.bits(F32.add(1.0, 2.0))))   # 1077936128

That is why every `tests/power/*.bend` fixture is in the `IO` shape and why
none of them appeared to have this problem. `run_gemv.sh` generates a
throwaway `_gemv_small.bend` in that shape, at 8 x 8 x 4 — the size the
interpreter can finish — and checks it against `twin_gemv small`, which is the
same C binary the timing uses.

## What this bench does not say

**It is not memory-bound, and a real decode step is.** A 512 x 512 F32 matrix
is 1 MB: it sits in L2/L3 and is re-read 512 times from cache. This bench
therefore measures *compute*, which is the harder case for Bend — and the one
where a scalar loop has nowhere to hide. The out-of-cache row below (4096 x
4096, 67 MB of weights, 8 steps) is the same code at a size that has to come
off RAM, and it is there to say whether the ratio moves when the wall changes.

**It is one shape at one size.** No tiling, no blocking, no batch dimension, no
transposed access, no quantized weights, no GPU lane (`--gpu off` throughout).
A GEMV is the skeleton of a decode step, not a decode step.

**A `1T/16T` number is not a scaling law.** Sixteen threads on eight physical
cores is eight cores plus SMT, and the ceiling is nearer 10x than 16x before
anything in the runtime is blamed.

## Deliberate ceilings

- **No attention-head variant.** The brief made it optional. A softmax needs
  `F32.exp`, which is libm's in emitted C and `Math.exp` in emitted JS — a
  bench pinned to this machine's libm, against POWER.md's "no float reaches a
  printed line" convention. The GEMV answers the question the lane was
  opened for; the head variant would have to quantise its way out of exp
  first, and that is a lane of its own.
- **The interpret lane runs at 8 x 8 x 4**, not at the benched size — the
  interpreter cannot reach it. It checks the program, not the scale.
- **The out-of-cache row is a probe, not a committed bench.** It is the same
  `twin_gemv.c` with `MAXM`/`MAXK` at 4096 and one call changed, plus a
  four-line Bend file importing `gemv.bend`. A 67 MB static array and a 67 MB
  Bend heap do not belong in a bench directory that runs 48 rows on every
  invocation.
- **No `_pin_` row.** `bench/runtime/` pins are the gate's contract across 48
  minis; this lane measured one machine and has no business writing one.
- **One size, one dtype.** No sweep over M, K, or shard count beyond the
  thread curve below.

## Evidence — how to re-run every number here

    BEND_NO_TELEMETRY=1 bash tests/power/bench/run_gemv.sh

prints the machine line, the interpret check, the two rows under
`/tmp/bend-bench.lock` at medians of three, and the reference builds. The
gemv rows alone, inside the existing protocol:

    flock /tmp/bend-bench.lock bash tests/power/bench/run.sh gemv

The F64 probes are `docs/omen/f64-drop-c-backend.md`'s two reproducers,
verbatim, built with `-o` and run at `--threads 1` and `--threads 16`.

`bun gates/repo.ts` — **PASS: 55 / 55**.
