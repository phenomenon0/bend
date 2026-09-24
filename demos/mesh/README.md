# demos/mesh — a fork tree whose leaves are machines

Every program in `demos/monoids` computes a small summary (Kulisch limbs, a
state map, a histogram) that joins associatively, and every leaf is a pure
function of its range. So nothing makes a leaf live in the same process as its
join. `worker.bend` is a net server that answers one leaf over HTTP.
`mesh.bend` splits a job into chunks, hands them to the workers, joins what
comes back with the job's own monoid, and prints what the single-process
program prints, **bit for bit**.

That turns three distributed-systems problems into non-problems:

- **Retry is free.** A worker that fails (refused, reset, timed out) gives its
  chunk back and retires. Whoever re-runs the chunk returns the same bytes, so
  nothing is double-counted.
- **Hedging is safe.** Once the queue is empty, idle workers take chunks that
  are out but not back yet (Dean & Barroso's hedged requests, from "The Tail at
  Scale"). The first copy to land is kept, and a later copy must equal it.
  Usually hedging is where duplicate work bites; here the duplicates are the
  same function of the same range.
- **Splitting is free.** The chunk count changes only the schedule.

The worker that lands the last missing chunk prints the answer and ends the
process. Straggling requests are abandoned: their answers can only repeat what
is already in.

```bash
bun bend2/main.ts demos/mesh/worker.bend -o worker && ./worker --port 9101 [--slow MS]
bun bend2/main.ts demos/mesh/mesh.bend -o mesh
./mesh lost 8 0 64 4 http://127.0.0.1:9101 ...   # job a n chunks depth urls
./mesh lost 8 0 0 8                               # chunks 0: in this process
demos/mesh/mesh.sh                                # the runs below, checked
```

## Measured

These runs used four workers on one 4-vCPU box, one thread each, standing in
for four machines. Each output must equal the oracle's pinned answer: the DP
histogram from `lostupdate_gen.py`, and `kulisch_big`'s bits.

| run | lost 8: 601,080,390 schedules | exact 7: 2^26 floats |
|---|---:|---:|
| one process, 1 thread | 37.8 s | 2.81 s |
| 4 workers, 64 chunks | 9.5 s | 0.75 s |
| worker 0 sleeps 4 s before every leaf | 12.3 s (it finished 2 chunks, the rest took 62) | 0.96 s |
| worker 1 `kill -9`'d at 2 s | 12.1 s (1 retry) | 0.77 s (done before the kill) |

All eight runs print the pinned answer. The last two rows run on the 3
remaining workers, so the expected time is about 4/3 of the clean run's.

## A priced job on preemptible machines

`option.bend` prices a European call (S0 100, K 105, r 5%, sigma 20%, T 1)
by Monte Carlo. Each path is a pure function of (seed, i). exp and log are
built from IEEE + - * / sqrt floor, not libm, because libm differs between
machines. Payoffs are summed in fixed point, 96-bit integers, so the join is
associative. `option_ref.py` (CPython) and `option_twin.c` do the same
operations in the same order. `spot.sh` runs the mesh while a chaos loop
SIGKILLs a random worker every 1-3 s and restarts it 1-4 s later. A failed
post now costs the worker a strike (250 ms backoff), not its life: it
retires after 40 failures in a row.

2e7 paths. Every row prints the twin's bits, `eabd3861 0a0c5497 ...`:

| run | time | notes |
|---|---:|---|
| C twin, 4 threads | 1.2 s | |
| mesh, one process | 18.3 s | |
| 2 workers x 50 chunks | 37.1 s | |
| 4 workers x 200 chunks | 18.6 s | |
| 4 workers, spot chaos | 21.8 s | 5 kills, 45 re-admitted posts |

The bits also match across Python, the C twin at 1/3/4 threads, and Bend's
JS lane (2e4 paths).

**Accuracy.** Over 10 seeds at 4e6 paths, the error against Black-Scholes
(8.0213522) has rms z 0.97. At 4e8 paths it is 8.021388 +- 0.00066
(z +0.05). exp is within 1 ulp of libm; log within 2.

**Speed, 4e6 paths, one core** (four cores scale about 4x for all three):

| | paths/s | vs Bend |
|---|---:|---:|
| Bend (C lane) | 0.28 M | 1x |
| C twin: same bits | 4.3 M | 15x |
| C with libm and a double sum | 10.3 M | 37x |
| Bend (JS lane) | ~0.0007 M | 1/400x |

## The fair verdict

- **The bit-identity is real but it is not Bend's.** The C twin has it too.
  What buys it is the design: pure leaves, integer sums, and hand-built
  exp/log. That costs 2.4x in C, mostly in exp/log.
- **Bend's C lane is 15x the twin today.** Spot machines run 60-90% below
  on-demand prices. At a 90% discount, Bend on spot still costs 1.5x the
  twin on demand; at 70%, 4.6x. The twin on spot costs 0.1-0.3x. For this
  job the mesh protocol is worth using now; Bend's runtime is the bill.
- **Plain C drifts, but harmlessly for price.** The libm/double version
  changes in the 14th digit with the thread count. That is irrelevant to a
  price with se 0.0066. It matters for byte-level audits, result caches,
  and safe hedging; nowhere else.
- **FMA is the live hazard.** Built with FMA contraction, the twin flips
  the last bit (`a971f236`). clang contracts `a*b+c` by default (GCC does
  not under `-std=c11`), so `bend2/main.ts` now passes `-ffp-contract=off`.
- **Test caveat.** The four "machines" are four processes on one 4-vCPU box.
  Nothing here measured network latency or cross-machine libm.

## What it is not yet

- **Duplicates are rarely compared now.** The coordinator halts as soon as the
  answer is complete, so a hedged duplicate is only compared when it lands
  first. A version that waited for every loop compared 3 of 3 as equal. An
  audit mode that waits for them all would make that check permanent.
- **Re-admission is blind.** A down worker is retried every 250 ms, with no
  health probe. Each retry takes a chunk off the queue and puts it back.
- **One coordinator.** Its board is a channel of one, which is fine at 64
  chunks. At thousands of chunks the board should be a tree too.
