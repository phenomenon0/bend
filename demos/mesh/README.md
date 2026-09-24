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

## What it is not yet

- **Duplicates are rarely compared now.** The coordinator halts as soon as the
  answer is complete, so a hedged duplicate is only compared when it lands
  first. A version that waited for every loop compared 3 of 3 as equal. An
  audit mode that waits for them all would make that check permanent.
- **A dead worker stays dead.** There is no re-admission and no health probe
  between chunks.
- **One coordinator.** Its board is a channel of one, which is fine at 64
  chunks. At thousands of chunks the board should be a tree too.
