# placement lane — the first energy-routed dispatch, CPU vs the RTX 3090 (opus 5.5, 2026-09-27)

Branch `placement`, worktree `bend-work-placement`, off `81f12fc5`. **Userland
only**: `bend2/` is untouched, so the full battery was not run. New:

    demos/placement/main.bend    the kernel: one bang, 4^7 leaves, one flat loop per row
    demos/placement/twin.c       its C twin, same F32 order, same join tree
    demos/placement/place.py     measure (both rails, net of idle) and route (the policy)
    demos/placement/run.sh       build, table, identity, two routed runs
    docs/omen/lanes/placement-evidence/   the receipts this report cites (copied from
                                          demos/placement/receipts/ after the run)

`bun gates/repo.ts` gives **PASS: 56 / 56**: every new path lands on an existing
rule and no cap moved. Every number below comes from
`placement-evidence/{table,routed}.jsonl`, `gpu_*.csv` or `run.log` of the one
run of `bash demos/placement/run.sh` at 00:42–00:50 local time. The exceptions
are in §4 (the tail split and the fit), which are arithmetic on those receipts
and are labelled as such.

## Verdict

| | |
|---|---|
| same four lines, C twin = CPU pool = GPU | **yes, at all 7 sizes plus both routed runs**; no divergence (`identity.txt`) |
| the GPU is faster in wall time | from 131,072 cols up: 2.3x at 131k, 4.0x at 1M, 4.9x at 16M |
| the GPU is cheaper in energy | **only from ~4M cols (69 G MACs) up.** 4M is a tie (640 vs 642 J), 8M goes to the GPU by 13%, 16M by 29%, **but both gaps are inside the CPU rows' idle-drift error bars** (§3, residuals) |
| why the crossover sits so far above the time crossover | every GPU launch costs a fixed **~240–340 J** of tail after the process exits: the 3090 stays above idle for seconds (~6 s in the 1M row) |
| the policy routes both ways | 4,096 cols → **CPU** (predicted 0.21 J, measured 1.42 J/run); 12,582,912 cols → **GPU** (predicted 1463 J, measured 1471 J) |

The time crossover and the energy crossover are **30x apart in work** on this
box. A dispatcher that places work by speed would send every run from ~131k
cols up to the GPU, and pay 2.9x the energy at 131k and 1.5x at 1M. That gap
is the finding.

## 1. The kernel, and why this one

`main.bend` computes y = A·x over 16384 rows of `PLACE_COLS` columns. A weight
and an input are each hashed from their index (`v(p)` of the tensor lane's
`bench_blocked`), not loaded. It is a decode step's dot products with no memory
traffic. That is deliberate: the CUDA heap is managed memory, and pages fault
across PCIe on first touch (`bend guide shaders`). A loaded matrix would
measure the bus, not the unit.

The shape follows the shaders guide. One bang, `node!(7n, 0, m)`, forks four
ways seven times, so 4^7 = 16384 leaves, which is the device's lane cube. There
is one row per leaf, and each row is a flat tail loop (`dot`, a serial F32
chain). The four results fold up the same fixed tree:

- `mix` for the checksum;
- `or` and `and` over the bits;
- the nonfinite probe.

The tree is fixed, so the answer does not depend on the schedule.

**One binary serves both units.** `--gpu off` runs the bang on the CPU pool
(16 threads) and `--gpu on` runs it on the 3090. This is the same source and
the same build, and no CUDA was written. The GPU program is NVRTC-compiled with
`--fmad=false` (`comp.ts:6533`), so no mul+add fuses into an FMA. That is why
bit identity with the CPU is possible at all.

## 2. The four-lane law on the GPU

`place.py measure` compares **every** run's stdout to the twin's, byte for
byte, and stops the script on any difference. That covers 200 + 40 + 6 + 1 +
1 + 1 + 1 runs per unit plus the routed runs. Each row stores what the lane
printed (`four`) next to what the twin printed (`twin`), and `run.sh`
re-asserts `off == on == twin` per size:

    cols      acc         or          and         nonfinite
    1024      340750020   4294967295  0           0
    16384     2008321637  4294967295  0           0
    131072    2975651827  4294967295  0           0
    1048576   1291939912  4294967295  0           0
    4194304   856031264   3355443199  1073741824  0
    8388608   65632       3355443199  1073741824  0
    16777216  1342242816  3355443199  1073741824  0

`or != and` and nonfinite = 0 in every row, so the probes pass as well. The
twin threads its 16384 rows over 16 pthreads into an array and joins the tree
serially. Before `run.sh` used it, it matched the single-threaded twin's output
at 1,024, 131,072 and 4,194,304 cols. `run.sh` deletes the twin's cached
answers at the start of every run.

## 3. The table

Box: Ryzen 7 7700X (8C/16T), RTX 3090 (driver 580.119.02, limit 370 W), CUDA
13.1, clang 21.1.7. **The box was shared**: load average was 5–15 from other
lanes' gates during the run (`load` per row). `runs` is the batch size: runs
back to back inside one window, the same count for both units at a size.

| cols | MACs | unit | runs | wall s (median) | window s | CPU J net | GPU J net | **J/run** | ± J/run | nJ/MAC |
|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|---:|
| 1,024 | 16.8 M | CPU | 200 | 0.011 | 4.0 | 23.5 | −108.4 | **−0.42** | 0.51 | — |
| 1,024 | 16.8 M | GPU | 200 | 0.100 | 29.1 | 110.2 | 2132.7 | **11.2** | 0.32 | 668 |
| 16,384 | 268 M | CPU | 40 | 0.073 | 4.0 | 99.5 | 9.5 | **2.73** | 0.29 | 10.2 |
| 16,384 | 268 M | GPU | 40 | 0.116 | 9.0 | 38.7 | 591.7 | **15.8** | 0.58 | 58.7 |
| 131,072 | 2.15 G | CPU | 6 | 0.452 | 4.0 | 148.9 | −8.4 | **23.4** | 2.0 | 10.9 |
| 131,072 | 2.15 G | GPU | 6 | 0.198 | 6.0 | 10.9 | 394.4 | **67.6** | 5.8 | 31.5 |
| 1,048,576 | 17.2 G | CPU | 1 | 3.455 | 5.1 | 189.4 | 10.3 | **200** | 13 | 11.6 |
| 1,048,576 | 17.2 G | GPU | 1 | 0.856 | 9.0 | 2.4 | 299.6 | **302** | 39 | 17.6 |
| 4,194,304 | 68.7 G | CPU | 1 | 13.70 | 17.2 | 610.9 | 29.4 | **640** | 99 | 9.3 |
| 4,194,304 | 68.7 G | GPU | 1 | 2.925 | 8.0 | 29.9 | 612.2 | **642** | 36 | 9.3 |
| 8,388,608 | 137 G | CPU | 1 | 27.96 | 29.4 | 1223.4 | −13.1 | **1210** | 197 | 8.8 |
| 8,388,608 | 137 G | GPU | 1 | 5.676 | 11.1 | 79.9 | 970.0 | **1050** | 75 | 7.6 |
| 16,777,216 | 275 G | CPU | 1 | 54.62 | 55.7 | 2755.8 | −134.6 | **2621** | 709 | 9.5 |
| 16,777,216 | 275 G | GPU | 1 | 11.19 | 17.1 | 21.8 | 1829.4 | **1851** | 245 | 6.7 |

J/run is (CPU J net + GPU J net) / runs, **both rails for both units**. A GPU
run also spins a host thread, and a CPU run leaves the GPU drawing whatever the
desktop draws. The negative entries are noise, not credits: a rail's
idle-subtracted draw came out under its baseline. The 1,024 CPU row is the
clearest case. Its GPU idle before the batch read **70.2 W** against 20.7 W
after, because something else used the card during the idle window, and the
mean of the two over-subtracts. That row reads "under the noise floor", not
−0.42 J.

## 4. Why the GPU loses until ~4M cols

The run windows in the `gpu_on_*.csv` samples can be split at the run's end
(row start + median wall) for the single-run rows. This split is arithmetic on
the committed CSVs and rows (trapezoid, net of the row's mean idle); `run.sh`
does not print it:

| cols | wall s | GPU net J, in the run | GPU net J, after exit | tail s | peak W | mean W in run |
|---:|---:|---:|---:|---:|---:|---:|
| 1,048,576 | 0.86 | 34.6 | 252.1 | 8.2 | 151 | 66 |
| 4,194,304 | 2.92 | 357.5 | 242.8 | 5.1 | 178 | 146 |
| 8,388,608 | 5.68 | 698.5 | 259.5 | 5.4 | 194 | 145 |
| 12,582,912 | 8.46 | 1098.4 | 311.3 | 4.6 | 195 | 152 |
| 16,777,216 | 11.19 | 1478.3 | 339.0 | 5.9 | 194 | 154 |

The split smears by up to ~0.5 s, because `power.draw.instant` refreshes about
twice a second (see residuals). The tail column is still unmistakable: about
**250–340 J per launch whatever the size**. In `gpu_on_1048576.csv` the card
reads ~126 W for ~1.3 s after the run ends, then 25–30 W for ~4 s, and is back
at 18.7 W about 6 s after exit. That tail belongs to the run that caused it.

*Derived, not measured:* a line through the three largest GPU rows gives
≈ 250 J + 5.8 nJ/MAC. The CPU pool is roughly flat at 9–11 nJ/MAC from 16k
cols up. The two meet near 60 G MACs, about 3.6M cols, which agrees with the
measured 4M tie.

Below ~16k cols, the GPU's cost per run is mostly the process's CUDA
bring-up. `wall_s` is ~0.10 s even at 1,024 cols (CPU: 0.011 s), and 200 of
those back to back held the card up for 29 s.

## 5. The integration method and the baselines

- **CPU rail.** `/run/power-sampler/latest.json`: `intel-rapl:0` = package-0
  `energy_uj` plus its `ts`, rewritten about once a second. A window opens on a
  sampler tick (polled at 10 ms) and closes on the first tick after the GPU has
  settled. J = Δenergy_uj / 1e6. The counter wraps at
  `max_energy_range_uj` = 65,532,610,987. It wrapped once during this lane,
  between the smoke tests (63 G) and the cited run (6.2 G at its first row),
  and no cited row straddles a wrap. Δ is taken modulo the range regardless.
- **GPU rail.** `nvidia-smi --query-gpu=power.draw.instant -lms 100` runs as a
  single long-lived process for the whole row. Each line is stamped with
  `time.time()` on arrival (the pipe is line-buffered; checked at 100 ms
  cadence). J = the trapezoid integral over the same window, with the window's
  edges holding the nearest sample. `power.draw` (the default) is a 1 s
  average on Ampere, so `.instant` is used instead.
- **One window for both rails.** It closes only after 1 s of GPU samples sit
  under the pre-batch GPU idle + 4 W (15 s cap), and then on the next sampler
  tick. So the GPU tail is inside the window, and the CPU rail covers the same
  seconds.
- **Idle baselines, both rails, per row.** Each is measured over ~4 s (two
  sampler ticks apart), once **before** and once **after** each batch. The
  **mean** of the two is subtracted over the whole window, from both rails.
  Measured idles: CPU package **51.7–100.3 W** (the other lanes' load, not
  this machine's true idle); GPU **18.3–23.8 W**, except the one 70.2 W outlier
  above. `±J/run` = half the pre/post gap on each rail × window / runs. It is
  the drift of the other lanes' load across the batch, shown as an error bar
  rather than hidden.

## 6. The policy

`place.py route OUT M` reads `table.jsonl` and predicts J/run for `M` cols on
each unit:

- **By default**, it interpolates log-log (linear in log J vs log cols) between
  the two nearest measured sizes. Above the largest measured size it holds the
  largest row's value; below the smallest it extends the line through the two
  smallest.
- **If a bracketing J is ≤ 0** (noise floor), it interpolates linearly instead.

It picks the lower prediction, prints the decision and the numbers behind it
to stderr (`route.log`), and prints the unit. `run.sh` then runs that unit and
measures it into `routed.jsonl`:

    route m=4096 (67,108,864 MACs): predicted J/run  CPU 0.206  GPU 13.295  -> CPU (16 threads)
        4096  off  100 runs  0.023 s  measured 1.417 ± 0.292 J/run
    route m=12582912 (206,158,430,208 MACs): predicted J/run  CPU 1902.063  GPU 1462.928  -> GPU (RTX 3090)
    12582912   on    1 run   8.462 s  measured 1471.494 ± 30.245 J/run

The big prediction landed within 0.6%. The small one is under the noise floor
on both sides of the comparison. The CPU's 0.206 is interpolated from the
−0.42 row, and the measured 1.4 J/run is ~7x that, but both are ~10x below the
GPU's 13.3, so the decision does not depend on it. Both routed runs printed the
twin's four lines.

## Residuals, named

- **A shared box.** Other lanes' gates ran throughout (load 5–15). CPU idle
  moved by up to 24.5 W inside one batch (the 16M CPU row: 51.7 → 76.2 W).
  That is why that row carries ±709 J. **The 8M and 16M GPU wins are inside
  the CPU rows' error bars**; only the point estimates favour the GPU.
  Worse, the error bar does not capture displacement: on a loaded box, this
  program's 16 threads take cores from other work rather than adding their
  full draw. The measured CPU net (~44–55 W for 16 busy threads) is therefore
  likely a *lower bound*. If so, the CPU looks cheaper here than on a quiet
  box, and the true crossover sits at or below 4M cols. A quiet-box rerun is
  the fix: `bash demos/placement/run.sh` needs no arguments.
- **Rail scope.** The CPU rail is package-0 only: no DRAM, VRMs, fans, PSU
  loss or the rest of the board. The GPU rail is NVIDIA's board-power sensor
  (±5 W per its own docs), which means the whole card. Neither is wall power.
- **Sampling granularity.** The CPU rail refreshes at 1 Hz. The windows are
  aligned to its ticks, so what it adds is idle seconds that the baseline
  subtracts, but a sub-second run's own energy is below its resolution; the
  small sizes are batched (200 / 40 / 6 runs) for that reason. The GPU is
  polled at 100 ms, but `power.draw.instant` visibly changes only about every
  0.5 s (repeated values in `gpu_*.csv`). That smears where the run ends and
  the tail begins (§4), not the window's total.
- **Launch overhead is included on purpose.** Each run is a fresh process:
  CUDA context, module load and the clock ramp for the GPU; `fork` + `exec`
  for both units. A resident runtime that keeps a context and dispatches many
  bangs would pay the ~250–340 J tail once per burst, not once per run. The
  small-size GPU rows (batched, so the tail is amortized over 200 or 40 runs)
  are already the generous case for the GPU, and it still loses there: 5.8x at
  16k cols, and at 1k cols 11.2 J against a CPU row that is under its ±0.5 J
  noise floor.
- **Occupancy.** The runtime's lane cube is 16384, so 16384 rows keep ~13%
  of a 3090's resident threads busy (82 SMs x 1536, from the spec sheet, not
  measured). The GPU peaked at ~195 W against a
  370 W limit. A kernel that filled the card would move the crossover. This
  lane measured the runtime as it is.
- **The kernel is compute-only by design.** A decode that reads real weights
  would put managed-memory page faults on the GPU side of the ledger.

## Receipts, and a gate conflict

The brief says receipts go in `demos/placement/receipts/`, and `run.sh`
writes them there. But `gates/repo.ts` only allows
`demos/<dir>/<name>.(bend|c|sh|md|py)`, so a tracked file under
`demos/placement/receipts/` fails the gate for every lane. The receipts
directory therefore stays **untracked**, regenerated by each run (**never
`git add demos/placement`** wholesale). The run this report cites is
committed under `docs/omen/lanes/placement-evidence/`, where
`docs/omen/…` is allowed; `kernels-2-evidence/` set that precedent. A
`.gitignore` line would be the cleaner fix, but `.gitignore` was outside this
lane's editable set.
