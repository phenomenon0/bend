# demos/parallel — two things only Bend gives you from one source

Both demos scan a generated text corpus (mixed ASCII/Unicode words, ragged
whitespace): lines → trim → words → a rolling checksum of every code point.
Every result is asserted byte-identical across lanes **and** equal to an
independent Python oracle. The scripts print only what they measure.

Machine for the tables below: Ryzen 7 7700X (8 cores / 16 threads), 30 GB,
RTX 3090, clang 21, CUDA at `/usr/local/cuda`. Measured 2026-09-18 **while the
machine was shared with other jobs (load average 9–16)**; a quiet machine
should do better. Re-run to get your own numbers.

## 1. The thread knob — `knob.bend`, `run_knob.sh`

```bash
demos/parallel/run_knob.sh            # corpus is generated on first run (~1 min)
SHARED=1 demos/parallel/run_knob.sh   # also show the formulation that does NOT scale
INTERP=full demos/parallel/run_knob.sh  # interpret the full corpus too (~4 min)
```

The parallel API is one line of `knob.bend`:

```python
a b = scan(p, block, String.take(s, half)) scan(p, block, String.drop(s, half))
```

One binary, compiled once; 575,739,085-byte corpus (536,870,912 code points,
96,728,910 words); median of 3:

| `--threads` | wall s | speedup | scan s | speedup | output |
|---:|---:|---:|---:|---:|---|
| 1  | 6.98 | 1.00× | 5.19 | 1.00× | `96728910:3451786287` |
| 2  | 4.71 | 1.48× | 2.74 | 1.90× | same |
| 4  | 3.36 | 2.08× | 1.43 | 3.64× | same |
| 8  | 2.81 | 2.49× | 0.93 | 5.56× | same |
| 16 | 2.79 | 2.50× | 0.83 | 6.22× | same |

`wall` includes reading and UTF-8-decoding the file, which is serial
(~1.7 s); `scan` is the fork/join tree only. Same program interpreted
(`bun bend2/main.ts knob.bend`): 18 MB slice in 6.0 s, full corpus in 233 s,
both equal to the oracle.

**Honest limit.** Without the `String.copy` in the leaf (all words are views
of ONE shared payload, so every core counts references on the same cell) the
same tree does not scale: scan 5.58 s → 4.30 s at 16 threads (1.30×).
`SHARED=1` measures that variant next to the real one.

On camera:
- "There is no thread code in this file. This one line says: these two calls are independent."
- "Same binary. I only turn the knob: one thread, five seconds; sixteen, under one."
- "Every run prints the same bytes, and Python agrees."
- "And the honest part: share one buffer across all cores and you get nothing. One copy per block fixes it."

## 2. The GPU lane — `gputext.bend`, `run_gputext.sh`

```bash
demos/parallel/run_gputext.sh                       # 18 MB, 72 MB, 288 MB at --gpu 4GB
SIZES=8192 GPU_MEM=8GB demos/parallel/run_gputext.sh  # the full 576 MB corpus
```

Independent 64K-code-point chunks; per chunk the word scan plus a native
`String.count(s, "gpu")`; results joined in order. The whole GPU API is the
`!` in `scan!(...)`. One compile emits `gputext` (222 KB) and `gputext.gpu`
(113 KB). Median of 3, after one untimed warm GPU run:

| corpus | lane | wall s | scan s | output |
|---|---|---:|---:|---|
| 18 MB  | `--gpu off` | 0.10 | 0.03 | `3023519:570736648:119881` |
| 18 MB  | `--gpu 4GB` | 0.84 | 0.68 | same |
| 72 MB  | `--gpu off` | 0.35 | 0.12 | `12090272:3856248570:480504` |
| 72 MB  | `--gpu 4GB` | 1.72 | 1.35 | same |
| 288 MB | `--gpu off` | 1.85 | 0.74 | `48363448:228016294:1922675` |
| 288 MB | `--gpu 4GB` | 2.93 | 2.02 | same |
| 576 MB | `--gpu off` | 3.10 | 1.10 | `96728910:3451786287:3844342` |
| 576 MB | `--gpu 8GB` | 4.17 | 2.52 | same |

During the GPU run `nvidia-smi` lists the process as a compute app (258 MiB)
and GPU utilization peaks at 100 %.

**Honest limits.** The GPU is *slower* than 16 CPU threads on this branchy
text work (the guide says so: the GPU shines on uniform numeric work). The
576 MB corpus does not fit a 4 GB span (`bend: out of memory: run again with a
bigger span`); 8 GB works. The claim is "same source, same bytes, no CUDA
written" — not throughput.

On camera:
- "One character — this bang — and the same function runs on the 3090. I wrote no CUDA."
- "CPU lane, GPU lane: identical output, and Python agrees."
- "It's not faster here — text is branchy, the CPU wins. For uniform numeric work the GPU wins. Same source either way."

## Files

`gen_corpus.py <out> <blocks>` writes the corpus and its oracles
(`.oracle`, `.oracle_gpu`) to `$HOME/videokit-corpus/` (not committed). Blocks
are exactly 65,536 code points of whole lines, so a cut at a block boundary
never splits a word and chunked scans equal the whole-text oracle.
