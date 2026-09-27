# Foundations pass — measured candidate, not a landing decision

2026-09-27 · astra-foundations · `foundations-pass` · starting commit `0c2d291d`.
Candidate code/test commit: `5a5da0c2` (separate from this report and evidence).

## Decision in brief

Keep one **candidate**: seven host-runtime lines using `memcpy` for unretained
block copies of at least 128 bytes. Measured clone-loop speedups are 2.11–2.16×
for 1 MiB and 3.34–3.56× for 8 KiB. There is a small-copy tradeoff: the 16-byte
clone loop was 1.8–2.3% slower in the two retained-cutoff comparisons. This is
not an engine speedup claim, and it is not permission to land the candidate.

The historical four-thread parallel GEMV knee is **already fixed in this HEAD**.
Restoring just contiguous ring assignment in temporary emitted C reproduces it.
The measured cause is coarse, uneven work assignment, not allocator-bank lock
contention. No scheduler change is proposed.

No arithmetic order, four-lane dot identity, prelude API, device path, checker,
compiler flag, or cap was changed. `bend2/bend.ts` was never edited. The
orchestrator decides whether the bulk-copy tradeoff warrants landing.

## Measurement and evidence

Host: Ryzen 7 7700X, eight physical cores / sixteen logical threads, Fedora 43,
Clang 21.1.7. This was a busy shared machine, not an isolated performance lab.
Load averages below are system load averages, **not occupied-core counts**.

Native ablations use `-std=c11 -O3 -ffp-contract=off`, `-lpthread -lm`, and
`--gpu off`. No reassociation, fast-math, FMA permission, or architecture tuning
was added. Repeated comparisons alternate variant order and use medians.
Timing holds `/tmp/bend-bench.lock`; unrelated work need not honor that lock.
Each timed run checks its exact stdout. Parallel GEMV additionally matches the
existing C twin's checksum, `646920195`.

Retained evidence under [`foundations-evidence/`](foundations-evidence/):

- `bench.py`: executed reproduction of the candidate and scheduler
  counterfactual; temporary emitted C only, no source rollback or external repo
  writes. Nine samples per variant. Run with
  `python3 docs/omen/lanes/foundations-evidence/bench.py`.
- `measurements.jsonl`: every sample and its load average from that reproduction.
- `exploration.jsonl`: original cutoff search, initial parallel curve, scheduler
  ablations, observed queue occupancy, per-worker probes, and tensor harness
  outputs, including rejected variants.
- `checks.txt`: verification receipts, including failures and exclusions.

Temporary generated C, binaries, venv, and exploratory scripts stayed under
`/tmp/astra-foundations/`; they are not deliverables. The pre-existing repository
`receipts/` directory was not edited or staged by this lane.

## Ranked findings

| Rank | Finding | Evidence / action | Real-workload relevance |
|---|---|---|---|
| 1 | Generic unretained block copies leave substantial host bandwidth unused | Retain the bounded `memcpy` candidate; details below | Activation/cache/attention clones can benefit; current weight reader and dot arithmetic do not directly benefit |
| 2 | C7's four-thread knee was a scheduling-granularity problem, already repaired | Current curve scales to 16T; restoring contiguous rings restores the plateau | Avoid spending another lane on a nonexistent current bank-lock bottleneck; no new speedup credited here |
| 3 | Automatic grouping of adjacent scalar reads remains a compiler opportunity | Existing `get4` group guard is the measured solution; no automatic pass implemented | Would remove manual load grouping, but current llama reader already calls `get4` |
| 4 | A native bulk reduction must implement the workload's actual reduction tree | No primitive added; serial/four-accumulator dot is not a substitute | Potentially useful only with a precise tree-order contract and matching C twin; no quantified remaining gain |
| 5 | Packed byte-word reads already exist; allocation/ownership changes need separate evidence | Reuse existing primitives; do not introduce a second packed reader or zero-copy tree fiction | Current engine's larger weight-read problem has already been addressed by another lane |

### 1. Bulk copy: mechanism, cutoff, and limits

`blk_fill` previously copied every Term in a loop, with a conditional retain.
The candidate is only:

```c
#if !DEVICE
  // Fresh blocks cannot overlap; keep leaf-sized copies inline.
  if (!keep && n >= 16) {
    memcpy(e.mem + dst, e.mem + src, n * sizeof(Term));
    return;
  }
#endif
```

`n` counts 64-bit Terms, so the threshold is 128 bytes. Packed F32/U32 arrays
store two cells per Term. This does not change representation or eliminate the
copy: it delegates sufficiently large raw copies to the host's native copy
implementation, consistent with the existing string-copy use of libc.
On this host, `OUTLINE` marks `blk_copy` `noinline, cold`. Disassembly of the
measured baseline shows one 64-bit load/store per raw-copy loop iteration; the
candidate has a guarded `memcpy@plt` call instead. Those instruction excerpts
are retained in `checks.txt`; no global optimization-attribute change was made.

All immediate callers were inspected:

- `blk_copy` allocates a fresh destination. Boxed `ARR` elements still request
  `keep=true` and go through `blk_keep`, not `memcpy`.
- `blk_node` allocates a fresh combined block and writes two disjoint halves;
  both source owners remain live until those copies finish.
- `blk_half` allocates a fresh half; the high-half path frees its source only
  after copying. Shared boxed halves retain each element.
- Host allocation failure exits through `err_fail`, rather than continuing with
  an aliasing destination. The device preprocessor excludes the new branch.

This justifies `memcpy`, rather than overlap-tolerant `memmove`. The source can
itself be shared, but it cannot overlap the fresh destination. Small and
retaining copies keep the original loop. Ownership, allocation, wrapping,
boxing, and all floating-point operations are otherwise unchanged.

#### Cutoff search (nine interleaved samples, seconds)

Load1 during this search: 5.77–6.12. Workload sizes and repetitions are reproduced
in `bench.py`. The tree workload clones a 2,048-cell array and consumes the clone
by balanced splitting/summing, repeated 4,096 times.

| Workload | Original loop | Unconditional memcpy | Cut 8 Terms | **Cut 16 Terms** | Cut 128 Terms |
|---|---:|---:|---:|---:|---:|
| Tree sum | 0.060869 | 0.065869 | 0.062907 | **0.061343** | 0.061967 |
| 16-byte clone | 0.048979 | 0.050195 | 0.049409 | **0.049876** | 0.052700 |
| 8 KiB clone | 0.029652 | 0.008825 | 0.008797 | **0.008866** | 0.009320 |
| 1 MiB clone | 0.289498 | 0.137267 | 0.139852 | **0.136902** | 0.135270 |

**Rejected:** unconditional `memcpy`, despite its large-copy wins. It regressed
this tree workload by 8.2% in the cutoff comparison (5.7% in the earlier shape
comparison). Copying the many small halves through libc was not free.

The retained 16-Term cutoff preserves the large-copy wins while putting the
tree result within 0.8% of its original median. This is an empirical cutoff for
this host, not a universal optimum. Tiny-copy overhead remains a tradeoff.

#### Independently rerun retained candidate (nine interleaved samples)

| Workload | Before | Candidate | Interpretation | Load1 range |
|---|---:|---:|---|---:|
| 1 MiB clone × 8,192 | 0.300546 | 0.139198 | 2.16× faster | 10.66–11.33 |
| 8 KiB clone × 131,072 | 0.032179 | 0.009048 | 3.56× faster | 10.66 |
| 16-byte clone × 4,194,304 | 0.052831 | 0.054067 | 2.3% slower | 10.13–10.66 |
| Tree sum | 0.062530 | 0.062629 | 0.2% slower; no win claimed | 10.13 |

The repeated direction of the tiny-copy delta is disclosed, not dismissed as
proof of noise. These are complete process/loop timings, not isolated memcpy
bandwidth measurements. No claim is made about end-to-end token throughput.

#### Regression intent and review

`tests/reg/array_copy_bulk.bend` checks every U32 cell **in order**, before and
after independently modifying a clone. Sizes 16/32/64 cells exercise 64/128/256
bytes, below/at/above the cutoff, with splitting and rebuilding. A separate
boxed case constructs distinct strings at runtime, clones their array, and
consumes both owners.

The first draft only checked sums and repeated literals. Independent review
correctly identified that permutations and some lifetime defects could pass.
A temporary emitted-C mutation removing `!keep` indeed survived that draft.
The strengthened witness rejects both tested mutations:

1. Copy `(n - 1) * sizeof(Term)` bytes instead of `n * sizeof(Term)`.
2. Remove the `!keep` condition, wrongly copying owning handles without retain.

Both mutants exit zero but print incorrect output; stdout comparison, not
sanitizer detection, kills them. The unmutated witness passes ASan+UBSan at
`-O1`, and its normal check/interpreter/JS/C lanes pass. The reviewer re-read the
strengthened witness and found both coverage gaps addressed; the review itself
was static and did not independently rerun tests.

### 2. C7 knee: an existing fix, with a causal counterfactual

Current baseline, five samples per thread count, load1 3.34–4.52:

| Threads | Median seconds | Speedup from 1T |
|---:|---:|---:|
| 1 | 0.337027 | 1.00× |
| 2 | 0.175536 | 1.92× |
| 4 | 0.092118 | 3.66× |
| 8 | 0.054063 | 6.23× |
| 16 | 0.042880 | 7.86× |

The runtime currently stripes ring assignment within each row. Replacing just
that assignment with the older contiguous `r * LINE + i` mapping, in emitted C,
restores the plateau. No compiler source change is needed for this experiment.

Seven-sample ablations, load1 approximately 5.14–5.29:

| Threads | Current striped | Contiguous | Plain bank counters | Plain private ring cursor |
|---:|---:|---:|---:|---:|
| 4 | 0.090923 | 0.095496 | 0.091145 | 0.091583 |
| 8 | 0.053956 | 0.091417 | 0.053999 | 0.053448 |
| 16 | 0.043882 | 0.090866 | 0.044177 | 0.042783 |

The bank and ring-counter experiments do not establish a worthwhile gain and
are **not retained**. In the 8T striped probe there were zero bank-lock retries,
zero pushes, and 28 pops, all empty. This benchmark is not spending its time
contending over allocation-bank locks.

Observed queue occupancy explains the difference (load1 5.19): two grow workers
each execute one shard; **62**, not 64, tasks remain, 31 per populated row at
ring offsets 31–61. Contiguous mapping groups each row as `[1, 16, 14]`, producing
four heavy indivisible units. Striped mapping spreads these over 16 units:
14 units with four tasks and two with three. The 8T probes show approximately
39–47 ms drain work per striped worker, versus four contiguous workers with
74–86 ms, two with about 5–6 ms, and two essentially idle.

The original static hypothesis was that fork-free-leaf handoff queued all 64
leaves. The measured frontier disproved that: this call shape goes through
`emit_fuse`, bypassing the explicit handoff, and `par` is classified forky at
segment level, not separately for its depth-zero branch. Credit **striping** for
this particular benchmark, not leaf handoff.

The relevant pre-existing change is `cea509768d72eb22b977c23816c893b77fe7ff2f`,
“Run fork-free leaves sequentially and distribute CPU ring work”; the later
`aa5208a6` is cleanup. This lane did not invent or reapply that fix.

The committed reproduction repeated the counterfactual under higher load:

| Threads | Striped | Contiguous | Load1 range |
|---:|---:|---:|---:|
| 1 | 0.331152 | 0.330621 | 9.48–10.13 |
| 2 | 0.173713 | 0.172841 | 9.12–9.48 |
| 4 | 0.092510 | 0.096602 | 9.12 |
| 8 | 0.054758 | 0.092162 | 8.87–9.12 |
| 16 | 0.043795 | 0.092579 | 8.87 |

### 3. Automatic adjacent reads: useful, but not implemented

The older tensor-view receipt attributes failed widening to the `blk_ptr` cast.
The newer C2b2 experiments and current `get4` implementation support the more
specific diagnosis: individually wrapped offsets block contiguous-load
reasoning; a **group range guard** enables it. A pointer-cast-only fix was not
sufficient. Use the later measured explanation rather than blending them.

A correct automatic pass needs to recognize adjacent reads of the same owned
array through the emitted ownership/continuation flow, preserve wrapping at the
last cells, and respect intervening writes, effects, and boxed retain behavior.
This is not safely replaced by a regex over emitted C or by one guard per read.

No automatic pass was written or benchmarked here. Existing `Array.get4`
already closes the measured tensor gap to roughly 1.06–1.11× C in the historical
receipts. The current llama-bend reader uses it already. Compiler headroom was
only 102 tokens initially and is 49 after this candidate; a general pass would
need an explicit scope/cap decision or compensating simplification, not a hidden
cap increase. Do not allocate the historical 2.6× gap as an additional available
speedup on today's reader.

### 4. Bulk dot/reduce: preserve the real oracle, not an attractive loop

The read-only llama-bend reference at
`9a6e71ce17b9cfa8b0bfe0b76aacba6cb7b89abc` uses a balanced adjacent-pair F32
reduction tree. Width 6,144 is zero-padded to 8,192. Its quad combines
`(w0*x0 + w1*x1) + (w2*x2 + w3*x3)`; higher levels retain that exact tree.

**A serial dot or four independent running accumulators changes FP order and
is not oracle-equivalent.** No such replacement was made. A native primitive
would need a declared tree/zero-padding contract, C twin, exact float fixtures,
wrap/shape laws, and cross-backend implementation. The engine already amortizes
reads over quads; this lane has no measurement showing how much further gain a
native reduction would buy. No speculative prelude API was added.

### 5. Current engine relevance and limits

`kernels/io.bend`, `kernels/gemv.bend`, the relevant operations and engine callers,
and `reports/llb-forward.md` were inspected read-only. Current dimensions include
42 layers, model width 2,048, FFN width 6,144, and vocabulary 130,560.

The current reader already consumes one packed `Bytes` per layer, reads weights
with `Bytes.word_le`, and reads activations with `Array.get4`. The native
`str_word_le_peek` already has a packed four-byte path. A second word-read
primitive would duplicate existing machinery. Array pattern matching/rebuilding
really allocates/copies; it is not a free persistent-tree view.

The reference fast-lane commit reports 902.6 s → 41.9 s per step at 16T. That is
**another lane's result**, not a foundations result. The prompt's approximately
42-second logits and 2.5-second FFN-down bill describes an older reference
state, not a measured bill with this candidate. Operation clocks also omit
some orchestration/cache/loading costs. No full-engine run was performed here.

The bulk-copy candidate can reduce existing clone/copy costs in RMS, cache, and
attention work. It does not directly speed the current packed weight reader,
change `io.rows`' sequential ownership flow, or accelerate dot arithmetic.
Amdahl's fraction was not measured, so no projected seconds/token are given.

## Tensor harness before / after

`bash demos/tensor/bench.sh` passed exact-output and nondegeneracy checks both
times. These are the harness's reported timings, not the nine-sample clone
experiment above.

| Bench | C before | Bend 1T before | Bend 16T before | C after | Bend 1T after | Bend 16T after |
|---|---:|---:|---:|---:|---:|---:|
| gemv | 0.151 | 0.157 | 0.159 | 0.157 | 0.162 | 0.162 |
| split | 0.153 | 0.157 | 0.155 | 0.156 | 0.161 | 0.160 |
| blocked | 0.042 | 0.045 | 0.046 | 0.043 | 0.050 | 0.049 |

Load before: `5.66 5.82 5.74`; after: `7.38 5.96 5.57`.
The blocked 1T/C ratio moved from 1.09× to 1.17×; this is not hidden. However,
compiling the before/after emitted C with identical flags gives byte-identical
`.text` for blocked, SHA-256
`71ffff6bdedc4474dbbb84c42fb1ff6b7b744ecc81f55fb2309f33318100da21`.
The extra runtime branch is unused there. These wall-time samples do not
establish a generated-code regression or a tensor speedup from this candidate.

## Verification and honest failures

Verification completed locally. This is not an all-green repository: the native
socket test timed out and the repository gate retains seven baseline failures.

Verified:

- `bash tests/run.sh`: **22 pass, 0 fail**, including the harness's `mc_pi [gpu]`.
- `bash tests/power/run.sh`: **190 pass, 0 fail**, including Python oracle
  fixture comparisons, check/interpreter/JS/C/C-1T and the deliberately wrong
  expected-output control. Full suite, no prefix filter.
- `bash demos/tensor/run.sh`: **10 pass, 0 fail**.
- `bash tests/strings/run.sh`: **101 pass, 1 fail**. The native
  `io_sock_utf8` printed only `263802747` and stalled; it was bounded to the
  harness's usual 300 seconds by signaling its `timeout` wrapper at 300.9 s,
  producing status 124. `STRING_TIMEOUT=1500` was used for the suite to allow
  the slow `deep` interpreter, which completed successfully without interruption.
  No fixture was skipped. Native socket before/after `.text` is byte-identical,
  SHA-256 `0599470209b894feba3a1e8f8fb78b3e464333e86f961e27f36600a98358af56`;
  the candidate does not change that executable's instructions. This does not
  make the failing test a pass. Its check/interpreter/JS lanes passed.
- Focused Arrays: **159 checks pass, 0 fail**, covering 21 runnable specimens
  with check/interpreter/JS/C-1T/C-16T, their builds, plus four ASan+UBSan cases
  (`array_copy_bulk`, `array_clone_boxed`, `array_fork_unshare`, `array_split_join`).
  The count includes build/emit steps; it is not 159 distinct fixtures.
- New witness mutations: both rejected by exact output; unmutated sanitized
  native witness passes. Independent static runtime review found no correctness
  issue; the two test-coverage findings were fixed and re-reviewed.
- `bash tests/caps.sh`: exit zero. Compiler 99,151 / 99,200 tokens; prelude
  63,739 / 64,000, unchanged. No cap edits.

The string and power Python oracles use an isolated `/tmp` venv: CPython
3.11.14, NumPy 2.4.6, SciPy 1.17.1, zlib 1.3.1. This is **not** the 3.11.15
interpreter mentioned by some older receipts. The actual fixture comparisons,
not a presumed compatible version number, determine the oracle verdicts. No
Python dependency or environment file was added to the repository.

Array exclusions are explicit, not a claim that every `array*.bend` passed:
`array_open_element` is an open-element-type compile-negative specimen;
`array_bounds_000`, `array_bounds_001`, `array_slab`, and `array_struct_swap`
contain obsolete syntax rejected before this runtime is reached. The initial
broad runner also misclassified the exact unsafe/foreign-code informational
notice as an error on three otherwise passing specimens. The final runner
accepts only that exact notice, never arbitrary stderr. No historical fixture or
checker was edited to obtain the focused result. The exploratory runs recorded
139 pass / 29 fail initially, then 159 / 8 after fixing notice handling and three
exclusions; the remaining eight failures were the four attempted lanes each for
`array_slab` and `array_struct_swap`. The final 159 / 0 is explicitly the runnable
subset, after strengthening the new witness and excluding all five named files.

Before this lane and after the code change, `bun gates/repo.ts` reports **93/100**
with the same seven failures, also unchanged with all deliverable paths staged:

```text
bend2/effs/tls_listen.c          6726 > 4000
demos/io_http_engine/PROOF.bend  200564 > 64000
demos/io_http_engine/README.md   19215 > 4000
demos/io_http_engine/check.c     21361 > 4000
demos/io_http_engine/control.c   5886 > 4000
power/deflate_proof.bend         85426 > 64000
upstream/verify.sh              4370 > 4000
```

The number is the gate's own score, not a fraction of individual files. New
files are included only once staged; final staged results are recorded with the
verification receipts. Neither `gates/repo.ts` nor `tests/caps.sh` was changed.

Not run: the mini-cluster full `gates/test.ts`, performance and release gates;
a dedicated Metal/CUDA candidate campaign; llama-bend end-to-end or NumPy engine
oracle. The host-only preprocessor guard and existing GPU-labeled harness passes
are not substitutes for a full device campaign.

Read gaps: the requested `docs/omen/lanes/c2b.md` and
`docs/omen/reports/plan-beat-c-one-core.md` were absent under those names. Related
claims in C2b2/C3 were read, but that is not equivalent to reading those missing
files. Compiler and prelude reading was targeted at the actual access, emission,
ownership, copy, allocation, and scheduling paths, not a claim to have audited
every line of the language implementation.
