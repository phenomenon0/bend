# String lanes

Run from the repository root:

```sh
bash tests/run.sh --strings  # or bash tests/strings/run.sh
python3 tests/strings/runtime.py
bash tests/strings/bench.sh  # reproducible baseline/candidate acceptance
```

`run.sh` independently checks each specimen, then compares its measured `#|`
block with interpretation, emitted JS, and emitted C. `gpu.bend` also executes
on CUDA/Metal when available; absence of a device fails that lane. The f64
runner remains `bash tests/run.sh` (16 results); numerical edge regressions
remain `bash tests/codex/run.sh` (161 results).

`raw_strings.bend` is the one intentional JS rejection. Its exact diagnostic
and exit status are checked against `raw_strings.js-error`; interpret and C
preserve the raw U32 cells. `raw_chars.bend` succeeds on every lane.

`deep.bend` is a **pure** main. It constructs 180,224 characters for each of
length, split, words, and uppercase comparison, returning four booleans so that
strong normalization does not need to print a huge unary Nat or string. Each
scan gets a fresh source to avoid retaining an entire normalizer graph across
all four tuple fields. The expected lengths are arithmetic expressions because
a literal `180224n` itself exceeds the checker's current syntax-walk stack.
The interpreter is intentionally allowed 300 seconds (`STRING_TIMEOUT` can
change this). This does not claim general checker stack safety.

`io_utf8.bend` is an IO main, so its CLI/interpret lane uses JS IO. It reads
`utf8.bin`, whose bytes are:

```text
ef bb bf 41 00 f0 9f 98 80 c0 80 ed a0 80 f4 90 80 80 e2 82
```

The expected code points preserve the BOM and NUL and replace each ill-formed
byte individually. The runtime probe additionally checks C and JS against an
independent Python strict-decoding oracle on 517 byte vectors.

`runtime.py` emits a fresh C/JS runtime into a temporary directory. The C probe
runs under ASan/UBSan and instruments Corpus allocations (ASan cannot detect
intra-Corpus frees by itself). It checks descriptor/payload ownership, static
immutability even behind a count wrapper, alias detachment, unique payload
reuse, geometric growth, zero-copy split fields, tiny-view retention followed
by compact copying, correct physical free classes, and zero live allocations.
The production representation and allocator are exercised through bookkeeping
wrappers. Another 77 injected allocation failures emulate the device's sticky
error state on the host and verify that failed payload/count/descriptor
allocations cannot overwrite runtime control words. This is fault injection,
not physical GPU memory exhaustion. LeakSanitizer is disabled because the runtime retains
its process-lifetime Corpus mapping; the explicit allocation tracker checks
all string allocations. No full performance benchmark claim is made here.

`bench_words.bend` is a small pure oracle. Its checksum visits every code point
of every token; an independent Python oracle in `bench.sh` checks the large
results. The harness creates `/tmp/bench-base` at `master` if it is absent,
then uses that compiler and this checkout on identical generated drivers.
The baseline receives only the missing `words`/`copy` reference definitions
and their helpers, loaded as Base definitions; its existing APIs are unchanged.
Neither compiler uses `~/.bend`.

The benchmark uses one C worker, GPU off, identical Clang flags, one warm
process, and seven fresh measured processes per row. Each process is measured
with `/usr/bin/time -v`; native clock markers separate file IO/decode or
runtime construction from processing. A separate instrumented C build records
allocation counts, live/peak requested Corpus bytes, and payload cells copied
by `str_copy_cells`. Those counters exclude allocator reserves, IO mallocs,
and instrumentation overhead from the primary timing runs.

Inputs are exactly 1/8/64 MiB. They repeat the specified ASCII unit or a
mixed Unicode unit; a final prefix (padded with ASCII spaces if it cuts a
UTF-8 scalar) fills the requested byte size. The consuming scan uses windows
of 256 complete units, then `lines`, `trim`, `words`, and checksums. The
materialized mode builds the whole token list before consuming it. The
44-byte legacy corpus is also measured at 1024/4096 repetitions. Its new
checksum workload is not a rerun of the historical saved binary.

By default JS runs through 8 MiB; larger JS cases are explicitly unmeasured.
Baseline stack overflows are recorded failures, never a timing speedup.
Retention compares a three-character view with `copy`; requested live bytes
show release even when the allocator retains resident pages. Adversarial
search doubles text and needle lengths together.
Separate construction rows cover concat, join, repeat, unique append, and
retained snapshots at two scales; Map rows build and query 64 keys sharing
256- or 4096-character prefixes.

Artifacts include sources, binary hashes, provenance, all stdout/stderr,
verbose time reports, allocation snapshots, `raw.jsonl`, and `table.md`.
Set `BENCH_OUT` to keep them at a chosen path, `BENCH_BASE` for another
baseline checkout, `BENCH_FILTER` for a case-name regex, `BENCH_SIZES` for
comma-separated MiB sizes, `BENCH_JS_MAX_MIB` for the JS limit, or
`BENCH_TIMEOUT` for the per-process timeout (120 seconds by default).
The harness exits unsuccessfully if any candidate result fails its oracle.
See `SLICE5-NOTES.md` at the repository root for the measured acceptance run.
