# String lanes

Run from the repository root:

```sh
bash tests/run.sh --strings  # or bash tests/strings/run.sh
python3 tests/strings/runtime.py
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
wrappers. Another 34 injected allocation failures emulate the device's sticky
error state on the host and verify that failed payload/count/descriptor
allocations cannot overwrite runtime control words. This is fault injection,
not physical GPU memory exhaustion. LeakSanitizer is disabled because the runtime retains
its process-lifetime Corpus mapping; the explicit allocation tracker checks
all string allocations. No full performance benchmark claim is made here.
