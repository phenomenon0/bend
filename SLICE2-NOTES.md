# Slice 2 — packed strings and fast natives

Built on `strings` from `fb838f2`, 2026-09-17 (America/Chicago).

## Implemented

- `TAG_STR=7`: class-1 two-word descriptors `{data, off<<32|len}` over
  Corpus-relative, reference-counted packed U32 payloads. Empty results are
  `CID_SNIL`. Static images include the entire declared payload capacity.
- Closed literal/manual chains are collected before recursive lowering and
  emitted as one static payload plus descriptor. Open `SCon` uses geometric
  prepend growth and reuses unique headroom. Logical `CID_SCON` matching routes
  field extraction through a consuming string helper. Strings remain boxed.
- Taking metadata uses `ctr_take(..., 1, ...)`: move from a unique descriptor;
  retain its one payload field before dropping a shared descriptor. Writes
  additionally require a dynamic underlying payload location and count one.
  Counts are installed before publication; static wrappers do not confer
  writability. Drop visits one field and frees the descriptor in class 1.
- Existing operations have C/JS adapters: length, emptiness, get, take/drop,
  append, reverse, comparator/relations, prefix/suffix, split/lines, ASCII
  trim/case, and list conversions. `cmp` returns the original two handles
  alongside a flattened comparison word; Maybe results use boxed adapters.
- End windows, slice, cut, copy, concat/join/repeat, and words also have bulk
  natives because the Slice 2 acceptance specimens exercise those paths.
  These are already done for the next slice; clone keeps its checked aliasing
  definition. The rest of the new substring APIs remain reference definitions.
- Native list builders propagate their sealed-field status into compiler hot
  type analysis. String extraction marks an owned root through the fixed-point
  borrow analysis, including polymorphic containers. Generic lists, arrays,
  partial applications, and shared `!` transfers are covered by specimens.
- JS strings use scalar code-point helpers and bulk operations. Raw U32 Char
  values use tagged Char dispatch; string construction rejects them with the
  exact diagnostic in `raw_strings.js-error`. ASCII case and whitespace scope
  is preserved.
- C IO decodes UTF-8 forward into a capacity-sized payload, then shrinks the
  logical length. C/JS replace each ill-formed byte separately and retain BOM.
  C output returns a separately owned, NUL-terminated buffer with explicit
  length; NUL remains an ordinary element. Raw UTF-8 output is rejected.
- Reference split/words use accumulators. Repeating an empty string exits
  immediately even for an oversized Nat. Char case bodies remain unchanged.

## Verification

| Gate | Result |
| --- | --- |
| Whole Base | All terms check |
| Strings check | 15/15 |
| Strings interpret/CLI | 15/15 |
| Strings JS | 15/15, including the pinned raw-string rejection |
| Strings C host | 15/15 |
| Strings CUDA | 1/1 (`gpu.bend`, actual device execution) |
| `bash tests/run.sh` | 16/16, including f64 CUDA |
| `bash tests/codex/run.sh` | 161/161, zero suite errors |
| `python3 tests/strings/runtime.py` | ASan/UBSan pass; 53,362 tracked allocations, zero live |
| Allocation failure injection | 34 cases; sticky device-style error state simulated on host |
| UTF-8 oracle | C and JS agree with independent strict-prefix oracle on 517 byte vectors |
| `git diff --check` | Pass |

The string suite is available as `bash tests/run.sh --strings` or
`bash tests/strings/run.sh`; its full matrix has **61 passing results**. Every
`#|` block was measured. `io_utf8.bend` is an IO main, so its CLI lane uses JS;
the other 14 specimens, including `deep.bend`, use pure normalization.

`deep.bend` processes 44 × 4096 = **180,224 characters** through length,
split, words, and uppercase comparison. A measured run completed in 131.53 s
on interpret (3,309,632 KiB peak RSS), about 0.05 s on emitted JS, and below
0.01 s on emitted C. These are single process runs, including startup, not
the Slice 5 benchmark protocol. The result is four checked booleans rather
than a huge unary result; expected counts use arithmetic expressions because
a literal `180224n` exceeds the existing syntax-walk stack. Each scan builds
its own source instead of keeping a shared normalizer graph alive across all
four tuple fields. No checker or `bend.ts` changes were made.

The ownership probe verifies shared-descriptor detachment when payload count
is still one, static-origin checks through wrappers, overlapping views, unique
payload reuse, geometric growth, shared split payloads, empty-window release,
and actual slab release when a tiny retained view is copied. It checks
allocation/free classes in addition to ASan/UBSan, because sanitizer shadow
memory alone cannot see frees within the custom Corpus allocator.

Machine: NVIDIA GeForce RTX 3090, clang 21.1.7, Bun 1.3.4, Linux. CUDA builds
and runs are measured. Metal was not available on this host.

Token measurements (`ttok`, no cap changes):

| File | Tokens |
| --- | ---: |
| `bend2/base.bend` | 27,844 |
| `bend2/comp.ts` | 69,918 |

## Boundaries and leftovers

No requested Slice 2 implementation piece was deferred. No regression was
observed in the required suites. `bend.ts`, `main.ts`, and `~/.bend` were left
untouched; nothing was pushed.

Remaining planned work is outside this slice: KMP/other new substring natives,
`Map.bit`, the paired numerical-text corrections, full benchmark/retention
instrumentation at 1/8/64 MiB, physical device exhaustion tests, and Metal
hardware validation. General checker stack safety and string-level raw JS support remain
explicit non-goals in the locked plan. JS substring storage retention remains
engine-dependent; `copy` only promises compact private storage on the C lane.
