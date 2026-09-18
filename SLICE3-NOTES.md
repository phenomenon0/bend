# Slice 3 — string natives and shared KMP

Built on `strings` from `6020861`, 2026-09-17 (America/Chicago).
Implementation: `b1cdce4`. Tests: `7b7f826`. No push.

## Implemented

- All 23 requested operations have C and JS native rows. Slice 2 already
  supplied take_end/drop_end/get_end, slice/cut/copy, concat/join/repeat,
  and words; this slice supplies the remaining 13. `clone` remains its
  ordinary checked definition. No reference semantics changed.
- C host and device share one forward KMP cursor for find/find_last,
  contains/count, replace, split_on, and partition. Each call builds at most
  one packed U32 prefix table. Empty and one-cell needles, and needles longer
  than the input, bypass the table. Last-match search retains the last start
  while allowing overlap; count/replace/split consume nonoverlapping matches.
- Search tables are private Corpus allocations. Every returning path closes
  the cursor. On a sticky device error, scratch goes directly back to the
  owning lane's free list because normal `heap_free` deliberately stops on
  error. The error flag is preserved; no host pointer enters device code.
- Replacement reads only original input and grows one destination. It never
  searches inserted text. Substring split and splitlines emit forward lists
  of views, with sealed fields before publication. Partition's nested tuple
  follows the same ownership protocol; native aggregate rows inform compiler
  field/borrow analysis. Capitalize and padding use Slice 2's descriptor and
  payload uniqueness checks. Hash is FNV-1a over four LE bytes per U32 cell.
- JS uses native bulk operations where scalar-string semantics agree with
  UTF-16 search. Only a returned search position is converted to code points.
  Padding counts code points, replacements are literal (including `$&`),
  capitalization is ASCII-only, and splitlines uses the specified boundaries.
  Raw padding cells are preserved on C/interpret and explicitly rejected by
  JS when they would construct a raw string; an unused raw fill is accepted.
- concat/join/repeat retain one destination. Runtime allocation bounds verify
  linear payload growth independently of retained-snapshot semantics.

Contract detail: the committed reference definition, Slice 1 fixture, and
`plan-astra-v2.md` specify `find_last(s, "") = length(s)`. This was preserved;
`find(s, "") = 0`, `count(s, "") = length(s)+1`, `split_on(s, "") = [s]`, and
`partition(s, "") = (s, "", "")`. The user's “empty needle at 0” shorthand was
flagged during implementation rather than silently changing the last-match law.

## Verification

| Gate | Result |
| --- | --- |
| Whole Base | All terms check |
| Strings check | 18/18 |
| Strings interpret/CLI | 18/18 |
| Strings JS | 18/18, including pinned raw-string rejection |
| Strings C host | 18/18 |
| Strings CUDA | 1/1, expanded native and shared-view fixture |
| `bash tests/run.sh --strings` | 73/73 |
| `bash tests/run.sh` | 16/16 |
| `bash tests/codex/run.sh` | 161/161, zero suite errors |
| `python3 tests/strings/runtime.py` | ASan/UBSan pass; 230,324 allocations, zero live |
| Device-style allocation failure injection | 77 passing cases |
| `git diff --check` | Pass |

Every `#|` was measured against the reference execution and compared on each
applicable lane. `io_utf8.bend` is an IO main, so its CLI lane executes JS;
the other 17 specimens use pure normalization. `deep.bend` still completes
its 180,224-character workload on interpret, JS, and C.

Added `replace.bend`, `split.bend`, and `padding.bend`; strengthened search,
concat snapshots, GPU calls, hash construction equivalence, and raw strings.
The expanded GPU fixture exercises substring search, replacement, partition,
split_on/splitlines, padding, capitalization, and hash across shared `!` tasks.

Additional probes:

- 4,437 C cases against an independent naive search/replacement/split/partition
  oracle, including NUL, supplementary scalars, surrogate cells, and U32 max.
  Retained inputs remain unchanged; nonempty split fields share source payloads.
- Adversarial `a...ab` with text/needle lengths 131,072/8,192 and
  262,144/16,384: **548,856 / 1,097,720 cell reads**. Both satisfy the linear
  operation bound; doubling input doubles reads. Exactly one table per call,
  and no table for bypass cases, are instrumented assertions.
- concat/join of 8,192 fields meet linear payload-allocation bounds; repeat
  allocates one appropriately sized payload. These are structural measurements,
  not the deferred end-to-end benchmark target.
- 1,799 JS cases agree with Python scalar-string oracles; a 262,144-cell
  repeated-prefix case also passes. 517 UTF-8 vectors still agree across C/JS.
- Allocation failures cover table allocation, replacement growth, view/list and
  tuple construction, and padding. They assert zero live search tables and
  unchanged protected runtime control words. This simulates sticky device
  errors on the host; it is not physical GPU exhaustion testing. Successful
  operations have full allocation/free-class accounting and zero live blocks.
- Oversized padding/repetition return the pinned length diagnostic on C and JS.

## Token ledger

Measured with `ttok` (default tokenizer); caps unchanged.

| File | Before | After | Delta |
| --- | ---: | ---: | ---: |
| `bend2/base.bend` | 27,844 | 27,844 | 0 |
| `bend2/comp.ts` | 69,918 | 74,220 | +4,302 |
| `bend2/bend.ts` | 40,399 | 40,399 | 0 |
| `bend2/main.ts` | 5,292 | 5,292 | 0 |

Changed/new `.bend` specimens: concat 545, gpu 726, hash 188,
padding 439, raw_strings 365, replace 320, search 538, split 630 tokens.
All string specimens remain below 800 tokens.

## Regressions and leftovers

No observed regression and no requested Slice 3 implementation deferred.
No piece hit the 15-minute fallback threshold. `bend.ts`, `main.ts`, Base
reference definitions, and `~/.bend` were untouched. Work is committed locally
on `strings`; nothing was pushed.

Metal execution remains unavailable on this Linux host. Map.bit, remaining
IO/numeric-text work, full 1/8/64 MiB benchmark acceptance, and physical device
exhaustion remain their planned later-slice gates. No full benchmark speedup
or memory target is claimed from the structural probes above.
