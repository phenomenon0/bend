# Slice 5 — benchmarks, structural acceptance, and landing caps

Built on `strings` from `335f3405d15d3eb51f698526f612c01fe96eaa37`, on 2026-09-17 (America/Chicago). Frozen cons baseline: `master` at `309bbf62fd83e0c2f81eb5d176c11bca09b49686`, created with `git worktree add /tmp/bench-base master`. No push; no access to `~/.bend`.

**The processing target is not fully met.** The file-decoded consuming scans miss the 2× processing target. The C memory target passes. Construction and IO rows are kept separate because their baseline ownership costs differ. Every candidate benchmark result matches its independent content oracle. No compiler, Base, parser, or CLI implementation changed in this slice.

## Protocol and provenance

Final acceptance command:

```sh
BENCH_OUT=/tmp/bend-strings-slice5-acceptance bash tests/strings/bench.sh
```

The harness emits identical Bend drivers with both frozen compilers, and Clang builds each primary executable once. Each C and JS row has one untimed warm process followed by seven fresh measured processes. The cache is warm; JS JIT state starts fresh per process. The C lane uses `--gpu off --threads 1`; Clang uses `-std=c11 -O3 -g -fno-omit-frame-pointer -lpthread -lm`. Wall times include process startup and the GNU time/timeout wrappers. Native monotonic markers separate IO plus UTF-8 decode, or construction, from processing. Each run also has `/usr/bin/time -v` peak RSS. The desktop remained active; CPU affinity, frequency, and system caches were not forced. Ranges expose run variation.

Both large corpora are exactly 1/8/64 MiB of UTF-8 input. ASCII repeats `"  alpha beta\n gamma\t\n"`; Unicode repeats `"  café λ😀\n 漢字\t\n"`. A scalar-safe final prefix, padded with ASCII spaces if necessary, fills the requested byte size. Construction performs repeat plus that same suffix. The consuming path uses windows of 256 complete corpus units, then lines, trim, words, and a checksum which reads every token code point (`h = 33*h + codepoint`, U32 wrap; sum token hashes and count tokens). The final window may be partial. The materialized path retains all tokens before consuming them. The small pure oracle additionally checks interpretation; its main is pure.

Baseline lacks `String.words` and `String.copy`. Only their candidate reference definitions and the new words helpers are loaded into its Base namespace, with the same Base-definition treatment as the standard library. No existing baseline definition, native, runtime, or compiler is replaced. The same workload calls the same API names on both lanes. Driver, input, source, and binary hashes are recorded below.

JS runs through 8 MiB, including full-input failures on the baseline. 64 MiB JS is explicitly **not run**. A failure has a measured failure wall/RSS but no successful processing median or speedup. The legacy rows use the specified 44-byte corpus at 1024/4096 repetitions with this content-checking workload; they do not reuse or compare against the historical saved binary timing.

A separate instrumented C executable counts `heap_alloc`/`heap_free` requested Corpus bytes, allocations, frees, and interval peak live bytes. It does not measure allocator reserves, runtime stacks/control tables, or IO malloc buffers; RSS does. Counters are excluded from primary timings. `copy_cells` counts candidate `str_copy_cells` only; baseline has no such counter and reports null. Zero copies is asserted separately for contiguous split/trim/windows. Each marker resets the interval peak after recording it. The small live remainder at the final marker is the result/IO continuation, not a leak claim; the independent sanitizer probe verifies zero live allocations.

## Consuming scans — C comparison

All times below are medians of seven valid runs. The formal target applies to 8/64 MiB; 1 MiB is shown for scale. Full ranges and every sample are below. RSS is median process peak in KiB. Runtime peak is a single separate instrumented run, in bytes.

| Corpus / MiB / source | Process ms base → candidate | Speedup | RSS KiB base → candidate | RSS reduction | Runtime peak bytes base → candidate | Processing ≥2× | Memory ≥2× (RSS/runtime) |
|---|---:|---:|---:|---:|---:|---|---|
| ascii / 1 / io | 17.003 → 13.807 | 1.23× | 19,632 → 7,288 | 2.69× | 16,863,232 → 4,231,232 | MISS | PASS |
| ascii / 1 / construct | 33.666 → 13.466 | 2.50× | 43,256 → 6,248 | 6.92× | 25,294,744 → 4,231,232 | PASS | PASS |
| ascii / 8 / io | 134.152 → 103.987 | 1.29× | 141,284 → 43,112 | 3.28× | 134,303,744 → 33,591,360 | MISS | PASS |
| ascii / 8 / construct | 271.338 → 111.160 | 2.44× | 329,904 → 34,916 | 9.45× | 201,455,344 → 33,591,360 | PASS | PASS |
| ascii / 64 / io | 1094.442 → 875.736 | 1.25× | 1,115,832 → 329,784 | 3.38× | 1,073,827,840 → 268,472,384 | MISS | PASS |
| ascii / 64 / construct | 2153.915 → 838.084 | 2.57× | 2,622,840 → 264,312 | 9.92× | 1,610,741,656 → 268,472,384 | PASS | PASS |
| unicode / 1 / io | 10.445 → 9.626 | 1.09× | 13,492 → 5,752 | 2.35× | 10,547,216 → 4,231,232 | MISS | PASS |
| unicode / 1 / construct | 19.613 → 9.766 | 2.01× | 27,896 → 4,844 | 5.76× | 15,820,552 → 4,231,232 | PASS | PASS |
| unicode / 8 / io | 86.437 → 73.566 | 1.17× | 92,268 → 30,772 | 3.00× | 83,947,552 → 33,591,360 | MISS | PASS |
| unicode / 8 / construct | 151.441 → 72.360 | 2.09× | 207,016 → 22,608 | 9.16× | 125,921,152 → 33,591,360 | PASS | PASS |
| unicode / 64 / io | 655.862 → 603.976 | 1.09× | 722,792 → 231,336 | 3.12× | 671,150,096 → 268,472,384 | MISS | PASS |
| unicode / 64 / construct | 1280.261 → 626.300 | 2.04× | 1,640,052 → 165,996 | 9.88× | 1,006,724,872 → 268,472,384 | PASS | PASS |

## JS bounded scans — decode and RSS regressions

Candidate JS processing is faster on these completed file scans, but IO/decode is substantially slower. At 8 MiB peak RSS is higher; at 1 MiB it is lower. The C memory result must not be generalized to JS. Source inspection finds the candidate decoder building an array of per-code-point strings before joining it; baseline uses TextDecoder. The candidate decoder preserves the required malformed-byte and BOM semantics, so an optimization must preserve that contract. This is a named follow-up, not a silent pass of a memory target.

| Corpus / MiB | Acquire ms base → candidate | Process ms base → candidate | Peak RSS KiB base → candidate |
|---|---:|---:|---:|
| ascii / 1 | 10.990 → 51.976 | 889.938 → 131.569 | 187,216 → 137,924 |
| ascii / 8 | 17.275 → 332.862 | 7329.375 → 895.710 | 236,472 → 418,812 |
| unicode / 1 | 11.407 → 58.499 | 616.873 → 94.793 | 163,008 → 141,116 |
| unicode / 8 | 20.555 → 424.715 | 5433.779 → 608.619 | 289,780 → 534,844 |

## Allocation and materialized-list costs

Processing allocation counts are phase 3 minus phase 1. All counts come from separate instrumented executions. Keeping all tokens changes the workload memory peak; it is not conflated with the bounded scan.

| Workload | Allocations during processing base → candidate | Peak requested bytes base → candidate | Candidate live bytes with token list retained (phase 2) |
|---|---:|---:|---:|
| legacy-1024 | 246,797 → 113,676 | 1,081,392 → 704,568 | 704,536 |
| legacy-4096 | 987,149 → 454,668 | 4,325,424 → 2,818,104 | 2,818,072 |
| ascii-1MiB-io-scan | 2,496,813 → 2,497,399 | 16,863,232 → 4,231,232 | — |
| ascii-1MiB-construct-scan | 6,840,712 → 2,497,399 | 25,294,744 → 4,231,232 | — |
| ascii-1MiB-io-materialize | 1,448,048 → 2,496,623 | 16,777,288 → 11,384,616 | 11,384,584 |
| ascii-8MiB-io-scan | 19,974,444 → 19,979,125 | 134,303,744 → 33,591,360 | — |
| ascii-8MiB-construct-scan | 54,725,691 → 19,979,125 | 201,455,344 → 33,591,360 | — |
| ascii-8MiB-io-materialize | 11,584,282 → 19,972,889 | 134,217,800 → 91,076,392 | 91,076,360 |
| ascii-64MiB-io-scan | 159,795,501 → 159,832,951 | 1,073,827,840 → 268,472,384 | — |
| ascii-64MiB-construct-scan | 437,805,448 → 159,832,951 | 1,610,741,656 → 268,472,384 | — |
| ascii-64MiB-io-materialize | 92,674,160 → 159,783,023 | 1,073,741,896 → 728,610,600 | 728,610,568 |
| unicode-1MiB-io-scan | 1,660,425 → 1,660,935 | 10,547,216 → 4,231,232 | — |
| unicode-1MiB-construct-scan | 3,888,483 → 1,660,935 | 15,820,552 → 4,231,232 | — |
| unicode-1MiB-io-materialize | 1,004,900 → 1,660,259 | 10,485,848 → 10,485,824 | 10,485,784 |
| unicode-8MiB-io-scan | 13,283,339 → 13,287,433 | 83,947,552 → 33,591,360 | — |
| unicode-8MiB-construct-scan | 31,107,774 → 13,287,433 | 125,921,152 → 33,591,360 | — |
| unicode-8MiB-io-materialize | 8,039,098 → 13,281,977 | 83,886,184 → 83,886,136 | 83,886,104 |
| unicode-64MiB-io-scan | 106,266,633 → 106,299,399 | 671,150,096 → 268,472,384 | — |
| unicode-64MiB-construct-scan | 248,862,051 → 106,299,399 | 1,006,724,872 → 268,472,384 | — |
| unicode-64MiB-io-materialize | 64,312,676 → 106,255,715 | 671,088,728 → 671,088,704 | 671,088,664 |

Materialization and subsequent checksum consumption are separately timed at marker 2:

| Materialized workload | Build token list ms base → candidate | Consume token contents ms base → candidate |
|---|---:|---:|
| legacy-1024 | 1.403 → 0.389 | 0.152 → 0.266 |
| legacy-4096 | 5.442 → 1.629 | 1.048 → 1.044 |
| ascii-1MiB-io-materialize | 19.399 → 10.747 | 1.092 → 5.266 |
| ascii-8MiB-io-materialize | 145.917 → 81.085 | 8.209 → 41.308 |
| ascii-64MiB-io-materialize | 1177.890 → 647.771 | 69.542 → 337.823 |
| unicode-1MiB-io-materialize | 11.461 → 8.263 | 0.568 → 2.795 |
| unicode-8MiB-io-materialize | 91.340 → 65.924 | 4.827 → 21.551 |
| unicode-64MiB-io-materialize | 748.878 → 547.077 | 40.195 → 171.566 |

At 64 MiB, materialized ASCII token consumption alone regresses from 69.542 to 337.823 ms; materialized Unicode consumption regresses from 40.195 to 171.566 ms. This custom SCon checksum exposes descriptor churn even while native splitting improves. Fully materializing the Unicode tokens also removes the requested-heap advantage (671,088,728 versus 671,088,704 bytes). These results are kept separate from the consuming-scan target; no 2× materialized-list memory claim is made.


## Retention and adversarial search

`retained` keeps the three-character value alive across marker 2 and then reads its actual contents. `copy` can release the original payload while the allocator retains resident pages; peak RSS is therefore not a retained-owner metric. Marker 2 includes the IO continuation as well as the string.

| Probe | Baseline live bytes at marker 2 | Candidate live bytes at marker 2 | Candidate payload cells copied |
|---|---:|---:|---:|
| retain-8MiB-view | 72 | 33,554,488 | 0 |
| retain-8MiB-copy | 72 | 72 | 3 |

| Adversarial text / needle chars | C processing ms base → candidate | JS baseline | JS candidate processing ms |
|---|---:|---|---:|
| 32,768 / 512 | 107.022 → 0.107 | exit 1 | 0.170 |
| 65,536 / 1,024 | 422.550 → 0.212 | exit 1 | 0.286 |
| 131,072 / 2,048 | 1670.125 → 0.426 | exit 1 | 0.467 |

The search text and needle both end in `b` after long runs of `a`; the result is checked. The structural probe independently verifies the KMP read bound, rather than inferring asymptotics solely from wall time. Builder and Map timings are included in the complete table: concat/join/repeat, unique append, retained snapshots, and 64 keys with 256/4096-character shared prefixes.

## Profile after the target miss

Profiling used the same ASCII 64 MiB file-consuming workload and frozen compiler outputs, with `-pg` added for a separate diagnostic build. Seven complete executions per compiler produced matching checksums. GNU gprof sampled at 0.01-second granularity; its perturbed timings are not used for speedup claims. The final primary and profiled-source workloads are checked for equivalent preprocessed C below.

The candidate profile attributes 29.75% of sampled whole-process CPU to `WL_FID_WORDS_SCAN_K13` (the continuation that calls the token checksum loop), 21.63% to `str_split_take`, 16.56% to `io_str`, and 13.50% to `rfc_wrap`. There are 536,958,520 `rfc_wrap` calls across the seven profiled candidate runs. The generated checksum loop invokes `str_uncons` for each code point; source inspection and the allocation counters explain why packed storage does not automatically make this custom character walk twice as fast. These observations point to descriptor/reference-count churn and list processing as optimization candidates. They do not prove that an adaptive-width representation would fix the time target.

No UTF-8/adaptive-width experiment or compiler optimization was made. The miss now justifies that experiment as a follow-up, alongside descriptor reuse and bulk character consumption; any improvement still needs the same workload and protocol. The custom checksum was kept unchanged after the miss.

Profile reproduction (run from the artifact directory; repeat execution seven times with distinct output prefixes):

```sh
clang -std=c11 -O3 -g -fno-omit-frame-pointer -pg ascii-64MiB-io-scan.candidate.c -lpthread -lm -o profile-candidate
GMON_OUT_PREFIX="$PWD/gmon-candidate" ./profile-candidate --gpu off --threads 1
gprof -b -p profile-candidate gmon-candidate.*
gprof -b -p -l profile-candidate gmon-candidate.*
```

## Frozen-tree gates and caps

Full battery: **strings 85/85**, **f64 16/16**, **codex 161/161** (zero suite errors), whole Base, and all caps pass. String and f64 CUDA fixtures ran on the RTX 3090.

Measured with `ttok 0.3`, using its default tokenizer, via `ttok < file`:

| File | Exact tokens | Landing cap |
|---|---:|---:|
| `bend2/base.bend` | 27,844 | 28,000 |
| `bend2/comp.ts` | 74,981 | 75,000 |
| `bend2/bend.ts` | 40,399 | 41,000 |
| `bend2/main.ts` | 5,292 | 10,000 |
| `tests/strings/bench_words.bend` | 484 | 1,200 |

| Structural gate | Fresh measured result |
|---|---|
| No per-character source cells | Four allocations at 1,048,576 / 8,388,608 / 67,108,864 cells |
| O(1) C length/get/slice | One cell read and three allocations total at each of those sizes |
| Contiguous split/trim share payloads | Pointer identity asserted; zero payload copies and zero new payload allocations |
| Bounded consuming descriptors | Native probe peaks at 2,059 live blocks at all three sizes; all blocks counted, including descriptors |
| Compiled consuming workload | Peak requested heap is payload capacity + 36,928 bytes at 1/8/64 MiB on both corpora |
| Ownership and sanitizers | ASan/UBSan; 80,492,647 allocations, zero live; 77 injected failures |
| Unique growth and bulk builders | Linear payload-allocation bounds pass for prepend/append/concat/join/repeat |
| General search scaling | 548,856 / 1,097,720 cell reads when text and needle double; linear bound passes |

<details>
<summary>strings: measured verification output</summary>

```text
ok   adt            [check]
ok   adt            [interpret]
ok   adt            [js]
ok   adt            [c]
ok   ascii          [check]
ok   ascii          [interpret]
ok   ascii          [js]
ok   ascii          [c]
ok   bench_words    [check]
ok   bench_words    [interpret]
ok   bench_words    [js]
ok   bench_words    [c]
ok   compare        [check]
ok   compare        [interpret]
ok   compare        [js]
ok   compare        [c]
ok   concat         [check]
ok   concat         [interpret]
ok   concat         [js]
ok   concat         [c]
ok   deep           [check]
ok   deep           [interpret]
ok   deep           [js]
ok   deep           [c]
ok   gpu            [check]
ok   gpu            [interpret]
ok   gpu            [js]
ok   gpu            [c]
ok   gpu            [gpu]
ok   hash           [check]
ok   hash           [interpret]
ok   hash           [js]
ok   hash           [c]
ok   indices        [check]
ok   indices        [interpret]
ok   indices        [js]
ok   indices        [c]
ok   io_utf8        [check]
ok   io_utf8        [interpret]
ok   io_utf8        [js]
ok   io_utf8        [c]
ok   laws           [check]
ok   laws           [interpret]
ok   laws           [js]
ok   laws           [c]
ok   map_keys       [check]
ok   map_keys       [interpret]
ok   map_keys       [js]
ok   map_keys       [c]
ok   numeric_text   [check]
ok   numeric_text   [interpret]
ok   numeric_text   [js]
ok   numeric_text   [c]
ok   padding        [check]
ok   padding        [interpret]
ok   padding        [js]
ok   padding        [c]
ok   raw_chars      [check]
ok   raw_chars      [interpret]
ok   raw_chars      [js]
ok   raw_chars      [c]
ok   raw_strings    [check]
ok   raw_strings    [interpret]
ok   raw_strings    [js: expected rejection]
ok   raw_strings    [c]
ok   replace        [check]
ok   replace        [interpret]
ok   replace        [js]
ok   replace        [c]
ok   search         [check]
ok   search         [interpret]
ok   search         [js]
ok   search         [c]
ok   sharing        [check]
ok   sharing        [interpret]
ok   sharing        [js]
ok   sharing        [c]
ok   split          [check]
ok   split          [interpret]
ok   split          [js]
ok   split          [c]
ok   unicode        [check]
ok   unicode        [interpret]
ok   unicode        [js]
ok   unicode        [c]

Strings PASS: 85, FAIL: 0
```

</details>

<details>
<summary>f64: measured verification output</summary>

```text
ok   convert                [interpret]
ok   convert                [js]
ok   convert                [c]
ok   mc_pi                  [interpret]
ok   mc_pi                  [js]
ok   mc_pi                  [c]
ok   mc_pi                  [gpu]
ok   read_roundtrip         [interpret]
ok   read_roundtrip         [js]
ok   read_roundtrip         [c]
ok   show_decimals          [interpret]
ok   show_decimals          [js]
ok   show_decimals          [c]
ok   show_specials          [interpret]
ok   show_specials          [js]
ok   show_specials          [c]

PASS: 16, FAIL: 0
```

</details>

<details>
<summary>codex: measured verification output</summary>

```text
PASS round_sum
PASS round_third
PASS round_pow_half
PASS round_large_swallow
PASS round_large_cancel
PASS round_large_next
PASS round_tie_even_down
PASS round_tie_even_up
PASS round_subnormal
PASS round_subnormal_double
PASS round_subnormal_half
PASS round_subnormal_tie
PASS round_subnormal_div
PASS round_subnormal_neg_div
PASS round_min_normal
PASS round_below_normal
PASS round_recover_normal
PASS round_integer_literal
PASS round_decimal_exponent
PASS round_integer_exponent
PASS round_max_finite
PASS round_max_overflow
PASS round_above_f32_integer
PASS round_last_exact_integer
PASS round_integer_tie
PASS special_zero
PASS special_neg_zero
PASS special_zero_equal
PASS special_zero_not_less
PASS special_double_neg_zero
PASS special_abs_neg_zero
PASS special_reciprocal_zero
PASS special_reciprocal_neg_zero
PASS special_overflow
PASS special_neg_overflow
PASS special_inf_add
PASS special_inf_opposite
PASS special_inf_sub
PASS special_inf_zero_mul
PASS special_inf_div
PASS special_finite_div_inf
PASS special_negative_div_inf
PASS special_nan
PASS special_nan_add
PASS special_nan_mul
PASS special_nan_div
PASS special_sqrt_negative
PASS special_nan_eq
PASS special_nan_ne
PASS special_nan_lt
PASS special_nan_le
PASS special_nan_gt
PASS special_nan_ge
PASS special_inf_eq
PASS special_inf_gt
PASS special_neg_inf_lt
PASS special_mod_zero
PASS special_mod_neg_zero
PASS conv_u32_zero
PASS conv_u32_max
PASS conv_u32_above_f32
PASS conv_truncate
PASS conv_fraction
PASS conv_negative
PASS conv_u32_last_fraction
PASS conv_u32_limit
PASS conv_u32_above_limit
PASS conv_u32_inf
PASS conv_u32_neg_inf
PASS conv_u32_nan
PASS conv_widen_tenth
PASS conv_widen_sum
PASS conv_narrow_tenth
PASS conv_narrow_tie
PASS conv_narrow_above_tie
PASS conv_narrow_overflow
PASS conv_narrow_underflow
PASS conv_narrow_neg_zero
PASS conv_from_nat
PASS conv_from_nat_zero
PASS conv_to_nat
PASS conv_bits_zero
PASS conv_bits_subnormal
PASS conv_bits_next_subnormal
PASS math_neg
PASS math_abs
PASS math_mod
PASS math_mod_negative
PASS math_mod_negative_divisor
PASS math_pow_negative
PASS math_sqrt
PASS math_atan2_scaled
PASS math_exp_scaled
PASS math_log_scaled
PASS math_log2_scaled
PASS math_log10_scaled
PASS math_sin_scaled
PASS math_cos_scaled
PASS math_tan_scaled
PASS math_asin_scaled
PASS math_acos_scaled
PASS math_atan_scaled
PASS math_sinh_scaled
PASS math_cosh_scaled
PASS math_tanh_scaled
PASS math_floor_negative
PASS math_ceil_negative
PASS math_trunc_negative
PASS math_floor_positive
PASS math_ceil_positive
PASS math_trunc_neg_fraction
PASS math_pi
PASS math_eq
PASS math_ne
PASS math_lt
PASS math_le_equal
PASS math_gt
PASS math_ge_equal
PASS text_integer
PASS text_small_fixed
PASS text_small_scientific
PASS text_large_fixed
PASS text_large_scientific
PASS text_negative_fixed
PASS text_negative_scientific
PASS read_decimal
PASS read_integer
PASS read_exponent
PASS read_integer_exponent
PASS read_subnormal
PASS read_max_finite
PASS read_neg_zero
PASS read_neg_zero_decimal
PASS read_inf
PASS read_neg_inf
PASS read_nan
PASS read_overflow
PASS read_underflow
PASS read_neg_underflow
PASS read_halfway_even
PASS read_above_halfway
PASS read_empty
PASS read_spaces_only
PASS read_junk
PASS read_trailing_junk
PASS read_incomplete_exp
PASS read_incomplete_sign
PASS read_literal_suffix
PASS read_embedded_nul
PASS read_hex
PASS read_underscore
PASS roundtrip_sum
PASS roundtrip_third
PASS roundtrip_subnormal
PASS roundtrip_neg_zero
PASS roundtrip_inf
PASS roundtrip_nan
PASS precision_f64
PASS precision_f32_widened
PASS precision_f64_digits
PASS precision_f32_digits

161 PASS, 0 FAIL; 0 suite errors
```

</details>

<details>
<summary>runtime: measured verification output</summary>

```text
KMP/replace/split/partition naive oracle: ok (4437 cases)
Adversarial a...ab: 548856 / 1097720 cell reads (2x input), linear bound passed
concat/join/repeat: linear payload allocation bounds passed
Structural 1048576 cells: source allocations=4; length/get/slice reads=1 allocations=3; scan peak live blocks=2059; payload copies=0
Structural 8388608 cells: source allocations=4; length/get/slice reads=1 allocations=3; scan peak live blocks=2059; payload copies=0
Structural 67108864 cells: source allocations=4; length/get/slice reads=1 allocations=3; scan peak live blocks=2059; payload copies=0
runtime ownership + UTF-8: ok (80492647 allocations, zero live)
Device-style allocation failures: ok (77 injected cases)
JS UTF-8: ok (517 byte vectors)
JS text Python oracle: ok (1799 cases + adversarial search)
C/JS string length diagnostics: ok
```

</details>

<details>
<summary>base: measured verification output</summary>

```text
All terms check.
```

</details>

<details>
<summary>caps: measured verification output</summary>

```text
ok   bend2/base.bend                27844 <= 28000
ok   bend2/bend.ts                  40399 <= 41000
ok   bend2/comp.ts                  74981 <= 75000
ok   bend2/main.ts                   5292 <= 10000
ok   tests/f64/convert.bend           250 <= 16000
ok   tests/f64/mc_pi.bend             478 <= 16000
ok   tests/f64/read_roundtrip.bend     239 <= 16000
ok   tests/f64/show_decimals.bend     246 <= 16000
ok   tests/f64/show_specials.bend     244 <= 16000
ok   tests/strings/adt.bend           385 <= 16000
ok   tests/strings/ascii.bend         246 <= 16000
ok   tests/strings/bench_words.bend     484 <= 1200
ok   tests/strings/compare.bend       281 <= 16000
ok   tests/strings/concat.bend        545 <= 16000
ok   tests/strings/deep.bend          242 <= 16000
ok   tests/strings/gpu.bend           726 <= 16000
ok   tests/strings/hash.bend          188 <= 16000
ok   tests/strings/indices.bend       537 <= 16000
ok   tests/strings/io_utf8.bend       282 <= 16000
ok   tests/strings/laws.bend          492 <= 16000
ok   tests/strings/map_keys.bend     1214 <= 16000
ok   tests/strings/numeric_text.bend     413 <= 16000
ok   tests/strings/padding.bend       439 <= 16000
ok   tests/strings/raw_chars.bend     210 <= 16000
ok   tests/strings/raw_strings.bend     521 <= 16000
ok   tests/strings/replace.bend       320 <= 16000
ok   tests/strings/search.bend        538 <= 16000
ok   tests/strings/sharing.bend       444 <= 16000
ok   tests/strings/split.bend         630 <= 16000
ok   tests/strings/unicode.bend       468 <= 16000
```

</details>

`tests/run.sh` already dispatches `--strings`, and the strings runner discovers the new oracle automatically; no runner change was needed. `tests/caps.sh` now includes every string specimen, the 1,200-token benchmark oracle cap, and the next-thousand Base/compiler caps. The upstream allow-list is absent from this fork.

`bend2/bend.ts` and `bend2/main.ts` are unchanged, as are `bend2/base.bend` and `bend2/comp.ts`. CUDA execution in the strings/f64 suites is actual device evidence. Metal is unavailable on this Linux host; host fault injection does not claim physical device exhaustion coverage.

## Commits and remaining work

`83e55c44f5d06021582cb8ddb447d47f74543377` — `test(strings): add reproducible benchmarks and structural acceptance gates`.

The acceptance ledger/caps are a second local commit. No push. The compiler sources and benchmark harness remained frozen during the final benchmark and subsequent battery; only this measurement ledger was written afterward.

- Open acceptance target: ≥2× processing on file-decoded 8/64 MiB consuming scans. C memory and structural gates pass.
- JS IO/decode latency and peak RSS regress on the measured valid corpora; optimize the decoder without weakening its byte/BOM contract.
- 64 MiB JS is unmeasured (the reproducible default limits JS to 8 MiB); baseline recursive-library overflows at smaller sizes are recorded results.
- Metal hardware and physical device exhaustion are outside the available hardware evidence.
- No requested benchmark workload or landing cap is left unimplemented. No storage experiment was performed.

## Complete comparison table

| Workload | Lane | Valid | Wall ms median [min,max] | Acquire ms | Process ms median [min,max] | Peak RSS KiB median [min,max] |
|---|---|---:|---:|---:|---:|---:|
| legacy-1024 | base/c | 7/7 | 4.499 [3.998,4.949] | 0.575 [0.556,0.768] | 1.597 [1.367,1.768] | 4324.000 [4216.000,4400.000] |
| legacy-1024 | base/js | FAIL 1 | 22.395 [20.678,26.006] | — | — | 52132.000 [51880.000,52392.000] |
| legacy-1024 | candidate/c | 7/7 | 2.683 [2.554,2.816] | 0.070 [0.062,0.074] | 0.665 [0.645,0.777] | 2788.000 [2680.000,2924.000] |
| legacy-1024 | candidate/js | 7/7 | 26.076 [24.575,28.715] | 0.388 [0.346,0.614] | 9.376 [8.241,10.423] | 62696.000 [62552.000,62816.000] |
| legacy-4096 | base/c | 7/7 | 11.776 [10.945,12.948] | 2.379 [2.259,2.787] | 6.386 [6.024,7.422] | 10608.000 [10488.000,10740.000] |
| legacy-4096 | base/js | FAIL 1 | 23.413 [21.048,26.010] | — | — | 52824.000 [52388.000,52964.000] |
| legacy-4096 | candidate/c | 7/7 | 5.088 [4.983,5.367] | 0.248 [0.240,0.252] | 2.667 [2.607,2.891] | 4712.000 [4600.000,4852.000] |
| legacy-4096 | candidate/js | 7/7 | 49.298 [46.319,50.704] | 0.386 [0.367,0.429] | 27.856 [26.848,28.920] | 90200.000 [89884.000,90464.000] |
| ascii-1MiB-io-scan | base/c | 7/7 | 28.397 [27.532,29.204] | 7.988 [7.698,8.616] | 17.003 [16.580,17.762] | 19632.000 [19428.000,19704.000] |
| ascii-1MiB-io-scan | base/js | 7/7 | 924.164 [911.849,936.993] | 10.990 [10.178,13.033] | 889.938 [877.286,900.492] | 187216.000 [185964.000,188824.000] |
| ascii-1MiB-io-scan | candidate/c | 7/7 | 19.787 [18.979,21.036] | 2.956 [2.705,3.656] | 13.807 [13.442,15.644] | 7288.000 [7216.000,7416.000] |
| ascii-1MiB-io-scan | candidate/js | 7/7 | 205.956 [197.502,207.012] | 51.976 [50.125,53.670] | 131.569 [125.125,134.841] | 137924.000 [136568.000,138192.000] |
| ascii-1MiB-construct-scan | base/c | 7/7 | 64.860 [62.913,66.737] | 26.588 [25.235,27.796] | 33.666 [33.119,35.182] | 43256.000 [43128.000,43380.000] |
| ascii-1MiB-construct-scan | base/js | FAIL 1 | 21.841 [20.464,23.245] | — | — | 51220.000 [51040.000,51740.000] |
| ascii-1MiB-construct-scan | candidate/c | 7/7 | 17.454 [17.333,19.772] | 1.680 [1.418,1.855] | 13.466 [13.143,15.460] | 6248.000 [6172.000,6380.000] |
| ascii-1MiB-construct-scan | candidate/js | 7/7 | 154.368 [145.782,158.238] | 0.217 [0.210,0.257] | 131.833 [124.621,136.845] | 99940.000 [99040.000,104972.000] |
| ascii-1MiB-io-materialize | base/c | 7/7 | 34.007 [32.408,35.393] | 8.131 [7.840,9.084] | 20.354 [19.413,22.122] | 43256.000 [43028.000,43364.000] |
| ascii-1MiB-io-materialize | base/js | FAIL 1 | 33.003 [30.718,34.768] | — | — | 57028.000 [56636.000,57252.000] |
| ascii-1MiB-io-materialize | candidate/c | 7/7 | 21.720 [20.789,23.330] | 2.730 [2.592,3.450] | 16.166 [15.244,17.407] | 13264.000 [13012.000,13476.000] |
| ascii-1MiB-io-materialize | candidate/js | 7/7 | 192.537 [184.436,196.676] | 51.524 [50.297,56.781] | 117.140 [112.325,120.776] | 178248.000 [177364.000,178508.000] |
| ascii-8MiB-io-scan | base/c | 7/7 | 207.802 [201.376,224.184] | 61.918 [60.158,68.559] | 134.152 [131.057,145.468] | 141284.000 [141172.000,141488.000] |
| ascii-8MiB-io-scan | base/js | 7/7 | 7374.618 [7247.949,7471.292] | 17.275 [15.810,18.854] | 7329.375 [7207.025,7427.358] | 236472.000 [226444.000,243156.000] |
| ascii-8MiB-io-scan | candidate/c | 7/7 | 133.563 [127.906,138.661] | 23.261 [21.433,25.283] | 103.987 [101.370,110.053] | 43112.000 [43056.000,43192.000] |
| ascii-8MiB-io-scan | candidate/js | 7/7 | 1271.769 [1223.148,1283.887] | 332.862 [311.339,349.845] | 895.710 [863.061,911.209] | 418812.000 [398792.000,446948.000] |
| ascii-8MiB-construct-scan | base/c | 7/7 | 508.357 [498.458,519.807] | 215.930 [209.389,221.330] | 271.338 [263.559,282.527] | 329904.000 [329404.000,330036.000] |
| ascii-8MiB-construct-scan | base/js | FAIL 1 | 22.224 [20.838,25.132] | — | — | 51296.000 [51180.000,51624.000] |
| ascii-8MiB-construct-scan | candidate/c | 7/7 | 128.763 [123.377,130.730] | 12.962 [11.858,14.010] | 111.160 [106.767,114.443] | 34916.000 [34800.000,34996.000] |
| ascii-8MiB-construct-scan | candidate/js | 7/7 | 937.651 [905.729,962.952] | 0.245 [0.209,0.355] | 913.821 [881.302,938.713] | 113256.000 [112288.000,114916.000] |
| ascii-8MiB-io-materialize | base/c | 7/7 | 242.860 [234.277,248.392] | 64.677 [63.033,67.970] | 154.252 [149.895,158.517] | 329544.000 [329312.000,329808.000] |
| ascii-8MiB-io-materialize | base/js | FAIL 1 | 40.189 [36.346,43.793] | — | — | 71420.000 [71400.000,71724.000] |
| ascii-8MiB-io-materialize | candidate/c | 7/7 | 152.015 [150.224,164.248] | 23.128 [20.446,25.207] | 122.393 [121.258,130.578] | 90908.000 [90812.000,91228.000] |
| ascii-8MiB-io-materialize | candidate/js | 7/7 | 1314.041 [1262.879,1356.513] | 328.721 [319.301,345.082] | 935.341 [885.974,977.350] | 569744.000 [563844.000,579908.000] |
| ascii-64MiB-io-scan | base/c | 7/7 | 1688.742 [1667.065,1705.610] | 519.033 [510.165,531.572] | 1094.442 [1076.993,1115.740] | 1115832.000 [1115748.000,1116148.000] |
| ascii-64MiB-io-scan | base/js | NOT RUN (JS size limit) | — | — | — | — |
| ascii-64MiB-io-scan | candidate/c | 7/7 | 1087.338 [1023.134,1163.221] | 186.817 [179.225,209.802] | 875.736 [826.620,954.964] | 329784.000 [329576.000,329972.000] |
| ascii-64MiB-io-scan | candidate/js | NOT RUN (JS size limit) | — | — | — | — |
| ascii-64MiB-construct-scan | base/c | 7/7 | 4014.996 [3982.819,4046.072] | 1697.148 [1683.039,1725.400] | 2153.915 [2125.594,2177.398] | 2622840.000 [2622768.000,2623480.000] |
| ascii-64MiB-construct-scan | base/js | NOT RUN (JS size limit) | — | — | — | — |
| ascii-64MiB-construct-scan | candidate/c | 7/7 | 961.836 [935.103,975.114] | 100.037 [95.141,102.936] | 838.084 [817.510,851.442] | 264312.000 [264056.000,264504.000] |
| ascii-64MiB-construct-scan | candidate/js | NOT RUN (JS size limit) | — | — | — | — |
| ascii-64MiB-io-materialize | base/c | 7/7 | 1921.914 [1911.940,1944.100] | 501.138 [495.107,520.736] | 1248.595 [1231.265,1274.178] | 2623188.000 [2622924.000,2623404.000] |
| ascii-64MiB-io-materialize | base/js | NOT RUN (JS size limit) | — | — | — | — |
| ascii-64MiB-io-materialize | candidate/c | 7/7 | 1218.370 [1200.792,1245.480] | 178.963 [171.282,209.442] | 987.886 [971.915,1013.269] | 713324.000 [713132.000,713588.000] |
| ascii-64MiB-io-materialize | candidate/js | NOT RUN (JS size limit) | — | — | — | — |
| unicode-1MiB-io-scan | base/c | 7/7 | 18.754 [17.973,19.247] | 5.295 [5.177,5.771] | 10.445 [10.052,10.895] | 13492.000 [13428.000,13548.000] |
| unicode-1MiB-io-scan | base/js | 7/7 | 651.642 [633.105,688.294] | 11.407 [10.980,12.289] | 616.873 [597.353,654.236] | 163008.000 [162568.000,163500.000] |
| unicode-1MiB-io-scan | candidate/c | 7/7 | 15.024 [14.175,16.989] | 2.536 [2.325,2.752] | 9.626 [9.255,11.897] | 5752.000 [5732.000,5812.000] |
| unicode-1MiB-io-scan | candidate/js | 7/7 | 178.221 [168.199,189.359] | 58.499 [56.156,60.180] | 94.793 [90.213,107.569] | 141116.000 [139008.000,147708.000] |
| unicode-1MiB-construct-scan | base/c | 7/7 | 41.284 [39.154,43.310] | 17.000 [16.007,18.396] | 19.613 [19.382,22.621] | 27896.000 [27764.000,27956.000] |
| unicode-1MiB-construct-scan | base/js | FAIL 1 | 22.717 [21.276,25.994] | — | — | 51704.000 [51596.000,51724.000] |
| unicode-1MiB-construct-scan | candidate/c | 7/7 | 13.156 [12.324,15.323] | 1.059 [0.981,1.401] | 9.766 [9.031,11.500] | 4844.000 [4712.000,4984.000] |
| unicode-1MiB-construct-scan | candidate/js | 7/7 | 119.013 [117.167,120.536] | 0.219 [0.205,0.297] | 96.068 [94.907,98.160] | 96500.000 [95652.000,103648.000] |
| unicode-1MiB-io-materialize | base/c | 7/7 | 21.858 [20.793,22.656] | 5.327 [5.064,5.811] | 12.030 [11.207,12.758] | 27864.000 [27508.000,28004.000] |
| unicode-1MiB-io-materialize | base/js | FAIL 1 | 33.131 [28.897,36.371] | — | — | 57724.000 [57452.000,57976.000] |
| unicode-1MiB-io-materialize | candidate/c | 7/7 | 16.701 [16.172,17.918] | 2.446 [2.309,2.973] | 11.127 [10.975,12.232] | 10988.000 [10836.000,11100.000] |
| unicode-1MiB-io-materialize | candidate/js | 7/7 | 168.408 [160.712,172.503] | 58.508 [56.360,59.687] | 86.460 [80.257,90.572] | 162252.000 [161100.000,163976.000] |
| unicode-8MiB-io-scan | base/c | 7/7 | 136.050 [131.038,140.385] | 42.872 [40.792,44.991] | 86.437 [80.420,88.861] | 92268.000 [92080.000,92280.000] |
| unicode-8MiB-io-scan | base/js | 7/7 | 5487.262 [5455.827,5566.148] | 20.555 [19.742,21.876] | 5433.779 [5404.097,5511.607] | 289780.000 [287848.000,333472.000] |
| unicode-8MiB-io-scan | candidate/c | 7/7 | 96.291 [93.411,101.215] | 19.704 [19.176,20.518] | 73.566 [69.584,78.170] | 30772.000 [30584.000,30840.000] |
| unicode-8MiB-io-scan | candidate/js | 7/7 | 1068.935 [1049.443,1113.723] | 424.715 [414.097,433.164] | 608.619 [582.691,630.542] | 534844.000 [532900.000,555616.000] |
| unicode-8MiB-construct-scan | base/c | 7/7 | 298.913 [291.462,306.445] | 130.304 [128.280,136.820] | 151.441 [149.936,159.541] | 207016.000 [206824.000,207220.000] |
| unicode-8MiB-construct-scan | base/js | FAIL 1 | 22.605 [21.241,24.563] | — | — | 51776.000 [51520.000,52088.000] |
| unicode-8MiB-construct-scan | candidate/c | 7/7 | 84.129 [83.042,96.174] | 8.111 [7.520,8.499] | 72.360 [71.801,83.998] | 22608.000 [22500.000,22836.000] |
| unicode-8MiB-construct-scan | candidate/js | 7/7 | 645.374 [626.102,656.070] | 0.245 [0.208,0.268] | 621.092 [601.987,631.140] | 117016.000 [115576.000,117536.000] |
| unicode-8MiB-io-materialize | base/c | 7/7 | 154.870 [146.427,160.187] | 42.333 [39.897,46.533] | 96.511 [91.989,100.257] | 206904.000 [206588.000,207128.000] |
| unicode-8MiB-io-materialize | base/js | FAIL 1 | 42.817 [41.131,44.771] | — | — | 74700.000 [74556.000,74936.000] |
| unicode-8MiB-io-materialize | candidate/c | 7/7 | 114.859 [111.190,118.521] | 20.057 [18.419,20.432] | 87.476 [84.956,93.658] | 71840.000 [71736.000,72036.000] |
| unicode-8MiB-io-materialize | candidate/js | 7/7 | 1162.128 [1130.683,1199.268] | 435.927 [418.942,450.487] | 664.028 [653.002,699.493] | 715312.000 [710252.000,720448.000] |
| unicode-64MiB-io-scan | base/c | 7/7 | 1043.408 [1029.942,1066.736] | 337.692 [333.504,349.923] | 655.862 [649.751,671.340] | 722792.000 [722480.000,723044.000] |
| unicode-64MiB-io-scan | base/js | NOT RUN (JS size limit) | — | — | — | — |
| unicode-64MiB-io-scan | candidate/c | 7/7 | 775.263 [741.670,822.237] | 155.541 [150.882,164.503] | 603.976 [577.149,653.347] | 231336.000 [231024.000,231528.000] |
| unicode-64MiB-io-scan | candidate/js | NOT RUN (JS size limit) | — | — | — | — |
| unicode-64MiB-construct-scan | base/c | 7/7 | 2472.437 [2460.853,2500.677] | 1086.504 [1069.719,1102.745] | 1280.261 [1265.836,1291.467] | 1640052.000 [1639860.000,1640632.000] |
| unicode-64MiB-construct-scan | base/js | NOT RUN (JS size limit) | — | — | — | — |
| unicode-64MiB-construct-scan | candidate/c | 7/7 | 711.881 [682.547,733.087] | 68.782 [67.758,77.471] | 626.300 [602.021,648.837] | 165996.000 [165932.000,166120.000] |
| unicode-64MiB-construct-scan | candidate/js | NOT RUN (JS size limit) | — | — | — | — |
| unicode-64MiB-io-materialize | base/c | 7/7 | 1227.300 [1202.212,1238.639] | 335.147 [327.031,346.640] | 787.192 [771.725,813.740] | 1640324.000 [1639776.000,1640612.000] |
| unicode-64MiB-io-materialize | base/js | NOT RUN (JS size limit) | — | — | — | — |
| unicode-64MiB-io-materialize | candidate/c | 7/7 | 916.022 [891.307,930.039] | 155.035 [151.712,164.868] | 719.822 [695.065,725.208] | 558852.000 [558492.000,559136.000] |
| unicode-64MiB-io-materialize | candidate/js | NOT RUN (JS size limit) | — | — | — | — |
| retain-8MiB-view | base/c | 7/7 | 133.875 [133.241,136.280] | 61.246 [59.429,63.652] | 62.684 [62.452,63.802] | 141420.000 [141284.000,141488.000] |
| retain-8MiB-view | base/js | 7/7 | 38.459 [35.598,39.177] | 17.281 [16.422,19.312] | 4.115 [3.785,4.362] | 70124.000 [69844.000,70248.000] |
| retain-8MiB-view | candidate/c | 7/7 | 26.294 [24.866,26.768] | 21.761 [20.495,22.564] | 0.009 [0.008,0.009] | 43056.000 [42872.000,43256.000] |
| retain-8MiB-view | candidate/js | 7/7 | 366.885 [352.864,390.828] | 332.585 [319.128,348.761] | 0.234 [0.203,0.344] | 328256.000 [327940.000,328576.000] |
| retain-8MiB-copy | base/c | 7/7 | 136.723 [132.930,144.276] | 62.984 [59.691,66.525] | 63.978 [61.519,66.157] | 141356.000 [141168.000,141556.000] |
| retain-8MiB-copy | base/js | 7/7 | 37.574 [34.313,41.516] | 17.119 [16.332,20.321] | 4.302 [3.903,5.195] | 70644.000 [70400.000,70840.000] |
| retain-8MiB-copy | candidate/c | 7/7 | 25.721 [24.935,27.280] | 21.684 [21.129,22.941] | 0.009 [0.008,0.011] | 43116.000 [42868.000,43244.000] |
| retain-8MiB-copy | candidate/js | 7/7 | 360.755 [355.654,383.408] | 327.899 [320.549,348.601] | 0.218 [0.187,0.394] | 328120.000 [327932.000,328516.000] |
| search-32768-512 | base/c | 7/7 | 110.186 [105.451,113.675] | 0.836 [0.794,0.878] | 107.022 [102.345,110.389] | 3508.000 [3320.000,3572.000] |
| search-32768-512 | base/js | FAIL 1 | 21.518 [20.805,22.164] | — | — | 51704.000 [51316.000,51908.000] |
| search-32768-512 | candidate/c | 7/7 | 2.011 [1.908,2.195] | 0.091 [0.083,0.121] | 0.107 [0.103,0.146] | 2352.000 [2172.000,2408.000] |
| search-32768-512 | candidate/js | 7/7 | 16.851 [16.740,18.015] | 0.261 [0.209,0.302] | 0.170 [0.153,0.199] | 42052.000 [41984.000,42180.000] |
| search-65536-1024 | base/c | 7/7 | 426.699 [418.624,452.500] | 1.826 [1.626,2.222] | 422.550 [414.597,448.108] | 4708.000 [4432.000,4836.000] |
| search-65536-1024 | base/js | FAIL 1 | 23.296 [20.840,25.954] | — | — | 51592.000 [51136.000,51852.000] |
| search-65536-1024 | candidate/c | 7/7 | 2.318 [2.131,2.503] | 0.170 [0.163,0.220] | 0.212 [0.208,0.239] | 2424.000 [2352.000,2488.000] |
| search-65536-1024 | candidate/js | 7/7 | 17.795 [16.135,20.125] | 0.241 [0.218,0.267] | 0.286 [0.258,0.294] | 42096.000 [41992.000,42308.000] |
| search-131072-2048 | base/c | 7/7 | 1676.450 [1644.997,1695.191] | 3.424 [3.306,3.792] | 1670.125 [1638.641,1689.219] | 7404.000 [7216.000,7528.000] |
| search-131072-2048 | base/js | FAIL 1 | 22.848 [22.138,26.126] | — | — | 51904.000 [51508.000,52036.000] |
| search-131072-2048 | candidate/c | 7/7 | 2.598 [2.555,2.869] | 0.340 [0.315,0.490] | 0.426 [0.411,0.492] | 2660.000 [2512.000,2804.000] |
| search-131072-2048 | candidate/js | 7/7 | 17.564 [17.418,18.360] | 0.311 [0.231,0.357] | 0.467 [0.457,0.523] | 42304.000 [42120.000,42508.000] |
| build-concat-1024 | base/c | 7/7 | 1.815 [1.718,1.867] | 0.042 [0.040,0.046] | 0.010 [0.010,0.011] | 2304.000 [2168.000,2424.000] |
| build-concat-1024 | base/js | 7/7 | 19.170 [17.832,23.267] | 0.922 [0.877,1.241] | 1.138 [0.880,1.344] | 46976.000 [46592.000,47052.000] |
| build-concat-1024 | candidate/c | 7/7 | 1.950 [1.760,2.001] | 0.082 [0.071,0.091] | 0.025 [0.025,0.033] | 2480.000 [2296.000,2548.000] |
| build-concat-1024 | candidate/js | 7/7 | 20.029 [17.852,21.553] | 0.922 [0.793,1.204] | 1.302 [1.166,1.480] | 47424.000 [47052.000,47480.000] |
| build-concat-4096 | base/c | 7/7 | 2.088 [1.971,2.290] | 0.191 [0.176,0.256] | 0.038 [0.037,0.042] | 2552.000 [2372.000,2676.000] |
| build-concat-4096 | base/js | 7/7 | 21.885 [20.209,27.686] | 1.817 [1.628,1.920] | 2.807 [2.589,3.209] | 53244.000 [52748.000,53512.000] |
| build-concat-4096 | candidate/c | 7/7 | 2.186 [2.103,2.269] | 0.169 [0.163,0.197] | 0.103 [0.095,0.155] | 2552.000 [2472.000,2676.000] |
| build-concat-4096 | candidate/js | 7/7 | 23.057 [21.235,27.793] | 1.723 [1.554,1.891] | 2.886 [2.695,3.557] | 53512.000 [53248.000,53700.000] |
| build-join-1024 | base/c | 7/7 | 1.941 [1.802,2.035] | 0.050 [0.045,0.057] | 0.013 [0.013,0.014] | 2352.000 [2224.000,2420.000] |
| build-join-1024 | base/js | 7/7 | 18.767 [18.480,21.919] | 1.049 [0.934,1.236] | 1.316 [1.071,1.676] | 47244.000 [47112.000,47736.000] |
| build-join-1024 | candidate/c | 7/7 | 1.917 [1.802,2.143] | 0.093 [0.081,0.133] | 0.034 [0.033,0.042] | 2408.000 [2276.000,2552.000] |
| build-join-1024 | candidate/js | 7/7 | 19.320 [18.577,21.834] | 0.871 [0.802,0.990] | 1.323 [1.253,1.727] | 47872.000 [47548.000,48008.000] |
| build-join-4096 | base/c | 7/7 | 2.102 [2.034,2.239] | 0.240 [0.217,0.309] | 0.050 [0.048,0.052] | 2680.000 [2600.000,2744.000] |
| build-join-4096 | base/js | 7/7 | 23.469 [21.806,25.807] | 1.982 [1.829,2.091] | 3.546 [3.078,6.147] | 54136.000 [53940.000,54212.000] |
| build-join-4096 | candidate/c | 7/7 | 2.115 [2.066,2.414] | 0.175 [0.167,0.237] | 0.139 [0.126,0.173] | 2616.000 [2424.000,2676.000] |
| build-join-4096 | candidate/js | 7/7 | 23.137 [21.204,26.723] | 1.689 [1.513,1.901] | 3.436 [3.305,4.417] | 54572.000 [54136.000,55308.000] |
| build-repeat-1024 | base/c | 7/7 | 1.840 [1.744,1.914] | 0.038 [0.037,0.046] | 0.010 [0.010,0.011] | 2360.000 [2168.000,2420.000] |
| build-repeat-1024 | base/js | 7/7 | 18.275 [16.460,20.347] | 0.701 [0.645,0.844] | 1.104 [0.933,1.504] | 46912.000 [46524.000,47048.000] |
| build-repeat-1024 | candidate/c | 7/7 | 1.895 [1.741,1.991] | 0.019 [0.015,0.023] | 0.025 [0.024,0.028] | 2288.000 [2168.000,2420.000] |
| build-repeat-1024 | candidate/js | 7/7 | 19.345 [17.650,21.212] | 0.310 [0.254,0.349] | 1.557 [1.499,1.898] | 47488.000 [46916.000,47624.000] |
| build-repeat-4096 | base/c | 7/7 | 2.100 [1.944,2.315] | 0.173 [0.170,0.265] | 0.037 [0.036,0.040] | 2536.000 [2472.000,2676.000] |
| build-repeat-4096 | base/js | 7/7 | 21.255 [19.813,25.112] | 1.315 [1.222,1.590] | 2.726 [2.618,3.838] | 51984.000 [50048.000,52492.000] |
| build-repeat-4096 | candidate/c | 7/7 | 1.937 [1.841,2.167] | 0.032 [0.030,0.040] | 0.097 [0.093,0.107] | 2412.000 [2276.000,2424.000] |
| build-repeat-4096 | candidate/js | 7/7 | 20.498 [19.854,23.325] | 0.275 [0.257,0.391] | 3.338 [3.040,3.986] | 52808.000 [51684.000,53128.000] |
| build-append-1024 | base/c | 7/7 | 3.251 [3.157,3.609] | 1.474 [1.310,1.765] | 0.004 [0.003,0.006] | 2168.000 [2088.000,2228.000] |
| build-append-1024 | base/js | 7/7 | 18.571 [18.215,19.209] | 1.101 [0.924,1.210] | 0.445 [0.375,0.550] | 46584.000 [46476.000,46840.000] |
| build-append-1024 | candidate/c | 7/7 | 1.881 [1.804,2.037] | 0.085 [0.075,0.095] | 0.009 [0.009,0.013] | 2548.000 [2484.000,2552.000] |
| build-append-1024 | candidate/js | 7/7 | 19.148 [18.468,20.519] | 1.061 [0.850,1.167] | 0.434 [0.383,0.583] | 47040.000 [46736.000,47308.000] |
| build-append-4096 | base/c | 7/7 | 26.046 [23.848,26.785] | 23.610 [21.644,24.647] | 0.014 [0.013,0.016] | 2276.000 [2088.000,2420.000] |
| build-append-4096 | base/js | 7/7 | 19.927 [18.829,22.549] | 1.490 [1.295,1.727] | 1.163 [1.081,1.297] | 50824.000 [48456.000,50940.000] |
| build-append-4096 | candidate/c | 7/7 | 2.035 [1.967,2.168] | 0.127 [0.122,0.140] | 0.031 [0.030,0.046] | 2404.000 [2296.000,2548.000] |
| build-append-4096 | candidate/js | 7/7 | 19.750 [18.555,22.170] | 1.385 [1.308,1.653] | 1.085 [1.020,1.240] | 51256.000 [50820.000,51536.000] |
| build-snapshots-128 | base/c | 7/7 | 1.937 [1.823,2.145] | 0.151 [0.146,0.227] | 0.027 [0.026,0.036] | 2404.000 [2296.000,2476.000] |
| build-snapshots-128 | base/js | 7/7 | 20.339 [19.424,23.424] | 0.484 [0.426,0.532] | 2.233 [2.060,2.427] | 50764.000 [50560.000,51132.000] |
| build-snapshots-128 | candidate/c | 7/7 | 1.955 [1.837,2.013] | 0.076 [0.073,0.103] | 0.055 [0.055,0.056] | 2424.000 [2352.000,2548.000] |
| build-snapshots-128 | candidate/js | 7/7 | 20.794 [19.761,23.430] | 0.457 [0.443,1.094] | 2.236 [2.095,2.667] | 51396.000 [51136.000,52168.000] |
| build-snapshots-512 | base/c | 7/7 | 5.225 [4.974,5.616] | 2.331 [2.204,2.756] | 0.620 [0.546,0.648] | 5352.000 [5296.000,5420.000] |
| build-snapshots-512 | base/js | 7/7 | 39.457 [37.864,40.232] | 0.673 [0.606,0.795] | 17.580 [16.582,18.216] | 76484.000 [76304.000,76732.000] |
| build-snapshots-512 | candidate/c | 7/7 | 3.349 [3.291,3.691] | 0.496 [0.468,0.645] | 0.949 [0.850,1.003] | 3756.000 [3576.000,3820.000] |
| build-snapshots-512 | candidate/js | 7/7 | 40.227 [38.246,42.154] | 0.640 [0.555,0.834] | 17.557 [16.575,19.539] | 77000.000 [76864.000,77256.000] |
| map-prefix-256 | base/c | 7/7 | 5.293 [5.064,5.564] | 1.477 [1.376,1.809] | 1.793 [1.736,1.958] | 2544.000 [2528.000,2676.000] |
| map-prefix-256 | base/js | 7/7 | 83.366 [80.334,87.198] | 38.151 [36.508,41.563] | 19.616 [19.090,23.263] | 100420.000 [100168.000,100936.000] |
| map-prefix-256 | candidate/c | 7/7 | 2.512 [2.247,2.965] | 0.433 [0.394,0.586] | 0.039 [0.037,0.077] | 2424.000 [2360.000,2548.000] |
| map-prefix-256 | candidate/js | 7/7 | 44.113 [43.035,49.586] | 15.444 [14.716,16.693] | 5.787 [5.061,7.406] | 83448.000 [82568.000,83852.000] |
| map-prefix-4096 | base/c | 7/7 | 61.803 [60.728,64.321] | 24.007 [23.262,27.004] | 35.083 [34.520,36.893] | 8620.000 [8568.000,8724.000] |
| map-prefix-4096 | base/js | 7/7 | 741.196 [731.076,754.061] | 386.551 [378.645,397.741] | 329.109 [310.765,349.679] | 138408.000 [135976.000,139776.000] |
| map-prefix-4096 | candidate/c | 7/7 | 8.289 [8.170,9.952] | 5.877 [5.676,7.337] | 0.169 [0.159,0.205] | 3496.000 [3428.000,3556.000] |
| map-prefix-4096 | candidate/js | 7/7 | 192.346 [187.315,203.191] | 118.782 [114.695,128.438] | 49.188 [44.631,53.303] | 115524.000 [114876.000,116476.000] |

## Full provenance and raw measurements

All acceptance numbers are from this final invocation. Earlier exploratory runs were superseded and are not used in these tables. Full emitted sources, primary and instrumented binaries, stdout/stderr, verbose GNU time reports, and per-run JSON remain at `/tmp/bend-strings-slice5-acceptance`. Every raw numeric sample used here (including warmups, failures, monotonic markers, and counter snapshots) is embedded below; reproduction does not depend on preserving `/tmp`.

<details><summary>Machine, versions, flags, warm state, and source identities</summary>

```json
{
  "start_utc": "2026-09-18T03:16:27Z",
  "candidate": "335f3405d15d3eb51f698526f612c01fe96eaa37",
  "baseline": "309bbf62fd83e0c2f81eb5d176c11bca09b49686",
  "candidate_branch": "strings",
  "baseline_status": "",
  "baseline_sources": {
    "bend2/base.bend": "d8acbea4eba04f74bc0c2e30f18e68d2c4d36042ddabbd1da3022fa984479e8e",
    "bend2/comp.ts": "9a2e8c1d817e9f7bb2da4073ea1094f26859cf13be86b5f99aca00a440429acf",
    "bend2/bend.ts": "2fe2456499af467aa2b0eddf0d2dc1338e125a3efa81956b3039414d81e3f629",
    "bend2/main.ts": "a455c2279b6b5c5485d31018e939c98c357bb6395db819449d05fa2d910d3e4a"
  },
  "machine": "Linux-6.17.12-300.fc43.x86_64-x86_64-with-glibc2.42",
  "cpu": "Architecture:                            x86_64\nCPU op-mode(s):                          32-bit, 64-bit\nAddress sizes:                           48 bits physical, 48 bits virtual\nByte Order:                              Little Endian\nCPU(s):                                  16\nOn-line CPU(s) list:                     0-15\nVendor ID:                               AuthenticAMD\nModel name:                              AMD Ryzen 7 7700X 8-Core Processor\nCPU family:                              25\nModel:                                   97\nThread(s) per core:                      2\nCore(s) per socket:                      8\nSocket(s):                               1\nStepping:                                2\nFrequency boost:                         enabled\nCPU(s) scaling MHz:                      93%\nCPU max MHz:                             5575.8662\nCPU min MHz:                             403.0750\nBogoMIPS:                                8983.08\nFlags:                                   fpu vme de pse tsc msr pae mce cx8 apic sep mtrr pge mca cmov pat pse36 clflush mmx fxsr sse sse2 ht syscall nx mmxext fxsr_opt pdpe1gb rdtscp lm constant_tsc rep_good amd_lbr_v2 nopl xtopology nonstop_tsc cpuid extd_apicid aperfmperf rapl pni pclmulqdq monitor ssse3 fma cx16 sse4_1 sse4_2 movbe popcnt aes xsave avx f16c rdrand lahf_lm cmp_legacy svm extapic cr8_legacy abm sse4a misalignsse 3dnowprefetch osvw ibs skinit wdt tce topoext perfctr_core perfctr_nb bpext perfctr_llc mwaitx cpuid_fault cpb cat_l3 cdp_l3 hw_pstate ssbd mba perfmon_v2 ibrs ibpb stibp ibrs_enhanced vmmcall fsgsbase bmi1 avx2 smep bmi2 erms invpcid cqm rdt_a avx512f avx512dq rdseed adx smap avx512ifma clflushopt clwb avx512cd sha_ni avx512bw avx512vl xsaveopt xsavec xgetbv1 xsaves cqm_llc cqm_occup_llc cqm_mbm_total cqm_mbm_local user_shstk avx512_bf16 clzero irperf xsaveerptr rdpru wbnoinvd cppc arat npt lbrv svm_lock nrip_save tsc_scale vmcb_clean flushbyasid decodeassists pausefilter pfthreshold avic vgif x2avic v_spec_ctrl vnmi avx512vbmi umip pku ospke avx512_vbmi2 gfni vaes vpclmulqdq avx512_vnni avx512_bitalg avx512_vpopcntdq rdpid overflow_recov succor smca fsrm flush_l1d amd_lbr_pmc_freeze\nVirtualization:                          AMD-V\nL1d cache:                               256 KiB (8 instances)\nL1i cache:                               256 KiB (8 instances)\nL2 cache:                                8 MiB (8 instances)\nL3 cache:                                32 MiB (1 instance)\nNUMA node(s):                            1\nNUMA node0 CPU(s):                       0-15\nVulnerability Gather data sampling:      Not affected\nVulnerability Ghostwrite:                Not affected\nVulnerability Indirect target selection: Not affected\nVulnerability Itlb multihit:             Not affected\nVulnerability L1tf:                      Not affected\nVulnerability Mds:                       Not affected\nVulnerability Meltdown:                  Not affected\nVulnerability Mmio stale data:           Not affected\nVulnerability Old microcode:             Not affected\nVulnerability Reg file data sampling:    Not affected\nVulnerability Retbleed:                  Not affected\nVulnerability Spec rstack overflow:      Mitigation; Safe RET\nVulnerability Spec store bypass:         Mitigation; Speculative Store Bypass disabled via prctl\nVulnerability Spectre v1:                Mitigation; usercopy/swapgs barriers and __user pointer sanitization\nVulnerability Spectre v2:                Mitigation; Enhanced / Automatic IBRS; IBPB conditional; STIBP always-on; PBRSB-eIBRS Not affected; BHI Not affected\nVulnerability Srbds:                     Not affected\nVulnerability Tsa:                       Mitigation; Clear CPU buffers\nVulnerability Tsx async abort:           Not affected\nVulnerability Vmscape:                   Mitigation; IBPB before exit to userspace",
  "memory": "total        used        free      shared  buff/cache   available\nMem:     32699092992 19207802880  2812628992   766390272 10947977216 13491290112\nSwap:    33529257984 18648031232 14881226752",
  "compiler": "clang version 21.1.7 (Fedora 21.1.7-1.fc43)\nTarget: x86_64-redhat-linux-gnu\nThread model: posix\nInstalledDir: /home/omen/opt/clang21/usr/bin",
  "bun": "1.3.4",
  "flags": [
    "-std=c11",
    "-O3",
    "-g",
    "-fno-omit-frame-pointer",
    "-lpthread",
    "-lm"
  ],
  "c_args": [
    "--gpu",
    "off",
    "--threads",
    "1"
  ],
  "warmups": 1,
  "measurements": 7,
  "timeout_seconds": 120,
  "js_max_input_bytes": 8388608,
  "warm_state": "One untimed process per row, then seven fresh processes; page cache warm; JS JIT starts fresh each process; no cache flush or CPU pinning.",
  "counters": "Separate instrumented binary: heap_alloc/free requested bytes (not allocator reserve, RSS, or malloc); tick snapshots reset interval peak.",
  "sources": {
    "bend2/base.bend": "a11a95b3a544fa305b50f3c32c2079bbfccfadbf46705cb8b7ac75201bb5f8df",
    "bend2/comp.ts": "cfeab708fbe67911805481c50e32fe42a1ce14a00f691ac13d0d5b223b1b4850",
    "tests/strings/bench_words.bend": "fa49ba89c724f5ec4cb02098e7a9348d3f6ae5575c8013a938b2b457a855b83f",
    "tests/strings/bench.sh": "6ec4059e9e52c8d4218aadf6ac507a0362320273213ea2862ca83a1886e4058a"
  }
}
```

</details>

<details><summary>Workload parameters, exact byte counts, oracles, input/driver/binary identities</summary>

```json
[
  {
    "name": "legacy-1024",
    "corpus": "legacy",
    "reps": 1024,
    "mode": "materialize",
    "source": "construct",
    "bytes": 45056,
    "codepoints": 45056,
    "suffix": "",
    "expected": "9216:3218203648",
    "driver_sha256": "f7a2aa46ccdc65dfb1b7dd1a09f57add1c9a2c63c5d7ca5c30492eb525767720",
    "base_binary_sha256": "36dcdf2f54d28de1690b3cc2634648a1117e7f22cc49354d5c18553e271acb3b",
    "candidate_binary_sha256": "74a6e6fa7c39669653c3aeb9f1e60d28aeffc743aca7f3ea2b301cb888c417e9"
  },
  {
    "name": "legacy-4096",
    "corpus": "legacy",
    "reps": 4096,
    "mode": "materialize",
    "source": "construct",
    "bytes": 180224,
    "codepoints": 180224,
    "suffix": "",
    "expected": "36864:4282880000",
    "driver_sha256": "d12292b7228d367d77da3e72dd52f14216c471919e668e23c5af9bc141841f7f",
    "base_binary_sha256": "f58e05d674a4abfdea08ea0bb24cfbda3844410cd34bce819baae7a93f0c34c1",
    "candidate_binary_sha256": "24d3d1e7ec7acb272dad64471fb334e34a80d0f9e45f69a48bc712a2588bc7dd"
  },
  {
    "name": "ascii-1MiB-io-scan",
    "corpus": "ascii",
    "reps": 49932,
    "size_bytes": 1048576,
    "mode": "scan",
    "source": "io",
    "bytes": 1048576,
    "codepoints": 1048576,
    "suffix": "  al",
    "expected": "149797:986728105",
    "input_sha256": "95b6f45ba77fb40dc0b3e8524db8e9069cac6f0b74f7873621490cd756b65d2c",
    "driver_sha256": "f82c99ec589ace7fe3be028d3b23182db4965f6e9615156381e3752dde085bb9",
    "base_binary_sha256": "71e73957030e76f8764885b4a0cb4fe15377891a61e01cd26138097652733011",
    "candidate_binary_sha256": "85ee303fdc535d049b6a8773e4f3c1104d8e735e65b1d39d153434c32581e72e"
  },
  {
    "name": "ascii-1MiB-construct-scan",
    "corpus": "ascii",
    "reps": 49932,
    "size_bytes": 1048576,
    "mode": "scan",
    "source": "construct",
    "bytes": 1048576,
    "codepoints": 1048576,
    "suffix": "  al",
    "expected": "149797:986728105",
    "driver_sha256": "73355d79f1b267122df1d32deb237edbb1f5c0636200a591cdc79ab73b6139a1",
    "base_binary_sha256": "0fbc0cf186d4038b9265fca7074ed2ae53277abc31ab42e4d8558d9f5ca0decc",
    "candidate_binary_sha256": "0f9d310bc06d54cec88b2684bf936b344d5679438431854a31008418c9b3fa39"
  },
  {
    "name": "ascii-1MiB-io-materialize",
    "corpus": "ascii",
    "reps": 49932,
    "size_bytes": 1048576,
    "mode": "materialize",
    "source": "io",
    "bytes": 1048576,
    "codepoints": 1048576,
    "suffix": "  al",
    "expected": "149797:986728105",
    "input_sha256": "95b6f45ba77fb40dc0b3e8524db8e9069cac6f0b74f7873621490cd756b65d2c",
    "driver_sha256": "f61201c1be6c8bee4f17d9ad8ed40e6144a949d4d955af9682e95b4f277f5290",
    "base_binary_sha256": "d0bec91026f1a539d14034fe321444c0a8e1e3a419ed22bd93fbd74195b30566",
    "candidate_binary_sha256": "a86f4829708c0a9b41bff10709929db2f738a3da325e261a0b1642f1fd692355"
  },
  {
    "name": "ascii-8MiB-io-scan",
    "corpus": "ascii",
    "reps": 399457,
    "size_bytes": 8388608,
    "mode": "scan",
    "source": "io",
    "bytes": 8388608,
    "codepoints": 8388608,
    "suffix": "  alpha bet",
    "expected": "1198373:3966417190",
    "input_sha256": "0b6ddf9b9444849a1ea1e867d32da4dccdfd75702427667a9dafd5fbf035ed31",
    "driver_sha256": "0a1d3d780c2c1260f7df446f60d0eb44990673474c7adcfd3e2d7eed155a9b90",
    "base_binary_sha256": "128acadfe712f27e338e2761512385a68e5db62481847ee3d13bb1768d9bddee",
    "candidate_binary_sha256": "0bfa16b0c562d4f16d0e9c714f3a46d9b99630c09d87a4162f465efbcd0012f3"
  },
  {
    "name": "ascii-8MiB-construct-scan",
    "corpus": "ascii",
    "reps": 399457,
    "size_bytes": 8388608,
    "mode": "scan",
    "source": "construct",
    "bytes": 8388608,
    "codepoints": 8388608,
    "suffix": "  alpha bet",
    "expected": "1198373:3966417190",
    "driver_sha256": "22a405b20d8c233ef5cac661e1a96a119dc9f9f440008e99e41fd1fc3fe109b5",
    "base_binary_sha256": "5619c65aead33322d99c37e96527f90ba53c106ba96679ea4f04fdb65cacf7c2",
    "candidate_binary_sha256": "4838d5789b299b778b6ec85050276928d5cc2ad42f777de9e09d44e2b583aaad"
  },
  {
    "name": "ascii-8MiB-io-materialize",
    "corpus": "ascii",
    "reps": 399457,
    "size_bytes": 8388608,
    "mode": "materialize",
    "source": "io",
    "bytes": 8388608,
    "codepoints": 8388608,
    "suffix": "  alpha bet",
    "expected": "1198373:3966417190",
    "input_sha256": "0b6ddf9b9444849a1ea1e867d32da4dccdfd75702427667a9dafd5fbf035ed31",
    "driver_sha256": "5ce42fe3976f84293e9fbd35bf67ce6a58e1e344edb5c8540976cbee7153ecc0",
    "base_binary_sha256": "c93f7226dfc4ca12ed908bb243d4f11bf9fd8dfcaf477d69c098fda36732cdb9",
    "candidate_binary_sha256": "c95dcfcbf44d04b75278d3907bc1d1cf62de184aa84b2bac05d632036d954372"
  },
  {
    "name": "ascii-64MiB-io-scan",
    "corpus": "ascii",
    "reps": 3195660,
    "size_bytes": 67108864,
    "mode": "scan",
    "source": "io",
    "bytes": 67108864,
    "codepoints": 67108864,
    "suffix": "  al",
    "expected": "9586981:1707099817",
    "input_sha256": "54d2dd39cc2c4995b12d7f8efa26ef125c7e847cb38838450c62c92f3726a33c",
    "driver_sha256": "c7c4ca083d78a9e1356845a261c465e27774b3bd5f5e820543c35e43f2721ed5",
    "base_binary_sha256": "9465a36d81acc36a825fdc970c72b02585a77ec47ededc0896c7c10aba48a1a2",
    "candidate_binary_sha256": "3e68c3d413034937cc87fbfbb0f95ebba2be8130c259e8934105f94e29638678"
  },
  {
    "name": "ascii-64MiB-construct-scan",
    "corpus": "ascii",
    "reps": 3195660,
    "size_bytes": 67108864,
    "mode": "scan",
    "source": "construct",
    "bytes": 67108864,
    "codepoints": 67108864,
    "suffix": "  al",
    "expected": "9586981:1707099817",
    "driver_sha256": "46eb09d0a5df1a75ee21e31efc2dd2c71c9f2469f105849e9bf5cb5e2d425093",
    "base_binary_sha256": "467b3b127051248cdbdede9f590c6f4adb08331240cb8fa17749f2fbcafa4daf",
    "candidate_binary_sha256": "04ee4668551ace23921753d5d5a644c42b5fdc31d82ae5a1e08ccd62a3681c2b"
  },
  {
    "name": "ascii-64MiB-io-materialize",
    "corpus": "ascii",
    "reps": 3195660,
    "size_bytes": 67108864,
    "mode": "materialize",
    "source": "io",
    "bytes": 67108864,
    "codepoints": 67108864,
    "suffix": "  al",
    "expected": "9586981:1707099817",
    "input_sha256": "54d2dd39cc2c4995b12d7f8efa26ef125c7e847cb38838450c62c92f3726a33c",
    "driver_sha256": "fc0c327c6e956aa99a41c92671074d1415d4b51871c30457c3c44c9be1a78bf5",
    "base_binary_sha256": "73a6dd6db0e9ea6d060307eb755a23c1c629c8f3e2c9e689b113cfb0311558ff",
    "candidate_binary_sha256": "81a1ac5c23b4817c7b33aba2c1b11992255630e4f645525e0049aabe1d066b4c"
  },
  {
    "name": "unicode-1MiB-io-scan",
    "corpus": "unicode",
    "reps": 43690,
    "size_bytes": 1048576,
    "mode": "scan",
    "source": "io",
    "bytes": 1048576,
    "codepoints": 655361,
    "suffix": "  café λ😀\n ",
    "expected": "131072:3087947764",
    "input_sha256": "bce0ae6d8db6083b7a352d8c224adb801e442f12d596565f4cac9571c6c225fc",
    "driver_sha256": "f9ef5974ac8389aab4fb9d857830a23dc2ae00544ea2798fa2772d979b9a7dfe",
    "base_binary_sha256": "dac7b503c74561d95dc997a9b7dc336aad87bcc06ce0eed6cd736f594cc32703",
    "candidate_binary_sha256": "09f71ac97c472a33421c3bfa6fb0175f39ddd51a977a282f045d0f1a1385e740"
  },
  {
    "name": "unicode-1MiB-construct-scan",
    "corpus": "unicode",
    "reps": 43690,
    "size_bytes": 1048576,
    "mode": "scan",
    "source": "construct",
    "bytes": 1048576,
    "codepoints": 655361,
    "suffix": "  café λ😀\n ",
    "expected": "131072:3087947764",
    "driver_sha256": "1c2890aaa9dccc5e1955b69b79353073ed965c32c836a47958f58bf0037123d3",
    "base_binary_sha256": "75f9c1ca08c36ee7f4f725b054484e9648151822db3054ac88d73c5cc2feb82a",
    "candidate_binary_sha256": "20f817ca37f490981470ca99f48d974cd0c63025e6435860ecf30748641c6ce2"
  },
  {
    "name": "unicode-1MiB-io-materialize",
    "corpus": "unicode",
    "reps": 43690,
    "size_bytes": 1048576,
    "mode": "materialize",
    "source": "io",
    "bytes": 1048576,
    "codepoints": 655361,
    "suffix": "  café λ😀\n ",
    "expected": "131072:3087947764",
    "input_sha256": "bce0ae6d8db6083b7a352d8c224adb801e442f12d596565f4cac9571c6c225fc",
    "driver_sha256": "10e9349bba2ebe7842553c979ccaadf9a9743eb2d1ca632b37f86a058b36ec5a",
    "base_binary_sha256": "1d1efbbf352f8276791c821d0f6fa3d6c5a6dea76663386e7c631eeff27969ca",
    "candidate_binary_sha256": "63e14f9a88024385cb12f6a470994b1b5f9d51349ca1e5ac4a4a1339b6887c23"
  },
  {
    "name": "unicode-8MiB-io-scan",
    "corpus": "unicode",
    "reps": 349525,
    "size_bytes": 8388608,
    "mode": "scan",
    "source": "io",
    "bytes": 8388608,
    "codepoints": 5242882,
    "suffix": "  café ",
    "expected": "1048576:3225742726",
    "input_sha256": "fafa0715d12636916f9bc2c2aae31f735fecaa081f1364e4aff9b2ac9e05f022",
    "driver_sha256": "901d3d1d574c29c98ecedc02f1c4a54bd98e725bec4bb02a484263798d23db75",
    "base_binary_sha256": "6826b89b1e22490375090b2658c157da777715babbbc4277f0a9093caf91fb21",
    "candidate_binary_sha256": "3ae14a7ab0c0aba8394398a076b3b8eb474cb85a6e05ba23b79e23a286cdca8d"
  },
  {
    "name": "unicode-8MiB-construct-scan",
    "corpus": "unicode",
    "reps": 349525,
    "size_bytes": 8388608,
    "mode": "scan",
    "source": "construct",
    "bytes": 8388608,
    "codepoints": 5242882,
    "suffix": "  café ",
    "expected": "1048576:3225742726",
    "driver_sha256": "f622702d455c481cec8bd26cbc6eaca4b86c3455b482b19b5347348b9b209361",
    "base_binary_sha256": "964292be2ccc1b67ffbcaac6168bb71cd3d647f78f4b8c956919a464c3a75583",
    "candidate_binary_sha256": "ab7977ed6caf2ca6e0398b61b8f169057a7a1725764313e0b74c263ad9256e51"
  },
  {
    "name": "unicode-8MiB-io-materialize",
    "corpus": "unicode",
    "reps": 349525,
    "size_bytes": 8388608,
    "mode": "materialize",
    "source": "io",
    "bytes": 8388608,
    "codepoints": 5242882,
    "suffix": "  café ",
    "expected": "1048576:3225742726",
    "input_sha256": "fafa0715d12636916f9bc2c2aae31f735fecaa081f1364e4aff9b2ac9e05f022",
    "driver_sha256": "4212087e129d3eb46b2815d13f921ab808fb7426e7367eae3d9c6629c5104075",
    "base_binary_sha256": "18044c0565c83082870c1dbbf6e98c7863f0cff9af3183f6d88d69413306f0af",
    "candidate_binary_sha256": "5150025b71ed18227486bf111645f2b8416c06d8a7d7fd30a4d259635b4051ea"
  },
  {
    "name": "unicode-64MiB-io-scan",
    "corpus": "unicode",
    "reps": 2796202,
    "size_bytes": 67108864,
    "mode": "scan",
    "source": "io",
    "bytes": 67108864,
    "codepoints": 41943041,
    "suffix": "  café λ😀\n ",
    "expected": "8388608:20207604",
    "input_sha256": "ea6e1b065b3625d4a62f6b4fb59cb3033d395f66a10dda7758ad3e8aff22f671",
    "driver_sha256": "b7fc0e568ca2775d92a263942c7bc47b251ed33a2e4b0bc8eeea57bf23fb9fde",
    "base_binary_sha256": "dc511a61ef02df5414eca1167dea2697709ad5bc060df92b31ee425b3a4b8d54",
    "candidate_binary_sha256": "cbc6aece5e5a066ba1dcd42a66edd0d495e911ac67b9147dfef4a3639331c43c"
  },
  {
    "name": "unicode-64MiB-construct-scan",
    "corpus": "unicode",
    "reps": 2796202,
    "size_bytes": 67108864,
    "mode": "scan",
    "source": "construct",
    "bytes": 67108864,
    "codepoints": 41943041,
    "suffix": "  café λ😀\n ",
    "expected": "8388608:20207604",
    "driver_sha256": "0ca573831a7166fb3a42a2f2e906d5904402ff33741939ecacd56e56e015320c",
    "base_binary_sha256": "96bfd2f5d77f63e688bf06a0f29412577b9cd2bb4e2b18385e07e7290f54a3e3",
    "candidate_binary_sha256": "74e4529a24077973cda356d1ef92c5f7012c63513fc3256d520dc1c6a3123d37"
  },
  {
    "name": "unicode-64MiB-io-materialize",
    "corpus": "unicode",
    "reps": 2796202,
    "size_bytes": 67108864,
    "mode": "materialize",
    "source": "io",
    "bytes": 67108864,
    "codepoints": 41943041,
    "suffix": "  café λ😀\n ",
    "expected": "8388608:20207604",
    "input_sha256": "ea6e1b065b3625d4a62f6b4fb59cb3033d395f66a10dda7758ad3e8aff22f671",
    "driver_sha256": "bca4ba09e6c035abb21e9e285e53a237383a868ad700eb27932e5397854b7d5e",
    "base_binary_sha256": "fa94254afc45b091b37e89aa05b37feda1dc11ffaea1d15c342c17604278b94a",
    "candidate_binary_sha256": "469fb26c09e9b26db40760705119dadf831e001e59c0dc6306962df4ae5d787c"
  },
  {
    "name": "retain-8MiB-view",
    "corpus": "ascii",
    "reps": 399457,
    "size_bytes": 8388608,
    "mode": "view",
    "source": "io",
    "bytes": 8388608,
    "codepoints": 8388608,
    "suffix": "  alpha bet",
    "expected": "3:125497",
    "input_sha256": "0b6ddf9b9444849a1ea1e867d32da4dccdfd75702427667a9dafd5fbf035ed31",
    "driver_sha256": "afa0839506adaf0bf09b32a873035d3404c24458109b742ed4ada25e4162c39e",
    "base_binary_sha256": "180f04f9c87fd2049901bbcc459d0cf048335992a9bfe46949f47d567fe2e085",
    "candidate_binary_sha256": "a117b32121bc9eb359182c1678c472e6b408e8693f431e5a8486f16401136aa7"
  },
  {
    "name": "retain-8MiB-copy",
    "corpus": "ascii",
    "reps": 399457,
    "size_bytes": 8388608,
    "mode": "copy",
    "source": "io",
    "bytes": 8388608,
    "codepoints": 8388608,
    "suffix": "  alpha bet",
    "expected": "3:125497",
    "input_sha256": "0b6ddf9b9444849a1ea1e867d32da4dccdfd75702427667a9dafd5fbf035ed31",
    "driver_sha256": "3f65066409d6cee7c42474e29563811dc0060d33798093b6b93dad988f80e57f",
    "base_binary_sha256": "b969d0fcfbd16574e90c34ae8c06b341ae39b80e409db60c736e5dd9cef8c77a",
    "candidate_binary_sha256": "1399a9f605a487e321b2dac6d55a6f4b3bb884e5ce4de9e38397bec9378ecbb0"
  },
  {
    "name": "search-32768-512",
    "corpus": "search",
    "n": 32768,
    "m": 512,
    "mode": "search",
    "source": "construct",
    "bytes": 32768,
    "expected": "1:1",
    "driver_sha256": "5f2ba9f582464d4afe63bde884a7b6cde88a73019dd2c193f19a1ce99b4dd601",
    "base_binary_sha256": "6803bdebd05a3707f2ce4306826d0e6d62a2daaa96c0fd58f2286dfb2b9c7a93",
    "candidate_binary_sha256": "0fbcdde1efe0ddf3b5715636f175bc517ba7e93bd6c02ae3eec73a5d24f1491b"
  },
  {
    "name": "search-65536-1024",
    "corpus": "search",
    "n": 65536,
    "m": 1024,
    "mode": "search",
    "source": "construct",
    "bytes": 65536,
    "expected": "1:1",
    "driver_sha256": "f7493cea78c708b5f6a6d782152d2dc51d4fb4a2aa1eb387884314fe279855ba",
    "base_binary_sha256": "c0660c9fc0bd73fb6ba53e85e63ed9d13a3f6a0191555b14d64ec39a21dcaf05",
    "candidate_binary_sha256": "1c0d6fa7bd0c05441eef9bdd5e4c5537de36bbcd82e217a4c768a0071033e553"
  },
  {
    "name": "search-131072-2048",
    "corpus": "search",
    "n": 131072,
    "m": 2048,
    "mode": "search",
    "source": "construct",
    "bytes": 131072,
    "expected": "1:1",
    "driver_sha256": "6de92c496d62596f537fd5824d8507bb3f3a6434f7048d872293674a4426d27b",
    "base_binary_sha256": "51327dcf9542cac1439f4be61dc49d8fcd41f9851b95a535c3d82ecd5bb840de",
    "candidate_binary_sha256": "10766d340bcd141e6ff51570d89f975218d3753dcca3d921b8e163dd5f7fba7b"
  },
  {
    "name": "build-concat-1024",
    "mode": "builder",
    "op": "concat",
    "n": 1024,
    "source": "construct",
    "bytes": 6144,
    "expected": "1:4141009920",
    "driver_sha256": "0d9f8b5d2fc79b33e0833d74994747fe8adc5a60ce70d79458fc1cb071b9a36d",
    "base_binary_sha256": "e214b4abb39e0b1aa6828f9154f6aaa95e8be7c15e79f35bcf05bc99ffa44b19",
    "candidate_binary_sha256": "7f80686e4a41b572effc222e38f59820a15aca3a263bb4f5f7744c9f1128c5aa"
  },
  {
    "name": "build-concat-4096",
    "mode": "builder",
    "op": "concat",
    "n": 4096,
    "source": "construct",
    "bytes": 24576,
    "expected": "1:1196109824",
    "driver_sha256": "5802874b6f457eb9d2c4e299cefe708561e984150513f08eb25c8aabdbccc9e5",
    "base_binary_sha256": "7830e746fcd519d3ca9074ce4ffcf5e7feee6ee14331b6e5fd3ca919c37b1c3e",
    "candidate_binary_sha256": "676e784bb4b50b4a998bfb954945bc08b0fcdab8ebcc86dc0f5d8ab9ef6e9b8e"
  },
  {
    "name": "build-join-1024",
    "mode": "builder",
    "op": "join",
    "n": 1024,
    "source": "construct",
    "bytes": 7167,
    "expected": "1:4151188228",
    "driver_sha256": "9a455d1ae1000202bd367e17bc4ff8d79605457c39469a28d9d3113f500e6c83",
    "base_binary_sha256": "fcf0072ee404979667ab5a642513c03bf23d8a3ea0692077fedb96c935f578e3",
    "candidate_binary_sha256": "72b704c5f49a5fdf188f8149464014a446fed7735e6cd80085271d6b3a671ea6"
  },
  {
    "name": "build-join-4096",
    "mode": "builder",
    "op": "join",
    "n": 4096,
    "source": "construct",
    "bytes": 28671,
    "expected": "1:3695447812",
    "driver_sha256": "3dde97035a584201fc8ca057fcb5450e6f6cbe6ad1bf740c078d7bf84b03877b",
    "base_binary_sha256": "c2ce1e5e420ac57b195218816203a7c3f669a63c67ddb246ef4195b99f2f1b91",
    "candidate_binary_sha256": "1f20c3ffafc5b489791311dc4ff647a0882ff35f91d12c40e491ff561a33fe61"
  },
  {
    "name": "build-repeat-1024",
    "mode": "builder",
    "op": "repeat",
    "n": 1024,
    "source": "construct",
    "bytes": 6144,
    "expected": "1:4141009920",
    "driver_sha256": "7dcfd1dbc5a2e14277c55428726f743f5109f640714409a8f37698f36b8302be",
    "base_binary_sha256": "3817dd6259fbb448888cf1b6e88b7c845dbaae3dd9b5f5e56526daca72fdf4d0",
    "candidate_binary_sha256": "5f7b5fb57debe7fbe353d868ef90003cc31668b5ba4e63b6980d14998447814b"
  },
  {
    "name": "build-repeat-4096",
    "mode": "builder",
    "op": "repeat",
    "n": 4096,
    "source": "construct",
    "bytes": 24576,
    "expected": "1:1196109824",
    "driver_sha256": "4e720f85aff50c82942841b523aa26a13c3774e8fdd19b4314aa2c4e65a7d44f",
    "base_binary_sha256": "2690aab9bbc396d8c8128c6d9fdae2acef475490b9d7e80565f3d854c2d5df9c",
    "candidate_binary_sha256": "a3bc10f7ad2412b814b3d94c1659cfca1232ed52d21f184b522be6a944ee9a01"
  },
  {
    "name": "build-append-1024",
    "mode": "builder",
    "op": "append",
    "n": 1024,
    "source": "construct",
    "bytes": 1024,
    "expected": "1:1046732800",
    "driver_sha256": "ecb63d8fe5e881e92ecf331e9d01b54b8ce80e841ff9a862bb9de6cb4889737e",
    "base_binary_sha256": "91480b54ad82652b5023e002624fb54bdb5284344f982ea67d41e7939c055986",
    "candidate_binary_sha256": "cddf697f29b5caea79ae0ed8703b9fadcb5280b924f466891885c4a1c9cda499"
  },
  {
    "name": "build-append-4096",
    "mode": "builder",
    "op": "append",
    "n": 4096,
    "source": "construct",
    "bytes": 4096,
    "expected": "1:2576318464",
    "driver_sha256": "258190606ae9c1ff13d8170ffd04312aea4303031a6e482fa206e7ea48673820",
    "base_binary_sha256": "21feb02be503e0427c7ec1823eb47b9f320f663a6fc113bdcaefbc1b3ab52995",
    "candidate_binary_sha256": "f9bd5efb76cb39e23824b80e769d22d799c068e4b05a0b26c828526d619a02e8"
  },
  {
    "name": "build-snapshots-128",
    "mode": "builder",
    "op": "snapshots",
    "n": 128,
    "source": "construct",
    "bytes": 8256,
    "expected": "129:161603072",
    "driver_sha256": "1f2a4f145d0686481cefcf49be7d303346eef4d5d551c6fad50d2c06b4fb5d89",
    "base_binary_sha256": "7b567a866c933ea2226411dd553c5b467d5faa18563d1ee646fbf40e219b3389",
    "candidate_binary_sha256": "1e06122da2c953055373d18d9e3b8fd656c02e3075106849ad49740f1d01146d"
  },
  {
    "name": "build-snapshots-512",
    "mode": "builder",
    "op": "snapshots",
    "n": 512,
    "source": "construct",
    "bytes": 131328,
    "expected": "513:725317632",
    "driver_sha256": "4e23a5b82f19632ad3c24bdc318ae1a22e6dfb83d55c831b403477ccb46b218e",
    "base_binary_sha256": "c1012992aea14ec6ad8601ccab6a16fa9a0ac3e1d50726aa8b5f723b0507811a",
    "candidate_binary_sha256": "40a06b8b91227e3abe76c0b13b22bdc8a5f12bf5bf1c982958f9b910ec36731a"
  },
  {
    "name": "map-prefix-256",
    "mode": "map",
    "prefix": 256,
    "n": 64,
    "source": "construct",
    "bytes": 16503,
    "expected": "64:2080",
    "driver_sha256": "b6dff38409cb92aab85980b9003274b760dc2fc0039ab51bc47c8da607d5a2ef",
    "base_binary_sha256": "5b316e8040cff25e0357e05315d588bc8eeef28ba2a6115c511bfc33d5e96a31",
    "candidate_binary_sha256": "b85b9920471c29f130aba55b750f939c8cd93a981911d4e8fe0e980594f57502"
  },
  {
    "name": "map-prefix-4096",
    "mode": "map",
    "prefix": 4096,
    "n": 64,
    "source": "construct",
    "bytes": 262263,
    "expected": "64:2080",
    "driver_sha256": "fa25f6980cca241f424bd8d5969e5e16cd860bc01ffc338dff70fc12de5641df",
    "base_binary_sha256": "0df0ffdb34b8b0e0d58ad389ecae44efc79ed87ce445e919dab29e544cc75b14",
    "candidate_binary_sha256": "1f3f90a340f237f09035fdd9c874795060ff37fabfe4c1168a1e06e83b4dff0e"
  }
]
```

</details>

<details><summary>All raw acceptance runs (JSON Lines)</summary>

```jsonl
{"case": "legacy-1024", "lane": "base", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "9216:3218203648", "wall_ms": 4.621265, "rss_kib": 4468, "marks": [{"phase": 0, "ns": 190860249090066}, {"phase": 1, "ns": 190860249747602}, {"phase": 2, "ns": 190860251133167}, {"phase": 3, "ns": 190860251233507}], "diagnostic": "", "acquire_ms": 0.657536, "process_ms": 1.485905, "materialize_ms": 1.385565, "consume_ms": 0.10034}
{"case": "legacy-1024", "lane": "base", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "9216:3218203648", "wall_ms": 4.137419, "rss_kib": 4272, "marks": [{"phase": 0, "ns": 190860253945084}, {"phase": 1, "ns": 190860254500627}, {"phase": 2, "ns": 190860255783748}, {"phase": 3, "ns": 190860255889418}], "diagnostic": "", "acquire_ms": 0.555543, "process_ms": 1.388791, "materialize_ms": 1.283121, "consume_ms": 0.10567}
{"case": "legacy-1024", "lane": "base", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "9216:3218203648", "wall_ms": 4.485739, "rss_kib": 4344, "marks": [{"phase": 0, "ns": 190860258352444}, {"phase": 1, "ns": 190860258910732}, {"phase": 2, "ns": 190860260313260}, {"phase": 3, "ns": 190860260469355}], "diagnostic": "", "acquire_ms": 0.558288, "process_ms": 1.558623, "materialize_ms": 1.402528, "consume_ms": 0.156095}
{"case": "legacy-1024", "lane": "base", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "9216:3218203648", "wall_ms": 4.661531, "rss_kib": 4272, "marks": [{"phase": 0, "ns": 190860263148892}, {"phase": 1, "ns": 190860263724002}, {"phase": 2, "ns": 190860265074971}, {"phase": 3, "ns": 190860265321398}], "diagnostic": "", "acquire_ms": 0.57511, "process_ms": 1.597396, "materialize_ms": 1.350969, "consume_ms": 0.246427}
{"case": "legacy-1024", "lane": "base", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "9216:3218203648", "wall_ms": 4.499155, "rss_kib": 4328, "marks": [{"phase": 0, "ns": 190860267764156}, {"phase": 1, "ns": 190860268532161}, {"phase": 2, "ns": 190860270073081}, {"phase": 3, "ns": 190860270176787}], "diagnostic": "", "acquire_ms": 0.768005, "process_ms": 1.644626, "materialize_ms": 1.54092, "consume_ms": 0.103706}
{"case": "legacy-1024", "lane": "base", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "9216:3218203648", "wall_ms": 4.948605, "rss_kib": 4216, "marks": [{"phase": 0, "ns": 190860272871623}, {"phase": 1, "ns": 190860273484875}, {"phase": 2, "ns": 190860275014954}, {"phase": 3, "ns": 190860275252464}], "diagnostic": "", "acquire_ms": 0.613252, "process_ms": 1.767589, "materialize_ms": 1.530079, "consume_ms": 0.23751}
{"case": "legacy-1024", "lane": "base", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "9216:3218203648", "wall_ms": 4.678965, "rss_kib": 4324, "marks": [{"phase": 0, "ns": 190860277732943}, {"phase": 1, "ns": 190860278366774}, {"phase": 2, "ns": 190860279925317}, {"phase": 3, "ns": 190860280075311}], "diagnostic": "", "acquire_ms": 0.633831, "process_ms": 1.708537, "materialize_ms": 1.558543, "consume_ms": 0.149994}
{"case": "legacy-1024", "lane": "base", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "9216:3218203648", "wall_ms": 3.997994, "rss_kib": 4400, "marks": [{"phase": 0, "ns": 190860282342236}, {"phase": 1, "ns": 190860282905573}, {"phase": 2, "ns": 190860284121537}, {"phase": 3, "ns": 190860284273064}], "diagnostic": "", "acquire_ms": 0.563337, "process_ms": 1.367491, "materialize_ms": 1.215964, "consume_ms": 0.151527}
{"case": "legacy-1024", "lane": "base", "kind": "js", "run": "warm", "status": 1, "correct": false, "stdout": "", "wall_ms": 20.986241, "rss_kib": 52132, "marks": [{"phase": 0, "ns": 8452154}, {"phase": 1, "ns": 9106583}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 0.654429}
{"case": "legacy-1024", "lane": "base", "kind": "js", "run": 1, "status": 1, "correct": false, "stdout": "", "wall_ms": 23.339569, "rss_kib": 52192, "marks": [{"phase": 0, "ns": 7733162}, {"phase": 1, "ns": 8397270}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 0.664108}
{"case": "legacy-1024", "lane": "base", "kind": "js", "run": 2, "status": 1, "correct": false, "stdout": "", "wall_ms": 26.005571, "rss_kib": 52068, "marks": [{"phase": 0, "ns": 8491368}, {"phase": 1, "ns": 9394820}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 0.903452}
{"case": "legacy-1024", "lane": "base", "kind": "js", "run": 3, "status": 1, "correct": false, "stdout": "", "wall_ms": 22.394789, "rss_kib": 52312, "marks": [{"phase": 0, "ns": 8847082}, {"phase": 1, "ns": 9497364}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 0.650282}
{"case": "legacy-1024", "lane": "base", "kind": "js", "run": 4, "status": 1, "correct": false, "stdout": "", "wall_ms": 24.846434, "rss_kib": 52132, "marks": [{"phase": 0, "ns": 10110426}, {"phase": 1, "ns": 10854926}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 0.7445}
{"case": "legacy-1024", "lane": "base", "kind": "js", "run": 5, "status": 1, "correct": false, "stdout": "", "wall_ms": 21.593251, "rss_kib": 51880, "marks": [{"phase": 0, "ns": 8026037}, {"phase": 1, "ns": 8703049}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 0.677012}
{"case": "legacy-1024", "lane": "base", "kind": "js", "run": 6, "status": 1, "correct": false, "stdout": "", "wall_ms": 20.678337, "rss_kib": 52392, "marks": [{"phase": 0, "ns": 7594569}, {"phase": 1, "ns": 8214353}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 0.619784}
{"case": "legacy-1024", "lane": "base", "kind": "js", "run": 7, "status": 1, "correct": false, "stdout": "", "wall_ms": 20.894767, "rss_kib": 52004, "marks": [{"phase": 0, "ns": 7681694}, {"phase": 1, "ns": 8371290}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 0.689596}
{"case": "legacy-1024", "lane": "base", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "9216:3218203648", "wall_ms": 5.042184, "rss_kib": 4324, "marks": [{"phase": 0, "ns": 190860468900554, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": null}, {"phase": 1, "ns": 190860469637781, "allocs": 90122, "frees": 9, "live": 1081360, "peak": 1081376, "copy_cells": null}, {"phase": 2, "ns": 190860471574190, "allocs": 336913, "frees": 265231, "live": 933912, "peak": 1081392, "copy_cells": null}, {"phase": 3, "ns": 190860471739203, "allocs": 336919, "frees": 336917, "live": 32, "peak": 933944, "copy_cells": null}], "diagnostic": "", "acquire_ms": 0.737227, "process_ms": 2.101422, "materialize_ms": 1.936409, "consume_ms": 0.165013}
{"case": "legacy-1024", "lane": "candidate", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "9216:3218203648", "wall_ms": 2.960029, "rss_kib": 2932, "marks": [{"phase": 0, "ns": 190861417915032}, {"phase": 1, "ns": 190861417988120}, {"phase": 2, "ns": 190861418389280}, {"phase": 3, "ns": 190861418656346}], "diagnostic": "", "acquire_ms": 0.073088, "process_ms": 0.668226, "materialize_ms": 0.40116, "consume_ms": 0.267066}
{"case": "legacy-1024", "lane": "candidate", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "9216:3218203648", "wall_ms": 2.698893, "rss_kib": 2800, "marks": [{"phase": 0, "ns": 190861420804676}, {"phase": 1, "ns": 190861420869980}, {"phase": 2, "ns": 190861421255861}, {"phase": 3, "ns": 190861421514742}], "diagnostic": "", "acquire_ms": 0.065304, "process_ms": 0.644762, "materialize_ms": 0.385881, "consume_ms": 0.258881}
{"case": "legacy-1024", "lane": "candidate", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "9216:3218203648", "wall_ms": 2.684315, "rss_kib": 2680, "marks": [{"phase": 0, "ns": 190861423656109}, {"phase": 1, "ns": 190861423727905}, {"phase": 2, "ns": 190861424116872}, {"phase": 3, "ns": 190861424374009}], "diagnostic": "", "acquire_ms": 0.071796, "process_ms": 0.646104, "materialize_ms": 0.388967, "consume_ms": 0.257137}
{"case": "legacy-1024", "lane": "candidate", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "9216:3218203648", "wall_ms": 2.815755, "rss_kib": 2788, "marks": [{"phase": 0, "ns": 190861426386271}, {"phase": 1, "ns": 190861426460502}, {"phase": 2, "ns": 190861426913069}, {"phase": 3, "ns": 190861427237965}], "diagnostic": "", "acquire_ms": 0.074231, "process_ms": 0.777463, "materialize_ms": 0.452567, "consume_ms": 0.324896}
{"case": "legacy-1024", "lane": "candidate", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "9216:3218203648", "wall_ms": 2.682683, "rss_kib": 2788, "marks": [{"phase": 0, "ns": 190861429428265}, {"phase": 1, "ns": 190861429498247}, {"phase": 2, "ns": 190861429886353}, {"phase": 3, "ns": 190861430159340}], "diagnostic": "", "acquire_ms": 0.069982, "process_ms": 0.661093, "materialize_ms": 0.388106, "consume_ms": 0.272987}
{"case": "legacy-1024", "lane": "candidate", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "9216:3218203648", "wall_ms": 2.674707, "rss_kib": 2872, "marks": [{"phase": 0, "ns": 190861432227779}, {"phase": 1, "ns": 190861432290037}, {"phase": 2, "ns": 190861432678162}, {"phase": 3, "ns": 190861432954896}], "diagnostic": "", "acquire_ms": 0.062258, "process_ms": 0.664859, "materialize_ms": 0.388125, "consume_ms": 0.276734}
{"case": "legacy-1024", "lane": "candidate", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "9216:3218203648", "wall_ms": 2.554389, "rss_kib": 2788, "marks": [{"phase": 0, "ns": 190861434908117}, {"phase": 1, "ns": 190861434977879}, {"phase": 2, "ns": 190861435392244}, {"phase": 3, "ns": 190861435643891}], "diagnostic": "", "acquire_ms": 0.069762, "process_ms": 0.666012, "materialize_ms": 0.414365, "consume_ms": 0.251647}
{"case": "legacy-1024", "lane": "candidate", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "9216:3218203648", "wall_ms": 2.561413, "rss_kib": 2924, "marks": [{"phase": 0, "ns": 190861437606289}, {"phase": 1, "ns": 190861437673066}, {"phase": 2, "ns": 190861438088453}, {"phase": 3, "ns": 190861438353956}], "diagnostic": "", "acquire_ms": 0.066777, "process_ms": 0.68089, "materialize_ms": 0.415387, "consume_ms": 0.265503}
{"case": "legacy-1024", "lane": "candidate", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "9216:3218203648", "wall_ms": 24.150215, "rss_kib": 62948, "marks": [{"phase": 0, "ns": 7852908}, {"phase": 1, "ns": 8254098}, {"phase": 2, "ns": 11429023}, {"phase": 3, "ns": 17057567}], "diagnostic": "", "acquire_ms": 0.40119, "process_ms": 8.803469, "materialize_ms": 3.174925, "consume_ms": 5.628544}
{"case": "legacy-1024", "lane": "candidate", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "9216:3218203648", "wall_ms": 24.57492, "rss_kib": 62692, "marks": [{"phase": 0, "ns": 7798836}, {"phase": 1, "ns": 8185809}, {"phase": 2, "ns": 11559421}, {"phase": 3, "ns": 17576772}], "diagnostic": "", "acquire_ms": 0.386973, "process_ms": 9.390963, "materialize_ms": 3.373612, "consume_ms": 6.017351}
{"case": "legacy-1024", "lane": "candidate", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "9216:3218203648", "wall_ms": 24.830515, "rss_kib": 62816, "marks": [{"phase": 0, "ns": 9014519}, {"phase": 1, "ns": 9397144}, {"phase": 2, "ns": 12330161}, {"phase": 3, "ns": 17637787}], "diagnostic": "", "acquire_ms": 0.382625, "process_ms": 8.240643, "materialize_ms": 2.933017, "consume_ms": 5.307626}
{"case": "legacy-1024", "lane": "candidate", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "9216:3218203648", "wall_ms": 28.715475, "rss_kib": 62552, "marks": [{"phase": 0, "ns": 7772335}, {"phase": 1, "ns": 8169037}, {"phase": 2, "ns": 11598394}, {"phase": 3, "ns": 17733107}], "diagnostic": "", "acquire_ms": 0.396702, "process_ms": 9.56407, "materialize_ms": 3.429357, "consume_ms": 6.134713}
{"case": "legacy-1024", "lane": "candidate", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "9216:3218203648", "wall_ms": 28.287895, "rss_kib": 62812, "marks": [{"phase": 0, "ns": 8544589}, {"phase": 1, "ns": 9158191}, {"phase": 2, "ns": 12085417}, {"phase": 3, "ns": 17997178}], "diagnostic": "", "acquire_ms": 0.613602, "process_ms": 8.838987, "materialize_ms": 2.927226, "consume_ms": 5.911761}
{"case": "legacy-1024", "lane": "candidate", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "9216:3218203648", "wall_ms": 26.075994, "rss_kib": 62556, "marks": [{"phase": 0, "ns": 7948400}, {"phase": 1, "ns": 8403732}, {"phase": 2, "ns": 12269005}, {"phase": 3, "ns": 18826630}], "diagnostic": "", "acquire_ms": 0.455332, "process_ms": 10.422898, "materialize_ms": 3.865273, "consume_ms": 6.557625}
{"case": "legacy-1024", "lane": "candidate", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "9216:3218203648", "wall_ms": 24.983815, "rss_kib": 62696, "marks": [{"phase": 0, "ns": 7821209}, {"phase": 1, "ns": 8167274}, {"phase": 2, "ns": 11136831}, {"phase": 3, "ns": 17542818}], "diagnostic": "", "acquire_ms": 0.346065, "process_ms": 9.375544, "materialize_ms": 2.969557, "consume_ms": 6.405987}
{"case": "legacy-1024", "lane": "candidate", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "9216:3218203648", "wall_ms": 26.126911, "rss_kib": 62708, "marks": [{"phase": 0, "ns": 8307149}, {"phase": 1, "ns": 8694774}, {"phase": 2, "ns": 11617541}, {"phase": 3, "ns": 17871771}], "diagnostic": "", "acquire_ms": 0.387625, "process_ms": 9.176997, "materialize_ms": 2.922767, "consume_ms": 6.25423}
{"case": "legacy-1024", "lane": "candidate", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "9216:3218203648", "wall_ms": 2.867092, "rss_kib": 2868, "marks": [{"phase": 0, "ns": 190861649764269, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": 0}, {"phase": 1, "ns": 190861649831086, "allocs": 15, "frees": 9, "live": 262200, "peak": 262216, "copy_cells": 45056}, {"phase": 2, "ns": 190861650266090, "allocs": 60437, "frees": 23570, "live": 704536, "peak": 704552, "copy_cells": 45056}, {"phase": 3, "ns": 190861650620541, "allocs": 113691, "frees": 113689, "live": 32, "peak": 704568, "copy_cells": 45056}], "diagnostic": "", "acquire_ms": 0.066817, "process_ms": 0.789455, "materialize_ms": 0.435004, "consume_ms": 0.354451}
{"case": "legacy-4096", "lane": "base", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "36864:4282880000", "wall_ms": 11.729002, "rss_kib": 10612, "marks": [{"phase": 0, "ns": 190862697292102}, {"phase": 1, "ns": 190862699804362}, {"phase": 2, "ns": 190862705332105}, {"phase": 3, "ns": 190862706405308}], "diagnostic": "", "acquire_ms": 2.51226, "process_ms": 6.600946, "materialize_ms": 5.527743, "consume_ms": 1.073203}
{"case": "legacy-4096", "lane": "base", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "36864:4282880000", "wall_ms": 11.12582, "rss_kib": 10732, "marks": [{"phase": 0, "ns": 190862709149497}, {"phase": 1, "ns": 190862711528715}, {"phase": 2, "ns": 190862716700504}, {"phase": 3, "ns": 190862717748439}], "diagnostic": "", "acquire_ms": 2.379218, "process_ms": 6.219724, "materialize_ms": 5.171789, "consume_ms": 1.047935}
{"case": "legacy-4096", "lane": "base", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "36864:4282880000", "wall_ms": 12.38197, "rss_kib": 10740, "marks": [{"phase": 0, "ns": 190862720668762}, {"phase": 1, "ns": 190862723246977}, {"phase": 2, "ns": 190862729073205}, {"phase": 3, "ns": 190862730279902}], "diagnostic": "", "acquire_ms": 2.578215, "process_ms": 7.032925, "materialize_ms": 5.826228, "consume_ms": 1.206697}
{"case": "legacy-4096", "lane": "base", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "36864:4282880000", "wall_ms": 11.776251, "rss_kib": 10600, "marks": [{"phase": 0, "ns": 190862733477991}, {"phase": 1, "ns": 190862735771717}, {"phase": 2, "ns": 190862740948865}, {"phase": 3, "ns": 190862742157726}], "diagnostic": "", "acquire_ms": 2.293726, "process_ms": 6.386009, "materialize_ms": 5.177148, "consume_ms": 1.208861}
{"case": "legacy-4096", "lane": "base", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "36864:4282880000", "wall_ms": 11.790458, "rss_kib": 10540, "marks": [{"phase": 0, "ns": 190862744903618}, {"phase": 1, "ns": 190862747283297}, {"phase": 2, "ns": 190862752817542}, {"phase": 3, "ns": 190862754124588}], "diagnostic": "", "acquire_ms": 2.379679, "process_ms": 6.841291, "materialize_ms": 5.534245, "consume_ms": 1.307046}
{"case": "legacy-4096", "lane": "base", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "36864:4282880000", "wall_ms": 11.203877, "rss_kib": 10608, "marks": [{"phase": 0, "ns": 190862756951655}, {"phase": 1, "ns": 190862759295886}, {"phase": 2, "ns": 190862764738317}, {"phase": 3, "ns": 190862765576155}], "diagnostic": "", "acquire_ms": 2.344231, "process_ms": 6.280269, "materialize_ms": 5.442431, "consume_ms": 0.837838}
{"case": "legacy-4096", "lane": "base", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "36864:4282880000", "wall_ms": 12.947841, "rss_kib": 10608, "marks": [{"phase": 0, "ns": 190862768444790}, {"phase": 1, "ns": 190862771231770}, {"phase": 2, "ns": 190862777647946}, {"phase": 3, "ns": 190862778653582}], "diagnostic": "", "acquire_ms": 2.78698, "process_ms": 7.421812, "materialize_ms": 6.416176, "consume_ms": 1.005636}
{"case": "legacy-4096", "lane": "base", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "36864:4282880000", "wall_ms": 10.944746, "rss_kib": 10488, "marks": [{"phase": 0, "ns": 190862781558646}, {"phase": 1, "ns": 190862783817185}, {"phase": 2, "ns": 190862788855961}, {"phase": 3, "ns": 190862789841579}], "diagnostic": "", "acquire_ms": 2.258539, "process_ms": 6.024394, "materialize_ms": 5.038776, "consume_ms": 0.985618}
{"case": "legacy-4096", "lane": "base", "kind": "js", "run": "warm", "status": 1, "correct": false, "stdout": "", "wall_ms": 22.214929, "rss_kib": 52876, "marks": [{"phase": 0, "ns": 8430633}, {"phase": 1, "ns": 9778096}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 1.347463}
{"case": "legacy-4096", "lane": "base", "kind": "js", "run": 1, "status": 1, "correct": false, "stdout": "", "wall_ms": 22.007015, "rss_kib": 52824, "marks": [{"phase": 0, "ns": 8032268}, {"phase": 1, "ns": 9382225}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 1.349957}
{"case": "legacy-4096", "lane": "base", "kind": "js", "run": 2, "status": 1, "correct": false, "stdout": "", "wall_ms": 21.047738, "rss_kib": 52900, "marks": [{"phase": 0, "ns": 7850533}, {"phase": 1, "ns": 9043554}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 1.193021}
{"case": "legacy-4096", "lane": "base", "kind": "js", "run": 3, "status": 1, "correct": false, "stdout": "", "wall_ms": 23.628397, "rss_kib": 52764, "marks": [{"phase": 0, "ns": 10170289}, {"phase": 1, "ns": 11412201}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 1.241912}
{"case": "legacy-4096", "lane": "base", "kind": "js", "run": 4, "status": 1, "correct": false, "stdout": "", "wall_ms": 26.009648, "rss_kib": 52444, "marks": [{"phase": 0, "ns": 8377392}, {"phase": 1, "ns": 9852176}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 1.474784}
{"case": "legacy-4096", "lane": "base", "kind": "js", "run": 5, "status": 1, "correct": false, "stdout": "", "wall_ms": 22.127584, "rss_kib": 52900, "marks": [{"phase": 0, "ns": 7849111}, {"phase": 1, "ns": 9094540}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 1.245429}
{"case": "legacy-4096", "lane": "base", "kind": "js", "run": 6, "status": 1, "correct": false, "stdout": "", "wall_ms": 23.412558, "rss_kib": 52964, "marks": [{"phase": 0, "ns": 7795790}, {"phase": 1, "ns": 9120911}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 1.325121}
{"case": "legacy-4096", "lane": "base", "kind": "js", "run": 7, "status": 1, "correct": false, "stdout": "", "wall_ms": 24.576173, "rss_kib": 52388, "marks": [{"phase": 0, "ns": 7973166}, {"phase": 1, "ns": 9297115}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 1.323949}
{"case": "legacy-4096", "lane": "base", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "36864:4282880000", "wall_ms": 15.772733, "rss_kib": 10616, "marks": [{"phase": 0, "ns": 190862979231331, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": null}, {"phase": 1, "ns": 190862982284646, "allocs": 360458, "frees": 9, "live": 4325392, "peak": 4325408, "copy_cells": null}, {"phase": 2, "ns": 190862990635779, "allocs": 1347601, "frees": 1060879, "live": 3735576, "peak": 4325424, "copy_cells": null}, {"phase": 3, "ns": 190862992183441, "allocs": 1347607, "frees": 1347605, "live": 32, "peak": 3735608, "copy_cells": null}], "diagnostic": "", "acquire_ms": 3.053315, "process_ms": 9.898795, "materialize_ms": 8.351133, "consume_ms": 1.547662}
{"case": "legacy-4096", "lane": "candidate", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "36864:4282880000", "wall_ms": 5.296555, "rss_kib": 4600, "marks": [{"phase": 0, "ns": 190864039282201}, {"phase": 1, "ns": 190864039524520}, {"phase": 2, "ns": 190864041201607}, {"phase": 3, "ns": 190864042263289}], "diagnostic": "", "acquire_ms": 0.242319, "process_ms": 2.738769, "materialize_ms": 1.677087, "consume_ms": 1.061682}
{"case": "legacy-4096", "lane": "candidate", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "36864:4282880000", "wall_ms": 5.088471, "rss_kib": 4656, "marks": [{"phase": 0, "ns": 190864044713351}, {"phase": 1, "ns": 190864044954357}, {"phase": 2, "ns": 190864046517309}, {"phase": 3, "ns": 190864047561056}], "diagnostic": "", "acquire_ms": 0.241006, "process_ms": 2.606699, "materialize_ms": 1.562952, "consume_ms": 1.043747}
{"case": "legacy-4096", "lane": "candidate", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "36864:4282880000", "wall_ms": 5.034348, "rss_kib": 4712, "marks": [{"phase": 0, "ns": 190864049882895}, {"phase": 1, "ns": 190864050122930}, {"phase": 2, "ns": 190864051721178}, {"phase": 3, "ns": 190864052790163}], "diagnostic": "", "acquire_ms": 0.240035, "process_ms": 2.667233, "materialize_ms": 1.598248, "consume_ms": 1.068985}
{"case": "legacy-4096", "lane": "candidate", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "36864:4282880000", "wall_ms": 5.200282, "rss_kib": 4844, "marks": [{"phase": 0, "ns": 190864054991103}, {"phase": 1, "ns": 190864055243511}, {"phase": 2, "ns": 190864057063680}, {"phase": 3, "ns": 190864058099382}], "diagnostic": "", "acquire_ms": 0.252408, "process_ms": 2.855871, "materialize_ms": 1.820169, "consume_ms": 1.035702}
{"case": "legacy-4096", "lane": "candidate", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "36864:4282880000", "wall_ms": 5.367199, "rss_kib": 4852, "marks": [{"phase": 0, "ns": 190864060459664}, {"phase": 1, "ns": 190864060708866}, {"phase": 2, "ns": 190864062454343}, {"phase": 3, "ns": 190864063599984}], "diagnostic": "", "acquire_ms": 0.249202, "process_ms": 2.891118, "materialize_ms": 1.745477, "consume_ms": 1.145641}
{"case": "legacy-4096", "lane": "candidate", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "36864:4282880000", "wall_ms": 4.983462, "rss_kib": 4716, "marks": [{"phase": 0, "ns": 190864065913397}, {"phase": 1, "ns": 190864066162218}, {"phase": 2, "ns": 190864067727153}, {"phase": 3, "ns": 190864068791189}], "diagnostic": "", "acquire_ms": 0.248821, "process_ms": 2.628971, "materialize_ms": 1.564935, "consume_ms": 1.064036}
{"case": "legacy-4096", "lane": "candidate", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "36864:4282880000", "wall_ms": 5.065477, "rss_kib": 4656, "marks": [{"phase": 0, "ns": 190864071176769}, {"phase": 1, "ns": 190864071417325}, {"phase": 2, "ns": 190864073045910}, {"phase": 3, "ns": 190864074062847}], "diagnostic": "", "acquire_ms": 0.240556, "process_ms": 2.645522, "materialize_ms": 1.628585, "consume_ms": 1.016937}
{"case": "legacy-4096", "lane": "candidate", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "36864:4282880000", "wall_ms": 5.138646, "rss_kib": 4600, "marks": [{"phase": 0, "ns": 190864076260911}, {"phase": 1, "ns": 190864076508821}, {"phase": 2, "ns": 190864078193082}, {"phase": 3, "ns": 190864079235467}], "diagnostic": "", "acquire_ms": 0.24791, "process_ms": 2.726646, "materialize_ms": 1.684261, "consume_ms": 1.042385}
{"case": "legacy-4096", "lane": "candidate", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "36864:4282880000", "wall_ms": 56.202021, "rss_kib": 89824, "marks": [{"phase": 0, "ns": 8787820}, {"phase": 1, "ns": 9279341}, {"phase": 2, "ns": 18297427}, {"phase": 3, "ns": 41264962}], "diagnostic": "", "acquire_ms": 0.491521, "process_ms": 31.985621, "materialize_ms": 9.018086, "consume_ms": 22.967535}
{"case": "legacy-4096", "lane": "candidate", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "36864:4282880000", "wall_ms": 50.704156, "rss_kib": 89884, "marks": [{"phase": 0, "ns": 8742814}, {"phase": 1, "ns": 9138985}, {"phase": 2, "ns": 17146716}, {"phase": 3, "ns": 38059268}], "diagnostic": "", "acquire_ms": 0.396171, "process_ms": 28.920283, "materialize_ms": 8.007731, "consume_ms": 20.912552}
{"case": "legacy-4096", "lane": "candidate", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "36864:4282880000", "wall_ms": 49.540611, "rss_kib": 90200, "marks": [{"phase": 0, "ns": 8058047}, {"phase": 1, "ns": 8425934}, {"phase": 2, "ns": 16041884}, {"phase": 3, "ns": 36899872}], "diagnostic": "", "acquire_ms": 0.367887, "process_ms": 28.473938, "materialize_ms": 7.61595, "consume_ms": 20.857988}
{"case": "legacy-4096", "lane": "candidate", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "36864:4282880000", "wall_ms": 49.297971, "rss_kib": 90464, "marks": [{"phase": 0, "ns": 8235704}, {"phase": 1, "ns": 8606697}, {"phase": 2, "ns": 16144528}, {"phase": 3, "ns": 36383874}], "diagnostic": "", "acquire_ms": 0.370993, "process_ms": 27.777177, "materialize_ms": 7.537831, "consume_ms": 20.239346}
{"case": "legacy-4096", "lane": "candidate", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "36864:4282880000", "wall_ms": 50.202645, "rss_kib": 89892, "marks": [{"phase": 0, "ns": 8423991}, {"phase": 1, "ns": 8809741}, {"phase": 2, "ns": 16438204}, {"phase": 3, "ns": 36665928}], "diagnostic": "", "acquire_ms": 0.38575, "process_ms": 27.856187, "materialize_ms": 7.628463, "consume_ms": 20.227724}
{"case": "legacy-4096", "lane": "candidate", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "36864:4282880000", "wall_ms": 46.651898, "rss_kib": 90200, "marks": [{"phase": 0, "ns": 7908263}, {"phase": 1, "ns": 8337066}, {"phase": 2, "ns": 15933678}, {"phase": 3, "ns": 35504097}], "diagnostic": "", "acquire_ms": 0.428803, "process_ms": 27.167031, "materialize_ms": 7.596612, "consume_ms": 19.570419}
{"case": "legacy-4096", "lane": "candidate", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "36864:4282880000", "wall_ms": 48.657768, "rss_kib": 90340, "marks": [{"phase": 0, "ns": 7753861}, {"phase": 1, "ns": 8145012}, {"phase": 2, "ns": 15715165}, {"phase": 3, "ns": 36493281}], "diagnostic": "", "acquire_ms": 0.391151, "process_ms": 28.348269, "materialize_ms": 7.570153, "consume_ms": 20.778116}
{"case": "legacy-4096", "lane": "candidate", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "36864:4282880000", "wall_ms": 46.318566, "rss_kib": 90280, "marks": [{"phase": 0, "ns": 7892323}, {"phase": 1, "ns": 8259328}, {"phase": 2, "ns": 15556263}, {"phase": 3, "ns": 35107065}], "diagnostic": "", "acquire_ms": 0.367005, "process_ms": 26.847737, "materialize_ms": 7.296935, "consume_ms": 19.550802}
{"case": "legacy-4096", "lane": "candidate", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "36864:4282880000", "wall_ms": 5.436591, "rss_kib": 4472, "marks": [{"phase": 0, "ns": 190864480774614, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": 0}, {"phase": 1, "ns": 190864481084821, "allocs": 15, "frees": 9, "live": 1048632, "peak": 1048648, "copy_cells": 180224}, {"phase": 2, "ns": 190864482807545, "allocs": 241685, "frees": 94226, "live": 2818072, "peak": 2818088, "copy_cells": 180224}, {"phase": 3, "ns": 190864484055099, "allocs": 454683, "frees": 454681, "live": 32, "peak": 2818104, "copy_cells": 180224}], "diagnostic": "", "acquire_ms": 0.310207, "process_ms": 2.970278, "materialize_ms": 1.722724, "consume_ms": 1.247554}
{"case": "ascii-1MiB-io-scan", "lane": "base", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 27.799058, "rss_kib": 19572, "marks": [{"phase": 0, "ns": 190865732576820}, {"phase": 1, "ns": 190865740219750}, {"phase": 3, "ns": 190865757238404}], "diagnostic": "", "acquire_ms": 7.64293, "process_ms": 17.018654}
{"case": "ascii-1MiB-io-scan", "lane": "base", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 28.397022, "rss_kib": 19428, "marks": [{"phase": 0, "ns": 190865760576188}, {"phase": 1, "ns": 190865769118162}, {"phase": 3, "ns": 190865785731077}], "diagnostic": "", "acquire_ms": 8.541974, "process_ms": 16.612915}
{"case": "ascii-1MiB-io-scan", "lane": "base", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 27.982095, "rss_kib": 19440, "marks": [{"phase": 0, "ns": 190865789075404}, {"phase": 1, "ns": 190865796855163}, {"phase": 3, "ns": 190865813857687}], "diagnostic": "", "acquire_ms": 7.779759, "process_ms": 17.002524}
{"case": "ascii-1MiB-io-scan", "lane": "base", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 28.953326, "rss_kib": 19632, "marks": [{"phase": 0, "ns": 190865817209427}, {"phase": 1, "ns": 190865824907101}, {"phase": 3, "ns": 190865842669033}], "diagnostic": "", "acquire_ms": 7.697674, "process_ms": 17.761932}
{"case": "ascii-1MiB-io-scan", "lane": "base", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 28.437268, "rss_kib": 19704, "marks": [{"phase": 0, "ns": 190865846486316}, {"phase": 1, "ns": 190865854537981}, {"phase": 3, "ns": 190865871671903}], "diagnostic": "", "acquire_ms": 8.051665, "process_ms": 17.133922}
{"case": "ascii-1MiB-io-scan", "lane": "base", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 27.531672, "rss_kib": 19640, "marks": [{"phase": 0, "ns": 190865874996512}, {"phase": 1, "ns": 190865882921787}, {"phase": 3, "ns": 190865899501430}], "diagnostic": "", "acquire_ms": 7.925275, "process_ms": 16.579643}
{"case": "ascii-1MiB-io-scan", "lane": "base", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 27.844375, "rss_kib": 19640, "marks": [{"phase": 0, "ns": 190865902759973}, {"phase": 1, "ns": 190865910748408}, {"phase": 3, "ns": 190865927534522}], "diagnostic": "", "acquire_ms": 7.988435, "process_ms": 16.786114}
{"case": "ascii-1MiB-io-scan", "lane": "base", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 29.20398, "rss_kib": 19512, "marks": [{"phase": 0, "ns": 190865930921799}, {"phase": 1, "ns": 190865939537703}, {"phase": 3, "ns": 190865956898215}], "diagnostic": "", "acquire_ms": 8.615904, "process_ms": 17.360512}
{"case": "ascii-1MiB-io-scan", "lane": "base", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 929.501437, "rss_kib": 186828, "marks": [{"phase": 0, "ns": 9326710}, {"phase": 1, "ns": 21633547}, {"phase": 3, "ns": 913072330}], "diagnostic": "", "acquire_ms": 12.306837, "process_ms": 891.438783}
{"case": "ascii-1MiB-io-scan", "lane": "base", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 936.99279, "rss_kib": 188812, "marks": [{"phase": 0, "ns": 9265766}, {"phase": 1, "ns": 20074264}, {"phase": 3, "ns": 920566449}], "diagnostic": "", "acquire_ms": 10.808498, "process_ms": 900.492185}
{"case": "ascii-1MiB-io-scan", "lane": "base", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 911.848852, "rss_kib": 188824, "marks": [{"phase": 0, "ns": 8804572}, {"phase": 1, "ns": 19580228}, {"phase": 3, "ns": 897083558}], "diagnostic": "", "acquire_ms": 10.775656, "process_ms": 877.50333}
{"case": "ascii-1MiB-io-scan", "lane": "base", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 917.205341, "rss_kib": 186444, "marks": [{"phase": 0, "ns": 8718628}, {"phase": 1, "ns": 21751210}, {"phase": 3, "ns": 899036928}], "diagnostic": "", "acquire_ms": 13.032582, "process_ms": 877.285718}
{"case": "ascii-1MiB-io-scan", "lane": "base", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 924.164416, "rss_kib": 187216, "marks": [{"phase": 0, "ns": 9004070}, {"phase": 1, "ns": 19181883}, {"phase": 3, "ns": 909119431}], "diagnostic": "", "acquire_ms": 10.177813, "process_ms": 889.937548}
{"case": "ascii-1MiB-io-scan", "lane": "base", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 932.737848, "rss_kib": 186144, "marks": [{"phase": 0, "ns": 8672321}, {"phase": 1, "ns": 19662583}, {"phase": 3, "ns": 916768473}], "diagnostic": "", "acquire_ms": 10.990262, "process_ms": 897.10589}
{"case": "ascii-1MiB-io-scan", "lane": "base", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 929.642114, "rss_kib": 187840, "marks": [{"phase": 0, "ns": 8748415}, {"phase": 1, "ns": 19830341}, {"phase": 3, "ns": 914635902}], "diagnostic": "", "acquire_ms": 11.081926, "process_ms": 894.805561}
{"case": "ascii-1MiB-io-scan", "lane": "base", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 917.305942, "rss_kib": 185964, "marks": [{"phase": 0, "ns": 8298232}, {"phase": 1, "ns": 20267649}, {"phase": 3, "ns": 900659502}], "diagnostic": "", "acquire_ms": 11.969417, "process_ms": 880.391853}
{"case": "ascii-1MiB-io-scan", "lane": "base", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 41.484708, "rss_kib": 19692, "marks": [{"phase": 0, "ns": 190873361488571, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": null}, {"phase": 1, "ns": 190873369232342, "allocs": 1048612, "frees": 34, "live": 16777240, "peak": 16777288, "copy_cells": null}, {"phase": 3, "ns": 190873399117985, "allocs": 3545425, "frees": 3545423, "live": 32, "peak": 16863232, "copy_cells": null}], "diagnostic": "", "acquire_ms": 7.743771, "process_ms": 29.885643}
{"case": "ascii-1MiB-io-scan", "lane": "candidate", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 18.952588, "rss_kib": 7336, "marks": [{"phase": 0, "ns": 190874547050226}, {"phase": 1, "ns": 190874549948217}, {"phase": 3, "ns": 190874563313098}], "diagnostic": "", "acquire_ms": 2.897991, "process_ms": 13.364881}
{"case": "ascii-1MiB-io-scan", "lane": "candidate", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 18.978898, "rss_kib": 7288, "marks": [{"phase": 0, "ns": 190874566179218}, {"phase": 1, "ns": 190874568884354}, {"phase": 3, "ns": 190874582462269}], "diagnostic": "", "acquire_ms": 2.705136, "process_ms": 13.577915}
{"case": "ascii-1MiB-io-scan", "lane": "candidate", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 20.191546, "rss_kib": 7288, "marks": [{"phase": 0, "ns": 190874585323820}, {"phase": 1, "ns": 190874588280282}, {"phase": 3, "ns": 190874603046859}], "diagnostic": "", "acquire_ms": 2.956462, "process_ms": 14.766577}
{"case": "ascii-1MiB-io-scan", "lane": "candidate", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 21.036326, "rss_kib": 7216, "marks": [{"phase": 0, "ns": 190874605640503}, {"phase": 1, "ns": 190874608527242}, {"phase": 3, "ns": 190874624171041}], "diagnostic": "", "acquire_ms": 2.886739, "process_ms": 15.643799}
{"case": "ascii-1MiB-io-scan", "lane": "candidate", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 19.450281, "rss_kib": 7288, "marks": [{"phase": 0, "ns": 190874626971397}, {"phase": 1, "ns": 190874630114432}, {"phase": 3, "ns": 190874643921801}], "diagnostic": "", "acquire_ms": 3.143035, "process_ms": 13.807369}
{"case": "ascii-1MiB-io-scan", "lane": "candidate", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 19.438078, "rss_kib": 7416, "marks": [{"phase": 0, "ns": 190874646682151}, {"phase": 1, "ns": 190874650090058}, {"phase": 3, "ns": 190874663532086}], "diagnostic": "", "acquire_ms": 3.407907, "process_ms": 13.442028}
{"case": "ascii-1MiB-io-scan", "lane": "candidate", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 19.786558, "rss_kib": 7280, "marks": [{"phase": 0, "ns": 190874666123646}, {"phase": 1, "ns": 190874669779532}, {"phase": 3, "ns": 190874683448780}], "diagnostic": "", "acquire_ms": 3.655886, "process_ms": 13.669248}
{"case": "ascii-1MiB-io-scan", "lane": "candidate", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 20.198528, "rss_kib": 7344, "marks": [{"phase": 0, "ns": 190874686123368}, {"phase": 1, "ns": 190874689026037}, {"phase": 3, "ns": 190874703821018}], "diagnostic": "", "acquire_ms": 2.902669, "process_ms": 14.794981}
{"case": "ascii-1MiB-io-scan", "lane": "candidate", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 199.292615, "rss_kib": 138060, "marks": [{"phase": 0, "ns": 8339981}, {"phase": 1, "ns": 61419266}, {"phase": 3, "ns": 187172892}], "diagnostic": "", "acquire_ms": 53.079285, "process_ms": 125.753626}
{"case": "ascii-1MiB-io-scan", "lane": "candidate", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 204.960143, "rss_kib": 137432, "marks": [{"phase": 0, "ns": 8278735}, {"phase": 1, "ns": 58944307}, {"phase": 3, "ns": 190513501}], "diagnostic": "", "acquire_ms": 50.665572, "process_ms": 131.569194}
{"case": "ascii-1MiB-io-scan", "lane": "candidate", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 199.641165, "rss_kib": 138192, "marks": [{"phase": 0, "ns": 8770487}, {"phase": 1, "ns": 58895786}, {"phase": 3, "ns": 186676011}], "diagnostic": "", "acquire_ms": 50.125299, "process_ms": 127.780225}
{"case": "ascii-1MiB-io-scan", "lane": "candidate", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 205.95616, "rss_kib": 138000, "marks": [{"phase": 0, "ns": 8200477}, {"phase": 1, "ns": 60176261}, {"phase": 3, "ns": 192991436}], "diagnostic": "", "acquire_ms": 51.975784, "process_ms": 132.815175}
{"case": "ascii-1MiB-io-scan", "lane": "candidate", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 206.578018, "rss_kib": 137224, "marks": [{"phase": 0, "ns": 9059124}, {"phase": 1, "ns": 62247696}, {"phase": 3, "ns": 194126367}], "diagnostic": "", "acquire_ms": 53.188572, "process_ms": 131.878671}
{"case": "ascii-1MiB-io-scan", "lane": "candidate", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 206.65803, "rss_kib": 137924, "marks": [{"phase": 0, "ns": 9264192}, {"phase": 1, "ns": 62933926}, {"phase": 3, "ns": 192837755}], "diagnostic": "", "acquire_ms": 53.669734, "process_ms": 129.903829}
{"case": "ascii-1MiB-io-scan", "lane": "candidate", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 197.502193, "rss_kib": 137928, "marks": [{"phase": 0, "ns": 8617908}, {"phase": 1, "ns": 61066639}, {"phase": 3, "ns": 186192055}], "diagnostic": "", "acquire_ms": 52.448731, "process_ms": 125.125416}
{"case": "ascii-1MiB-io-scan", "lane": "candidate", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 207.012421, "rss_kib": 136568, "marks": [{"phase": 0, "ns": 8827124}, {"phase": 1, "ns": 59293499}, {"phase": 3, "ns": 194134733}], "diagnostic": "", "acquire_ms": 50.466375, "process_ms": 134.841234}
{"case": "ascii-1MiB-io-scan", "lane": "candidate", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 22.023617, "rss_kib": 7084, "marks": [{"phase": 0, "ns": 190876335550004, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": 0}, {"phase": 1, "ns": 190876338341703, "allocs": 40, "frees": 34, "live": 4194360, "peak": 4194408, "copy_cells": 0}, {"phase": 3, "ns": 190876354792992, "allocs": 2497439, "frees": 2497437, "live": 32, "peak": 4231232, "copy_cells": 0}], "diagnostic": "", "acquire_ms": 2.791699, "process_ms": 16.451289}
{"case": "ascii-1MiB-construct-scan", "lane": "base", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 65.985297, "rss_kib": 43240, "marks": [{"phase": 0, "ns": 190877502423913}, {"phase": 1, "ns": 190877530230175}, {"phase": 3, "ns": 190877563723442}], "diagnostic": "", "acquire_ms": 27.806262, "process_ms": 33.493267}
{"case": "ascii-1MiB-construct-scan", "lane": "base", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 66.736551, "rss_kib": 43256, "marks": [{"phase": 0, "ns": 190877568144899}, {"phase": 1, "ns": 190877595941363}, {"phase": 3, "ns": 190877630632119}], "diagnostic": "", "acquire_ms": 27.796464, "process_ms": 34.690756}
{"case": "ascii-1MiB-construct-scan", "lane": "base", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 65.795288, "rss_kib": 43176, "marks": [{"phase": 0, "ns": 190877635423006}, {"phase": 1, "ns": 190877662272636}, {"phase": 3, "ns": 190877696656621}], "diagnostic": "", "acquire_ms": 26.84963, "process_ms": 34.383985}
{"case": "ascii-1MiB-construct-scan", "lane": "base", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 62.913197, "rss_kib": 43128, "marks": [{"phase": 0, "ns": 190877701171255}, {"phase": 1, "ns": 190877726405975}, {"phase": 3, "ns": 190877759755530}], "diagnostic": "", "acquire_ms": 25.23472, "process_ms": 33.349555}
{"case": "ascii-1MiB-construct-scan", "lane": "base", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 63.407794, "rss_kib": 43372, "marks": [{"phase": 0, "ns": 190877764231079}, {"phase": 1, "ns": 190877790213636}, {"phase": 3, "ns": 190877823374684}], "diagnostic": "", "acquire_ms": 25.982557, "process_ms": 33.161048}
{"case": "ascii-1MiB-construct-scan", "lane": "base", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 63.394108, "rss_kib": 43308, "marks": [{"phase": 0, "ns": 190877828121738}, {"phase": 1, "ns": 190877853556638}, {"phase": 3, "ns": 190877886675526}], "diagnostic": "", "acquire_ms": 25.4349, "process_ms": 33.118888}
{"case": "ascii-1MiB-construct-scan", "lane": "base", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 66.485244, "rss_kib": 43128, "marks": [{"phase": 0, "ns": 190877891672483}, {"phase": 1, "ns": 190877918260447}, {"phase": 3, "ns": 190877953442173}], "diagnostic": "", "acquire_ms": 26.587964, "process_ms": 35.181726}
{"case": "ascii-1MiB-construct-scan", "lane": "base", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 64.860216, "rss_kib": 43380, "marks": [{"phase": 0, "ns": 190877958271884}, {"phase": 1, "ns": 190877985123778}, {"phase": 3, "ns": 190878018789422}], "diagnostic": "", "acquire_ms": 26.851894, "process_ms": 33.665644}
{"case": "ascii-1MiB-construct-scan", "lane": "base", "kind": "js", "run": "warm", "status": 1, "correct": false, "stdout": "", "wall_ms": 21.210496, "rss_kib": 51228, "marks": [{"phase": 0, "ns": 7922540}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "ascii-1MiB-construct-scan", "lane": "base", "kind": "js", "run": 1, "status": 1, "correct": false, "stdout": "", "wall_ms": 21.899171, "rss_kib": 51040, "marks": [{"phase": 0, "ns": 8529501}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "ascii-1MiB-construct-scan", "lane": "base", "kind": "js", "run": 2, "status": 1, "correct": false, "stdout": "", "wall_ms": 21.46612, "rss_kib": 51168, "marks": [{"phase": 0, "ns": 9137593}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "ascii-1MiB-construct-scan", "lane": "base", "kind": "js", "run": 3, "status": 1, "correct": false, "stdout": "", "wall_ms": 21.631403, "rss_kib": 51740, "marks": [{"phase": 0, "ns": 8744528}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "ascii-1MiB-construct-scan", "lane": "base", "kind": "js", "run": 4, "status": 1, "correct": false, "stdout": "", "wall_ms": 20.464483, "rss_kib": 51220, "marks": [{"phase": 0, "ns": 8040784}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "ascii-1MiB-construct-scan", "lane": "base", "kind": "js", "run": 5, "status": 1, "correct": false, "stdout": "", "wall_ms": 23.245071, "rss_kib": 51364, "marks": [{"phase": 0, "ns": 9584009}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "ascii-1MiB-construct-scan", "lane": "base", "kind": "js", "run": 6, "status": 1, "correct": false, "stdout": "", "wall_ms": 22.039397, "rss_kib": 51360, "marks": [{"phase": 0, "ns": 8368214}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "ascii-1MiB-construct-scan", "lane": "base", "kind": "js", "run": 7, "status": 1, "correct": false, "stdout": "", "wall_ms": 21.84098, "rss_kib": 51220, "marks": [{"phase": 0, "ns": 7990729}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "ascii-1MiB-construct-scan", "lane": "base", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 83.164416, "rss_kib": 42980, "marks": [{"phase": 0, "ns": 190878198624913, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": null}, {"phase": 1, "ns": 190878228901355, "allocs": 4194298, "frees": 2097152, "live": 25165752, "peak": 25165768, "copy_cells": null}, {"phase": 3, "ns": 190878277527504, "allocs": 11035010, "frees": 11035008, "live": 32, "peak": 25294744, "copy_cells": null}], "diagnostic": "", "acquire_ms": 30.276442, "process_ms": 48.626149}
{"case": "ascii-1MiB-construct-scan", "lane": "candidate", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 18.095574, "rss_kib": 6244, "marks": [{"phase": 0, "ns": 190879325688687}, {"phase": 1, "ns": 190879327365714}, {"phase": 3, "ns": 190879341321164}], "diagnostic": "", "acquire_ms": 1.677027, "process_ms": 13.95545}
{"case": "ascii-1MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 17.333471, "rss_kib": 6192, "marks": [{"phase": 0, "ns": 190879343956337}, {"phase": 1, "ns": 190879345625409}, {"phase": 3, "ns": 190879358937521}], "diagnostic": "", "acquire_ms": 1.669072, "process_ms": 13.312112}
{"case": "ascii-1MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 19.026388, "rss_kib": 6172, "marks": [{"phase": 0, "ns": 190879361661812}, {"phase": 1, "ns": 190879363516396}, {"phase": 3, "ns": 190879378048008}], "diagnostic": "", "acquire_ms": 1.854584, "process_ms": 14.531612}
{"case": "ascii-1MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 17.429853, "rss_kib": 6380, "marks": [{"phase": 0, "ns": 190879380621143}, {"phase": 1, "ns": 190879382304482}, {"phase": 3, "ns": 190879395646210}], "diagnostic": "", "acquire_ms": 1.683339, "process_ms": 13.341728}
{"case": "ascii-1MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 17.357747, "rss_kib": 6248, "marks": [{"phase": 0, "ns": 190879398332129}, {"phase": 1, "ns": 190879399854583}, {"phase": 3, "ns": 190879413320195}], "diagnostic": "", "acquire_ms": 1.522454, "process_ms": 13.465612}
{"case": "ascii-1MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 17.454199, "rss_kib": 6372, "marks": [{"phase": 0, "ns": 190879415767272}, {"phase": 1, "ns": 190879417574806}, {"phase": 3, "ns": 190879430717497}], "diagnostic": "", "acquire_ms": 1.807534, "process_ms": 13.142691}
{"case": "ascii-1MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 17.542937, "rss_kib": 6372, "marks": [{"phase": 0, "ns": 190879433559191}, {"phase": 1, "ns": 190879434976937}, {"phase": 3, "ns": 190879448660853}], "diagnostic": "", "acquire_ms": 1.417746, "process_ms": 13.683916}
{"case": "ascii-1MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 19.772421, "rss_kib": 6244, "marks": [{"phase": 0, "ns": 190879451325561}, {"phase": 1, "ns": 190879453005264}, {"phase": 3, "ns": 190879468465716}], "diagnostic": "", "acquire_ms": 1.679703, "process_ms": 15.460452}
{"case": "ascii-1MiB-construct-scan", "lane": "candidate", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 147.266064, "rss_kib": 99296, "marks": [{"phase": 0, "ns": 8647924}, {"phase": 1, "ns": 8852361}, {"phase": 3, "ns": 135340259}], "diagnostic": "", "acquire_ms": 0.204437, "process_ms": 126.487898}
{"case": "ascii-1MiB-construct-scan", "lane": "candidate", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 145.782282, "rss_kib": 104972, "marks": [{"phase": 0, "ns": 8369728}, {"phase": 1, "ns": 8626785}, {"phase": 3, "ns": 133247865}], "diagnostic": "", "acquire_ms": 0.257057, "process_ms": 124.62108}
{"case": "ascii-1MiB-construct-scan", "lane": "candidate", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 158.238091, "rss_kib": 99544, "marks": [{"phase": 0, "ns": 8298793}, {"phase": 1, "ns": 8508861}, {"phase": 3, "ns": 145353981}], "diagnostic": "", "acquire_ms": 0.210068, "process_ms": 136.84512}
{"case": "ascii-1MiB-construct-scan", "lane": "candidate", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 154.831117, "rss_kib": 99040, "marks": [{"phase": 0, "ns": 8687319}, {"phase": 1, "ns": 8904501}, {"phase": 3, "ns": 140737435}], "diagnostic": "", "acquire_ms": 0.217182, "process_ms": 131.832934}
{"case": "ascii-1MiB-construct-scan", "lane": "candidate", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 152.315631, "rss_kib": 100952, "marks": [{"phase": 0, "ns": 8602018}, {"phase": 1, "ns": 8824499}, {"phase": 3, "ns": 138244903}], "diagnostic": "", "acquire_ms": 0.222481, "process_ms": 129.420404}
{"case": "ascii-1MiB-construct-scan", "lane": "candidate", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 154.775211, "rss_kib": 99940, "marks": [{"phase": 0, "ns": 8183575}, {"phase": 1, "ns": 8394174}, {"phase": 3, "ns": 141314468}], "diagnostic": "", "acquire_ms": 0.210599, "process_ms": 132.920294}
{"case": "ascii-1MiB-construct-scan", "lane": "candidate", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 148.015785, "rss_kib": 101212, "marks": [{"phase": 0, "ns": 8363887}, {"phase": 1, "ns": 8580357}, {"phase": 3, "ns": 135635429}], "diagnostic": "", "acquire_ms": 0.21647, "process_ms": 127.055072}
{"case": "ascii-1MiB-construct-scan", "lane": "candidate", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 154.367739, "rss_kib": 99612, "marks": [{"phase": 0, "ns": 7771304}, {"phase": 1, "ns": 7999326}, {"phase": 3, "ns": 141125220}], "diagnostic": "", "acquire_ms": 0.228022, "process_ms": 133.125894}
{"case": "ascii-1MiB-construct-scan", "lane": "candidate", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 20.358942, "rss_kib": 6516, "marks": [{"phase": 0, "ns": 190880688180629, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": 0}, {"phase": 1, "ns": 190880689602974, "allocs": 17, "frees": 11, "live": 4194360, "peak": 4194376, "copy_cells": 1048576}, {"phase": 3, "ns": 190880706194839, "allocs": 2497416, "frees": 2497414, "live": 32, "peak": 4231232, "copy_cells": 1048576}], "diagnostic": "", "acquire_ms": 1.422345, "process_ms": 16.591865}
{"case": "ascii-1MiB-io-materialize", "lane": "base", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 34.331927, "rss_kib": 43236, "marks": [{"phase": 0, "ns": 190881903967369}, {"phase": 1, "ns": 190881912320435}, {"phase": 2, "ns": 190881931161993}, {"phase": 3, "ns": 190881932228153}], "diagnostic": "", "acquire_ms": 8.353066, "process_ms": 19.907718, "materialize_ms": 18.841558, "consume_ms": 1.06616}
{"case": "ascii-1MiB-io-materialize", "lane": "base", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 35.392956, "rss_kib": 43044, "marks": [{"phase": 0, "ns": 190881938512970}, {"phase": 1, "ns": 190881947596480}, {"phase": 2, "ns": 190881967925015}, {"phase": 3, "ns": 190881968958583}], "diagnostic": "", "acquire_ms": 9.08351, "process_ms": 21.362103, "materialize_ms": 20.328535, "consume_ms": 1.033568}
{"case": "ascii-1MiB-io-materialize", "lane": "base", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 32.843246, "rss_kib": 43288, "marks": [{"phase": 0, "ns": 190881974045782}, {"phase": 1, "ns": 190881981885365}, {"phase": 2, "ns": 190882000206727}, {"phase": 3, "ns": 190882001298485}], "diagnostic": "", "acquire_ms": 7.839583, "process_ms": 19.41312, "materialize_ms": 18.321362, "consume_ms": 1.091758}
{"case": "ascii-1MiB-io-materialize", "lane": "base", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 34.979493, "rss_kib": 43300, "marks": [{"phase": 0, "ns": 190882007128170}, {"phase": 1, "ns": 190882015192299}, {"phase": 2, "ns": 190882035117500}, {"phase": 3, "ns": 190882036819484}], "diagnostic": "", "acquire_ms": 8.064129, "process_ms": 21.627185, "materialize_ms": 19.925201, "consume_ms": 1.701984}
{"case": "ascii-1MiB-io-materialize", "lane": "base", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 35.133234, "rss_kib": 43028, "marks": [{"phase": 0, "ns": 190882042314946}, {"phase": 1, "ns": 190882050445931}, {"phase": 2, "ns": 190882071273161}, {"phase": 3, "ns": 190882072567433}], "diagnostic": "", "acquire_ms": 8.130985, "process_ms": 22.121502, "materialize_ms": 20.82723, "consume_ms": 1.294272}
{"case": "ascii-1MiB-io-materialize", "lane": "base", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 32.408472, "rss_kib": 43364, "marks": [{"phase": 0, "ns": 190882077654802}, {"phase": 1, "ns": 190882085759918}, {"phase": 2, "ns": 190882104658955}, {"phase": 3, "ns": 190882105846515}], "diagnostic": "", "acquire_ms": 8.105116, "process_ms": 20.086597, "materialize_ms": 18.899037, "consume_ms": 1.18756}
{"case": "ascii-1MiB-io-materialize", "lane": "base", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 33.068032, "rss_kib": 43216, "marks": [{"phase": 0, "ns": 190882110290615}, {"phase": 1, "ns": 190882118487986}, {"phase": 2, "ns": 190882137887230}, {"phase": 3, "ns": 190882138842269}], "diagnostic": "", "acquire_ms": 8.197371, "process_ms": 20.354283, "materialize_ms": 19.399244, "consume_ms": 0.955039}
{"case": "ascii-1MiB-io-materialize", "lane": "base", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 34.00684, "rss_kib": 43256, "marks": [{"phase": 0, "ns": 190882143468404}, {"phase": 1, "ns": 190882152263908}, {"phase": 2, "ns": 190882171420623}, {"phase": 3, "ns": 190882172437490}], "diagnostic": "", "acquire_ms": 8.795504, "process_ms": 20.173582, "materialize_ms": 19.156715, "consume_ms": 1.016867}
{"case": "ascii-1MiB-io-materialize", "lane": "base", "kind": "js", "run": "warm", "status": 1, "correct": false, "stdout": "", "wall_ms": 31.630618, "rss_kib": 57072, "marks": [{"phase": 0, "ns": 9606551}, {"phase": 1, "ns": 21695555}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 12.089004}
{"case": "ascii-1MiB-io-materialize", "lane": "base", "kind": "js", "run": 1, "status": 1, "correct": false, "stdout": "", "wall_ms": 33.406753, "rss_kib": 57084, "marks": [{"phase": 0, "ns": 8404202}, {"phase": 1, "ns": 19748987}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 11.344785}
{"case": "ascii-1MiB-io-materialize", "lane": "base", "kind": "js", "run": 2, "status": 1, "correct": false, "stdout": "", "wall_ms": 31.025241, "rss_kib": 56944, "marks": [{"phase": 0, "ns": 8149260}, {"phase": 1, "ns": 18964270}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 10.81501}
{"case": "ascii-1MiB-io-materialize", "lane": "base", "kind": "js", "run": 3, "status": 1, "correct": false, "stdout": "", "wall_ms": 33.395231, "rss_kib": 57252, "marks": [{"phase": 0, "ns": 9815116}, {"phase": 1, "ns": 22390302}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 12.575186}
{"case": "ascii-1MiB-io-materialize", "lane": "base", "kind": "js", "run": 4, "status": 1, "correct": false, "stdout": "", "wall_ms": 34.768002, "rss_kib": 56636, "marks": [{"phase": 0, "ns": 9546587}, {"phase": 1, "ns": 22420388}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 12.873801}
{"case": "ascii-1MiB-io-materialize", "lane": "base", "kind": "js", "run": 5, "status": 1, "correct": false, "stdout": "", "wall_ms": 30.717658, "rss_kib": 56824, "marks": [{"phase": 0, "ns": 9598265}, {"phase": 1, "ns": 21083785}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 11.48552}
{"case": "ascii-1MiB-io-materialize", "lane": "base", "kind": "js", "run": 6, "status": 1, "correct": false, "stdout": "", "wall_ms": 33.002658, "rss_kib": 57140, "marks": [{"phase": 0, "ns": 8473934}, {"phase": 1, "ns": 20018197}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 11.544263}
{"case": "ascii-1MiB-io-materialize", "lane": "base", "kind": "js", "run": 7, "status": 1, "correct": false, "stdout": "", "wall_ms": 31.047463, "rss_kib": 57028, "marks": [{"phase": 0, "ns": 8558876}, {"phase": 1, "ns": 19147097}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 10.588221}
{"case": "ascii-1MiB-io-materialize", "lane": "base", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 43.280611, "rss_kib": 43236, "marks": [{"phase": 0, "ns": 190882438101173, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": null}, {"phase": 1, "ns": 190882445883177, "allocs": 1048612, "frees": 34, "live": 16777240, "peak": 16777288, "copy_cells": null}, {"phase": 2, "ns": 190882475427192, "allocs": 2496654, "frees": 1647805, "live": 13581576, "peak": 16777272, "copy_cells": null}, {"phase": 3, "ns": 190882476976387, "allocs": 2496660, "frees": 2496658, "live": 32, "peak": 13581608, "copy_cells": null}], "diagnostic": "", "acquire_ms": 7.782004, "process_ms": 31.09321, "materialize_ms": 29.544015, "consume_ms": 1.549195}
{"case": "ascii-1MiB-io-materialize", "lane": "candidate", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 22.562868, "rss_kib": 13236, "marks": [{"phase": 0, "ns": 190883625822871}, {"phase": 1, "ns": 190883628770876}, {"phase": 2, "ns": 190883640222733}, {"phase": 3, "ns": 190883645372891}], "diagnostic": "", "acquire_ms": 2.948005, "process_ms": 16.602015, "materialize_ms": 11.451857, "consume_ms": 5.150158}
{"case": "ascii-1MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 21.720201, "rss_kib": 13196, "marks": [{"phase": 0, "ns": 190883648488373}, {"phase": 1, "ns": 190883651218085}, {"phase": 2, "ns": 190883661965177}, {"phase": 3, "ns": 190883667383963}], "diagnostic": "", "acquire_ms": 2.729712, "process_ms": 16.165878, "materialize_ms": 10.747092, "consume_ms": 5.418786}
{"case": "ascii-1MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 23.329731, "rss_kib": 13276, "marks": [{"phase": 0, "ns": 190883670358729}, {"phase": 1, "ns": 190883673471707}, {"phase": 2, "ns": 190883685801958}, {"phase": 3, "ns": 190883690878697}], "diagnostic": "", "acquire_ms": 3.112978, "process_ms": 17.40699, "materialize_ms": 12.330251, "consume_ms": 5.076739}
{"case": "ascii-1MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 23.259959, "rss_kib": 13252, "marks": [{"phase": 0, "ns": 190883693899250}, {"phase": 1, "ns": 190883697349577}, {"phase": 2, "ns": 190883709237560}, {"phase": 3, "ns": 190883714324959}], "diagnostic": "", "acquire_ms": 3.450327, "process_ms": 16.975382, "materialize_ms": 11.887983, "consume_ms": 5.087399}
{"case": "ascii-1MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 22.359663, "rss_kib": 13476, "marks": [{"phase": 0, "ns": 190883717492059}, {"phase": 1, "ns": 190883720280883}, {"phase": 2, "ns": 190883731102847}, {"phase": 3, "ns": 190883736734817}], "diagnostic": "", "acquire_ms": 2.788824, "process_ms": 16.453934, "materialize_ms": 10.821964, "consume_ms": 5.63197}
{"case": "ascii-1MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 21.20229, "rss_kib": 13460, "marks": [{"phase": 0, "ns": 190883739916726}, {"phase": 1, "ns": 190883742508957}, {"phase": 2, "ns": 190883752960479}, {"phase": 3, "ns": 190883758226305}], "diagnostic": "", "acquire_ms": 2.592231, "process_ms": 15.717348, "materialize_ms": 10.451522, "consume_ms": 5.265826}
{"case": "ascii-1MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 20.789108, "rss_kib": 13264, "marks": [{"phase": 0, "ns": 190883761374510}, {"phase": 1, "ns": 190883764070498}, {"phase": 2, "ns": 190883774215269}, {"phase": 3, "ns": 190883779314780}], "diagnostic": "", "acquire_ms": 2.695988, "process_ms": 15.244282, "materialize_ms": 10.144771, "consume_ms": 5.099511}
{"case": "ascii-1MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 21.237547, "rss_kib": 13012, "marks": [{"phase": 0, "ns": 190883782288895}, {"phase": 1, "ns": 190883784972770}, {"phase": 2, "ns": 190883795382943}, {"phase": 3, "ns": 190883800712711}], "diagnostic": "", "acquire_ms": 2.683875, "process_ms": 15.739941, "materialize_ms": 10.410173, "consume_ms": 5.329768}
{"case": "ascii-1MiB-io-materialize", "lane": "candidate", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 199.008527, "rss_kib": 177996, "marks": [{"phase": 0, "ns": 8551993}, {"phase": 1, "ns": 64266241}, {"phase": 2, "ns": 116110075}, {"phase": 3, "ns": 182592354}], "diagnostic": "", "acquire_ms": 55.714248, "process_ms": 118.326113, "materialize_ms": 51.843834, "consume_ms": 66.482279}
{"case": "ascii-1MiB-io-materialize", "lane": "candidate", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 193.192036, "rss_kib": 177624, "marks": [{"phase": 0, "ns": 8443217}, {"phase": 1, "ns": 58740211}, {"phase": 2, "ns": 111225271}, {"phase": 3, "ns": 178471968}], "diagnostic": "", "acquire_ms": 50.296994, "process_ms": 119.731757, "materialize_ms": 52.48506, "consume_ms": 67.246697}
{"case": "ascii-1MiB-io-materialize", "lane": "candidate", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 184.436007, "rss_kib": 178508, "marks": [{"phase": 0, "ns": 8568665}, {"phase": 1, "ns": 59118908}, {"phase": 2, "ns": 113423545}, {"phase": 3, "ns": 171443652}], "diagnostic": "", "acquire_ms": 50.550243, "process_ms": 112.324744, "materialize_ms": 54.304637, "consume_ms": 58.020107}
{"case": "ascii-1MiB-io-materialize", "lane": "candidate", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 191.126323, "rss_kib": 178504, "marks": [{"phase": 0, "ns": 8092452}, {"phase": 1, "ns": 59055988}, {"phase": 2, "ns": 114676118}, {"phase": 3, "ns": 176195544}], "diagnostic": "", "acquire_ms": 50.963536, "process_ms": 117.139556, "materialize_ms": 55.62013, "consume_ms": 61.519426}
{"case": "ascii-1MiB-io-materialize", "lane": "candidate", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 195.685661, "rss_kib": 177364, "marks": [{"phase": 0, "ns": 9299840}, {"phase": 1, "ns": 61749743}, {"phase": 2, "ns": 119224646}, {"phase": 3, "ns": 180163533}], "diagnostic": "", "acquire_ms": 52.449903, "process_ms": 118.41379, "materialize_ms": 57.474903, "consume_ms": 60.938887}
{"case": "ascii-1MiB-io-materialize", "lane": "candidate", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 196.676277, "rss_kib": 177420, "marks": [{"phase": 0, "ns": 8713930}, {"phase": 1, "ns": 63465463}, {"phase": 2, "ns": 120249688}, {"phase": 3, "ns": 184241819}], "diagnostic": "", "acquire_ms": 54.751533, "process_ms": 120.776356, "materialize_ms": 56.784225, "consume_ms": 63.992131}
{"case": "ascii-1MiB-io-materialize", "lane": "candidate", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 192.536886, "rss_kib": 178248, "marks": [{"phase": 0, "ns": 8723418}, {"phase": 1, "ns": 65504196}, {"phase": 2, "ns": 119220007}, {"phase": 3, "ns": 178838031}], "diagnostic": "", "acquire_ms": 56.780778, "process_ms": 113.333835, "materialize_ms": 53.715811, "consume_ms": 59.618024}
{"case": "ascii-1MiB-io-materialize", "lane": "candidate", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 192.285088, "rss_kib": 178456, "marks": [{"phase": 0, "ns": 8530021}, {"phase": 1, "ns": 60054420}, {"phase": 2, "ns": 115149204}, {"phase": 3, "ns": 176331963}], "diagnostic": "", "acquire_ms": 51.524399, "process_ms": 116.277543, "materialize_ms": 55.094784, "consume_ms": 61.182759}
{"case": "ascii-1MiB-io-materialize", "lane": "candidate", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "149797:986728105", "wall_ms": 24.359723, "rss_kib": 13360, "marks": [{"phase": 0, "ns": 190885350417411, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": 0}, {"phase": 1, "ns": 190885353351971, "allocs": 40, "frees": 34, "live": 4194360, "peak": 4194408, "copy_cells": 0}, {"phase": 2, "ns": 190885364292980, "allocs": 1398151, "frees": 798960, "live": 11384584, "peak": 11384600, "copy_cells": 0}, {"phase": 3, "ns": 190885371505155, "allocs": 2496663, "frees": 2496661, "live": 32, "peak": 11384616, "copy_cells": 0}], "diagnostic": "", "acquire_ms": 2.93456, "process_ms": 18.153184, "materialize_ms": 10.941009, "consume_ms": 7.212175}
{"case": "ascii-8MiB-io-scan", "lane": "base", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 207.608129, "rss_kib": 141284, "marks": [{"phase": 0, "ns": 190886681406537}, {"phase": 1, "ns": 190886744310306}, {"phase": 3, "ns": 190886878316939}], "diagnostic": "", "acquire_ms": 62.903769, "process_ms": 134.006633}
{"case": "ascii-8MiB-io-scan", "lane": "base", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 219.434496, "rss_kib": 141240, "marks": [{"phase": 0, "ns": 190886889095710}, {"phase": 1, "ns": 190886954208325}, {"phase": 3, "ns": 190887098659075}], "diagnostic": "", "acquire_ms": 65.112615, "process_ms": 144.45075}
{"case": "ascii-8MiB-io-scan", "lane": "base", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 205.512248, "rss_kib": 141488, "marks": [{"phase": 0, "ns": 190887108666365}, {"phase": 1, "ns": 190887170584547}, {"phase": 3, "ns": 190887304736855}], "diagnostic": "", "acquire_ms": 61.918182, "process_ms": 134.152308}
{"case": "ascii-8MiB-io-scan", "lane": "base", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 208.50005, "rss_kib": 141172, "marks": [{"phase": 0, "ns": 190887314266721}, {"phase": 1, "ns": 190887375497901}, {"phase": 3, "ns": 190887511705092}], "diagnostic": "", "acquire_ms": 61.23118, "process_ms": 136.207191}
{"case": "ascii-8MiB-io-scan", "lane": "base", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 201.376223, "rss_kib": 141196, "marks": [{"phase": 0, "ns": 190887523194310}, {"phase": 1, "ns": 190887583352517}, {"phase": 3, "ns": 190887715203676}], "diagnostic": "", "acquire_ms": 60.158207, "process_ms": 131.851159}
{"case": "ascii-8MiB-io-scan", "lane": "base", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 207.224103, "rss_kib": 141360, "marks": [{"phase": 0, "ns": 190887724745935}, {"phase": 1, "ns": 190887790310716}, {"phase": 3, "ns": 190887921367780}], "diagnostic": "", "acquire_ms": 65.564781, "process_ms": 131.057064}
{"case": "ascii-8MiB-io-scan", "lane": "base", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 207.802408, "rss_kib": 141284, "marks": [{"phase": 0, "ns": 190887932118608}, {"phase": 1, "ns": 190887994029757}, {"phase": 3, "ns": 190888127193552}], "diagnostic": "", "acquire_ms": 61.911149, "process_ms": 133.163795}
{"case": "ascii-8MiB-io-scan", "lane": "base", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 224.184335, "rss_kib": 141284, "marks": [{"phase": 0, "ns": 190888140360308}, {"phase": 1, "ns": 190888208919072}, {"phase": 3, "ns": 190888354386949}], "diagnostic": "", "acquire_ms": 68.558764, "process_ms": 145.467877}
{"case": "ascii-8MiB-io-scan", "lane": "base", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 7304.39295, "rss_kib": 235552, "marks": [{"phase": 0, "ns": 8833897}, {"phase": 1, "ns": 25949885}, {"phase": 3, "ns": 7285897958}], "diagnostic": "", "acquire_ms": 17.115988, "process_ms": 7259.948073}
{"case": "ascii-8MiB-io-scan", "lane": "base", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 7408.192411, "rss_kib": 235832, "marks": [{"phase": 0, "ns": 8680125}, {"phase": 1, "ns": 27160889}, {"phase": 3, "ns": 7393026616}], "diagnostic": "", "acquire_ms": 18.480764, "process_ms": 7365.865727}
{"case": "ascii-8MiB-io-scan", "lane": "base", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 7301.264593, "rss_kib": 243156, "marks": [{"phase": 0, "ns": 8418420}, {"phase": 1, "ns": 25615281}, {"phase": 3, "ns": 7281606408}], "diagnostic": "", "acquire_ms": 17.196861, "process_ms": 7255.991127}
{"case": "ascii-8MiB-io-scan", "lane": "base", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 7374.61818, "rss_kib": 226444, "marks": [{"phase": 0, "ns": 9160486}, {"phase": 1, "ns": 28013986}, {"phase": 3, "ns": 7357389418}], "diagnostic": "", "acquire_ms": 18.8535, "process_ms": 7329.375432}
{"case": "ascii-8MiB-io-scan", "lane": "base", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 7282.196996, "rss_kib": 242792, "marks": [{"phase": 0, "ns": 9072549}, {"phase": 1, "ns": 24882723}, {"phase": 3, "ns": 7267237293}], "diagnostic": "", "acquire_ms": 15.810174, "process_ms": 7242.35457}
{"case": "ascii-8MiB-io-scan", "lane": "base", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 7247.94938, "rss_kib": 239852, "marks": [{"phase": 0, "ns": 8132678}, {"phase": 1, "ns": 24893504}, {"phase": 3, "ns": 7231918928}], "diagnostic": "", "acquire_ms": 16.760826, "process_ms": 7207.025424}
{"case": "ascii-8MiB-io-scan", "lane": "base", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 7459.250426, "rss_kib": 236472, "marks": [{"phase": 0, "ns": 8617587}, {"phase": 1, "ns": 25892907}, {"phase": 3, "ns": 7442873307}], "diagnostic": "", "acquire_ms": 17.27532, "process_ms": 7416.9804}
{"case": "ascii-8MiB-io-scan", "lane": "base", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 7471.29165, "rss_kib": 229212, "marks": [{"phase": 0, "ns": 9208486}, {"phase": 1, "ns": 26942285}, {"phase": 3, "ns": 7454299967}], "diagnostic": "", "acquire_ms": 17.733799, "process_ms": 7427.357682}
{"case": "ascii-8MiB-io-scan", "lane": "base", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 313.605515, "rss_kib": 141412, "marks": [{"phase": 0, "ns": 190947215777783, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": null}, {"phase": 1, "ns": 190947285478891, "allocs": 8388644, "frees": 34, "live": 134217752, "peak": 134217800, "copy_cells": null}, {"phase": 3, "ns": 190947517446122, "allocs": 28363088, "frees": 28363086, "live": 32, "peak": 134303744, "copy_cells": null}], "diagnostic": "", "acquire_ms": 69.701108, "process_ms": 231.967231}
{"case": "ascii-8MiB-io-scan", "lane": "candidate", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 131.479975, "rss_kib": 43256, "marks": [{"phase": 0, "ns": 190948623178431}, {"phase": 1, "ns": 190948646673705}, {"phase": 3, "ns": 190948750630695}], "diagnostic": "", "acquire_ms": 23.495274, "process_ms": 103.95699}
{"case": "ascii-8MiB-io-scan", "lane": "candidate", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 127.905643, "rss_kib": 43112, "marks": [{"phase": 0, "ns": 190948754712398}, {"phase": 1, "ns": 190948776193797}, {"phase": 3, "ns": 190948878857206}], "diagnostic": "", "acquire_ms": 21.481399, "process_ms": 102.663409}
{"case": "ascii-8MiB-io-scan", "lane": "candidate", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 135.32495, "rss_kib": 43108, "marks": [{"phase": 0, "ns": 190948882800006}, {"phase": 1, "ns": 190948904233094}, {"phase": 3, "ns": 190949013379966}], "diagnostic": "", "acquire_ms": 21.433088, "process_ms": 109.146872}
{"case": "ascii-8MiB-io-scan", "lane": "candidate", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 138.661372, "rss_kib": 43124, "marks": [{"phase": 0, "ns": 190949018396170}, {"phase": 1, "ns": 190949041657382}, {"phase": 3, "ns": 190949151555838}], "diagnostic": "", "acquire_ms": 23.261212, "process_ms": 109.898456}
{"case": "ascii-8MiB-io-scan", "lane": "candidate", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 137.419328, "rss_kib": 43064, "marks": [{"phase": 0, "ns": 190949157218927}, {"phase": 1, "ns": 190949180518551}, {"phase": 3, "ns": 190949290571791}], "diagnostic": "", "acquire_ms": 23.299624, "process_ms": 110.05324}
{"case": "ascii-8MiB-io-scan", "lane": "candidate", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 132.07343, "rss_kib": 43192, "marks": [{"phase": 0, "ns": 190949295073330}, {"phase": 1, "ns": 190949319401342}, {"phase": 3, "ns": 190949422236416}], "diagnostic": "", "acquire_ms": 24.328012, "process_ms": 102.835074}
{"case": "ascii-8MiB-io-scan", "lane": "candidate", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 128.111814, "rss_kib": 43188, "marks": [{"phase": 0, "ns": 190949427205381}, {"phase": 1, "ns": 190949450050263}, {"phase": 3, "ns": 190949551420572}], "diagnostic": "", "acquire_ms": 22.844882, "process_ms": 101.370309}
{"case": "ascii-8MiB-io-scan", "lane": "candidate", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 133.562731, "rss_kib": 43056, "marks": [{"phase": 0, "ns": 190949555298429}, {"phase": 1, "ns": 190949580581180}, {"phase": 3, "ns": 190949684568006}], "diagnostic": "", "acquire_ms": 25.282751, "process_ms": 103.986826}
{"case": "ascii-8MiB-io-scan", "lane": "candidate", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 1271.919782, "rss_kib": 428712, "marks": [{"phase": 0, "ns": 8813378}, {"phase": 1, "ns": 332938373}, {"phase": 3, "ns": 1247290508}], "diagnostic": "", "acquire_ms": 324.124995, "process_ms": 914.352135}
{"case": "ascii-8MiB-io-scan", "lane": "candidate", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 1271.769256, "rss_kib": 403196, "marks": [{"phase": 0, "ns": 8819680}, {"phase": 1, "ns": 341681428}, {"phase": 3, "ns": 1252199729}], "diagnostic": "", "acquire_ms": 332.861748, "process_ms": 910.518301}
{"case": "ascii-8MiB-io-scan", "lane": "candidate", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 1223.148318, "rss_kib": 446948, "marks": [{"phase": 0, "ns": 8163778}, {"phase": 1, "ns": 319502337}, {"phase": 3, "ns": 1205788718}], "diagnostic": "", "acquire_ms": 311.338559, "process_ms": 886.286381}
{"case": "ascii-8MiB-io-scan", "lane": "candidate", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 1274.596042, "rss_kib": 401424, "marks": [{"phase": 0, "ns": 8720452}, {"phase": 1, "ns": 354308081}, {"phase": 3, "ns": 1250018437}], "diagnostic": "", "acquire_ms": 345.587629, "process_ms": 895.710356}
{"case": "ascii-8MiB-io-scan", "lane": "candidate", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 1244.853391, "rss_kib": 432788, "marks": [{"phase": 0, "ns": 8969043}, {"phase": 1, "ns": 329529004}, {"phase": 3, "ns": 1219511788}], "diagnostic": "", "acquire_ms": 320.559961, "process_ms": 889.982784}
{"case": "ascii-8MiB-io-scan", "lane": "candidate", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 1274.487887, "rss_kib": 420256, "marks": [{"phase": 0, "ns": 8742654}, {"phase": 1, "ns": 340346079}, {"phase": 3, "ns": 1251555369}], "diagnostic": "", "acquire_ms": 331.603425, "process_ms": 911.20929}
{"case": "ascii-8MiB-io-scan", "lane": "candidate", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 1231.064867, "rss_kib": 418812, "marks": [{"phase": 0, "ns": 9647618}, {"phase": 1, "ns": 349509469}, {"phase": 3, "ns": 1212570296}], "diagnostic": "", "acquire_ms": 339.861851, "process_ms": 863.060827}
{"case": "ascii-8MiB-io-scan", "lane": "candidate", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 1283.886765, "rss_kib": 398792, "marks": [{"phase": 0, "ns": 8625473}, {"phase": 1, "ns": 358470748}, {"phase": 3, "ns": 1264535662}], "diagnostic": "", "acquire_ms": 349.845275, "process_ms": 906.064914}
{"case": "ascii-8MiB-io-scan", "lane": "candidate", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 154.890379, "rss_kib": 43108, "marks": [{"phase": 0, "ns": 190959766694040, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": 0}, {"phase": 1, "ns": 190959790563032, "allocs": 40, "frees": 34, "live": 33554488, "peak": 33554536, "copy_cells": 0}, {"phase": 3, "ns": 190959917196365, "allocs": 19979165, "frees": 19979163, "live": 32, "peak": 33591360, "copy_cells": 0}], "diagnostic": "", "acquire_ms": 23.868992, "process_ms": 126.633333}
{"case": "ascii-8MiB-construct-scan", "lane": "base", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 503.802437, "rss_kib": 329520, "marks": [{"phase": 0, "ns": 190961067520699}, {"phase": 1, "ns": 190961279394340}, {"phase": 3, "ns": 190961546214244}], "diagnostic": "", "acquire_ms": 211.873641, "process_ms": 266.819904}
{"case": "ascii-8MiB-construct-scan", "lane": "base", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 519.806891, "rss_kib": 330032, "marks": [{"phase": 0, "ns": 190961571582137}, {"phase": 1, "ns": 190961792912445}, {"phase": 3, "ns": 190962068582768}], "diagnostic": "", "acquire_ms": 221.330308, "process_ms": 275.670323}
{"case": "ascii-8MiB-construct-scan", "lane": "base", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 498.457644, "rss_kib": 329708, "marks": [{"phase": 0, "ns": 190962091745212}, {"phase": 1, "ns": 190962306603059}, {"phase": 3, "ns": 190962570162016}], "diagnostic": "", "acquire_ms": 214.857847, "process_ms": 263.558957}
{"case": "ascii-8MiB-construct-scan", "lane": "base", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 508.356866, "rss_kib": 329404, "marks": [{"phase": 0, "ns": 190962590321010}, {"phase": 1, "ns": 190962799709964}, {"phase": 3, "ns": 190963073786096}], "diagnostic": "", "acquire_ms": 209.388954, "process_ms": 274.076132}
{"case": "ascii-8MiB-construct-scan", "lane": "base", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 512.799543, "rss_kib": 330036, "marks": [{"phase": 0, "ns": 190963099080129}, {"phase": 1, "ns": 190963317324620}, {"phase": 3, "ns": 190963588662524}], "diagnostic": "", "acquire_ms": 218.244491, "process_ms": 271.337904}
{"case": "ascii-8MiB-construct-scan", "lane": "base", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 505.469986, "rss_kib": 329912, "marks": [{"phase": 0, "ns": 190963611838013}, {"phase": 1, "ns": 190963828191812}, {"phase": 3, "ns": 190964094301360}], "diagnostic": "", "acquire_ms": 216.353799, "process_ms": 266.109548}
{"case": "ascii-8MiB-construct-scan", "lane": "base", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 507.897316, "rss_kib": 329572, "marks": [{"phase": 0, "ns": 190964117383452}, {"phase": 1, "ns": 190964333136393}, {"phase": 3, "ns": 190964599911673}], "diagnostic": "", "acquire_ms": 215.752941, "process_ms": 266.77528}
{"case": "ascii-8MiB-construct-scan", "lane": "base", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 519.486152, "rss_kib": 329904, "marks": [{"phase": 0, "ns": 190964625518007}, {"phase": 1, "ns": 190964841448064}, {"phase": 3, "ns": 190965123975378}], "diagnostic": "", "acquire_ms": 215.930057, "process_ms": 282.527314}
{"case": "ascii-8MiB-construct-scan", "lane": "base", "kind": "js", "run": "warm", "status": 1, "correct": false, "stdout": "", "wall_ms": 21.584845, "rss_kib": 51440, "marks": [{"phase": 0, "ns": 8578112}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "ascii-8MiB-construct-scan", "lane": "base", "kind": "js", "run": 1, "status": 1, "correct": false, "stdout": "", "wall_ms": 22.224357, "rss_kib": 51180, "marks": [{"phase": 0, "ns": 7948259}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "ascii-8MiB-construct-scan", "lane": "base", "kind": "js", "run": 2, "status": 1, "correct": false, "stdout": "", "wall_ms": 25.131705, "rss_kib": 51624, "marks": [{"phase": 0, "ns": 9425087}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "ascii-8MiB-construct-scan", "lane": "base", "kind": "js", "run": 3, "status": 1, "correct": false, "stdout": "", "wall_ms": 21.813709, "rss_kib": 51272, "marks": [{"phase": 0, "ns": 8702197}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "ascii-8MiB-construct-scan", "lane": "base", "kind": "js", "run": 4, "status": 1, "correct": false, "stdout": "", "wall_ms": 24.725405, "rss_kib": 51552, "marks": [{"phase": 0, "ns": 8903950}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "ascii-8MiB-construct-scan", "lane": "base", "kind": "js", "run": 5, "status": 1, "correct": false, "stdout": "", "wall_ms": 21.452645, "rss_kib": 51296, "marks": [{"phase": 0, "ns": 8295848}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "ascii-8MiB-construct-scan", "lane": "base", "kind": "js", "run": 6, "status": 1, "correct": false, "stdout": "", "wall_ms": 20.837639, "rss_kib": 51292, "marks": [{"phase": 0, "ns": 8422627}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "ascii-8MiB-construct-scan", "lane": "base", "kind": "js", "run": 7, "status": 1, "correct": false, "stdout": "", "wall_ms": 22.61183, "rss_kib": 51368, "marks": [{"phase": 0, "ns": 9871373}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "ascii-8MiB-construct-scan", "lane": "base", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 676.059169, "rss_kib": 329572, "marks": [{"phase": 0, "ns": 190965327157612, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": null}, {"phase": 1, "ns": 190965576471559, "allocs": 33554398, "frees": 16777202, "live": 201326352, "peak": 201326368, "copy_cells": null}, {"phase": 3, "ns": 190965981404094, "allocs": 88280089, "frees": 88280087, "live": 32, "peak": 201455344, "copy_cells": null}], "diagnostic": "", "acquire_ms": 249.313947, "process_ms": 404.932535}
{"case": "ascii-8MiB-construct-scan", "lane": "candidate", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 123.951461, "rss_kib": 34928, "marks": [{"phase": 0, "ns": 190967047441446}, {"phase": 1, "ns": 190967059921942}, {"phase": 3, "ns": 190967167357612}], "diagnostic": "", "acquire_ms": 12.480496, "process_ms": 107.43567}
{"case": "ascii-8MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 130.730355, "rss_kib": 34920, "marks": [{"phase": 0, "ns": 190967171803275}, {"phase": 1, "ns": 190967183661392}, {"phase": 3, "ns": 190967298104378}], "diagnostic": "", "acquire_ms": 11.858117, "process_ms": 114.442986}
{"case": "ascii-8MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 128.763348, "rss_kib": 34916, "marks": [{"phase": 0, "ns": 190967302467885}, {"phase": 1, "ns": 190967315066625}, {"phase": 3, "ns": 190967426314578}], "diagnostic": "", "acquire_ms": 12.59874, "process_ms": 111.247953}
{"case": "ascii-8MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 129.191229, "rss_kib": 34800, "marks": [{"phase": 0, "ns": 190967431385235}, {"phase": 1, "ns": 190967444760106}, {"phase": 3, "ns": 190967555920533}], "diagnostic": "", "acquire_ms": 13.374871, "process_ms": 111.160427}
{"case": "ascii-8MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 129.742965, "rss_kib": 34864, "marks": [{"phase": 0, "ns": 190967560723223}, {"phase": 1, "ns": 190967573685391}, {"phase": 3, "ns": 190967686553343}], "diagnostic": "", "acquire_ms": 12.962168, "process_ms": 112.867952}
{"case": "ascii-8MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 127.88261, "rss_kib": 34808, "marks": [{"phase": 0, "ns": 190967690700631}, {"phase": 1, "ns": 190967704710775}, {"phase": 3, "ns": 190967814753365}], "diagnostic": "", "acquire_ms": 14.010144, "process_ms": 110.04259}
{"case": "ascii-8MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 126.799859, "rss_kib": 34936, "marks": [{"phase": 0, "ns": 190967818845568}, {"phase": 1, "ns": 190967831890142}, {"phase": 3, "ns": 190967941706734}], "diagnostic": "", "acquire_ms": 13.044574, "process_ms": 109.816592}
{"case": "ascii-8MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 123.376533, "rss_kib": 34996, "marks": [{"phase": 0, "ns": 190967945719687}, {"phase": 1, "ns": 190967958237874}, {"phase": 3, "ns": 190968065004957}], "diagnostic": "", "acquire_ms": 12.518187, "process_ms": 106.767083}
{"case": "ascii-8MiB-construct-scan", "lane": "candidate", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 958.731518, "rss_kib": 112432, "marks": [{"phase": 0, "ns": 8384916}, {"phase": 1, "ns": 8594543}, {"phase": 3, "ns": 942011499}], "diagnostic": "", "acquire_ms": 0.209627, "process_ms": 933.416956}
{"case": "ascii-8MiB-construct-scan", "lane": "candidate", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 950.360126, "rss_kib": 113608, "marks": [{"phase": 0, "ns": 11381073}, {"phase": 1, "ns": 11736046}, {"phase": 3, "ns": 934313935}], "diagnostic": "", "acquire_ms": 0.354973, "process_ms": 922.577889}
{"case": "ascii-8MiB-construct-scan", "lane": "candidate", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 930.022985, "rss_kib": 114916, "marks": [{"phase": 0, "ns": 9059304}, {"phase": 1, "ns": 9357549}, {"phase": 3, "ns": 914572202}], "diagnostic": "", "acquire_ms": 0.298245, "process_ms": 905.214653}
{"case": "ascii-8MiB-construct-scan", "lane": "candidate", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 905.729489, "rss_kib": 114272, "marks": [{"phase": 0, "ns": 9385412}, {"phase": 1, "ns": 9630236}, {"phase": 3, "ns": 890932514}], "diagnostic": "", "acquire_ms": 0.244824, "process_ms": 881.302278}
{"case": "ascii-8MiB-construct-scan", "lane": "candidate", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 937.650747, "rss_kib": 112828, "marks": [{"phase": 0, "ns": 8556551}, {"phase": 1, "ns": 8795033}, {"phase": 3, "ns": 922615671}], "diagnostic": "", "acquire_ms": 0.238482, "process_ms": 913.820638}
{"case": "ascii-8MiB-construct-scan", "lane": "candidate", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 928.237773, "rss_kib": 113256, "marks": [{"phase": 0, "ns": 8466261}, {"phase": 1, "ns": 8681438}, {"phase": 3, "ns": 913178602}], "diagnostic": "", "acquire_ms": 0.215177, "process_ms": 904.497164}
{"case": "ascii-8MiB-construct-scan", "lane": "candidate", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 962.951673, "rss_kib": 112872, "marks": [{"phase": 0, "ns": 8433278}, {"phase": 1, "ns": 8642083}, {"phase": 3, "ns": 947354802}], "diagnostic": "", "acquire_ms": 0.208805, "process_ms": 938.712719}
{"case": "ascii-8MiB-construct-scan", "lane": "candidate", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 946.69398, "rss_kib": 112288, "marks": [{"phase": 0, "ns": 9514737}, {"phase": 1, "ns": 9852267}, {"phase": 3, "ns": 933686907}], "diagnostic": "", "acquire_ms": 0.33753, "process_ms": 923.83464}
{"case": "ascii-8MiB-construct-scan", "lane": "candidate", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 144.504041, "rss_kib": 34916, "marks": [{"phase": 0, "ns": 190975591591821, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": 0}, {"phase": 1, "ns": 190975604775049, "allocs": 17, "frees": 11, "live": 33554488, "peak": 33554504, "copy_cells": 8388608}, {"phase": 3, "ns": 190975731438619, "allocs": 19979142, "frees": 19979140, "live": 32, "peak": 33591360, "copy_cells": 8388608}], "diagnostic": "", "acquire_ms": 13.183228, "process_ms": 126.66357}
{"case": "ascii-8MiB-io-materialize", "lane": "base", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 256.06105, "rss_kib": 329900, "marks": [{"phase": 0, "ns": 190976937883039}, {"phase": 1, "ns": 190977006679462}, {"phase": 2, "ns": 190977160628899}, {"phase": 3, "ns": 190977169475480}], "diagnostic": "", "acquire_ms": 68.796423, "process_ms": 162.796018, "materialize_ms": 153.949437, "consume_ms": 8.846581}
{"case": "ascii-8MiB-io-materialize", "lane": "base", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 246.871108, "rss_kib": 329312, "marks": [{"phase": 0, "ns": 190977194061361}, {"phase": 1, "ns": 190977260752255}, {"phase": 2, "ns": 190977408489201}, {"phase": 3, "ns": 190977417269968}], "diagnostic": "", "acquire_ms": 66.690894, "process_ms": 156.517713, "materialize_ms": 147.736946, "consume_ms": 8.780767}
{"case": "ascii-8MiB-io-materialize", "lane": "base", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 238.196573, "rss_kib": 329808, "marks": [{"phase": 0, "ns": 190977441288273}, {"phase": 1, "ns": 190977505809767}, {"phase": 2, "ns": 190977648320311}, {"phase": 3, "ns": 190977656529335}], "diagnostic": "", "acquire_ms": 64.521494, "process_ms": 150.719568, "materialize_ms": 142.510544, "consume_ms": 8.209024}
{"case": "ascii-8MiB-io-materialize", "lane": "base", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 242.251616, "rss_kib": 329460, "marks": [{"phase": 0, "ns": 190977679684625}, {"phase": 1, "ns": 190977743294712}, {"phase": 2, "ns": 190977889211029}, {"phase": 3, "ns": 190977897233539}], "diagnostic": "", "acquire_ms": 63.610087, "process_ms": 153.938827, "materialize_ms": 145.916317, "consume_ms": 8.02251}
{"case": "ascii-8MiB-io-materialize", "lane": "base", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 246.915663, "rss_kib": 329544, "marks": [{"phase": 0, "ns": 190977921996956}, {"phase": 1, "ns": 190977989967234}, {"phase": 2, "ns": 190978135884703}, {"phase": 3, "ns": 190978144218994}], "diagnostic": "", "acquire_ms": 67.970278, "process_ms": 154.25176, "materialize_ms": 145.917469, "consume_ms": 8.334291}
{"case": "ascii-8MiB-io-materialize", "lane": "base", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 248.39233, "rss_kib": 329620, "marks": [{"phase": 0, "ns": 190978169206947}, {"phase": 1, "ns": 190978233883645}, {"phase": 2, "ns": 190978383824016}, {"phase": 3, "ns": 190978392401056}], "diagnostic": "", "acquire_ms": 64.676698, "process_ms": 158.517411, "materialize_ms": 149.940371, "consume_ms": 8.57704}
{"case": "ascii-8MiB-io-materialize", "lane": "base", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 242.859888, "rss_kib": 329676, "marks": [{"phase": 0, "ns": 190978417734754}, {"phase": 1, "ns": 190978482636107}, {"phase": 2, "ns": 190978630464547}, {"phase": 3, "ns": 190978638586916}], "diagnostic": "", "acquire_ms": 64.901353, "process_ms": 155.950809, "materialize_ms": 147.82844, "consume_ms": 8.122369}
{"case": "ascii-8MiB-io-materialize", "lane": "base", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 234.276577, "rss_kib": 329512, "marks": [{"phase": 0, "ns": 190978661025589}, {"phase": 1, "ns": 190978724058613}, {"phase": 2, "ns": 190978865830297}, {"phase": 3, "ns": 190978873954038}], "diagnostic": "", "acquire_ms": 63.033024, "process_ms": 149.895425, "materialize_ms": 141.771684, "consume_ms": 8.123741}
{"case": "ascii-8MiB-io-materialize", "lane": "base", "kind": "js", "run": "warm", "status": 1, "correct": false, "stdout": "", "wall_ms": 39.437359, "rss_kib": 71480, "marks": [{"phase": 0, "ns": 8845038}, {"phase": 1, "ns": 26907630}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 18.062592}
{"case": "ascii-8MiB-io-materialize", "lane": "base", "kind": "js", "run": 1, "status": 1, "correct": false, "stdout": "", "wall_ms": 39.033874, "rss_kib": 71684, "marks": [{"phase": 0, "ns": 9172408}, {"phase": 1, "ns": 26150746}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 16.978338}
{"case": "ascii-8MiB-io-materialize", "lane": "base", "kind": "js", "run": 2, "status": 1, "correct": false, "stdout": "", "wall_ms": 40.188853, "rss_kib": 71724, "marks": [{"phase": 0, "ns": 10068506}, {"phase": 1, "ns": 26398906}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 16.3304}
{"case": "ascii-8MiB-io-materialize", "lane": "base", "kind": "js", "run": 3, "status": 1, "correct": false, "stdout": "", "wall_ms": 40.480125, "rss_kib": 71420, "marks": [{"phase": 0, "ns": 9138224}, {"phase": 1, "ns": 26869298}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 17.731074}
{"case": "ascii-8MiB-io-materialize", "lane": "base", "kind": "js", "run": 4, "status": 1, "correct": false, "stdout": "", "wall_ms": 40.96327, "rss_kib": 71416, "marks": [{"phase": 0, "ns": 8942573}, {"phase": 1, "ns": 27313038}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 18.370465}
{"case": "ascii-8MiB-io-materialize", "lane": "base", "kind": "js", "run": 5, "status": 1, "correct": false, "stdout": "", "wall_ms": 38.269867, "rss_kib": 71408, "marks": [{"phase": 0, "ns": 8585196}, {"phase": 1, "ns": 25485125}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 16.899929}
{"case": "ascii-8MiB-io-materialize", "lane": "base", "kind": "js", "run": 6, "status": 1, "correct": false, "stdout": "", "wall_ms": 43.792631, "rss_kib": 71400, "marks": [{"phase": 0, "ns": 9896149}, {"phase": 1, "ns": 29351941}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 19.455792}
{"case": "ascii-8MiB-io-materialize", "lane": "base", "kind": "js", "run": 7, "status": 1, "correct": false, "stdout": "", "wall_ms": 36.345842, "rss_kib": 71476, "marks": [{"phase": 0, "ns": 9645385}, {"phase": 1, "ns": 27139109}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 17.493724}
{"case": "ascii-8MiB-io-materialize", "lane": "base", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 317.712096, "rss_kib": 329592, "marks": [{"phase": 0, "ns": 190979215437281, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": null}, {"phase": 1, "ns": 190979275926035, "allocs": 8388644, "frees": 34, "live": 134217752, "peak": 134217800, "copy_cells": null}, {"phase": 2, "ns": 190979499363134, "allocs": 19972920, "frees": 13182139, "live": 108652488, "peak": 134217784, "copy_cells": null}, {"phase": 3, "ns": 190979511461196, "allocs": 19972926, "frees": 19972924, "live": 32, "peak": 108652520, "copy_cells": null}], "diagnostic": "", "acquire_ms": 60.488754, "process_ms": 235.535161, "materialize_ms": 223.437099, "consume_ms": 12.098062}
{"case": "ascii-8MiB-io-materialize", "lane": "candidate", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 156.052891, "rss_kib": 91160, "marks": [{"phase": 0, "ns": 190980677582709}, {"phase": 1, "ns": 190980701667942}, {"phase": 2, "ns": 190980784058671}, {"phase": 3, "ns": 190980826127486}], "diagnostic": "", "acquire_ms": 24.085233, "process_ms": 124.459544, "materialize_ms": 82.390729, "consume_ms": 42.068815}
{"case": "ascii-8MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 164.247768, "rss_kib": 91168, "marks": [{"phase": 0, "ns": 190980833888009}, {"phase": 1, "ns": 190980859094747}, {"phase": 2, "ns": 190980946843939}, {"phase": 3, "ns": 190980989673144}], "diagnostic": "", "acquire_ms": 25.206738, "process_ms": 130.578397, "materialize_ms": 87.749192, "consume_ms": 42.829205}
{"case": "ascii-8MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 150.856878, "rss_kib": 90812, "marks": [{"phase": 0, "ns": 190980998168179}, {"phase": 1, "ns": 190981018613856}, {"phase": 2, "ns": 190981099698811}, {"phase": 3, "ns": 190981141007295}], "diagnostic": "", "acquire_ms": 20.445677, "process_ms": 122.393439, "materialize_ms": 81.084955, "consume_ms": 41.308484}
{"case": "ascii-8MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 155.680026, "rss_kib": 90908, "marks": [{"phase": 0, "ns": 190981149121318}, {"phase": 1, "ns": 190981172248947}, {"phase": 2, "ns": 190981253910505}, {"phase": 3, "ns": 190981297151761}], "diagnostic": "", "acquire_ms": 23.127629, "process_ms": 124.902814, "materialize_ms": 81.661558, "consume_ms": 43.241256}
{"case": "ascii-8MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 151.951221, "rss_kib": 91228, "marks": [{"phase": 0, "ns": 190981304921111}, {"phase": 1, "ns": 190981328114994}, {"phase": 2, "ns": 190981408322508}, {"phase": 3, "ns": 190981449590996}], "diagnostic": "", "acquire_ms": 23.193883, "process_ms": 121.476002, "materialize_ms": 80.207514, "consume_ms": 41.268488}
{"case": "ascii-8MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 156.23145, "rss_kib": 90840, "marks": [{"phase": 0, "ns": 190981457226713}, {"phase": 1, "ns": 190981480565070}, {"phase": 2, "ns": 190981563210713}, {"phase": 3, "ns": 190981604507374}], "diagnostic": "", "acquire_ms": 23.338357, "process_ms": 123.942304, "materialize_ms": 82.645643, "consume_ms": 41.296661}
{"case": "ascii-8MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 150.224179, "rss_kib": 90852, "marks": [{"phase": 0, "ns": 190981613605412}, {"phase": 1, "ns": 190981635710052}, {"phase": 2, "ns": 190981716724604}, {"phase": 3, "ns": 190981756967730}], "diagnostic": "", "acquire_ms": 22.10464, "process_ms": 121.257678, "materialize_ms": 81.014552, "consume_ms": 40.243126}
{"case": "ascii-8MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 152.014511, "rss_kib": 91076, "marks": [{"phase": 0, "ns": 190981763971469}, {"phase": 1, "ns": 190981786338035}, {"phase": 2, "ns": 190981865726086}, {"phase": 3, "ns": 190981907969281}], "diagnostic": "", "acquire_ms": 22.366566, "process_ms": 121.631246, "materialize_ms": 79.388051, "consume_ms": 42.243195}
{"case": "ascii-8MiB-io-materialize", "lane": "candidate", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 1267.370542, "rss_kib": 574364, "marks": [{"phase": 0, "ns": 8761139}, {"phase": 1, "ns": 340627962}, {"phase": 2, "ns": 690224867}, {"phase": 3, "ns": 1229796634}], "diagnostic": "", "acquire_ms": 331.866823, "process_ms": 889.168672, "materialize_ms": 349.596905, "consume_ms": 539.571767}
{"case": "ascii-8MiB-io-materialize", "lane": "candidate", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 1262.878943, "rss_kib": 578128, "marks": [{"phase": 0, "ns": 8842784}, {"phase": 1, "ns": 328143299}, {"phase": 2, "ns": 677049636}, {"phase": 3, "ns": 1218478821}], "diagnostic": "", "acquire_ms": 319.300515, "process_ms": 890.335522, "materialize_ms": 348.906337, "consume_ms": 541.429185}
{"case": "ascii-8MiB-io-materialize", "lane": "candidate", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 1269.276052, "rss_kib": 579908, "marks": [{"phase": 0, "ns": 9191083}, {"phase": 1, "ns": 339688712}, {"phase": 2, "ns": 675833220}, {"phase": 3, "ns": 1225662972}], "diagnostic": "", "acquire_ms": 330.497629, "process_ms": 885.97426, "materialize_ms": 336.144508, "consume_ms": 549.829752}
{"case": "ascii-8MiB-io-materialize", "lane": "candidate", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 1324.756247, "rss_kib": 566788, "marks": [{"phase": 0, "ns": 9124117}, {"phase": 1, "ns": 350938908}, {"phase": 2, "ns": 713458267}, {"phase": 3, "ns": 1286280220}], "diagnostic": "", "acquire_ms": 341.814791, "process_ms": 935.341312, "materialize_ms": 362.519359, "consume_ms": 572.821953}
{"case": "ascii-8MiB-io-materialize", "lane": "candidate", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 1324.190725, "rss_kib": 569744, "marks": [{"phase": 0, "ns": 9919043}, {"phase": 1, "ns": 355000593}, {"phase": 2, "ns": 727473570}, {"phase": 3, "ns": 1290713499}], "diagnostic": "", "acquire_ms": 345.08155, "process_ms": 935.712906, "materialize_ms": 372.472977, "consume_ms": 563.239929}
{"case": "ascii-8MiB-io-materialize", "lane": "candidate", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 1356.512895, "rss_kib": 563844, "marks": [{"phase": 0, "ns": 9302695}, {"phase": 1, "ns": 338023918}, {"phase": 2, "ns": 726999592}, {"phase": 3, "ns": 1315373801}], "diagnostic": "", "acquire_ms": 328.721223, "process_ms": 977.349883, "materialize_ms": 388.975674, "consume_ms": 588.374209}
{"case": "ascii-8MiB-io-materialize", "lane": "candidate", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 1314.040825, "rss_kib": 563964, "marks": [{"phase": 0, "ns": 8023121}, {"phase": 1, "ns": 329736527}, {"phase": 2, "ns": 693733014}, {"phase": 3, "ns": 1267816187}], "diagnostic": "", "acquire_ms": 321.713406, "process_ms": 938.07966, "materialize_ms": 363.996487, "consume_ms": 574.083173}
{"case": "ascii-8MiB-io-materialize", "lane": "candidate", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 1294.050501, "rss_kib": 570316, "marks": [{"phase": 0, "ns": 9356047}, {"phase": 1, "ns": 334068285}, {"phase": 2, "ns": 696869447}, {"phase": 3, "ns": 1257648964}], "diagnostic": "", "acquire_ms": 324.712238, "process_ms": 923.580679, "materialize_ms": 362.801162, "consume_ms": 560.779517}
{"case": "ascii-8MiB-io-materialize", "lane": "candidate", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "1198373:3966417190", "wall_ms": 177.20687, "rss_kib": 90904, "marks": [{"phase": 0, "ns": 190992331102044, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": 0}, {"phase": 1, "ns": 190992356406978, "allocs": 40, "frees": 34, "live": 33554488, "peak": 33554536, "copy_cells": 0}, {"phase": 2, "ns": 190992445763184, "allocs": 11184857, "frees": 6391362, "live": 91076360, "peak": 91076376, "copy_cells": 0}, {"phase": 3, "ns": 190992501079408, "allocs": 19972929, "frees": 19972927, "live": 32, "peak": 91076392, "copy_cells": 0}], "diagnostic": "", "acquire_ms": 25.304934, "process_ms": 144.67243, "materialize_ms": 89.356206, "consume_ms": 55.316224}
{"case": "ascii-64MiB-io-scan", "lane": "base", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 1685.493449, "rss_kib": 1116208, "marks": [{"phase": 0, "ns": 190993832830838}, {"phase": 1, "ns": 190994345813037}, {"phase": 3, "ns": 190995454455369}], "diagnostic": "", "acquire_ms": 512.982199, "process_ms": 1108.642332}
{"case": "ascii-64MiB-io-scan", "lane": "base", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 1695.645784, "rss_kib": 1115832, "marks": [{"phase": 0, "ns": 190995518370675}, {"phase": 1, "ns": 190996028535937}, {"phase": 3, "ns": 190997138912224}], "diagnostic": "", "acquire_ms": 510.165262, "process_ms": 1110.376287}
{"case": "ascii-64MiB-io-scan", "lane": "base", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 1667.064703, "rss_kib": 1116132, "marks": [{"phase": 0, "ns": 190997214386981}, {"phase": 1, "ns": 190997726838595}, {"phase": 3, "ns": 190998815466246}], "diagnostic": "", "acquire_ms": 512.451614, "process_ms": 1088.627651}
{"case": "ascii-64MiB-io-scan", "lane": "base", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 1688.742334, "rss_kib": 1115748, "marks": [{"phase": 0, "ns": 190998881546935}, {"phase": 1, "ns": 190999394778045}, {"phase": 3, "ns": 191000501732409}], "diagnostic": "", "acquire_ms": 513.23111, "process_ms": 1106.954364}
{"case": "ascii-64MiB-io-scan", "lane": "base", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 1705.610062, "rss_kib": 1116016, "marks": [{"phase": 0, "ns": 191000570636427}, {"phase": 1, "ns": 191001091980529}, {"phase": 3, "ns": 191002207720368}], "diagnostic": "", "acquire_ms": 521.344102, "process_ms": 1115.739839}
{"case": "ascii-64MiB-io-scan", "lane": "base", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 1676.386594, "rss_kib": 1116148, "marks": [{"phase": 0, "ns": 191002276427442}, {"phase": 1, "ns": 191002795459994}, {"phase": 3, "ns": 191003888203935}], "diagnostic": "", "acquire_ms": 519.032552, "process_ms": 1092.743941}
{"case": "ascii-64MiB-io-scan", "lane": "base", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 1667.359101, "rss_kib": 1115832, "marks": [{"phase": 0, "ns": 191003952847480}, {"phase": 1, "ns": 191004476579516}, {"phase": 3, "ns": 191005553572795}], "diagnostic": "", "acquire_ms": 523.732036, "process_ms": 1076.993279}
{"case": "ascii-64MiB-io-scan", "lane": "base", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 1692.070731, "rss_kib": 1115824, "marks": [{"phase": 0, "ns": 191005620746584}, {"phase": 1, "ns": 191006152318434}, {"phase": 3, "ns": 191007246760071}], "diagnostic": "", "acquire_ms": 531.57185, "process_ms": 1094.441637}
{"case": "ascii-64MiB-io-scan", "lane": "base", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 2542.725042, "rss_kib": 1115948, "marks": [{"phase": 0, "ns": 191007312776327, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": null}, {"phase": 1, "ns": 191007829030846, "allocs": 67108900, "frees": 34, "live": 1073741848, "peak": 1073741896, "copy_cells": null}, {"phase": 3, "ns": 191009786869257, "allocs": 226904401, "frees": 226904399, "live": 32, "peak": 1073827840, "copy_cells": null}], "diagnostic": "", "acquire_ms": 516.254519, "process_ms": 1957.838411}
{"case": "ascii-64MiB-io-scan", "lane": "candidate", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 1152.568426, "rss_kib": 329588, "marks": [{"phase": 0, "ns": 191011050245442}, {"phase": 1, "ns": 191011244787115}, {"phase": 3, "ns": 191012185878511}], "diagnostic": "", "acquire_ms": 194.541673, "process_ms": 941.091396}
{"case": "ascii-64MiB-io-scan", "lane": "candidate", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 1130.392079, "rss_kib": 329576, "marks": [{"phase": 0, "ns": 191012202784241}, {"phase": 1, "ns": 191012412585967}, {"phase": 3, "ns": 191013315663000}], "diagnostic": "", "acquire_ms": 209.801726, "process_ms": 903.077033}
{"case": "ascii-64MiB-io-scan", "lane": "candidate", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 1099.0666, "rss_kib": 329844, "marks": [{"phase": 0, "ns": 191013333388332}, {"phase": 1, "ns": 191013519897457}, {"phase": 3, "ns": 191014409464765}], "diagnostic": "", "acquire_ms": 186.509125, "process_ms": 889.567308}
{"case": "ascii-64MiB-io-scan", "lane": "candidate", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 1084.582057, "rss_kib": 329780, "marks": [{"phase": 0, "ns": 191014432822990}, {"phase": 1, "ns": 191014621687896}, {"phase": 3, "ns": 191015497423469}], "diagnostic": "", "acquire_ms": 188.864906, "process_ms": 875.735573}
{"case": "ascii-64MiB-io-scan", "lane": "candidate", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 1163.220808, "rss_kib": 329848, "marks": [{"phase": 0, "ns": 191015517475631}, {"phase": 1, "ns": 191015704293120}, {"phase": 3, "ns": 191016659257400}], "diagnostic": "", "acquire_ms": 186.817489, "process_ms": 954.96428}
{"case": "ascii-64MiB-io-scan", "lane": "candidate", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 1087.337517, "rss_kib": 329652, "marks": [{"phase": 0, "ns": 191016680908330}, {"phase": 1, "ns": 191016875019718}, {"phase": 3, "ns": 191017749624186}], "diagnostic": "", "acquire_ms": 194.111388, "process_ms": 874.604468}
{"case": "ascii-64MiB-io-scan", "lane": "candidate", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 1023.134307, "rss_kib": 329972, "marks": [{"phase": 0, "ns": 191017768474400}, {"phase": 1, "ns": 191017947699745}, {"phase": 3, "ns": 191018774319931}], "diagnostic": "", "acquire_ms": 179.225345, "process_ms": 826.620186}
{"case": "ascii-64MiB-io-scan", "lane": "candidate", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 1043.913204, "rss_kib": 329784, "marks": [{"phase": 0, "ns": 191018791748481}, {"phase": 1, "ns": 191018972416329}, {"phase": 3, "ns": 191019818621621}], "diagnostic": "", "acquire_ms": 180.667848, "process_ms": 846.205292}
{"case": "ascii-64MiB-io-scan", "lane": "candidate", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 1169.335242, "rss_kib": 329592, "marks": [{"phase": 0, "ns": 191019835860232, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": 0}, {"phase": 1, "ns": 191020016829501, "allocs": 40, "frees": 34, "live": 268435512, "peak": 268435560, "copy_cells": 0}, {"phase": 3, "ns": 191020989097735, "allocs": 159832991, "frees": 159832989, "live": 32, "peak": 268472384, "copy_cells": 0}], "diagnostic": "", "acquire_ms": 180.969269, "process_ms": 972.268234}
{"case": "ascii-64MiB-construct-scan", "lane": "base", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 4415.540206, "rss_kib": 2623208, "marks": [{"phase": 0, "ns": 191022150445825}, {"phase": 1, "ns": 191024221780860}, {"phase": 3, "ns": 191026390613335}], "diagnostic": "", "acquire_ms": 2071.335035, "process_ms": 2168.832475}
{"case": "ascii-64MiB-construct-scan", "lane": "base", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 4027.403722, "rss_kib": 2623480, "marks": [{"phase": 0, "ns": 191026566168907}, {"phase": 1, "ns": 191028263317067}, {"phase": 3, "ns": 191030426686051}], "diagnostic": "", "acquire_ms": 1697.14816, "process_ms": 2163.368984}
{"case": "ascii-64MiB-construct-scan", "lane": "base", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 4002.201203, "rss_kib": 2622840, "marks": [{"phase": 0, "ns": 191030593816832}, {"phase": 1, "ns": 191032295482762}, {"phase": 3, "ns": 191034429289817}], "diagnostic": "", "acquire_ms": 1701.66593, "process_ms": 2133.807055}
{"case": "ascii-64MiB-construct-scan", "lane": "base", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 3982.818991, "rss_kib": 2622828, "marks": [{"phase": 0, "ns": 191034595928986}, {"phase": 1, "ns": 191036280529753}, {"phase": 3, "ns": 191038406194863}], "diagnostic": "", "acquire_ms": 1684.600767, "process_ms": 2125.66511}
{"case": "ascii-64MiB-construct-scan", "lane": "base", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 4003.136705, "rss_kib": 2622768, "marks": [{"phase": 0, "ns": 191038579083642}, {"phase": 1, "ns": 191040262122491}, {"phase": 3, "ns": 191042416037754}], "diagnostic": "", "acquire_ms": 1683.038849, "process_ms": 2153.915263}
{"case": "ascii-64MiB-construct-scan", "lane": "base", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 4025.456142, "rss_kib": 2622840, "marks": [{"phase": 0, "ns": 191042582408875}, {"phase": 1, "ns": 191044276009043}, {"phase": 3, "ns": 191046440896624}], "diagnostic": "", "acquire_ms": 1693.600168, "process_ms": 2164.887581}
{"case": "ascii-64MiB-construct-scan", "lane": "base", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 4014.996144, "rss_kib": 2623024, "marks": [{"phase": 0, "ns": 191046608135349}, {"phase": 1, "ns": 191048333535175}, {"phase": 3, "ns": 191050459128849}], "diagnostic": "", "acquire_ms": 1725.399826, "process_ms": 2125.593674}
{"case": "ascii-64MiB-construct-scan", "lane": "base", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 4046.072392, "rss_kib": 2623076, "marks": [{"phase": 0, "ns": 191050623525059}, {"phase": 1, "ns": 191052323210977}, {"phase": 3, "ns": 191054500609151}], "diagnostic": "", "acquire_ms": 1699.685918, "process_ms": 2177.398174}
{"case": "ascii-64MiB-construct-scan", "lane": "base", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 5274.875363, "rss_kib": 2623340, "marks": [{"phase": 0, "ns": 191054669577723, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": null}, {"phase": 1, "ns": 191056640064788, "allocs": 268435450, "frees": 134217728, "live": 1610612664, "peak": 1610612680, "copy_cells": null}, {"phase": 3, "ns": 191059778900777, "allocs": 706240898, "frees": 706240896, "live": 32, "peak": 1610741656, "copy_cells": null}], "diagnostic": "", "acquire_ms": 1970.487065, "process_ms": 3138.835989}
{"case": "ascii-64MiB-construct-scan", "lane": "candidate", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 960.158531, "rss_kib": 264164, "marks": [{"phase": 0, "ns": 191060989059765}, {"phase": 1, "ns": 191061091745346}, {"phase": 3, "ns": 191061931904933}], "diagnostic": "", "acquire_ms": 102.685581, "process_ms": 840.159587}
{"case": "ascii-64MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 935.10325, "rss_kib": 264312, "marks": [{"phase": 0, "ns": 191061949093630}, {"phase": 1, "ns": 191062049130682}, {"phase": 3, "ns": 191062866640838}], "diagnostic": "", "acquire_ms": 100.037052, "process_ms": 817.510156}
{"case": "ascii-64MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 957.092111, "rss_kib": 264504, "marks": [{"phase": 0, "ns": 191062884325303}, {"phase": 1, "ns": 191062985354867}, {"phase": 3, "ns": 191063823438732}], "diagnostic": "", "acquire_ms": 101.029564, "process_ms": 838.083865}
{"case": "ascii-64MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 965.085716, "rss_kib": 264056, "marks": [{"phase": 0, "ns": 191063841743903}, {"phase": 1, "ns": 191063944680229}, {"phase": 3, "ns": 191064782678341}], "diagnostic": "", "acquire_ms": 102.936326, "process_ms": 837.998112}
{"case": "ascii-64MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 957.838846, "rss_kib": 264244, "marks": [{"phase": 0, "ns": 191064807136260}, {"phase": 1, "ns": 191064909536981}, {"phase": 3, "ns": 191065743146178}], "diagnostic": "", "acquire_ms": 102.400721, "process_ms": 833.609197}
{"case": "ascii-64MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 975.113875, "rss_kib": 264308, "marks": [{"phase": 0, "ns": 191065764998771}, {"phase": 1, "ns": 191065864976832}, {"phase": 3, "ns": 191066716418825}], "diagnostic": "", "acquire_ms": 99.978061, "process_ms": 851.441993}
{"case": "ascii-64MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 961.83596, "rss_kib": 264360, "marks": [{"phase": 0, "ns": 191066740357771}, {"phase": 1, "ns": 191066836488081}, {"phase": 3, "ns": 191067684490349}], "diagnostic": "", "acquire_ms": 96.13031, "process_ms": 848.002268}
{"case": "ascii-64MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 964.814392, "rss_kib": 264436, "marks": [{"phase": 0, "ns": 191067702299671}, {"phase": 1, "ns": 191067797440678}, {"phase": 3, "ns": 191068645376559}], "diagnostic": "", "acquire_ms": 95.141007, "process_ms": 847.935881}
{"case": "ascii-64MiB-construct-scan", "lane": "candidate", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 1119.807376, "rss_kib": 264276, "marks": [{"phase": 0, "ns": 191068667452454, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": 0}, {"phase": 1, "ns": 191068771386440, "allocs": 17, "frees": 11, "live": 268435512, "peak": 268435528, "copy_cells": 67108864}, {"phase": 3, "ns": 191069765260329, "allocs": 159832968, "frees": 159832966, "live": 32, "peak": 268472384, "copy_cells": 67108864}], "diagnostic": "", "acquire_ms": 103.933986, "process_ms": 993.873889}
{"case": "ascii-64MiB-io-materialize", "lane": "base", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 1916.181026, "rss_kib": 2623020, "marks": [{"phase": 0, "ns": 191070992024919}, {"phase": 1, "ns": 191071484851220}, {"phase": 2, "ns": 191072679723927}, {"phase": 3, "ns": 191072749152758}], "diagnostic": "", "acquire_ms": 492.826301, "process_ms": 1264.301538, "materialize_ms": 1194.872707, "consume_ms": 69.428831}
{"case": "ascii-64MiB-io-materialize", "lane": "base", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 1921.914198, "rss_kib": 2623404, "marks": [{"phase": 0, "ns": 191072908210143}, {"phase": 1, "ns": 191073403317024}, {"phase": 2, "ns": 191074578039193}, {"phase": 3, "ns": 191074651911554}], "diagnostic": "", "acquire_ms": 495.106881, "process_ms": 1248.59453, "materialize_ms": 1174.722169, "consume_ms": 73.872361}
{"case": "ascii-64MiB-io-materialize", "lane": "base", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 1917.598391, "rss_kib": 2623128, "marks": [{"phase": 0, "ns": 191074830450498}, {"phase": 1, "ns": 191075351186067}, {"phase": 2, "ns": 191076513563537}, {"phase": 3, "ns": 191076582450732}], "diagnostic": "", "acquire_ms": 520.735569, "process_ms": 1231.264665, "materialize_ms": 1162.37747, "consume_ms": 68.887195}
{"case": "ascii-64MiB-io-materialize", "lane": "base", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 1911.940091, "rss_kib": 2623352, "marks": [{"phase": 0, "ns": 191076748234711}, {"phase": 1, "ns": 191077247251120}, {"phase": 2, "ns": 191078425140680}, {"phase": 3, "ns": 191078490617564}], "diagnostic": "", "acquire_ms": 499.016409, "process_ms": 1243.366444, "materialize_ms": 1177.88956, "consume_ms": 65.476884}
{"case": "ascii-64MiB-io-materialize", "lane": "base", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 1920.020179, "rss_kib": 2623188, "marks": [{"phase": 0, "ns": 191078660453379}, {"phase": 1, "ns": 191079160668790}, {"phase": 2, "ns": 191080349325069}, {"phase": 3, "ns": 191080415131547}], "diagnostic": "", "acquire_ms": 500.215411, "process_ms": 1254.462757, "materialize_ms": 1188.656279, "consume_ms": 65.806478}
{"case": "ascii-64MiB-io-materialize", "lane": "base", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 1944.099952, "rss_kib": 2622924, "marks": [{"phase": 0, "ns": 191080580518444}, {"phase": 1, "ns": 191081086779248}, {"phase": 2, "ns": 191082270185079}, {"phase": 3, "ns": 191082340553581}], "diagnostic": "", "acquire_ms": 506.260804, "process_ms": 1253.774333, "materialize_ms": 1183.405831, "consume_ms": 70.368502}
{"case": "ascii-64MiB-io-materialize", "lane": "base", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 1925.271168, "rss_kib": 2623172, "marks": [{"phase": 0, "ns": 191082525177585}, {"phase": 1, "ns": 191083040365092}, {"phase": 2, "ns": 191084214379940}, {"phase": 3, "ns": 191084284071931}], "diagnostic": "", "acquire_ms": 515.187507, "process_ms": 1243.706839, "materialize_ms": 1174.014848, "consume_ms": 69.691991}
{"case": "ascii-64MiB-io-materialize", "lane": "base", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 1939.16963, "rss_kib": 2623220, "marks": [{"phase": 0, "ns": 191084450209790}, {"phase": 1, "ns": 191084951347788}, {"phase": 2, "ns": 191086155983782}, {"phase": 3, "ns": 191086225525919}], "diagnostic": "", "acquire_ms": 501.137998, "process_ms": 1274.178131, "materialize_ms": 1204.635994, "consume_ms": 69.542137}
{"case": "ascii-64MiB-io-materialize", "lane": "base", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 2655.325488, "rss_kib": 2622900, "marks": [{"phase": 0, "ns": 191086389541848, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": null}, {"phase": 1, "ns": 191086919011344, "allocs": 67108900, "frees": 34, "live": 1073741848, "peak": 1073741896, "copy_cells": null}, {"phase": 2, "ns": 191088788541444, "allocs": 159783054, "frees": 105456829, "live": 869219592, "peak": 1073741880, "copy_cells": null}, {"phase": 3, "ns": 191088880351459, "allocs": 159783060, "frees": 159783058, "live": 32, "peak": 869219624, "copy_cells": null}], "diagnostic": "", "acquire_ms": 529.469496, "process_ms": 1961.340115, "materialize_ms": 1869.5301, "consume_ms": 91.810015}
{"case": "ascii-64MiB-io-materialize", "lane": "candidate", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 1244.902804, "rss_kib": 713392, "marks": [{"phase": 0, "ns": 191090239763756}, {"phase": 1, "ns": 191090429825923}, {"phase": 2, "ns": 191091077092581}, {"phase": 3, "ns": 191091430730362}], "diagnostic": "", "acquire_ms": 190.062167, "process_ms": 1000.904439, "materialize_ms": 647.266658, "consume_ms": 353.637781}
{"case": "ascii-64MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 1218.311493, "rss_kib": 713264, "marks": [{"phase": 0, "ns": 191091484946341}, {"phase": 1, "ns": 191091673904145}, {"phase": 2, "ns": 191092318137727}, {"phase": 3, "ns": 191092653304182}], "diagnostic": "", "acquire_ms": 188.957804, "process_ms": 979.400037, "materialize_ms": 644.233582, "consume_ms": 335.166455}
{"case": "ascii-64MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 1208.354319, "rss_kib": 713588, "marks": [{"phase": 0, "ns": 191092703324361}, {"phase": 1, "ns": 191092882287770}, {"phase": 2, "ns": 191093528451137}, {"phase": 3, "ns": 191093859974931}], "diagnostic": "", "acquire_ms": 178.963409, "process_ms": 977.687161, "materialize_ms": 646.163367, "consume_ms": 331.523794}
{"case": "ascii-64MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 1245.479708, "rss_kib": 713324, "marks": [{"phase": 0, "ns": 191093911849564}, {"phase": 1, "ns": 191094090723423}, {"phase": 2, "ns": 191094748996784}, {"phase": 3, "ns": 191095103992879}], "diagnostic": "", "acquire_ms": 178.873859, "process_ms": 1013.269456, "materialize_ms": 658.273361, "consume_ms": 354.996095}
{"case": "ascii-64MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 1241.651044, "rss_kib": 713340, "marks": [{"phase": 0, "ns": 191095157969083}, {"phase": 1, "ns": 191095367410677}, {"phase": 2, "ns": 191096015181330}, {"phase": 3, "ns": 191096355296520}], "diagnostic": "", "acquire_ms": 209.441594, "process_ms": 987.885843, "materialize_ms": 647.770653, "consume_ms": 340.11519}
{"case": "ascii-64MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 1218.370216, "rss_kib": 713288, "marks": [{"phase": 0, "ns": 191096399567648}, {"phase": 1, "ns": 191096570849392}, {"phase": 2, "ns": 191097221522124}, {"phase": 3, "ns": 191097564975219}], "diagnostic": "", "acquire_ms": 171.281744, "process_ms": 994.125827, "materialize_ms": 650.672732, "consume_ms": 343.453095}
{"case": "ascii-64MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 1200.792381, "rss_kib": 713132, "marks": [{"phase": 0, "ns": 191097618102835}, {"phase": 1, "ns": 191097795110489}, {"phase": 2, "ns": 191098437256836}, {"phase": 3, "ns": 191098767025504}], "diagnostic": "", "acquire_ms": 177.007654, "process_ms": 971.915015, "materialize_ms": 642.146347, "consume_ms": 329.768668}
{"case": "ascii-64MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 1244.197148, "rss_kib": 713380, "marks": [{"phase": 0, "ns": 191098819161041}, {"phase": 1, "ns": 191099003752893}, {"phase": 2, "ns": 191099664915880}, {"phase": 3, "ns": 191100002739229}], "diagnostic": "", "acquire_ms": 184.591852, "process_ms": 998.986336, "materialize_ms": 661.162987, "consume_ms": 337.823349}
{"case": "ascii-64MiB-io-materialize", "lane": "candidate", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "9586981:1707099817", "wall_ms": 1369.836437, "rss_kib": 713084, "marks": [{"phase": 0, "ns": 191100063946323, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": 0}, {"phase": 1, "ns": 191100252657630, "allocs": 40, "frees": 34, "live": 268435512, "peak": 268435560, "copy_cells": 0}, {"phase": 2, "ns": 191100977335073, "allocs": 89478535, "frees": 51130608, "live": 728610568, "peak": 728610584, "copy_cells": 0}, {"phase": 3, "ns": 191101383414121, "allocs": 159783063, "frees": 159783061, "live": 32, "peak": 728610600, "copy_cells": 0}], "diagnostic": "", "acquire_ms": 188.711307, "process_ms": 1130.756491, "materialize_ms": 724.677443, "consume_ms": 406.079048}
{"case": "unicode-1MiB-io-scan", "lane": "base", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 19.571821, "rss_kib": 13412, "marks": [{"phase": 0, "ns": 191102679165143}, {"phase": 1, "ns": 191102684906601}, {"phase": 3, "ns": 191102695645888}], "diagnostic": "", "acquire_ms": 5.741458, "process_ms": 10.739287}
{"case": "unicode-1MiB-io-scan", "lane": "base", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 18.626971, "rss_kib": 13428, "marks": [{"phase": 0, "ns": 191102698877681}, {"phase": 1, "ns": 191102704064519}, {"phase": 3, "ns": 191102714760644}], "diagnostic": "", "acquire_ms": 5.186838, "process_ms": 10.696125}
{"case": "unicode-1MiB-io-scan", "lane": "base", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 18.918714, "rss_kib": 13496, "marks": [{"phase": 0, "ns": 191102717767470}, {"phase": 1, "ns": 191102723538224}, {"phase": 3, "ns": 191102733808482}], "diagnostic": "", "acquire_ms": 5.770754, "process_ms": 10.270258}
{"case": "unicode-1MiB-io-scan", "lane": "base", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 18.951506, "rss_kib": 13492, "marks": [{"phase": 0, "ns": 191102736667048}, {"phase": 1, "ns": 191102742097597}, {"phase": 3, "ns": 191102752722307}], "diagnostic": "", "acquire_ms": 5.430549, "process_ms": 10.62471}
{"case": "unicode-1MiB-io-scan", "lane": "base", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 19.246956, "rss_kib": 13432, "marks": [{"phase": 0, "ns": 191102755950653}, {"phase": 1, "ns": 191102761415908}, {"phase": 3, "ns": 191102772310870}], "diagnostic": "", "acquire_ms": 5.465255, "process_ms": 10.894962}
{"case": "unicode-1MiB-io-scan", "lane": "base", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 18.753561, "rss_kib": 13548, "marks": [{"phase": 0, "ns": 191102775343656}, {"phase": 1, "ns": 191102780638397}, {"phase": 3, "ns": 191102791082946}], "diagnostic": "", "acquire_ms": 5.294741, "process_ms": 10.444549}
{"case": "unicode-1MiB-io-scan", "lane": "base", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 18.320059, "rss_kib": 13496, "marks": [{"phase": 0, "ns": 191102794301524}, {"phase": 1, "ns": 191102799478512}, {"phase": 3, "ns": 191102809530747}], "diagnostic": "", "acquire_ms": 5.176988, "process_ms": 10.052235}
{"case": "unicode-1MiB-io-scan", "lane": "base", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 17.972752, "rss_kib": 13428, "marks": [{"phase": 0, "ns": 191102812634398}, {"phase": 1, "ns": 191102817856061}, {"phase": 3, "ns": 191102827948933}], "diagnostic": "", "acquire_ms": 5.221663, "process_ms": 10.092872}
{"case": "unicode-1MiB-io-scan", "lane": "base", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 642.212322, "rss_kib": 162932, "marks": [{"phase": 0, "ns": 8842703}, {"phase": 1, "ns": 21026948}, {"phase": 3, "ns": 627836114}], "diagnostic": "", "acquire_ms": 12.184245, "process_ms": 606.809166}
{"case": "unicode-1MiB-io-scan", "lane": "base", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 651.641917, "rss_kib": 163052, "marks": [{"phase": 0, "ns": 9397615}, {"phase": 1, "ns": 21053238}, {"phase": 3, "ns": 637926422}], "diagnostic": "", "acquire_ms": 11.655623, "process_ms": 616.873184}
{"case": "unicode-1MiB-io-scan", "lane": "base", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 662.950262, "rss_kib": 162568, "marks": [{"phase": 0, "ns": 10463294}, {"phase": 1, "ns": 21745089}, {"phase": 3, "ns": 646881318}], "diagnostic": "", "acquire_ms": 11.281795, "process_ms": 625.136229}
{"case": "unicode-1MiB-io-scan", "lane": "base", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 641.207678, "rss_kib": 163392, "marks": [{"phase": 0, "ns": 9126040}, {"phase": 1, "ns": 21415073}, {"phase": 3, "ns": 626582729}], "diagnostic": "", "acquire_ms": 12.289033, "process_ms": 605.167656}
{"case": "unicode-1MiB-io-scan", "lane": "base", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 633.105307, "rss_kib": 162936, "marks": [{"phase": 0, "ns": 8927644}, {"phase": 1, "ns": 20097787}, {"phase": 3, "ns": 617450297}], "diagnostic": "", "acquire_ms": 11.170143, "process_ms": 597.35251}
{"case": "unicode-1MiB-io-scan", "lane": "base", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 656.508728, "rss_kib": 162768, "marks": [{"phase": 0, "ns": 9274341}, {"phase": 1, "ns": 20864740}, {"phase": 3, "ns": 640304777}], "diagnostic": "", "acquire_ms": 11.590399, "process_ms": 619.440037}
{"case": "unicode-1MiB-io-scan", "lane": "base", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 688.294239, "rss_kib": 163008, "marks": [{"phase": 0, "ns": 9257479}, {"phase": 1, "ns": 20237182}, {"phase": 3, "ns": 674473494}], "diagnostic": "", "acquire_ms": 10.979703, "process_ms": 654.236312}
{"case": "unicode-1MiB-io-scan", "lane": "base", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 647.697986, "rss_kib": 163500, "marks": [{"phase": 0, "ns": 9425398}, {"phase": 1, "ns": 20832110}, {"phase": 3, "ns": 634060618}], "diagnostic": "", "acquire_ms": 11.406712, "process_ms": 613.228508}
{"case": "unicode-1MiB-io-scan", "lane": "base", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 26.938668, "rss_kib": 13492, "marks": [{"phase": 0, "ns": 191108055954445, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": null}, {"phase": 1, "ns": 191108062052860, "allocs": 655397, "frees": 34, "live": 10485800, "peak": 10485848, "copy_cells": null}, {"phase": 3, "ns": 191108080121303, "allocs": 2315822, "frees": 2315820, "live": 32, "peak": 10547216, "copy_cells": null}], "diagnostic": "", "acquire_ms": 6.098415, "process_ms": 18.068443}
{"case": "unicode-1MiB-io-scan", "lane": "candidate", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 15.004619, "rss_kib": 5752, "marks": [{"phase": 0, "ns": 191109227820854}, {"phase": 1, "ns": 191109230448492}, {"phase": 3, "ns": 191109239935496}], "diagnostic": "", "acquire_ms": 2.627638, "process_ms": 9.487004}
{"case": "unicode-1MiB-io-scan", "lane": "candidate", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 14.175497, "rss_kib": 5812, "marks": [{"phase": 0, "ns": 191109242635963}, {"phase": 1, "ns": 191109244960878}, {"phase": 3, "ns": 191109254215852}], "diagnostic": "", "acquire_ms": 2.324915, "process_ms": 9.254974}
{"case": "unicode-1MiB-io-scan", "lane": "candidate", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 15.024245, "rss_kib": 5752, "marks": [{"phase": 0, "ns": 191109257294545}, {"phase": 1, "ns": 191109259919579}, {"phase": 3, "ns": 191109269545166}], "diagnostic": "", "acquire_ms": 2.625034, "process_ms": 9.625587}
{"case": "unicode-1MiB-io-scan", "lane": "candidate", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 14.65714, "rss_kib": 5732, "marks": [{"phase": 0, "ns": 191109272300175}, {"phase": 1, "ns": 191109274836310}, {"phase": 3, "ns": 191109284448602}], "diagnostic": "", "acquire_ms": 2.536135, "process_ms": 9.612292}
{"case": "unicode-1MiB-io-scan", "lane": "candidate", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 15.643689, "rss_kib": 5808, "marks": [{"phase": 0, "ns": 191109287108832}, {"phase": 1, "ns": 191109289700342}, {"phase": 3, "ns": 191109300233899}], "diagnostic": "", "acquire_ms": 2.59151, "process_ms": 10.533557}
{"case": "unicode-1MiB-io-scan", "lane": "candidate", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 16.761327, "rss_kib": 5808, "marks": [{"phase": 0, "ns": 191109302896304}, {"phase": 1, "ns": 191109305648177}, {"phase": 3, "ns": 191109317160158}], "diagnostic": "", "acquire_ms": 2.751873, "process_ms": 11.511981}
{"case": "unicode-1MiB-io-scan", "lane": "candidate", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 14.642492, "rss_kib": 5752, "marks": [{"phase": 0, "ns": 191109320192333}, {"phase": 1, "ns": 191109322641964}, {"phase": 3, "ns": 191109331990556}], "diagnostic": "", "acquire_ms": 2.449631, "process_ms": 9.348592}
{"case": "unicode-1MiB-io-scan", "lane": "candidate", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 16.989238, "rss_kib": 5732, "marks": [{"phase": 0, "ns": 191109334840546}, {"phase": 1, "ns": 191109337350181}, {"phase": 3, "ns": 191109349246760}], "diagnostic": "", "acquire_ms": 2.509635, "process_ms": 11.896579}
{"case": "unicode-1MiB-io-scan", "lane": "candidate", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 177.51822, "rss_kib": 139316, "marks": [{"phase": 0, "ns": 10162423}, {"phase": 1, "ns": 72427402}, {"phase": 3, "ns": 165422764}], "diagnostic": "", "acquire_ms": 62.264979, "process_ms": 92.995362}
{"case": "unicode-1MiB-io-scan", "lane": "candidate", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 189.358574, "rss_kib": 145016, "marks": [{"phase": 0, "ns": 8888140}, {"phase": 1, "ns": 68006718}, {"phase": 3, "ns": 175575981}], "diagnostic": "", "acquire_ms": 59.118578, "process_ms": 107.569263}
{"case": "unicode-1MiB-io-scan", "lane": "candidate", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 172.499241, "rss_kib": 139280, "marks": [{"phase": 0, "ns": 8995073}, {"phase": 1, "ns": 66841690}, {"phase": 3, "ns": 159015806}], "diagnostic": "", "acquire_ms": 57.846617, "process_ms": 92.174116}
{"case": "unicode-1MiB-io-scan", "lane": "candidate", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 178.436821, "rss_kib": 147708, "marks": [{"phase": 0, "ns": 9328374}, {"phase": 1, "ns": 67827758}, {"phase": 3, "ns": 163805340}], "diagnostic": "", "acquire_ms": 58.499384, "process_ms": 95.977582}
{"case": "unicode-1MiB-io-scan", "lane": "candidate", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 168.382572, "rss_kib": 139456, "marks": [{"phase": 0, "ns": 10111327}, {"phase": 1, "ns": 66696024}, {"phase": 3, "ns": 156908623}], "diagnostic": "", "acquire_ms": 56.584697, "process_ms": 90.212599}
{"case": "unicode-1MiB-io-scan", "lane": "candidate", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 179.204045, "rss_kib": 143624, "marks": [{"phase": 0, "ns": 9375793}, {"phase": 1, "ns": 68505853}, {"phase": 3, "ns": 166307250}], "diagnostic": "", "acquire_ms": 59.13006, "process_ms": 97.801397}
{"case": "unicode-1MiB-io-scan", "lane": "candidate", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 178.221413, "rss_kib": 141116, "marks": [{"phase": 0, "ns": 10071181}, {"phase": 1, "ns": 70251019}, {"phase": 3, "ns": 165043575}], "diagnostic": "", "acquire_ms": 60.179838, "process_ms": 94.792556}
{"case": "unicode-1MiB-io-scan", "lane": "candidate", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 168.198794, "rss_kib": 139008, "marks": [{"phase": 0, "ns": 9043594}, {"phase": 1, "ns": 65199899}, {"phase": 3, "ns": 156035789}], "diagnostic": "", "acquire_ms": 56.156305, "process_ms": 90.83589}
{"case": "unicode-1MiB-io-scan", "lane": "candidate", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 15.87151, "rss_kib": 5732, "marks": [{"phase": 0, "ns": 191110765448703, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": 0}, {"phase": 1, "ns": 191110768041315, "allocs": 40, "frees": 34, "live": 4194360, "peak": 4194408, "copy_cells": 0}, {"phase": 3, "ns": 191110778988125, "allocs": 1660975, "frees": 1660973, "live": 32, "peak": 4231232, "copy_cells": 0}], "diagnostic": "", "acquire_ms": 2.592612, "process_ms": 10.94681}
{"case": "unicode-1MiB-construct-scan", "lane": "base", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 45.243219, "rss_kib": 27700, "marks": [{"phase": 0, "ns": 191111976317796}, {"phase": 1, "ns": 191111995356287}, {"phase": 3, "ns": 191112016673916}], "diagnostic": "", "acquire_ms": 19.038491, "process_ms": 21.317629}
{"case": "unicode-1MiB-construct-scan", "lane": "base", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 41.376353, "rss_kib": 27764, "marks": [{"phase": 0, "ns": 191112021818643}, {"phase": 1, "ns": 191112039551090}, {"phase": 3, "ns": 191112059029183}], "diagnostic": "", "acquire_ms": 17.732447, "process_ms": 19.478093}
{"case": "unicode-1MiB-construct-scan", "lane": "base", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 39.153801, "rss_kib": 27952, "marks": [{"phase": 0, "ns": 191112063332236}, {"phase": 1, "ns": 191112079339283}, {"phase": 3, "ns": 191112098721115}], "diagnostic": "", "acquire_ms": 16.007047, "process_ms": 19.381832}
{"case": "unicode-1MiB-construct-scan", "lane": "base", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 39.183748, "rss_kib": 27952, "marks": [{"phase": 0, "ns": 191112102711224}, {"phase": 1, "ns": 191112118915615}, {"phase": 3, "ns": 191112138383780}], "diagnostic": "", "acquire_ms": 16.204391, "process_ms": 19.468165}
{"case": "unicode-1MiB-construct-scan", "lane": "base", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 42.177591, "rss_kib": 27956, "marks": [{"phase": 0, "ns": 191112142082588}, {"phase": 1, "ns": 191112160479053}, {"phase": 3, "ns": 191112180092162}], "diagnostic": "", "acquire_ms": 18.396465, "process_ms": 19.613109}
{"case": "unicode-1MiB-construct-scan", "lane": "base", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 40.96889, "rss_kib": 27876, "marks": [{"phase": 0, "ns": 191112184558354}, {"phase": 1, "ns": 191112201655456}, {"phase": 3, "ns": 191112221714020}], "diagnostic": "", "acquire_ms": 17.097102, "process_ms": 20.058564}
{"case": "unicode-1MiB-construct-scan", "lane": "base", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 43.310256, "rss_kib": 27896, "marks": [{"phase": 0, "ns": 191112225695904}, {"phase": 1, "ns": 191112242695722}, {"phase": 3, "ns": 191112265316621}], "diagnostic": "", "acquire_ms": 16.999818, "process_ms": 22.620899}
{"case": "unicode-1MiB-construct-scan", "lane": "base", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 41.284378, "rss_kib": 27884, "marks": [{"phase": 0, "ns": 191112269338090}, {"phase": 1, "ns": 191112286269218}, {"phase": 3, "ns": 191112306800467}], "diagnostic": "", "acquire_ms": 16.931128, "process_ms": 20.531249}
{"case": "unicode-1MiB-construct-scan", "lane": "base", "kind": "js", "run": "warm", "status": 1, "correct": false, "stdout": "", "wall_ms": 21.656691, "rss_kib": 51644, "marks": [{"phase": 0, "ns": 8821022}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "unicode-1MiB-construct-scan", "lane": "base", "kind": "js", "run": 1, "status": 1, "correct": false, "stdout": "", "wall_ms": 21.665268, "rss_kib": 51648, "marks": [{"phase": 0, "ns": 8696898}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "unicode-1MiB-construct-scan", "lane": "base", "kind": "js", "run": 2, "status": 1, "correct": false, "stdout": "", "wall_ms": 22.74341, "rss_kib": 51720, "marks": [{"phase": 0, "ns": 9538913}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "unicode-1MiB-construct-scan", "lane": "base", "kind": "js", "run": 3, "status": 1, "correct": false, "stdout": "", "wall_ms": 25.993608, "rss_kib": 51664, "marks": [{"phase": 0, "ns": 11408785}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "unicode-1MiB-construct-scan", "lane": "base", "kind": "js", "run": 4, "status": 1, "correct": false, "stdout": "", "wall_ms": 21.276261, "rss_kib": 51724, "marks": [{"phase": 0, "ns": 8575828}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "unicode-1MiB-construct-scan", "lane": "base", "kind": "js", "run": 5, "status": 1, "correct": false, "stdout": "", "wall_ms": 23.039641, "rss_kib": 51704, "marks": [{"phase": 0, "ns": 9010823}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "unicode-1MiB-construct-scan", "lane": "base", "kind": "js", "run": 6, "status": 1, "correct": false, "stdout": "", "wall_ms": 21.77702, "rss_kib": 51712, "marks": [{"phase": 0, "ns": 8778142}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "unicode-1MiB-construct-scan", "lane": "base", "kind": "js", "run": 7, "status": 1, "correct": false, "stdout": "", "wall_ms": 22.717341, "rss_kib": 51596, "marks": [{"phase": 0, "ns": 9625005}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "unicode-1MiB-construct-scan", "lane": "base", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 53.227967, "rss_kib": 27896, "marks": [{"phase": 0, "ns": 191112493267001, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": null}, {"phase": 1, "ns": 191112513425805, "allocs": 2621410, "frees": 1310708, "live": 15728424, "peak": 15728440, "copy_cells": null}, {"phase": 3, "ns": 191112542723172, "allocs": 6509893, "frees": 6509891, "live": 32, "peak": 15820552, "copy_cells": null}], "diagnostic": "", "acquire_ms": 20.158804, "process_ms": 29.297367}
{"case": "unicode-1MiB-construct-scan", "lane": "candidate", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 13.574529, "rss_kib": 4836, "marks": [{"phase": 0, "ns": 191113540498703}, {"phase": 1, "ns": 191113541543833}, {"phase": 3, "ns": 191113551587121}], "diagnostic": "", "acquire_ms": 1.04513, "process_ms": 10.043288}
{"case": "unicode-1MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 15.323342, "rss_kib": 4856, "marks": [{"phase": 0, "ns": 191113554366948}, {"phase": 1, "ns": 191113555768414}, {"phase": 3, "ns": 191113567267961}], "diagnostic": "", "acquire_ms": 1.401466, "process_ms": 11.499547}
{"case": "unicode-1MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 13.085001, "rss_kib": 4920, "marks": [{"phase": 0, "ns": 191113569728893}, {"phase": 1, "ns": 191113570721444}, {"phase": 3, "ns": 191113580393429}], "diagnostic": "", "acquire_ms": 0.992551, "process_ms": 9.671985}
{"case": "unicode-1MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 13.155956, "rss_kib": 4984, "marks": [{"phase": 0, "ns": 191113583098093}, {"phase": 1, "ns": 191113584226851}, {"phase": 3, "ns": 191113593902453}], "diagnostic": "", "acquire_ms": 1.128758, "process_ms": 9.675602}
{"case": "unicode-1MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 13.507662, "rss_kib": 4712, "marks": [{"phase": 0, "ns": 191113596453537}, {"phase": 1, "ns": 191113597544554}, {"phase": 3, "ns": 191113607607569}], "diagnostic": "", "acquire_ms": 1.091017, "process_ms": 10.063015}
{"case": "unicode-1MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 14.266309, "rss_kib": 4784, "marks": [{"phase": 0, "ns": 191113610095914}, {"phase": 1, "ns": 191113611154469}, {"phase": 3, "ns": 191113622035835}], "diagnostic": "", "acquire_ms": 1.058555, "process_ms": 10.881366}
{"case": "unicode-1MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 13.068871, "rss_kib": 4840, "marks": [{"phase": 0, "ns": 191113624549227}, {"phase": 1, "ns": 191113625567366}, {"phase": 3, "ns": 191113635332918}], "diagnostic": "", "acquire_ms": 1.018139, "process_ms": 9.765552}
{"case": "unicode-1MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 12.323839, "rss_kib": 4844, "marks": [{"phase": 0, "ns": 191113637756961}, {"phase": 1, "ns": 191113638738110}, {"phase": 3, "ns": 191113647768770}], "diagnostic": "", "acquire_ms": 0.981149, "process_ms": 9.03066}
{"case": "unicode-1MiB-construct-scan", "lane": "candidate", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 116.224312, "rss_kib": 96648, "marks": [{"phase": 0, "ns": 9457278}, {"phase": 1, "ns": 9673337}, {"phase": 3, "ns": 104171235}], "diagnostic": "", "acquire_ms": 0.216059, "process_ms": 94.497898}
{"case": "unicode-1MiB-construct-scan", "lane": "candidate", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 120.53573, "rss_kib": 96500, "marks": [{"phase": 0, "ns": 8774774}, {"phase": 1, "ns": 9071947}, {"phase": 3, "ns": 107231633}], "diagnostic": "", "acquire_ms": 0.297173, "process_ms": 98.159686}
{"case": "unicode-1MiB-construct-scan", "lane": "candidate", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 119.201933, "rss_kib": 103648, "marks": [{"phase": 0, "ns": 9224347}, {"phase": 1, "ns": 9505950}, {"phase": 3, "ns": 105574214}], "diagnostic": "", "acquire_ms": 0.281603, "process_ms": 96.068264}
{"case": "unicode-1MiB-construct-scan", "lane": "candidate", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 119.881641, "rss_kib": 96120, "marks": [{"phase": 0, "ns": 9686042}, {"phase": 1, "ns": 9905187}, {"phase": 3, "ns": 106513974}], "diagnostic": "", "acquire_ms": 0.219145, "process_ms": 96.608787}
{"case": "unicode-1MiB-construct-scan", "lane": "candidate", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 117.167428, "rss_kib": 96064, "marks": [{"phase": 0, "ns": 8832264}, {"phase": 1, "ns": 9072479}, {"phase": 3, "ns": 104868417}], "diagnostic": "", "acquire_ms": 0.240215, "process_ms": 95.795938}
{"case": "unicode-1MiB-construct-scan", "lane": "candidate", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 119.013055, "rss_kib": 103572, "marks": [{"phase": 0, "ns": 9048774}, {"phase": 1, "ns": 9267208}, {"phase": 3, "ns": 105198341}], "diagnostic": "", "acquire_ms": 0.218434, "process_ms": 95.931133}
{"case": "unicode-1MiB-construct-scan", "lane": "candidate", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 117.344544, "rss_kib": 95652, "marks": [{"phase": 0, "ns": 8554568}, {"phase": 1, "ns": 8759626}, {"phase": 3, "ns": 105322266}], "diagnostic": "", "acquire_ms": 0.205058, "process_ms": 96.56264}
{"case": "unicode-1MiB-construct-scan", "lane": "candidate", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 117.977704, "rss_kib": 102508, "marks": [{"phase": 0, "ns": 9816529}, {"phase": 1, "ns": 10029182}, {"phase": 3, "ns": 104936285}], "diagnostic": "", "acquire_ms": 0.212653, "process_ms": 94.907103}
{"case": "unicode-1MiB-construct-scan", "lane": "candidate", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 14.722714, "rss_kib": 4724, "marks": [{"phase": 0, "ns": 191114599354468, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": 0}, {"phase": 1, "ns": 191114600424456, "allocs": 17, "frees": 11, "live": 4194360, "peak": 4194376, "copy_cells": 655361}, {"phase": 3, "ns": 191114611637249, "allocs": 1660952, "frees": 1660950, "live": 32, "peak": 4231232, "copy_cells": 655361}], "diagnostic": "", "acquire_ms": 1.069988, "process_ms": 11.212793}
{"case": "unicode-1MiB-io-materialize", "lane": "base", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 21.690395, "rss_kib": 27936, "marks": [{"phase": 0, "ns": 191115759491313}, {"phase": 1, "ns": 191115765878224}, {"phase": 2, "ns": 191115776959499}, {"phase": 3, "ns": 191115777463654}], "diagnostic": "", "acquire_ms": 6.386911, "process_ms": 11.58543, "materialize_ms": 11.081275, "consume_ms": 0.504155}
{"case": "unicode-1MiB-io-materialize", "lane": "base", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 20.798595, "rss_kib": 27876, "marks": [{"phase": 0, "ns": 191115781319219}, {"phase": 1, "ns": 191115786383454}, {"phase": 2, "ns": 191115797069911}, {"phase": 3, "ns": 191115797590026}], "diagnostic": "", "acquire_ms": 5.064235, "process_ms": 11.206572, "materialize_ms": 10.686457, "consume_ms": 0.520115}
{"case": "unicode-1MiB-io-materialize", "lane": "base", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 20.792815, "rss_kib": 27980, "marks": [{"phase": 0, "ns": 191115802336919}, {"phase": 1, "ns": 191115807646189}, {"phase": 2, "ns": 191115818851939}, {"phase": 3, "ns": 191115819376293}], "diagnostic": "", "acquire_ms": 5.30927, "process_ms": 11.730104, "materialize_ms": 11.20575, "consume_ms": 0.524354}
{"case": "unicode-1MiB-io-materialize", "lane": "base", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 20.923362, "rss_kib": 28004, "marks": [{"phase": 0, "ns": 191115823334131}, {"phase": 1, "ns": 191115828661465}, {"phase": 2, "ns": 191115840122048}, {"phase": 3, "ns": 191115840691397}], "diagnostic": "", "acquire_ms": 5.327334, "process_ms": 12.029932, "materialize_ms": 11.460583, "consume_ms": 0.569349}
{"case": "unicode-1MiB-io-materialize", "lane": "base", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 22.656135, "rss_kib": 27564, "marks": [{"phase": 0, "ns": 191115844598660}, {"phase": 1, "ns": 191115849898902}, {"phase": 2, "ns": 191115861776175}, {"phase": 3, "ns": 191115862656563}], "diagnostic": "", "acquire_ms": 5.300242, "process_ms": 12.757661, "materialize_ms": 11.877273, "consume_ms": 0.880388}
{"case": "unicode-1MiB-io-materialize", "lane": "base", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 21.949556, "rss_kib": 27856, "marks": [{"phase": 0, "ns": 191115867336950}, {"phase": 1, "ns": 191115872981304}, {"phase": 2, "ns": 191115884944610}, {"phase": 3, "ns": 191115885512997}], "diagnostic": "", "acquire_ms": 5.644354, "process_ms": 12.531693, "materialize_ms": 11.963306, "consume_ms": 0.568387}
{"case": "unicode-1MiB-io-materialize", "lane": "base", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 21.858263, "rss_kib": 27864, "marks": [{"phase": 0, "ns": 191115889536831}, {"phase": 1, "ns": 191115895347590}, {"phase": 2, "ns": 191115906703034}, {"phase": 3, "ns": 191115907360199}], "diagnostic": "", "acquire_ms": 5.810759, "process_ms": 12.012609, "materialize_ms": 11.355444, "consume_ms": 0.657165}
{"case": "unicode-1MiB-io-materialize", "lane": "base", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 21.939888, "rss_kib": 27508, "marks": [{"phase": 0, "ns": 191115911394292}, {"phase": 1, "ns": 191115916813369}, {"phase": 2, "ns": 191115928769963}, {"phase": 3, "ns": 191115929303243}], "diagnostic": "", "acquire_ms": 5.419077, "process_ms": 12.489874, "materialize_ms": 11.956594, "consume_ms": 0.53328}
{"case": "unicode-1MiB-io-materialize", "lane": "base", "kind": "js", "run": "warm", "status": 1, "correct": false, "stdout": "", "wall_ms": 29.908555, "rss_kib": 57968, "marks": [{"phase": 0, "ns": 8848084}, {"phase": 1, "ns": 20337492}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 11.489408}
{"case": "unicode-1MiB-io-materialize", "lane": "base", "kind": "js", "run": 1, "status": 1, "correct": false, "stdout": "", "wall_ms": 30.86613, "rss_kib": 57976, "marks": [{"phase": 0, "ns": 9549442}, {"phase": 1, "ns": 21317128}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 11.767686}
{"case": "unicode-1MiB-io-materialize", "lane": "base", "kind": "js", "run": 2, "status": 1, "correct": false, "stdout": "", "wall_ms": 28.896939, "rss_kib": 57656, "marks": [{"phase": 0, "ns": 8667772}, {"phase": 1, "ns": 19493412}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 10.82564}
{"case": "unicode-1MiB-io-materialize", "lane": "base", "kind": "js", "run": 3, "status": 1, "correct": false, "stdout": "", "wall_ms": 34.381479, "rss_kib": 57724, "marks": [{"phase": 0, "ns": 9893124}, {"phase": 1, "ns": 21924890}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 12.031766}
{"case": "unicode-1MiB-io-materialize", "lane": "base", "kind": "js", "run": 4, "status": 1, "correct": false, "stdout": "", "wall_ms": 30.795065, "rss_kib": 57704, "marks": [{"phase": 0, "ns": 9562548}, {"phase": 1, "ns": 20467919}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 10.905371}
{"case": "unicode-1MiB-io-materialize", "lane": "base", "kind": "js", "run": 5, "status": 1, "correct": false, "stdout": "", "wall_ms": 36.370799, "rss_kib": 57848, "marks": [{"phase": 0, "ns": 9409528}, {"phase": 1, "ns": 21450431}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 12.040903}
{"case": "unicode-1MiB-io-materialize", "lane": "base", "kind": "js", "run": 6, "status": 1, "correct": false, "stdout": "", "wall_ms": 35.682395, "rss_kib": 57452, "marks": [{"phase": 0, "ns": 9767175}, {"phase": 1, "ns": 22181826}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 12.414651}
{"case": "unicode-1MiB-io-materialize", "lane": "base", "kind": "js", "run": 7, "status": 1, "correct": false, "stdout": "", "wall_ms": 33.131412, "rss_kib": 57848, "marks": [{"phase": 0, "ns": 9302765}, {"phase": 1, "ns": 20944011}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 11.641246}
{"case": "unicode-1MiB-io-materialize", "lane": "base", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 29.322545, "rss_kib": 27804, "marks": [{"phase": 0, "ns": 191116195352136, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": null}, {"phase": 1, "ns": 191116201051344, "allocs": 655397, "frees": 34, "live": 10485800, "peak": 10485848, "copy_cells": null}, {"phase": 2, "ns": 191116219125568, "allocs": 1660291, "frees": 1179691, "live": 7689592, "peak": 10485832, "copy_cells": null}, {"phase": 3, "ns": 191116220047224, "allocs": 1660297, "frees": 1660295, "live": 32, "peak": 7689624, "copy_cells": null}], "diagnostic": "", "acquire_ms": 5.699208, "process_ms": 18.99588, "materialize_ms": 18.074224, "consume_ms": 0.921656}
{"case": "unicode-1MiB-io-materialize", "lane": "candidate", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 16.725088, "rss_kib": 10984, "marks": [{"phase": 0, "ns": 191117369051968}, {"phase": 1, "ns": 191117371369128}, {"phase": 2, "ns": 191117380201752}, {"phase": 3, "ns": 191117383085346}], "diagnostic": "", "acquire_ms": 2.31716, "process_ms": 11.716218, "materialize_ms": 8.832624, "consume_ms": 2.883594}
{"case": "unicode-1MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 16.50433, "rss_kib": 11100, "marks": [{"phase": 0, "ns": 191117386209866}, {"phase": 1, "ns": 191117388692770}, {"phase": 2, "ns": 191117396955935}, {"phase": 3, "ns": 191117399667292}], "diagnostic": "", "acquire_ms": 2.482904, "process_ms": 10.974522, "materialize_ms": 8.263165, "consume_ms": 2.711357}
{"case": "unicode-1MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 17.917697, "rss_kib": 10956, "marks": [{"phase": 0, "ns": 191117402669430}, {"phase": 1, "ns": 191117405642133}, {"phase": 2, "ns": 191117415131491}, {"phase": 3, "ns": 191117417874138}], "diagnostic": "", "acquire_ms": 2.972703, "process_ms": 12.232005, "materialize_ms": 9.489358, "consume_ms": 2.742647}
{"case": "unicode-1MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 16.701423, "rss_kib": 10988, "marks": [{"phase": 0, "ns": 191117420814549}, {"phase": 1, "ns": 191117423260092}, {"phase": 2, "ns": 191117431409232}, {"phase": 3, "ns": 191117434586341}], "diagnostic": "", "acquire_ms": 2.445543, "process_ms": 11.326249, "materialize_ms": 8.14914, "consume_ms": 3.177109}
{"case": "unicode-1MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 16.30399, "rss_kib": 11036, "marks": [{"phase": 0, "ns": 191117437660185}, {"phase": 1, "ns": 191117439979809}, {"phase": 2, "ns": 191117448170969}, {"phase": 3, "ns": 191117451107022}], "diagnostic": "", "acquire_ms": 2.319624, "process_ms": 11.127213, "materialize_ms": 8.19116, "consume_ms": 2.936053}
{"case": "unicode-1MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 16.83145, "rss_kib": 10920, "marks": [{"phase": 0, "ns": 191117454175966}, {"phase": 1, "ns": 191117456982433}, {"phase": 2, "ns": 191117465254005}, {"phase": 3, "ns": 191117468048509}], "diagnostic": "", "acquire_ms": 2.806467, "process_ms": 11.066076, "materialize_ms": 8.271572, "consume_ms": 2.794504}
{"case": "unicode-1MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 16.17194, "rss_kib": 11032, "marks": [{"phase": 0, "ns": 191117471132983}, {"phase": 1, "ns": 191117473442158}, {"phase": 2, "ns": 191117481582321}, {"phase": 3, "ns": 191117484524635}], "diagnostic": "", "acquire_ms": 2.309175, "process_ms": 11.082477, "materialize_ms": 8.140163, "consume_ms": 2.942314}
{"case": "unicode-1MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 17.309696, "rss_kib": 10836, "marks": [{"phase": 0, "ns": 191117487663633}, {"phase": 1, "ns": 191117489977907}, {"phase": 2, "ns": 191117499507602}, {"phase": 3, "ns": 191117502097229}], "diagnostic": "", "acquire_ms": 2.314274, "process_ms": 12.119322, "materialize_ms": 9.529695, "consume_ms": 2.589627}
{"case": "unicode-1MiB-io-materialize", "lane": "candidate", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 166.844408, "rss_kib": 162272, "marks": [{"phase": 0, "ns": 9580040}, {"phase": 1, "ns": 70075006}, {"phase": 2, "ns": 113059505}, {"phase": 3, "ns": 151773133}], "diagnostic": "", "acquire_ms": 60.494966, "process_ms": 81.698127, "materialize_ms": 42.984499, "consume_ms": 38.713628}
{"case": "unicode-1MiB-io-materialize", "lane": "candidate", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 172.502809, "rss_kib": 161368, "marks": [{"phase": 0, "ns": 9245387}, {"phase": 1, "ns": 68763682}, {"phase": 2, "ns": 116704812}, {"phase": 3, "ns": 159335772}], "diagnostic": "", "acquire_ms": 59.518295, "process_ms": 90.57209, "materialize_ms": 47.94113, "consume_ms": 42.63096}
{"case": "unicode-1MiB-io-materialize", "lane": "candidate", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 166.01167, "rss_kib": 163976, "marks": [{"phase": 0, "ns": 9851655}, {"phase": 1, "ns": 69538940}, {"phase": 2, "ns": 112287272}, {"phase": 3, "ns": 152294581}], "diagnostic": "", "acquire_ms": 59.687285, "process_ms": 82.755641, "materialize_ms": 42.748332, "consume_ms": 40.007309}
{"case": "unicode-1MiB-io-materialize", "lane": "candidate", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 169.554502, "rss_kib": 161100, "marks": [{"phase": 0, "ns": 9937778}, {"phase": 1, "ns": 67699575}, {"phase": 2, "ns": 114513149}, {"phase": 3, "ns": 155160711}], "diagnostic": "", "acquire_ms": 57.761797, "process_ms": 87.461136, "materialize_ms": 46.813574, "consume_ms": 40.647562}
{"case": "unicode-1MiB-io-materialize", "lane": "candidate", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 160.712239, "rss_kib": 162776, "marks": [{"phase": 0, "ns": 9797122}, {"phase": 1, "ns": 66157063}, {"phase": 2, "ns": 106858667}, {"phase": 3, "ns": 146413889}], "diagnostic": "", "acquire_ms": 56.359941, "process_ms": 80.256826, "materialize_ms": 40.701604, "consume_ms": 39.555222}
{"case": "unicode-1MiB-io-materialize", "lane": "candidate", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 167.257561, "rss_kib": 162952, "marks": [{"phase": 0, "ns": 9100312}, {"phase": 1, "ns": 68297549}, {"phase": 2, "ns": 115455926}, {"phase": 3, "ns": 154757759}], "diagnostic": "", "acquire_ms": 59.197237, "process_ms": 86.46021, "materialize_ms": 47.158377, "consume_ms": 39.301833}
{"case": "unicode-1MiB-io-materialize", "lane": "candidate", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 168.407659, "rss_kib": 162252, "marks": [{"phase": 0, "ns": 9582586}, {"phase": 1, "ns": 66573051}, {"phase": 2, "ns": 109943753}, {"phase": 3, "ns": 153869516}], "diagnostic": "", "acquire_ms": 56.990465, "process_ms": 87.296465, "materialize_ms": 43.370702, "consume_ms": 43.925763}
{"case": "unicode-1MiB-io-materialize", "lane": "candidate", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 169.762697, "rss_kib": 161552, "marks": [{"phase": 0, "ns": 10999220}, {"phase": 1, "ns": 69507551}, {"phase": 2, "ns": 111431762}, {"phase": 3, "ns": 154520960}], "diagnostic": "", "acquire_ms": 58.508331, "process_ms": 85.013409, "materialize_ms": 41.924211, "consume_ms": 43.089198}
{"case": "unicode-1MiB-io-materialize", "lane": "candidate", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "131072:3087947764", "wall_ms": 18.338805, "rss_kib": 10872, "marks": [{"phase": 0, "ns": 191118847917955, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": 0}, {"phase": 1, "ns": 191118850486832, "allocs": 40, "frees": 34, "live": 4194360, "peak": 4194408, "copy_cells": 0}, {"phase": 2, "ns": 191118859891420, "allocs": 1223385, "frees": 699094, "live": 10485784, "peak": 10485824, "copy_cells": 0}, {"phase": 3, "ns": 191118863139745, "allocs": 1660299, "frees": 1660297, "live": 32, "peak": 10485816, "copy_cells": 0}], "diagnostic": "", "acquire_ms": 2.568877, "process_ms": 12.652913, "materialize_ms": 9.404588, "consume_ms": 3.248325}
{"case": "unicode-8MiB-io-scan", "lane": "base", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 131.438527, "rss_kib": 92260, "marks": [{"phase": 0, "ns": 191120118756870}, {"phase": 1, "ns": 191120161835899}, {"phase": 3, "ns": 191120243305704}], "diagnostic": "", "acquire_ms": 43.079029, "process_ms": 81.469805}
{"case": "unicode-8MiB-io-scan", "lane": "base", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 134.805796, "rss_kib": 92276, "marks": [{"phase": 0, "ns": 191120250235674}, {"phase": 1, "ns": 191120295226795}, {"phase": 3, "ns": 191120377260217}], "diagnostic": "", "acquire_ms": 44.991121, "process_ms": 82.033422}
{"case": "unicode-8MiB-io-scan", "lane": "base", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 131.037858, "rss_kib": 92280, "marks": [{"phase": 0, "ns": 191120385246499}, {"phase": 1, "ns": 191120427299513}, {"phase": 3, "ns": 191120510076174}], "diagnostic": "", "acquire_ms": 42.053014, "process_ms": 82.776661}
{"case": "unicode-8MiB-io-scan", "lane": "base", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 132.485982, "rss_kib": 92080, "marks": [{"phase": 0, "ns": 191120516403943}, {"phase": 1, "ns": 191120560629023}, {"phase": 3, "ns": 191120641049459}], "diagnostic": "", "acquire_ms": 44.22508, "process_ms": 80.420436}
{"case": "unicode-8MiB-io-scan", "lane": "base", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 140.385027, "rss_kib": 92280, "marks": [{"phase": 0, "ns": 191120649251048}, {"phase": 1, "ns": 191120692123175}, {"phase": 3, "ns": 191120780983853}], "diagnostic": "", "acquire_ms": 42.872127, "process_ms": 88.860678}
{"case": "unicode-8MiB-io-scan", "lane": "base", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 137.179383, "rss_kib": 92264, "marks": [{"phase": 0, "ns": 191120789809674}, {"phase": 1, "ns": 191120830602121}, {"phase": 3, "ns": 191120918120265}], "diagnostic": "", "acquire_ms": 40.792447, "process_ms": 87.518144}
{"case": "unicode-8MiB-io-scan", "lane": "base", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 136.392542, "rss_kib": 92132, "marks": [{"phase": 0, "ns": 191120927069079}, {"phase": 1, "ns": 191120970824179}, {"phase": 3, "ns": 191121057261165}], "diagnostic": "", "acquire_ms": 43.7551, "process_ms": 86.436986}
{"case": "unicode-8MiB-io-scan", "lane": "base", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 136.049673, "rss_kib": 92268, "marks": [{"phase": 0, "ns": 191121063524922}, {"phase": 1, "ns": 191121104703079}, {"phase": 3, "ns": 191121192521583}], "diagnostic": "", "acquire_ms": 41.178157, "process_ms": 87.818504}
{"case": "unicode-8MiB-io-scan", "lane": "base", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 5500.702722, "rss_kib": 288560, "marks": [{"phase": 0, "ns": 8985244}, {"phase": 1, "ns": 30468657}, {"phase": 3, "ns": 5477675473}], "diagnostic": "", "acquire_ms": 21.483413, "process_ms": 5447.206816}
{"case": "unicode-8MiB-io-scan", "lane": "base", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 5470.339475, "rss_kib": 289780, "marks": [{"phase": 0, "ns": 9099711}, {"phase": 1, "ns": 28841764}, {"phase": 3, "ns": 5448136829}], "diagnostic": "", "acquire_ms": 19.742053, "process_ms": 5419.295065}
{"case": "unicode-8MiB-io-scan", "lane": "base", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 5566.147615, "rss_kib": 289256, "marks": [{"phase": 0, "ns": 10233990}, {"phase": 1, "ns": 32110197}, {"phase": 3, "ns": 5543717368}], "diagnostic": "", "acquire_ms": 21.876207, "process_ms": 5511.607171}
{"case": "unicode-8MiB-io-scan", "lane": "base", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 5455.826779, "rss_kib": 290656, "marks": [{"phase": 0, "ns": 9334426}, {"phase": 1, "ns": 29448675}, {"phase": 3, "ns": 5433545394}], "diagnostic": "", "acquire_ms": 20.114249, "process_ms": 5404.096719}
{"case": "unicode-8MiB-io-scan", "lane": "base", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 5519.554458, "rss_kib": 333472, "marks": [{"phase": 0, "ns": 9317163}, {"phase": 1, "ns": 29167752}, {"phase": 3, "ns": 5502668066}], "diagnostic": "", "acquire_ms": 19.850589, "process_ms": 5473.500314}
{"case": "unicode-8MiB-io-scan", "lane": "base", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 5537.957296, "rss_kib": 287848, "marks": [{"phase": 0, "ns": 9665552}, {"phase": 1, "ns": 30220897}, {"phase": 3, "ns": 5520950433}], "diagnostic": "", "acquire_ms": 20.555345, "process_ms": 5490.729536}
{"case": "unicode-8MiB-io-scan", "lane": "base", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 5456.53969, "rss_kib": 289428, "marks": [{"phase": 0, "ns": 10061693}, {"phase": 1, "ns": 30786949}, {"phase": 3, "ns": 5437390248}], "diagnostic": "", "acquire_ms": 20.725256, "process_ms": 5406.603299}
{"case": "unicode-8MiB-io-scan", "lane": "base", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 5487.261917, "rss_kib": 294340, "marks": [{"phase": 0, "ns": 9874157}, {"phase": 1, "ns": 31703726}, {"phase": 3, "ns": 5465482612}], "diagnostic": "", "acquire_ms": 21.829569, "process_ms": 5433.778886}
{"case": "unicode-8MiB-io-scan", "lane": "base", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 209.256873, "rss_kib": 92012, "marks": [{"phase": 0, "ns": 191165195703384, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": null}, {"phase": 1, "ns": 191165243039949, "allocs": 5242918, "frees": 34, "live": 83886136, "peak": 83886184, "copy_cells": null}, {"phase": 3, "ns": 191165396867805, "allocs": 18526257, "frees": 18526255, "live": 32, "peak": 83947552, "copy_cells": null}], "diagnostic": "", "acquire_ms": 47.336565, "process_ms": 153.827856}
{"case": "unicode-8MiB-io-scan", "lane": "candidate", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 95.933729, "rss_kib": 30904, "marks": [{"phase": 0, "ns": 191166549579883}, {"phase": 1, "ns": 191166570068101}, {"phase": 3, "ns": 191166641629002}], "diagnostic": "", "acquire_ms": 20.488218, "process_ms": 71.560901}
{"case": "unicode-8MiB-io-scan", "lane": "candidate", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 93.410788, "rss_kib": 30584, "marks": [{"phase": 0, "ns": 191166645815363}, {"phase": 1, "ns": 191166666206747}, {"phase": 3, "ns": 191166735791154}], "diagnostic": "", "acquire_ms": 20.391384, "process_ms": 69.584407}
{"case": "unicode-8MiB-io-scan", "lane": "candidate", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 95.188857, "rss_kib": 30820, "marks": [{"phase": 0, "ns": 191166739317936}, {"phase": 1, "ns": 191166758674589}, {"phase": 3, "ns": 191166831104948}], "diagnostic": "", "acquire_ms": 19.356653, "process_ms": 72.430359}
{"case": "unicode-8MiB-io-scan", "lane": "candidate", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 101.215024, "rss_kib": 30772, "marks": [{"phase": 0, "ns": 191166834652599}, {"phase": 1, "ns": 191166854356631}, {"phase": 3, "ns": 191166932526564}], "diagnostic": "", "acquire_ms": 19.704032, "process_ms": 78.169933}
{"case": "unicode-8MiB-io-scan", "lane": "candidate", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 96.194202, "rss_kib": 30764, "marks": [{"phase": 0, "ns": 191166936236613}, {"phase": 1, "ns": 191166956501006}, {"phase": 3, "ns": 191167028968996}], "diagnostic": "", "acquire_ms": 20.264393, "process_ms": 72.46799}
{"case": "unicode-8MiB-io-scan", "lane": "candidate", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 96.290946, "rss_kib": 30828, "marks": [{"phase": 0, "ns": 191167032494065}, {"phase": 1, "ns": 191167051727946}, {"phase": 3, "ns": 191167125293886}], "diagnostic": "", "acquire_ms": 19.233881, "process_ms": 73.56594}
{"case": "unicode-8MiB-io-scan", "lane": "candidate", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 96.457731, "rss_kib": 30840, "marks": [{"phase": 0, "ns": 191167128877315}, {"phase": 1, "ns": 191167148052925}, {"phase": 3, "ns": 191167222086632}], "diagnostic": "", "acquire_ms": 19.17561, "process_ms": 74.033707}
{"case": "unicode-8MiB-io-scan", "lane": "candidate", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 99.719, "rss_kib": 30764, "marks": [{"phase": 0, "ns": 191167225556876}, {"phase": 1, "ns": 191167246074399}, {"phase": 3, "ns": 191167321754735}], "diagnostic": "", "acquire_ms": 20.517523, "process_ms": 75.680336}
{"case": "unicode-8MiB-io-scan", "lane": "candidate", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 1058.035942, "rss_kib": 535160, "marks": [{"phase": 0, "ns": 9996800}, {"phase": 1, "ns": 432744198}, {"phase": 3, "ns": 1027965419}], "diagnostic": "", "acquire_ms": 422.747398, "process_ms": 595.221221}
{"case": "unicode-8MiB-io-scan", "lane": "candidate", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 1092.47988, "rss_kib": 534024, "marks": [{"phase": 0, "ns": 9138174}, {"phase": 1, "ns": 433853070}, {"phase": 3, "ns": 1060867908}], "diagnostic": "", "acquire_ms": 424.714896, "process_ms": 627.014838}
{"case": "unicode-8MiB-io-scan", "lane": "candidate", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 1068.935202, "rss_kib": 555616, "marks": [{"phase": 0, "ns": 9664721}, {"phase": 1, "ns": 423761860}, {"phase": 3, "ns": 1032381135}], "diagnostic": "", "acquire_ms": 414.097139, "process_ms": 608.619275}
{"case": "unicode-8MiB-io-scan", "lane": "candidate", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 1065.801486, "rss_kib": 534204, "marks": [{"phase": 0, "ns": 9386424}, {"phase": 1, "ns": 435676955}, {"phase": 3, "ns": 1032209622}], "diagnostic": "", "acquire_ms": 426.290531, "process_ms": 596.532667}
{"case": "unicode-8MiB-io-scan", "lane": "candidate", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 1102.308854, "rss_kib": 532900, "marks": [{"phase": 0, "ns": 9936837}, {"phase": 1, "ns": 438547625}, {"phase": 3, "ns": 1068568960}], "diagnostic": "", "acquire_ms": 428.610788, "process_ms": 630.021335}
{"case": "unicode-8MiB-io-scan", "lane": "candidate", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 1057.11167, "rss_kib": 549660, "marks": [{"phase": 0, "ns": 10175429}, {"phase": 1, "ns": 425946129}, {"phase": 3, "ns": 1021041421}], "diagnostic": "", "acquire_ms": 415.7707, "process_ms": 595.095292}
{"case": "unicode-8MiB-io-scan", "lane": "candidate", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 1113.723209, "rss_kib": 534844, "marks": [{"phase": 0, "ns": 10566529}, {"phase": 1, "ns": 443730032}, {"phase": 3, "ns": 1074271783}], "diagnostic": "", "acquire_ms": 433.163503, "process_ms": 630.541751}
{"case": "unicode-8MiB-io-scan", "lane": "candidate", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 1049.442641, "rss_kib": 547540, "marks": [{"phase": 0, "ns": 9731287}, {"phase": 1, "ns": 429650767}, {"phase": 3, "ns": 1012341979}], "diagnostic": "", "acquire_ms": 419.91948, "process_ms": 582.691212}
{"case": "unicode-8MiB-io-scan", "lane": "candidate", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 112.963243, "rss_kib": 30964, "marks": [{"phase": 0, "ns": 191175934931643, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": 0}, {"phase": 1, "ns": 191175955709870, "allocs": 40, "frees": 34, "live": 33554488, "peak": 33554536, "copy_cells": 0}, {"phase": 3, "ns": 191176043496263, "allocs": 13287473, "frees": 13287471, "live": 32, "peak": 33591360, "copy_cells": 0}], "diagnostic": "", "acquire_ms": 20.778227, "process_ms": 87.786393}
{"case": "unicode-8MiB-construct-scan", "lane": "base", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 320.273358, "rss_kib": 206764, "marks": [{"phase": 0, "ns": 191177192886917}, {"phase": 1, "ns": 191177331991268}, {"phase": 3, "ns": 191177494596234}], "diagnostic": "", "acquire_ms": 139.104351, "process_ms": 162.604966}
{"case": "unicode-8MiB-construct-scan", "lane": "base", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 306.444518, "rss_kib": 207088, "marks": [{"phase": 0, "ns": 191177513605659}, {"phase": 1, "ns": 191177650425853}, {"phase": 3, "ns": 191177805229267}], "diagnostic": "", "acquire_ms": 136.820194, "process_ms": 154.803414}
{"case": "unicode-8MiB-construct-scan", "lane": "base", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 299.107828, "rss_kib": 206896, "marks": [{"phase": 0, "ns": 191177820091095}, {"phase": 1, "ns": 191177954515488}, {"phase": 3, "ns": 191178105775740}], "diagnostic": "", "acquire_ms": 134.424393, "process_ms": 151.260252}
{"case": "unicode-8MiB-construct-scan", "lane": "base", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 291.462282, "rss_kib": 206968, "marks": [{"phase": 0, "ns": 191178119090266}, {"phase": 1, "ns": 191178247369868}, {"phase": 3, "ns": 191178397306221}], "diagnostic": "", "acquire_ms": 128.279602, "process_ms": 149.936353}
{"case": "unicode-8MiB-construct-scan", "lane": "base", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 298.913419, "rss_kib": 207220, "marks": [{"phase": 0, "ns": 191178410808613}, {"phase": 1, "ns": 191178543739357}, {"phase": 3, "ns": 191178697837836}], "diagnostic": "", "acquire_ms": 132.930744, "process_ms": 154.098479}
{"case": "unicode-8MiB-construct-scan", "lane": "base", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 300.134973, "rss_kib": 207080, "marks": [{"phase": 0, "ns": 191178709915088}, {"phase": 1, "ns": 191178838248241}, {"phase": 3, "ns": 191178997788861}], "diagnostic": "", "acquire_ms": 128.333153, "process_ms": 159.54062}
{"case": "unicode-8MiB-construct-scan", "lane": "base", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 293.343496, "rss_kib": 207016, "marks": [{"phase": 0, "ns": 191179010257785}, {"phase": 1, "ns": 191179139714316}, {"phase": 3, "ns": 191179291155571}], "diagnostic": "", "acquire_ms": 129.456531, "process_ms": 151.441255}
{"case": "unicode-8MiB-construct-scan", "lane": "base", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 293.475787, "rss_kib": 206824, "marks": [{"phase": 0, "ns": 191179303692644}, {"phase": 1, "ns": 191179433996852}, {"phase": 3, "ns": 191179585431373}], "diagnostic": "", "acquire_ms": 130.304208, "process_ms": 151.434521}
{"case": "unicode-8MiB-construct-scan", "lane": "base", "kind": "js", "run": "warm", "status": 1, "correct": false, "stdout": "", "wall_ms": 22.566695, "rss_kib": 51584, "marks": [{"phase": 0, "ns": 9226501}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "unicode-8MiB-construct-scan", "lane": "base", "kind": "js", "run": 1, "status": 1, "correct": false, "stdout": "", "wall_ms": 24.3268, "rss_kib": 52088, "marks": [{"phase": 0, "ns": 10407719}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "unicode-8MiB-construct-scan", "lane": "base", "kind": "js", "run": 2, "status": 1, "correct": false, "stdout": "", "wall_ms": 21.797799, "rss_kib": 51528, "marks": [{"phase": 0, "ns": 8825170}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "unicode-8MiB-construct-scan", "lane": "base", "kind": "js", "run": 3, "status": 1, "correct": false, "stdout": "", "wall_ms": 22.28431, "rss_kib": 51592, "marks": [{"phase": 0, "ns": 9114489}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "unicode-8MiB-construct-scan", "lane": "base", "kind": "js", "run": 4, "status": 1, "correct": false, "stdout": "", "wall_ms": 24.562727, "rss_kib": 52028, "marks": [{"phase": 0, "ns": 9873697}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "unicode-8MiB-construct-scan", "lane": "base", "kind": "js", "run": 5, "status": 1, "correct": false, "stdout": "", "wall_ms": 22.605389, "rss_kib": 51776, "marks": [{"phase": 0, "ns": 9425628}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "unicode-8MiB-construct-scan", "lane": "base", "kind": "js", "run": 6, "status": 1, "correct": false, "stdout": "", "wall_ms": 22.892563, "rss_kib": 51520, "marks": [{"phase": 0, "ns": 9836636}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "unicode-8MiB-construct-scan", "lane": "base", "kind": "js", "run": 7, "status": 1, "correct": false, "stdout": "", "wall_ms": 21.241124, "rss_kib": 51960, "marks": [{"phase": 0, "ns": 8909169}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "unicode-8MiB-construct-scan", "lane": "base", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 412.443416, "rss_kib": 206888, "marks": [{"phase": 0, "ns": 191179781171818, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": null}, {"phase": 1, "ns": 191179937286667, "allocs": 20971510, "frees": 10485758, "live": 125829024, "peak": 125829040, "copy_cells": null}, {"phase": 3, "ns": 191180177581937, "allocs": 52079284, "frees": 52079282, "live": 32, "peak": 125921152, "copy_cells": null}], "diagnostic": "", "acquire_ms": 156.114849, "process_ms": 240.29527}
{"case": "unicode-8MiB-construct-scan", "lane": "candidate", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 86.345683, "rss_kib": 22568, "marks": [{"phase": 0, "ns": 191181187655889}, {"phase": 1, "ns": 191181196493613}, {"phase": 3, "ns": 191181270250214}], "diagnostic": "", "acquire_ms": 8.837724, "process_ms": 73.756601}
{"case": "unicode-8MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 96.173503, "rss_kib": 22504, "marks": [{"phase": 0, "ns": 191181274123242}, {"phase": 1, "ns": 191181282524569}, {"phase": 3, "ns": 191181366522755}], "diagnostic": "", "acquire_ms": 8.401327, "process_ms": 83.998186}
{"case": "unicode-8MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 84.128753, "rss_kib": 22640, "marks": [{"phase": 0, "ns": 191181370417644}, {"phase": 1, "ns": 191181378917137}, {"phase": 3, "ns": 191181451211167}], "diagnostic": "", "acquire_ms": 8.499493, "process_ms": 72.29403}
{"case": "unicode-8MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 83.422564, "rss_kib": 22836, "marks": [{"phase": 0, "ns": 191181454821468}, {"phase": 1, "ns": 191181463243334}, {"phase": 3, "ns": 191181535044651}], "diagnostic": "", "acquire_ms": 8.421866, "process_ms": 71.801317}
{"case": "unicode-8MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 86.779365, "rss_kib": 22500, "marks": [{"phase": 0, "ns": 191181538234765}, {"phase": 1, "ns": 191181546105477}, {"phase": 3, "ns": 191181621701172}], "diagnostic": "", "acquire_ms": 7.870712, "process_ms": 75.595695}
{"case": "unicode-8MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 94.943974, "rss_kib": 22644, "marks": [{"phase": 0, "ns": 191181625419667}, {"phase": 1, "ns": 191181633530304}, {"phase": 3, "ns": 191181716742991}], "diagnostic": "", "acquire_ms": 8.110637, "process_ms": 83.212687}
{"case": "unicode-8MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 83.405893, "rss_kib": 22608, "marks": [{"phase": 0, "ns": 191181720693165}, {"phase": 1, "ns": 191181728336596}, {"phase": 3, "ns": 191181800509767}], "diagnostic": "", "acquire_ms": 7.643431, "process_ms": 72.173171}
{"case": "unicode-8MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 83.042064, "rss_kib": 22572, "marks": [{"phase": 0, "ns": 191181804182616}, {"phase": 1, "ns": 191181811702704}, {"phase": 3, "ns": 191181884062298}], "diagnostic": "", "acquire_ms": 7.520088, "process_ms": 72.359594}
{"case": "unicode-8MiB-construct-scan", "lane": "candidate", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 658.178912, "rss_kib": 116080, "marks": [{"phase": 0, "ns": 9316552}, {"phase": 1, "ns": 9559362}, {"phase": 3, "ns": 644629171}], "diagnostic": "", "acquire_ms": 0.24281, "process_ms": 635.069809}
{"case": "unicode-8MiB-construct-scan", "lane": "candidate", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 656.069957, "rss_kib": 116472, "marks": [{"phase": 0, "ns": 9844972}, {"phase": 1, "ns": 10107670}, {"phase": 3, "ns": 641247564}], "diagnostic": "", "acquire_ms": 0.262698, "process_ms": 631.139894}
{"case": "unicode-8MiB-construct-scan", "lane": "candidate", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 648.71397, "rss_kib": 117016, "marks": [{"phase": 0, "ns": 9526148}, {"phase": 1, "ns": 9778115}, {"phase": 3, "ns": 634525438}], "diagnostic": "", "acquire_ms": 0.251967, "process_ms": 624.747323}
{"case": "unicode-8MiB-construct-scan", "lane": "candidate", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 649.483708, "rss_kib": 117216, "marks": [{"phase": 0, "ns": 9265354}, {"phase": 1, "ns": 9533532}, {"phase": 3, "ns": 634472628}], "diagnostic": "", "acquire_ms": 0.268178, "process_ms": 624.939096}
{"case": "unicode-8MiB-construct-scan", "lane": "candidate", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 626.101568, "rss_kib": 115708, "marks": [{"phase": 0, "ns": 9167810}, {"phase": 1, "ns": 9413105}, {"phase": 3, "ns": 611400055}], "diagnostic": "", "acquire_ms": 0.245295, "process_ms": 601.98695}
{"case": "unicode-8MiB-construct-scan", "lane": "candidate", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 628.648032, "rss_kib": 117536, "marks": [{"phase": 0, "ns": 9334676}, {"phase": 1, "ns": 9556406}, {"phase": 3, "ns": 613610182}], "diagnostic": "", "acquire_ms": 0.22173, "process_ms": 604.053776}
{"case": "unicode-8MiB-construct-scan", "lane": "candidate", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 645.373562, "rss_kib": 117288, "marks": [{"phase": 0, "ns": 9288578}, {"phase": 1, "ns": 9497684}, {"phase": 3, "ns": 630589831}], "diagnostic": "", "acquire_ms": 0.209106, "process_ms": 621.092147}
{"case": "unicode-8MiB-construct-scan", "lane": "candidate", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 641.760014, "rss_kib": 115576, "marks": [{"phase": 0, "ns": 8822835}, {"phase": 1, "ns": 9030880}, {"phase": 3, "ns": 626188993}], "diagnostic": "", "acquire_ms": 0.208045, "process_ms": 617.158113}
{"case": "unicode-8MiB-construct-scan", "lane": "candidate", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 100.793796, "rss_kib": 22704, "marks": [{"phase": 0, "ns": 191187043273431, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": 0}, {"phase": 1, "ns": 191187051839571, "allocs": 17, "frees": 11, "live": 33554488, "peak": 33554504, "copy_cells": 5242882}, {"phase": 3, "ns": 191187140787454, "allocs": 13287450, "frees": 13287448, "live": 32, "peak": 33591360, "copy_cells": 5242882}], "diagnostic": "", "acquire_ms": 8.56614, "process_ms": 88.947883}
{"case": "unicode-8MiB-io-materialize", "lane": "base", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 167.462859, "rss_kib": 206880, "marks": [{"phase": 0, "ns": 191188293838834}, {"phase": 1, "ns": 191188339134292}, {"phase": 2, "ns": 191188438072844}, {"phase": 3, "ns": 191188443300388}], "diagnostic": "", "acquire_ms": 45.295458, "process_ms": 104.166096, "materialize_ms": 98.938552, "consume_ms": 5.227544}
{"case": "unicode-8MiB-io-materialize", "lane": "base", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 160.187485, "rss_kib": 206588, "marks": [{"phase": 0, "ns": 191188461414187}, {"phase": 1, "ns": 191188505953332}, {"phase": 2, "ns": 191188601291141}, {"phase": 3, "ns": 191188606210151}], "diagnostic": "", "acquire_ms": 44.539145, "process_ms": 100.256819, "materialize_ms": 95.337809, "consume_ms": 4.91901}
{"case": "unicode-8MiB-io-materialize", "lane": "base", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 159.713648, "rss_kib": 206808, "marks": [{"phase": 0, "ns": 191188621933230}, {"phase": 1, "ns": 191188668466423}, {"phase": 2, "ns": 191188759806539}, {"phase": 3, "ns": 191188764977275}], "diagnostic": "", "acquire_ms": 46.533193, "process_ms": 96.510852, "materialize_ms": 91.340116, "consume_ms": 5.170736}
{"case": "unicode-8MiB-io-materialize", "lane": "base", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 154.86985, "rss_kib": 206936, "marks": [{"phase": 0, "ns": 191188781739263}, {"phase": 1, "ns": 191188825159398}, {"phase": 2, "ns": 191188918078906}, {"phase": 3, "ns": 191188922905430}], "diagnostic": "", "acquire_ms": 43.420135, "process_ms": 97.746032, "materialize_ms": 92.919508, "consume_ms": 4.826524}
{"case": "unicode-8MiB-io-materialize", "lane": "base", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 154.984738, "rss_kib": 206904, "marks": [{"phase": 0, "ns": 191188936957844}, {"phase": 1, "ns": 191188978383781}, {"phase": 2, "ns": 191189072718630}, {"phase": 3, "ns": 191189077490942}], "diagnostic": "", "acquire_ms": 41.425937, "process_ms": 99.107161, "materialize_ms": 94.334849, "consume_ms": 4.772312}
{"case": "unicode-8MiB-io-materialize", "lane": "base", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 148.12457, "rss_kib": 206764, "marks": [{"phase": 0, "ns": 191189091911664}, {"phase": 1, "ns": 191189132550389}, {"phase": 2, "ns": 191189223037378}, {"phase": 3, "ns": 191189227660306}], "diagnostic": "", "acquire_ms": 40.638725, "process_ms": 95.109917, "materialize_ms": 90.486989, "consume_ms": 4.622928}
{"case": "unicode-8MiB-io-materialize", "lane": "base", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 147.169552, "rss_kib": 206916, "marks": [{"phase": 0, "ns": 191189240323308}, {"phase": 1, "ns": 191189282656694}, {"phase": 2, "ns": 191189371651857}, {"phase": 3, "ns": 191189376257953}], "diagnostic": "", "acquire_ms": 42.333386, "process_ms": 93.601259, "materialize_ms": 88.995163, "consume_ms": 4.606096}
{"case": "unicode-8MiB-io-materialize", "lane": "base", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 146.427455, "rss_kib": 207128, "marks": [{"phase": 0, "ns": 191189388063811}, {"phase": 1, "ns": 191189427960550}, {"phase": 2, "ns": 191189514920737}, {"phase": 3, "ns": 191189519949305}], "diagnostic": "", "acquire_ms": 39.896739, "process_ms": 91.988755, "materialize_ms": 86.960187, "consume_ms": 5.028568}
{"case": "unicode-8MiB-io-materialize", "lane": "base", "kind": "js", "run": "warm", "status": 1, "correct": false, "stdout": "", "wall_ms": 42.598799, "rss_kib": 74812, "marks": [{"phase": 0, "ns": 9294279}, {"phase": 1, "ns": 29397367}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 20.103088}
{"case": "unicode-8MiB-io-materialize", "lane": "base", "kind": "js", "run": 1, "status": 1, "correct": false, "stdout": "", "wall_ms": 43.727096, "rss_kib": 74700, "marks": [{"phase": 0, "ns": 9667507}, {"phase": 1, "ns": 29873640}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 20.206133}
{"case": "unicode-8MiB-io-materialize", "lane": "base", "kind": "js", "run": 2, "status": 1, "correct": false, "stdout": "", "wall_ms": 44.770904, "rss_kib": 74676, "marks": [{"phase": 0, "ns": 8991635}, {"phase": 1, "ns": 30189267}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 21.197632}
{"case": "unicode-8MiB-io-materialize", "lane": "base", "kind": "js", "run": 3, "status": 1, "correct": false, "stdout": "", "wall_ms": 42.648242, "rss_kib": 74936, "marks": [{"phase": 0, "ns": 8926462}, {"phase": 1, "ns": 30212231}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 21.285769}
{"case": "unicode-8MiB-io-materialize", "lane": "base", "kind": "js", "run": 4, "status": 1, "correct": false, "stdout": "", "wall_ms": 41.131048, "rss_kib": 74752, "marks": [{"phase": 0, "ns": 9581282}, {"phase": 1, "ns": 28783604}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 19.202322}
{"case": "unicode-8MiB-io-materialize", "lane": "base", "kind": "js", "run": 5, "status": 1, "correct": false, "stdout": "", "wall_ms": 43.846433, "rss_kib": 74616, "marks": [{"phase": 0, "ns": 9627821}, {"phase": 1, "ns": 30155734}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 20.527913}
{"case": "unicode-8MiB-io-materialize", "lane": "base", "kind": "js", "run": 6, "status": 1, "correct": false, "stdout": "", "wall_ms": 42.816832, "rss_kib": 74556, "marks": [{"phase": 0, "ns": 8685035}, {"phase": 1, "ns": 29299872}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 20.614837}
{"case": "unicode-8MiB-io-materialize", "lane": "base", "kind": "js", "run": 7, "status": 1, "correct": false, "stdout": "", "wall_ms": 41.607571, "rss_kib": 74808, "marks": [{"phase": 0, "ns": 8835500}, {"phase": 1, "ns": 27839686}], "diagnostic": "bend: memory fault (machine stack overflow?)", "acquire_ms": 19.004186}
{"case": "unicode-8MiB-io-materialize", "lane": "base", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 207.864876, "rss_kib": 206916, "marks": [{"phase": 0, "ns": 191189878930299, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": null}, {"phase": 1, "ns": 191189922669559, "allocs": 5242918, "frees": 34, "live": 83886136, "peak": 83886184, "copy_cells": null}, {"phase": 2, "ns": 191190066442104, "allocs": 13282010, "frees": 9437228, "live": 61516504, "peak": 83886168, "copy_cells": null}, {"phase": 3, "ns": 191190073631816, "allocs": 13282016, "frees": 13282014, "live": 32, "peak": 61516536, "copy_cells": null}], "diagnostic": "", "acquire_ms": 43.73926, "process_ms": 150.962257, "materialize_ms": 143.772545, "consume_ms": 7.189712}
{"case": "unicode-8MiB-io-materialize", "lane": "candidate", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 121.337308, "rss_kib": 71636, "marks": [{"phase": 0, "ns": 191191231386988}, {"phase": 1, "ns": 191191250528574}, {"phase": 2, "ns": 191191318451773}, {"phase": 3, "ns": 191191344779054}], "diagnostic": "", "acquire_ms": 19.141586, "process_ms": 94.25048, "materialize_ms": 67.923199, "consume_ms": 26.327281}
{"case": "unicode-8MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 118.521413, "rss_kib": 71912, "marks": [{"phase": 0, "ns": 191191353195460}, {"phase": 1, "ns": 191191373252681}, {"phase": 2, "ns": 191191442388868}, {"phase": 3, "ns": 191191464976673}], "diagnostic": "", "acquire_ms": 20.057221, "process_ms": 91.723992, "materialize_ms": 69.136187, "consume_ms": 22.587805}
{"case": "unicode-8MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 114.858554, "rss_kib": 71840, "marks": [{"phase": 0, "ns": 191191471677879}, {"phase": 1, "ns": 191191491839348}, {"phase": 2, "ns": 191191557682356}, {"phase": 3, "ns": 191191579228718}], "diagnostic": "", "acquire_ms": 20.161469, "process_ms": 87.38937, "materialize_ms": 65.843008, "consume_ms": 21.546362}
{"case": "unicode-8MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 111.190304, "rss_kib": 72036, "marks": [{"phase": 0, "ns": 191191586720422}, {"phase": 1, "ns": 191191607152493}, {"phase": 2, "ns": 191191671552807}, {"phase": 3, "ns": 191191692108423}], "diagnostic": "", "acquire_ms": 20.432071, "process_ms": 84.95593, "materialize_ms": 64.400314, "consume_ms": 20.555616}
{"case": "unicode-8MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 114.739017, "rss_kib": 71804, "marks": [{"phase": 0, "ns": 191191697953086}, {"phase": 1, "ns": 191191718242236}, {"phase": 2, "ns": 191191784079874}, {"phase": 3, "ns": 191191805393155}], "diagnostic": "", "acquire_ms": 20.28915, "process_ms": 87.150919, "materialize_ms": 65.837638, "consume_ms": 21.313281}
{"case": "unicode-8MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 116.543477, "rss_kib": 71736, "marks": [{"phase": 0, "ns": 191191813141084}, {"phase": 1, "ns": 191191832724928}, {"phase": 2, "ns": 191191901067873}, {"phase": 3, "ns": 191191922681923}], "diagnostic": "", "acquire_ms": 19.583844, "process_ms": 89.956995, "materialize_ms": 68.342945, "consume_ms": 21.61405}
{"case": "unicode-8MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 118.207599, "rss_kib": 71828, "marks": [{"phase": 0, "ns": 191191929993776}, {"phase": 1, "ns": 191191948412663}, {"phase": 2, "ns": 191192019402593}, {"phase": 3, "ns": 191192042070861}], "diagnostic": "", "acquire_ms": 18.418887, "process_ms": 93.658198, "materialize_ms": 70.98993, "consume_ms": 22.668268}
{"case": "unicode-8MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 113.401473, "rss_kib": 71896, "marks": [{"phase": 0, "ns": 191192048194222}, {"phase": 1, "ns": 191192067858889}, {"phase": 2, "ns": 191192133782971}, {"phase": 3, "ns": 191192155334392}], "diagnostic": "", "acquire_ms": 19.664667, "process_ms": 87.475503, "materialize_ms": 65.924082, "consume_ms": 21.551421}
{"case": "unicode-8MiB-io-materialize", "lane": "candidate", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 1141.912998, "rss_kib": 727180, "marks": [{"phase": 0, "ns": 10454187}, {"phase": 1, "ns": 443516418}, {"phase": 2, "ns": 743802558}, {"phase": 3, "ns": 1091769976}], "diagnostic": "", "acquire_ms": 433.062231, "process_ms": 648.253558, "materialize_ms": 300.28614, "consume_ms": 347.967418}
{"case": "unicode-8MiB-io-materialize", "lane": "candidate", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 1130.68278, "rss_kib": 715312, "marks": [{"phase": 0, "ns": 9179432}, {"phase": 1, "ns": 428121681}, {"phase": 2, "ns": 727919525}, {"phase": 3, "ns": 1081123715}], "diagnostic": "", "acquire_ms": 418.942249, "process_ms": 653.002034, "materialize_ms": 299.797844, "consume_ms": 353.20419}
{"case": "unicode-8MiB-io-materialize", "lane": "candidate", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 1162.127726, "rss_kib": 712444, "marks": [{"phase": 0, "ns": 9633752}, {"phase": 1, "ns": 446896090}, {"phase": 2, "ns": 756870877}, {"phase": 3, "ns": 1119224621}], "diagnostic": "", "acquire_ms": 437.262338, "process_ms": 672.328531, "materialize_ms": 309.974787, "consume_ms": 362.353744}
{"case": "unicode-8MiB-io-materialize", "lane": "candidate", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 1162.773942, "rss_kib": 715368, "marks": [{"phase": 0, "ns": 10258727}, {"phase": 1, "ns": 446185755}, {"phase": 2, "ns": 748741906}, {"phase": 3, "ns": 1110800000}], "diagnostic": "", "acquire_ms": 435.927028, "process_ms": 664.614245, "materialize_ms": 302.556151, "consume_ms": 362.058094}
{"case": "unicode-8MiB-io-materialize", "lane": "candidate", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 1146.650754, "rss_kib": 710252, "marks": [{"phase": 0, "ns": 9707983}, {"phase": 1, "ns": 439083178}, {"phase": 2, "ns": 738537142}, {"phase": 3, "ns": 1095882107}], "diagnostic": "", "acquire_ms": 429.375195, "process_ms": 656.798929, "materialize_ms": 299.453964, "consume_ms": 357.344965}
{"case": "unicode-8MiB-io-materialize", "lane": "candidate", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 1199.267573, "rss_kib": 720448, "marks": [{"phase": 0, "ns": 9391053}, {"phase": 1, "ns": 449717016}, {"phase": 2, "ns": 762651249}, {"phase": 3, "ns": 1149210254}], "diagnostic": "", "acquire_ms": 440.325963, "process_ms": 699.493238, "materialize_ms": 312.934233, "consume_ms": 386.559005}
{"case": "unicode-8MiB-io-materialize", "lane": "candidate", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 1137.220477, "rss_kib": 711912, "marks": [{"phase": 0, "ns": 9913733}, {"phase": 1, "ns": 432852864}, {"phase": 2, "ns": 736584732}, {"phase": 3, "ns": 1088829124}], "diagnostic": "", "acquire_ms": 422.939131, "process_ms": 655.97626, "materialize_ms": 303.731868, "consume_ms": 352.244392}
{"case": "unicode-8MiB-io-materialize", "lane": "candidate", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 1175.547712, "rss_kib": 719504, "marks": [{"phase": 0, "ns": 9317533}, {"phase": 1, "ns": 459804116}, {"phase": 2, "ns": 769947051}, {"phase": 3, "ns": 1123831870}], "diagnostic": "", "acquire_ms": 450.486583, "process_ms": 664.027754, "materialize_ms": 310.142935, "consume_ms": 353.884819}
{"case": "unicode-8MiB-io-materialize", "lane": "candidate", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "1048576:3225742726", "wall_ms": 131.109674, "rss_kib": 71536, "marks": [{"phase": 0, "ns": 191201419750191, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": 0}, {"phase": 1, "ns": 191201439501863, "allocs": 40, "frees": 34, "live": 33554488, "peak": 33554536, "copy_cells": 0}, {"phase": 2, "ns": 191201514212732, "allocs": 9786755, "frees": 5592448, "live": 83886104, "peak": 83886120, "copy_cells": 0}, {"phase": 3, "ns": 191201544144201, "allocs": 13282017, "frees": 13282015, "live": 32, "peak": 83886136, "copy_cells": 0}], "diagnostic": "", "acquire_ms": 19.751672, "process_ms": 104.642338, "materialize_ms": 74.710869, "consume_ms": 29.931469}
{"case": "unicode-64MiB-io-scan", "lane": "base", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 1046.753015, "rss_kib": 722804, "marks": [{"phase": 0, "ns": 191202879762838}, {"phase": 1, "ns": 191203213186291}, {"phase": 3, "ns": 191203884305080}], "diagnostic": "", "acquire_ms": 333.423453, "process_ms": 671.118789}
{"case": "unicode-64MiB-io-scan", "lane": "base", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 1031.524844, "rss_kib": 722948, "marks": [{"phase": 0, "ns": 191203926555849}, {"phase": 1, "ns": 191204262683635}, {"phase": 3, "ns": 191204918179935}], "diagnostic": "", "acquire_ms": 336.127786, "process_ms": 655.4963}
{"case": "unicode-64MiB-io-scan", "lane": "base", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 1029.941613, "rss_kib": 722480, "marks": [{"phase": 0, "ns": 191204958190020}, {"phase": 1, "ns": 191205291694285}, {"phase": 3, "ns": 191205945029661}], "diagnostic": "", "acquire_ms": 333.504265, "process_ms": 653.335376}
{"case": "unicode-64MiB-io-scan", "lane": "base", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 1043.407757, "rss_kib": 722792, "marks": [{"phase": 0, "ns": 191205988519578}, {"phase": 1, "ns": 191206326211768}, {"phase": 3, "ns": 191206983444919}], "diagnostic": "", "acquire_ms": 337.69219, "process_ms": 657.233151}
{"case": "unicode-64MiB-io-scan", "lane": "base", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 1054.380577, "rss_kib": 722660, "marks": [{"phase": 0, "ns": 191207031892980}, {"phase": 1, "ns": 191207373688735}, {"phase": 3, "ns": 191208038494222}], "diagnostic": "", "acquire_ms": 341.795755, "process_ms": 664.805487}
{"case": "unicode-64MiB-io-scan", "lane": "base", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 1030.111346, "rss_kib": 722860, "marks": [{"phase": 0, "ns": 191208086522117}, {"phase": 1, "ns": 191208420236251}, {"phase": 3, "ns": 191209069987205}], "diagnostic": "", "acquire_ms": 333.714134, "process_ms": 649.750954}
{"case": "unicode-64MiB-io-scan", "lane": "base", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 1050.722837, "rss_kib": 723044, "marks": [{"phase": 0, "ns": 191209116854702}, {"phase": 1, "ns": 191209465652974}, {"phase": 3, "ns": 191210121514826}], "diagnostic": "", "acquire_ms": 348.798272, "process_ms": 655.861852}
{"case": "unicode-64MiB-io-scan", "lane": "base", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 1066.735675, "rss_kib": 722612, "marks": [{"phase": 0, "ns": 191210167771686}, {"phase": 1, "ns": 191210517694499}, {"phase": 3, "ns": 191211189034557}], "diagnostic": "", "acquire_ms": 349.922813, "process_ms": 671.340058}
{"case": "unicode-64MiB-io-scan", "lane": "base", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 1527.045099, "rss_kib": 722740, "marks": [{"phase": 0, "ns": 191211234726195, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": null}, {"phase": 1, "ns": 191211570616221, "allocs": 41943077, "frees": 34, "live": 671088680, "peak": 671088728, "copy_cells": null}, {"phase": 3, "ns": 191212713748689, "allocs": 148209710, "frees": 148209708, "live": 32, "peak": 671150096, "copy_cells": null}], "diagnostic": "", "acquire_ms": 335.890026, "process_ms": 1143.132468}
{"case": "unicode-64MiB-io-scan", "lane": "candidate", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 783.769911, "rss_kib": 231472, "marks": [{"phase": 0, "ns": 191213905673801}, {"phase": 1, "ns": 191214071294360}, {"phase": 3, "ns": 191214678634001}], "diagnostic": "", "acquire_ms": 165.620559, "process_ms": 607.339641}
{"case": "unicode-64MiB-io-scan", "lane": "candidate", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 773.89434, "rss_kib": 231088, "marks": [{"phase": 0, "ns": 191214689857736}, {"phase": 1, "ns": 191214847666364}, {"phase": 3, "ns": 191215451642212}], "diagnostic": "", "acquire_ms": 157.808628, "process_ms": 603.975848}
{"case": "unicode-64MiB-io-scan", "lane": "candidate", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 777.292528, "rss_kib": 231208, "marks": [{"phase": 0, "ns": 191215463782393}, {"phase": 1, "ns": 191215619323555}, {"phase": 3, "ns": 191216228017893}], "diagnostic": "", "acquire_ms": 155.541162, "process_ms": 608.694338}
{"case": "unicode-64MiB-io-scan", "lane": "candidate", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 775.262823, "rss_kib": 231336, "marks": [{"phase": 0, "ns": 191216241231598}, {"phase": 1, "ns": 191216401158610}, {"phase": 3, "ns": 191217002930172}], "diagnostic": "", "acquire_ms": 159.927012, "process_ms": 601.771562}
{"case": "unicode-64MiB-io-scan", "lane": "candidate", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 768.867015, "rss_kib": 231024, "marks": [{"phase": 0, "ns": 191217016844885}, {"phase": 1, "ns": 191217171784117}, {"phase": 3, "ns": 191217773187200}], "diagnostic": "", "acquire_ms": 154.939232, "process_ms": 601.403083}
{"case": "unicode-64MiB-io-scan", "lane": "candidate", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 797.876878, "rss_kib": 231352, "marks": [{"phase": 0, "ns": 191217785835674}, {"phase": 1, "ns": 191217950339027}, {"phase": 3, "ns": 191218570286124}], "diagnostic": "", "acquire_ms": 164.503353, "process_ms": 619.947097}
{"case": "unicode-64MiB-io-scan", "lane": "candidate", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 741.669887, "rss_kib": 231340, "marks": [{"phase": 0, "ns": 191218584006479}, {"phase": 1, "ns": 191218734888123}, {"phase": 3, "ns": 191219312037054}], "diagnostic": "", "acquire_ms": 150.881644, "process_ms": 577.148931}
{"case": "unicode-64MiB-io-scan", "lane": "candidate", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 822.237202, "rss_kib": 231528, "marks": [{"phase": 0, "ns": 191219325768961}, {"phase": 1, "ns": 191219480518784}, {"phase": 3, "ns": 191220133866273}], "diagnostic": "", "acquire_ms": 154.749823, "process_ms": 653.347489}
{"case": "unicode-64MiB-io-scan", "lane": "candidate", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 870.20884, "rss_kib": 231080, "marks": [{"phase": 0, "ns": 191220148390461, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": 0}, {"phase": 1, "ns": 191220315277820, "allocs": 40, "frees": 34, "live": 268435512, "peak": 268435560, "copy_cells": 0}, {"phase": 3, "ns": 191221004353150, "allocs": 106299439, "frees": 106299437, "live": 32, "peak": 268472384, "copy_cells": 0}], "diagnostic": "", "acquire_ms": 166.887359, "process_ms": 689.07533}
{"case": "unicode-64MiB-construct-scan", "lane": "base", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 2489.155613, "rss_kib": 1640680, "marks": [{"phase": 0, "ns": 191222263711572}, {"phase": 1, "ns": 191223362744558}, {"phase": 3, "ns": 191224656162255}], "diagnostic": "", "acquire_ms": 1099.032986, "process_ms": 1293.417697}
{"case": "unicode-64MiB-construct-scan", "lane": "base", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 2460.853246, "rss_kib": 1640040, "marks": [{"phase": 0, "ns": 191224753041515}, {"phase": 1, "ns": 191225822760442}, {"phase": 3, "ns": 191227112229383}], "diagnostic": "", "acquire_ms": 1069.718927, "process_ms": 1289.468941}
{"case": "unicode-64MiB-construct-scan", "lane": "base", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 2472.832061, "rss_kib": 1639860, "marks": [{"phase": 0, "ns": 191227214050777}, {"phase": 1, "ns": 191228313923525}, {"phase": 3, "ns": 191229579759460}], "diagnostic": "", "acquire_ms": 1099.872748, "process_ms": 1265.835935}
{"case": "unicode-64MiB-construct-scan", "lane": "base", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 2462.521607, "rss_kib": 1640632, "marks": [{"phase": 0, "ns": 191229687140267}, {"phase": 1, "ns": 191230773643944}, {"phase": 3, "ns": 191232049663784}], "diagnostic": "", "acquire_ms": 1086.503677, "process_ms": 1276.01984}
{"case": "unicode-64MiB-construct-scan", "lane": "base", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 2500.677357, "rss_kib": 1640184, "marks": [{"phase": 0, "ns": 191232150007108}, {"phase": 1, "ns": 191233252752357}, {"phase": 3, "ns": 191234544219754}], "diagnostic": "", "acquire_ms": 1102.745249, "process_ms": 1291.467397}
{"case": "unicode-64MiB-construct-scan", "lane": "base", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 2478.629425, "rss_kib": 1640052, "marks": [{"phase": 0, "ns": 191234650792981}, {"phase": 1, "ns": 191235750917865}, {"phase": 3, "ns": 191237024391511}], "diagnostic": "", "acquire_ms": 1100.124884, "process_ms": 1273.473646}
{"case": "unicode-64MiB-construct-scan", "lane": "base", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 2462.847795, "rss_kib": 1640040, "marks": [{"phase": 0, "ns": 191237129522625}, {"phase": 1, "ns": 191238210095366}, {"phase": 3, "ns": 191239490356141}], "diagnostic": "", "acquire_ms": 1080.572741, "process_ms": 1280.260775}
{"case": "unicode-64MiB-construct-scan", "lane": "base", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 2472.436922, "rss_kib": 1640624, "marks": [{"phase": 0, "ns": 191239592510174}, {"phase": 1, "ns": 191240669192354}, {"phase": 3, "ns": 191241957465850}], "diagnostic": "", "acquire_ms": 1076.68218, "process_ms": 1288.273496}
{"case": "unicode-64MiB-construct-scan", "lane": "base", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 3354.445377, "rss_kib": 1640568, "marks": [{"phase": 0, "ns": 191242065213561, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": null}, {"phase": 1, "ns": 191243371012421, "allocs": 167772130, "frees": 83886068, "live": 1006632744, "peak": 1006632760, "copy_cells": null}, {"phase": 3, "ns": 191245310623608, "allocs": 416634181, "frees": 416634179, "live": 32, "peak": 1006724872, "copy_cells": null}], "diagnostic": "", "acquire_ms": 1305.79886, "process_ms": 1939.611187}
{"case": "unicode-64MiB-construct-scan", "lane": "candidate", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 702.145493, "rss_kib": 165928, "marks": [{"phase": 0, "ns": 191246513865110}, {"phase": 1, "ns": 191246576500400}, {"phase": 3, "ns": 191247204529140}], "diagnostic": "", "acquire_ms": 62.63529, "process_ms": 628.02874}
{"case": "unicode-64MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 682.54657, "rss_kib": 165964, "marks": [{"phase": 0, "ns": 191247216272118}, {"phase": 1, "ns": 191247284030064}, {"phase": 3, "ns": 191247886050778}], "diagnostic": "", "acquire_ms": 67.757946, "process_ms": 602.020714}
{"case": "unicode-64MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 697.797646, "rss_kib": 165996, "marks": [{"phase": 0, "ns": 191247898975315}, {"phase": 1, "ns": 191247969417026}, {"phase": 3, "ns": 191248584877363}], "diagnostic": "", "acquire_ms": 70.441711, "process_ms": 615.460337}
{"case": "unicode-64MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 721.633715, "rss_kib": 165932, "marks": [{"phase": 0, "ns": 191248597141178}, {"phase": 1, "ns": 191248674612627}, {"phase": 3, "ns": 191249304344594}], "diagnostic": "", "acquire_ms": 77.471449, "process_ms": 629.731967}
{"case": "unicode-64MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 711.880948, "rss_kib": 165936, "marks": [{"phase": 0, "ns": 191249318937903}, {"phase": 1, "ns": 191249389588639}, {"phase": 3, "ns": 191250017468677}], "diagnostic": "", "acquire_ms": 70.650736, "process_ms": 627.880038}
{"case": "unicode-64MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 711.915132, "rss_kib": 166064, "marks": [{"phase": 0, "ns": 191250031330650}, {"phase": 1, "ns": 191250100083251}, {"phase": 3, "ns": 191250726383715}], "diagnostic": "", "acquire_ms": 68.752601, "process_ms": 626.300464}
{"case": "unicode-64MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 697.565866, "rss_kib": 166120, "marks": [{"phase": 0, "ns": 191250743351904}, {"phase": 1, "ns": 191250811978235}, {"phase": 3, "ns": 191251428955415}], "diagnostic": "", "acquire_ms": 68.626331, "process_ms": 616.97718}
{"case": "unicode-64MiB-construct-scan", "lane": "candidate", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 733.086685, "rss_kib": 165996, "marks": [{"phase": 0, "ns": 191251440813933}, {"phase": 1, "ns": 191251509596300}, {"phase": 3, "ns": 191252158433604}], "diagnostic": "", "acquire_ms": 68.782367, "process_ms": 648.837304}
{"case": "unicode-64MiB-construct-scan", "lane": "candidate", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 818.123868, "rss_kib": 165752, "marks": [{"phase": 0, "ns": 191252174183794, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": 0}, {"phase": 1, "ns": 191252244991027, "allocs": 17, "frees": 11, "live": 268435512, "peak": 268435528, "copy_cells": 41943041}, {"phase": 3, "ns": 191252979012253, "allocs": 106299416, "frees": 106299414, "live": 32, "peak": 268472384, "copy_cells": 41943041}], "diagnostic": "", "acquire_ms": 70.807233, "process_ms": 734.021226}
{"case": "unicode-64MiB-io-materialize", "lane": "base", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 1254.045596, "rss_kib": 1640112, "marks": [{"phase": 0, "ns": 191254298349914}, {"phase": 1, "ns": 191254653062371}, {"phase": 2, "ns": 191255411029284}, {"phase": 3, "ns": 191255449919296}], "diagnostic": "", "acquire_ms": 354.712457, "process_ms": 796.856925, "materialize_ms": 757.966913, "consume_ms": 38.890012}
{"case": "unicode-64MiB-io-materialize", "lane": "base", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 1227.300184, "rss_kib": 1640528, "marks": [{"phase": 0, "ns": 191255552307744}, {"phase": 1, "ns": 191255886084356}, {"phase": 2, "ns": 191256640747650}, {"phase": 3, "ns": 191256680972912}], "diagnostic": "", "acquire_ms": 333.776612, "process_ms": 794.888556, "materialize_ms": 754.663294, "consume_ms": 40.225262}
{"case": "unicode-64MiB-io-materialize", "lane": "base", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 1222.679459, "rss_kib": 1640612, "marks": [{"phase": 0, "ns": 191256779618498}, {"phase": 1, "ns": 191257121611587}, {"phase": 2, "ns": 191257864990692}, {"phase": 3, "ns": 191257906526086}], "diagnostic": "", "acquire_ms": 341.993089, "process_ms": 784.914499, "materialize_ms": 743.379105, "consume_ms": 41.535394}
{"case": "unicode-64MiB-io-materialize", "lane": "base", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 1223.71983, "rss_kib": 1640060, "marks": [{"phase": 0, "ns": 191258002587056}, {"phase": 1, "ns": 191258332953256}, {"phase": 2, "ns": 191259083936458}, {"phase": 3, "ns": 191259124033797}], "diagnostic": "", "acquire_ms": 330.3662, "process_ms": 791.080541, "materialize_ms": 750.983202, "consume_ms": 40.097339}
{"case": "unicode-64MiB-io-materialize", "lane": "base", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 1233.701623, "rss_kib": 1639776, "marks": [{"phase": 0, "ns": 191259226644647}, {"phase": 1, "ns": 191259572442464}, {"phase": 2, "ns": 191260321320938}, {"phase": 3, "ns": 191260359634568}], "diagnostic": "", "acquire_ms": 345.797817, "process_ms": 787.192104, "materialize_ms": 748.878474, "consume_ms": 38.31363}
{"case": "unicode-64MiB-io-materialize", "lane": "base", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 1231.339167, "rss_kib": 1640576, "marks": [{"phase": 0, "ns": 191260460541138}, {"phase": 1, "ns": 191260807181582}, {"phase": 2, "ns": 191261544728026}, {"phase": 3, "ns": 191261584922791}], "diagnostic": "", "acquire_ms": 346.640444, "process_ms": 777.741209, "materialize_ms": 737.546444, "consume_ms": 40.194765}
{"case": "unicode-64MiB-io-materialize", "lane": "base", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 1202.212222, "rss_kib": 1640196, "marks": [{"phase": 0, "ns": 191261692209158}, {"phase": 1, "ns": 191262027356086}, {"phase": 2, "ns": 191262760495090}, {"phase": 3, "ns": 191262799080956}], "diagnostic": "", "acquire_ms": 335.146928, "process_ms": 771.72487, "materialize_ms": 733.139004, "consume_ms": 38.585866}
{"case": "unicode-64MiB-io-materialize", "lane": "base", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 1238.638887, "rss_kib": 1640324, "marks": [{"phase": 0, "ns": 191262894301463}, {"phase": 1, "ns": 191263221332174}, {"phase": 2, "ns": 191263992364672}, {"phase": 3, "ns": 191264035072056}], "diagnostic": "", "acquire_ms": 327.030711, "process_ms": 813.739882, "materialize_ms": 771.032498, "consume_ms": 42.707384}
{"case": "unicode-64MiB-io-materialize", "lane": "base", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 1646.722943, "rss_kib": 1639944, "marks": [{"phase": 0, "ns": 191264133555956, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": null}, {"phase": 1, "ns": 191264478166404, "allocs": 41943077, "frees": 34, "live": 671088680, "peak": 671088728, "copy_cells": null}, {"phase": 2, "ns": 191265621156382, "allocs": 106255747, "frees": 75497515, "live": 492131704, "peak": 671088712, "copy_cells": null}, {"phase": 3, "ns": 191265680720103, "allocs": 106255753, "frees": 106255751, "live": 32, "peak": 492131736, "copy_cells": null}], "diagnostic": "", "acquire_ms": 344.610448, "process_ms": 1202.553699, "materialize_ms": 1142.989978, "consume_ms": 59.563721}
{"case": "unicode-64MiB-io-materialize", "lane": "candidate", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 889.89088, "rss_kib": 559164, "marks": [{"phase": 0, "ns": 191266874429415}, {"phase": 1, "ns": 191267033531163}, {"phase": 2, "ns": 191267554311076}, {"phase": 3, "ns": 191267723409815}], "diagnostic": "", "acquire_ms": 159.101748, "process_ms": 689.878652, "materialize_ms": 520.779913, "consume_ms": 169.098739}
{"case": "unicode-64MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 921.223684, "rss_kib": 558852, "marks": [{"phase": 0, "ns": 191267764510435}, {"phase": 1, "ns": 191267919545038}, {"phase": 2, "ns": 191268461438423}, {"phase": 3, "ns": 191268641549806}], "diagnostic": "", "acquire_ms": 155.034603, "process_ms": 722.004768, "materialize_ms": 541.893385, "consume_ms": 180.111383}
{"case": "unicode-64MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 916.022239, "rss_kib": 558940, "marks": [{"phase": 0, "ns": 191268685850329}, {"phase": 1, "ns": 191268840790052}, {"phase": 2, "ns": 191269387866898}, {"phase": 3, "ns": 191269558551241}], "diagnostic": "", "acquire_ms": 154.939723, "process_ms": 717.761189, "materialize_ms": 547.076846, "consume_ms": 170.684343}
{"case": "unicode-64MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 930.038525, "rss_kib": 559028, "marks": [{"phase": 0, "ns": 191269602127772}, {"phase": 1, "ns": 191269766995945}, {"phase": 2, "ns": 191270319800373}, {"phase": 3, "ns": 191270492177162}], "diagnostic": "", "acquire_ms": 164.868173, "process_ms": 725.181217, "materialize_ms": 552.804428, "consume_ms": 172.376789}
{"case": "unicode-64MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 914.992028, "rss_kib": 559136, "marks": [{"phase": 0, "ns": 191270532489208}, {"phase": 1, "ns": 191270690356828}, {"phase": 2, "ns": 191271231937230}, {"phase": 3, "ns": 191271404535489}], "diagnostic": "", "acquire_ms": 157.86762, "process_ms": 714.178661, "materialize_ms": 541.580402, "consume_ms": 172.598259}
{"case": "unicode-64MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 914.003715, "rss_kib": 558708, "marks": [{"phase": 0, "ns": 191271447598187}, {"phase": 1, "ns": 191271602289489}, {"phase": 2, "ns": 191272151282435}, {"phase": 3, "ns": 191272322111733}], "diagnostic": "", "acquire_ms": 154.691302, "process_ms": 719.822244, "materialize_ms": 548.992946, "consume_ms": 170.829298}
{"case": "unicode-64MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 917.781462, "rss_kib": 558492, "marks": [{"phase": 0, "ns": 191272361699316}, {"phase": 1, "ns": 191272513410933}, {"phase": 2, "ns": 191273071173324}, {"phase": 3, "ns": 191273238618660}], "diagnostic": "", "acquire_ms": 151.711617, "process_ms": 725.207727, "materialize_ms": 557.762391, "consume_ms": 167.445336}
{"case": "unicode-64MiB-io-materialize", "lane": "candidate", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 891.306563, "rss_kib": 558724, "marks": [{"phase": 0, "ns": 191273279600285}, {"phase": 1, "ns": 191273441725662}, {"phase": 2, "ns": 191273965224546}, {"phase": 3, "ns": 191274136790299}], "diagnostic": "", "acquire_ms": 162.125377, "process_ms": 695.064637, "materialize_ms": 523.498884, "consume_ms": 171.565753}
{"case": "unicode-64MiB-io-materialize", "lane": "candidate", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "8388608:20207604", "wall_ms": 1005.612269, "rss_kib": 558892, "marks": [{"phase": 0, "ns": 191274171158654, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": 0}, {"phase": 1, "ns": 191274323299234, "allocs": 40, "frees": 34, "live": 268435512, "peak": 268435560, "copy_cells": 0}, {"phase": 2, "ns": 191274918078468, "allocs": 78293721, "frees": 44739286, "live": 671088664, "peak": 671088704, "copy_cells": 0}, {"phase": 3, "ns": 191275139328864, "allocs": 106255755, "frees": 106255753, "live": 32, "peak": 671088696, "copy_cells": 0}], "diagnostic": "", "acquire_ms": 152.14058, "process_ms": 816.02963, "materialize_ms": 594.779234, "consume_ms": 221.250396}
{"case": "retain-8MiB-view", "lane": "base", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 137.386126, "rss_kib": 141488, "marks": [{"phase": 0, "ns": 191276126203853}, {"phase": 1, "ns": 191276189190320}, {"phase": 2, "ns": 191276252622660}, {"phase": 3, "ns": 191276252631757}], "diagnostic": "", "acquire_ms": 62.986467, "process_ms": 63.441437, "materialize_ms": 63.43234, "consume_ms": 0.009097}
{"case": "retain-8MiB-view", "lane": "base", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 135.769753, "rss_kib": 141284, "marks": [{"phase": 0, "ns": 191276263575171}, {"phase": 1, "ns": 191276327227348}, {"phase": 2, "ns": 191276389668210}, {"phase": 3, "ns": 191276389679682}], "diagnostic": "", "acquire_ms": 63.652177, "process_ms": 62.452334, "materialize_ms": 62.440862, "consume_ms": 0.011472}
{"case": "retain-8MiB-view", "lane": "base", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 133.485005, "rss_kib": 141420, "marks": [{"phase": 0, "ns": 191276399823070}, {"phase": 1, "ns": 191276460230800}, {"phase": 2, "ns": 191276523889490}, {"phase": 3, "ns": 191276523899579}], "diagnostic": "", "acquire_ms": 60.40773, "process_ms": 63.668779, "materialize_ms": 63.65869, "consume_ms": 0.010089}
{"case": "retain-8MiB-view", "lane": "base", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 133.569644, "rss_kib": 141488, "marks": [{"phase": 0, "ns": 191276533381013}, {"phase": 1, "ns": 191276594587286}, {"phase": 2, "ns": 191276657107268}, {"phase": 3, "ns": 191276657116285}], "diagnostic": "", "acquire_ms": 61.206273, "process_ms": 62.528999, "materialize_ms": 62.519982, "consume_ms": 0.009017}
{"case": "retain-8MiB-view", "lane": "base", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 133.240922, "rss_kib": 141300, "marks": [{"phase": 0, "ns": 191276667128875}, {"phase": 1, "ns": 191276726557901}, {"phase": 2, "ns": 191276789231815}, {"phase": 3, "ns": 191276789242004}], "diagnostic": "", "acquire_ms": 59.429026, "process_ms": 62.684103, "materialize_ms": 62.673914, "consume_ms": 0.010189}
{"case": "retain-8MiB-view", "lane": "base", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 134.834081, "rss_kib": 141300, "marks": [{"phase": 0, "ns": 191276800492710}, {"phase": 1, "ns": 191276861738768}, {"phase": 2, "ns": 191276924369670}, {"phase": 3, "ns": 191276924381332}], "diagnostic": "", "acquire_ms": 61.246058, "process_ms": 62.642564, "materialize_ms": 62.630902, "consume_ms": 0.011662}
{"case": "retain-8MiB-view", "lane": "base", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 136.279849, "rss_kib": 141480, "marks": [{"phase": 0, "ns": 191276935822629}, {"phase": 1, "ns": 191276997938415}, {"phase": 2, "ns": 191277061319078}, {"phase": 3, "ns": 191277061330429}], "diagnostic": "", "acquire_ms": 62.115786, "process_ms": 63.392014, "materialize_ms": 63.380663, "consume_ms": 0.011351}
{"case": "retain-8MiB-view", "lane": "base", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 133.874993, "rss_kib": 141428, "marks": [{"phase": 0, "ns": 191277072013149}, {"phase": 1, "ns": 191277133350520}, {"phase": 2, "ns": 191277197141050}, {"phase": 3, "ns": 191277197152461}], "diagnostic": "", "acquire_ms": 61.337371, "process_ms": 63.801941, "materialize_ms": 63.79053, "consume_ms": 0.011411}
{"case": "retain-8MiB-view", "lane": "base", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 37.241389, "rss_kib": 69884, "marks": [{"phase": 0, "ns": 8656030}, {"phase": 1, "ns": 25252294}, {"phase": 2, "ns": 29588239}, {"phase": 3, "ns": 29706002}], "diagnostic": "", "acquire_ms": 16.596264, "process_ms": 4.453708, "materialize_ms": 4.335945, "consume_ms": 0.117763}
{"case": "retain-8MiB-view", "lane": "base", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 37.842828, "rss_kib": 70200, "marks": [{"phase": 0, "ns": 9182307}, {"phase": 1, "ns": 26109819}, {"phase": 2, "ns": 30284518}, {"phase": 3, "ns": 30415997}], "diagnostic": "", "acquire_ms": 16.927512, "process_ms": 4.306178, "materialize_ms": 4.174699, "consume_ms": 0.131479}
{"case": "retain-8MiB-view", "lane": "base", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 39.131149, "rss_kib": 70012, "marks": [{"phase": 0, "ns": 8960377}, {"phase": 1, "ns": 28272195}, {"phase": 2, "ns": 31978838}, {"phase": 3, "ns": 32087935}], "diagnostic": "", "acquire_ms": 19.311818, "process_ms": 3.81574, "materialize_ms": 3.706643, "consume_ms": 0.109097}
{"case": "retain-8MiB-view", "lane": "base", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 35.597795, "rss_kib": 70140, "marks": [{"phase": 0, "ns": 8559107}, {"phase": 1, "ns": 24981060}, {"phase": 2, "ns": 28678475}, {"phase": 3, "ns": 28785809}], "diagnostic": "", "acquire_ms": 16.421953, "process_ms": 3.804749, "materialize_ms": 3.697415, "consume_ms": 0.107334}
{"case": "retain-8MiB-view", "lane": "base", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 38.459256, "rss_kib": 70124, "marks": [{"phase": 0, "ns": 10188623}, {"phase": 1, "ns": 27185827}, {"phase": 2, "ns": 31216533}, {"phase": 3, "ns": 31349836}], "diagnostic": "", "acquire_ms": 16.997204, "process_ms": 4.164009, "materialize_ms": 4.030706, "consume_ms": 0.133303}
{"case": "retain-8MiB-view", "lane": "base", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 38.113461, "rss_kib": 70248, "marks": [{"phase": 0, "ns": 9864790}, {"phase": 1, "ns": 27146282}, {"phase": 2, "ns": 30818128}, {"phase": 3, "ns": 30930812}], "diagnostic": "", "acquire_ms": 17.281492, "process_ms": 3.78453, "materialize_ms": 3.671846, "consume_ms": 0.112684}
{"case": "retain-8MiB-view", "lane": "base", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 38.879312, "rss_kib": 69996, "marks": [{"phase": 0, "ns": 9692744}, {"phase": 1, "ns": 27940877}, {"phase": 2, "ns": 31943230}, {"phase": 3, "ns": 32055743}], "diagnostic": "", "acquire_ms": 18.248133, "process_ms": 4.114866, "materialize_ms": 4.002353, "consume_ms": 0.112513}
{"case": "retain-8MiB-view", "lane": "base", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 39.176636, "rss_kib": 69844, "marks": [{"phase": 0, "ns": 9458249}, {"phase": 1, "ns": 27113209}, {"phase": 2, "ns": 31361949}, {"phase": 3, "ns": 31475153}], "diagnostic": "", "acquire_ms": 17.65496, "process_ms": 4.361944, "materialize_ms": 4.24874, "consume_ms": 0.113204}
{"case": "retain-8MiB-view", "lane": "base", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 134.346947, "rss_kib": 141412, "marks": [{"phase": 0, "ns": 191277512419174, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": null}, {"phase": 1, "ns": 191277575573177, "allocs": 8388644, "frees": 34, "live": 134217752, "peak": 134217800, "copy_cells": null}, {"phase": 2, "ns": 191277636312836, "allocs": 8388653, "frees": 8388648, "live": 72, "peak": 134217784, "copy_cells": null}, {"phase": 3, "ns": 191277636325981, "allocs": 8388659, "frees": 8388657, "live": 32, "peak": 104, "copy_cells": null}], "diagnostic": "", "acquire_ms": 63.154003, "process_ms": 60.752804, "materialize_ms": 60.739659, "consume_ms": 0.013145}
{"case": "retain-8MiB-view", "lane": "candidate", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 26.522159, "rss_kib": 43184, "marks": [{"phase": 0, "ns": 191278590552423}, {"phase": 1, "ns": 191278612574967}, {"phase": 2, "ns": 191278612582161}, {"phase": 3, "ns": 191278612584094}], "diagnostic": "", "acquire_ms": 22.022544, "process_ms": 0.009127, "materialize_ms": 0.007194, "consume_ms": 0.001933}
{"case": "retain-8MiB-view", "lane": "candidate", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 24.865942, "rss_kib": 43000, "marks": [{"phase": 0, "ns": 191278617297905}, {"phase": 1, "ns": 191278637792565}, {"phase": 2, "ns": 191278637799648}, {"phase": 3, "ns": 191278637801612}], "diagnostic": "", "acquire_ms": 20.49466, "process_ms": 0.009047, "materialize_ms": 0.007083, "consume_ms": 0.001964}
{"case": "retain-8MiB-view", "lane": "candidate", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 26.327801, "rss_kib": 43256, "marks": [{"phase": 0, "ns": 191278642267413}, {"phase": 1, "ns": 191278664028212}, {"phase": 2, "ns": 191278664034514}, {"phase": 3, "ns": 191278664036357}], "diagnostic": "", "acquire_ms": 21.760799, "process_ms": 0.008145, "materialize_ms": 0.006302, "consume_ms": 0.001843}
{"case": "retain-8MiB-view", "lane": "candidate", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 26.148752, "rss_kib": 43056, "marks": [{"phase": 0, "ns": 191278668730020}, {"phase": 1, "ns": 191278690457956}, {"phase": 2, "ns": 191278690465140}, {"phase": 3, "ns": 191278690467164}], "diagnostic": "", "acquire_ms": 21.727936, "process_ms": 0.009208, "materialize_ms": 0.007184, "consume_ms": 0.002024}
{"case": "retain-8MiB-view", "lane": "candidate", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 25.818136, "rss_kib": 42936, "marks": [{"phase": 0, "ns": 191278695146630}, {"phase": 1, "ns": 191278716823800}, {"phase": 2, "ns": 191278716830863}, {"phase": 3, "ns": 191278716833077}], "diagnostic": "", "acquire_ms": 21.67717, "process_ms": 0.009277, "materialize_ms": 0.007063, "consume_ms": 0.002214}
{"case": "retain-8MiB-view", "lane": "candidate", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 26.294087, "rss_kib": 42872, "marks": [{"phase": 0, "ns": 191278721122294}, {"phase": 1, "ns": 191278743373532}, {"phase": 2, "ns": 191278743379623}, {"phase": 3, "ns": 191278743381467}], "diagnostic": "", "acquire_ms": 22.251238, "process_ms": 0.007935, "materialize_ms": 0.006091, "consume_ms": 0.001844}
{"case": "retain-8MiB-view", "lane": "candidate", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 26.442839, "rss_kib": 43064, "marks": [{"phase": 0, "ns": 191278747524075}, {"phase": 1, "ns": 191278769538084}, {"phase": 2, "ns": 191278769544526}, {"phase": 3, "ns": 191278769546920}], "diagnostic": "", "acquire_ms": 22.014009, "process_ms": 0.008836, "materialize_ms": 0.006442, "consume_ms": 0.002394}
{"case": "retain-8MiB-view", "lane": "candidate", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 26.768236, "rss_kib": 43120, "marks": [{"phase": 0, "ns": 191278774134081}, {"phase": 1, "ns": 191278796697721}, {"phase": 2, "ns": 191278796704454}, {"phase": 3, "ns": 191278796707159}], "diagnostic": "", "acquire_ms": 22.56364, "process_ms": 0.009438, "materialize_ms": 0.006733, "consume_ms": 0.002705}
{"case": "retain-8MiB-view", "lane": "candidate", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 381.242652, "rss_kib": 328288, "marks": [{"phase": 0, "ns": 10618488}, {"phase": 1, "ns": 353953630}, {"phase": 2, "ns": 354052397}, {"phase": 3, "ns": 354161283}], "diagnostic": "", "acquire_ms": 343.335142, "process_ms": 0.207653, "materialize_ms": 0.098767, "consume_ms": 0.108886}
{"case": "retain-8MiB-view", "lane": "candidate", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 352.864135, "rss_kib": 328576, "marks": [{"phase": 0, "ns": 9159114}, {"phase": 1, "ns": 328286821}, {"phase": 2, "ns": 328388794}, {"phase": 3, "ns": 328489655}], "diagnostic": "", "acquire_ms": 319.127707, "process_ms": 0.202834, "materialize_ms": 0.101973, "consume_ms": 0.100861}
{"case": "retain-8MiB-view", "lane": "candidate", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 361.562465, "rss_kib": 327940, "marks": [{"phase": 0, "ns": 9086345}, {"phase": 1, "ns": 337738258}, {"phase": 2, "ns": 337854117}, {"phase": 3, "ns": 337955710}], "diagnostic": "", "acquire_ms": 328.651913, "process_ms": 0.217452, "materialize_ms": 0.115859, "consume_ms": 0.101593}
{"case": "retain-8MiB-view", "lane": "candidate", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 390.828113, "rss_kib": 328256, "marks": [{"phase": 0, "ns": 9417072}, {"phase": 1, "ns": 358178234}, {"phase": 2, "ns": 358347234}, {"phase": 3, "ns": 358522095}], "diagnostic": "", "acquire_ms": 348.761162, "process_ms": 0.343861, "materialize_ms": 0.169, "consume_ms": 0.174861}
{"case": "retain-8MiB-view", "lane": "candidate", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 372.201573, "rss_kib": 327988, "marks": [{"phase": 0, "ns": 10191348}, {"phase": 1, "ns": 350541594}, {"phase": 2, "ns": 350659017}, {"phase": 3, "ns": 350753817}], "diagnostic": "", "acquire_ms": 340.350246, "process_ms": 0.212223, "materialize_ms": 0.117423, "consume_ms": 0.0948}
{"case": "retain-8MiB-view", "lane": "candidate", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 381.307334, "rss_kib": 328316, "marks": [{"phase": 0, "ns": 9746445}, {"phase": 1, "ns": 358235341}, {"phase": 2, "ns": 358352313}, {"phase": 3, "ns": 358469024}], "diagnostic": "", "acquire_ms": 348.488896, "process_ms": 0.233683, "materialize_ms": 0.116972, "consume_ms": 0.116711}
{"case": "retain-8MiB-view", "lane": "candidate", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 364.942279, "rss_kib": 328296, "marks": [{"phase": 0, "ns": 10468734}, {"phase": 1, "ns": 341637816}, {"phase": 2, "ns": 341766299}, {"phase": 3, "ns": 341893911}], "diagnostic": "", "acquire_ms": 331.169082, "process_ms": 0.256095, "materialize_ms": 0.128483, "consume_ms": 0.127612}
{"case": "retain-8MiB-view", "lane": "candidate", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 366.88494, "rss_kib": 328020, "marks": [{"phase": 0, "ns": 9820536}, {"phase": 1, "ns": 342405470}, {"phase": 2, "ns": 342557849}, {"phase": 3, "ns": 342738141}], "diagnostic": "", "acquire_ms": 332.584934, "process_ms": 0.332671, "materialize_ms": 0.152379, "consume_ms": 0.180292}
{"case": "retain-8MiB-view", "lane": "candidate", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 29.639956, "rss_kib": 43208, "marks": [{"phase": 0, "ns": 191281774853771, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": 0}, {"phase": 1, "ns": 191281799145505, "allocs": 40, "frees": 34, "live": 33554488, "peak": 33554536, "copy_cells": 0}, {"phase": 2, "ns": 191281799155403, "allocs": 50, "frees": 44, "live": 33554488, "peak": 33554520, "copy_cells": 0}, {"phase": 3, "ns": 191281799159822, "allocs": 60, "frees": 58, "live": 32, "peak": 33554520, "copy_cells": 0}], "diagnostic": "", "acquire_ms": 24.291734, "process_ms": 0.014317, "materialize_ms": 0.009898, "consume_ms": 0.004419}
{"case": "retain-8MiB-copy", "lane": "base", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 140.350321, "rss_kib": 141408, "marks": [{"phase": 0, "ns": 191282854536295}, {"phase": 1, "ns": 191282918623276}, {"phase": 2, "ns": 191282984295380}, {"phase": 3, "ns": 191282984308294}], "diagnostic": "", "acquire_ms": 64.086981, "process_ms": 65.685018, "materialize_ms": 65.672104, "consume_ms": 0.012914}
{"case": "retain-8MiB-copy", "lane": "base", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 136.722708, "rss_kib": 141356, "marks": [{"phase": 0, "ns": 191282994896375}, {"phase": 1, "ns": 191283058134367}, {"phase": 2, "ns": 191283119644506}, {"phase": 3, "ns": 191283119653803}], "diagnostic": "", "acquire_ms": 63.237992, "process_ms": 61.519436, "materialize_ms": 61.510139, "consume_ms": 0.009297}
{"case": "retain-8MiB-copy", "lane": "base", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 134.995606, "rss_kib": 141168, "marks": [{"phase": 0, "ns": 191283132076400}, {"phase": 1, "ns": 191283195074658}, {"phase": 2, "ns": 191283257118818}, {"phase": 3, "ns": 191283257128426}], "diagnostic": "", "acquire_ms": 62.998258, "process_ms": 62.053768, "materialize_ms": 62.04416, "consume_ms": 0.009608}
{"case": "retain-8MiB-copy", "lane": "base", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 138.424553, "rss_kib": 141556, "marks": [{"phase": 0, "ns": 191283266993026}, {"phase": 1, "ns": 191283329474415}, {"phase": 2, "ns": 191283393096465}, {"phase": 3, "ns": 191283393105722}], "diagnostic": "", "acquire_ms": 62.481389, "process_ms": 63.631307, "materialize_ms": 63.62205, "consume_ms": 0.009257}
{"case": "retain-8MiB-copy", "lane": "base", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 144.275558, "rss_kib": 141288, "marks": [{"phase": 0, "ns": 191283405807678}, {"phase": 1, "ns": 191283472332327}, {"phase": 2, "ns": 191283537682892}, {"phase": 3, "ns": 191283537694484}], "diagnostic": "", "acquire_ms": 66.524649, "process_ms": 65.362157, "materialize_ms": 65.350565, "consume_ms": 0.011592}
{"case": "retain-8MiB-copy", "lane": "base", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 136.468647, "rss_kib": 141412, "marks": [{"phase": 0, "ns": 191283550157176}, {"phase": 1, "ns": 191283613141197}, {"phase": 2, "ns": 191283678597823}, {"phase": 3, "ns": 191283678607592}], "diagnostic": "", "acquire_ms": 62.984021, "process_ms": 65.466395, "materialize_ms": 65.456626, "consume_ms": 0.009769}
{"case": "retain-8MiB-copy", "lane": "base", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 139.767277, "rss_kib": 141364, "marks": [{"phase": 0, "ns": 191283686683032}, {"phase": 1, "ns": 191283748434487}, {"phase": 2, "ns": 191283814583044}, {"phase": 3, "ns": 191283814591791}], "diagnostic": "", "acquire_ms": 61.751455, "process_ms": 66.157304, "materialize_ms": 66.148557, "consume_ms": 0.008747}
{"case": "retain-8MiB-copy", "lane": "base", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 132.930283, "rss_kib": 141356, "marks": [{"phase": 0, "ns": 191283826932472}, {"phase": 1, "ns": 191283886623734}, {"phase": 2, "ns": 191283950591129}, {"phase": 3, "ns": 191283950601408}], "diagnostic": "", "acquire_ms": 59.691262, "process_ms": 63.977674, "materialize_ms": 63.967395, "consume_ms": 0.010279}
{"case": "retain-8MiB-copy", "lane": "base", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 34.540171, "rss_kib": 70528, "marks": [{"phase": 0, "ns": 9205882}, {"phase": 1, "ns": 26388126}, {"phase": 2, "ns": 30198455}, {"phase": 3, "ns": 30304907}], "diagnostic": "", "acquire_ms": 17.182244, "process_ms": 3.916781, "materialize_ms": 3.810329, "consume_ms": 0.106452}
{"case": "retain-8MiB-copy", "lane": "base", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 36.871618, "rss_kib": 70644, "marks": [{"phase": 0, "ns": 9285462}, {"phase": 1, "ns": 27547171}, {"phase": 2, "ns": 32601107}, {"phase": 3, "ns": 32742094}], "diagnostic": "", "acquire_ms": 18.261709, "process_ms": 5.194923, "materialize_ms": 5.053936, "consume_ms": 0.140987}
{"case": "retain-8MiB-copy", "lane": "base", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 39.117663, "rss_kib": 70700, "marks": [{"phase": 0, "ns": 9748369}, {"phase": 1, "ns": 26867574}, {"phase": 2, "ns": 31070627}, {"phase": 3, "ns": 31210572}], "diagnostic": "", "acquire_ms": 17.119205, "process_ms": 4.342998, "materialize_ms": 4.203053, "consume_ms": 0.139945}
{"case": "retain-8MiB-copy", "lane": "base", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 38.037026, "rss_kib": 70572, "marks": [{"phase": 0, "ns": 9732399}, {"phase": 1, "ns": 26064563}, {"phase": 2, "ns": 29879891}, {"phase": 3, "ns": 29967878}], "diagnostic": "", "acquire_ms": 16.332164, "process_ms": 3.903315, "materialize_ms": 3.815328, "consume_ms": 0.087987}
{"case": "retain-8MiB-copy", "lane": "base", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 34.312719, "rss_kib": 70840, "marks": [{"phase": 0, "ns": 9166547}, {"phase": 1, "ns": 26100120}, {"phase": 2, "ns": 29938222}, {"phase": 3, "ns": 30034284}], "diagnostic": "", "acquire_ms": 16.933573, "process_ms": 3.934164, "materialize_ms": 3.838102, "consume_ms": 0.096062}
{"case": "retain-8MiB-copy", "lane": "base", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 36.951209, "rss_kib": 70580, "marks": [{"phase": 0, "ns": 9027974}, {"phase": 1, "ns": 25856308}, {"phase": 2, "ns": 29685583}, {"phase": 3, "ns": 29782076}], "diagnostic": "", "acquire_ms": 16.828334, "process_ms": 3.925768, "materialize_ms": 3.829275, "consume_ms": 0.096493}
{"case": "retain-8MiB-copy", "lane": "base", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 37.574359, "rss_kib": 70400, "marks": [{"phase": 0, "ns": 8876778}, {"phase": 1, "ns": 26259301}, {"phase": 2, "ns": 30461543}, {"phase": 3, "ns": 30560972}], "diagnostic": "", "acquire_ms": 17.382523, "process_ms": 4.301671, "materialize_ms": 4.202242, "consume_ms": 0.099429}
{"case": "retain-8MiB-copy", "lane": "base", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 41.515597, "rss_kib": 70708, "marks": [{"phase": 0, "ns": 9024187}, {"phase": 1, "ns": 29345188}, {"phase": 2, "ns": 34021759}, {"phase": 3, "ns": 34111348}], "diagnostic": "", "acquire_ms": 20.321001, "process_ms": 4.76616, "materialize_ms": 4.676571, "consume_ms": 0.089589}
{"case": "retain-8MiB-copy", "lane": "base", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 133.612265, "rss_kib": 141284, "marks": [{"phase": 0, "ns": 191284260451318, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": null}, {"phase": 1, "ns": 191284323260117, "allocs": 8388644, "frees": 34, "live": 134217752, "peak": 134217800, "copy_cells": null}, {"phase": 2, "ns": 191284383678297, "allocs": 8388656, "frees": 8388651, "live": 72, "peak": 134217784, "copy_cells": null}, {"phase": 3, "ns": 191284383689558, "allocs": 8388662, "frees": 8388660, "live": 32, "peak": 104, "copy_cells": null}], "diagnostic": "", "acquire_ms": 62.808799, "process_ms": 60.429441, "materialize_ms": 60.41818, "consume_ms": 0.011261}
{"case": "retain-8MiB-copy", "lane": "candidate", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 25.052034, "rss_kib": 43064, "marks": [{"phase": 0, "ns": 191285388160234}, {"phase": 1, "ns": 191285409436254}, {"phase": 2, "ns": 191285409443999}, {"phase": 3, "ns": 191285409445692}], "diagnostic": "", "acquire_ms": 21.27602, "process_ms": 0.009438, "materialize_ms": 0.007745, "consume_ms": 0.001693}
{"case": "retain-8MiB-copy", "lane": "candidate", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 27.280126, "rss_kib": 43124, "marks": [{"phase": 0, "ns": 191285413417747}, {"phase": 1, "ns": 191285436210240}, {"phase": 2, "ns": 191285436219137}, {"phase": 3, "ns": 191285436221412}], "diagnostic": "", "acquire_ms": 22.792493, "process_ms": 0.011172, "materialize_ms": 0.008897, "consume_ms": 0.002275}
{"case": "retain-8MiB-copy", "lane": "candidate", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 27.153696, "rss_kib": 43064, "marks": [{"phase": 0, "ns": 191285440995557}, {"phase": 1, "ns": 191285462954801}, {"phase": 2, "ns": 191285462961664}, {"phase": 3, "ns": 191285462963237}], "diagnostic": "", "acquire_ms": 21.959244, "process_ms": 0.008436, "materialize_ms": 0.006863, "consume_ms": 0.001573}
{"case": "retain-8MiB-copy", "lane": "candidate", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 25.721282, "rss_kib": 42868, "marks": [{"phase": 0, "ns": 191285468533100}, {"phase": 1, "ns": 191285490217284}, {"phase": 2, "ns": 191285490224317}, {"phase": 3, "ns": 191285490225920}], "diagnostic": "", "acquire_ms": 21.684184, "process_ms": 0.008636, "materialize_ms": 0.007033, "consume_ms": 0.001603}
{"case": "retain-8MiB-copy", "lane": "candidate", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 25.386858, "rss_kib": 43120, "marks": [{"phase": 0, "ns": 191285494267267}, {"phase": 1, "ns": 191285515744719}, {"phase": 2, "ns": 191285515751491}, {"phase": 3, "ns": 191285515753054}], "diagnostic": "", "acquire_ms": 21.477452, "process_ms": 0.008335, "materialize_ms": 0.006772, "consume_ms": 0.001563}
{"case": "retain-8MiB-copy", "lane": "candidate", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 24.935333, "rss_kib": 43244, "marks": [{"phase": 0, "ns": 191285519766889}, {"phase": 1, "ns": 191285540901171}, {"phase": 2, "ns": 191285540907823}, {"phase": 3, "ns": 191285540909446}], "diagnostic": "", "acquire_ms": 21.134282, "process_ms": 0.008275, "materialize_ms": 0.006652, "consume_ms": 0.001623}
{"case": "retain-8MiB-copy", "lane": "candidate", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 27.012128, "rss_kib": 43116, "marks": [{"phase": 0, "ns": 191285544926888}, {"phase": 1, "ns": 191285567868283}, {"phase": 2, "ns": 191285567876599}, {"phase": 3, "ns": 191285567878623}], "diagnostic": "", "acquire_ms": 22.941395, "process_ms": 0.01034, "materialize_ms": 0.008316, "consume_ms": 0.002024}
{"case": "retain-8MiB-copy", "lane": "candidate", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 25.228819, "rss_kib": 43108, "marks": [{"phase": 0, "ns": 191285572382816}, {"phase": 1, "ns": 191285593511898}, {"phase": 2, "ns": 191285593519753}, {"phase": 3, "ns": 191285593521396}], "diagnostic": "", "acquire_ms": 21.129082, "process_ms": 0.009498, "materialize_ms": 0.007855, "consume_ms": 0.001643}
{"case": "retain-8MiB-copy", "lane": "candidate", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 348.287233, "rss_kib": 328292, "marks": [{"phase": 0, "ns": 9041240}, {"phase": 1, "ns": 322709784}, {"phase": 2, "ns": 322834390}, {"phase": 3, "ns": 322928038}], "diagnostic": "", "acquire_ms": 313.668544, "process_ms": 0.218254, "materialize_ms": 0.124606, "consume_ms": 0.093648}
{"case": "retain-8MiB-copy", "lane": "candidate", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 360.754795, "rss_kib": 328048, "marks": [{"phase": 0, "ns": 9332612}, {"phase": 1, "ns": 337231628}, {"phase": 2, "ns": 337344783}, {"phase": 3, "ns": 337458087}], "diagnostic": "", "acquire_ms": 327.899016, "process_ms": 0.226459, "materialize_ms": 0.113155, "consume_ms": 0.113304}
{"case": "retain-8MiB-copy", "lane": "candidate", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 361.009507, "rss_kib": 328120, "marks": [{"phase": 0, "ns": 9622992}, {"phase": 1, "ns": 339530243}, {"phase": 2, "ns": 339628589}, {"phase": 3, "ns": 339717117}], "diagnostic": "", "acquire_ms": 329.907251, "process_ms": 0.186874, "materialize_ms": 0.098346, "consume_ms": 0.088528}
{"case": "retain-8MiB-copy", "lane": "candidate", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 355.654332, "rss_kib": 328324, "marks": [{"phase": 0, "ns": 8962661}, {"phase": 1, "ns": 330507077}, {"phase": 2, "ns": 330721783}, {"phase": 3, "ns": 330900783}], "diagnostic": "", "acquire_ms": 321.544416, "process_ms": 0.393706, "materialize_ms": 0.214706, "consume_ms": 0.179}
{"case": "retain-8MiB-copy", "lane": "candidate", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 356.908638, "rss_kib": 327984, "marks": [{"phase": 0, "ns": 9114819}, {"phase": 1, "ns": 329664130}, {"phase": 2, "ns": 329761375}, {"phase": 3, "ns": 329867506}], "diagnostic": "", "acquire_ms": 320.549311, "process_ms": 0.203376, "materialize_ms": 0.097245, "consume_ms": 0.106131}
{"case": "retain-8MiB-copy", "lane": "candidate", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 383.407985, "rss_kib": 328516, "marks": [{"phase": 0, "ns": 10458054}, {"phase": 1, "ns": 359059533}, {"phase": 2, "ns": 359182236}, {"phase": 3, "ns": 359294208}], "diagnostic": "", "acquire_ms": 348.601479, "process_ms": 0.234675, "materialize_ms": 0.122703, "consume_ms": 0.111972}
{"case": "retain-8MiB-copy", "lane": "candidate", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 359.409095, "rss_kib": 328388, "marks": [{"phase": 0, "ns": 9457819}, {"phase": 1, "ns": 336780693}, {"phase": 2, "ns": 336898807}, {"phase": 3, "ns": 336997754}], "diagnostic": "", "acquire_ms": 327.322874, "process_ms": 0.217061, "materialize_ms": 0.118114, "consume_ms": 0.098947}
{"case": "retain-8MiB-copy", "lane": "candidate", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 363.426287, "rss_kib": 327932, "marks": [{"phase": 0, "ns": 9493798}, {"phase": 1, "ns": 342352380}, {"phase": 2, "ns": 342466176}, {"phase": 3, "ns": 342570173}], "diagnostic": "", "acquire_ms": 332.858582, "process_ms": 0.217793, "materialize_ms": 0.113796, "consume_ms": 0.103997}
{"case": "retain-8MiB-copy", "lane": "candidate", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "3:125497", "wall_ms": 28.55486, "rss_kib": 43124, "marks": [{"phase": 0, "ns": 191288488202773, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": 0}, {"phase": 1, "ns": 191288512112664, "allocs": 40, "frees": 34, "live": 33554488, "peak": 33554536, "copy_cells": 0}, {"phase": 2, "ns": 191288512121150, "allocs": 54, "frees": 48, "live": 72, "peak": 33554520, "copy_cells": 3}, {"phase": 3, "ns": 191288512124095, "allocs": 64, "frees": 62, "live": 32, "peak": 104, "copy_cells": 3}], "diagnostic": "", "acquire_ms": 23.909891, "process_ms": 0.011431, "materialize_ms": 0.008486, "consume_ms": 0.002945}
{"case": "search-32768-512", "lane": "base", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 111.550977, "rss_kib": 3444, "marks": [{"phase": 0, "ns": 191289411174880}, {"phase": 1, "ns": 191289411931904}, {"phase": 3, "ns": 191289520373641}], "diagnostic": "", "acquire_ms": 0.757024, "process_ms": 108.441737}
{"case": "search-32768-512", "lane": "base", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 110.186081, "rss_kib": 3372, "marks": [{"phase": 0, "ns": 191289522893344}, {"phase": 1, "ns": 191289523717576}, {"phase": 3, "ns": 191289630739683}], "diagnostic": "", "acquire_ms": 0.824232, "process_ms": 107.022107}
{"case": "search-32768-512", "lane": "base", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 107.210614, "rss_kib": 3564, "marks": [{"phase": 0, "ns": 191289633471008}, {"phase": 1, "ns": 191289634307052}, {"phase": 3, "ns": 191289738172267}], "diagnostic": "", "acquire_ms": 0.836044, "process_ms": 103.865215}
{"case": "search-32768-512", "lane": "base", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 113.309489, "rss_kib": 3320, "marks": [{"phase": 0, "ns": 191289740503705}, {"phase": 1, "ns": 191289741374645}, {"phase": 3, "ns": 191289851598498}], "diagnostic": "", "acquire_ms": 0.87094, "process_ms": 110.223853}
{"case": "search-32768-512", "lane": "base", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 110.062838, "rss_kib": 3508, "marks": [{"phase": 0, "ns": 191289854216849}, {"phase": 1, "ns": 191289855068813}, {"phase": 3, "ns": 191289961915567}], "diagnostic": "", "acquire_ms": 0.851964, "process_ms": 106.846754}
{"case": "search-32768-512", "lane": "base", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 105.450529, "rss_kib": 3440, "marks": [{"phase": 0, "ns": 191289964293112}, {"phase": 1, "ns": 191289965121321}, {"phase": 3, "ns": 191290067466326}], "diagnostic": "", "acquire_ms": 0.828209, "process_ms": 102.345005}
{"case": "search-32768-512", "lane": "base", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 113.675332, "rss_kib": 3572, "marks": [{"phase": 0, "ns": 191290070139431}, {"phase": 1, "ns": 191290071017404}, {"phase": 3, "ns": 191290181406611}], "diagnostic": "", "acquire_ms": 0.877973, "process_ms": 110.389207}
{"case": "search-32768-512", "lane": "base", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 112.28043, "rss_kib": 3508, "marks": [{"phase": 0, "ns": 191290183925804}, {"phase": 1, "ns": 191290184719818}, {"phase": 3, "ns": 191290293869175}], "diagnostic": "", "acquire_ms": 0.794014, "process_ms": 109.149357}
{"case": "search-32768-512", "lane": "base", "kind": "js", "run": "warm", "status": 1, "correct": false, "stdout": "", "wall_ms": 21.895774, "rss_kib": 51728, "marks": [{"phase": 0, "ns": 8995333}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "search-32768-512", "lane": "base", "kind": "js", "run": 1, "status": 1, "correct": false, "stdout": "", "wall_ms": 21.384316, "rss_kib": 51720, "marks": [{"phase": 0, "ns": 8584775}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "search-32768-512", "lane": "base", "kind": "js", "run": 2, "status": 1, "correct": false, "stdout": "", "wall_ms": 21.517808, "rss_kib": 51704, "marks": [{"phase": 0, "ns": 8493171}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "search-32768-512", "lane": "base", "kind": "js", "run": 3, "status": 1, "correct": false, "stdout": "", "wall_ms": 22.054906, "rss_kib": 51316, "marks": [{"phase": 0, "ns": 9470182}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "search-32768-512", "lane": "base", "kind": "js", "run": 4, "status": 1, "correct": false, "stdout": "", "wall_ms": 20.805398, "rss_kib": 51852, "marks": [{"phase": 0, "ns": 8280859}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "search-32768-512", "lane": "base", "kind": "js", "run": 5, "status": 1, "correct": false, "stdout": "", "wall_ms": 21.910181, "rss_kib": 51908, "marks": [{"phase": 0, "ns": 8675196}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "search-32768-512", "lane": "base", "kind": "js", "run": 6, "status": 1, "correct": false, "stdout": "", "wall_ms": 22.164233, "rss_kib": 51524, "marks": [{"phase": 0, "ns": 9371585}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "search-32768-512", "lane": "base", "kind": "js", "run": 7, "status": 1, "correct": false, "stdout": "", "wall_ms": 21.272253, "rss_kib": 51400, "marks": [{"phase": 0, "ns": 8858694}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "search-32768-512", "lane": "base", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 145.615627, "rss_kib": 3376, "marks": [{"phase": 0, "ns": 191290470829879, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": null}, {"phase": 1, "ns": 191290471996099, "allocs": 133121, "frees": 66563, "live": 798704, "peak": 798720, "copy_cells": null}, {"phase": 3, "ns": 191290614238455, "allocs": 133127, "frees": 133125, "live": 32, "peak": 798736, "copy_cells": null}], "diagnostic": "", "acquire_ms": 1.16622, "process_ms": 142.242356}
{"case": "search-32768-512", "lane": "candidate", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 2.312652, "rss_kib": 2348, "marks": [{"phase": 0, "ns": 191291510259299}, {"phase": 1, "ns": 191291510353658}, {"phase": 3, "ns": 191291510458446}], "diagnostic": "", "acquire_ms": 0.094359, "process_ms": 0.104788}
{"case": "search-32768-512", "lane": "candidate", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 2.19513, "rss_kib": 2172, "marks": [{"phase": 0, "ns": 191291512649347}, {"phase": 1, "ns": 191291512740099}, {"phase": 3, "ns": 191291512847533}], "diagnostic": "", "acquire_ms": 0.090752, "process_ms": 0.107434}
{"case": "search-32768-512", "lane": "candidate", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 1.93189, "rss_kib": 2400, "marks": [{"phase": 0, "ns": 191291514757521}, {"phase": 1, "ns": 191291514844937}, {"phase": 3, "ns": 191291514948523}], "diagnostic": "", "acquire_ms": 0.087416, "process_ms": 0.103586}
{"case": "search-32768-512", "lane": "candidate", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 2.011271, "rss_kib": 2408, "marks": [{"phase": 0, "ns": 191291516864183}, {"phase": 1, "ns": 191291516954303}, {"phase": 3, "ns": 191291517066125}], "diagnostic": "", "acquire_ms": 0.09012, "process_ms": 0.111822}
{"case": "search-32768-512", "lane": "candidate", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 2.134694, "rss_kib": 2348, "marks": [{"phase": 0, "ns": 191291519056737}, {"phase": 1, "ns": 191291519150234}, {"phase": 3, "ns": 191291519295990}], "diagnostic": "", "acquire_ms": 0.093497, "process_ms": 0.145756}
{"case": "search-32768-512", "lane": "candidate", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 1.907955, "rss_kib": 2352, "marks": [{"phase": 0, "ns": 191291521146957}, {"phase": 1, "ns": 191291521230064}, {"phase": 3, "ns": 191291521333540}], "diagnostic": "", "acquire_ms": 0.083107, "process_ms": 0.103476}
{"case": "search-32768-512", "lane": "candidate", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 1.940667, "rss_kib": 2356, "marks": [{"phase": 0, "ns": 191291523172134}, {"phase": 1, "ns": 191291523267134}, {"phase": 3, "ns": 191291523370680}], "diagnostic": "", "acquire_ms": 0.095, "process_ms": 0.103546}
{"case": "search-32768-512", "lane": "candidate", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 2.057959, "rss_kib": 2280, "marks": [{"phase": 0, "ns": 191291525261963}, {"phase": 1, "ns": 191291525383293}, {"phase": 3, "ns": 191291525514512}], "diagnostic": "", "acquire_ms": 0.12133, "process_ms": 0.131219}
{"case": "search-32768-512", "lane": "candidate", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 17.236647, "rss_kib": 41804, "marks": [{"phase": 0, "ns": 9566615}, {"phase": 1, "ns": 9848780}, {"phase": 3, "ns": 10031877}], "diagnostic": "", "acquire_ms": 0.282165, "process_ms": 0.183097}
{"case": "search-32768-512", "lane": "candidate", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 16.83233, "rss_kib": 42120, "marks": [{"phase": 0, "ns": 9288058}, {"phase": 1, "ns": 9505700}, {"phase": 3, "ns": 9659070}], "diagnostic": "", "acquire_ms": 0.217642, "process_ms": 0.15337}
{"case": "search-32768-512", "lane": "candidate", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 16.851186, "rss_kib": 42180, "marks": [{"phase": 0, "ns": 9338903}, {"phase": 1, "ns": 9628552}, {"phase": 3, "ns": 9827449}], "diagnostic": "", "acquire_ms": 0.289649, "process_ms": 0.198897}
{"case": "search-32768-512", "lane": "candidate", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 17.87173, "rss_kib": 41984, "marks": [{"phase": 0, "ns": 9877303}, {"phase": 1, "ns": 10086540}, {"phase": 3, "ns": 10256141}], "diagnostic": "", "acquire_ms": 0.209237, "process_ms": 0.169601}
{"case": "search-32768-512", "lane": "candidate", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 16.827442, "rss_kib": 42044, "marks": [{"phase": 0, "ns": 9013477}, {"phase": 1, "ns": 9300982}, {"phase": 3, "ns": 9470713}], "diagnostic": "", "acquire_ms": 0.287505, "process_ms": 0.169731}
{"case": "search-32768-512", "lane": "candidate", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 16.740096, "rss_kib": 41992, "marks": [{"phase": 0, "ns": 8886707}, {"phase": 1, "ns": 9148103}, {"phase": 3, "ns": 9342381}], "diagnostic": "", "acquire_ms": 0.261396, "process_ms": 0.194278}
{"case": "search-32768-512", "lane": "candidate", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 18.014812, "rss_kib": 42052, "marks": [{"phase": 0, "ns": 9823862}, {"phase": 1, "ns": 10125454}, {"phase": 3, "ns": 10292099}], "diagnostic": "", "acquire_ms": 0.301592, "process_ms": 0.166645}
{"case": "search-32768-512", "lane": "candidate", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 17.073458, "rss_kib": 42120, "marks": [{"phase": 0, "ns": 9294359}, {"phase": 1, "ns": 9531007}, {"phase": 3, "ns": 9701260}], "diagnostic": "", "acquire_ms": 0.236648, "process_ms": 0.170253}
{"case": "search-32768-512", "lane": "candidate", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 2.289097, "rss_kib": 2420, "marks": [{"phase": 0, "ns": 191291666798302, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": 0}, {"phase": 1, "ns": 191291666904303, "allocs": 23, "frees": 13, "live": 133216, "peak": 133232, "copy_cells": 33280}, {"phase": 3, "ns": 191291667023118, "allocs": 30, "frees": 28, "live": 32, "peak": 135232, "copy_cells": 33280}], "diagnostic": "", "acquire_ms": 0.106001, "process_ms": 0.118815}
{"case": "search-65536-1024", "lane": "base", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 434.836523, "rss_kib": 4856, "marks": [{"phase": 0, "ns": 191292463110956}, {"phase": 1, "ns": 191292464756003}, {"phase": 3, "ns": 191292895485043}], "diagnostic": "", "acquire_ms": 1.645047, "process_ms": 430.72904}
{"case": "search-65536-1024", "lane": "base", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 432.958314, "rss_kib": 4432, "marks": [{"phase": 0, "ns": 191292898096511}, {"phase": 1, "ns": 191292900242497}, {"phase": 3, "ns": 191293328591527}], "diagnostic": "", "acquire_ms": 2.145986, "process_ms": 428.34903}
{"case": "search-65536-1024", "lane": "base", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 430.943777, "rss_kib": 4648, "marks": [{"phase": 0, "ns": 191293331216952}, {"phase": 1, "ns": 191293333438651}, {"phase": 3, "ns": 191293759812269}], "diagnostic": "", "acquire_ms": 2.221699, "process_ms": 426.373618}
{"case": "search-65536-1024", "lane": "base", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 452.500289, "rss_kib": 4712, "marks": [{"phase": 0, "ns": 191293762356400}, {"phase": 1, "ns": 191293764401494}, {"phase": 3, "ns": 191294212509591}], "diagnostic": "", "acquire_ms": 2.045094, "process_ms": 448.108097}
{"case": "search-65536-1024", "lane": "base", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 426.698785, "rss_kib": 4792, "marks": [{"phase": 0, "ns": 191294215129545}, {"phase": 1, "ns": 191294216755165}, {"phase": 3, "ns": 191294639305650}], "diagnostic": "", "acquire_ms": 1.62562, "process_ms": 422.550485}
{"case": "search-65536-1024", "lane": "base", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 423.80409, "rss_kib": 4708, "marks": [{"phase": 0, "ns": 191294641888263}, {"phase": 1, "ns": 191294643514133}, {"phase": 3, "ns": 191295063345517}], "diagnostic": "", "acquire_ms": 1.62587, "process_ms": 419.831384}
{"case": "search-65536-1024", "lane": "base", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 418.623705, "rss_kib": 4652, "marks": [{"phase": 0, "ns": 191295065921828}, {"phase": 1, "ns": 191295067624654}, {"phase": 3, "ns": 191295482221460}], "diagnostic": "", "acquire_ms": 1.702826, "process_ms": 414.596806}
{"case": "search-65536-1024", "lane": "base", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 426.277606, "rss_kib": 4836, "marks": [{"phase": 0, "ns": 191295484711087}, {"phase": 1, "ns": 191295486537086}, {"phase": 3, "ns": 191295908600168}], "diagnostic": "", "acquire_ms": 1.825999, "process_ms": 422.063082}
{"case": "search-65536-1024", "lane": "base", "kind": "js", "run": "warm", "status": 1, "correct": false, "stdout": "", "wall_ms": 24.973826, "rss_kib": 51848, "marks": [{"phase": 0, "ns": 9484149}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "search-65536-1024", "lane": "base", "kind": "js", "run": 1, "status": 1, "correct": false, "stdout": "", "wall_ms": 21.093714, "rss_kib": 51520, "marks": [{"phase": 0, "ns": 9023837}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "search-65536-1024", "lane": "base", "kind": "js", "run": 2, "status": 1, "correct": false, "stdout": "", "wall_ms": 20.840415, "rss_kib": 51788, "marks": [{"phase": 0, "ns": 8499564}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "search-65536-1024", "lane": "base", "kind": "js", "run": 3, "status": 1, "correct": false, "stdout": "", "wall_ms": 24.720657, "rss_kib": 51136, "marks": [{"phase": 0, "ns": 10849245}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "search-65536-1024", "lane": "base", "kind": "js", "run": 4, "status": 1, "correct": false, "stdout": "", "wall_ms": 22.036801, "rss_kib": 51516, "marks": [{"phase": 0, "ns": 8817025}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "search-65536-1024", "lane": "base", "kind": "js", "run": 5, "status": 1, "correct": false, "stdout": "", "wall_ms": 25.066141, "rss_kib": 51648, "marks": [{"phase": 0, "ns": 9489509}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "search-65536-1024", "lane": "base", "kind": "js", "run": 6, "status": 1, "correct": false, "stdout": "", "wall_ms": 25.953903, "rss_kib": 51592, "marks": [{"phase": 0, "ns": 8987568}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "search-65536-1024", "lane": "base", "kind": "js", "run": 7, "status": 1, "correct": false, "stdout": "", "wall_ms": 23.295637, "rss_kib": 51852, "marks": [{"phase": 0, "ns": 9221081}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "search-65536-1024", "lane": "base", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 567.297106, "rss_kib": 4792, "marks": [{"phase": 0, "ns": 191296100938006, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": null}, {"phase": 1, "ns": 191296103034027, "allocs": 266241, "frees": 133123, "live": 1597424, "peak": 1597440, "copy_cells": null}, {"phase": 3, "ns": 191296665682736, "allocs": 266247, "frees": 266245, "live": 32, "peak": 1597456, "copy_cells": null}], "diagnostic": "", "acquire_ms": 2.096021, "process_ms": 562.648709}
{"case": "search-65536-1024", "lane": "candidate", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 2.579917, "rss_kib": 2528, "marks": [{"phase": 0, "ns": 191297562119017}, {"phase": 1, "ns": 191297562292125}, {"phase": 3, "ns": 191297562506601}], "diagnostic": "", "acquire_ms": 0.173108, "process_ms": 0.214476}
{"case": "search-65536-1024", "lane": "candidate", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 2.494366, "rss_kib": 2484, "marks": [{"phase": 0, "ns": 191297564706008}, {"phase": 1, "ns": 191297564904604}, {"phase": 3, "ns": 191297565143637}], "diagnostic": "", "acquire_ms": 0.198596, "process_ms": 0.239033}
{"case": "search-65536-1024", "lane": "candidate", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 2.296391, "rss_kib": 2484, "marks": [{"phase": 0, "ns": 191297567222216}, {"phase": 1, "ns": 191297567391917}, {"phase": 3, "ns": 191297567603618}], "diagnostic": "", "acquire_ms": 0.169701, "process_ms": 0.211701}
{"case": "search-65536-1024", "lane": "candidate", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 2.154622, "rss_kib": 2408, "marks": [{"phase": 0, "ns": 191297569556618}, {"phase": 1, "ns": 191297569725147}, {"phase": 3, "ns": 191297569935586}], "diagnostic": "", "acquire_ms": 0.168529, "process_ms": 0.210439}
{"case": "search-65536-1024", "lane": "candidate", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 2.503002, "rss_kib": 2416, "marks": [{"phase": 0, "ns": 191297572047988}, {"phase": 1, "ns": 191297572267985}, {"phase": 3, "ns": 191297572486078}], "diagnostic": "", "acquire_ms": 0.219997, "process_ms": 0.218093}
{"case": "search-65536-1024", "lane": "candidate", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 2.388285, "rss_kib": 2352, "marks": [{"phase": 0, "ns": 191297574762952}, {"phase": 1, "ns": 191297574930840}, {"phase": 3, "ns": 191297575148182}], "diagnostic": "", "acquire_ms": 0.167888, "process_ms": 0.217342}
{"case": "search-65536-1024", "lane": "candidate", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 2.131258, "rss_kib": 2424, "marks": [{"phase": 0, "ns": 191297577034095}, {"phase": 1, "ns": 191297577197425}, {"phase": 3, "ns": 191297577405419}], "diagnostic": "", "acquire_ms": 0.16333, "process_ms": 0.207994}
{"case": "search-65536-1024", "lane": "candidate", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 2.317781, "rss_kib": 2488, "marks": [{"phase": 0, "ns": 191297579352798}, {"phase": 1, "ns": 191297579530966}, {"phase": 3, "ns": 191297579741745}], "diagnostic": "", "acquire_ms": 0.178168, "process_ms": 0.210779}
{"case": "search-65536-1024", "lane": "candidate", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 17.283095, "rss_kib": 41848, "marks": [{"phase": 0, "ns": 9720878}, {"phase": 1, "ns": 9950954}, {"phase": 3, "ns": 10213140}], "diagnostic": "", "acquire_ms": 0.230076, "process_ms": 0.262186}
{"case": "search-65536-1024", "lane": "candidate", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 18.755354, "rss_kib": 42096, "marks": [{"phase": 0, "ns": 10165149}, {"phase": 1, "ns": 10401287}, {"phase": 3, "ns": 10666790}], "diagnostic": "", "acquire_ms": 0.236138, "process_ms": 0.265503}
{"case": "search-65536-1024", "lane": "candidate", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 20.124869, "rss_kib": 42048, "marks": [{"phase": 0, "ns": 9571244}, {"phase": 1, "ns": 9821618}, {"phase": 3, "ns": 10108001}], "diagnostic": "", "acquire_ms": 0.250374, "process_ms": 0.286383}
{"case": "search-65536-1024", "lane": "candidate", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 17.585879, "rss_kib": 42184, "marks": [{"phase": 0, "ns": 9863127}, {"phase": 1, "ns": 10103913}, {"phase": 3, "ns": 10363355}], "diagnostic": "", "acquire_ms": 0.240786, "process_ms": 0.259442}
{"case": "search-65536-1024", "lane": "candidate", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 17.905163, "rss_kib": 42048, "marks": [{"phase": 0, "ns": 9556546}, {"phase": 1, "ns": 9823221}, {"phase": 3, "ns": 10109013}], "diagnostic": "", "acquire_ms": 0.266675, "process_ms": 0.285792}
{"case": "search-65536-1024", "lane": "candidate", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 17.669427, "rss_kib": 41992, "marks": [{"phase": 0, "ns": 9965902}, {"phase": 1, "ns": 10183915}, {"phase": 3, "ns": 10441844}], "diagnostic": "", "acquire_ms": 0.218013, "process_ms": 0.257929}
{"case": "search-65536-1024", "lane": "candidate", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 17.795195, "rss_kib": 42308, "marks": [{"phase": 0, "ns": 9975610}, {"phase": 1, "ns": 10222147}, {"phase": 3, "ns": 10514471}], "diagnostic": "", "acquire_ms": 0.246537, "process_ms": 0.292324}
{"case": "search-65536-1024", "lane": "candidate", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 16.134819, "rss_kib": 42248, "marks": [{"phase": 0, "ns": 8813378}, {"phase": 1, "ns": 9035799}, {"phase": 3, "ns": 9329856}], "diagnostic": "", "acquire_ms": 0.222421, "process_ms": 0.294057}
{"case": "search-65536-1024", "lane": "candidate", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 2.604044, "rss_kib": 2344, "marks": [{"phase": 0, "ns": 191297727095876, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": 0}, {"phase": 1, "ns": 191297727273212, "allocs": 23, "frees": 13, "live": 266336, "peak": 266352, "copy_cells": 66560}, {"phase": 3, "ns": 191297727492317, "allocs": 30, "frees": 28, "live": 32, "peak": 270400, "copy_cells": 66560}], "diagnostic": "", "acquire_ms": 0.177336, "process_ms": 0.219105}
{"case": "search-131072-2048", "lane": "base", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 1662.765939, "rss_kib": 7396, "marks": [{"phase": 0, "ns": 191298623638499}, {"phase": 1, "ns": 191298627267625}, {"phase": 3, "ns": 191300283583082}], "diagnostic": "", "acquire_ms": 3.629126, "process_ms": 1656.315457}
{"case": "search-131072-2048", "lane": "base", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 1644.996663, "rss_kib": 7396, "marks": [{"phase": 0, "ns": 191300286824994}, {"phase": 1, "ns": 191300290249202}, {"phase": 3, "ns": 191301928889762}], "diagnostic": "", "acquire_ms": 3.424208, "process_ms": 1638.64056}
{"case": "search-131072-2048", "lane": "base", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 1672.629136, "rss_kib": 7216, "marks": [{"phase": 0, "ns": 191301931751143}, {"phase": 1, "ns": 191301935542667}, {"phase": 3, "ns": 191303601779542}], "diagnostic": "", "acquire_ms": 3.791524, "process_ms": 1666.236875}
{"case": "search-131072-2048", "lane": "base", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 1676.449825, "rss_kib": 7528, "marks": [{"phase": 0, "ns": 191303604477564}, {"phase": 1, "ns": 191303608209414}, {"phase": 3, "ns": 191305278334125}], "diagnostic": "", "acquire_ms": 3.73185, "process_ms": 1670.124711}
{"case": "search-131072-2048", "lane": "base", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 1671.320175, "rss_kib": 7476, "marks": [{"phase": 0, "ns": 191305281228028}, {"phase": 1, "ns": 191305284706729}, {"phase": 3, "ns": 191306949654621}], "diagnostic": "", "acquire_ms": 3.478701, "process_ms": 1664.947892}
{"case": "search-131072-2048", "lane": "base", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 1682.210359, "rss_kib": 7404, "marks": [{"phase": 0, "ns": 191306952737162}, {"phase": 1, "ns": 191306956061420}, {"phase": 3, "ns": 191308632382080}], "diagnostic": "", "acquire_ms": 3.324258, "process_ms": 1676.32066}
{"case": "search-131072-2048", "lane": "base", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 1695.191483, "rss_kib": 7288, "marks": [{"phase": 0, "ns": 191308634997465}, {"phase": 1, "ns": 191308638341962}, {"phase": 3, "ns": 191310327561059}], "diagnostic": "", "acquire_ms": 3.344497, "process_ms": 1689.219097}
{"case": "search-131072-2048", "lane": "base", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 1683.87374, "rss_kib": 7472, "marks": [{"phase": 0, "ns": 191310330377285}, {"phase": 1, "ns": 191310333683309}, {"phase": 3, "ns": 191312011636502}], "diagnostic": "", "acquire_ms": 3.306024, "process_ms": 1677.953193}
{"case": "search-131072-2048", "lane": "base", "kind": "js", "run": "warm", "status": 1, "correct": false, "stdout": "", "wall_ms": 25.99439, "rss_kib": 51720, "marks": [{"phase": 0, "ns": 10021247}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "search-131072-2048", "lane": "base", "kind": "js", "run": 1, "status": 1, "correct": false, "stdout": "", "wall_ms": 26.12642, "rss_kib": 51904, "marks": [{"phase": 0, "ns": 9182498}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "search-131072-2048", "lane": "base", "kind": "js", "run": 2, "status": 1, "correct": false, "stdout": "", "wall_ms": 22.137612, "rss_kib": 51508, "marks": [{"phase": 0, "ns": 9016764}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "search-131072-2048", "lane": "base", "kind": "js", "run": 3, "status": 1, "correct": false, "stdout": "", "wall_ms": 22.554412, "rss_kib": 52032, "marks": [{"phase": 0, "ns": 9327262}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "search-131072-2048", "lane": "base", "kind": "js", "run": 4, "status": 1, "correct": false, "stdout": "", "wall_ms": 22.848129, "rss_kib": 51644, "marks": [{"phase": 0, "ns": 9793715}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "search-131072-2048", "lane": "base", "kind": "js", "run": 5, "status": 1, "correct": false, "stdout": "", "wall_ms": 22.412073, "rss_kib": 51900, "marks": [{"phase": 0, "ns": 8844166}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "search-131072-2048", "lane": "base", "kind": "js", "run": 6, "status": 1, "correct": false, "stdout": "", "wall_ms": 23.76726, "rss_kib": 52036, "marks": [{"phase": 0, "ns": 9668929}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "search-131072-2048", "lane": "base", "kind": "js", "run": 7, "status": 1, "correct": false, "stdout": "", "wall_ms": 24.069182, "rss_kib": 51908, "marks": [{"phase": 0, "ns": 9371265}], "diagnostic": "bend: memory fault (machine stack overflow?)"}
{"case": "search-131072-2048", "lane": "base", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 2298.329304, "rss_kib": 7396, "marks": [{"phase": 0, "ns": 191312206348979, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": null}, {"phase": 1, "ns": 191312210907786, "allocs": 532481, "frees": 266243, "live": 3194864, "peak": 3194880, "copy_cells": null}, {"phase": 3, "ns": 191314501578629, "allocs": 532487, "frees": 532485, "live": 32, "peak": 3194896, "copy_cells": null}], "diagnostic": "", "acquire_ms": 4.558807, "process_ms": 2290.670843}
{"case": "search-131072-2048", "lane": "candidate", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 3.065969, "rss_kib": 2860, "marks": [{"phase": 0, "ns": 191315448641809}, {"phase": 1, "ns": 191315449019345}, {"phase": 3, "ns": 191315449435984}], "diagnostic": "", "acquire_ms": 0.377536, "process_ms": 0.416639}
{"case": "search-131072-2048", "lane": "candidate", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 2.640222, "rss_kib": 2804, "marks": [{"phase": 0, "ns": 191315451597960}, {"phase": 1, "ns": 191315451916704}, {"phase": 3, "ns": 191315452344906}], "diagnostic": "", "acquire_ms": 0.318744, "process_ms": 0.428202}
{"case": "search-131072-2048", "lane": "candidate", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 2.677212, "rss_kib": 2660, "marks": [{"phase": 0, "ns": 191315454370193}, {"phase": 1, "ns": 191315454710377}, {"phase": 3, "ns": 191315455136625}], "diagnostic": "", "acquire_ms": 0.340184, "process_ms": 0.426248}
{"case": "search-131072-2048", "lane": "candidate", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 2.869006, "rss_kib": 2512, "marks": [{"phase": 0, "ns": 191315457141513}, {"phase": 1, "ns": 191315457631892}, {"phase": 3, "ns": 191315458123934}], "diagnostic": "", "acquire_ms": 0.490379, "process_ms": 0.492042}
{"case": "search-131072-2048", "lane": "candidate", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 2.574728, "rss_kib": 2660, "marks": [{"phase": 0, "ns": 191315460110198}, {"phase": 1, "ns": 191315460426056}, {"phase": 3, "ns": 191315460836905}], "diagnostic": "", "acquire_ms": 0.315858, "process_ms": 0.410849}
{"case": "search-131072-2048", "lane": "candidate", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 2.555352, "rss_kib": 2660, "marks": [{"phase": 0, "ns": 191315462713039}, {"phase": 1, "ns": 191315463058273}, {"phase": 3, "ns": 191315463495361}], "diagnostic": "", "acquire_ms": 0.345234, "process_ms": 0.437088}
{"case": "search-131072-2048", "lane": "candidate", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 2.598243, "rss_kib": 2608, "marks": [{"phase": 0, "ns": 191315465465374}, {"phase": 1, "ns": 191315465780862}, {"phase": 3, "ns": 191315466204745}], "diagnostic": "", "acquire_ms": 0.315488, "process_ms": 0.423883}
{"case": "search-131072-2048", "lane": "candidate", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 2.588825, "rss_kib": 2744, "marks": [{"phase": 0, "ns": 191315468131305}, {"phase": 1, "ns": 191315468474054}, {"phase": 3, "ns": 191315468898268}], "diagnostic": "", "acquire_ms": 0.342749, "process_ms": 0.424214}
{"case": "search-131072-2048", "lane": "candidate", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 17.314795, "rss_kib": 42300, "marks": [{"phase": 0, "ns": 9346147}, {"phase": 1, "ns": 9601922}, {"phase": 3, "ns": 10079947}], "diagnostic": "", "acquire_ms": 0.255775, "process_ms": 0.478025}
{"case": "search-131072-2048", "lane": "candidate", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 17.564318, "rss_kib": 42380, "marks": [{"phase": 0, "ns": 8926472}, {"phase": 1, "ns": 9260305}, {"phase": 3, "ns": 9782915}], "diagnostic": "", "acquire_ms": 0.333833, "process_ms": 0.52261}
{"case": "search-131072-2048", "lane": "candidate", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 18.359674, "rss_kib": 42304, "marks": [{"phase": 0, "ns": 9875821}, {"phase": 1, "ns": 10106739}, {"phase": 3, "ns": 10612417}], "diagnostic": "", "acquire_ms": 0.230918, "process_ms": 0.505678}
{"case": "search-131072-2048", "lane": "candidate", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 17.905094, "rss_kib": 42508, "marks": [{"phase": 0, "ns": 9545895}, {"phase": 1, "ns": 9856704}, {"phase": 3, "ns": 10320894}], "diagnostic": "", "acquire_ms": 0.310809, "process_ms": 0.46419}
{"case": "search-131072-2048", "lane": "candidate", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 17.556884, "rss_kib": 42160, "marks": [{"phase": 0, "ns": 9582335}, {"phase": 1, "ns": 9841195}, {"phase": 3, "ns": 10302399}], "diagnostic": "", "acquire_ms": 0.25886, "process_ms": 0.461204}
{"case": "search-131072-2048", "lane": "candidate", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 17.538128, "rss_kib": 42492, "marks": [{"phase": 0, "ns": 9299860}, {"phase": 1, "ns": 9656525}, {"phase": 3, "ns": 10129972}], "diagnostic": "", "acquire_ms": 0.356665, "process_ms": 0.473447}
{"case": "search-131072-2048", "lane": "candidate", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 17.848476, "rss_kib": 42304, "marks": [{"phase": 0, "ns": 9562177}, {"phase": 1, "ns": 9889627}, {"phase": 3, "ns": 10356863}], "diagnostic": "", "acquire_ms": 0.32745, "process_ms": 0.467236}
{"case": "search-131072-2048", "lane": "candidate", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 17.417921, "rss_kib": 42120, "marks": [{"phase": 0, "ns": 9087217}, {"phase": 1, "ns": 9342280}, {"phase": 3, "ns": 9799666}], "diagnostic": "", "acquire_ms": 0.255063, "process_ms": 0.457386}
{"case": "search-131072-2048", "lane": "candidate", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "1:1", "wall_ms": 2.836754, "rss_kib": 2808, "marks": [{"phase": 0, "ns": 191315614214588, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": 0}, {"phase": 1, "ns": 191315614621639, "allocs": 23, "frees": 13, "live": 532576, "peak": 532592, "copy_cells": 133120}, {"phase": 3, "ns": 191315615046745, "allocs": 30, "frees": 28, "live": 32, "peak": 540736, "copy_cells": 133120}], "diagnostic": "", "acquire_ms": 0.407051, "process_ms": 0.425106}
{"case": "build-concat-1024", "lane": "base", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 2.28547, "rss_kib": 2276, "marks": [{"phase": 0, "ns": 191316411394826}, {"phase": 1, "ns": 191316411453838}, {"phase": 3, "ns": 191316411464257}], "diagnostic": "", "acquire_ms": 0.059012, "process_ms": 0.010419}
{"case": "build-concat-1024", "lane": "base", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 1.866887, "rss_kib": 2424, "marks": [{"phase": 0, "ns": 191316413470709}, {"phase": 1, "ns": 191316413512498}, {"phase": 3, "ns": 191316413522657}], "diagnostic": "", "acquire_ms": 0.041789, "process_ms": 0.010159}
{"case": "build-concat-1024", "lane": "base", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 1.788929, "rss_kib": 2412, "marks": [{"phase": 0, "ns": 191316415386158}, {"phase": 1, "ns": 191316415429761}, {"phase": 3, "ns": 191316415440661}], "diagnostic": "", "acquire_ms": 0.043603, "process_ms": 0.0109}
{"case": "build-concat-1024", "lane": "base", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 1.857009, "rss_kib": 2304, "marks": [{"phase": 0, "ns": 191316417332956}, {"phase": 1, "ns": 191316417374405}, {"phase": 3, "ns": 191316417384414}], "diagnostic": "", "acquire_ms": 0.041449, "process_ms": 0.010009}
{"case": "build-concat-1024", "lane": "base", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 1.733364, "rss_kib": 2420, "marks": [{"phase": 0, "ns": 191316419199743}, {"phase": 1, "ns": 191316419241222}, {"phase": 3, "ns": 191316419251551}], "diagnostic": "", "acquire_ms": 0.041479, "process_ms": 0.010329}
{"case": "build-concat-1024", "lane": "base", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 1.718125, "rss_kib": 2224, "marks": [{"phase": 0, "ns": 191316421019601}, {"phase": 1, "ns": 191316421065629}, {"phase": 3, "ns": 191316421076249}], "diagnostic": "", "acquire_ms": 0.046028, "process_ms": 0.01062}
{"case": "build-concat-1024", "lane": "base", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 1.815269, "rss_kib": 2168, "marks": [{"phase": 0, "ns": 191316422907789}, {"phase": 1, "ns": 191316422949768}, {"phase": 3, "ns": 191316422960949}], "diagnostic": "", "acquire_ms": 0.041979, "process_ms": 0.011181}
{"case": "build-concat-1024", "lane": "base", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 1.844996, "rss_kib": 2272, "marks": [{"phase": 0, "ns": 191316424847414}, {"phase": 1, "ns": 191316424887319}, {"phase": 3, "ns": 191316424897428}], "diagnostic": "", "acquire_ms": 0.039905, "process_ms": 0.010109}
{"case": "build-concat-1024", "lane": "base", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 19.425103, "rss_kib": 46856, "marks": [{"phase": 0, "ns": 10009034}, {"phase": 1, "ns": 11186134}, {"phase": 3, "ns": 12112058}], "diagnostic": "", "acquire_ms": 1.1771, "process_ms": 0.925924}
{"case": "build-concat-1024", "lane": "base", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 23.267193, "rss_kib": 46976, "marks": [{"phase": 0, "ns": 10094274}, {"phase": 1, "ns": 11020299}, {"phase": 3, "ns": 12364195}], "diagnostic": "", "acquire_ms": 0.926025, "process_ms": 1.343896}
{"case": "build-concat-1024", "lane": "base", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 19.170441, "rss_kib": 47036, "marks": [{"phase": 0, "ns": 9455204}, {"phase": 1, "ns": 10336934}, {"phase": 3, "ns": 11509296}], "diagnostic": "", "acquire_ms": 0.88173, "process_ms": 1.172362}
{"case": "build-concat-1024", "lane": "base", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 21.64561, "rss_kib": 47052, "marks": [{"phase": 0, "ns": 9580572}, {"phase": 1, "ns": 10821744}, {"phase": 3, "ns": 11701430}], "diagnostic": "", "acquire_ms": 1.241172, "process_ms": 0.879686}
{"case": "build-concat-1024", "lane": "base", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 19.452765, "rss_kib": 46844, "marks": [{"phase": 0, "ns": 9690460}, {"phase": 1, "ns": 10567952}, {"phase": 3, "ns": 11818241}], "diagnostic": "", "acquire_ms": 0.877492, "process_ms": 1.250289}
{"case": "build-concat-1024", "lane": "base", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 17.831584, "rss_kib": 46592, "marks": [{"phase": 0, "ns": 8876157}, {"phase": 1, "ns": 10014654}, {"phase": 3, "ns": 11020179}], "diagnostic": "", "acquire_ms": 1.138497, "process_ms": 1.005525}
{"case": "build-concat-1024", "lane": "base", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 18.132173, "rss_kib": 46924, "marks": [{"phase": 0, "ns": 8746260}, {"phase": 1, "ns": 9667776}, {"phase": 3, "ns": 10713397}], "diagnostic": "", "acquire_ms": 0.921516, "process_ms": 1.045621}
{"case": "build-concat-1024", "lane": "base", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 18.431992, "rss_kib": 46980, "marks": [{"phase": 0, "ns": 9395842}, {"phase": 1, "ns": 10276050}, {"phase": 3, "ns": 11414006}], "diagnostic": "", "acquire_ms": 0.880208, "process_ms": 1.137956}
{"case": "build-concat-1024", "lane": "base", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 2.105669, "rss_kib": 2412, "marks": [{"phase": 0, "ns": 191316586026778, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": null}, {"phase": 1, "ns": 191316586079408, "allocs": 7178, "frees": 1033, "live": 73744, "peak": 73760, "copy_cells": null}, {"phase": 3, "ns": 191316586095218, "allocs": 7184, "frees": 7182, "live": 32, "peak": 73776, "copy_cells": null}], "diagnostic": "", "acquire_ms": 0.05263, "process_ms": 0.01581}
{"case": "build-concat-1024", "lane": "candidate", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 2.292343, "rss_kib": 2344, "marks": [{"phase": 0, "ns": 191317481625683}, {"phase": 1, "ns": 191317481710012}, {"phase": 3, "ns": 191317481734950}], "diagnostic": "", "acquire_ms": 0.084329, "process_ms": 0.024938}
{"case": "build-concat-1024", "lane": "candidate", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 1.927843, "rss_kib": 2296, "marks": [{"phase": 0, "ns": 191317483729949}, {"phase": 1, "ns": 191317483807316}, {"phase": 3, "ns": 191317483832414}], "diagnostic": "", "acquire_ms": 0.077367, "process_ms": 0.025098}
{"case": "build-concat-1024", "lane": "candidate", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 2.000971, "rss_kib": 2296, "marks": [{"phase": 0, "ns": 191317485802787}, {"phase": 1, "ns": 191317485884572}, {"phase": 3, "ns": 191317485917664}], "diagnostic": "", "acquire_ms": 0.081785, "process_ms": 0.033092}
{"case": "build-concat-1024", "lane": "candidate", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 1.949684, "rss_kib": 2540, "marks": [{"phase": 0, "ns": 191317487853362}, {"phase": 1, "ns": 191317487939114}, {"phase": 3, "ns": 191317487964282}], "diagnostic": "", "acquire_ms": 0.085752, "process_ms": 0.025168}
{"case": "build-concat-1024", "lane": "candidate", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 1.879881, "rss_kib": 2352, "marks": [{"phase": 0, "ns": 191317489909658}, {"phase": 1, "ns": 191317489987906}, {"phase": 3, "ns": 191317490018023}], "diagnostic": "", "acquire_ms": 0.078248, "process_ms": 0.030117}
{"case": "build-concat-1024", "lane": "candidate", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 2.000059, "rss_kib": 2480, "marks": [{"phase": 0, "ns": 191317491948230}, {"phase": 1, "ns": 191317492039022}, {"phase": 3, "ns": 191317492065352}], "diagnostic": "", "acquire_ms": 0.090792, "process_ms": 0.02633}
{"case": "build-concat-1024", "lane": "candidate", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 1.971105, "rss_kib": 2548, "marks": [{"phase": 0, "ns": 191317494094096}, {"phase": 1, "ns": 191317494181381}, {"phase": 3, "ns": 191317494206398}], "diagnostic": "", "acquire_ms": 0.087285, "process_ms": 0.025017}
{"case": "build-concat-1024", "lane": "candidate", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 1.760315, "rss_kib": 2548, "marks": [{"phase": 0, "ns": 191317496029663}, {"phase": 1, "ns": 191317496101118}, {"phase": 3, "ns": 191317496126095}], "diagnostic": "", "acquire_ms": 0.071455, "process_ms": 0.024977}
{"case": "build-concat-1024", "lane": "candidate", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 19.407059, "rss_kib": 47624, "marks": [{"phase": 0, "ns": 9624455}, {"phase": 1, "ns": 10487800}, {"phase": 3, "ns": 11624955}], "diagnostic": "", "acquire_ms": 0.863345, "process_ms": 1.137155}
{"case": "build-concat-1024", "lane": "candidate", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 17.852073, "rss_kib": 47240, "marks": [{"phase": 0, "ns": 8776167}, {"phase": 1, "ns": 9668838}, {"phase": 3, "ns": 10999830}], "diagnostic": "", "acquire_ms": 0.892671, "process_ms": 1.330992}
{"case": "build-concat-1024", "lane": "candidate", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 21.553476, "rss_kib": 47480, "marks": [{"phase": 0, "ns": 9302365}, {"phase": 1, "ns": 10506586}, {"phase": 3, "ns": 11986460}], "diagnostic": "", "acquire_ms": 1.204221, "process_ms": 1.479874}
{"case": "build-concat-1024", "lane": "candidate", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 20.028757, "rss_kib": 47428, "marks": [{"phase": 0, "ns": 10412527}, {"phase": 1, "ns": 11506149}, {"phase": 3, "ns": 12808547}], "diagnostic": "", "acquire_ms": 1.093622, "process_ms": 1.302398}
{"case": "build-concat-1024", "lane": "candidate", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 18.662348, "rss_kib": 47428, "marks": [{"phase": 0, "ns": 9309728}, {"phase": 1, "ns": 10240522}, {"phase": 3, "ns": 11406551}], "diagnostic": "", "acquire_ms": 0.930794, "process_ms": 1.166029}
{"case": "build-concat-1024", "lane": "candidate", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 18.502726, "rss_kib": 47424, "marks": [{"phase": 0, "ns": 9419767}, {"phase": 1, "ns": 10252114}, {"phase": 3, "ns": 11510679}], "diagnostic": "", "acquire_ms": 0.832347, "process_ms": 1.258565}
{"case": "build-concat-1024", "lane": "candidate", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 20.515931, "rss_kib": 47052, "marks": [{"phase": 0, "ns": 10869163}, {"phase": 1, "ns": 11791360}, {"phase": 3, "ns": 13211981}], "diagnostic": "", "acquire_ms": 0.922197, "process_ms": 1.420621}
{"case": "build-concat-1024", "lane": "candidate", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 20.175636, "rss_kib": 47424, "marks": [{"phase": 0, "ns": 9314127}, {"phase": 1, "ns": 10107199}, {"phase": 3, "ns": 11323183}], "diagnostic": "", "acquire_ms": 0.793072, "process_ms": 1.215984}
{"case": "build-concat-1024", "lane": "candidate", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 2.271754, "rss_kib": 2344, "marks": [{"phase": 0, "ns": 191317656473524, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": 0}, {"phase": 1, "ns": 191317656568213, "allocs": 1059, "frees": 1053, "live": 16440, "peak": 30048, "copy_cells": 7149}, {"phase": 3, "ns": 191317656603300, "allocs": 7207, "frees": 7205, "live": 32, "peak": 16472, "copy_cells": 7149}], "diagnostic": "", "acquire_ms": 0.094689, "process_ms": 0.035087}
{"case": "build-concat-4096", "lane": "base", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 2.542588, "rss_kib": 2604, "marks": [{"phase": 0, "ns": 191318453696753}, {"phase": 1, "ns": 191318453892715}, {"phase": 3, "ns": 191318453928392}], "diagnostic": "", "acquire_ms": 0.195962, "process_ms": 0.035677}
{"case": "build-concat-4096", "lane": "base", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 2.093165, "rss_kib": 2552, "marks": [{"phase": 0, "ns": 191318455943871}, {"phase": 1, "ns": 191318456136836}, {"phase": 3, "ns": 191318456174919}], "diagnostic": "", "acquire_ms": 0.192965, "process_ms": 0.038083}
{"case": "build-concat-4096", "lane": "base", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 2.088236, "rss_kib": 2676, "marks": [{"phase": 0, "ns": 191318458173024}, {"phase": 1, "ns": 191318458374756}, {"phase": 3, "ns": 191318458411466}], "diagnostic": "", "acquire_ms": 0.201732, "process_ms": 0.03671}
{"case": "build-concat-4096", "lane": "base", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 2.045185, "rss_kib": 2536, "marks": [{"phase": 0, "ns": 191318460409572}, {"phase": 1, "ns": 191318460585605}, {"phase": 3, "ns": 191318460623026}], "diagnostic": "", "acquire_ms": 0.176033, "process_ms": 0.037421}
{"case": "build-concat-4096", "lane": "base", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 1.973039, "rss_kib": 2496, "marks": [{"phase": 0, "ns": 191318462502667}, {"phase": 1, "ns": 191318462690273}, {"phase": 3, "ns": 191318462727383}], "diagnostic": "", "acquire_ms": 0.187606, "process_ms": 0.03711}
{"case": "build-concat-4096", "lane": "base", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 2.128774, "rss_kib": 2372, "marks": [{"phase": 0, "ns": 191318464653502}, {"phase": 1, "ns": 191318464909788}, {"phase": 3, "ns": 191318464950044}], "diagnostic": "", "acquire_ms": 0.256286, "process_ms": 0.040256}
{"case": "build-concat-4096", "lane": "base", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 1.970653, "rss_kib": 2612, "marks": [{"phase": 0, "ns": 191318466803756}, {"phase": 1, "ns": 191318466990901}, {"phase": 3, "ns": 191318467032940}], "diagnostic": "", "acquire_ms": 0.187145, "process_ms": 0.042039}
{"case": "build-concat-4096", "lane": "base", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 2.290199, "rss_kib": 2676, "marks": [{"phase": 0, "ns": 191318469201249}, {"phase": 1, "ns": 191318469392250}, {"phase": 3, "ns": 191318469429932}], "diagnostic": "", "acquire_ms": 0.191001, "process_ms": 0.037682}
{"case": "build-concat-4096", "lane": "base", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 20.535587, "rss_kib": 53196, "marks": [{"phase": 0, "ns": 9312654}, {"phase": 1, "ns": 10958562}, {"phase": 3, "ns": 13707120}], "diagnostic": "", "acquire_ms": 1.645908, "process_ms": 2.748558}
{"case": "build-concat-4096", "lane": "base", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 20.208848, "rss_kib": 53512, "marks": [{"phase": 0, "ns": 8998128}, {"phase": 1, "ns": 10669525}, {"phase": 3, "ns": 13258790}], "diagnostic": "", "acquire_ms": 1.671397, "process_ms": 2.589265}
{"case": "build-concat-4096", "lane": "base", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 23.258496, "rss_kib": 52748, "marks": [{"phase": 0, "ns": 10093643}, {"phase": 1, "ns": 11722119}, {"phase": 3, "ns": 14930858}], "diagnostic": "", "acquire_ms": 1.628476, "process_ms": 3.208739}
{"case": "build-concat-4096", "lane": "base", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 21.672551, "rss_kib": 53316, "marks": [{"phase": 0, "ns": 9276936}, {"phase": 1, "ns": 10925219}, {"phase": 3, "ns": 14073434}], "diagnostic": "", "acquire_ms": 1.648283, "process_ms": 3.148215}
{"case": "build-concat-4096", "lane": "base", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 23.192621, "rss_kib": 53244, "marks": [{"phase": 0, "ns": 8716695}, {"phase": 1, "ns": 10575818}, {"phase": 3, "ns": 13319265}], "diagnostic": "", "acquire_ms": 1.859123, "process_ms": 2.743447}
{"case": "build-concat-4096", "lane": "base", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 21.885074, "rss_kib": 53240, "marks": [{"phase": 0, "ns": 9296964}, {"phase": 1, "ns": 11217192}, {"phase": 3, "ns": 13926145}], "diagnostic": "", "acquire_ms": 1.920228, "process_ms": 2.708953}
{"case": "build-concat-4096", "lane": "base", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 21.618429, "rss_kib": 53196, "marks": [{"phase": 0, "ns": 9409217}, {"phase": 1, "ns": 11226711}, {"phase": 3, "ns": 14034000}], "diagnostic": "", "acquire_ms": 1.817494, "process_ms": 2.807289}
{"case": "build-concat-4096", "lane": "base", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 27.686215, "rss_kib": 53256, "marks": [{"phase": 0, "ns": 12441051}, {"phase": 1, "ns": 14297007}, {"phase": 3, "ns": 17266614}], "diagnostic": "", "acquire_ms": 1.855956, "process_ms": 2.969607}
{"case": "build-concat-4096", "lane": "base", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 2.343961, "rss_kib": 2412, "marks": [{"phase": 0, "ns": 191318653234653, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": null}, {"phase": 1, "ns": 191318653458266, "allocs": 28682, "frees": 4105, "live": 294928, "peak": 294944, "copy_cells": null}, {"phase": 3, "ns": 191318653525293, "allocs": 28688, "frees": 28686, "live": 32, "peak": 294960, "copy_cells": null}], "diagnostic": "", "acquire_ms": 0.223613, "process_ms": 0.067027}
{"case": "build-concat-4096", "lane": "candidate", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 2.377624, "rss_kib": 2472, "marks": [{"phase": 0, "ns": 191319549248574}, {"phase": 1, "ns": 191319549410651}, {"phase": 3, "ns": 191319549506422}], "diagnostic": "", "acquire_ms": 0.162077, "process_ms": 0.095771}
{"case": "build-concat-4096", "lane": "candidate", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 2.179459, "rss_kib": 2472, "marks": [{"phase": 0, "ns": 191319551505380}, {"phase": 1, "ns": 191319551668358}, {"phase": 3, "ns": 191319551801010}], "diagnostic": "", "acquire_ms": 0.162978, "process_ms": 0.132652}
{"case": "build-concat-4096", "lane": "candidate", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 2.154752, "rss_kib": 2612, "marks": [{"phase": 0, "ns": 191319553894145}, {"phase": 1, "ns": 191319554062785}, {"phase": 3, "ns": 191319554158346}], "diagnostic": "", "acquire_ms": 0.16864, "process_ms": 0.095561}
{"case": "build-concat-4096", "lane": "candidate", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 2.25367, "rss_kib": 2472, "marks": [{"phase": 0, "ns": 191319556259146}, {"phase": 1, "ns": 191319556437905}, {"phase": 3, "ns": 191319556540690}], "diagnostic": "", "acquire_ms": 0.178759, "process_ms": 0.102785}
{"case": "build-concat-4096", "lane": "candidate", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 2.26949, "rss_kib": 2676, "marks": [{"phase": 0, "ns": 191319558709629}, {"phase": 1, "ns": 191319558895972}, {"phase": 3, "ns": 191319558997755}], "diagnostic": "", "acquire_ms": 0.186343, "process_ms": 0.101783}
{"case": "build-concat-4096", "lane": "candidate", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 2.186112, "rss_kib": 2552, "marks": [{"phase": 0, "ns": 191319560951075}, {"phase": 1, "ns": 191319561148169}, {"phase": 3, "ns": 191319561302802}], "diagnostic": "", "acquire_ms": 0.197094, "process_ms": 0.154633}
{"case": "build-concat-4096", "lane": "candidate", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 2.2279, "rss_kib": 2676, "marks": [{"phase": 0, "ns": 191319563420785}, {"phase": 1, "ns": 191319563586228}, {"phase": 3, "ns": 191319563694103}], "diagnostic": "", "acquire_ms": 0.165443, "process_ms": 0.107875}
{"case": "build-concat-4096", "lane": "candidate", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 2.103004, "rss_kib": 2532, "marks": [{"phase": 0, "ns": 191319565626814}, {"phase": 1, "ns": 191319565792118}, {"phase": 3, "ns": 191319565886877}], "diagnostic": "", "acquire_ms": 0.165304, "process_ms": 0.094759}
{"case": "build-concat-4096", "lane": "candidate", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 26.290991, "rss_kib": 53516, "marks": [{"phase": 0, "ns": 10797137}, {"phase": 1, "ns": 12479585}, {"phase": 3, "ns": 16178242}], "diagnostic": "", "acquire_ms": 1.682448, "process_ms": 3.698657}
{"case": "build-concat-4096", "lane": "candidate", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 27.792697, "rss_kib": 53444, "marks": [{"phase": 0, "ns": 11880029}, {"phase": 1, "ns": 13770590}, {"phase": 3, "ns": 17327750}], "diagnostic": "", "acquire_ms": 1.890561, "process_ms": 3.55716}
{"case": "build-concat-4096", "lane": "candidate", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 27.044629, "rss_kib": 53700, "marks": [{"phase": 0, "ns": 10040023}, {"phase": 1, "ns": 11730515}, {"phase": 3, "ns": 14616122}], "diagnostic": "", "acquire_ms": 1.690492, "process_ms": 2.885607}
{"case": "build-concat-4096", "lane": "candidate", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 21.657222, "rss_kib": 53400, "marks": [{"phase": 0, "ns": 9877504}, {"phase": 1, "ns": 11613133}, {"phase": 3, "ns": 14391347}], "diagnostic": "", "acquire_ms": 1.735629, "process_ms": 2.778214}
{"case": "build-concat-4096", "lane": "candidate", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 23.390717, "rss_kib": 53572, "marks": [{"phase": 0, "ns": 10197340}, {"phase": 1, "ns": 11811668}, {"phase": 3, "ns": 15214586}], "diagnostic": "", "acquire_ms": 1.614328, "process_ms": 3.402918}
{"case": "build-concat-4096", "lane": "candidate", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 22.166768, "rss_kib": 53624, "marks": [{"phase": 0, "ns": 10130343}, {"phase": 1, "ns": 11900206}, {"phase": 3, "ns": 14594882}], "diagnostic": "", "acquire_ms": 1.769863, "process_ms": 2.694676}
{"case": "build-concat-4096", "lane": "candidate", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 23.056894, "rss_kib": 53512, "marks": [{"phase": 0, "ns": 9171637}, {"phase": 1, "ns": 10894341}, {"phase": 3, "ns": 14081079}], "diagnostic": "", "acquire_ms": 1.722704, "process_ms": 3.186738}
{"case": "build-concat-4096", "lane": "candidate", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 21.234612, "rss_kib": 53248, "marks": [{"phase": 0, "ns": 9695930}, {"phase": 1, "ns": 11250335}, {"phase": 3, "ns": 14100986}], "diagnostic": "", "acquire_ms": 1.554405, "process_ms": 2.850651}
{"case": "build-concat-4096", "lane": "candidate", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 2.28004, "rss_kib": 2552, "marks": [{"phase": 0, "ns": 191319762344210, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": 0}, {"phase": 1, "ns": 191319762515495, "allocs": 4135, "frees": 4129, "live": 65592, "peak": 120160, "copy_cells": 28650}, {"phase": 3, "ns": 191319762643667, "allocs": 28715, "frees": 28713, "live": 32, "peak": 65624, "copy_cells": 28650}], "diagnostic": "", "acquire_ms": 0.171285, "process_ms": 0.128172}
{"case": "build-join-1024", "lane": "base", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "1:4151188228", "wall_ms": 2.357136, "rss_kib": 2280, "marks": [{"phase": 0, "ns": 191320558906367}, {"phase": 1, "ns": 191320558957754}, {"phase": 3, "ns": 191320558970619}], "diagnostic": "", "acquire_ms": 0.051387, "process_ms": 0.012865}
{"case": "build-join-1024", "lane": "base", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "1:4151188228", "wall_ms": 1.940737, "rss_kib": 2348, "marks": [{"phase": 0, "ns": 191320561050630}, {"phase": 1, "ns": 191320561098701}, {"phase": 3, "ns": 191320561111756}], "diagnostic": "", "acquire_ms": 0.048071, "process_ms": 0.013055}
{"case": "build-join-1024", "lane": "base", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "1:4151188228", "wall_ms": 2.035267, "rss_kib": 2352, "marks": [{"phase": 0, "ns": 191320563180415}, {"phase": 1, "ns": 191320563226422}, {"phase": 3, "ns": 191320563239577}], "diagnostic": "", "acquire_ms": 0.046007, "process_ms": 0.013155}
{"case": "build-join-1024", "lane": "base", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "1:4151188228", "wall_ms": 1.943332, "rss_kib": 2224, "marks": [{"phase": 0, "ns": 191320565226391}, {"phase": 1, "ns": 191320565271667}, {"phase": 3, "ns": 191320565284702}], "diagnostic": "", "acquire_ms": 0.045276, "process_ms": 0.013035}
{"case": "build-join-1024", "lane": "base", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "1:4151188228", "wall_ms": 1.88999, "rss_kib": 2360, "marks": [{"phase": 0, "ns": 191320567290512}, {"phase": 1, "ns": 191320567341448}, {"phase": 3, "ns": 191320567354884}], "diagnostic": "", "acquire_ms": 0.050936, "process_ms": 0.013436}
{"case": "build-join-1024", "lane": "base", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "1:4151188228", "wall_ms": 1.967588, "rss_kib": 2280, "marks": [{"phase": 0, "ns": 191320569378608}, {"phase": 1, "ns": 191320569428543}, {"phase": 3, "ns": 191320569441507}], "diagnostic": "", "acquire_ms": 0.049935, "process_ms": 0.012964}
{"case": "build-join-1024", "lane": "base", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "1:4151188228", "wall_ms": 1.860715, "rss_kib": 2400, "marks": [{"phase": 0, "ns": 191320571343010}, {"phase": 1, "ns": 191320571399958}, {"phase": 3, "ns": 191320571413624}], "diagnostic": "", "acquire_ms": 0.056948, "process_ms": 0.013666}
{"case": "build-join-1024", "lane": "base", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "1:4151188228", "wall_ms": 1.802405, "rss_kib": 2420, "marks": [{"phase": 0, "ns": 191320573286793}, {"phase": 1, "ns": 191320573336647}, {"phase": 3, "ns": 191320573349602}], "diagnostic": "", "acquire_ms": 0.049854, "process_ms": 0.012955}
{"case": "build-join-1024", "lane": "base", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "1:4151188228", "wall_ms": 22.127163, "rss_kib": 47496, "marks": [{"phase": 0, "ns": 10657542}, {"phase": 1, "ns": 11569750}, {"phase": 3, "ns": 12816733}], "diagnostic": "", "acquire_ms": 0.912208, "process_ms": 1.246983}
{"case": "build-join-1024", "lane": "base", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "1:4151188228", "wall_ms": 18.480383, "rss_kib": 47240, "marks": [{"phase": 0, "ns": 8966538}, {"phase": 1, "ns": 10084617}, {"phase": 3, "ns": 11156006}], "diagnostic": "", "acquire_ms": 1.118079, "process_ms": 1.071389}
{"case": "build-join-1024", "lane": "base", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "1:4151188228", "wall_ms": 18.610711, "rss_kib": 47244, "marks": [{"phase": 0, "ns": 9066408}, {"phase": 1, "ns": 10302119}, {"phase": 3, "ns": 11440125}], "diagnostic": "", "acquire_ms": 1.235711, "process_ms": 1.138006}
{"case": "build-join-1024", "lane": "base", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "1:4151188228", "wall_ms": 18.547621, "rss_kib": 47420, "marks": [{"phase": 0, "ns": 9005552}, {"phase": 1, "ns": 10054800}, {"phase": 3, "ns": 11370353}], "diagnostic": "", "acquire_ms": 1.049248, "process_ms": 1.315553}
{"case": "build-join-1024", "lane": "base", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "1:4151188228", "wall_ms": 18.766876, "rss_kib": 47556, "marks": [{"phase": 0, "ns": 8490767}, {"phase": 1, "ns": 9508826}, {"phase": 3, "ns": 11184821}], "diagnostic": "", "acquire_ms": 1.018059, "process_ms": 1.675995}
{"case": "build-join-1024", "lane": "base", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "1:4151188228", "wall_ms": 20.724615, "rss_kib": 47204, "marks": [{"phase": 0, "ns": 10831943}, {"phase": 1, "ns": 11981230}, {"phase": 3, "ns": 13386412}], "diagnostic": "", "acquire_ms": 1.149287, "process_ms": 1.405182}
{"case": "build-join-1024", "lane": "base", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "1:4151188228", "wall_ms": 21.919469, "rss_kib": 47736, "marks": [{"phase": 0, "ns": 9947096}, {"phase": 1, "ns": 10933845}, {"phase": 3, "ns": 12508569}], "diagnostic": "", "acquire_ms": 0.986749, "process_ms": 1.574724}
{"case": "build-join-1024", "lane": "base", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "1:4151188228", "wall_ms": 20.992253, "rss_kib": 47112, "marks": [{"phase": 0, "ns": 8948023}, {"phase": 1, "ns": 9881712}, {"phase": 3, "ns": 11013055}], "diagnostic": "", "acquire_ms": 0.933689, "process_ms": 1.131343}
{"case": "build-join-1024", "lane": "base", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "1:4151188228", "wall_ms": 2.218834, "rss_kib": 2172, "marks": [{"phase": 0, "ns": 191320737310176, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": null}, {"phase": 1, "ns": 191320737383765, "allocs": 9219, "frees": 1033, "live": 98232, "peak": 98248, "copy_cells": null}, {"phase": 3, "ns": 191320737404715, "allocs": 9225, "frees": 9223, "live": 32, "peak": 98264, "copy_cells": null}], "diagnostic": "", "acquire_ms": 0.073589, "process_ms": 0.02095}
{"case": "build-join-1024", "lane": "candidate", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "1:4151188228", "wall_ms": 2.620315, "rss_kib": 2408, "marks": [{"phase": 0, "ns": 191321633470744}, {"phase": 1, "ns": 191321633564472}, {"phase": 3, "ns": 191321633597635}], "diagnostic": "", "acquire_ms": 0.093728, "process_ms": 0.033163}
{"case": "build-join-1024", "lane": "candidate", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "1:4151188228", "wall_ms": 2.143341, "rss_kib": 2404, "marks": [{"phase": 0, "ns": 191321635883586}, {"phase": 1, "ns": 191321635964689}, {"phase": 3, "ns": 191321635997431}], "diagnostic": "", "acquire_ms": 0.081103, "process_ms": 0.032742}
{"case": "build-join-1024", "lane": "candidate", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "1:4151188228", "wall_ms": 1.896924, "rss_kib": 2552, "marks": [{"phase": 0, "ns": 191321637933650}, {"phase": 1, "ns": 191321638026656}, {"phase": 3, "ns": 191321638059809}], "diagnostic": "", "acquire_ms": 0.093006, "process_ms": 0.033153}
{"case": "build-join-1024", "lane": "candidate", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "1:4151188228", "wall_ms": 1.917082, "rss_kib": 2276, "marks": [{"phase": 0, "ns": 191321639945051}, {"phase": 1, "ns": 191321640052514}, {"phase": 3, "ns": 191321640087200}], "diagnostic": "", "acquire_ms": 0.107463, "process_ms": 0.034686}
{"case": "build-join-1024", "lane": "candidate", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "1:4151188228", "wall_ms": 1.884811, "rss_kib": 2408, "marks": [{"phase": 0, "ns": 191321641951362}, {"phase": 1, "ns": 191321642043887}, {"phase": 3, "ns": 191321642076880}], "diagnostic": "", "acquire_ms": 0.092525, "process_ms": 0.032993}
{"case": "build-join-1024", "lane": "candidate", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "1:4151188228", "wall_ms": 1.802295, "rss_kib": 2352, "marks": [{"phase": 0, "ns": 191321643889614}, {"phase": 1, "ns": 191321643971680}, {"phase": 3, "ns": 191321644009151}], "diagnostic": "", "acquire_ms": 0.082066, "process_ms": 0.037471}
{"case": "build-join-1024", "lane": "candidate", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "1:4151188228", "wall_ms": 1.92102, "rss_kib": 2476, "marks": [{"phase": 0, "ns": 191321645780126}, {"phase": 1, "ns": 191321645912627}, {"phase": 3, "ns": 191321645955077}], "diagnostic": "", "acquire_ms": 0.132501, "process_ms": 0.04245}
{"case": "build-join-1024", "lane": "candidate", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "1:4151188228", "wall_ms": 2.02703, "rss_kib": 2480, "marks": [{"phase": 0, "ns": 191321647929178}, {"phase": 1, "ns": 191321648054335}, {"phase": 3, "ns": 191321648088069}], "diagnostic": "", "acquire_ms": 0.125157, "process_ms": 0.033734}
{"case": "build-join-1024", "lane": "candidate", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "1:4151188228", "wall_ms": 20.742048, "rss_kib": 47808, "marks": [{"phase": 0, "ns": 10170690}, {"phase": 1, "ns": 11267658}, {"phase": 3, "ns": 13073360}], "diagnostic": "", "acquire_ms": 1.096968, "process_ms": 1.805702}
{"case": "build-join-1024", "lane": "candidate", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "1:4151188228", "wall_ms": 19.049512, "rss_kib": 47548, "marks": [{"phase": 0, "ns": 9814695}, {"phase": 1, "ns": 10685355}, {"phase": 3, "ns": 11997451}], "diagnostic": "", "acquire_ms": 0.87066, "process_ms": 1.312096}
{"case": "build-join-1024", "lane": "candidate", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "1:4151188228", "wall_ms": 21.834037, "rss_kib": 47948, "marks": [{"phase": 0, "ns": 9813092}, {"phase": 1, "ns": 10721082}, {"phase": 3, "ns": 12383201}], "diagnostic": "", "acquire_ms": 0.90799, "process_ms": 1.662119}
{"case": "build-join-1024", "lane": "candidate", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "1:4151188228", "wall_ms": 20.54757, "rss_kib": 47676, "marks": [{"phase": 0, "ns": 9757186}, {"phase": 1, "ns": 10566469}, {"phase": 3, "ns": 12293722}], "diagnostic": "", "acquire_ms": 0.809283, "process_ms": 1.727253}
{"case": "build-join-1024", "lane": "candidate", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "1:4151188228", "wall_ms": 19.320094, "rss_kib": 47880, "marks": [{"phase": 0, "ns": 9538171}, {"phase": 1, "ns": 10527826}, {"phase": 3, "ns": 11850983}], "diagnostic": "", "acquire_ms": 0.989655, "process_ms": 1.323157}
{"case": "build-join-1024", "lane": "candidate", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "1:4151188228", "wall_ms": 18.618895, "rss_kib": 47872, "marks": [{"phase": 0, "ns": 9218005}, {"phase": 1, "ns": 10158627}, {"phase": 3, "ns": 11472035}], "diagnostic": "", "acquire_ms": 0.940622, "process_ms": 1.313408}
{"case": "build-join-1024", "lane": "candidate", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "1:4151188228", "wall_ms": 18.576816, "rss_kib": 47740, "marks": [{"phase": 0, "ns": 9419807}, {"phase": 1, "ns": 10221977}, {"phase": 3, "ns": 11474961}], "diagnostic": "", "acquire_ms": 0.80217, "process_ms": 1.252984}
{"case": "build-join-1024", "lane": "candidate", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "1:4151188228", "wall_ms": 19.706707, "rss_kib": 48008, "marks": [{"phase": 0, "ns": 9868918}, {"phase": 1, "ns": 10728376}, {"phase": 3, "ns": 12093483}], "diagnostic": "", "acquire_ms": 0.859458, "process_ms": 1.365107}
{"case": "build-join-1024", "lane": "candidate", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "1:4151188228", "wall_ms": 2.100951, "rss_kib": 2344, "marks": [{"phase": 0, "ns": 191321810104199, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": 0}, {"phase": 1, "ns": 191321810194610, "allocs": 1059, "frees": 1053, "live": 16440, "peak": 32768, "copy_cells": 8177}, {"phase": 3, "ns": 191321810239685, "allocs": 9253, "frees": 9251, "live": 32, "peak": 16472, "copy_cells": 8177}], "diagnostic": "", "acquire_ms": 0.090411, "process_ms": 0.045075}
{"case": "build-join-4096", "lane": "base", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "1:3695447812", "wall_ms": 2.423221, "rss_kib": 2660, "marks": [{"phase": 0, "ns": 191322657377364}, {"phase": 1, "ns": 191322657615455}, {"phase": 3, "ns": 191322657665670}], "diagnostic": "", "acquire_ms": 0.238091, "process_ms": 0.050215}
{"case": "build-join-4096", "lane": "base", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "1:3695447812", "wall_ms": 2.239392, "rss_kib": 2664, "marks": [{"phase": 0, "ns": 191322659745611}, {"phase": 1, "ns": 191322660054636}, {"phase": 3, "ns": 191322660105993}], "diagnostic": "", "acquire_ms": 0.309025, "process_ms": 0.051357}
{"case": "build-join-4096", "lane": "base", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "1:3695447812", "wall_ms": 2.034074, "rss_kib": 2680, "marks": [{"phase": 0, "ns": 191322661934007}, {"phase": 1, "ns": 191322662186636}, {"phase": 3, "ns": 191322662238023}], "diagnostic": "", "acquire_ms": 0.252629, "process_ms": 0.051387}
{"case": "build-join-4096", "lane": "base", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "1:3695447812", "wall_ms": 2.101933, "rss_kib": 2680, "marks": [{"phase": 0, "ns": 191322664162359}, {"phase": 1, "ns": 191322664380312}, {"phase": 3, "ns": 191322664429675}], "diagnostic": "", "acquire_ms": 0.217953, "process_ms": 0.049363}
{"case": "build-join-4096", "lane": "base", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "1:3695447812", "wall_ms": 2.094598, "rss_kib": 2736, "marks": [{"phase": 0, "ns": 191322666305880}, {"phase": 1, "ns": 191322666556284}, {"phase": 3, "ns": 191322666607822}], "diagnostic": "", "acquire_ms": 0.250404, "process_ms": 0.051538}
{"case": "build-join-4096", "lane": "base", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "1:3695447812", "wall_ms": 2.071475, "rss_kib": 2736, "marks": [{"phase": 0, "ns": 191322668574428}, {"phase": 1, "ns": 191322668791620}, {"phase": 3, "ns": 191322668839200}], "diagnostic": "", "acquire_ms": 0.217192, "process_ms": 0.04758}
{"case": "build-join-4096", "lane": "base", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "1:3695447812", "wall_ms": 2.103816, "rss_kib": 2744, "marks": [{"phase": 0, "ns": 191322670671872}, {"phase": 1, "ns": 191322670910163}, {"phase": 3, "ns": 191322670960619}], "diagnostic": "", "acquire_ms": 0.238291, "process_ms": 0.050456}
{"case": "build-join-4096", "lane": "base", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "1:3695447812", "wall_ms": 2.124906, "rss_kib": 2600, "marks": [{"phase": 0, "ns": 191322672953304}, {"phase": 1, "ns": 191322673193590}, {"phase": 3, "ns": 191322673242913}], "diagnostic": "", "acquire_ms": 0.240286, "process_ms": 0.049323}
{"case": "build-join-4096", "lane": "base", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "1:3695447812", "wall_ms": 23.017189, "rss_kib": 54412, "marks": [{"phase": 0, "ns": 10311006}, {"phase": 1, "ns": 12601716}, {"phase": 3, "ns": 16042455}], "diagnostic": "", "acquire_ms": 2.29071, "process_ms": 3.440739}
{"case": "build-join-4096", "lane": "base", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "1:3695447812", "wall_ms": 25.615692, "rss_kib": 53960, "marks": [{"phase": 0, "ns": 9422472}, {"phase": 1, "ns": 11474099}, {"phase": 3, "ns": 17621446}], "diagnostic": "", "acquire_ms": 2.051627, "process_ms": 6.147347}
{"case": "build-join-4096", "lane": "base", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "1:3695447812", "wall_ms": 25.263004, "rss_kib": 54212, "marks": [{"phase": 0, "ns": 10108141}, {"phase": 1, "ns": 12090507}, {"phase": 3, "ns": 15636876}], "diagnostic": "", "acquire_ms": 1.982366, "process_ms": 3.546369}
{"case": "build-join-4096", "lane": "base", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "1:3695447812", "wall_ms": 25.806654, "rss_kib": 54144, "marks": [{"phase": 0, "ns": 9422973}, {"phase": 1, "ns": 11513494}, {"phase": 3, "ns": 15305859}], "diagnostic": "", "acquire_ms": 2.090521, "process_ms": 3.792365}
{"case": "build-join-4096", "lane": "base", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "1:3695447812", "wall_ms": 21.898039, "rss_kib": 54028, "marks": [{"phase": 0, "ns": 9170905}, {"phase": 1, "ns": 11218234}, {"phase": 3, "ns": 14794410}], "diagnostic": "", "acquire_ms": 2.047329, "process_ms": 3.576176}
{"case": "build-join-4096", "lane": "base", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "1:3695447812", "wall_ms": 23.10711, "rss_kib": 54136, "marks": [{"phase": 0, "ns": 9780179}, {"phase": 1, "ns": 11636587}, {"phase": 3, "ns": 14871065}], "diagnostic": "", "acquire_ms": 1.856408, "process_ms": 3.234478}
{"case": "build-join-4096", "lane": "base", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "1:3695447812", "wall_ms": 21.806245, "rss_kib": 53940, "marks": [{"phase": 0, "ns": 9590941}, {"phase": 1, "ns": 11419506}, {"phase": 3, "ns": 14497587}], "diagnostic": "", "acquire_ms": 1.828565, "process_ms": 3.078081}
{"case": "build-join-4096", "lane": "base", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "1:3695447812", "wall_ms": 23.468975, "rss_kib": 54156, "marks": [{"phase": 0, "ns": 8964634}, {"phase": 1, "ns": 10866788}, {"phase": 3, "ns": 14132295}], "diagnostic": "", "acquire_ms": 1.902154, "process_ms": 3.265507}
{"case": "build-join-4096", "lane": "base", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "1:3695447812", "wall_ms": 2.467915, "rss_kib": 2660, "marks": [{"phase": 0, "ns": 191322866916572, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": null}, {"phase": 1, "ns": 191322867213685, "allocs": 36867, "frees": 4105, "live": 393144, "peak": 393160, "copy_cells": null}, {"phase": 3, "ns": 191322867315358, "allocs": 36873, "frees": 36871, "live": 32, "peak": 393176, "copy_cells": null}], "diagnostic": "", "acquire_ms": 0.297113, "process_ms": 0.101673}
{"case": "build-join-4096", "lane": "candidate", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "1:3695447812", "wall_ms": 2.638609, "rss_kib": 2616, "marks": [{"phase": 0, "ns": 191323763248145}, {"phase": 1, "ns": 191323763421473}, {"phase": 3, "ns": 191323763595944}], "diagnostic": "", "acquire_ms": 0.173328, "process_ms": 0.174471}
{"case": "build-join-4096", "lane": "candidate", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "1:3695447812", "wall_ms": 2.324875, "rss_kib": 2668, "marks": [{"phase": 0, "ns": 191323765780653}, {"phase": 1, "ns": 191323765949553}, {"phase": 3, "ns": 191323766122661}], "diagnostic": "", "acquire_ms": 0.1689, "process_ms": 0.173108}
{"case": "build-join-4096", "lane": "candidate", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "1:3695447812", "wall_ms": 2.065974, "rss_kib": 2616, "marks": [{"phase": 0, "ns": 191323768080480}, {"phase": 1, "ns": 191323768255271}, {"phase": 3, "ns": 191323768385218}], "diagnostic": "", "acquire_ms": 0.174791, "process_ms": 0.129947}
{"case": "build-join-4096", "lane": "candidate", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "1:3695447812", "wall_ms": 2.413874, "rss_kib": 2532, "marks": [{"phase": 0, "ns": 191323770560038}, {"phase": 1, "ns": 191323770730962}, {"phase": 3, "ns": 191323770856881}], "diagnostic": "", "acquire_ms": 0.170924, "process_ms": 0.125919}
{"case": "build-join-4096", "lane": "candidate", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "1:3695447812", "wall_ms": 2.218173, "rss_kib": 2616, "marks": [{"phase": 0, "ns": 191323772872339}, {"phase": 1, "ns": 191323773109478}, {"phase": 3, "ns": 191323773248311}], "diagnostic": "", "acquire_ms": 0.237139, "process_ms": 0.138833}
{"case": "build-join-4096", "lane": "candidate", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "1:3695447812", "wall_ms": 2.115097, "rss_kib": 2676, "marks": [{"phase": 0, "ns": 191323775159963}, {"phase": 1, "ns": 191323775326589}, {"phase": 3, "ns": 191323775474078}], "diagnostic": "", "acquire_ms": 0.166626, "process_ms": 0.147489}
{"case": "build-join-4096", "lane": "candidate", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "1:3695447812", "wall_ms": 2.102954, "rss_kib": 2424, "marks": [{"phase": 0, "ns": 191323777389367}, {"phase": 1, "ns": 191323777578606}, {"phase": 3, "ns": 191323777705035}], "diagnostic": "", "acquire_ms": 0.189239, "process_ms": 0.126429}
{"case": "build-join-4096", "lane": "candidate", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "1:3695447812", "wall_ms": 2.114195, "rss_kib": 2604, "marks": [{"phase": 0, "ns": 191323779574427}, {"phase": 1, "ns": 191323779752845}, {"phase": 3, "ns": 191323779897619}], "diagnostic": "", "acquire_ms": 0.178418, "process_ms": 0.144774}
{"case": "build-join-4096", "lane": "candidate", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "1:3695447812", "wall_ms": 22.058522, "rss_kib": 54656, "marks": [{"phase": 0, "ns": 9819795}, {"phase": 1, "ns": 11425066}, {"phase": 3, "ns": 14920659}], "diagnostic": "", "acquire_ms": 1.605271, "process_ms": 3.495593}
{"case": "build-join-4096", "lane": "candidate", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "1:3695447812", "wall_ms": 22.834523, "rss_kib": 54476, "marks": [{"phase": 0, "ns": 10445851}, {"phase": 1, "ns": 11999234}, {"phase": 3, "ns": 15325005}], "diagnostic": "", "acquire_ms": 1.553383, "process_ms": 3.325771}
{"case": "build-join-4096", "lane": "candidate", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "1:3695447812", "wall_ms": 23.136735, "rss_kib": 55308, "marks": [{"phase": 0, "ns": 10141304}, {"phase": 1, "ns": 11830424}, {"phase": 3, "ns": 15266855}], "diagnostic": "", "acquire_ms": 1.68912, "process_ms": 3.436431}
{"case": "build-join-4096", "lane": "candidate", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "1:3695447812", "wall_ms": 23.790103, "rss_kib": 54716, "marks": [{"phase": 0, "ns": 11026020}, {"phase": 1, "ns": 12538786}, {"phase": 3, "ns": 16253824}], "diagnostic": "", "acquire_ms": 1.512766, "process_ms": 3.715038}
{"case": "build-join-4096", "lane": "candidate", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "1:3695447812", "wall_ms": 21.203923, "rss_kib": 54572, "marks": [{"phase": 0, "ns": 9119789}, {"phase": 1, "ns": 10681748}, {"phase": 3, "ns": 14021436}], "diagnostic": "", "acquire_ms": 1.561959, "process_ms": 3.339688}
{"case": "build-join-4096", "lane": "candidate", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "1:3695447812", "wall_ms": 23.986556, "rss_kib": 54136, "marks": [{"phase": 0, "ns": 9084542}, {"phase": 1, "ns": 10985894}, {"phase": 3, "ns": 14958150}], "diagnostic": "", "acquire_ms": 1.901352, "process_ms": 3.972256}
{"case": "build-join-4096", "lane": "candidate", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "1:3695447812", "wall_ms": 21.947232, "rss_kib": 54524, "marks": [{"phase": 0, "ns": 9595801}, {"phase": 1, "ns": 11296403}, {"phase": 3, "ns": 14600913}], "diagnostic": "", "acquire_ms": 1.700602, "process_ms": 3.30451}
{"case": "build-join-4096", "lane": "candidate", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "1:3695447812", "wall_ms": 26.723101, "rss_kib": 54608, "marks": [{"phase": 0, "ns": 9676784}, {"phase": 1, "ns": 11479028}, {"phase": 3, "ns": 15896418}], "diagnostic": "", "acquire_ms": 1.802244, "process_ms": 4.41739}
{"case": "build-join-4096", "lane": "candidate", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "1:3695447812", "wall_ms": 2.476062, "rss_kib": 2664, "marks": [{"phase": 0, "ns": 191323969319563, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": 0}, {"phase": 1, "ns": 191323969509012, "allocs": 4135, "frees": 4129, "live": 65592, "peak": 131072, "copy_cells": 32751}, {"phase": 3, "ns": 191323969687851, "allocs": 36905, "frees": 36903, "live": 32, "peak": 65624, "copy_cells": 32751}], "diagnostic": "", "acquire_ms": 0.189449, "process_ms": 0.178839}
{"case": "build-repeat-1024", "lane": "base", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 2.19558, "rss_kib": 2424, "marks": [{"phase": 0, "ns": 191324816435500}, {"phase": 1, "ns": 191324816475727}, {"phase": 3, "ns": 191324816485786}], "diagnostic": "", "acquire_ms": 0.040227, "process_ms": 0.010059}
{"case": "build-repeat-1024", "lane": "base", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 1.840477, "rss_kib": 2356, "marks": [{"phase": 0, "ns": 191324818408609}, {"phase": 1, "ns": 191324818445769}, {"phase": 3, "ns": 191324818456169}], "diagnostic": "", "acquire_ms": 0.03716, "process_ms": 0.0104}
{"case": "build-repeat-1024", "lane": "base", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 1.883769, "rss_kib": 2168, "marks": [{"phase": 0, "ns": 191324820436691}, {"phase": 1, "ns": 191324820482338}, {"phase": 3, "ns": 191324820492497}], "diagnostic": "", "acquire_ms": 0.045647, "process_ms": 0.010159}
{"case": "build-repeat-1024", "lane": "base", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 1.825829, "rss_kib": 2412, "marks": [{"phase": 0, "ns": 191324822356288}, {"phase": 1, "ns": 191324822396965}, {"phase": 3, "ns": 191324822406984}], "diagnostic": "", "acquire_ms": 0.040677, "process_ms": 0.010019}
{"case": "build-repeat-1024", "lane": "base", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 1.744355, "rss_kib": 2360, "marks": [{"phase": 0, "ns": 191324824227393}, {"phase": 1, "ns": 191324824264303}, {"phase": 3, "ns": 191324824274452}], "diagnostic": "", "acquire_ms": 0.03691, "process_ms": 0.010149}
{"case": "build-repeat-1024", "lane": "base", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 1.861466, "rss_kib": 2420, "marks": [{"phase": 0, "ns": 191324826158402}, {"phase": 1, "ns": 191324826204148}, {"phase": 3, "ns": 191324826214698}], "diagnostic": "", "acquire_ms": 0.045746, "process_ms": 0.01055}
{"case": "build-repeat-1024", "lane": "base", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 1.914207, "rss_kib": 2176, "marks": [{"phase": 0, "ns": 191324828200170}, {"phase": 1, "ns": 191324828238142}, {"phase": 3, "ns": 191324828248712}], "diagnostic": "", "acquire_ms": 0.037972, "process_ms": 0.01057}
{"case": "build-repeat-1024", "lane": "base", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 1.771877, "rss_kib": 2412, "marks": [{"phase": 0, "ns": 191324830122412}, {"phase": 1, "ns": 191324830159332}, {"phase": 3, "ns": 191324830169401}], "diagnostic": "", "acquire_ms": 0.03692, "process_ms": 0.010069}
{"case": "build-repeat-1024", "lane": "base", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 22.122994, "rss_kib": 47304, "marks": [{"phase": 0, "ns": 10450449}, {"phase": 1, "ns": 11108216}, {"phase": 3, "ns": 12345149}], "diagnostic": "", "acquire_ms": 0.657767, "process_ms": 1.236933}
{"case": "build-repeat-1024", "lane": "base", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 19.253719, "rss_kib": 47048, "marks": [{"phase": 0, "ns": 9271355}, {"phase": 1, "ns": 10078445}, {"phase": 3, "ns": 11499036}], "diagnostic": "", "acquire_ms": 0.80709, "process_ms": 1.420591}
{"case": "build-repeat-1024", "lane": "base", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 18.122966, "rss_kib": 46856, "marks": [{"phase": 0, "ns": 9232452}, {"phase": 1, "ns": 9877234}, {"phase": 3, "ns": 10981215}], "diagnostic": "", "acquire_ms": 0.644782, "process_ms": 1.103981}
{"case": "build-repeat-1024", "lane": "base", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 18.274654, "rss_kib": 46908, "marks": [{"phase": 0, "ns": 9083891}, {"phase": 1, "ns": 9927860}, {"phase": 3, "ns": 11431629}], "diagnostic": "", "acquire_ms": 0.843969, "process_ms": 1.503769}
{"case": "build-repeat-1024", "lane": "base", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 17.756872, "rss_kib": 46912, "marks": [{"phase": 0, "ns": 8970836}, {"phase": 1, "ns": 9619616}, {"phase": 3, "ns": 10655678}], "diagnostic": "", "acquire_ms": 0.64878, "process_ms": 1.036062}
{"case": "build-repeat-1024", "lane": "base", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 18.370445, "rss_kib": 46912, "marks": [{"phase": 0, "ns": 9777444}, {"phase": 1, "ns": 10478322}, {"phase": 3, "ns": 11557207}], "diagnostic": "", "acquire_ms": 0.700878, "process_ms": 1.078885}
{"case": "build-repeat-1024", "lane": "base", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 16.460226, "rss_kib": 46524, "marks": [{"phase": 0, "ns": 8407128}, {"phase": 1, "ns": 9066127}, {"phase": 3, "ns": 9998854}], "diagnostic": "", "acquire_ms": 0.658999, "process_ms": 0.932727}
{"case": "build-repeat-1024", "lane": "base", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 20.346599, "rss_kib": 46988, "marks": [{"phase": 0, "ns": 9325348}, {"phase": 1, "ns": 10057194}, {"phase": 3, "ns": 11342910}], "diagnostic": "", "acquire_ms": 0.731846, "process_ms": 1.285716}
{"case": "build-repeat-1024", "lane": "base", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 2.309896, "rss_kib": 2424, "marks": [{"phase": 0, "ns": 191324984702934, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": null}, {"phase": 1, "ns": 191324984751967, "allocs": 6154, "frees": 9, "live": 73744, "peak": 73760, "copy_cells": null}, {"phase": 3, "ns": 191324984767236, "allocs": 6160, "frees": 6158, "live": 32, "peak": 73776, "copy_cells": null}], "diagnostic": "", "acquire_ms": 0.049033, "process_ms": 0.015269}
{"case": "build-repeat-1024", "lane": "candidate", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 2.153009, "rss_kib": 2412, "marks": [{"phase": 0, "ns": 191325830185116}, {"phase": 1, "ns": 191325830209202}, {"phase": 3, "ns": 191325830239860}], "diagnostic": "", "acquire_ms": 0.024086, "process_ms": 0.030658}
{"case": "build-repeat-1024", "lane": "candidate", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 1.894559, "rss_kib": 2360, "marks": [{"phase": 0, "ns": 191325832233097}, {"phase": 1, "ns": 191325832251602}, {"phase": 3, "ns": 191325832276018}], "diagnostic": "", "acquire_ms": 0.018505, "process_ms": 0.024416}
{"case": "build-repeat-1024", "lane": "candidate", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 1.956828, "rss_kib": 2168, "marks": [{"phase": 0, "ns": 191325834300193}, {"phase": 1, "ns": 191325834320842}, {"phase": 3, "ns": 191325834349065}], "diagnostic": "", "acquire_ms": 0.020649, "process_ms": 0.028223}
{"case": "build-repeat-1024", "lane": "candidate", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 1.979711, "rss_kib": 2288, "marks": [{"phase": 0, "ns": 191325836372249}, {"phase": 1, "ns": 191325836395152}, {"phase": 3, "ns": 191325836419909}], "diagnostic": "", "acquire_ms": 0.022903, "process_ms": 0.024757}
{"case": "build-repeat-1024", "lane": "candidate", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 1.780574, "rss_kib": 2288, "marks": [{"phase": 0, "ns": 191325838375755}, {"phase": 1, "ns": 191325838390983}, {"phase": 3, "ns": 191325838415720}], "diagnostic": "", "acquire_ms": 0.015228, "process_ms": 0.024737}
{"case": "build-repeat-1024", "lane": "candidate", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 1.990932, "rss_kib": 2348, "marks": [{"phase": 0, "ns": 191325840413205}, {"phase": 1, "ns": 191325840430748}, {"phase": 3, "ns": 191325840455295}], "diagnostic": "", "acquire_ms": 0.017543, "process_ms": 0.024547}
{"case": "build-repeat-1024", "lane": "candidate", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 1.782608, "rss_kib": 2420, "marks": [{"phase": 0, "ns": 191325842354202}, {"phase": 1, "ns": 191325842373489}, {"phase": 3, "ns": 191325842397915}], "diagnostic": "", "acquire_ms": 0.019287, "process_ms": 0.024426}
{"case": "build-repeat-1024", "lane": "candidate", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 1.740928, "rss_kib": 2276, "marks": [{"phase": 0, "ns": 191325844219306}, {"phase": 1, "ns": 191325844234835}, {"phase": 3, "ns": 191325844259372}], "diagnostic": "", "acquire_ms": 0.015529, "process_ms": 0.024537}
{"case": "build-repeat-1024", "lane": "candidate", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 18.131512, "rss_kib": 47440, "marks": [{"phase": 0, "ns": 9437521}, {"phase": 1, "ns": 9695219}, {"phase": 3, "ns": 11148031}], "diagnostic": "", "acquire_ms": 0.257698, "process_ms": 1.452812}
{"case": "build-repeat-1024", "lane": "candidate", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 19.344771, "rss_kib": 47552, "marks": [{"phase": 0, "ns": 9670693}, {"phase": 1, "ns": 9999355}, {"phase": 3, "ns": 11896991}], "diagnostic": "", "acquire_ms": 0.328662, "process_ms": 1.897636}
{"case": "build-repeat-1024", "lane": "candidate", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 19.516276, "rss_kib": 47624, "marks": [{"phase": 0, "ns": 10208632}, {"phase": 1, "ns": 10555188}, {"phase": 3, "ns": 12330893}], "diagnostic": "", "acquire_ms": 0.346556, "process_ms": 1.775705}
{"case": "build-repeat-1024", "lane": "candidate", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 19.305867, "rss_kib": 47360, "marks": [{"phase": 0, "ns": 9848670}, {"phase": 1, "ns": 10138178}, {"phase": 3, "ns": 11846164}], "diagnostic": "", "acquire_ms": 0.289508, "process_ms": 1.707986}
{"case": "build-repeat-1024", "lane": "candidate", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 20.354034, "rss_kib": 47564, "marks": [{"phase": 0, "ns": 11702322}, {"phase": 1, "ns": 11985939}, {"phase": 3, "ns": 13543099}], "diagnostic": "", "acquire_ms": 0.283617, "process_ms": 1.55716}
{"case": "build-repeat-1024", "lane": "candidate", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 21.212179, "rss_kib": 47168, "marks": [{"phase": 0, "ns": 10255431}, {"phase": 1, "ns": 10604422}, {"phase": 3, "ns": 12103732}], "diagnostic": "", "acquire_ms": 0.348991, "process_ms": 1.49931}
{"case": "build-repeat-1024", "lane": "candidate", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 18.242593, "rss_kib": 46916, "marks": [{"phase": 0, "ns": 9246138}, {"phase": 1, "ns": 9500459}, {"phase": 3, "ns": 11037121}], "diagnostic": "", "acquire_ms": 0.254321, "process_ms": 1.536662}
{"case": "build-repeat-1024", "lane": "candidate", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 17.64986, "rss_kib": 47488, "marks": [{"phase": 0, "ns": 9116713}, {"phase": 1, "ns": 9426309}, {"phase": 3, "ns": 10948764}], "diagnostic": "", "acquire_ms": 0.309596, "process_ms": 1.522455}
{"case": "build-repeat-1024", "lane": "candidate", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "1:4141009920", "wall_ms": 2.464339, "rss_kib": 2224, "marks": [{"phase": 0, "ns": 191326002064974, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": 0}, {"phase": 1, "ns": 191326002089020, "allocs": 15, "frees": 9, "live": 16440, "peak": 16456, "copy_cells": 3072}, {"phase": 3, "ns": 191326002154444, "allocs": 6163, "frees": 6161, "live": 32, "peak": 16472, "copy_cells": 3072}], "diagnostic": "", "acquire_ms": 0.024046, "process_ms": 0.065424}
{"case": "build-repeat-4096", "lane": "base", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 2.777011, "rss_kib": 2668, "marks": [{"phase": 0, "ns": 191326799616285}, {"phase": 1, "ns": 191326799871239}, {"phase": 3, "ns": 191326799912567}], "diagnostic": "", "acquire_ms": 0.254954, "process_ms": 0.041328}
{"case": "build-repeat-4096", "lane": "base", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 2.315197, "rss_kib": 2532, "marks": [{"phase": 0, "ns": 191326802225359}, {"phase": 1, "ns": 191326802465213}, {"phase": 3, "ns": 191326802504568}], "diagnostic": "", "acquire_ms": 0.239854, "process_ms": 0.039355}
{"case": "build-repeat-4096", "lane": "base", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 2.077827, "rss_kib": 2472, "marks": [{"phase": 0, "ns": 191326804492875}, {"phase": 1, "ns": 191326804665772}, {"phase": 3, "ns": 191326804702762}], "diagnostic": "", "acquire_ms": 0.172897, "process_ms": 0.03699}
{"case": "build-repeat-4096", "lane": "base", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 1.943663, "rss_kib": 2532, "marks": [{"phase": 0, "ns": 191326806603734}, {"phase": 1, "ns": 191326806773516}, {"phase": 3, "ns": 191326806810726}], "diagnostic": "", "acquire_ms": 0.169782, "process_ms": 0.03721}
{"case": "build-repeat-4096", "lane": "base", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 2.21143, "rss_kib": 2536, "marks": [{"phase": 0, "ns": 191326808775208}, {"phase": 1, "ns": 191326809039829}, {"phase": 3, "ns": 191326809078523}], "diagnostic": "", "acquire_ms": 0.264621, "process_ms": 0.038694}
{"case": "build-repeat-4096", "lane": "base", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 2.212011, "rss_kib": 2668, "marks": [{"phase": 0, "ns": 191326811197517}, {"phase": 1, "ns": 191326811369724}, {"phase": 3, "ns": 191326811407215}], "diagnostic": "", "acquire_ms": 0.172207, "process_ms": 0.037491}
{"case": "build-repeat-4096", "lane": "base", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 2.019947, "rss_kib": 2612, "marks": [{"phase": 0, "ns": 191326813378019}, {"phase": 1, "ns": 191326813551177}, {"phase": 3, "ns": 191326813587456}], "diagnostic": "", "acquire_ms": 0.173158, "process_ms": 0.036279}
{"case": "build-repeat-4096", "lane": "base", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 2.100069, "rss_kib": 2676, "marks": [{"phase": 0, "ns": 191326815541418}, {"phase": 1, "ns": 191326815742719}, {"phase": 3, "ns": 191326815782274}], "diagnostic": "", "acquire_ms": 0.201301, "process_ms": 0.039555}
{"case": "build-repeat-4096", "lane": "base", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 21.193904, "rss_kib": 51900, "marks": [{"phase": 0, "ns": 9399589}, {"phase": 1, "ns": 10984381}, {"phase": 3, "ns": 14204332}], "diagnostic": "", "acquire_ms": 1.584792, "process_ms": 3.219951}
{"case": "build-repeat-4096", "lane": "base", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 19.812848, "rss_kib": 51904, "marks": [{"phase": 0, "ns": 8815693}, {"phase": 1, "ns": 10130945}, {"phase": 3, "ns": 12765396}], "diagnostic": "", "acquire_ms": 1.315252, "process_ms": 2.634451}
{"case": "build-repeat-4096", "lane": "base", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 20.617222, "rss_kib": 51904, "marks": [{"phase": 0, "ns": 9470212}, {"phase": 1, "ns": 10865175}, {"phase": 3, "ns": 13489297}], "diagnostic": "", "acquire_ms": 1.394963, "process_ms": 2.624122}
{"case": "build-repeat-4096", "lane": "base", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 22.561095, "rss_kib": 51984, "marks": [{"phase": 0, "ns": 11395991}, {"phase": 1, "ns": 12678902}, {"phase": 3, "ns": 15404626}], "diagnostic": "", "acquire_ms": 1.282911, "process_ms": 2.725724}
{"case": "build-repeat-4096", "lane": "base", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 20.124388, "rss_kib": 52416, "marks": [{"phase": 0, "ns": 9214849}, {"phase": 1, "ns": 10436443}, {"phase": 3, "ns": 13054934}], "diagnostic": "", "acquire_ms": 1.221594, "process_ms": 2.618491}
{"case": "build-repeat-4096", "lane": "base", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 21.25521, "rss_kib": 52424, "marks": [{"phase": 0, "ns": 9689869}, {"phase": 1, "ns": 11039846}, {"phase": 3, "ns": 13915394}], "diagnostic": "", "acquire_ms": 1.349977, "process_ms": 2.875548}
{"case": "build-repeat-4096", "lane": "base", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 25.112209, "rss_kib": 50048, "marks": [{"phase": 0, "ns": 11664249}, {"phase": 1, "ns": 13254091}, {"phase": 3, "ns": 17091882}], "diagnostic": "", "acquire_ms": 1.589842, "process_ms": 3.837791}
{"case": "build-repeat-4096", "lane": "base", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 24.299819, "rss_kib": 52492, "marks": [{"phase": 0, "ns": 9786522}, {"phase": 1, "ns": 11086875}, {"phase": 3, "ns": 14288091}], "diagnostic": "", "acquire_ms": 1.300353, "process_ms": 3.201216}
{"case": "build-repeat-4096", "lane": "base", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 2.344472, "rss_kib": 2536, "marks": [{"phase": 0, "ns": 191326994395890, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": null}, {"phase": 1, "ns": 191326994605918, "allocs": 24586, "frees": 9, "live": 294928, "peak": 294944, "copy_cells": null}, {"phase": 3, "ns": 191326994659599, "allocs": 24592, "frees": 24590, "live": 32, "peak": 294960, "copy_cells": null}], "diagnostic": "", "acquire_ms": 0.210028, "process_ms": 0.053681}
{"case": "build-repeat-4096", "lane": "candidate", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 2.489256, "rss_kib": 2224, "marks": [{"phase": 0, "ns": 191327890897094}, {"phase": 1, "ns": 191327890934054}, {"phase": 3, "ns": 191327891045425}], "diagnostic": "", "acquire_ms": 0.03696, "process_ms": 0.111371}
{"case": "build-repeat-4096", "lane": "candidate", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 1.98434, "rss_kib": 2356, "marks": [{"phase": 0, "ns": 191327893107291}, {"phase": 1, "ns": 191327893139022}, {"phase": 3, "ns": 191327893246425}], "diagnostic": "", "acquire_ms": 0.031731, "process_ms": 0.107403}
{"case": "build-repeat-4096", "lane": "candidate", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 1.903025, "rss_kib": 2424, "marks": [{"phase": 0, "ns": 191327895168376}, {"phase": 1, "ns": 191327895202000}, {"phase": 3, "ns": 191327895295026}], "diagnostic": "", "acquire_ms": 0.033624, "process_ms": 0.093026}
{"case": "build-repeat-4096", "lane": "candidate", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 2.166685, "rss_kib": 2420, "marks": [{"phase": 0, "ns": 191327897402219}, {"phase": 1, "ns": 191327897436734}, {"phase": 3, "ns": 191327897530341}], "diagnostic": "", "acquire_ms": 0.034515, "process_ms": 0.093607}
{"case": "build-repeat-4096", "lane": "candidate", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 1.93721, "rss_kib": 2412, "marks": [{"phase": 0, "ns": 191327899441482}, {"phase": 1, "ns": 191327899481729}, {"phase": 3, "ns": 191327899578282}], "diagnostic": "", "acquire_ms": 0.040247, "process_ms": 0.096553}
{"case": "build-repeat-4096", "lane": "candidate", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 1.841228, "rss_kib": 2288, "marks": [{"phase": 0, "ns": 191327901480806}, {"phase": 1, "ns": 191327901510632}, {"phase": 3, "ns": 191327901603759}], "diagnostic": "", "acquire_ms": 0.029826, "process_ms": 0.093127}
{"case": "build-repeat-4096", "lane": "candidate", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 1.969612, "rss_kib": 2412, "marks": [{"phase": 0, "ns": 191327903480865}, {"phase": 1, "ns": 191327903513016}, {"phase": 3, "ns": 191327903611393}], "diagnostic": "", "acquire_ms": 0.032151, "process_ms": 0.098377}
{"case": "build-repeat-4096", "lane": "candidate", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 1.893377, "rss_kib": 2276, "marks": [{"phase": 0, "ns": 191327905560165}, {"phase": 1, "ns": 191327905590412}, {"phase": 3, "ns": 191327905690412}], "diagnostic": "", "acquire_ms": 0.030247, "process_ms": 0.1}
{"case": "build-repeat-4096", "lane": "candidate", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 19.81917, "rss_kib": 52412, "marks": [{"phase": 0, "ns": 9511711}, {"phase": 1, "ns": 9785260}, {"phase": 3, "ns": 13119597}], "diagnostic": "", "acquire_ms": 0.273549, "process_ms": 3.334337}
{"case": "build-repeat-4096", "lane": "candidate", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 20.497515, "rss_kib": 51684, "marks": [{"phase": 0, "ns": 9034647}, {"phase": 1, "ns": 9309247}, {"phase": 3, "ns": 12972859}], "diagnostic": "", "acquire_ms": 0.2746, "process_ms": 3.663612}
{"case": "build-repeat-4096", "lane": "candidate", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 20.306454, "rss_kib": 52288, "marks": [{"phase": 0, "ns": 9128745}, {"phase": 1, "ns": 9386053}, {"phase": 3, "ns": 12785283}], "diagnostic": "", "acquire_ms": 0.257308, "process_ms": 3.39923}
{"case": "build-repeat-4096", "lane": "candidate", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 19.86144, "rss_kib": 52872, "marks": [{"phase": 0, "ns": 9251858}, {"phase": 1, "ns": 9553059}, {"phase": 3, "ns": 12593329}], "diagnostic": "", "acquire_ms": 0.301201, "process_ms": 3.04027}
{"case": "build-repeat-4096", "lane": "candidate", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 20.776223, "rss_kib": 53128, "marks": [{"phase": 0, "ns": 10182883}, {"phase": 1, "ns": 10442324}, {"phase": 3, "ns": 13780649}], "diagnostic": "", "acquire_ms": 0.259441, "process_ms": 3.338325}
{"case": "build-repeat-4096", "lane": "candidate", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 19.853875, "rss_kib": 53000, "marks": [{"phase": 0, "ns": 9275083}, {"phase": 1, "ns": 9547319}, {"phase": 3, "ns": 12679553}], "diagnostic": "", "acquire_ms": 0.272236, "process_ms": 3.132234}
{"case": "build-repeat-4096", "lane": "candidate", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 23.325092, "rss_kib": 52808, "marks": [{"phase": 0, "ns": 10115796}, {"phase": 1, "ns": 10408470}, {"phase": 3, "ns": 13726998}], "diagnostic": "", "acquire_ms": 0.292674, "process_ms": 3.318528}
{"case": "build-repeat-4096", "lane": "candidate", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 21.586679, "rss_kib": 52032, "marks": [{"phase": 0, "ns": 9769509}, {"phase": 1, "ns": 10160811}, {"phase": 3, "ns": 14147123}], "diagnostic": "", "acquire_ms": 0.391302, "process_ms": 3.986312}
{"case": "build-repeat-4096", "lane": "candidate", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "1:1196109824", "wall_ms": 2.189488, "rss_kib": 2216, "marks": [{"phase": 0, "ns": 191328075434393, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": 0}, {"phase": 1, "ns": 191328075470281, "allocs": 15, "frees": 9, "live": 65592, "peak": 65608, "copy_cells": 12288}, {"phase": 3, "ns": 191328075597222, "allocs": 24595, "frees": 24593, "live": 32, "peak": 65624, "copy_cells": 12288}], "diagnostic": "", "acquire_ms": 0.035888, "process_ms": 0.126941}
{"case": "build-append-1024", "lane": "base", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "1:1046732800", "wall_ms": 3.648312, "rss_kib": 2296, "marks": [{"phase": 0, "ns": 191328871927783}, {"phase": 1, "ns": 191328873429578}, {"phase": 3, "ns": 191328873433646}], "diagnostic": "", "acquire_ms": 1.501795, "process_ms": 0.004068}
{"case": "build-append-1024", "lane": "base", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "1:1046732800", "wall_ms": 3.282699, "rss_kib": 2160, "marks": [{"phase": 0, "ns": 191328875496805}, {"phase": 1, "ns": 191328876852854}, {"phase": 3, "ns": 191328876857293}], "diagnostic": "", "acquire_ms": 1.356049, "process_ms": 0.004439}
{"case": "build-append-1024", "lane": "base", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "1:1046732800", "wall_ms": 3.24058, "rss_kib": 2168, "marks": [{"phase": 0, "ns": 191328879008328}, {"phase": 1, "ns": 191328880318611}, {"phase": 3, "ns": 191328880321817}], "diagnostic": "", "acquire_ms": 1.310283, "process_ms": 0.003206}
{"case": "build-append-1024", "lane": "base", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "1:1046732800", "wall_ms": 3.357992, "rss_kib": 2228, "marks": [{"phase": 0, "ns": 191328882223309}, {"phase": 1, "ns": 191328883755372}, {"phase": 3, "ns": 191328883760201}], "diagnostic": "", "acquire_ms": 1.532063, "process_ms": 0.004829}
{"case": "build-append-1024", "lane": "base", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "1:1046732800", "wall_ms": 3.609038, "rss_kib": 2148, "marks": [{"phase": 0, "ns": 191328885757225}, {"phase": 1, "ns": 191328887522249}, {"phase": 3, "ns": 191328887527178}], "diagnostic": "", "acquire_ms": 1.765024, "process_ms": 0.004929}
{"case": "build-append-1024", "lane": "base", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "1:1046732800", "wall_ms": 3.250509, "rss_kib": 2168, "marks": [{"phase": 0, "ns": 191328889400097}, {"phase": 1, "ns": 191328890874290}, {"phase": 3, "ns": 191328890877806}], "diagnostic": "", "acquire_ms": 1.474193, "process_ms": 0.003516}
{"case": "build-append-1024", "lane": "base", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "1:1046732800", "wall_ms": 3.15651, "rss_kib": 2168, "marks": [{"phase": 0, "ns": 191328892707503}, {"phase": 1, "ns": 191328894169463}, {"phase": 3, "ns": 191328894172679}], "diagnostic": "", "acquire_ms": 1.46196, "process_ms": 0.003216}
{"case": "build-append-1024", "lane": "base", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "1:1046732800", "wall_ms": 3.239809, "rss_kib": 2088, "marks": [{"phase": 0, "ns": 191328895988810}, {"phase": 1, "ns": 191328897477290}, {"phase": 3, "ns": 191328897483431}], "diagnostic": "", "acquire_ms": 1.48848, "process_ms": 0.006141}
{"case": "build-append-1024", "lane": "base", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "1:1046732800", "wall_ms": 17.980396, "rss_kib": 46524, "marks": [{"phase": 0, "ns": 9523594}, {"phase": 1, "ns": 10516545}, {"phase": 3, "ns": 10904089}], "diagnostic": "", "acquire_ms": 0.992951, "process_ms": 0.387544}
{"case": "build-append-1024", "lane": "base", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "1:1046732800", "wall_ms": 18.570885, "rss_kib": 46536, "marks": [{"phase": 0, "ns": 9740885}, {"phase": 1, "ns": 10665096}, {"phase": 3, "ns": 11091785}], "diagnostic": "", "acquire_ms": 0.924211, "process_ms": 0.426689}
{"case": "build-append-1024", "lane": "base", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "1:1046732800", "wall_ms": 18.672698, "rss_kib": 46584, "marks": [{"phase": 0, "ns": 9756865}, {"phase": 1, "ns": 10967168}, {"phase": 3, "ns": 11480300}], "diagnostic": "", "acquire_ms": 1.210303, "process_ms": 0.513132}
{"case": "build-append-1024", "lane": "base", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "1:1046732800", "wall_ms": 19.208954, "rss_kib": 46796, "marks": [{"phase": 0, "ns": 10371831}, {"phase": 1, "ns": 11470372}, {"phase": 3, "ns": 11915155}], "diagnostic": "", "acquire_ms": 1.098541, "process_ms": 0.444783}
{"case": "build-append-1024", "lane": "base", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "1:1046732800", "wall_ms": 18.21516, "rss_kib": 46476, "marks": [{"phase": 0, "ns": 9282817}, {"phase": 1, "ns": 10383693}, {"phase": 3, "ns": 10916953}], "diagnostic": "", "acquire_ms": 1.100876, "process_ms": 0.53326}
{"case": "build-append-1024", "lane": "base", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "1:1046732800", "wall_ms": 18.543754, "rss_kib": 46532, "marks": [{"phase": 0, "ns": 9939081}, {"phase": 1, "ns": 11130138}, {"phase": 3, "ns": 11509957}], "diagnostic": "", "acquire_ms": 1.191057, "process_ms": 0.379819}
{"case": "build-append-1024", "lane": "base", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "1:1046732800", "wall_ms": 18.481645, "rss_kib": 46840, "marks": [{"phase": 0, "ns": 9534725}, {"phase": 1, "ns": 10738485}, {"phase": 3, "ns": 11288798}], "diagnostic": "", "acquire_ms": 1.20376, "process_ms": 0.550313}
{"case": "build-append-1024", "lane": "base", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "1:1046732800", "wall_ms": 18.713796, "rss_kib": 46732, "marks": [{"phase": 0, "ns": 10572291}, {"phase": 1, "ns": 11616499}, {"phase": 3, "ns": 11991880}], "diagnostic": "", "acquire_ms": 1.044208, "process_ms": 0.375381}
{"case": "build-append-1024", "lane": "base", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "1:1046732800", "wall_ms": 4.500236, "rss_kib": 2164, "marks": [{"phase": 0, "ns": 191329049763124, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": null}, {"phase": 1, "ns": 191329052062461, "allocs": 523787, "frees": 522762, "live": 16392, "peak": 16408, "copy_cells": null}, {"phase": 3, "ns": 191329052070807, "allocs": 523793, "frees": 523791, "live": 32, "peak": 16424, "copy_cells": null}], "diagnostic": "", "acquire_ms": 2.299337, "process_ms": 0.008346}
{"case": "build-append-1024", "lane": "candidate", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "1:1046732800", "wall_ms": 2.162417, "rss_kib": 2424, "marks": [{"phase": 0, "ns": 191329847579357}, {"phase": 1, "ns": 191329847663817}, {"phase": 3, "ns": 191329847672654}], "diagnostic": "", "acquire_ms": 0.08446, "process_ms": 0.008837}
{"case": "build-append-1024", "lane": "candidate", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "1:1046732800", "wall_ms": 2.036718, "rss_kib": 2548, "marks": [{"phase": 0, "ns": 191329849753276}, {"phase": 1, "ns": 191329849842555}, {"phase": 3, "ns": 191329849851572}], "diagnostic": "", "acquire_ms": 0.089279, "process_ms": 0.009017}
{"case": "build-append-1024", "lane": "candidate", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "1:1046732800", "wall_ms": 1.990101, "rss_kib": 2552, "marks": [{"phase": 0, "ns": 191329851893301}, {"phase": 1, "ns": 191329851978031}, {"phase": 3, "ns": 191329851987048}], "diagnostic": "", "acquire_ms": 0.08473, "process_ms": 0.009017}
{"case": "build-append-1024", "lane": "candidate", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "1:1046732800", "wall_ms": 1.803707, "rss_kib": 2548, "marks": [{"phase": 0, "ns": 191329853889994}, {"phase": 1, "ns": 191329853964735}, {"phase": 3, "ns": 191329853973532}], "diagnostic": "", "acquire_ms": 0.074741, "process_ms": 0.008797}
{"case": "build-append-1024", "lane": "candidate", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "1:1046732800", "wall_ms": 1.875403, "rss_kib": 2484, "marks": [{"phase": 0, "ns": 191329855806435}, {"phase": 1, "ns": 191329855882899}, {"phase": 3, "ns": 191329855891927}], "diagnostic": "", "acquire_ms": 0.076464, "process_ms": 0.009028}
{"case": "build-append-1024", "lane": "candidate", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "1:1046732800", "wall_ms": 1.903075, "rss_kib": 2548, "marks": [{"phase": 0, "ns": 191329857832794}, {"phase": 1, "ns": 191329857927563}, {"phase": 3, "ns": 191329857940638}], "diagnostic": "", "acquire_ms": 0.094769, "process_ms": 0.013075}
{"case": "build-append-1024", "lane": "candidate", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "1:1046732800", "wall_ms": 1.880643, "rss_kib": 2488, "marks": [{"phase": 0, "ns": 191329859777218}, {"phase": 1, "ns": 191329859865605}, {"phase": 3, "ns": 191329859874893}], "diagnostic": "", "acquire_ms": 0.088387, "process_ms": 0.009288}
{"case": "build-append-1024", "lane": "candidate", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "1:1046732800", "wall_ms": 1.862909, "rss_kib": 2540, "marks": [{"phase": 0, "ns": 191329861794149}, {"phase": 1, "ns": 191329861878238}, {"phase": 3, "ns": 191329861887195}], "diagnostic": "", "acquire_ms": 0.084089, "process_ms": 0.008957}
{"case": "build-append-1024", "lane": "candidate", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "1:1046732800", "wall_ms": 20.246189, "rss_kib": 47568, "marks": [{"phase": 0, "ns": 10666539}, {"phase": 1, "ns": 11824012}, {"phase": 3, "ns": 12453705}], "diagnostic": "", "acquire_ms": 1.157473, "process_ms": 0.629693}
{"case": "build-append-1024", "lane": "candidate", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "1:1046732800", "wall_ms": 19.148058, "rss_kib": 46736, "marks": [{"phase": 0, "ns": 10623248}, {"phase": 1, "ns": 11636517}, {"phase": 3, "ns": 12019553}], "diagnostic": "", "acquire_ms": 1.013269, "process_ms": 0.383036}
{"case": "build-append-1024", "lane": "candidate", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "1:1046732800", "wall_ms": 18.575654, "rss_kib": 47180, "marks": [{"phase": 0, "ns": 9755764}, {"phase": 1, "ns": 10605484}, {"phase": 3, "ns": 11019117}], "diagnostic": "", "acquire_ms": 0.84972, "process_ms": 0.413633}
{"case": "build-append-1024", "lane": "candidate", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "1:1046732800", "wall_ms": 18.467729, "rss_kib": 47112, "marks": [{"phase": 0, "ns": 9801570}, {"phase": 1, "ns": 10908006}, {"phase": 3, "ns": 11350515}], "diagnostic": "", "acquire_ms": 1.106436, "process_ms": 0.442509}
{"case": "build-append-1024", "lane": "candidate", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "1:1046732800", "wall_ms": 19.854236, "rss_kib": 46916, "marks": [{"phase": 0, "ns": 10391868}, {"phase": 1, "ns": 11502603}, {"phase": 3, "ns": 12085968}], "diagnostic": "", "acquire_ms": 1.110735, "process_ms": 0.583365}
{"case": "build-append-1024", "lane": "candidate", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "1:1046732800", "wall_ms": 20.518976, "rss_kib": 47308, "marks": [{"phase": 0, "ns": 10607838}, {"phase": 1, "ns": 11774338}, {"phase": 3, "ns": 12205004}], "diagnostic": "", "acquire_ms": 1.1665, "process_ms": 0.430666}
{"case": "build-append-1024", "lane": "candidate", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "1:1046732800", "wall_ms": 19.547655, "rss_kib": 46952, "marks": [{"phase": 0, "ns": 10312980}, {"phase": 1, "ns": 11373629}, {"phase": 3, "ns": 11875901}], "diagnostic": "", "acquire_ms": 1.060649, "process_ms": 0.502272}
{"case": "build-append-1024", "lane": "candidate", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "1:1046732800", "wall_ms": 18.999818, "rss_kib": 47040, "marks": [{"phase": 0, "ns": 10139430}, {"phase": 1, "ns": 11068881}, {"phase": 3, "ns": 11503094}], "diagnostic": "", "acquire_ms": 0.929451, "process_ms": 0.434213}
{"case": "build-append-1024", "lane": "candidate", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "1:1046732800", "wall_ms": 2.64414, "rss_kib": 2548, "marks": [{"phase": 0, "ns": 191330021367050, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": 0}, {"phase": 1, "ns": 191330021561158, "allocs": 2077, "frees": 2071, "live": 4152, "peak": 6160, "copy_cells": 2046}, {"phase": 3, "ns": 191330021574633, "allocs": 4129, "frees": 4127, "live": 32, "peak": 4184, "copy_cells": 2046}], "diagnostic": "", "acquire_ms": 0.194108, "process_ms": 0.013475}
{"case": "build-append-4096", "lane": "base", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "1:2576318464", "wall_ms": 24.064002, "rss_kib": 2276, "marks": [{"phase": 0, "ns": 191330818294670}, {"phase": 1, "ns": 191330840010393}, {"phase": 3, "ns": 191330840023428}], "diagnostic": "", "acquire_ms": 21.715723, "process_ms": 0.013035}
{"case": "build-append-4096", "lane": "base", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "1:2576318464", "wall_ms": 26.046037, "rss_kib": 2152, "marks": [{"phase": 0, "ns": 191330842714486}, {"phase": 1, "ns": 191330866260196}, {"phase": 3, "ns": 191330866274764}], "diagnostic": "", "acquire_ms": 23.54571, "process_ms": 0.014568}
{"case": "build-append-4096", "lane": "base", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "1:2576318464", "wall_ms": 25.76233, "rss_kib": 2276, "marks": [{"phase": 0, "ns": 191330868635597}, {"phase": 1, "ns": 191330892245749}, {"phase": 3, "ns": 191330892259265}], "diagnostic": "", "acquire_ms": 23.610152, "process_ms": 0.013516}
{"case": "build-append-4096", "lane": "base", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "1:2576318464", "wall_ms": 26.785278, "rss_kib": 2360, "marks": [{"phase": 0, "ns": 191330894535417}, {"phase": 1, "ns": 191330919182184}, {"phase": 3, "ns": 191330919195038}], "diagnostic": "", "acquire_ms": 24.646767, "process_ms": 0.012854}
{"case": "build-append-4096", "lane": "base", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "1:2576318464", "wall_ms": 26.449612, "rss_kib": 2088, "marks": [{"phase": 0, "ns": 191330921586008}, {"phase": 1, "ns": 191330945802399}, {"phase": 3, "ns": 191330945815534}], "diagnostic": "", "acquire_ms": 24.216391, "process_ms": 0.013135}
{"case": "build-append-4096", "lane": "base", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "1:2576318464", "wall_ms": 23.848284, "rss_kib": 2420, "marks": [{"phase": 0, "ns": 191330948246219}, {"phase": 1, "ns": 191330969890647}, {"phase": 3, "ns": 191330969906878}], "diagnostic": "", "acquire_ms": 21.644428, "process_ms": 0.016231}
{"case": "build-append-4096", "lane": "base", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "1:2576318464", "wall_ms": 26.242961, "rss_kib": 2276, "marks": [{"phase": 0, "ns": 191330972219990}, {"phase": 1, "ns": 191330996308810}, {"phase": 3, "ns": 191330996322736}], "diagnostic": "", "acquire_ms": 24.08882, "process_ms": 0.013926}
{"case": "build-append-4096", "lane": "base", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "1:2576318464", "wall_ms": 25.225593, "rss_kib": 2216, "marks": [{"phase": 0, "ns": 191330998631571}, {"phase": 1, "ns": 191331021668277}, {"phase": 3, "ns": 191331021681121}], "diagnostic": "", "acquire_ms": 23.036706, "process_ms": 0.012844}
{"case": "build-append-4096", "lane": "base", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "1:2576318464", "wall_ms": 21.570969, "rss_kib": 48520, "marks": [{"phase": 0, "ns": 9789217}, {"phase": 1, "ns": 11231539}, {"phase": 3, "ns": 12308350}], "diagnostic": "", "acquire_ms": 1.442322, "process_ms": 1.076811}
{"case": "build-append-4096", "lane": "base", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "1:2576318464", "wall_ms": 19.927285, "rss_kib": 50440, "marks": [{"phase": 0, "ns": 9737008}, {"phase": 1, "ns": 11341879}, {"phase": 3, "ns": 12422626}], "diagnostic": "", "acquire_ms": 1.604871, "process_ms": 1.080747}
{"case": "build-append-4096", "lane": "base", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "1:2576318464", "wall_ms": 19.032379, "rss_kib": 50880, "marks": [{"phase": 0, "ns": 9256167}, {"phase": 1, "ns": 10631623}, {"phase": 3, "ns": 11787633}], "diagnostic": "", "acquire_ms": 1.375456, "process_ms": 1.15601}
{"case": "build-append-4096", "lane": "base", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "1:2576318464", "wall_ms": 18.829375, "rss_kib": 50624, "marks": [{"phase": 0, "ns": 8947412}, {"phase": 1, "ns": 10331815}, {"phase": 3, "ns": 11420678}], "diagnostic": "", "acquire_ms": 1.384403, "process_ms": 1.088863}
{"case": "build-append-4096", "lane": "base", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "1:2576318464", "wall_ms": 19.644529, "rss_kib": 50884, "marks": [{"phase": 0, "ns": 9565824}, {"phase": 1, "ns": 11056077}, {"phase": 3, "ns": 12353345}], "diagnostic": "", "acquire_ms": 1.490253, "process_ms": 1.297268}
{"case": "build-append-4096", "lane": "base", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "1:2576318464", "wall_ms": 22.022334, "rss_kib": 50940, "marks": [{"phase": 0, "ns": 9863548}, {"phase": 1, "ns": 11590359}, {"phase": 3, "ns": 12753533}], "diagnostic": "", "acquire_ms": 1.726811, "process_ms": 1.163174}
{"case": "build-append-4096", "lane": "base", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "1:2576318464", "wall_ms": 20.404809, "rss_kib": 50824, "marks": [{"phase": 0, "ns": 10410735}, {"phase": 1, "ns": 11910036}, {"phase": 3, "ns": 13153131}], "diagnostic": "", "acquire_ms": 1.499301, "process_ms": 1.243095}
{"case": "build-append-4096", "lane": "base", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "1:2576318464", "wall_ms": 22.548922, "rss_kib": 48456, "marks": [{"phase": 0, "ns": 9541017}, {"phase": 1, "ns": 10835920}, {"phase": 3, "ns": 12068997}], "diagnostic": "", "acquire_ms": 1.294903, "process_ms": 1.233077}
{"case": "build-append-4096", "lane": "base", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "1:2576318464", "wall_ms": 43.121318, "rss_kib": 2296, "marks": [{"phase": 0, "ns": 191331189742334, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": null}, {"phase": 1, "ns": 191331230554888, "allocs": 8386571, "frees": 8382474, "live": 65544, "peak": 65560, "copy_cells": null}, {"phase": 3, "ns": 191331230584725, "allocs": 8386577, "frees": 8386575, "live": 32, "peak": 65576, "copy_cells": null}], "diagnostic": "", "acquire_ms": 40.812554, "process_ms": 0.029837}
{"case": "build-append-4096", "lane": "candidate", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "1:2576318464", "wall_ms": 2.367115, "rss_kib": 2548, "marks": [{"phase": 0, "ns": 191332026592301}, {"phase": 1, "ns": 191332026752114}, {"phase": 3, "ns": 191332026787691}], "diagnostic": "", "acquire_ms": 0.159813, "process_ms": 0.035577}
{"case": "build-append-4096", "lane": "candidate", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "1:2576318464", "wall_ms": 2.168418, "rss_kib": 2404, "marks": [{"phase": 0, "ns": 191332028979604}, {"phase": 1, "ns": 191332029119660}, {"phase": 3, "ns": 191332029150438}], "diagnostic": "", "acquire_ms": 0.140056, "process_ms": 0.030778}
{"case": "build-append-4096", "lane": "candidate", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "1:2576318464", "wall_ms": 1.982025, "rss_kib": 2488, "marks": [{"phase": 0, "ns": 191332031120320}, {"phase": 1, "ns": 191332031242682}, {"phase": 3, "ns": 191332031273320}], "diagnostic": "", "acquire_ms": 0.122362, "process_ms": 0.030638}
{"case": "build-append-4096", "lane": "candidate", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "1:2576318464", "wall_ms": 2.150324, "rss_kib": 2296, "marks": [{"phase": 0, "ns": 191332033364632}, {"phase": 1, "ns": 191332033494669}, {"phase": 3, "ns": 191332033535536}], "diagnostic": "", "acquire_ms": 0.130037, "process_ms": 0.040867}
{"case": "build-append-4096", "lane": "candidate", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "1:2576318464", "wall_ms": 2.152879, "rss_kib": 2404, "marks": [{"phase": 0, "ns": 191332035678707}, {"phase": 1, "ns": 191332035805577}, {"phase": 3, "ns": 191332035836756}], "diagnostic": "", "acquire_ms": 0.12687, "process_ms": 0.031179}
{"case": "build-append-4096", "lane": "candidate", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "1:2576318464", "wall_ms": 1.986804, "rss_kib": 2296, "marks": [{"phase": 0, "ns": 191332037785779}, {"phase": 1, "ns": 191332037910775}, {"phase": 3, "ns": 191332037956783}], "diagnostic": "", "acquire_ms": 0.124996, "process_ms": 0.046008}
{"case": "build-append-4096", "lane": "candidate", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "1:2576318464", "wall_ms": 1.966777, "rss_kib": 2476, "marks": [{"phase": 0, "ns": 191332039902910}, {"phase": 1, "ns": 191332040033026}, {"phase": 3, "ns": 191332040063775}], "diagnostic": "", "acquire_ms": 0.130116, "process_ms": 0.030749}
{"case": "build-append-4096", "lane": "candidate", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "1:2576318464", "wall_ms": 2.034645, "rss_kib": 2548, "marks": [{"phase": 0, "ns": 191332042054606}, {"phase": 1, "ns": 191332042178952}, {"phase": 3, "ns": 191332042209219}], "diagnostic": "", "acquire_ms": 0.124346, "process_ms": 0.030267}
{"case": "build-append-4096", "lane": "candidate", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "1:2576318464", "wall_ms": 18.666045, "rss_kib": 51068, "marks": [{"phase": 0, "ns": 9522221}, {"phase": 1, "ns": 10812165}, {"phase": 3, "ns": 11837468}], "diagnostic": "", "acquire_ms": 1.289944, "process_ms": 1.025303}
{"case": "build-append-4096", "lane": "candidate", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "1:2576318464", "wall_ms": 19.299365, "rss_kib": 51524, "marks": [{"phase": 0, "ns": 9820316}, {"phase": 1, "ns": 11205170}, {"phase": 3, "ns": 12259848}], "diagnostic": "", "acquire_ms": 1.384854, "process_ms": 1.054678}
{"case": "build-append-4096", "lane": "candidate", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "1:2576318464", "wall_ms": 19.749889, "rss_kib": 51536, "marks": [{"phase": 0, "ns": 9464011}, {"phase": 1, "ns": 10771698}, {"phase": 3, "ns": 11947386}], "diagnostic": "", "acquire_ms": 1.307687, "process_ms": 1.175688}
{"case": "build-append-4096", "lane": "candidate", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "1:2576318464", "wall_ms": 19.678694, "rss_kib": 50936, "marks": [{"phase": 0, "ns": 9709636}, {"phase": 1, "ns": 11362167}, {"phase": 3, "ns": 12429419}], "diagnostic": "", "acquire_ms": 1.652531, "process_ms": 1.067252}
{"case": "build-append-4096", "lane": "candidate", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "1:2576318464", "wall_ms": 20.057211, "rss_kib": 50820, "marks": [{"phase": 0, "ns": 9926276}, {"phase": 1, "ns": 11324836}, {"phase": 3, "ns": 12409962}], "diagnostic": "", "acquire_ms": 1.39856, "process_ms": 1.085126}
{"case": "build-append-4096", "lane": "candidate", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "1:2576318464", "wall_ms": 22.169633, "rss_kib": 51200, "marks": [{"phase": 0, "ns": 10281730}, {"phase": 1, "ns": 11858206}, {"phase": 3, "ns": 12946709}], "diagnostic": "", "acquire_ms": 1.576476, "process_ms": 1.088503}
{"case": "build-append-4096", "lane": "candidate", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "1:2576318464", "wall_ms": 18.554624, "rss_kib": 51388, "marks": [{"phase": 0, "ns": 9430738}, {"phase": 1, "ns": 10743926}, {"phase": 3, "ns": 11763538}], "diagnostic": "", "acquire_ms": 1.313188, "process_ms": 1.019612}
{"case": "build-append-4096", "lane": "candidate", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "1:2576318464", "wall_ms": 20.545516, "rss_kib": 51256, "marks": [{"phase": 0, "ns": 9579149}, {"phase": 1, "ns": 10942783}, {"phase": 3, "ns": 12182942}], "diagnostic": "", "acquire_ms": 1.363634, "process_ms": 1.240159}
{"case": "build-append-4096", "lane": "candidate", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "1:2576318464", "wall_ms": 2.394036, "rss_kib": 2540, "marks": [{"phase": 0, "ns": 191332204880010, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": 0}, {"phase": 1, "ns": 191332205026207, "allocs": 8225, "frees": 8219, "live": 16440, "peak": 24592, "copy_cells": 8190}, {"phase": 3, "ns": 191332205088585, "allocs": 16421, "frees": 16419, "live": 32, "peak": 16472, "copy_cells": 8190}], "diagnostic": "", "acquire_ms": 0.146197, "process_ms": 0.062378}
{"case": "build-snapshots-128", "lane": "base", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "129:161603072", "wall_ms": 2.560261, "rss_kib": 2552, "marks": [{"phase": 0, "ns": 191333001483385}, {"phase": 1, "ns": 191333001642947}, {"phase": 3, "ns": 191333001671571}], "diagnostic": "", "acquire_ms": 0.159562, "process_ms": 0.028624}
{"case": "build-snapshots-128", "lane": "base", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "129:161603072", "wall_ms": 1.961857, "rss_kib": 2404, "marks": [{"phase": 0, "ns": 191333003666811}, {"phase": 1, "ns": 191333003813229}, {"phase": 3, "ns": 191333003841562}], "diagnostic": "", "acquire_ms": 0.146418, "process_ms": 0.028333}
{"case": "build-snapshots-128", "lane": "base", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "129:161603072", "wall_ms": 1.893407, "rss_kib": 2352, "marks": [{"phase": 0, "ns": 191333005657773}, {"phase": 1, "ns": 191333005808439}, {"phase": 3, "ns": 191333005834679}], "diagnostic": "", "acquire_ms": 0.150666, "process_ms": 0.02624}
{"case": "build-snapshots-128", "lane": "base", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "129:161603072", "wall_ms": 2.145355, "rss_kib": 2404, "marks": [{"phase": 0, "ns": 191333007850658}, {"phase": 1, "ns": 191333008077228}, {"phase": 3, "ns": 191333008106132}], "diagnostic": "", "acquire_ms": 0.22657, "process_ms": 0.028904}
{"case": "build-snapshots-128", "lane": "base", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "129:161603072", "wall_ms": 1.876345, "rss_kib": 2296, "marks": [{"phase": 0, "ns": 191333009945046}, {"phase": 1, "ns": 191333010092776}, {"phase": 3, "ns": 191333010119256}], "diagnostic": "", "acquire_ms": 0.14773, "process_ms": 0.02648}
{"case": "build-snapshots-128", "lane": "base", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "129:161603072", "wall_ms": 1.822713, "rss_kib": 2476, "marks": [{"phase": 0, "ns": 191333011824106}, {"phase": 1, "ns": 191333011980873}, {"phase": 3, "ns": 191333012017192}], "diagnostic": "", "acquire_ms": 0.156767, "process_ms": 0.036319}
{"case": "build-snapshots-128", "lane": "base", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "129:161603072", "wall_ms": 2.027551, "rss_kib": 2476, "marks": [{"phase": 0, "ns": 191333013926620}, {"phase": 1, "ns": 191333014093857}, {"phase": 3, "ns": 191333014120507}], "diagnostic": "", "acquire_ms": 0.167237, "process_ms": 0.02665}
{"case": "build-snapshots-128", "lane": "base", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "129:161603072", "wall_ms": 1.93719, "rss_kib": 2408, "marks": [{"phase": 0, "ns": 191333016016058}, {"phase": 1, "ns": 191333016162426}, {"phase": 3, "ns": 191333016188515}], "diagnostic": "", "acquire_ms": 0.146368, "process_ms": 0.026089}
{"case": "build-snapshots-128", "lane": "base", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "129:161603072", "wall_ms": 19.799222, "rss_kib": 51020, "marks": [{"phase": 0, "ns": 10551381}, {"phase": 1, "ns": 10998609}, {"phase": 3, "ns": 12955316}], "diagnostic": "", "acquire_ms": 0.447228, "process_ms": 1.956707}
{"case": "build-snapshots-128", "lane": "base", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "129:161603072", "wall_ms": 19.581019, "rss_kib": 51132, "marks": [{"phase": 0, "ns": 9326080}, {"phase": 1, "ns": 9793625}, {"phase": 3, "ns": 12078965}], "diagnostic": "", "acquire_ms": 0.467545, "process_ms": 2.28534}
{"case": "build-snapshots-128", "lane": "base", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "129:161603072", "wall_ms": 20.339386, "rss_kib": 50828, "marks": [{"phase": 0, "ns": 9919213}, {"phase": 1, "ns": 10446863}, {"phase": 3, "ns": 12666047}], "diagnostic": "", "acquire_ms": 0.52765, "process_ms": 2.219184}
{"case": "build-snapshots-128", "lane": "base", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "129:161603072", "wall_ms": 19.424252, "rss_kib": 50764, "marks": [{"phase": 0, "ns": 9038133}, {"phase": 1, "ns": 9570482}, {"phase": 3, "ns": 11997891}], "diagnostic": "", "acquire_ms": 0.532349, "process_ms": 2.427409}
{"case": "build-snapshots-128", "lane": "base", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "129:161603072", "wall_ms": 21.704903, "rss_kib": 50560, "marks": [{"phase": 0, "ns": 9405550}, {"phase": 1, "ns": 9852677}, {"phase": 3, "ns": 12137937}], "diagnostic": "", "acquire_ms": 0.447127, "process_ms": 2.28526}
{"case": "build-snapshots-128", "lane": "base", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "129:161603072", "wall_ms": 20.012055, "rss_kib": 50628, "marks": [{"phase": 0, "ns": 9797022}, {"phase": 1, "ns": 10222538}, {"phase": 3, "ns": 12379234}], "diagnostic": "", "acquire_ms": 0.425516, "process_ms": 2.156696}
{"case": "build-snapshots-128", "lane": "base", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "129:161603072", "wall_ms": 22.014759, "rss_kib": 50768, "marks": [{"phase": 0, "ns": 9690310}, {"phase": 1, "ns": 10174747}, {"phase": 3, "ns": 12235141}], "diagnostic": "", "acquire_ms": 0.484437, "process_ms": 2.060394}
{"case": "build-snapshots-128", "lane": "base", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "129:161603072", "wall_ms": 23.42403, "rss_kib": 50700, "marks": [{"phase": 0, "ns": 10546892}, {"phase": 1, "ns": 11055216}, {"phase": 3, "ns": 13287986}], "diagnostic": "", "acquire_ms": 0.508324, "process_ms": 2.23277}
{"case": "build-snapshots-128", "lane": "base", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "129:161603072", "wall_ms": 2.291401, "rss_kib": 2296, "marks": [{"phase": 0, "ns": 191333186427334, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": null}, {"phase": 1, "ns": 191333186594130, "allocs": 16522, "frees": 9, "live": 198168, "peak": 198184, "copy_cells": null}, {"phase": 3, "ns": 191333186622494, "allocs": 16528, "frees": 16526, "live": 32, "peak": 198200, "copy_cells": null}], "diagnostic": "", "acquire_ms": 0.166796, "process_ms": 0.028364}
{"case": "build-snapshots-128", "lane": "candidate", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "129:161603072", "wall_ms": 2.181082, "rss_kib": 2404, "marks": [{"phase": 0, "ns": 191334082327209}, {"phase": 1, "ns": 191334082401480}, {"phase": 3, "ns": 191334082456073}], "diagnostic": "", "acquire_ms": 0.074271, "process_ms": 0.054593}
{"case": "build-snapshots-128", "lane": "candidate", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "129:161603072", "wall_ms": 2.013415, "rss_kib": 2416, "marks": [{"phase": 0, "ns": 191334084478665}, {"phase": 1, "ns": 191334084552465}, {"phase": 3, "ns": 191334084608060}], "diagnostic": "", "acquire_ms": 0.0738, "process_ms": 0.055595}
{"case": "build-snapshots-128", "lane": "candidate", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "129:161603072", "wall_ms": 1.970404, "rss_kib": 2548, "marks": [{"phase": 0, "ns": 191334086629500}, {"phase": 1, "ns": 191334086705404}, {"phase": 3, "ns": 191334086759977}], "diagnostic": "", "acquire_ms": 0.075904, "process_ms": 0.054573}
{"case": "build-snapshots-128", "lane": "candidate", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "129:161603072", "wall_ms": 1.83674, "rss_kib": 2416, "marks": [{"phase": 0, "ns": 191334088598861}, {"phase": 1, "ns": 191334088672090}, {"phase": 3, "ns": 191334088727485}], "diagnostic": "", "acquire_ms": 0.073229, "process_ms": 0.055395}
{"case": "build-snapshots-128", "lane": "candidate", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "129:161603072", "wall_ms": 1.959092, "rss_kib": 2352, "marks": [{"phase": 0, "ns": 191334090649977}, {"phase": 1, "ns": 191334090733125}, {"phase": 3, "ns": 191334090788570}], "diagnostic": "", "acquire_ms": 0.083148, "process_ms": 0.055445}
{"case": "build-snapshots-128", "lane": "candidate", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "129:161603072", "wall_ms": 1.909568, "rss_kib": 2548, "marks": [{"phase": 0, "ns": 191334092696475}, {"phase": 1, "ns": 191334092770425}, {"phase": 3, "ns": 191334092825088}], "diagnostic": "", "acquire_ms": 0.07395, "process_ms": 0.054663}
{"case": "build-snapshots-128", "lane": "candidate", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "129:161603072", "wall_ms": 1.954874, "rss_kib": 2424, "marks": [{"phase": 0, "ns": 191334094723455}, {"phase": 1, "ns": 191334094826250}, {"phase": 3, "ns": 191334094881585}], "diagnostic": "", "acquire_ms": 0.102795, "process_ms": 0.055335}
{"case": "build-snapshots-128", "lane": "candidate", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "129:161603072", "wall_ms": 1.876806, "rss_kib": 2548, "marks": [{"phase": 0, "ns": 191334096736098}, {"phase": 1, "ns": 191334096813274}, {"phase": 3, "ns": 191334096868930}], "diagnostic": "", "acquire_ms": 0.077176, "process_ms": 0.055656}
{"case": "build-snapshots-128", "lane": "candidate", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "129:161603072", "wall_ms": 20.026223, "rss_kib": 51880, "marks": [{"phase": 0, "ns": 10242997}, {"phase": 1, "ns": 10682079}, {"phase": 3, "ns": 12804851}], "diagnostic": "", "acquire_ms": 0.439082, "process_ms": 2.122772}
{"case": "build-snapshots-128", "lane": "candidate", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "129:161603072", "wall_ms": 20.793746, "rss_kib": 51344, "marks": [{"phase": 0, "ns": 10888570}, {"phase": 1, "ns": 11331148}, {"phase": 3, "ns": 13513734}], "diagnostic": "", "acquire_ms": 0.442578, "process_ms": 2.182586}
{"case": "build-snapshots-128", "lane": "candidate", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "129:161603072", "wall_ms": 19.891597, "rss_kib": 51136, "marks": [{"phase": 0, "ns": 10044751}, {"phase": 1, "ns": 10542564}, {"phase": 3, "ns": 12974191}], "diagnostic": "", "acquire_ms": 0.497813, "process_ms": 2.431627}
{"case": "build-snapshots-128", "lane": "candidate", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "129:161603072", "wall_ms": 20.257571, "rss_kib": 51784, "marks": [{"phase": 0, "ns": 10585886}, {"phase": 1, "ns": 11041760}, {"phase": 3, "ns": 13211050}], "diagnostic": "", "acquire_ms": 0.455874, "process_ms": 2.16929}
{"case": "build-snapshots-128", "lane": "candidate", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "129:161603072", "wall_ms": 21.18141, "rss_kib": 51396, "marks": [{"phase": 0, "ns": 10108682}, {"phase": 1, "ns": 10565728}, {"phase": 3, "ns": 13199959}], "diagnostic": "", "acquire_ms": 0.457046, "process_ms": 2.634231}
{"case": "build-snapshots-128", "lane": "candidate", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "129:161603072", "wall_ms": 23.429671, "rss_kib": 51388, "marks": [{"phase": 0, "ns": 12282461}, {"phase": 1, "ns": 12967859}, {"phase": 3, "ns": 15634902}], "diagnostic": "", "acquire_ms": 0.685398, "process_ms": 2.667043}
{"case": "build-snapshots-128", "lane": "candidate", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "129:161603072", "wall_ms": 21.393042, "rss_kib": 51732, "marks": [{"phase": 0, "ns": 10466721}, {"phase": 1, "ns": 11560884}, {"phase": 3, "ns": 13796480}], "diagnostic": "", "acquire_ms": 1.094163, "process_ms": 2.235596}
{"case": "build-snapshots-128", "lane": "candidate", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "129:161603072", "wall_ms": 19.760559, "rss_kib": 52168, "marks": [{"phase": 0, "ns": 10443887}, {"phase": 1, "ns": 10895843}, {"phase": 3, "ns": 12991003}], "diagnostic": "", "acquire_ms": 0.451956, "process_ms": 2.09516}
{"case": "build-snapshots-128", "lane": "candidate", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "129:161603072", "wall_ms": 2.262257, "rss_kib": 2352, "marks": [{"phase": 0, "ns": 191334267472360, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": 0}, {"phase": 1, "ns": 191334267557822, "allocs": 648, "frees": 9, "live": 92512, "peak": 92528, "copy_cells": 8255}, {"phase": 3, "ns": 191334267630630, "allocs": 16910, "frees": 16908, "live": 32, "peak": 92544, "copy_cells": 8255}], "diagnostic": "", "acquire_ms": 0.085462, "process_ms": 0.072808}
{"case": "build-snapshots-512", "lane": "base", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "513:725317632", "wall_ms": 5.59489, "rss_kib": 5364, "marks": [{"phase": 0, "ns": 191335064020680}, {"phase": 1, "ns": 191335066295500}, {"phase": 3, "ns": 191335067004754}], "diagnostic": "", "acquire_ms": 2.27482, "process_ms": 0.709254}
{"case": "build-snapshots-512", "lane": "base", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "513:725317632", "wall_ms": 5.297337, "rss_kib": 5368, "marks": [{"phase": 0, "ns": 191335069521512}, {"phase": 1, "ns": 191335071852318}, {"phase": 3, "ns": 191335072490097}], "diagnostic": "", "acquire_ms": 2.330806, "process_ms": 0.637779}
{"case": "build-snapshots-512", "lane": "base", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "513:725317632", "wall_ms": 5.615519, "rss_kib": 5420, "marks": [{"phase": 0, "ns": 191335074966158}, {"phase": 1, "ns": 191335077721819}, {"phase": 3, "ns": 191335078370287}], "diagnostic": "", "acquire_ms": 2.755661, "process_ms": 0.648468}
{"case": "build-snapshots-512", "lane": "base", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "513:725317632", "wall_ms": 5.205673, "rss_kib": 5296, "marks": [{"phase": 0, "ns": 191335080696014}, {"phase": 1, "ns": 191335082931920}, {"phase": 3, "ns": 191335083526346}], "diagnostic": "", "acquire_ms": 2.235906, "process_ms": 0.594426}
{"case": "build-snapshots-512", "lane": "base", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "513:725317632", "wall_ms": 5.152032, "rss_kib": 5352, "marks": [{"phase": 0, "ns": 191335086073943}, {"phase": 1, "ns": 191335088446218}, {"phase": 3, "ns": 191335089047006}], "diagnostic": "", "acquire_ms": 2.372275, "process_ms": 0.600788}
{"case": "build-snapshots-512", "lane": "base", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "513:725317632", "wall_ms": 5.346359, "rss_kib": 5360, "marks": [{"phase": 0, "ns": 191335091692658}, {"phase": 1, "ns": 191335093939946}, {"phase": 3, "ns": 191335094560281}], "diagnostic": "", "acquire_ms": 2.247288, "process_ms": 0.620335}
{"case": "build-snapshots-512", "lane": "base", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "513:725317632", "wall_ms": 5.224709, "rss_kib": 5348, "marks": [{"phase": 0, "ns": 191335096871851}, {"phase": 1, "ns": 191335099307165}, {"phase": 3, "ns": 191335099928452}], "diagnostic": "", "acquire_ms": 2.435314, "process_ms": 0.621287}
{"case": "build-snapshots-512", "lane": "base", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "513:725317632", "wall_ms": 4.974304, "rss_kib": 5348, "marks": [{"phase": 0, "ns": 191335102338488}, {"phase": 1, "ns": 191335104542334}, {"phase": 3, "ns": 191335105088548}], "diagnostic": "", "acquire_ms": 2.203846, "process_ms": 0.546214}
{"case": "build-snapshots-512", "lane": "base", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "513:725317632", "wall_ms": 40.649285, "rss_kib": 76616, "marks": [{"phase": 0, "ns": 9696311}, {"phase": 1, "ns": 10417618}, {"phase": 3, "ns": 28218704}], "diagnostic": "", "acquire_ms": 0.721307, "process_ms": 17.801086}
{"case": "build-snapshots-512", "lane": "base", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "513:725317632", "wall_ms": 37.864258, "rss_kib": 76544, "marks": [{"phase": 0, "ns": 9176646}, {"phase": 1, "ns": 9858438}, {"phase": 3, "ns": 27438386}], "diagnostic": "", "acquire_ms": 0.681792, "process_ms": 17.579948}
{"case": "build-snapshots-512", "lane": "base", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "513:725317632", "wall_ms": 39.174521, "rss_kib": 76304, "marks": [{"phase": 0, "ns": 9812601}, {"phase": 1, "ns": 10432356}, {"phase": 3, "ns": 28234073}], "diagnostic": "", "acquire_ms": 0.619755, "process_ms": 17.801717}
{"case": "build-snapshots-512", "lane": "base", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "513:725317632", "wall_ms": 40.232425, "rss_kib": 76732, "marks": [{"phase": 0, "ns": 9923110}, {"phase": 1, "ns": 10673151}, {"phase": 3, "ns": 28888893}], "diagnostic": "", "acquire_ms": 0.750041, "process_ms": 18.215742}
{"case": "build-snapshots-512", "lane": "base", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "513:725317632", "wall_ms": 39.788024, "rss_kib": 76416, "marks": [{"phase": 0, "ns": 9471565}, {"phase": 1, "ns": 10103082}, {"phase": 3, "ns": 27464385}], "diagnostic": "", "acquire_ms": 0.631517, "process_ms": 17.361303}
{"case": "build-snapshots-512", "lane": "base", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "513:725317632", "wall_ms": 37.950552, "rss_kib": 76672, "marks": [{"phase": 0, "ns": 9287206}, {"phase": 1, "ns": 9892964}, {"phase": 3, "ns": 26474901}], "diagnostic": "", "acquire_ms": 0.605758, "process_ms": 16.581937}
{"case": "build-snapshots-512", "lane": "base", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "513:725317632", "wall_ms": 39.724864, "rss_kib": 76484, "marks": [{"phase": 0, "ns": 11241569}, {"phase": 1, "ns": 12036214}, {"phase": 3, "ns": 28626988}], "diagnostic": "", "acquire_ms": 0.794645, "process_ms": 16.590774}
{"case": "build-snapshots-512", "lane": "base", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "513:725317632", "wall_ms": 39.456616, "rss_kib": 76356, "marks": [{"phase": 0, "ns": 9638771}, {"phase": 1, "ns": 10311987}, {"phase": 3, "ns": 28282745}], "diagnostic": "", "acquire_ms": 0.673216, "process_ms": 17.970758}
{"case": "build-snapshots-512", "lane": "base", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "513:725317632", "wall_ms": 5.675943, "rss_kib": 5424, "marks": [{"phase": 0, "ns": 191335423954490, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": null}, {"phase": 1, "ns": 191335426704360, "allocs": 262666, "frees": 9, "live": 3151896, "peak": 3151912, "copy_cells": null}, {"phase": 3, "ns": 191335427345324, "allocs": 262672, "frees": 262670, "live": 32, "peak": 3151928, "copy_cells": null}], "diagnostic": "", "acquire_ms": 2.74987, "process_ms": 0.640964}
{"case": "build-snapshots-512", "lane": "candidate", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "513:725317632", "wall_ms": 3.697846, "rss_kib": 3684, "marks": [{"phase": 0, "ns": 191336323425441}, {"phase": 1, "ns": 191336323946778}, {"phase": 3, "ns": 191336324935632}], "diagnostic": "", "acquire_ms": 0.521337, "process_ms": 0.988854}
{"case": "build-snapshots-512", "lane": "candidate", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "513:725317632", "wall_ms": 3.291166, "rss_kib": 3764, "marks": [{"phase": 0, "ns": 191336327102578}, {"phase": 1, "ns": 191336327592365}, {"phase": 3, "ns": 191336328442326}], "diagnostic": "", "acquire_ms": 0.489787, "process_ms": 0.849961}
{"case": "build-snapshots-512", "lane": "candidate", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "513:725317632", "wall_ms": 3.329247, "rss_kib": 3756, "marks": [{"phase": 0, "ns": 191336330530001}, {"phase": 1, "ns": 191336330998679}, {"phase": 3, "ns": 191336331947357}], "diagnostic": "", "acquire_ms": 0.468678, "process_ms": 0.948678}
{"case": "build-snapshots-512", "lane": "candidate", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "513:725317632", "wall_ms": 3.299602, "rss_kib": 3820, "marks": [{"phase": 0, "ns": 191336333942807}, {"phase": 1, "ns": 191336334410473}, {"phase": 3, "ns": 191336335358690}], "diagnostic": "", "acquire_ms": 0.467666, "process_ms": 0.948217}
{"case": "build-snapshots-512", "lane": "candidate", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "513:725317632", "wall_ms": 3.370316, "rss_kib": 3576, "marks": [{"phase": 0, "ns": 191336337416789}, {"phase": 1, "ns": 191336337938107}, {"phase": 3, "ns": 191336338850105}], "diagnostic": "", "acquire_ms": 0.521318, "process_ms": 0.911998}
{"case": "build-snapshots-512", "lane": "candidate", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "513:725317632", "wall_ms": 3.545006, "rss_kib": 3684, "marks": [{"phase": 0, "ns": 191336340926779}, {"phase": 1, "ns": 191336341540432}, {"phase": 3, "ns": 191336342525548}], "diagnostic": "", "acquire_ms": 0.613653, "process_ms": 0.985116}
{"case": "build-snapshots-512", "lane": "candidate", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "513:725317632", "wall_ms": 3.348764, "rss_kib": 3704, "marks": [{"phase": 0, "ns": 191336344542800}, {"phase": 1, "ns": 191336345039181}, {"phase": 3, "ns": 191336346041780}], "diagnostic": "", "acquire_ms": 0.496381, "process_ms": 1.002599}
{"case": "build-snapshots-512", "lane": "candidate", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "513:725317632", "wall_ms": 3.690963, "rss_kib": 3760, "marks": [{"phase": 0, "ns": 191336348182226}, {"phase": 1, "ns": 191336348826817}, {"phase": 3, "ns": 191336349788479}], "diagnostic": "", "acquire_ms": 0.644591, "process_ms": 0.961662}
{"case": "build-snapshots-512", "lane": "candidate", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "513:725317632", "wall_ms": 40.073685, "rss_kib": 77324, "marks": [{"phase": 0, "ns": 10610002}, {"phase": 1, "ns": 11204659}, {"phase": 3, "ns": 29018970}], "diagnostic": "", "acquire_ms": 0.594657, "process_ms": 17.814311}
{"case": "build-snapshots-512", "lane": "candidate", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "513:725317632", "wall_ms": 42.152183, "rss_kib": 76864, "marks": [{"phase": 0, "ns": 10656500}, {"phase": 1, "ns": 11403736}, {"phase": 3, "ns": 30942274}], "diagnostic": "", "acquire_ms": 0.747236, "process_ms": 19.538538}
{"case": "build-snapshots-512", "lane": "candidate", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "513:725317632", "wall_ms": 40.227456, "rss_kib": 77256, "marks": [{"phase": 0, "ns": 11177667}, {"phase": 1, "ns": 11789687}, {"phase": 3, "ns": 28572103}], "diagnostic": "", "acquire_ms": 0.61202, "process_ms": 16.782416}
{"case": "build-snapshots-512", "lane": "candidate", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "513:725317632", "wall_ms": 41.931825, "rss_kib": 77148, "marks": [{"phase": 0, "ns": 10306617}, {"phase": 1, "ns": 10943012}, {"phase": 3, "ns": 29181397}], "diagnostic": "", "acquire_ms": 0.636395, "process_ms": 18.238385}
{"case": "build-snapshots-512", "lane": "candidate", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "513:725317632", "wall_ms": 42.153736, "rss_kib": 76872, "marks": [{"phase": 0, "ns": 11002656}, {"phase": 1, "ns": 11679979}, {"phase": 3, "ns": 29845355}], "diagnostic": "", "acquire_ms": 0.677323, "process_ms": 18.165376}
{"case": "build-snapshots-512", "lane": "candidate", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "513:725317632", "wall_ms": 38.245592, "rss_kib": 77000, "marks": [{"phase": 0, "ns": 10027869}, {"phase": 1, "ns": 10668182}, {"phase": 3, "ns": 27243145}], "diagnostic": "", "acquire_ms": 0.640313, "process_ms": 16.574963}
{"case": "build-snapshots-512", "lane": "candidate", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "513:725317632", "wall_ms": 39.111642, "rss_kib": 77000, "marks": [{"phase": 0, "ns": 9657758}, {"phase": 1, "ns": 10212729}, {"phase": 3, "ns": 27769723}], "diagnostic": "", "acquire_ms": 0.554971, "process_ms": 17.556994}
{"case": "build-snapshots-512", "lane": "candidate", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "513:725317632", "wall_ms": 39.876992, "rss_kib": 77120, "marks": [{"phase": 0, "ns": 10780635}, {"phase": 1, "ns": 11614515}, {"phase": 3, "ns": 28582984}], "diagnostic": "", "acquire_ms": 0.83388, "process_ms": 16.968469}
{"case": "build-snapshots-512", "lane": "candidate", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "513:725317632", "wall_ms": 3.883708, "rss_kib": 3684, "marks": [{"phase": 0, "ns": 191336677684499, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": 0}, {"phase": 1, "ns": 191336678193864, "allocs": 2568, "frees": 9, "live": 1418592, "peak": 1418608, "copy_cells": 131327}, {"phase": 3, "ns": 191336679240908, "allocs": 264206, "frees": 264204, "live": 32, "peak": 1418624, "copy_cells": 131327}], "diagnostic": "", "acquire_ms": 0.509365, "process_ms": 1.047044}
{"case": "map-prefix-256", "lane": "base", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 5.491595, "rss_kib": 2544, "marks": [{"phase": 0, "ns": 191338026591753}, {"phase": 1, "ns": 191338028036501}, {"phase": 3, "ns": 191338029793609}], "diagnostic": "", "acquire_ms": 1.444748, "process_ms": 1.757108}
{"case": "map-prefix-256", "lane": "base", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 5.395051, "rss_kib": 2584, "marks": [{"phase": 0, "ns": 191338031983669}, {"phase": 1, "ns": 191338033460246}, {"phase": 3, "ns": 191338035300934}], "diagnostic": "", "acquire_ms": 1.476577, "process_ms": 1.840688}
{"case": "map-prefix-256", "lane": "base", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 5.524817, "rss_kib": 2532, "marks": [{"phase": 0, "ns": 191338037529045}, {"phase": 1, "ns": 191338039067159}, {"phase": 3, "ns": 191338041025350}], "diagnostic": "", "acquire_ms": 1.538114, "process_ms": 1.958191}
{"case": "map-prefix-256", "lane": "base", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 5.563511, "rss_kib": 2532, "marks": [{"phase": 0, "ns": 191338043229656}, {"phase": 1, "ns": 191338045038733}, {"phase": 3, "ns": 191338046774492}], "diagnostic": "", "acquire_ms": 1.809077, "process_ms": 1.735759}
{"case": "map-prefix-256", "lane": "base", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 5.064155, "rss_kib": 2544, "marks": [{"phase": 0, "ns": 191338048891904}, {"phase": 1, "ns": 191338050288790}, {"phase": 3, "ns": 191338052053504}], "diagnostic": "", "acquire_ms": 1.396886, "process_ms": 1.764714}
{"case": "map-prefix-256", "lane": "base", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 5.197397, "rss_kib": 2552, "marks": [{"phase": 0, "ns": 191338054176256}, {"phase": 1, "ns": 191338055551812}, {"phase": 3, "ns": 191338057399823}], "diagnostic": "", "acquire_ms": 1.375556, "process_ms": 1.848011}
{"case": "map-prefix-256", "lane": "base", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 5.153794, "rss_kib": 2528, "marks": [{"phase": 0, "ns": 191338059459746}, {"phase": 1, "ns": 191338060861211}, {"phase": 3, "ns": 191338062652334}], "diagnostic": "", "acquire_ms": 1.401465, "process_ms": 1.791123}
{"case": "map-prefix-256", "lane": "base", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 5.292738, "rss_kib": 2676, "marks": [{"phase": 0, "ns": 191338064869054}, {"phase": 1, "ns": 191338066347235}, {"phase": 3, "ns": 191338068140683}], "diagnostic": "", "acquire_ms": 1.478181, "process_ms": 1.793448}
{"case": "map-prefix-256", "lane": "base", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 82.922157, "rss_kib": 100548, "marks": [{"phase": 0, "ns": 11245205}, {"phase": 1, "ns": 49333128}, {"phase": 3, "ns": 70416633}], "diagnostic": "", "acquire_ms": 38.087923, "process_ms": 21.083505}
{"case": "map-prefix-256", "lane": "base", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 86.290859, "rss_kib": 100344, "marks": [{"phase": 0, "ns": 10775486}, {"phase": 1, "ns": 52338542}, {"phase": 3, "ns": 71954247}], "diagnostic": "", "acquire_ms": 41.563056, "process_ms": 19.615705}
{"case": "map-prefix-256", "lane": "base", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 81.696855, "rss_kib": 100168, "marks": [{"phase": 0, "ns": 10472782}, {"phase": 1, "ns": 49553295}, {"phase": 3, "ns": 68746228}], "diagnostic": "", "acquire_ms": 39.080513, "process_ms": 19.192933}
{"case": "map-prefix-256", "lane": "base", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 87.197557, "rss_kib": 100604, "marks": [{"phase": 0, "ns": 11224005}, {"phase": 1, "ns": 50371285}, {"phase": 3, "ns": 73634320}], "diagnostic": "", "acquire_ms": 39.14728, "process_ms": 23.263035}
{"case": "map-prefix-256", "lane": "base", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 80.762796, "rss_kib": 100816, "marks": [{"phase": 0, "ns": 11027333}, {"phase": 1, "ns": 48473589}, {"phase": 3, "ns": 67563167}], "diagnostic": "", "acquire_ms": 37.446256, "process_ms": 19.089578}
{"case": "map-prefix-256", "lane": "base", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 83.787636, "rss_kib": 100420, "marks": [{"phase": 0, "ns": 12043387}, {"phase": 1, "ns": 50194028}, {"phase": 3, "ns": 70348994}], "diagnostic": "", "acquire_ms": 38.150641, "process_ms": 20.154966}
{"case": "map-prefix-256", "lane": "base", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 83.365597, "rss_kib": 100336, "marks": [{"phase": 0, "ns": 11320778}, {"phase": 1, "ns": 49197621}, {"phase": 3, "ns": 68473351}], "diagnostic": "", "acquire_ms": 37.876843, "process_ms": 19.27573}
{"case": "map-prefix-256", "lane": "base", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 80.333873, "rss_kib": 100936, "marks": [{"phase": 0, "ns": 10499192}, {"phase": 1, "ns": 47006811}, {"phase": 3, "ns": 67319235}], "diagnostic": "", "acquire_ms": 36.507619, "process_ms": 20.312424}
{"case": "map-prefix-256", "lane": "base", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 6.387733, "rss_kib": 2424, "marks": [{"phase": 0, "ns": 191338738604721, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": null}, {"phase": 1, "ns": 191338740533606, "allocs": 339976, "frees": 306203, "live": 406296, "peak": 418544, "copy_cells": null}, {"phase": 3, "ns": 191338742792976, "allocs": 694358, "frees": 694356, "live": 32, "peak": 418640, "copy_cells": null}], "diagnostic": "", "acquire_ms": 1.928885, "process_ms": 2.25937}
{"case": "map-prefix-256", "lane": "candidate", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 2.88215, "rss_kib": 2424, "marks": [{"phase": 0, "ns": 191340139758934}, {"phase": 1, "ns": 191340140337450}, {"phase": 3, "ns": 191340140401601}], "diagnostic": "", "acquire_ms": 0.578516, "process_ms": 0.064151}
{"case": "map-prefix-256", "lane": "candidate", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 2.511809, "rss_kib": 2548, "marks": [{"phase": 0, "ns": 191340142580780}, {"phase": 1, "ns": 191340143092069}, {"phase": 3, "ns": 191340143130932}], "diagnostic": "", "acquire_ms": 0.511289, "process_ms": 0.038863}
{"case": "map-prefix-256", "lane": "candidate", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 2.46485, "rss_kib": 2424, "marks": [{"phase": 0, "ns": 191340145129419}, {"phase": 1, "ns": 191340145523395}, {"phase": 3, "ns": 191340145560365}], "diagnostic": "", "acquire_ms": 0.393976, "process_ms": 0.03697}
{"case": "map-prefix-256", "lane": "candidate", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 2.569718, "rss_kib": 2424, "marks": [{"phase": 0, "ns": 191340148053218}, {"phase": 1, "ns": 191340148461682}, {"phase": 3, "ns": 191340148498822}], "diagnostic": "", "acquire_ms": 0.408464, "process_ms": 0.03714}
{"case": "map-prefix-256", "lane": "candidate", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 2.246656, "rss_kib": 2404, "marks": [{"phase": 0, "ns": 191340150415494}, {"phase": 1, "ns": 191340150819549}, {"phase": 3, "ns": 191340150857541}], "diagnostic": "", "acquire_ms": 0.404055, "process_ms": 0.037992}
{"case": "map-prefix-256", "lane": "candidate", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 2.412311, "rss_kib": 2548, "marks": [{"phase": 0, "ns": 191340152848634}, {"phase": 1, "ns": 191340153306631}, {"phase": 3, "ns": 191340153354392}], "diagnostic": "", "acquire_ms": 0.457997, "process_ms": 0.047761}
{"case": "map-prefix-256", "lane": "candidate", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 2.857273, "rss_kib": 2360, "marks": [{"phase": 0, "ns": 191340155853186}, {"phase": 1, "ns": 191340156286357}, {"phase": 3, "ns": 191340156331021}], "diagnostic": "", "acquire_ms": 0.433171, "process_ms": 0.044664}
{"case": "map-prefix-256", "lane": "candidate", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 2.964857, "rss_kib": 2408, "marks": [{"phase": 0, "ns": 191340158808185}, {"phase": 1, "ns": 191340159394616}, {"phase": 3, "ns": 191340159471712}], "diagnostic": "", "acquire_ms": 0.586431, "process_ms": 0.077096}
{"case": "map-prefix-256", "lane": "candidate", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 49.778312, "rss_kib": 83716, "marks": [{"phase": 0, "ns": 14077191}, {"phase": 1, "ns": 31615830}, {"phase": 3, "ns": 36958653}], "diagnostic": "", "acquire_ms": 17.538639, "process_ms": 5.342823}
{"case": "map-prefix-256", "lane": "candidate", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 49.586187, "rss_kib": 83276, "marks": [{"phase": 0, "ns": 12547332}, {"phase": 1, "ns": 28991578}, {"phase": 3, "ns": 36397189}], "diagnostic": "", "acquire_ms": 16.444246, "process_ms": 7.405611}
{"case": "map-prefix-256", "lane": "candidate", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 46.398247, "rss_kib": 82568, "marks": [{"phase": 0, "ns": 12365398}, {"phase": 1, "ns": 29058004}, {"phase": 3, "ns": 34118532}], "diagnostic": "", "acquire_ms": 16.692606, "process_ms": 5.060528}
{"case": "map-prefix-256", "lane": "candidate", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 44.113449, "rss_kib": 83460, "marks": [{"phase": 0, "ns": 10607718}, {"phase": 1, "ns": 26051518}, {"phase": 3, "ns": 31451048}], "diagnostic": "", "acquire_ms": 15.4438, "process_ms": 5.39953}
{"case": "map-prefix-256", "lane": "candidate", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 43.825262, "rss_kib": 83832, "marks": [{"phase": 0, "ns": 10607036}, {"phase": 1, "ns": 25820219}, {"phase": 3, "ns": 31607494}], "diagnostic": "", "acquire_ms": 15.213183, "process_ms": 5.787275}
{"case": "map-prefix-256", "lane": "candidate", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 43.034975, "rss_kib": 83148, "marks": [{"phase": 0, "ns": 11470152}, {"phase": 1, "ns": 26185762}, {"phase": 3, "ns": 31521281}], "diagnostic": "", "acquire_ms": 14.71561, "process_ms": 5.335519}
{"case": "map-prefix-256", "lane": "candidate", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 43.985546, "rss_kib": 83852, "marks": [{"phase": 0, "ns": 11462838}, {"phase": 1, "ns": 26715015}, {"phase": 3, "ns": 32605655}], "diagnostic": "", "acquire_ms": 15.252177, "process_ms": 5.89064}
{"case": "map-prefix-256", "lane": "candidate", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 46.651537, "rss_kib": 83448, "marks": [{"phase": 0, "ns": 12630360}, {"phase": 1, "ns": 28735282}, {"phase": 3, "ns": 35643060}], "diagnostic": "", "acquire_ms": 16.104922, "process_ms": 6.907778}
{"case": "map-prefix-256", "lane": "candidate", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 2.644971, "rss_kib": 2552, "marks": [{"phase": 0, "ns": 191340530881915, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": 0}, {"phase": 1, "ns": 191340531429953, "allocs": 67028, "frees": 66513, "live": 138256, "peak": 138272, "copy_cells": 16814}, {"phase": 3, "ns": 191340531482513, "allocs": 68821, "frees": 68819, "live": 32, "peak": 140328, "copy_cells": 33372}], "diagnostic": "", "acquire_ms": 0.548038, "process_ms": 0.05256}
{"case": "map-prefix-4096", "lane": "base", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 63.88087, "rss_kib": 8616, "marks": [{"phase": 0, "ns": 191341878907589}, {"phase": 1, "ns": 191341905050330}, {"phase": 3, "ns": 191341940101489}], "diagnostic": "", "acquire_ms": 26.142741, "process_ms": 35.051159}
{"case": "map-prefix-4096", "lane": "base", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 61.528493, "rss_kib": 8616, "marks": [{"phase": 0, "ns": 191341942833645}, {"phase": 1, "ns": 191341966773903}, {"phase": 3, "ns": 191342001857112}], "diagnostic": "", "acquire_ms": 23.940258, "process_ms": 35.083209}
{"case": "map-prefix-4096", "lane": "base", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 64.263275, "rss_kib": 8724, "marks": [{"phase": 0, "ns": 191342004595370}, {"phase": 1, "ns": 191342029452225}, {"phase": 3, "ns": 191342066345013}], "diagnostic": "", "acquire_ms": 24.856855, "process_ms": 36.892788}
{"case": "map-prefix-4096", "lane": "base", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 63.316691, "rss_kib": 8600, "marks": [{"phase": 0, "ns": 191342069123306}, {"phase": 1, "ns": 191342093427865}, {"phase": 3, "ns": 191342129808272}], "diagnostic": "", "acquire_ms": 24.304559, "process_ms": 36.380407}
{"case": "map-prefix-4096", "lane": "base", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 61.803444, "rss_kib": 8676, "marks": [{"phase": 0, "ns": 191342132837822}, {"phase": 1, "ns": 191342156844325}, {"phase": 3, "ns": 191342191833707}], "diagnostic": "", "acquire_ms": 24.006503, "process_ms": 34.989382}
{"case": "map-prefix-4096", "lane": "base", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 64.320733, "rss_kib": 8680, "marks": [{"phase": 0, "ns": 191342194796781}, {"phase": 1, "ns": 191342221800513}, {"phase": 3, "ns": 191342256320355}], "diagnostic": "", "acquire_ms": 27.003732, "process_ms": 34.519842}
{"case": "map-prefix-4096", "lane": "base", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 61.627431, "rss_kib": 8620, "marks": [{"phase": 0, "ns": 191342259229477}, {"phase": 1, "ns": 191342282859166}, {"phase": 3, "ns": 191342318119010}], "diagnostic": "", "acquire_ms": 23.629689, "process_ms": 35.259844}
{"case": "map-prefix-4096", "lane": "base", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 60.728037, "rss_kib": 8568, "marks": [{"phase": 0, "ns": 191342320949733}, {"phase": 1, "ns": 191342344211927}, {"phase": 3, "ns": 191342379153277}], "diagnostic": "", "acquire_ms": 23.262194, "process_ms": 34.94135}
{"case": "map-prefix-4096", "lane": "base", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 759.93917, "rss_kib": 138300, "marks": [{"phase": 0, "ns": 10224932}, {"phase": 1, "ns": 411820786}, {"phase": 3, "ns": 743205917}], "diagnostic": "", "acquire_ms": 401.595854, "process_ms": 331.385131}
{"case": "map-prefix-4096", "lane": "base", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 731.519566, "rss_kib": 135976, "marks": [{"phase": 0, "ns": 10944415}, {"phase": 1, "ns": 405088030}, {"phase": 3, "ns": 715853063}], "diagnostic": "", "acquire_ms": 394.143615, "process_ms": 310.765033}
{"case": "map-prefix-4096", "lane": "base", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 741.195799, "rss_kib": 138408, "marks": [{"phase": 0, "ns": 10725380}, {"phase": 1, "ns": 396995558}, {"phase": 3, "ns": 726104426}], "diagnostic": "", "acquire_ms": 386.270178, "process_ms": 329.108868}
{"case": "map-prefix-4096", "lane": "base", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 752.279067, "rss_kib": 139248, "marks": [{"phase": 0, "ns": 10416325}, {"phase": 1, "ns": 389061696}, {"phase": 3, "ns": 738740777}], "diagnostic": "", "acquire_ms": 378.645371, "process_ms": 349.679081}
{"case": "map-prefix-4096", "lane": "base", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 731.075805, "rss_kib": 138720, "marks": [{"phase": 0, "ns": 10560207}, {"phase": 1, "ns": 394983766}, {"phase": 3, "ns": 715462473}], "diagnostic": "", "acquire_ms": 384.423559, "process_ms": 320.478707}
{"case": "map-prefix-4096", "lane": "base", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 746.961492, "rss_kib": 136192, "marks": [{"phase": 0, "ns": 10398652}, {"phase": 1, "ns": 396949320}, {"phase": 3, "ns": 731714184}], "diagnostic": "", "acquire_ms": 386.550668, "process_ms": 334.764864}
{"case": "map-prefix-4096", "lane": "base", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 754.061244, "rss_kib": 137988, "marks": [{"phase": 0, "ns": 10412318}, {"phase": 1, "ns": 408153749}, {"phase": 3, "ns": 738506944}], "diagnostic": "", "acquire_ms": 397.741431, "process_ms": 330.353195}
{"case": "map-prefix-4096", "lane": "base", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 740.052803, "rss_kib": 139776, "marks": [{"phase": 0, "ns": 11009619}, {"phase": 1, "ns": 399655097}, {"phase": 3, "ns": 725543774}], "diagnostic": "", "acquire_ms": 388.645478, "process_ms": 325.888677}
{"case": "map-prefix-4096", "lane": "base", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 74.587285, "rss_kib": 8688, "marks": [{"phase": 0, "ns": 191348340691229, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": null}, {"phase": 1, "ns": 191348372792950, "allocs": 5393416, "frees": 4860443, "live": 6396696, "peak": 6593264, "copy_cells": null}, {"phase": 3, "ns": 191348412686443, "allocs": 11023958, "frees": 11023956, "live": 32, "peak": 6593360, "copy_cells": null}], "diagnostic": "", "acquire_ms": 32.101721, "process_ms": 39.893493}
{"case": "map-prefix-4096", "lane": "candidate", "kind": "c", "run": "warm", "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 8.058768, "rss_kib": 3628, "marks": [{"phase": 0, "ns": 191349810138452}, {"phase": 1, "ns": 191349815742890}, {"phase": 3, "ns": 191349815908343}], "diagnostic": "", "acquire_ms": 5.604438, "process_ms": 0.165453}
{"case": "map-prefix-4096", "lane": "candidate", "kind": "c", "run": 1, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 8.997317, "rss_kib": 3448, "marks": [{"phase": 0, "ns": 191349818274226}, {"phase": 1, "ns": 191349824911441}, {"phase": 3, "ns": 191349825073007}], "diagnostic": "", "acquire_ms": 6.637215, "process_ms": 0.161566}
{"case": "map-prefix-4096", "lane": "candidate", "kind": "c", "run": 2, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 8.289335, "rss_kib": 3428, "marks": [{"phase": 0, "ns": 191349827356223}, {"phase": 1, "ns": 191349833232977}, {"phase": 3, "ns": 191349833404252}], "diagnostic": "", "acquire_ms": 5.876754, "process_ms": 0.171275}
{"case": "map-prefix-4096", "lane": "candidate", "kind": "c", "run": 3, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 8.237737, "rss_kib": 3556, "marks": [{"phase": 0, "ns": 191349836048111}, {"phase": 1, "ns": 191349841724265}, {"phase": 3, "ns": 191349841929193}], "diagnostic": "", "acquire_ms": 5.676154, "process_ms": 0.204928}
{"case": "map-prefix-4096", "lane": "candidate", "kind": "c", "run": 4, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 8.224652, "rss_kib": 3428, "marks": [{"phase": 0, "ns": 191349844349338}, {"phase": 1, "ns": 191349850221283}, {"phase": 3, "ns": 191349850387919}], "diagnostic": "", "acquire_ms": 5.871945, "process_ms": 0.166636}
{"case": "map-prefix-4096", "lane": "candidate", "kind": "c", "run": 5, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 8.397551, "rss_kib": 3512, "marks": [{"phase": 0, "ns": 191349852777216}, {"phase": 1, "ns": 191349858836306}, {"phase": 3, "ns": 191349858994866}], "diagnostic": "", "acquire_ms": 6.05909, "process_ms": 0.15856}
{"case": "map-prefix-4096", "lane": "candidate", "kind": "c", "run": 6, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 8.170159, "rss_kib": 3496, "marks": [{"phase": 0, "ns": 191349861345329}, {"phase": 1, "ns": 191349867142753}, {"phase": 3, "ns": 191349867316372}], "diagnostic": "", "acquire_ms": 5.797424, "process_ms": 0.173619}
{"case": "map-prefix-4096", "lane": "candidate", "kind": "c", "run": 7, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 9.951705, "rss_kib": 3508, "marks": [{"phase": 0, "ns": 191349869908814}, {"phase": 1, "ns": 191349877246145}, {"phase": 3, "ns": 191349877414715}], "diagnostic": "", "acquire_ms": 7.337331, "process_ms": 0.16857}
{"case": "map-prefix-4096", "lane": "candidate", "kind": "js", "run": "warm", "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 198.012559, "rss_kib": 115276, "marks": [{"phase": 0, "ns": 10966929}, {"phase": 1, "ns": 131095197}, {"phase": 3, "ns": 183464407}], "diagnostic": "", "acquire_ms": 120.128268, "process_ms": 52.36921}
{"case": "map-prefix-4096", "lane": "candidate", "kind": "js", "run": 1, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 189.172421, "rss_kib": 115716, "marks": [{"phase": 0, "ns": 10711604}, {"phase": 1, "ns": 125406979}, {"phase": 3, "ns": 174595132}], "diagnostic": "", "acquire_ms": 114.695375, "process_ms": 49.188153}
{"case": "map-prefix-4096", "lane": "candidate", "kind": "js", "run": 2, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 191.062552, "rss_kib": 115236, "marks": [{"phase": 0, "ns": 10704761}, {"phase": 1, "ns": 128965531}, {"phase": 3, "ns": 178259084}], "diagnostic": "", "acquire_ms": 118.26077, "process_ms": 49.293553}
{"case": "map-prefix-4096", "lane": "candidate", "kind": "js", "run": 3, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 192.346033, "rss_kib": 114876, "marks": [{"phase": 0, "ns": 11326379}, {"phase": 1, "ns": 130108667}, {"phase": 3, "ns": 179314033}], "diagnostic": "", "acquire_ms": 118.782288, "process_ms": 49.205366}
{"case": "map-prefix-4096", "lane": "candidate", "kind": "js", "run": 4, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 187.314551, "rss_kib": 115524, "marks": [{"phase": 0, "ns": 10702176}, {"phase": 1, "ns": 127312028}, {"phase": 3, "ns": 171942847}], "diagnostic": "", "acquire_ms": 116.609852, "process_ms": 44.630819}
{"case": "map-prefix-4096", "lane": "candidate", "kind": "js", "run": 5, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 203.191422, "rss_kib": 116084, "marks": [{"phase": 0, "ns": 11278479}, {"phase": 1, "ns": 139716341}, {"phase": 3, "ns": 187416926}], "diagnostic": "", "acquire_ms": 128.437862, "process_ms": 47.700585}
{"case": "map-prefix-4096", "lane": "candidate", "kind": "js", "run": 6, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 198.064458, "rss_kib": 116476, "marks": [{"phase": 0, "ns": 12558274}, {"phase": 1, "ns": 135767900}, {"phase": 3, "ns": 183225214}], "diagnostic": "", "acquire_ms": 123.209626, "process_ms": 47.457314}
{"case": "map-prefix-4096", "lane": "candidate", "kind": "js", "run": 7, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 199.487985, "rss_kib": 115272, "marks": [{"phase": 0, "ns": 10953953}, {"phase": 1, "ns": 130648620}, {"phase": 3, "ns": 183951198}], "diagnostic": "", "acquire_ms": 119.694667, "process_ms": 53.302578}
{"case": "map-prefix-4096", "lane": "candidate", "kind": "c-counters", "run": 1, "status": 0, "correct": true, "stdout": "64:2080", "wall_ms": 10.162655, "rss_kib": 3512, "marks": [{"phase": 0, "ns": 191351440373907, "allocs": 5, "frees": 4, "live": 16, "peak": 32, "copy_cells": 0}, {"phase": 1, "ns": 191351447919914, "allocs": 1034708, "frees": 1034193, "live": 2119696, "peak": 2119712, "copy_cells": 266414}, {"phase": 3, "ns": 191351448122929, "allocs": 1036501, "frees": 1036499, "live": 32, "peak": 2152488, "copy_cells": 528732}], "diagnostic": "", "acquire_ms": 7.546007, "process_ms": 0.203015}
```

</details>

<details><summary>All raw GNU time -v resource measurements (CSV)</summary>

Command identities and flags are in the provenance, workload metadata, and corresponding JSON run above. Elapsed GNU time has its native centisecond resolution; wall_ms above uses the external monotonic clock.

```csv
case,lane,kind,run,User time (seconds),System time (seconds),Percent of CPU this job got,Elapsed (wall clock) time (h:mm:ss or m:ss),Average shared text size (kbytes),Average unshared data size (kbytes),Average stack size (kbytes),Average total size (kbytes),Maximum resident set size (kbytes),Average resident set size (kbytes),Major (requiring I/O) page faults,Minor (reclaiming a frame) page faults,Voluntary context switches,Involuntary context switches,Swaps,File system inputs,File system outputs,Socket messages sent,Socket messages received,Signals delivered,Page size (bytes),Exit status
legacy-1024,base,c,warm,0.00,0.00,100%,0:00.00,0,0,0,0,4468,0,0,748,3,0,0,0,0,0,0,0,4096,0
legacy-1024,base,c,1,0.00,0.00,66%,0:00.00,0,0,0,0,4272,0,0,741,3,0,0,0,0,0,0,0,4096,0
legacy-1024,base,c,2,0.00,0.00,66%,0:00.00,0,0,0,0,4344,0,0,745,3,0,0,0,0,0,0,0,4096,0
legacy-1024,base,c,3,0.00,0.00,66%,0:00.00,0,0,0,0,4272,0,0,743,3,0,0,0,0,0,0,0,4096,0
legacy-1024,base,c,4,0.00,0.00,100%,0:00.00,0,0,0,0,4328,0,0,744,3,0,0,0,0,0,0,0,4096,0
legacy-1024,base,c,5,0.00,0.00,75%,0:00.00,0,0,0,0,4216,0,0,743,3,0,0,0,0,0,0,0,4096,0
legacy-1024,base,c,6,0.00,0.00,100%,0:00.00,0,0,0,0,4324,0,0,746,3,2,0,0,0,0,0,0,4096,0
legacy-1024,base,c,7,0.00,0.00,66%,0:00.00,0,0,0,0,4400,0,0,744,3,1,0,0,0,0,0,0,4096,0
legacy-1024,base,js,warm,0.01,0.00,115%,0:00.02,0,0,0,0,52132,0,0,5043,107,7,0,0,0,0,0,0,4096,1
legacy-1024,base,js,1,0.01,0.01,113%,0:00.02,0,0,0,0,52192,0,0,5042,131,3,0,0,0,0,0,0,4096,1
legacy-1024,base,js,2,0.01,0.01,104%,0:00.02,0,0,0,0,52068,0,0,4988,119,25,0,0,0,0,0,0,4096,1
legacy-1024,base,js,3,0.01,0.00,114%,0:00.02,0,0,0,0,52312,0,0,5044,122,74,0,0,0,0,0,0,4096,1
legacy-1024,base,js,4,0.01,0.01,104%,0:00.02,0,0,0,0,52132,0,0,5039,122,13,0,0,0,0,0,0,4096,1
legacy-1024,base,js,5,0.01,0.01,115%,0:00.02,0,0,0,0,51880,0,0,5038,125,4,0,0,0,0,0,0,4096,1
legacy-1024,base,js,6,0.01,0.01,115%,0:00.01,0,0,0,0,52392,0,0,5046,115,4,0,0,0,0,0,0,4096,1
legacy-1024,base,js,7,0.01,0.01,115%,0:00.02,0,0,0,0,52004,0,0,5042,112,5,0,0,0,0,0,0,4096,1
legacy-1024,base,c-counters,1,0.00,0.00,75%,0:00.00,0,0,0,0,4324,0,0,746,3,1,0,0,0,0,0,0,4096,0
legacy-1024,candidate,c,warm,0.00,0.00,50%,0:00.00,0,0,0,0,2932,0,0,377,3,2,0,0,0,0,0,0,4096,0
legacy-1024,candidate,c,1,0.00,0.00,100%,0:00.00,0,0,0,0,2800,0,0,369,3,0,0,0,0,0,0,0,4096,0
legacy-1024,candidate,c,2,0.00,0.00,50%,0:00.00,0,0,0,0,2680,0,0,371,3,2,0,0,0,0,0,0,4096,0
legacy-1024,candidate,c,3,0.00,0.00,50%,0:00.00,0,0,0,0,2788,0,0,371,3,2,0,0,0,0,0,0,4096,0
legacy-1024,candidate,c,4,0.00,0.00,100%,0:00.00,0,0,0,0,2788,0,0,373,3,0,0,0,0,0,0,0,4096,0
legacy-1024,candidate,c,5,0.00,0.00,100%,0:00.00,0,0,0,0,2872,0,0,374,3,0,0,0,0,0,0,0,4096,0
legacy-1024,candidate,c,6,0.00,0.00,100%,0:00.00,0,0,0,0,2788,0,0,371,3,0,0,0,0,0,0,0,4096,0
legacy-1024,candidate,c,7,0.00,0.00,100%,0:00.00,0,0,0,0,2924,0,0,374,3,1,0,0,0,0,0,0,4096,0
legacy-1024,candidate,js,warm,0.02,0.00,152%,0:00.02,0,0,0,0,62948,0,0,6992,148,9,0,0,0,0,0,0,4096,0
legacy-1024,candidate,js,1,0.02,0.01,156%,0:00.02,0,0,0,0,62692,0,0,6957,158,0,0,0,0,0,0,0,4096,0
legacy-1024,candidate,js,2,0.02,0.01,154%,0:00.02,0,0,0,0,62816,0,0,7021,133,6,0,0,0,0,0,0,4096,0
legacy-1024,candidate,js,3,0.02,0.01,148%,0:00.02,0,0,0,0,62552,0,0,6941,136,9,0,0,0,0,0,0,4096,0
legacy-1024,candidate,js,4,0.02,0.01,137%,0:00.02,0,0,0,0,62812,0,0,7002,126,13,0,0,0,0,0,0,4096,0
legacy-1024,candidate,js,5,0.03,0.00,152%,0:00.02,0,0,0,0,62556,0,0,6938,136,10,0,0,0,0,0,0,4096,0
legacy-1024,candidate,js,6,0.02,0.01,158%,0:00.02,0,0,0,0,62696,0,0,6992,139,5,0,0,0,0,0,0,4096,0
legacy-1024,candidate,js,7,0.02,0.01,148%,0:00.02,0,0,0,0,62708,0,0,6952,118,7,0,0,0,0,0,0,4096,0
legacy-1024,candidate,c-counters,1,0.00,0.00,50%,0:00.00,0,0,0,0,2868,0,0,375,3,0,0,0,0,0,0,0,4096,0
legacy-4096,base,c,warm,0.00,0.00,100%,0:00.01,0,0,0,0,10612,0,0,2332,3,1,0,0,0,0,0,0,4096,0
legacy-4096,base,c,1,0.00,0.00,90%,0:00.01,0,0,0,0,10732,0,0,2332,3,1,0,0,0,0,0,0,4096,0
legacy-4096,base,c,2,0.00,0.00,90%,0:00.01,0,0,0,0,10740,0,0,2334,3,7,0,0,0,0,0,0,4096,0
legacy-4096,base,c,3,0.00,0.00,90%,0:00.01,0,0,0,0,10600,0,0,2328,3,2,0,0,0,0,0,0,4096,0
legacy-4096,base,c,4,0.00,0.00,100%,0:00.01,0,0,0,0,10540,0,0,2330,3,2,0,0,0,0,0,0,4096,0
legacy-4096,base,c,5,0.00,0.00,90%,0:00.01,0,0,0,0,10608,0,0,2328,3,3,0,0,0,0,0,0,4096,0
legacy-4096,base,c,6,0.00,0.00,91%,0:00.01,0,0,0,0,10608,0,0,2326,3,0,0,0,0,0,0,0,4096,0
legacy-4096,base,c,7,0.00,0.00,90%,0:00.01,0,0,0,0,10488,0,0,2328,3,0,0,0,0,0,0,0,4096,0
legacy-4096,base,js,warm,0.01,0.01,114%,0:00.02,0,0,0,0,52876,0,0,5180,128,8,0,0,0,0,0,0,4096,1
legacy-4096,base,js,1,0.01,0.01,119%,0:00.02,0,0,0,0,52824,0,0,5170,118,4,0,0,0,0,0,0,4096,1
legacy-4096,base,js,2,0.01,0.00,110%,0:00.02,0,0,0,0,52900,0,0,5165,37,5,0,0,0,0,0,0,4096,1
legacy-4096,base,js,3,0.01,0.01,113%,0:00.02,0,0,0,0,52764,0,0,5178,136,6,0,0,0,0,0,0,4096,1
legacy-4096,base,js,4,0.01,0.00,113%,0:00.02,0,0,0,0,52444,0,0,5074,120,4,0,0,0,0,0,0,4096,1
legacy-4096,base,js,5,0.01,0.00,114%,0:00.02,0,0,0,0,52900,0,0,5178,118,5,0,0,0,0,0,0,4096,1
legacy-4096,base,js,6,0.01,0.01,113%,0:00.02,0,0,0,0,52964,0,0,5153,113,1,0,0,0,0,0,0,4096,1
legacy-4096,base,js,7,0.01,0.01,113%,0:00.02,0,0,0,0,52388,0,0,5177,129,4,0,0,0,0,0,0,4096,1
legacy-4096,base,c-counters,1,0.01,0.00,100%,0:00.01,0,0,0,0,10616,0,0,2327,3,0,0,0,0,0,0,0,4096,0
legacy-4096,candidate,c,warm,0.00,0.00,75%,0:00.00,0,0,0,0,4600,0,0,832,3,1,0,0,0,0,0,0,4096,0
legacy-4096,candidate,c,1,0.00,0.00,100%,0:00.00,0,0,0,0,4656,0,0,832,3,1,0,0,0,0,0,0,4096,0
legacy-4096,candidate,c,2,0.00,0.00,75%,0:00.00,0,0,0,0,4712,0,0,833,3,0,0,0,0,0,0,0,4096,0
legacy-4096,candidate,c,3,0.00,0.00,75%,0:00.00,0,0,0,0,4844,0,0,834,3,0,0,0,0,0,0,0,4096,0
legacy-4096,candidate,c,4,0.00,0.00,75%,0:00.00,0,0,0,0,4852,0,0,836,3,0,0,0,0,0,0,0,4096,0
legacy-4096,candidate,c,5,0.00,0.00,75%,0:00.00,0,0,0,0,4716,0,0,834,3,2,0,0,0,0,0,0,4096,0
legacy-4096,candidate,c,6,0.00,0.00,75%,0:00.00,0,0,0,0,4656,0,0,836,3,2,0,0,0,0,0,0,4096,0
legacy-4096,candidate,c,7,0.00,0.00,75%,0:00.00,0,0,0,0,4600,0,0,832,2,1,0,0,0,0,0,0,4096,0
legacy-4096,candidate,js,warm,0.04,0.02,132%,0:00.05,0,0,0,0,89824,0,0,13672,340,23,0,0,0,0,0,0,4096,0
legacy-4096,candidate,js,1,0.04,0.02,136%,0:00.04,0,0,0,0,89884,0,0,13723,272,9,0,0,0,0,0,0,4096,0
legacy-4096,candidate,js,2,0.04,0.02,139%,0:00.04,0,0,0,0,90200,0,0,13853,327,6,0,0,0,0,0,0,4096,0
legacy-4096,candidate,js,3,0.04,0.02,141%,0:00.04,0,0,0,0,90464,0,0,13861,262,4,0,0,0,0,0,0,4096,0
legacy-4096,candidate,js,4,0.04,0.02,136%,0:00.04,0,0,0,0,89892,0,0,13738,256,13,0,0,0,0,0,0,4096,0
legacy-4096,candidate,js,5,0.03,0.02,140%,0:00.04,0,0,0,0,90200,0,0,13740,260,2,0,0,0,0,0,0,4096,0
legacy-4096,candidate,js,6,0.03,0.02,140%,0:00.04,0,0,0,0,90340,0,0,13907,277,13,0,0,0,0,0,0,4096,0
legacy-4096,candidate,js,7,0.04,0.02,142%,0:00.04,0,0,0,0,90280,0,0,13864,265,7,0,0,0,0,0,0,4096,0
legacy-4096,candidate,c-counters,1,0.00,0.00,75%,0:00.00,0,0,0,0,4472,0,0,830,2,3,0,0,0,0,0,0,4096,0
ascii-1MiB-io-scan,base,c,warm,0.02,0.00,100%,0:00.02,0,0,0,0,19572,0,0,4620,7,4,0,0,0,0,0,0,4096,0
ascii-1MiB-io-scan,base,c,1,0.02,0.00,96%,0:00.02,0,0,0,0,19428,0,0,4619,7,6,0,0,0,0,0,0,4096,0
ascii-1MiB-io-scan,base,c,2,0.01,0.00,96%,0:00.02,0,0,0,0,19440,0,0,4618,7,4,0,0,0,0,0,0,4096,0
ascii-1MiB-io-scan,base,c,3,0.02,0.00,96%,0:00.02,0,0,0,0,19632,0,0,4622,7,7,0,0,0,0,0,0,4096,0
ascii-1MiB-io-scan,base,c,4,0.01,0.00,96%,0:00.02,0,0,0,0,19704,0,0,4620,7,2,0,0,0,0,0,0,4096,0
ascii-1MiB-io-scan,base,c,5,0.01,0.00,96%,0:00.02,0,0,0,0,19640,0,0,4619,7,6,0,0,0,0,0,0,4096,0
ascii-1MiB-io-scan,base,c,6,0.02,0.00,96%,0:00.02,0,0,0,0,19640,0,0,4619,7,0,0,0,0,0,0,0,4096,0
ascii-1MiB-io-scan,base,c,7,0.01,0.00,92%,0:00.02,0,0,0,0,19512,0,0,4617,7,18,0,0,0,0,0,0,4096,0
ascii-1MiB-io-scan,base,js,warm,0.98,0.12,119%,0:00.92,0,0,0,0,186828,0,0,44154,11466,181,0,0,0,0,0,0,4096,0
ascii-1MiB-io-scan,base,js,1,0.98,0.13,119%,0:00.93,0,0,0,0,188812,0,0,43114,11836,237,0,0,0,0,0,0,4096,0
ascii-1MiB-io-scan,base,js,2,0.98,0.11,119%,0:00.91,0,0,0,0,188824,0,0,43040,11224,215,0,0,0,0,0,0,4096,0
ascii-1MiB-io-scan,base,js,3,0.96,0.11,118%,0:00.91,0,0,0,0,186444,0,0,43725,10983,268,0,0,0,0,0,0,4096,0
ascii-1MiB-io-scan,base,js,4,0.95,0.14,118%,0:00.92,0,0,0,0,187216,0,0,42697,11874,229,0,0,0,0,0,0,4096,0
ascii-1MiB-io-scan,base,js,5,0.96,0.13,118%,0:00.93,0,0,0,0,186144,0,0,42741,11685,150,0,0,0,0,0,0,4096,0
ascii-1MiB-io-scan,base,js,6,0.98,0.11,119%,0:00.92,0,0,0,0,187840,0,0,43387,11612,211,0,0,0,0,0,0,4096,0
ascii-1MiB-io-scan,base,js,7,0.96,0.12,119%,0:00.91,0,0,0,0,185964,0,0,43162,11298,173,0,0,0,0,0,0,4096,0
ascii-1MiB-io-scan,base,c-counters,1,0.03,0.00,97%,0:00.04,0,0,0,0,19692,0,0,4619,7,12,0,0,0,0,0,0,4096,0
ascii-1MiB-io-scan,candidate,c,warm,0.01,0.00,94%,0:00.01,0,0,0,0,7336,0,0,1506,7,2,0,0,0,0,0,0,4096,0
ascii-1MiB-io-scan,candidate,c,1,0.01,0.00,94%,0:00.01,0,0,0,0,7288,0,0,1508,7,3,0,0,0,0,0,0,4096,0
ascii-1MiB-io-scan,candidate,c,2,0.01,0.00,94%,0:00.01,0,0,0,0,7288,0,0,1509,7,1,0,0,0,0,0,0,4096,0
ascii-1MiB-io-scan,candidate,c,3,0.01,0.00,95%,0:00.02,0,0,0,0,7216,0,0,1510,7,4,0,0,0,0,0,0,4096,0
ascii-1MiB-io-scan,candidate,c,4,0.01,0.00,94%,0:00.01,0,0,0,0,7288,0,0,1507,7,1,0,0,0,0,0,0,4096,0
ascii-1MiB-io-scan,candidate,c,5,0.01,0.00,94%,0:00.01,0,0,0,0,7416,0,0,1509,7,5,0,0,0,0,0,0,4096,0
ascii-1MiB-io-scan,candidate,c,6,0.01,0.00,100%,0:00.01,0,0,0,0,7280,0,0,1503,7,3,0,0,0,0,0,0,4096,0
ascii-1MiB-io-scan,candidate,c,7,0.01,0.00,94%,0:00.01,0,0,0,0,7344,0,0,1506,7,3,0,0,0,0,0,0,4096,0
ascii-1MiB-io-scan,candidate,js,warm,0.21,0.04,131%,0:00.19,0,0,0,0,138060,0,0,25380,1035,76,0,0,0,0,0,0,4096,0
ascii-1MiB-io-scan,candidate,js,1,0.21,0.04,129%,0:00.20,0,0,0,0,137432,0,0,25171,1050,60,0,0,0,0,0,0,4096,0
ascii-1MiB-io-scan,candidate,js,2,0.20,0.05,132%,0:00.19,0,0,0,0,138192,0,0,25410,992,38,0,0,0,0,0,0,4096,0
ascii-1MiB-io-scan,candidate,js,3,0.21,0.05,129%,0:00.20,0,0,0,0,138000,0,0,25445,1084,96,0,0,0,0,0,0,4096,0
ascii-1MiB-io-scan,candidate,js,4,0.21,0.05,129%,0:00.20,0,0,0,0,137224,0,0,25207,1103,47,0,0,0,0,0,0,4096,0
ascii-1MiB-io-scan,candidate,js,5,0.20,0.05,128%,0:00.20,0,0,0,0,137924,0,0,25353,1004,51,0,0,0,0,0,0,4096,0
ascii-1MiB-io-scan,candidate,js,6,0.20,0.05,131%,0:00.19,0,0,0,0,137928,0,0,25279,1033,39,0,0,0,0,0,0,4096,0
ascii-1MiB-io-scan,candidate,js,7,0.21,0.05,129%,0:00.20,0,0,0,0,136568,0,0,25127,1066,34,0,0,0,0,0,0,4096,0
ascii-1MiB-io-scan,candidate,c-counters,1,0.01,0.00,90%,0:00.02,0,0,0,0,7084,0,0,1508,7,7,0,0,0,0,0,0,4096,0
ascii-1MiB-construct-scan,base,c,warm,0.04,0.01,98%,0:00.06,0,0,0,0,43240,0,0,10482,3,14,0,0,0,0,0,0,4096,0
ascii-1MiB-construct-scan,base,c,1,0.05,0.00,98%,0:00.06,0,0,0,0,43256,0,0,10483,3,3,0,0,0,0,0,0,4096,0
ascii-1MiB-construct-scan,base,c,2,0.05,0.01,98%,0:00.06,0,0,0,0,43176,0,0,10481,3,4,0,0,0,0,0,0,4096,0
ascii-1MiB-construct-scan,base,c,3,0.04,0.01,98%,0:00.06,0,0,0,0,43128,0,0,10483,3,2,0,0,0,0,0,0,4096,0
ascii-1MiB-construct-scan,base,c,4,0.04,0.01,96%,0:00.06,0,0,0,0,43372,0,0,10481,3,14,0,0,0,0,0,0,4096,0
ascii-1MiB-construct-scan,base,c,5,0.04,0.01,98%,0:00.06,0,0,0,0,43308,0,0,10478,3,0,0,0,0,0,0,0,4096,0
ascii-1MiB-construct-scan,base,c,6,0.05,0.01,98%,0:00.06,0,0,0,0,43128,0,0,10480,3,7,0,0,0,0,0,0,4096,0
ascii-1MiB-construct-scan,base,c,7,0.04,0.01,96%,0:00.06,0,0,0,0,43380,0,0,10485,3,14,0,0,0,0,0,0,4096,0
ascii-1MiB-construct-scan,base,js,warm,0.01,0.01,110%,0:00.02,0,0,0,0,51228,0,0,4905,111,7,0,0,0,0,0,0,4096,1
ascii-1MiB-construct-scan,base,js,1,0.01,0.00,115%,0:00.02,0,0,0,0,51040,0,0,4896,129,11,0,0,0,0,0,0,4096,1
ascii-1MiB-construct-scan,base,js,2,0.01,0.00,110%,0:00.02,0,0,0,0,51168,0,0,4902,119,6,0,0,0,0,0,0,4096,1
ascii-1MiB-construct-scan,base,js,3,0.01,0.01,115%,0:00.02,0,0,0,0,51740,0,0,4899,121,23,0,0,0,0,0,0,4096,1
ascii-1MiB-construct-scan,base,js,4,0.01,0.00,115%,0:00.01,0,0,0,0,51220,0,0,4900,112,4,0,0,0,0,0,0,4096,1
ascii-1MiB-construct-scan,base,js,5,0.01,0.01,113%,0:00.02,0,0,0,0,51364,0,0,4900,110,7,0,0,0,0,0,0,4096,1
ascii-1MiB-construct-scan,base,js,6,0.01,0.01,104%,0:00.02,0,0,0,0,51360,0,0,4906,121,5,0,0,0,0,0,0,4096,1
ascii-1MiB-construct-scan,base,js,7,0.01,0.00,109%,0:00.02,0,0,0,0,51220,0,0,4892,121,19,0,0,0,0,0,0,4096,1
ascii-1MiB-construct-scan,base,c-counters,1,0.06,0.01,98%,0:00.08,0,0,0,0,42980,0,0,10481,3,19,0,0,0,0,0,0,4096,0
ascii-1MiB-construct-scan,candidate,c,warm,0.01,0.00,94%,0:00.01,0,0,0,0,6244,0,0,1250,3,4,0,0,0,0,0,0,4096,0
ascii-1MiB-construct-scan,candidate,c,1,0.01,0.00,93%,0:00.01,0,0,0,0,6192,0,0,1247,3,2,0,0,0,0,0,0,4096,0
ascii-1MiB-construct-scan,candidate,c,2,0.01,0.00,94%,0:00.01,0,0,0,0,6172,0,0,1250,3,10,0,0,0,0,0,0,4096,0
ascii-1MiB-construct-scan,candidate,c,3,0.01,0.00,93%,0:00.01,0,0,0,0,6380,0,0,1250,3,3,0,0,0,0,0,0,4096,0
ascii-1MiB-construct-scan,candidate,c,4,0.01,0.00,93%,0:00.01,0,0,0,0,6248,0,0,1247,3,6,0,0,0,0,0,0,4096,0
ascii-1MiB-construct-scan,candidate,c,5,0.01,0.00,93%,0:00.01,0,0,0,0,6372,0,0,1249,3,10,0,0,0,0,0,0,4096,0
ascii-1MiB-construct-scan,candidate,c,6,0.01,0.00,93%,0:00.01,0,0,0,0,6372,0,0,1250,3,7,0,0,0,0,0,0,4096,0
ascii-1MiB-construct-scan,candidate,c,7,0.01,0.00,94%,0:00.01,0,0,0,0,6244,0,0,1249,3,13,0,0,0,0,0,0,4096,0
ascii-1MiB-construct-scan,candidate,js,warm,0.15,0.04,134%,0:00.14,0,0,0,0,99296,0,0,16118,982,18,0,0,0,0,0,0,4096,0
ascii-1MiB-construct-scan,candidate,js,1,0.18,0.04,155%,0:00.14,0,0,0,0,104972,0,0,17905,993,41,0,0,0,0,0,0,4096,0
ascii-1MiB-construct-scan,candidate,js,2,0.18,0.02,131%,0:00.15,0,0,0,0,99544,0,0,16200,941,33,0,0,0,0,0,0,4096,0
ascii-1MiB-construct-scan,candidate,js,3,0.16,0.04,133%,0:00.15,0,0,0,0,99040,0,0,16098,917,18,0,0,0,0,0,0,4096,0
ascii-1MiB-construct-scan,candidate,js,4,0.17,0.03,135%,0:00.15,0,0,0,0,100952,0,0,16483,928,56,0,0,0,0,0,0,4096,0
ascii-1MiB-construct-scan,candidate,js,5,0.17,0.02,131%,0:00.15,0,0,0,0,99940,0,0,16269,889,57,0,0,0,0,0,0,4096,0
ascii-1MiB-construct-scan,candidate,js,6,0.16,0.03,136%,0:00.14,0,0,0,0,101212,0,0,16622,920,19,0,0,0,0,0,0,4096,0
ascii-1MiB-construct-scan,candidate,js,7,0.15,0.04,132%,0:00.15,0,0,0,0,99612,0,0,16206,929,82,0,0,0,0,0,0,4096,0
ascii-1MiB-construct-scan,candidate,c-counters,1,0.01,0.00,94%,0:00.01,0,0,0,0,6516,0,0,1249,3,1,0,0,0,0,0,0,4096,0
ascii-1MiB-io-materialize,base,c,warm,0.01,0.01,96%,0:00.03,0,0,0,0,43236,0,0,10716,7,9,0,0,0,0,0,0,4096,0
ascii-1MiB-io-materialize,base,c,1,0.01,0.01,97%,0:00.03,0,0,0,0,43044,0,0,10720,7,4,0,0,0,0,0,0,4096,0
ascii-1MiB-io-materialize,base,c,2,0.01,0.01,100%,0:00.03,0,0,0,0,43288,0,0,10716,7,6,0,0,0,0,0,0,4096,0
ascii-1MiB-io-materialize,base,c,3,0.01,0.01,97%,0:00.03,0,0,0,0,43300,0,0,10717,7,14,0,0,0,0,0,0,4096,0
ascii-1MiB-io-materialize,base,c,4,0.01,0.01,97%,0:00.03,0,0,0,0,43028,0,0,10712,7,13,0,0,0,0,0,0,4096,0
ascii-1MiB-io-materialize,base,c,5,0.01,0.01,96%,0:00.03,0,0,0,0,43364,0,0,10716,7,1,0,0,0,0,0,0,4096,0
ascii-1MiB-io-materialize,base,c,6,0.01,0.01,96%,0:00.03,0,0,0,0,43216,0,0,10717,7,3,0,0,0,0,0,0,4096,0
ascii-1MiB-io-materialize,base,c,7,0.01,0.01,96%,0:00.03,0,0,0,0,43256,0,0,10718,7,7,0,0,0,0,0,0,4096,0
ascii-1MiB-io-materialize,base,js,warm,0.01,0.01,110%,0:00.03,0,0,0,0,57072,0,0,5785,100,3,0,0,0,0,0,0,4096,1
ascii-1MiB-io-materialize,base,js,1,0.01,0.01,103%,0:00.03,0,0,0,0,57084,0,0,5763,132,4,0,0,0,0,0,0,4096,1
ascii-1MiB-io-materialize,base,js,2,0.01,0.01,106%,0:00.03,0,0,0,0,56944,0,0,5778,127,2,0,0,0,0,0,0,4096,1
ascii-1MiB-io-materialize,base,js,3,0.02,0.00,106%,0:00.03,0,0,0,0,57252,0,0,5782,119,10,0,0,0,0,0,0,4096,1
ascii-1MiB-io-materialize,base,js,4,0.02,0.00,109%,0:00.03,0,0,0,0,56636,0,0,5781,132,12,0,0,0,0,0,0,4096,1
ascii-1MiB-io-materialize,base,js,5,0.02,0.01,106%,0:00.02,0,0,0,0,56824,0,0,5762,104,9,0,0,0,0,0,0,4096,1
ascii-1MiB-io-materialize,base,js,6,0.01,0.02,109%,0:00.03,0,0,0,0,57140,0,0,5777,120,0,0,0,0,0,0,0,4096,1
ascii-1MiB-io-materialize,base,js,7,0.01,0.01,106%,0:00.03,0,0,0,0,57028,0,0,5786,133,14,0,0,0,0,0,0,4096,1
ascii-1MiB-io-materialize,base,c-counters,1,0.02,0.01,97%,0:00.04,0,0,0,0,43236,0,0,10719,7,4,0,0,0,0,0,0,4096,0
ascii-1MiB-io-materialize,candidate,c,warm,0.01,0.00,95%,0:00.02,0,0,0,0,13236,0,0,3264,6,3,0,0,0,0,0,0,4096,0
ascii-1MiB-io-materialize,candidate,c,1,0.01,0.00,95%,0:00.02,0,0,0,0,13196,0,0,3261,7,5,0,0,0,0,0,0,4096,0
ascii-1MiB-io-materialize,candidate,c,2,0.01,0.00,95%,0:00.02,0,0,0,0,13276,0,0,3266,7,5,0,0,0,0,0,0,4096,0
ascii-1MiB-io-materialize,candidate,c,3,0.01,0.00,95%,0:00.02,0,0,0,0,13252,0,0,3263,7,9,0,0,0,0,0,0,4096,0
ascii-1MiB-io-materialize,candidate,c,4,0.01,0.00,95%,0:00.02,0,0,0,0,13476,0,0,3265,7,12,0,0,0,0,0,0,4096,0
ascii-1MiB-io-materialize,candidate,c,5,0.01,0.00,95%,0:00.02,0,0,0,0,13460,0,0,3260,7,7,0,0,0,0,0,0,4096,0
ascii-1MiB-io-materialize,candidate,c,6,0.01,0.00,94%,0:00.01,0,0,0,0,13264,0,0,3263,7,1,0,0,0,0,0,0,4096,0
ascii-1MiB-io-materialize,candidate,c,7,0.01,0.00,95%,0:00.02,0,0,0,0,13012,0,0,3262,7,6,0,0,0,0,0,0,4096,0
ascii-1MiB-io-materialize,candidate,js,warm,0.21,0.08,147%,0:00.19,0,0,0,0,177996,0,0,35434,8455,58,0,0,0,0,0,0,4096,0
ascii-1MiB-io-materialize,candidate,js,1,0.20,0.08,150%,0:00.19,0,0,0,0,177624,0,0,35267,8645,108,0,0,0,0,0,0,4096,0
ascii-1MiB-io-materialize,candidate,js,2,0.18,0.09,155%,0:00.18,0,0,0,0,178508,0,0,35495,9266,58,0,0,0,0,0,0,4096,0
ascii-1MiB-io-materialize,candidate,js,3,0.20,0.08,148%,0:00.19,0,0,0,0,178504,0,0,35477,7279,275,0,0,0,0,0,0,4096,0
ascii-1MiB-io-materialize,candidate,js,4,0.19,0.09,147%,0:00.19,0,0,0,0,177364,0,0,35238,8108,111,0,0,0,0,0,0,4096,0
ascii-1MiB-io-materialize,candidate,js,5,0.21,0.07,151%,0:00.19,0,0,0,0,177420,0,0,35262,8469,233,0,0,0,0,0,0,4096,0
ascii-1MiB-io-materialize,candidate,js,6,0.20,0.08,151%,0:00.19,0,0,0,0,178248,0,0,35534,8989,80,0,0,0,0,0,0,4096,0
ascii-1MiB-io-materialize,candidate,js,7,0.21,0.07,147%,0:00.19,0,0,0,0,178456,0,0,35583,6426,407,0,0,0,0,0,0,4096,0
ascii-1MiB-io-materialize,candidate,c-counters,1,0.01,0.00,95%,0:00.02,0,0,0,0,13360,0,0,3260,7,2,0,0,0,0,0,0,4096,0
ascii-8MiB-io-scan,base,c,warm,0.15,0.04,98%,0:00.20,0,0,0,0,141284,0,0,35085,7,41,0,0,0,0,0,0,4096,0
ascii-8MiB-io-scan,base,c,1,0.16,0.04,94%,0:00.21,0,0,0,0,141240,0,0,35086,7,15,0,0,0,0,0,0,4096,0
ascii-8MiB-io-scan,base,c,2,0.15,0.05,99%,0:00.20,0,0,0,0,141488,0,0,35085,7,30,0,0,0,0,0,0,4096,0
ascii-8MiB-io-scan,base,c,3,0.15,0.05,98%,0:00.20,0,0,0,0,141172,0,0,35089,7,40,0,0,0,0,0,0,4096,0
ascii-8MiB-io-scan,base,c,4,0.14,0.05,99%,0:00.20,0,0,0,0,141196,0,0,35083,7,14,0,0,0,0,0,0,4096,0
ascii-8MiB-io-scan,base,c,5,0.14,0.05,97%,0:00.20,0,0,0,0,141360,0,0,35082,7,59,0,0,0,0,0,0,4096,0
ascii-8MiB-io-scan,base,c,6,0.15,0.05,98%,0:00.20,0,0,0,0,141284,0,0,35086,7,37,0,0,0,0,0,0,4096,0
ascii-8MiB-io-scan,base,c,7,0.16,0.05,98%,0:00.22,0,0,0,0,141284,0,0,35085,7,53,0,0,0,0,0,0,4096,0
ascii-8MiB-io-scan,base,js,warm,7.61,0.68,113%,0:07.30,0,0,0,0,235552,0,0,119802,109068,1880,0,0,0,0,0,0,4096,0
ascii-8MiB-io-scan,base,js,1,7.70,0.66,112%,0:07.40,0,0,0,0,235832,0,0,118587,108698,1857,0,0,0,0,0,0,4096,0
ascii-8MiB-io-scan,base,js,2,7.59,0.69,113%,0:07.30,0,0,0,0,243156,0,0,123591,110077,1672,0,0,0,0,0,0,4096,0
ascii-8MiB-io-scan,base,js,3,7.74,0.61,113%,0:07.37,0,0,0,0,226444,0,0,118714,111085,1654,0,0,0,0,0,0,4096,0
ascii-8MiB-io-scan,base,js,4,7.53,0.72,113%,0:07.28,0,0,0,0,242792,0,0,124519,107612,1741,0,0,0,0,0,0,4096,0
ascii-8MiB-io-scan,base,js,5,7.51,0.71,113%,0:07.24,0,0,0,0,239852,0,0,125461,106935,1470,0,0,0,0,0,0,4096,0
ascii-8MiB-io-scan,base,js,6,7.74,0.70,113%,0:07.45,0,0,0,0,236472,0,0,125500,111905,2096,0,0,0,0,0,0,4096,0
ascii-8MiB-io-scan,base,js,7,7.74,0.70,113%,0:07.47,0,0,0,0,229212,0,0,125889,110421,1880,0,0,0,0,0,0,4096,0
ascii-8MiB-io-scan,base,c-counters,1,0.25,0.05,99%,0:00.31,0,0,0,0,141412,0,0,35081,7,36,0,0,0,0,0,0,4096,0
ascii-8MiB-io-scan,candidate,c,warm,0.11,0.01,99%,0:00.13,0,0,0,0,43256,0,0,10480,7,0,0,0,0,0,0,0,4096,0
ascii-8MiB-io-scan,candidate,c,1,0.11,0.01,98%,0:00.12,0,0,0,0,43112,0,0,10476,7,3,0,0,0,0,0,0,4096,0
ascii-8MiB-io-scan,candidate,c,2,0.11,0.01,99%,0:00.13,0,0,0,0,43108,0,0,10474,7,40,0,0,0,0,0,0,4096,0
ascii-8MiB-io-scan,candidate,c,3,0.12,0.01,99%,0:00.13,0,0,0,0,43124,0,0,10475,7,22,0,0,0,0,0,0,4096,0
ascii-8MiB-io-scan,candidate,c,4,0.11,0.01,98%,0:00.13,0,0,0,0,43064,0,0,10475,7,13,0,0,0,0,0,0,4096,0
ascii-8MiB-io-scan,candidate,c,5,0.11,0.01,98%,0:00.13,0,0,0,0,43192,0,0,10478,7,2,0,0,0,0,0,0,4096,0
ascii-8MiB-io-scan,candidate,c,6,0.11,0.01,98%,0:00.12,0,0,0,0,43188,0,0,10477,7,8,0,0,0,0,0,0,4096,0
ascii-8MiB-io-scan,candidate,c,7,0.11,0.01,97%,0:00.13,0,0,0,0,43056,0,0,10474,7,35,0,0,0,0,0,0,4096,0
ascii-8MiB-io-scan,candidate,js,warm,1.17,0.19,107%,0:01.27,0,0,0,0,428712,0,0,105733,2545,265,0,0,0,0,0,0,4096,0
ascii-8MiB-io-scan,candidate,js,1,1.16,0.19,107%,0:01.27,0,0,0,0,403196,0,0,105815,2578,259,0,0,0,0,0,0,4096,0
ascii-8MiB-io-scan,candidate,js,2,1.13,0.17,107%,0:01.22,0,0,0,0,446948,0,0,105840,2636,245,0,0,0,0,0,0,4096,0
ascii-8MiB-io-scan,candidate,js,3,1.18,0.18,107%,0:01.27,0,0,0,0,401424,0,0,105749,2490,277,0,0,0,0,0,0,4096,0
ascii-8MiB-io-scan,candidate,js,4,1.14,0.18,107%,0:01.24,0,0,0,0,432788,0,0,105744,2579,301,0,0,0,0,0,0,4096,0
ascii-8MiB-io-scan,candidate,js,5,1.18,0.17,106%,0:01.27,0,0,0,0,420256,0,0,105571,2547,265,0,0,0,0,0,0,4096,0
ascii-8MiB-io-scan,candidate,js,6,1.14,0.18,107%,0:01.23,0,0,0,0,418812,0,0,105533,2492,205,0,0,0,0,0,0,4096,0
ascii-8MiB-io-scan,candidate,js,7,1.20,0.18,108%,0:01.28,0,0,0,0,398792,0,0,105024,2828,375,0,0,0,0,0,0,4096,0
ascii-8MiB-io-scan,candidate,c-counters,1,0.13,0.01,98%,0:00.15,0,0,0,0,43108,0,0,10480,7,19,0,0,0,0,0,0,4096,0
ascii-8MiB-construct-scan,base,c,warm,0.33,0.15,99%,0:00.50,0,0,0,0,329520,0,0,82160,3,58,0,0,0,0,0,0,4096,0
ascii-8MiB-construct-scan,base,c,1,0.23,0.27,98%,0:00.51,0,0,0,0,330032,0,0,82165,3,108,0,0,0,0,0,0,4096,0
ascii-8MiB-construct-scan,base,c,2,0.37,0.11,99%,0:00.49,0,0,0,0,329708,0,0,82162,3,33,0,0,0,0,0,0,4096,0
ascii-8MiB-construct-scan,base,c,3,0.39,0.10,98%,0:00.50,0,0,0,0,329404,0,0,82163,3,123,0,0,0,0,0,0,4096,0
ascii-8MiB-construct-scan,base,c,4,0.40,0.10,98%,0:00.51,0,0,0,0,330036,0,0,82161,3,105,0,0,0,0,0,0,4096,0
ascii-8MiB-construct-scan,base,c,5,0.38,0.10,98%,0:00.50,0,0,0,0,329912,0,0,82164,3,84,0,0,0,0,0,0,4096,0
ascii-8MiB-construct-scan,base,c,6,0.38,0.12,99%,0:00.50,0,0,0,0,329572,0,0,82162,3,35,0,0,0,0,0,0,4096,0
ascii-8MiB-construct-scan,base,c,7,0.40,0.10,98%,0:00.51,0,0,0,0,329904,0,0,82160,3,105,0,0,0,0,0,0,4096,0
ascii-8MiB-construct-scan,base,js,warm,0.01,0.00,110%,0:00.02,0,0,0,0,51440,0,0,4926,120,9,0,0,0,0,0,0,4096,1
ascii-8MiB-construct-scan,base,js,1,0.01,0.00,114%,0:00.02,0,0,0,0,51180,0,0,4931,120,9,0,0,0,0,0,0,4096,1
ascii-8MiB-construct-scan,base,js,2,0.01,0.01,108%,0:00.02,0,0,0,0,51624,0,0,4930,123,62,0,0,0,0,0,0,4096,1
ascii-8MiB-construct-scan,base,js,3,0.01,0.00,110%,0:00.02,0,0,0,0,51272,0,0,4931,118,8,0,0,0,0,0,0,4096,1
ascii-8MiB-construct-scan,base,js,4,0.01,0.01,113%,0:00.02,0,0,0,0,51552,0,0,4932,117,3,0,0,0,0,0,0,4096,1
ascii-8MiB-construct-scan,base,js,5,0.00,0.01,115%,0:00.02,0,0,0,0,51296,0,0,4921,134,5,0,0,0,0,0,0,4096,1
ascii-8MiB-construct-scan,base,js,6,0.01,0.00,115%,0:00.01,0,0,0,0,51292,0,0,4926,128,1,0,0,0,0,0,0,4096,1
ascii-8MiB-construct-scan,base,js,7,0.01,0.01,114%,0:00.02,0,0,0,0,51368,0,0,4931,130,46,0,0,0,0,0,0,4096,1
ascii-8MiB-construct-scan,base,c-counters,1,0.54,0.12,99%,0:00.67,0,0,0,0,329572,0,0,82162,3,46,0,0,0,0,0,0,4096,0
ascii-8MiB-construct-scan,candidate,c,warm,0.11,0.00,98%,0:00.12,0,0,0,0,34928,0,0,8422,3,14,0,0,0,0,0,0,4096,0
ascii-8MiB-construct-scan,candidate,c,1,0.11,0.01,99%,0:00.12,0,0,0,0,34920,0,0,8422,3,9,0,0,0,0,0,0,4096,0
ascii-8MiB-construct-scan,candidate,c,2,0.11,0.01,98%,0:00.12,0,0,0,0,34916,0,0,8424,3,20,0,0,0,0,0,0,4096,0
ascii-8MiB-construct-scan,candidate,c,3,0.11,0.01,98%,0:00.12,0,0,0,0,34800,0,0,8420,3,20,0,0,0,0,0,0,4096,0
ascii-8MiB-construct-scan,candidate,c,4,0.11,0.01,99%,0:00.12,0,0,0,0,34864,0,0,8425,3,51,0,0,0,0,0,0,4096,0
ascii-8MiB-construct-scan,candidate,c,5,0.11,0.01,98%,0:00.12,0,0,0,0,34808,0,0,8425,3,7,0,0,0,0,0,0,4096,0
ascii-8MiB-construct-scan,candidate,c,6,0.11,0.01,96%,0:00.12,0,0,0,0,34936,0,0,8425,3,19,0,0,0,0,0,0,4096,0
ascii-8MiB-construct-scan,candidate,c,7,0.11,0.01,99%,0:00.12,0,0,0,0,34996,0,0,8424,3,3,0,0,0,0,0,0,4096,0
ascii-8MiB-construct-scan,candidate,js,warm,0.98,0.08,111%,0:00.95,0,0,0,0,112432,0,0,19992,6568,276,0,0,0,0,0,0,4096,0
ascii-8MiB-construct-scan,candidate,js,1,0.98,0.08,111%,0:00.94,0,0,0,0,113608,0,0,20169,6836,320,0,0,0,0,0,0,4096,0
ascii-8MiB-construct-scan,candidate,js,2,0.96,0.08,112%,0:00.92,0,0,0,0,114916,0,0,20592,6938,246,0,0,0,0,0,0,4096,0
ascii-8MiB-construct-scan,candidate,js,3,0.96,0.06,113%,0:00.90,0,0,0,0,114272,0,0,20542,6856,148,0,0,0,0,0,0,4096,0
ascii-8MiB-construct-scan,candidate,js,4,0.99,0.05,112%,0:00.93,0,0,0,0,112828,0,0,20160,6834,150,0,0,0,0,0,0,4096,0
ascii-8MiB-construct-scan,candidate,js,5,0.96,0.06,111%,0:00.92,0,0,0,0,113256,0,0,20193,6662,250,0,0,0,0,0,0,4096,0
ascii-8MiB-construct-scan,candidate,js,6,1.01,0.06,111%,0:00.96,0,0,0,0,112872,0,0,20227,6539,207,0,0,0,0,0,0,4096,0
ascii-8MiB-construct-scan,candidate,js,7,0.98,0.07,111%,0:00.94,0,0,0,0,112288,0,0,19946,6880,145,0,0,0,0,0,0,4096,0
ascii-8MiB-construct-scan,candidate,c-counters,1,0.13,0.01,99%,0:00.14,0,0,0,0,34916,0,0,8421,3,18,0,0,0,0,0,0,4096,0
ascii-8MiB-io-materialize,base,c,warm,0.13,0.11,98%,0:00.25,0,0,0,0,329900,0,0,84191,6,51,0,0,0,0,0,0,4096,0
ascii-8MiB-io-materialize,base,c,1,0.12,0.11,98%,0:00.24,0,0,0,0,329312,0,0,84189,7,33,0,0,0,0,0,0,4096,0
ascii-8MiB-io-materialize,base,c,2,0.12,0.11,98%,0:00.23,0,0,0,0,329808,0,0,84188,7,14,0,0,0,0,0,0,4096,0
ascii-8MiB-io-materialize,base,c,3,0.11,0.12,98%,0:00.24,0,0,0,0,329460,0,0,84190,7,31,0,0,0,0,0,0,4096,0
ascii-8MiB-io-materialize,base,c,4,0.12,0.11,98%,0:00.24,0,0,0,0,329544,0,0,84190,7,66,0,0,0,0,0,0,4096,0
ascii-8MiB-io-materialize,base,c,5,0.12,0.12,99%,0:00.24,0,0,0,0,329620,0,0,84190,7,39,0,0,0,0,0,0,4096,0
ascii-8MiB-io-materialize,base,c,6,0.12,0.11,98%,0:00.24,0,0,0,0,329676,0,0,84191,7,34,0,0,0,0,0,0,4096,0
ascii-8MiB-io-materialize,base,c,7,0.12,0.10,99%,0:00.23,0,0,0,0,329512,0,0,84190,7,43,0,0,0,0,0,0,4096,0
ascii-8MiB-io-materialize,base,js,warm,0.02,0.02,105%,0:00.03,0,0,0,0,71480,0,0,9385,108,9,0,0,0,0,0,0,4096,1
ascii-8MiB-io-materialize,base,js,1,0.01,0.02,105%,0:00.03,0,0,0,0,71684,0,0,9382,124,7,0,0,0,0,0,0,4096,1
ascii-8MiB-io-materialize,base,js,2,0.01,0.02,105%,0:00.03,0,0,0,0,71724,0,0,9399,106,12,0,0,0,0,0,0,4096,1
ascii-8MiB-io-materialize,base,js,3,0.02,0.02,107%,0:00.03,0,0,0,0,71420,0,0,9393,115,21,0,0,0,0,0,0,4096,1
ascii-8MiB-io-materialize,base,js,4,0.02,0.01,105%,0:00.04,0,0,0,0,71416,0,0,9383,133,12,0,0,0,0,0,0,4096,1
ascii-8MiB-io-materialize,base,js,5,0.01,0.02,105%,0:00.03,0,0,0,0,71408,0,0,9384,114,13,0,0,0,0,0,0,4096,1
ascii-8MiB-io-materialize,base,js,6,0.02,0.02,109%,0:00.04,0,0,0,0,71400,0,0,9406,134,12,0,0,0,0,0,0,4096,1
ascii-8MiB-io-materialize,base,js,7,0.02,0.01,105%,0:00.03,0,0,0,0,71476,0,0,9386,118,11,0,0,0,0,0,0,4096,1
ascii-8MiB-io-materialize,base,c-counters,1,0.20,0.10,99%,0:00.31,0,0,0,0,329592,0,0,84192,7,34,0,0,0,0,0,0,4096,0
ascii-8MiB-io-materialize,candidate,c,warm,0.11,0.03,98%,0:00.15,0,0,0,0,91160,0,0,24516,7,35,0,0,0,0,0,0,4096,0
ascii-8MiB-io-materialize,candidate,c,1,0.12,0.04,98%,0:00.16,0,0,0,0,91168,0,0,24516,7,8,0,0,0,0,0,0,4096,0
ascii-8MiB-io-materialize,candidate,c,2,0.11,0.03,100%,0:00.14,0,0,0,0,90812,0,0,24517,7,19,0,0,0,0,0,0,4096,0
ascii-8MiB-io-materialize,candidate,c,3,0.12,0.03,99%,0:00.15,0,0,0,0,90908,0,0,24518,7,12,0,0,0,0,0,0,4096,0
ascii-8MiB-io-materialize,candidate,c,4,0.11,0.03,98%,0:00.15,0,0,0,0,91228,0,0,24523,7,10,0,0,0,0,0,0,4096,0
ascii-8MiB-io-materialize,candidate,c,5,0.12,0.03,98%,0:00.15,0,0,0,0,90840,0,0,24517,7,23,0,0,0,0,0,0,4096,0
ascii-8MiB-io-materialize,candidate,c,6,0.11,0.03,98%,0:00.14,0,0,0,0,90852,0,0,24518,7,21,0,0,0,0,0,0,4096,0
ascii-8MiB-io-materialize,candidate,c,7,0.11,0.03,98%,0:00.15,0,0,0,0,91076,0,0,24519,7,24,0,0,0,0,0,0,4096,0
ascii-8MiB-io-materialize,candidate,js,warm,1.45,0.64,166%,0:01.26,0,0,0,0,574364,0,0,192961,122447,550,0,0,0,0,0,0,4096,0
ascii-8MiB-io-materialize,candidate,js,1,1.44,0.65,166%,0:01.26,0,0,0,0,578128,0,0,192989,122003,562,0,0,0,0,0,0,4096,0
ascii-8MiB-io-materialize,candidate,js,2,1.41,0.66,163%,0:01.26,0,0,0,0,579908,0,0,193504,114628,621,0,0,0,0,0,0,4096,0
ascii-8MiB-io-materialize,candidate,js,3,1.52,0.63,162%,0:01.32,0,0,0,0,566788,0,0,192644,112702,1209,0,0,0,0,0,0,4096,0
ascii-8MiB-io-materialize,candidate,js,4,1.49,0.68,164%,0:01.32,0,0,0,0,569744,0,0,193419,119534,828,0,0,0,0,0,0,4096,0
ascii-8MiB-io-materialize,candidate,js,5,1.53,0.65,161%,0:01.35,0,0,0,0,563844,0,0,191973,114577,1105,0,0,0,0,0,0,4096,0
ascii-8MiB-io-materialize,candidate,js,6,1.46,0.66,162%,0:01.31,0,0,0,0,563964,0,0,191200,113955,944,0,0,0,0,0,0,4096,0
ascii-8MiB-io-materialize,candidate,js,7,1.46,0.66,164%,0:01.29,0,0,0,0,570316,0,0,192328,116102,867,0,0,0,0,0,0,4096,0
ascii-8MiB-io-materialize,candidate,c-counters,1,0.14,0.03,98%,0:00.17,0,0,0,0,90904,0,0,24519,7,27,0,0,0,0,0,0,4096,0
ascii-64MiB-io-scan,base,c,warm,1.28,0.39,99%,0:01.68,0,0,0,0,1116208,0,0,278803,7,138,0,0,0,0,0,0,4096,0
ascii-64MiB-io-scan,base,c,1,1.25,0.42,99%,0:01.69,0,0,0,0,1115832,0,0,278803,7,268,0,0,0,0,0,0,4096,0
ascii-64MiB-io-scan,base,c,2,1.24,0.41,99%,0:01.66,0,0,0,0,1116132,0,0,278803,7,312,0,0,0,0,0,0,4096,0
ascii-64MiB-io-scan,base,c,3,1.27,0.39,99%,0:01.68,0,0,0,0,1115748,0,0,278805,6,169,0,0,0,0,0,0,4096,0
ascii-64MiB-io-scan,base,c,4,1.27,0.41,99%,0:01.70,0,0,0,0,1116016,0,0,278801,7,181,0,0,0,0,0,0,4096,0
ascii-64MiB-io-scan,base,c,5,1.25,0.40,99%,0:01.67,0,0,0,0,1116148,0,0,278803,7,176,0,0,0,0,0,0,4096,0
ascii-64MiB-io-scan,base,c,6,1.22,0.42,99%,0:01.66,0,0,0,0,1115832,0,0,278806,7,167,0,0,0,0,0,0,4096,0
ascii-64MiB-io-scan,base,c,7,1.27,0.40,99%,0:01.69,0,0,0,0,1115824,0,0,278799,7,168,0,0,0,0,0,0,4096,0
ascii-64MiB-io-scan,base,c-counters,1,2.13,0.38,99%,0:02.54,0,0,0,0,1115948,0,0,278803,6,244,0,0,0,0,0,0,4096,0
ascii-64MiB-io-scan,candidate,c,warm,1.01,0.12,99%,0:01.15,0,0,0,0,329588,0,0,82155,7,113,0,0,0,0,0,0,4096,0
ascii-64MiB-io-scan,candidate,c,1,0.97,0.15,99%,0:01.12,0,0,0,0,329576,0,0,82154,7,129,0,0,0,0,0,0,4096,0
ascii-64MiB-io-scan,candidate,c,2,0.95,0.12,98%,0:01.09,0,0,0,0,329844,0,0,82157,7,163,0,0,0,0,0,0,4096,0
ascii-64MiB-io-scan,candidate,c,3,0.94,0.13,99%,0:01.08,0,0,0,0,329780,0,0,82155,9,33,0,0,0,0,0,0,4096,0
ascii-64MiB-io-scan,candidate,c,4,1.02,0.12,98%,0:01.16,0,0,0,0,329848,0,0,82160,7,219,0,0,0,0,0,0,4096,0
ascii-64MiB-io-scan,candidate,c,5,0.93,0.13,98%,0:01.08,0,0,0,0,329652,0,0,82157,7,206,0,0,0,0,0,0,4096,0
ascii-64MiB-io-scan,candidate,c,6,0.88,0.13,99%,0:01.02,0,0,0,0,329972,0,0,82156,7,22,0,0,0,0,0,0,4096,0
ascii-64MiB-io-scan,candidate,c,7,0.91,0.12,99%,0:01.04,0,0,0,0,329784,0,0,82157,7,147,0,0,0,0,0,0,4096,0
ascii-64MiB-io-scan,candidate,c-counters,1,1.04,0.11,99%,0:01.16,0,0,0,0,329592,0,0,82155,7,89,0,0,0,0,0,0,4096,0
ascii-64MiB-construct-scan,base,c,warm,3.39,0.97,98%,0:04.41,0,0,0,0,2623208,0,0,655613,3,558,0,0,0,0,0,0,4096,0
ascii-64MiB-construct-scan,base,c,1,3.06,0.92,99%,0:04.02,0,0,0,0,2623480,0,0,655616,4,457,0,0,0,0,0,0,4096,0
ascii-64MiB-construct-scan,base,c,2,2.98,0.99,99%,0:04.00,0,0,0,0,2622840,0,0,655613,3,337,0,0,0,0,0,0,4096,0
ascii-64MiB-construct-scan,base,c,3,3.03,0.91,99%,0:03.98,0,0,0,0,2622828,0,0,655612,2,492,0,0,0,0,0,0,4096,0
ascii-64MiB-construct-scan,base,c,4,3.06,0.91,99%,0:04.00,0,0,0,0,2622768,0,0,655612,3,397,0,0,0,0,0,0,4096,0
ascii-64MiB-construct-scan,base,c,5,3.08,0.91,99%,0:04.02,0,0,0,0,2622840,0,0,655611,3,457,0,0,0,0,0,0,4096,0
ascii-64MiB-construct-scan,base,c,6,3.04,0.91,98%,0:04.01,0,0,0,0,2623024,0,0,655611,3,637,0,0,0,0,0,0,4096,0
ascii-64MiB-construct-scan,base,c,7,3.06,0.93,98%,0:04.04,0,0,0,0,2623076,0,0,655610,3,622,0,0,0,0,0,0,4096,0
ascii-64MiB-construct-scan,base,c-counters,1,4.28,0.93,98%,0:05.27,0,0,0,0,2623340,0,0,655612,3,793,0,0,0,0,0,0,4096,0
ascii-64MiB-construct-scan,candidate,c,warm,0.84,0.09,98%,0:00.95,0,0,0,0,264164,0,0,65766,3,172,0,0,0,0,0,0,4096,0
ascii-64MiB-construct-scan,candidate,c,1,0.84,0.08,99%,0:00.93,0,0,0,0,264312,0,0,65766,3,179,0,0,0,0,0,0,4096,0
ascii-64MiB-construct-scan,candidate,c,2,0.85,0.09,99%,0:00.95,0,0,0,0,264504,0,0,65767,3,112,0,0,0,0,0,0,4096,0
ascii-64MiB-construct-scan,candidate,c,3,0.85,0.09,98%,0:00.96,0,0,0,0,264056,0,0,65770,3,151,0,0,0,0,0,0,4096,0
ascii-64MiB-construct-scan,candidate,c,4,0.67,0.26,98%,0:00.95,0,0,0,0,264244,0,0,65769,3,187,0,0,0,0,0,0,4096,0
ascii-64MiB-construct-scan,candidate,c,5,0.86,0.10,99%,0:00.97,0,0,0,0,264308,0,0,65770,3,68,0,0,0,0,0,0,4096,0
ascii-64MiB-construct-scan,candidate,c,6,0.86,0.09,99%,0:00.96,0,0,0,0,264360,0,0,65766,3,48,0,0,0,0,0,0,4096,0
ascii-64MiB-construct-scan,candidate,c,7,0.86,0.09,99%,0:00.96,0,0,0,0,264436,0,0,65771,3,126,0,0,0,0,0,0,4096,0
ascii-64MiB-construct-scan,candidate,c-counters,1,1.00,0.10,99%,0:01.11,0,0,0,0,264276,0,0,65772,3,111,0,0,0,0,0,0,4096,0
ascii-64MiB-io-materialize,base,c,warm,0.98,0.91,98%,0:01.91,0,0,0,0,2623020,0,0,671973,7,320,0,0,0,0,0,0,4096,0
ascii-64MiB-io-materialize,base,c,1,0.95,0.94,98%,0:01.92,0,0,0,0,2623404,0,0,671972,7,250,0,0,0,0,0,0,4096,0
ascii-64MiB-io-materialize,base,c,2,0.94,0.95,99%,0:01.91,0,0,0,0,2623128,0,0,671976,8,108,0,0,0,0,0,0,4096,0
ascii-64MiB-io-materialize,base,c,3,0.98,0.91,99%,0:01.91,0,0,0,0,2623352,0,0,671975,7,84,0,0,0,0,0,0,4096,0
ascii-64MiB-io-materialize,base,c,4,0.96,0.93,99%,0:01.91,0,0,0,0,2623188,0,0,671976,7,236,0,0,0,0,0,0,4096,0
ascii-64MiB-io-materialize,base,c,5,0.96,0.96,99%,0:01.94,0,0,0,0,2622924,0,0,671975,7,192,0,0,0,0,0,0,4096,0
ascii-64MiB-io-materialize,base,c,6,0.99,0.91,99%,0:01.92,0,0,0,0,2623172,0,0,671973,7,114,0,0,0,0,0,0,4096,0
ascii-64MiB-io-materialize,base,c,7,0.98,0.92,98%,0:01.93,0,0,0,0,2623220,0,0,671972,7,357,0,0,0,0,0,0,4096,0
ascii-64MiB-io-materialize,base,c-counters,1,1.65,0.97,99%,0:02.65,0,0,0,0,2622900,0,0,671973,7,261,0,0,0,0,0,0,4096,0
ascii-64MiB-io-materialize,candidate,c,warm,0.93,0.29,98%,0:01.24,0,0,0,0,713392,0,0,194507,7,121,0,0,0,0,0,0,4096,0
ascii-64MiB-io-materialize,candidate,c,1,0.92,0.28,99%,0:01.21,0,0,0,0,713264,0,0,194505,7,224,0,0,0,0,0,0,4096,0
ascii-64MiB-io-materialize,candidate,c,2,0.91,0.28,99%,0:01.20,0,0,0,0,713588,0,0,194503,7,41,0,0,0,0,0,0,4096,0
ascii-64MiB-io-materialize,candidate,c,3,0.95,0.27,99%,0:01.24,0,0,0,0,713324,0,0,194503,6,77,0,0,0,0,0,0,4096,0
ascii-64MiB-io-materialize,candidate,c,4,0.94,0.29,99%,0:01.24,0,0,0,0,713340,0,0,194504,7,140,0,0,0,0,0,0,4096,0
ascii-64MiB-io-materialize,candidate,c,5,0.93,0.27,99%,0:01.21,0,0,0,0,713288,0,0,194506,7,111,0,0,0,0,0,0,4096,0
ascii-64MiB-io-materialize,candidate,c,6,0.91,0.27,99%,0:01.19,0,0,0,0,713132,0,0,194503,7,69,0,0,0,0,0,0,4096,0
ascii-64MiB-io-materialize,candidate,c,7,0.93,0.30,99%,0:01.24,0,0,0,0,713380,0,0,194507,6,99,0,0,0,0,0,0,4096,0
ascii-64MiB-io-materialize,candidate,c-counters,1,1.01,0.33,98%,0:01.36,0,0,0,0,713084,0,0,194506,7,248,0,0,0,0,0,0,4096,0
unicode-1MiB-io-scan,base,c,warm,0.01,0.00,94%,0:00.01,0,0,0,0,13412,0,0,3066,6,13,0,0,0,0,0,0,4096,0
unicode-1MiB-io-scan,base,c,1,0.00,0.00,94%,0:00.01,0,0,0,0,13428,0,0,3067,7,0,0,0,0,0,0,0,4096,0
unicode-1MiB-io-scan,base,c,2,0.01,0.00,94%,0:00.01,0,0,0,0,13496,0,0,3068,7,5,0,0,0,0,0,0,4096,0
unicode-1MiB-io-scan,base,c,3,0.01,0.00,94%,0:00.01,0,0,0,0,13492,0,0,3066,7,1,0,0,0,0,0,0,4096,0
unicode-1MiB-io-scan,base,c,4,0.01,0.00,94%,0:00.01,0,0,0,0,13432,0,0,3068,7,7,0,0,0,0,0,0,4096,0
unicode-1MiB-io-scan,base,c,5,0.01,0.00,100%,0:00.01,0,0,0,0,13548,0,0,3069,7,7,0,0,0,0,0,0,4096,0
unicode-1MiB-io-scan,base,c,6,0.01,0.00,94%,0:00.01,0,0,0,0,13496,0,0,3068,7,4,0,0,0,0,0,0,4096,0
unicode-1MiB-io-scan,base,c,7,0.01,0.00,94%,0:00.01,0,0,0,0,13428,0,0,3069,7,1,0,0,0,0,0,0,4096,0
unicode-1MiB-io-scan,base,js,warm,0.65,0.11,120%,0:00.64,0,0,0,0,162932,0,0,34679,5697,134,0,0,0,0,0,0,4096,0
unicode-1MiB-io-scan,base,js,1,0.68,0.09,120%,0:00.65,0,0,0,0,163052,0,0,34517,5712,242,0,0,0,0,0,0,4096,0
unicode-1MiB-io-scan,base,js,2,0.70,0.08,119%,0:00.66,0,0,0,0,162568,0,0,34296,5918,131,0,0,0,0,0,0,4096,0
unicode-1MiB-io-scan,base,js,3,0.69,0.07,120%,0:00.64,0,0,0,0,163392,0,0,34511,5613,136,0,0,0,0,0,0,4096,0
unicode-1MiB-io-scan,base,js,4,0.66,0.09,120%,0:00.63,0,0,0,0,162936,0,0,34826,5643,169,0,0,0,0,0,0,4096,0
unicode-1MiB-io-scan,base,js,5,0.68,0.10,119%,0:00.65,0,0,0,0,162768,0,0,34468,5807,146,0,0,0,0,0,0,4096,0
unicode-1MiB-io-scan,base,js,6,0.72,0.09,119%,0:00.68,0,0,0,0,163008,0,0,34423,5868,256,0,0,0,0,0,0,4096,0
unicode-1MiB-io-scan,base,js,7,0.67,0.10,119%,0:00.64,0,0,0,0,163500,0,0,34338,5957,186,0,0,0,0,0,0,4096,0
unicode-1MiB-io-scan,base,c-counters,1,0.02,0.00,96%,0:00.02,0,0,0,0,13492,0,0,3065,6,9,0,0,0,0,0,0,4096,0
unicode-1MiB-io-scan,candidate,c,warm,0.01,0.00,100%,0:00.01,0,0,0,0,5752,0,0,1134,7,1,0,0,0,0,0,0,4096,0
unicode-1MiB-io-scan,candidate,c,1,0.01,0.00,92%,0:00.01,0,0,0,0,5812,0,0,1132,7,2,0,0,0,0,0,0,4096,0
unicode-1MiB-io-scan,candidate,c,2,0.01,0.00,92%,0:00.01,0,0,0,0,5752,0,0,1133,7,10,0,0,0,0,0,0,4096,0
unicode-1MiB-io-scan,candidate,c,3,0.01,0.00,100%,0:00.01,0,0,0,0,5732,0,0,1132,7,1,0,0,0,0,0,0,4096,0
unicode-1MiB-io-scan,candidate,c,4,0.01,0.00,100%,0:00.01,0,0,0,0,5808,0,0,1133,7,3,0,0,0,0,0,0,4096,0
unicode-1MiB-io-scan,candidate,c,5,0.01,0.00,100%,0:00.01,0,0,0,0,5808,0,0,1134,7,2,0,0,0,0,0,0,4096,0
unicode-1MiB-io-scan,candidate,c,6,0.01,0.00,92%,0:00.01,0,0,0,0,5752,0,0,1132,7,4,0,0,0,0,0,0,4096,0
unicode-1MiB-io-scan,candidate,c,7,0.01,0.00,93%,0:00.01,0,0,0,0,5732,0,0,1131,8,0,0,0,0,0,0,0,4096,0
unicode-1MiB-io-scan,candidate,js,warm,0.17,0.05,127%,0:00.17,0,0,0,0,139316,0,0,25769,809,64,0,0,0,0,0,0,4096,0
unicode-1MiB-io-scan,candidate,js,1,0.18,0.05,125%,0:00.18,0,0,0,0,145016,0,0,27085,767,59,0,0,0,0,0,0,4096,0
unicode-1MiB-io-scan,candidate,js,2,0.17,0.04,129%,0:00.17,0,0,0,0,139280,0,0,25655,791,38,0,0,0,0,0,0,4096,0
unicode-1MiB-io-scan,candidate,js,3,0.20,0.05,144%,0:00.17,0,0,0,0,147708,0,0,27833,855,28,0,0,0,0,0,0,4096,0
unicode-1MiB-io-scan,candidate,js,4,0.17,0.04,128%,0:00.16,0,0,0,0,139456,0,0,25745,770,49,0,0,0,0,0,0,4096,0
unicode-1MiB-io-scan,candidate,js,5,0.17,0.04,125%,0:00.17,0,0,0,0,143624,0,0,26746,793,41,0,0,0,0,0,0,4096,0
unicode-1MiB-io-scan,candidate,js,6,0.18,0.04,128%,0:00.17,0,0,0,0,141116,0,0,26083,759,41,0,0,0,0,0,0,4096,0
unicode-1MiB-io-scan,candidate,js,7,0.16,0.05,129%,0:00.16,0,0,0,0,139008,0,0,25627,697,41,0,0,0,0,0,0,4096,0
unicode-1MiB-io-scan,candidate,c-counters,1,0.01,0.00,100%,0:00.01,0,0,0,0,5732,0,0,1132,7,4,0,0,0,0,0,0,4096,0
unicode-1MiB-construct-scan,base,c,warm,0.03,0.00,93%,0:00.04,0,0,0,0,27700,0,0,6626,3,6,0,0,0,0,0,0,4096,0
unicode-1MiB-construct-scan,base,c,1,0.02,0.01,97%,0:00.04,0,0,0,0,27764,0,0,6626,3,2,0,0,0,0,0,0,4096,0
unicode-1MiB-construct-scan,base,c,2,0.03,0.00,97%,0:00.03,0,0,0,0,27952,0,0,6626,3,7,0,0,0,0,0,0,4096,0
unicode-1MiB-construct-scan,base,c,3,0.03,0.00,97%,0:00.03,0,0,0,0,27952,0,0,6627,3,2,0,0,0,0,0,0,4096,0
unicode-1MiB-construct-scan,base,c,4,0.03,0.00,97%,0:00.04,0,0,0,0,27956,0,0,6627,3,31,0,0,0,0,0,0,4096,0
unicode-1MiB-construct-scan,base,c,5,0.03,0.00,95%,0:00.04,0,0,0,0,27876,0,0,6626,3,8,0,0,0,0,0,0,4096,0
unicode-1MiB-construct-scan,base,c,6,0.03,0.00,95%,0:00.04,0,0,0,0,27896,0,0,6625,3,10,0,0,0,0,0,0,4096,0
unicode-1MiB-construct-scan,base,c,7,0.03,0.00,97%,0:00.04,0,0,0,0,27884,0,0,6627,3,19,0,0,0,0,0,0,4096,0
unicode-1MiB-construct-scan,base,js,warm,0.01,0.00,110%,0:00.02,0,0,0,0,51644,0,0,4972,108,2,0,0,0,0,0,0,4096,1
unicode-1MiB-construct-scan,base,js,1,0.01,0.00,115%,0:00.02,0,0,0,0,51648,0,0,4977,118,3,0,0,0,0,0,0,4096,1
unicode-1MiB-construct-scan,base,js,2,0.01,0.01,119%,0:00.02,0,0,0,0,51720,0,0,4981,128,21,0,0,0,0,0,0,4096,1
unicode-1MiB-construct-scan,base,js,3,0.01,0.01,108%,0:00.02,0,0,0,0,51664,0,0,4978,128,8,0,0,0,0,0,0,4096,1
unicode-1MiB-construct-scan,base,js,4,0.01,0.00,110%,0:00.02,0,0,0,0,51724,0,0,4983,101,8,0,0,0,0,0,0,4096,1
unicode-1MiB-construct-scan,base,js,5,0.01,0.00,109%,0:00.02,0,0,0,0,51704,0,0,4988,115,21,0,0,0,0,0,0,4096,1
unicode-1MiB-construct-scan,base,js,6,0.01,0.01,115%,0:00.02,0,0,0,0,51712,0,0,4978,145,8,0,0,0,0,0,0,4096,1
unicode-1MiB-construct-scan,base,js,7,0.01,0.01,114%,0:00.02,0,0,0,0,51596,0,0,4984,129,2,0,0,0,0,0,0,4096,1
unicode-1MiB-construct-scan,base,c-counters,1,0.04,0.01,98%,0:00.05,0,0,0,0,27896,0,0,6625,3,0,0,0,0,0,0,0,4096,0
unicode-1MiB-construct-scan,candidate,c,warm,0.00,0.00,91%,0:00.01,0,0,0,0,4836,0,0,873,3,6,0,0,0,0,0,0,4096,0
unicode-1MiB-construct-scan,candidate,c,1,0.01,0.00,92%,0:00.01,0,0,0,0,4856,0,0,873,3,5,0,0,0,0,0,0,4096,0
unicode-1MiB-construct-scan,candidate,c,2,0.01,0.00,100%,0:00.01,0,0,0,0,4920,0,0,876,3,1,0,0,0,0,0,0,4096,0
unicode-1MiB-construct-scan,candidate,c,3,0.01,0.00,91%,0:00.01,0,0,0,0,4984,0,0,874,3,11,0,0,0,0,0,0,4096,0
unicode-1MiB-construct-scan,candidate,c,4,0.01,0.00,91%,0:00.01,0,0,0,0,4712,0,0,873,3,2,0,0,0,0,0,0,4096,0
unicode-1MiB-construct-scan,candidate,c,5,0.01,0.00,92%,0:00.01,0,0,0,0,4784,0,0,873,2,9,0,0,0,0,0,0,4096,0
unicode-1MiB-construct-scan,candidate,c,6,0.01,0.00,91%,0:00.01,0,0,0,0,4840,0,0,872,2,3,0,0,0,0,0,0,4096,0
unicode-1MiB-construct-scan,candidate,c,7,0.00,0.00,90%,0:00.01,0,0,0,0,4844,0,0,874,2,4,0,0,0,0,0,0,4096,0
unicode-1MiB-construct-scan,candidate,js,warm,0.12,0.03,135%,0:00.11,0,0,0,0,96648,0,0,15503,769,29,0,0,0,0,0,0,4096,0
unicode-1MiB-construct-scan,candidate,js,1,0.12,0.03,133%,0:00.11,0,0,0,0,96500,0,0,15454,775,35,0,0,0,0,0,0,4096,0
unicode-1MiB-construct-scan,candidate,js,2,0.15,0.03,160%,0:00.11,0,0,0,0,103648,0,0,17392,731,17,0,0,0,0,0,0,4096,0
unicode-1MiB-construct-scan,candidate,js,3,0.11,0.03,130%,0:00.11,0,0,0,0,96120,0,0,15270,795,35,0,0,0,0,0,0,4096,0
unicode-1MiB-construct-scan,candidate,js,4,0.11,0.03,134%,0:00.11,0,0,0,0,96064,0,0,15297,747,32,0,0,0,0,0,0,4096,0
unicode-1MiB-construct-scan,candidate,js,5,0.13,0.04,155%,0:00.11,0,0,0,0,103572,0,0,17457,776,49,0,0,0,0,0,0,4096,0
unicode-1MiB-construct-scan,candidate,js,6,0.12,0.03,133%,0:00.11,0,0,0,0,95652,0,0,15216,748,30,0,0,0,0,0,0,4096,0
unicode-1MiB-construct-scan,candidate,js,7,0.12,0.04,142%,0:00.11,0,0,0,0,102508,0,0,17089,764,42,0,0,0,0,0,0,4096,0
unicode-1MiB-construct-scan,candidate,c-counters,1,0.01,0.00,92%,0:00.01,0,0,0,0,4724,0,0,878,3,4,0,0,0,0,0,0,4096,0
unicode-1MiB-io-materialize,base,c,warm,0.01,0.00,95%,0:00.02,0,0,0,0,27936,0,0,6878,7,8,0,0,0,0,0,0,4096,0
unicode-1MiB-io-materialize,base,c,1,0.00,0.01,100%,0:00.01,0,0,0,0,27876,0,0,6875,7,6,0,0,0,0,0,0,4096,0
unicode-1MiB-io-materialize,base,c,2,0.01,0.00,100%,0:00.01,0,0,0,0,27980,0,0,6878,7,4,0,0,0,0,0,0,4096,0
unicode-1MiB-io-materialize,base,c,3,0.01,0.00,95%,0:00.02,0,0,0,0,28004,0,0,6879,7,1,0,0,0,0,0,0,4096,0
unicode-1MiB-io-materialize,base,c,4,0.00,0.01,100%,0:00.02,0,0,0,0,27564,0,0,6879,7,3,0,0,0,0,0,0,4096,0
unicode-1MiB-io-materialize,base,c,5,0.01,0.00,95%,0:00.02,0,0,0,0,27856,0,0,6874,7,4,0,0,0,0,0,0,4096,0
unicode-1MiB-io-materialize,base,c,6,0.01,0.01,95%,0:00.02,0,0,0,0,27864,0,0,6877,7,1,0,0,0,0,0,0,4096,0
unicode-1MiB-io-materialize,base,c,7,0.00,0.01,95%,0:00.02,0,0,0,0,27508,0,0,6879,7,7,0,0,0,0,0,0,4096,0
unicode-1MiB-io-materialize,base,js,warm,0.02,0.01,110%,0:00.02,0,0,0,0,57968,0,0,5971,121,7,0,0,0,0,0,0,4096,1
unicode-1MiB-io-materialize,base,js,1,0.01,0.01,103%,0:00.03,0,0,0,0,57976,0,0,5962,125,19,0,0,0,0,0,0,4096,1
unicode-1MiB-io-materialize,base,js,2,0.01,0.01,111%,0:00.02,0,0,0,0,57656,0,0,5971,119,6,0,0,0,0,0,0,4096,1
unicode-1MiB-io-materialize,base,js,3,0.01,0.01,109%,0:00.03,0,0,0,0,57724,0,0,5983,127,16,0,0,0,0,0,0,4096,1
unicode-1MiB-io-materialize,base,js,4,0.02,0.01,113%,0:00.02,0,0,0,0,57704,0,0,5982,139,9,0,0,0,0,0,0,4096,1
unicode-1MiB-io-materialize,base,js,5,0.02,0.01,102%,0:00.03,0,0,0,0,57848,0,0,5961,105,9,0,0,0,0,0,0,4096,1
unicode-1MiB-io-materialize,base,js,6,0.02,0.01,108%,0:00.03,0,0,0,0,57452,0,0,5975,123,8,0,0,0,0,0,0,4096,1
unicode-1MiB-io-materialize,base,js,7,0.02,0.01,109%,0:00.03,0,0,0,0,57848,0,0,5983,107,26,0,0,0,0,0,0,4096,1
unicode-1MiB-io-materialize,base,c-counters,1,0.01,0.01,96%,0:00.02,0,0,0,0,27804,0,0,6873,7,9,0,0,0,0,0,0,4096,0
unicode-1MiB-io-materialize,candidate,c,warm,0.01,0.00,100%,0:00.01,0,0,0,0,10984,0,0,2669,7,0,0,0,0,0,0,0,4096,0
unicode-1MiB-io-materialize,candidate,c,1,0.01,0.00,93%,0:00.01,0,0,0,0,11100,0,0,2673,7,3,0,0,0,0,0,0,4096,0
unicode-1MiB-io-materialize,candidate,c,2,0.01,0.00,94%,0:00.01,0,0,0,0,10956,0,0,2670,7,5,0,0,0,0,0,0,4096,0
unicode-1MiB-io-materialize,candidate,c,3,0.00,0.00,93%,0:00.01,0,0,0,0,10988,0,0,2673,7,14,0,0,0,0,0,0,4096,0
unicode-1MiB-io-materialize,candidate,c,4,0.01,0.00,93%,0:00.01,0,0,0,0,11036,0,0,2671,7,0,0,0,0,0,0,0,4096,0
unicode-1MiB-io-materialize,candidate,c,5,0.01,0.00,100%,0:00.01,0,0,0,0,10920,0,0,2668,7,0,0,0,0,0,0,0,4096,0
unicode-1MiB-io-materialize,candidate,c,6,0.01,0.00,93%,0:00.01,0,0,0,0,11032,0,0,2672,7,1,0,0,0,0,0,0,4096,0
unicode-1MiB-io-materialize,candidate,c,7,0.01,0.00,93%,0:00.01,0,0,0,0,10836,0,0,2673,7,3,0,0,0,0,0,0,4096,0
unicode-1MiB-io-materialize,candidate,js,warm,0.17,0.07,150%,0:00.16,0,0,0,0,162272,0,0,31474,6253,49,0,0,0,0,0,0,4096,0
unicode-1MiB-io-materialize,candidate,js,1,0.18,0.06,148%,0:00.17,0,0,0,0,161368,0,0,31425,5756,48,0,0,0,0,0,0,4096,0
unicode-1MiB-io-materialize,candidate,js,2,0.16,0.08,152%,0:00.16,0,0,0,0,163976,0,0,31966,6184,36,0,0,0,0,0,0,4096,0
unicode-1MiB-io-materialize,candidate,js,3,0.17,0.07,149%,0:00.16,0,0,0,0,161100,0,0,31307,6152,68,0,0,0,0,0,0,4096,0
unicode-1MiB-io-materialize,candidate,js,4,0.16,0.07,150%,0:00.15,0,0,0,0,162776,0,0,31628,6007,28,0,0,0,0,0,0,4096,0
unicode-1MiB-io-materialize,candidate,js,5,0.17,0.07,148%,0:00.16,0,0,0,0,162952,0,0,31562,6035,71,0,0,0,0,0,0,4096,0
unicode-1MiB-io-materialize,candidate,js,6,0.17,0.07,147%,0:00.16,0,0,0,0,162252,0,0,31489,5883,76,0,0,0,0,0,0,4096,0
unicode-1MiB-io-materialize,candidate,js,7,0.18,0.06,146%,0:00.16,0,0,0,0,161552,0,0,31269,5519,135,0,0,0,0,0,0,4096,0
unicode-1MiB-io-materialize,candidate,c-counters,1,0.01,0.00,94%,0:00.01,0,0,0,0,10872,0,0,2668,7,4,0,0,0,0,0,0,4096,0
unicode-8MiB-io-scan,base,c,warm,0.09,0.03,99%,0:00.13,0,0,0,0,92260,0,0,22779,7,7,0,0,0,0,0,0,4096,0
unicode-8MiB-io-scan,base,c,1,0.09,0.03,99%,0:00.13,0,0,0,0,92276,0,0,22779,7,11,0,0,0,0,0,0,4096,0
unicode-8MiB-io-scan,base,c,2,0.09,0.03,97%,0:00.13,0,0,0,0,92280,0,0,22779,7,21,0,0,0,0,0,0,4096,0
unicode-8MiB-io-scan,base,c,3,0.10,0.02,98%,0:00.13,0,0,0,0,92080,0,0,22778,7,20,0,0,0,0,0,0,4096,0
unicode-8MiB-io-scan,base,c,4,0.10,0.03,98%,0:00.13,0,0,0,0,92280,0,0,22782,6,13,0,0,0,0,0,0,4096,0
unicode-8MiB-io-scan,base,c,5,0.10,0.03,98%,0:00.13,0,0,0,0,92264,0,0,22778,7,17,0,0,0,0,0,0,4096,0
unicode-8MiB-io-scan,base,c,6,0.10,0.02,97%,0:00.13,0,0,0,0,92132,0,0,22778,7,28,0,0,0,0,0,0,4096,0
unicode-8MiB-io-scan,base,c,7,0.10,0.02,97%,0:00.13,0,0,0,0,92268,0,0,22778,7,26,0,0,0,0,0,0,4096,0
unicode-8MiB-io-scan,base,js,warm,5.62,0.45,110%,0:05.49,0,0,0,0,288560,0,0,127362,56122,1338,0,0,0,0,0,0,4096,0
unicode-8MiB-io-scan,base,js,1,5.58,0.43,110%,0:05.46,0,0,0,0,289780,0,0,127629,52359,1191,0,0,0,0,0,0,4096,0
unicode-8MiB-io-scan,base,js,2,5.56,0.57,110%,0:05.56,0,0,0,0,289256,0,0,123261,56011,1696,0,0,0,0,0,0,4096,0
unicode-8MiB-io-scan,base,js,3,5.54,0.44,109%,0:05.45,0,0,0,0,290656,0,0,125238,51823,1222,0,0,0,0,0,0,4096,0
unicode-8MiB-io-scan,base,js,4,5.64,0.43,110%,0:05.51,0,0,0,0,333472,0,0,148460,51870,1343,0,0,0,0,0,0,4096,0
unicode-8MiB-io-scan,base,js,5,5.65,0.46,110%,0:05.53,0,0,0,0,287848,0,0,121365,58327,1554,0,0,0,0,0,0,4096,0
unicode-8MiB-io-scan,base,js,6,5.61,0.42,110%,0:05.45,0,0,0,0,289428,0,0,121790,58142,1442,0,0,0,0,0,0,4096,0
unicode-8MiB-io-scan,base,js,7,5.55,0.48,110%,0:05.48,0,0,0,0,294340,0,0,131322,52067,1599,0,0,0,0,0,0,4096,0
unicode-8MiB-io-scan,base,c-counters,1,0.17,0.03,99%,0:00.20,0,0,0,0,92012,0,0,22779,7,40,0,0,0,0,0,0,4096,0
unicode-8MiB-io-scan,candidate,c,warm,0.08,0.01,98%,0:00.09,0,0,0,0,30904,0,0,7404,7,5,0,0,0,0,0,0,4096,0
unicode-8MiB-io-scan,candidate,c,1,0.07,0.01,98%,0:00.09,0,0,0,0,30584,0,0,7403,7,4,0,0,0,0,0,0,4096,0
unicode-8MiB-io-scan,candidate,c,2,0.08,0.01,97%,0:00.09,0,0,0,0,30820,0,0,7406,7,6,0,0,0,0,0,0,4096,0
unicode-8MiB-io-scan,candidate,c,3,0.08,0.01,98%,0:00.10,0,0,0,0,30772,0,0,7403,7,17,0,0,0,0,0,0,4096,0
unicode-8MiB-io-scan,candidate,c,4,0.08,0.01,98%,0:00.09,0,0,0,0,30764,0,0,7405,7,5,0,0,0,0,0,0,4096,0
unicode-8MiB-io-scan,candidate,c,5,0.08,0.01,98%,0:00.09,0,0,0,0,30828,0,0,7406,7,5,0,0,0,0,0,0,4096,0
unicode-8MiB-io-scan,candidate,c,6,0.08,0.01,98%,0:00.09,0,0,0,0,30840,0,0,7402,7,9,0,0,0,0,0,0,4096,0
unicode-8MiB-io-scan,candidate,c,7,0.07,0.01,98%,0:00.09,0,0,0,0,30764,0,0,7404,7,23,0,0,0,0,0,0,4096,0
unicode-8MiB-io-scan,candidate,js,warm,1.01,0.22,117%,0:01.05,0,0,0,0,535160,0,0,137963,2394,113,0,0,0,0,0,0,4096,0
unicode-8MiB-io-scan,candidate,js,1,1.05,0.21,115%,0:01.09,0,0,0,0,534024,0,0,137729,2284,258,0,0,0,0,0,0,4096,0
unicode-8MiB-io-scan,candidate,js,2,0.98,0.25,115%,0:01.06,0,0,0,0,555616,0,0,137888,2323,204,0,0,0,0,0,0,4096,0
unicode-8MiB-io-scan,candidate,js,3,1.01,0.23,116%,0:01.06,0,0,0,0,534204,0,0,137945,2257,170,0,0,0,0,0,0,4096,0
unicode-8MiB-io-scan,candidate,js,4,1.03,0.23,115%,0:01.10,0,0,0,0,532900,0,0,137824,2270,224,0,0,0,0,0,0,4096,0
unicode-8MiB-io-scan,candidate,js,5,0.99,0.23,116%,0:01.05,0,0,0,0,549660,0,0,137088,2330,68,0,0,0,0,0,0,4096,0
unicode-8MiB-io-scan,candidate,js,6,1.04,0.23,115%,0:01.11,0,0,0,0,534844,0,0,138123,2444,255,0,0,0,0,0,0,4096,0
unicode-8MiB-io-scan,candidate,js,7,0.99,0.22,116%,0:01.04,0,0,0,0,547540,0,0,138057,2123,88,0,0,0,0,0,0,4096,0
unicode-8MiB-io-scan,candidate,c-counters,1,0.09,0.01,96%,0:00.11,0,0,0,0,30964,0,0,7407,7,22,0,0,0,0,0,0,4096,0
unicode-8MiB-construct-scan,base,c,warm,0.23,0.07,98%,0:00.31,0,0,0,0,206764,0,0,51427,3,25,0,0,0,0,0,0,4096,0
unicode-8MiB-construct-scan,base,c,1,0.23,0.06,99%,0:00.30,0,0,0,0,207088,0,0,51425,3,7,0,0,0,0,0,0,4096,0
unicode-8MiB-construct-scan,base,c,2,0.21,0.07,99%,0:00.29,0,0,0,0,206896,0,0,51426,3,13,0,0,0,0,0,0,4096,0
unicode-8MiB-construct-scan,base,c,3,0.22,0.06,99%,0:00.29,0,0,0,0,206968,0,0,51423,3,3,0,0,0,0,0,0,4096,0
unicode-8MiB-construct-scan,base,c,4,0.21,0.07,97%,0:00.29,0,0,0,0,207220,0,0,51429,3,58,0,0,0,0,0,0,4096,0
unicode-8MiB-construct-scan,base,c,5,0.23,0.06,97%,0:00.29,0,0,0,0,207080,0,0,51423,2,68,0,0,0,0,0,0,4096,0
unicode-8MiB-construct-scan,base,c,6,0.22,0.06,97%,0:00.29,0,0,0,0,207016,0,0,51425,3,60,0,0,0,0,0,0,4096,0
unicode-8MiB-construct-scan,base,c,7,0.22,0.06,99%,0:00.29,0,0,0,0,206824,0,0,51425,3,17,0,0,0,0,0,0,4096,0
unicode-8MiB-construct-scan,base,js,warm,0.01,0.01,109%,0:00.02,0,0,0,0,51584,0,0,4995,124,7,0,0,0,0,0,0,4096,1
unicode-8MiB-construct-scan,base,js,1,0.01,0.01,108%,0:00.02,0,0,0,0,52088,0,0,5007,116,5,0,0,0,0,0,0,4096,1
unicode-8MiB-construct-scan,base,js,2,0.01,0.01,110%,0:00.02,0,0,0,0,51528,0,0,5003,140,8,0,0,0,0,0,0,4096,1
unicode-8MiB-construct-scan,base,js,3,0.01,0.00,109%,0:00.02,0,0,0,0,51592,0,0,5000,109,18,0,0,0,0,0,0,4096,1
unicode-8MiB-construct-scan,base,js,4,0.01,0.01,108%,0:00.02,0,0,0,0,52028,0,0,5010,113,8,0,0,0,0,0,0,4096,1
unicode-8MiB-construct-scan,base,js,5,0.01,0.01,109%,0:00.02,0,0,0,0,51776,0,0,5022,124,3,0,0,0,0,0,0,4096,1
unicode-8MiB-construct-scan,base,js,6,0.01,0.01,109%,0:00.02,0,0,0,0,51520,0,0,5015,106,7,0,0,0,0,0,0,4096,1
unicode-8MiB-construct-scan,base,js,7,0.01,0.01,110%,0:00.02,0,0,0,0,51960,0,0,5008,121,6,0,0,0,0,0,0,4096,1
unicode-8MiB-construct-scan,base,c-counters,1,0.34,0.06,98%,0:00.41,0,0,0,0,206888,0,0,51422,2,77,0,0,0,0,0,0,4096,0
unicode-8MiB-construct-scan,candidate,c,warm,0.07,0.00,97%,0:00.08,0,0,0,0,22568,0,0,5353,3,4,0,0,0,0,0,0,4096,0
unicode-8MiB-construct-scan,candidate,c,1,0.08,0.00,97%,0:00.09,0,0,0,0,22504,0,0,5351,2,32,0,0,0,0,0,0,4096,0
unicode-8MiB-construct-scan,candidate,c,2,0.07,0.00,97%,0:00.08,0,0,0,0,22640,0,0,5351,3,4,0,0,0,0,0,0,4096,0
unicode-8MiB-construct-scan,candidate,c,3,0.07,0.00,97%,0:00.08,0,0,0,0,22836,0,0,5357,3,16,0,0,0,0,0,0,4096,0
unicode-8MiB-construct-scan,candidate,c,4,0.07,0.00,98%,0:00.08,0,0,0,0,22500,0,0,5352,3,5,0,0,0,0,0,0,4096,0
unicode-8MiB-construct-scan,candidate,c,5,0.08,0.00,97%,0:00.09,0,0,0,0,22644,0,0,5358,2,15,0,0,0,0,0,0,4096,0
unicode-8MiB-construct-scan,candidate,c,6,0.07,0.00,100%,0:00.08,0,0,0,0,22608,0,0,5357,3,8,0,0,0,0,0,0,4096,0
unicode-8MiB-construct-scan,candidate,c,7,0.07,0.00,96%,0:00.08,0,0,0,0,22572,0,0,5353,3,20,0,0,0,0,0,0,4096,0
unicode-8MiB-construct-scan,candidate,js,warm,0.69,0.05,114%,0:00.65,0,0,0,0,116080,0,0,20881,4661,236,0,0,0,0,0,0,4096,0
unicode-8MiB-construct-scan,candidate,js,1,0.69,0.05,114%,0:00.65,0,0,0,0,116472,0,0,21049,4711,191,0,0,0,0,0,0,4096,0
unicode-8MiB-construct-scan,candidate,js,2,0.67,0.07,115%,0:00.64,0,0,0,0,117016,0,0,21110,4811,147,0,0,0,0,0,0,4096,0
unicode-8MiB-construct-scan,candidate,js,3,0.68,0.07,116%,0:00.64,0,0,0,0,117216,0,0,21275,4827,80,0,0,0,0,0,0,4096,0
unicode-8MiB-construct-scan,candidate,js,4,0.66,0.05,116%,0:00.62,0,0,0,0,115708,0,0,20902,4850,104,0,0,0,0,0,0,4096,0
unicode-8MiB-construct-scan,candidate,js,5,0.67,0.05,116%,0:00.62,0,0,0,0,117536,0,0,21192,4726,108,0,0,0,0,0,0,4096,0
unicode-8MiB-construct-scan,candidate,js,6,0.67,0.07,116%,0:00.64,0,0,0,0,117288,0,0,21263,4669,153,0,0,0,0,0,0,4096,0
unicode-8MiB-construct-scan,candidate,js,7,0.65,0.08,115%,0:00.64,0,0,0,0,115576,0,0,20801,4463,102,0,0,0,0,0,0,4096,0
unicode-8MiB-construct-scan,candidate,c-counters,1,0.08,0.01,98%,0:00.09,0,0,0,0,22704,0,0,5348,3,18,0,0,0,0,0,0,4096,0
unicode-8MiB-io-materialize,base,c,warm,0.08,0.08,98%,0:00.16,0,0,0,0,206880,0,0,53470,7,20,0,0,0,0,0,0,4096,0
unicode-8MiB-io-materialize,base,c,1,0.08,0.07,98%,0:00.15,0,0,0,0,206588,0,0,53469,7,45,0,0,0,0,0,0,4096,0
unicode-8MiB-io-materialize,base,c,2,0.07,0.07,98%,0:00.15,0,0,0,0,206808,0,0,53470,7,17,0,0,0,0,0,0,4096,0
unicode-8MiB-io-materialize,base,c,3,0.06,0.08,99%,0:00.15,0,0,0,0,206936,0,0,53469,7,11,0,0,0,0,0,0,4096,0
unicode-8MiB-io-materialize,base,c,4,0.08,0.07,98%,0:00.15,0,0,0,0,206904,0,0,53469,7,35,0,0,0,0,0,0,4096,0
unicode-8MiB-io-materialize,base,c,5,0.07,0.07,99%,0:00.14,0,0,0,0,206764,0,0,53466,7,4,0,0,0,0,0,0,4096,0
unicode-8MiB-io-materialize,base,c,6,0.07,0.06,97%,0:00.14,0,0,0,0,206916,0,0,53468,8,34,0,0,0,0,0,0,4096,0
unicode-8MiB-io-materialize,base,c,7,0.08,0.06,98%,0:00.14,0,0,0,0,207128,0,0,53470,7,1,0,0,0,0,0,0,4096,0
unicode-8MiB-io-materialize,base,js,warm,0.02,0.02,107%,0:00.04,0,0,0,0,74812,0,0,10213,114,4,0,0,0,0,0,0,4096,1
unicode-8MiB-io-materialize,base,js,1,0.02,0.01,109%,0:00.04,0,0,0,0,74700,0,0,10204,110,9,0,0,0,0,0,0,4096,1
unicode-8MiB-io-materialize,base,js,2,0.01,0.02,106%,0:00.04,0,0,0,0,74676,0,0,10218,111,5,0,0,0,0,0,0,4096,1
unicode-8MiB-io-materialize,base,js,3,0.02,0.02,107%,0:00.04,0,0,0,0,74936,0,0,10203,117,5,0,0,0,0,0,0,4096,1
unicode-8MiB-io-materialize,base,js,4,0.02,0.02,107%,0:00.04,0,0,0,0,74752,0,0,10203,108,4,0,0,0,0,0,0,4096,1
unicode-8MiB-io-materialize,base,js,5,0.02,0.02,107%,0:00.04,0,0,0,0,74616,0,0,10201,99,3,0,0,0,0,0,0,4096,1
unicode-8MiB-io-materialize,base,js,6,0.02,0.02,109%,0:00.04,0,0,0,0,74556,0,0,10221,144,6,0,0,0,0,0,0,4096,1
unicode-8MiB-io-materialize,base,js,7,0.02,0.02,110%,0:00.04,0,0,0,0,74808,0,0,10193,130,1,0,0,0,0,0,0,4096,1
unicode-8MiB-io-materialize,base,c-counters,1,0.13,0.07,98%,0:00.20,0,0,0,0,206916,0,0,53472,7,32,0,0,0,0,0,0,4096,0
unicode-8MiB-io-materialize,candidate,c,warm,0.08,0.03,99%,0:00.12,0,0,0,0,71636,0,0,19694,7,7,0,0,0,0,0,0,4096,0
unicode-8MiB-io-materialize,candidate,c,1,0.08,0.02,98%,0:00.11,0,0,0,0,71912,0,0,19697,7,19,0,0,0,0,0,0,4096,0
unicode-8MiB-io-materialize,candidate,c,2,0.07,0.03,98%,0:00.11,0,0,0,0,71840,0,0,19694,7,25,0,0,0,0,0,0,4096,0
unicode-8MiB-io-materialize,candidate,c,3,0.07,0.02,97%,0:00.11,0,0,0,0,72036,0,0,19694,7,21,0,0,0,0,0,0,4096,0
unicode-8MiB-io-materialize,candidate,c,4,0.08,0.03,99%,0:00.11,0,0,0,0,71804,0,0,19693,7,25,0,0,0,0,0,0,4096,0
unicode-8MiB-io-materialize,candidate,c,5,0.09,0.02,99%,0:00.11,0,0,0,0,71736,0,0,19691,7,17,0,0,0,0,0,0,4096,0
unicode-8MiB-io-materialize,candidate,c,6,0.09,0.02,98%,0:00.11,0,0,0,0,71828,0,0,19695,7,11,0,0,0,0,0,0,4096,0
unicode-8MiB-io-materialize,candidate,c,7,0.08,0.02,98%,0:00.11,0,0,0,0,71896,0,0,19696,7,22,0,0,0,0,0,0,4096,0
unicode-8MiB-io-materialize,candidate,js,warm,1.30,0.50,158%,0:01.14,0,0,0,0,727180,0,0,205434,80375,551,0,0,0,0,0,0,4096,0
unicode-8MiB-io-materialize,candidate,js,1,1.25,0.53,158%,0:01.12,0,0,0,0,715312,0,0,202115,80443,433,0,0,0,0,0,0,4096,0
unicode-8MiB-io-materialize,candidate,js,2,1.30,0.54,159%,0:01.16,0,0,0,0,712444,0,0,201464,80774,341,0,0,0,0,0,0,4096,0
unicode-8MiB-io-materialize,candidate,js,3,1.33,0.50,158%,0:01.16,0,0,0,0,715368,0,0,201898,84324,439,0,0,0,0,0,0,4096,0
unicode-8MiB-io-materialize,candidate,js,4,1.32,0.48,157%,0:01.14,0,0,0,0,710252,0,0,201594,75834,548,0,0,0,0,0,0,4096,0
unicode-8MiB-io-materialize,candidate,js,5,1.33,0.52,155%,0:01.19,0,0,0,0,720448,0,0,203150,81924,498,0,0,0,0,0,0,4096,0
unicode-8MiB-io-materialize,candidate,js,6,1.26,0.54,158%,0:01.13,0,0,0,0,711912,0,0,201034,82863,306,0,0,0,0,0,0,4096,0
unicode-8MiB-io-materialize,candidate,js,7,1.32,0.52,156%,0:01.17,0,0,0,0,719504,0,0,203066,85362,353,0,0,0,0,0,0,4096,0
unicode-8MiB-io-materialize,candidate,c-counters,1,0.10,0.02,98%,0:00.13,0,0,0,0,71536,0,0,19695,7,26,0,0,0,0,0,0,4096,0
unicode-64MiB-io-scan,base,c,warm,0.78,0.24,98%,0:01.04,0,0,0,0,722804,0,0,180480,7,171,0,0,0,0,0,0,4096,0
unicode-64MiB-io-scan,base,c,1,0.77,0.24,99%,0:01.03,0,0,0,0,722948,0,0,180481,7,43,0,0,0,0,0,0,4096,0
unicode-64MiB-io-scan,base,c,2,0.75,0.26,98%,0:01.02,0,0,0,0,722480,0,0,180476,7,143,0,0,0,0,0,0,4096,0
unicode-64MiB-io-scan,base,c,3,0.77,0.25,98%,0:01.04,0,0,0,0,722792,0,0,180481,7,220,0,0,0,0,0,0,4096,0
unicode-64MiB-io-scan,base,c,4,0.76,0.26,98%,0:01.05,0,0,0,0,722660,0,0,180479,7,212,0,0,0,0,0,0,4096,0
unicode-64MiB-io-scan,base,c,5,0.75,0.26,98%,0:01.02,0,0,0,0,722860,0,0,180479,7,123,0,0,0,0,0,0,4096,0
unicode-64MiB-io-scan,base,c,6,0.77,0.25,98%,0:01.04,0,0,0,0,723044,0,0,180482,7,199,0,0,0,0,0,0,4096,0
unicode-64MiB-io-scan,base,c,7,0.78,0.26,98%,0:01.06,0,0,0,0,722612,0,0,180483,7,215,0,0,0,0,0,0,4096,0
unicode-64MiB-io-scan,base,c-counters,1,1.25,0.25,99%,0:01.52,0,0,0,0,722740,0,0,180478,7,49,0,0,0,0,0,0,4096,0
unicode-64MiB-io-scan,candidate,c,warm,0.67,0.09,98%,0:00.78,0,0,0,0,231472,0,0,57572,7,166,0,0,0,0,0,0,4096,0
unicode-64MiB-io-scan,candidate,c,1,0.66,0.09,99%,0:00.77,0,0,0,0,231088,0,0,57570,7,169,0,0,0,0,0,0,4096,0
unicode-64MiB-io-scan,candidate,c,2,0.67,0.09,99%,0:00.77,0,0,0,0,231208,0,0,57570,7,104,0,0,0,0,0,0,4096,0
unicode-64MiB-io-scan,candidate,c,3,0.67,0.09,98%,0:00.77,0,0,0,0,231336,0,0,57572,7,146,0,0,0,0,0,0,4096,0
unicode-64MiB-io-scan,candidate,c,4,0.66,0.09,98%,0:00.76,0,0,0,0,231024,0,0,57573,7,168,0,0,0,0,0,0,4096,0
unicode-64MiB-io-scan,candidate,c,5,0.69,0.09,99%,0:00.79,0,0,0,0,231352,0,0,57575,7,87,0,0,0,0,0,0,4096,0
unicode-64MiB-io-scan,candidate,c,6,0.64,0.09,99%,0:00.74,0,0,0,0,231340,0,0,57571,7,26,0,0,0,0,0,0,4096,0
unicode-64MiB-io-scan,candidate,c,7,0.71,0.09,98%,0:00.82,0,0,0,0,231528,0,0,57573,7,109,0,0,0,0,0,0,4096,0
unicode-64MiB-io-scan,candidate,c-counters,1,0.75,0.10,99%,0:00.86,0,0,0,0,231080,0,0,57572,7,58,0,0,0,0,0,0,4096,0
unicode-64MiB-construct-scan,base,c,warm,1.88,0.59,99%,0:02.48,0,0,0,0,1640680,0,0,409835,3,43,0,0,0,0,0,0,4096,0
unicode-64MiB-construct-scan,base,c,1,1.88,0.56,99%,0:02.45,0,0,0,0,1640040,0,0,409831,3,83,0,0,0,0,0,0,4096,0
unicode-64MiB-construct-scan,base,c,2,1.88,0.57,99%,0:02.47,0,0,0,0,1639860,0,0,409831,3,157,0,0,0,0,0,0,4096,0
unicode-64MiB-construct-scan,base,c,3,1.88,0.56,99%,0:02.46,0,0,0,0,1640632,0,0,409834,3,87,0,0,0,0,0,0,4096,0
unicode-64MiB-construct-scan,base,c,4,1.89,0.57,98%,0:02.49,0,0,0,0,1640184,0,0,409831,3,329,0,0,0,0,0,0,4096,0
unicode-64MiB-construct-scan,base,c,5,1.90,0.55,99%,0:02.47,0,0,0,0,1640052,0,0,409833,3,207,0,0,0,0,0,0,4096,0
unicode-64MiB-construct-scan,base,c,6,1.57,0.85,98%,0:02.46,0,0,0,0,1640040,0,0,409836,3,332,0,0,0,0,0,0,4096,0
unicode-64MiB-construct-scan,base,c,7,1.88,0.55,98%,0:02.47,0,0,0,0,1640624,0,0,409830,3,250,0,0,0,0,0,0,4096,0
unicode-64MiB-construct-scan,base,c-counters,1,2.72,0.58,98%,0:03.35,0,0,0,0,1640568,0,0,409832,3,411,0,0,0,0,0,0,4096,0
unicode-64MiB-construct-scan,candidate,c,warm,0.63,0.05,99%,0:00.70,0,0,0,0,165928,0,0,41183,3,38,0,0,0,0,0,0,4096,0
unicode-64MiB-construct-scan,candidate,c,1,0.62,0.05,98%,0:00.68,0,0,0,0,165964,0,0,41187,3,105,0,0,0,0,0,0,4096,0
unicode-64MiB-construct-scan,candidate,c,2,0.63,0.05,99%,0:00.69,0,0,0,0,165996,0,0,41186,3,63,0,0,0,0,0,0,4096,0
unicode-64MiB-construct-scan,candidate,c,3,0.63,0.07,98%,0:00.72,0,0,0,0,165932,0,0,41184,3,103,0,0,0,0,0,0,4096,0
unicode-64MiB-construct-scan,candidate,c,4,0.64,0.05,98%,0:00.71,0,0,0,0,165936,0,0,41186,3,138,0,0,0,0,0,0,4096,0
unicode-64MiB-construct-scan,candidate,c,5,0.63,0.06,98%,0:00.71,0,0,0,0,166064,0,0,41183,2,79,0,0,0,0,0,0,4096,0
unicode-64MiB-construct-scan,candidate,c,6,0.62,0.05,98%,0:00.69,0,0,0,0,166120,0,0,41185,3,144,0,0,0,0,0,0,4096,0
unicode-64MiB-construct-scan,candidate,c,7,0.66,0.06,98%,0:00.73,0,0,0,0,165996,0,0,41186,3,139,0,0,0,0,0,0,4096,0
unicode-64MiB-construct-scan,candidate,c-counters,1,0.76,0.04,99%,0:00.81,0,0,0,0,165752,0,0,41183,3,93,0,0,0,0,0,0,4096,0
unicode-64MiB-io-materialize,base,c,warm,0.64,0.59,99%,0:01.25,0,0,0,0,1640112,0,0,426211,7,101,0,0,0,0,0,0,4096,0
unicode-64MiB-io-materialize,base,c,1,0.66,0.54,98%,0:01.22,0,0,0,0,1640528,0,0,426209,7,226,0,0,0,0,0,0,4096,0
unicode-64MiB-io-materialize,base,c,2,0.63,0.56,98%,0:01.22,0,0,0,0,1640612,0,0,426205,7,189,0,0,0,0,0,0,4096,0
unicode-64MiB-io-materialize,base,c,3,0.63,0.58,99%,0:01.22,0,0,0,0,1640060,0,0,426209,7,179,0,0,0,0,0,0,4096,0
unicode-64MiB-io-materialize,base,c,4,0.64,0.58,99%,0:01.23,0,0,0,0,1639776,0,0,426209,7,143,0,0,0,0,0,0,4096,0
unicode-64MiB-io-materialize,base,c,5,0.65,0.56,99%,0:01.23,0,0,0,0,1640576,0,0,426211,6,73,0,0,0,0,0,0,4096,0
unicode-64MiB-io-materialize,base,c,6,0.62,0.57,99%,0:01.20,0,0,0,0,1640196,0,0,426212,7,120,0,0,0,0,0,0,4096,0
unicode-64MiB-io-materialize,base,c,7,0.67,0.54,98%,0:01.23,0,0,0,0,1640324,0,0,426207,7,235,0,0,0,0,0,0,4096,0
unicode-64MiB-io-materialize,base,c-counters,1,1.00,0.61,98%,0:01.64,0,0,0,0,1639944,0,0,426211,7,243,0,0,0,0,0,0,4096,0
unicode-64MiB-io-materialize,candidate,c,warm,0.65,0.22,99%,0:00.88,0,0,0,0,559164,0,0,155882,7,173,0,0,0,0,0,0,4096,0
unicode-64MiB-io-materialize,candidate,c,1,0.66,0.24,98%,0:00.92,0,0,0,0,558852,0,0,155882,7,168,0,0,0,0,0,0,4096,0
unicode-64MiB-io-materialize,candidate,c,2,0.64,0.25,99%,0:00.91,0,0,0,0,558940,0,0,155883,7,135,0,0,0,0,0,0,4096,0
unicode-64MiB-io-materialize,candidate,c,3,0.66,0.25,98%,0:00.92,0,0,0,0,559028,0,0,155885,7,117,0,0,0,0,0,0,4096,0
unicode-64MiB-io-materialize,candidate,c,4,0.66,0.23,98%,0:00.91,0,0,0,0,559136,0,0,155887,8,175,0,0,0,0,0,0,4096,0
unicode-64MiB-io-materialize,candidate,c,5,0.67,0.22,98%,0:00.91,0,0,0,0,558708,0,0,155882,9,136,0,0,0,0,0,0,4096,0
unicode-64MiB-io-materialize,candidate,c,6,0.67,0.23,99%,0:00.91,0,0,0,0,558492,0,0,155881,7,144,0,0,0,0,0,0,4096,0
unicode-64MiB-io-materialize,candidate,c,7,0.65,0.22,99%,0:00.89,0,0,0,0,558724,0,0,155880,7,80,0,0,0,0,0,0,4096,0
unicode-64MiB-io-materialize,candidate,c-counters,1,0.75,0.23,98%,0:01.00,0,0,0,0,558892,0,0,155879,7,199,0,0,0,0,0,0,4096,0
retain-8MiB-view,base,c,warm,0.08,0.05,98%,0:00.13,0,0,0,0,141488,0,0,35038,7,12,0,0,0,0,0,0,4096,0
retain-8MiB-view,base,c,1,0.08,0.05,98%,0:00.13,0,0,0,0,141284,0,0,35039,6,29,0,0,0,0,0,0,4096,0
retain-8MiB-view,base,c,2,0.08,0.04,99%,0:00.13,0,0,0,0,141420,0,0,35038,7,5,0,0,0,0,0,0,4096,0
retain-8MiB-view,base,c,3,0.08,0.04,98%,0:00.13,0,0,0,0,141488,0,0,35038,7,44,0,0,0,0,0,0,4096,0
retain-8MiB-view,base,c,4,0.08,0.05,99%,0:00.13,0,0,0,0,141300,0,0,35042,7,16,0,0,0,0,0,0,4096,0
retain-8MiB-view,base,c,5,0.08,0.05,99%,0:00.13,0,0,0,0,141300,0,0,35041,7,5,0,0,0,0,0,0,4096,0
retain-8MiB-view,base,c,6,0.07,0.05,98%,0:00.13,0,0,0,0,141480,0,0,35039,8,38,0,0,0,0,0,0,4096,0
retain-8MiB-view,base,c,7,0.08,0.04,97%,0:00.13,0,0,0,0,141428,0,0,35039,7,28,0,0,0,0,0,0,4096,0
retain-8MiB-view,base,js,warm,0.01,0.02,105%,0:00.03,0,0,0,0,69884,0,0,9722,202,15,0,0,0,0,0,0,4096,0
retain-8MiB-view,base,js,1,0.02,0.01,102%,0:00.03,0,0,0,0,70200,0,0,9706,229,20,0,0,0,0,0,0,4096,0
retain-8MiB-view,base,js,2,0.02,0.01,105%,0:00.03,0,0,0,0,70012,0,0,9717,230,25,0,0,0,0,0,0,4096,0
retain-8MiB-view,base,js,3,0.02,0.01,108%,0:00.03,0,0,0,0,70140,0,0,9722,216,4,0,0,0,0,0,0,4096,0
retain-8MiB-view,base,js,4,0.02,0.01,105%,0:00.03,0,0,0,0,70124,0,0,9721,239,61,0,0,0,0,0,0,4096,0
retain-8MiB-view,base,js,5,0.02,0.01,105%,0:00.03,0,0,0,0,70248,0,0,9720,228,6,0,0,0,0,0,0,4096,0
retain-8MiB-view,base,js,6,0.02,0.01,102%,0:00.03,0,0,0,0,69996,0,0,9726,218,15,0,0,0,0,0,0,4096,0
retain-8MiB-view,base,js,7,0.01,0.02,105%,0:00.03,0,0,0,0,69844,0,0,9726,236,23,0,0,0,0,0,0,4096,0
retain-8MiB-view,base,c-counters,1,0.08,0.04,99%,0:00.13,0,0,0,0,141412,0,0,35035,7,5,0,0,0,0,0,0,4096,0
retain-8MiB-view,candidate,c,warm,0.00,0.01,96%,0:00.02,0,0,0,0,43184,0,0,10459,7,1,0,0,0,0,0,0,4096,0
retain-8MiB-view,candidate,c,1,0.01,0.01,100%,0:00.02,0,0,0,0,43000,0,0,10461,7,4,0,0,0,0,0,0,4096,0
retain-8MiB-view,candidate,c,2,0.01,0.01,96%,0:00.02,0,0,0,0,43256,0,0,10461,7,3,0,0,0,0,0,0,4096,0
retain-8MiB-view,candidate,c,3,0.00,0.01,96%,0:00.02,0,0,0,0,43056,0,0,10455,7,15,0,0,0,0,0,0,4096,0
retain-8MiB-view,candidate,c,4,0.00,0.01,100%,0:00.02,0,0,0,0,42936,0,0,10463,7,8,0,0,0,0,0,0,4096,0
retain-8MiB-view,candidate,c,5,0.00,0.01,96%,0:00.02,0,0,0,0,42872,0,0,10459,7,9,0,0,0,0,0,0,4096,0
retain-8MiB-view,candidate,c,6,0.00,0.01,100%,0:00.02,0,0,0,0,43064,0,0,10461,7,8,0,0,0,0,0,0,4096,0
retain-8MiB-view,candidate,c,7,0.00,0.01,96%,0:00.02,0,0,0,0,43120,0,0,10458,7,5,0,0,0,0,0,0,4096,0
retain-8MiB-view,candidate,js,warm,0.27,0.11,103%,0:00.38,0,0,0,0,328288,0,0,73271,414,68,0,0,0,0,0,0,4096,0
retain-8MiB-view,candidate,js,1,0.25,0.10,104%,0:00.35,0,0,0,0,328576,0,0,73262,395,59,0,0,0,0,0,0,4096,0
retain-8MiB-view,candidate,js,2,0.25,0.11,104%,0:00.36,0,0,0,0,327940,0,0,73261,412,62,0,0,0,0,0,0,4096,0
retain-8MiB-view,candidate,js,3,0.28,0.12,103%,0:00.38,0,0,0,0,328256,0,0,73258,321,130,0,0,0,0,0,0,4096,0
retain-8MiB-view,candidate,js,4,0.27,0.11,103%,0:00.37,0,0,0,0,327988,0,0,73240,403,184,0,0,0,0,0,0,4096,0
retain-8MiB-view,candidate,js,5,0.28,0.11,103%,0:00.38,0,0,0,0,328316,0,0,73267,432,63,0,0,0,0,0,0,4096,0
retain-8MiB-view,candidate,js,6,0.27,0.10,103%,0:00.36,0,0,0,0,328296,0,0,73271,374,47,0,0,0,0,0,0,4096,0
retain-8MiB-view,candidate,js,7,0.26,0.11,104%,0:00.36,0,0,0,0,328020,0,0,73256,404,61,0,0,0,0,0,0,4096,0
retain-8MiB-view,candidate,c-counters,1,0.00,0.02,96%,0:00.02,0,0,0,0,43208,0,0,10459,7,5,0,0,0,0,0,0,4096,0
retain-8MiB-copy,base,c,warm,0.08,0.05,97%,0:00.13,0,0,0,0,141408,0,0,35036,7,25,0,0,0,0,0,0,4096,0
retain-8MiB-copy,base,c,1,0.08,0.05,99%,0:00.13,0,0,0,0,141356,0,0,35037,6,16,0,0,0,0,0,0,4096,0
retain-8MiB-copy,base,c,2,0.08,0.04,98%,0:00.13,0,0,0,0,141168,0,0,35040,7,20,0,0,0,0,0,0,4096,0
retain-8MiB-copy,base,c,3,0.08,0.05,99%,0:00.13,0,0,0,0,141556,0,0,35039,7,29,0,0,0,0,0,0,4096,0
retain-8MiB-copy,base,c,4,0.08,0.05,97%,0:00.14,0,0,0,0,141288,0,0,35039,7,30,0,0,0,0,0,0,4096,0
retain-8MiB-copy,base,c,5,0.08,0.04,99%,0:00.13,0,0,0,0,141412,0,0,35040,7,11,0,0,0,0,0,0,4096,0
retain-8MiB-copy,base,c,6,0.08,0.04,99%,0:00.13,0,0,0,0,141364,0,0,35036,7,7,0,0,0,0,0,0,4096,0
retain-8MiB-copy,base,c,7,0.08,0.04,99%,0:00.13,0,0,0,0,141356,0,0,35037,7,6,0,0,0,0,0,0,4096,0
retain-8MiB-copy,base,js,warm,0.01,0.01,109%,0:00.03,0,0,0,0,70528,0,0,9852,228,12,0,0,0,0,0,0,4096,0
retain-8MiB-copy,base,js,1,0.02,0.01,108%,0:00.03,0,0,0,0,70644,0,0,9840,248,5,0,0,0,0,0,0,4096,0
retain-8MiB-copy,base,js,2,0.01,0.02,105%,0:00.03,0,0,0,0,70700,0,0,9853,249,9,0,0,0,0,0,0,4096,0
retain-8MiB-copy,base,js,3,0.01,0.02,102%,0:00.03,0,0,0,0,70572,0,0,9851,200,5,0,0,0,0,0,0,4096,0
retain-8MiB-copy,base,js,4,0.01,0.01,109%,0:00.03,0,0,0,0,70840,0,0,9850,203,18,0,0,0,0,0,0,4096,0
retain-8MiB-copy,base,js,5,0.01,0.01,105%,0:00.03,0,0,0,0,70580,0,0,9839,210,19,0,0,0,0,0,0,4096,0
retain-8MiB-copy,base,js,6,0.01,0.02,108%,0:00.03,0,0,0,0,70400,0,0,9847,244,18,0,0,0,0,0,0,4096,0
retain-8MiB-copy,base,js,7,0.02,0.02,107%,0:00.04,0,0,0,0,70708,0,0,9837,226,14,0,0,0,0,0,0,4096,0
retain-8MiB-copy,base,c-counters,1,0.07,0.05,99%,0:00.13,0,0,0,0,141284,0,0,35037,7,9,0,0,0,0,0,0,4096,0
retain-8MiB-copy,candidate,c,warm,0.01,0.01,95%,0:00.02,0,0,0,0,43064,0,0,10460,7,22,0,0,0,0,0,0,4096,0
retain-8MiB-copy,candidate,c,1,0.01,0.01,96%,0:00.02,0,0,0,0,43124,0,0,10463,7,7,0,0,0,0,0,0,4096,0
retain-8MiB-copy,candidate,c,2,0.00,0.01,96%,0:00.02,0,0,0,0,43064,0,0,10457,7,14,0,0,0,0,0,0,4096,0
retain-8MiB-copy,candidate,c,3,0.00,0.01,95%,0:00.02,0,0,0,0,42868,0,0,10458,7,7,0,0,0,0,0,0,4096,0
retain-8MiB-copy,candidate,c,4,0.00,0.01,95%,0:00.02,0,0,0,0,43120,0,0,10457,7,3,0,0,0,0,0,0,4096,0
retain-8MiB-copy,candidate,c,5,0.00,0.01,95%,0:00.02,0,0,0,0,43244,0,0,10463,7,3,0,0,0,0,0,0,4096,0
retain-8MiB-copy,candidate,c,6,0.01,0.01,96%,0:00.02,0,0,0,0,43116,0,0,10459,7,3,0,0,0,0,0,0,4096,0
retain-8MiB-copy,candidate,c,7,0.00,0.01,95%,0:00.02,0,0,0,0,43108,0,0,10459,7,6,0,0,0,0,0,0,4096,0
retain-8MiB-copy,candidate,js,warm,0.25,0.10,104%,0:00.34,0,0,0,0,328292,0,0,73268,419,19,0,0,0,0,0,0,4096,0
retain-8MiB-copy,candidate,js,1,0.25,0.12,103%,0:00.35,0,0,0,0,328048,0,0,73258,342,29,0,0,0,0,0,0,4096,0
retain-8MiB-copy,candidate,js,2,0.27,0.09,104%,0:00.36,0,0,0,0,328120,0,0,73264,342,37,0,0,0,0,0,0,4096,0
retain-8MiB-copy,candidate,js,3,0.27,0.09,103%,0:00.35,0,0,0,0,328324,0,0,73274,363,38,0,0,0,0,0,0,4096,0
retain-8MiB-copy,candidate,js,4,0.26,0.10,103%,0:00.35,0,0,0,0,327984,0,0,73261,383,34,0,0,0,0,0,0,4096,0
retain-8MiB-copy,candidate,js,5,0.27,0.11,103%,0:00.38,0,0,0,0,328516,0,0,73261,378,12,0,0,0,0,0,0,4096,0
retain-8MiB-copy,candidate,js,6,0.25,0.11,103%,0:00.35,0,0,0,0,328388,0,0,73264,340,88,0,0,0,0,0,0,4096,0
retain-8MiB-copy,candidate,js,7,0.27,0.09,103%,0:00.36,0,0,0,0,327932,0,0,73261,373,82,0,0,0,0,0,0,4096,0
retain-8MiB-copy,candidate,c-counters,1,0.00,0.01,96%,0:00.02,0,0,0,0,43124,0,0,10462,7,5,0,0,0,0,0,0,4096,0
search-32768-512,base,c,warm,0.10,0.00,99%,0:00.11,0,0,0,0,3444,0,0,539,3,12,0,0,0,0,0,0,4096,0
search-32768-512,base,c,1,0.10,0.00,99%,0:00.10,0,0,0,0,3372,0,0,536,2,7,0,0,0,0,0,0,4096,0
search-32768-512,base,c,2,0.10,0.00,97%,0:00.10,0,0,0,0,3564,0,0,537,3,22,0,0,0,0,0,0,4096,0
search-32768-512,base,c,3,0.11,0.00,99%,0:00.11,0,0,0,0,3320,0,0,535,3,25,0,0,0,0,0,0,4096,0
search-32768-512,base,c,4,0.10,0.00,99%,0:00.10,0,0,0,0,3508,0,0,539,2,24,0,0,0,0,0,0,4096,0
search-32768-512,base,c,5,0.10,0.00,98%,0:00.10,0,0,0,0,3440,0,0,534,3,31,0,0,0,0,0,0,4096,0
search-32768-512,base,c,6,0.11,0.00,100%,0:00.11,0,0,0,0,3572,0,0,537,3,21,0,0,0,0,0,0,4096,0
search-32768-512,base,c,7,0.10,0.00,99%,0:00.11,0,0,0,0,3508,0,0,540,3,12,0,0,0,0,0,0,4096,0
search-32768-512,base,js,warm,0.00,0.01,104%,0:00.02,0,0,0,0,51728,0,0,4989,108,3,0,0,0,0,0,0,4096,1
search-32768-512,base,js,1,0.01,0.01,115%,0:00.02,0,0,0,0,51720,0,0,4985,111,5,0,0,0,0,0,0,4096,1
search-32768-512,base,js,2,0.01,0.01,115%,0:00.02,0,0,0,0,51704,0,0,4999,124,4,0,0,0,0,0,0,4096,1
search-32768-512,base,js,3,0.01,0.01,109%,0:00.02,0,0,0,0,51316,0,0,4984,129,11,0,0,0,0,0,0,4096,1
search-32768-512,base,js,4,0.01,0.00,115%,0:00.01,0,0,0,0,51852,0,0,4995,121,11,0,0,0,0,0,0,4096,1
search-32768-512,base,js,5,0.01,0.01,109%,0:00.02,0,0,0,0,51908,0,0,4984,114,4,0,0,0,0,0,0,4096,1
search-32768-512,base,js,6,0.01,0.01,119%,0:00.02,0,0,0,0,51524,0,0,4982,115,11,0,0,0,0,0,0,4096,1
search-32768-512,base,js,7,0.01,0.00,110%,0:00.02,0,0,0,0,51400,0,0,4995,121,2,0,0,0,0,0,0,4096,1
search-32768-512,base,c-counters,1,0.14,0.00,99%,0:00.14,0,0,0,0,3376,0,0,535,3,11,0,0,0,0,0,0,4096,0
search-32768-512,candidate,c,warm,0.00,0.00,0%,0:00.00,0,0,0,0,2348,0,0,247,3,0,0,0,0,0,0,0,4096,0
search-32768-512,candidate,c,1,0.00,0.00,100%,0:00.00,0,0,0,0,2172,0,0,249,3,1,0,0,0,0,0,0,4096,0
search-32768-512,candidate,c,2,0.00,0.00,100%,0:00.00,0,0,0,0,2400,0,0,250,3,0,0,0,0,0,0,0,4096,0
search-32768-512,candidate,c,3,0.00,0.00,0%,0:00.00,0,0,0,0,2408,0,0,251,3,0,0,0,0,0,0,0,4096,0
search-32768-512,candidate,c,4,0.00,0.00,0%,0:00.00,0,0,0,0,2348,0,0,250,3,0,0,0,0,0,0,0,4096,0
search-32768-512,candidate,c,5,0.00,0.00,100%,0:00.00,0,0,0,0,2352,0,0,249,3,0,0,0,0,0,0,0,4096,0
search-32768-512,candidate,c,6,0.00,0.00,100%,0:00.00,0,0,0,0,2356,0,0,250,3,1,0,0,0,0,0,0,4096,0
search-32768-512,candidate,c,7,0.00,0.00,100%,0:00.00,0,0,0,0,2280,0,0,250,3,0,0,0,0,0,0,0,4096,0
search-32768-512,candidate,js,warm,0.01,0.00,112%,0:00.01,0,0,0,0,41804,0,0,3251,125,3,0,0,0,0,0,0,4096,0
search-32768-512,candidate,js,1,0.01,0.00,106%,0:00.01,0,0,0,0,42120,0,0,3247,114,3,0,0,0,0,0,0,4096,0
search-32768-512,candidate,js,2,0.01,0.00,100%,0:00.01,0,0,0,0,42180,0,0,3250,103,4,0,0,0,0,0,0,4096,0
search-32768-512,candidate,js,3,0.00,0.00,106%,0:00.01,0,0,0,0,41984,0,0,3243,122,2,0,0,0,0,0,0,4096,0
search-32768-512,candidate,js,4,0.00,0.00,113%,0:00.01,0,0,0,0,42044,0,0,3249,113,5,0,0,0,0,0,0,4096,0
search-32768-512,candidate,js,5,0.00,0.00,106%,0:00.01,0,0,0,0,41992,0,0,3239,99,0,0,0,0,0,0,0,4096,0
search-32768-512,candidate,js,6,0.00,0.01,100%,0:00.01,0,0,0,0,42052,0,0,3251,127,5,0,0,0,0,0,0,4096,0
search-32768-512,candidate,js,7,0.01,0.00,106%,0:00.01,0,0,0,0,42120,0,0,3240,107,1,0,0,0,0,0,0,4096,0
search-32768-512,candidate,c-counters,1,0.00,0.00,0%,0:00.00,0,0,0,0,2420,0,0,253,3,0,0,0,0,0,0,0,4096,0
search-65536-1024,base,c,warm,0.43,0.00,99%,0:00.43,0,0,0,0,4856,0,0,858,3,18,0,0,0,0,0,0,4096,0
search-65536-1024,base,c,1,0.42,0.00,99%,0:00.43,0,0,0,0,4432,0,0,856,3,44,0,0,0,0,0,0,4096,0
search-65536-1024,base,c,2,0.42,0.00,98%,0:00.43,0,0,0,0,4648,0,0,860,3,58,0,0,0,0,0,0,4096,0
search-65536-1024,base,c,3,0.44,0.00,99%,0:00.45,0,0,0,0,4712,0,0,859,3,131,0,0,0,0,0,0,4096,0
search-65536-1024,base,c,4,0.42,0.00,99%,0:00.42,0,0,0,0,4792,0,0,858,3,74,0,0,0,0,0,0,4096,0
search-65536-1024,base,c,5,0.41,0.00,99%,0:00.42,0,0,0,0,4708,0,0,858,3,33,0,0,0,0,0,0,4096,0
search-65536-1024,base,c,6,0.41,0.00,99%,0:00.41,0,0,0,0,4652,0,0,860,3,21,0,0,0,0,0,0,4096,0
search-65536-1024,base,c,7,0.42,0.00,99%,0:00.42,0,0,0,0,4836,0,0,861,3,57,0,0,0,0,0,0,4096,0
search-65536-1024,base,js,warm,0.01,0.01,104%,0:00.02,0,0,0,0,51848,0,0,5001,106,5,0,0,0,0,0,0,4096,1
search-65536-1024,base,js,1,0.01,0.00,110%,0:00.02,0,0,0,0,51520,0,0,4987,120,8,0,0,0,0,0,0,4096,1
search-65536-1024,base,js,2,0.01,0.01,110%,0:00.02,0,0,0,0,51788,0,0,5006,115,8,0,0,0,0,0,0,4096,1
search-65536-1024,base,js,3,0.01,0.00,100%,0:00.02,0,0,0,0,51136,0,0,4991,136,8,0,0,0,0,0,0,4096,1
search-65536-1024,base,js,4,0.00,0.01,114%,0:00.02,0,0,0,0,51516,0,0,4999,127,6,0,0,0,0,0,0,4096,1
search-65536-1024,base,js,5,0.01,0.01,108%,0:00.02,0,0,0,0,51648,0,0,4993,114,3,0,0,0,0,0,0,4096,1
search-65536-1024,base,js,6,0.01,0.01,108%,0:00.02,0,0,0,0,51592,0,0,4993,119,15,0,0,0,0,0,0,4096,1
search-65536-1024,base,js,7,0.01,0.01,109%,0:00.02,0,0,0,0,51852,0,0,4984,109,5,0,0,0,0,0,0,4096,1
search-65536-1024,base,c-counters,1,0.55,0.00,99%,0:00.56,0,0,0,0,4792,0,0,857,3,69,0,0,0,0,0,0,4096,0
search-65536-1024,candidate,c,warm,0.00,0.00,0%,0:00.00,0,0,0,0,2528,0,0,283,3,0,0,0,0,0,0,0,4096,0
search-65536-1024,candidate,c,1,0.00,0.00,100%,0:00.00,0,0,0,0,2484,0,0,283,3,2,0,0,0,0,0,0,4096,0
search-65536-1024,candidate,c,2,0.00,0.00,100%,0:00.00,0,0,0,0,2484,0,0,279,3,0,0,0,0,0,0,0,4096,0
search-65536-1024,candidate,c,3,0.00,0.00,0%,0:00.00,0,0,0,0,2408,0,0,282,3,0,0,0,0,0,0,0,4096,0
search-65536-1024,candidate,c,4,0.00,0.00,100%,0:00.00,0,0,0,0,2416,0,0,278,3,6,0,0,0,0,0,0,4096,0
search-65536-1024,candidate,c,5,0.00,0.00,0%,0:00.00,0,0,0,0,2352,0,0,277,3,0,0,0,0,0,0,0,4096,0
search-65536-1024,candidate,c,6,0.00,0.00,100%,0:00.00,0,0,0,0,2424,0,0,283,3,0,0,0,0,0,0,0,4096,0
search-65536-1024,candidate,c,7,0.00,0.00,0%,0:00.00,0,0,0,0,2488,0,0,285,3,0,0,0,0,0,0,0,4096,0
search-65536-1024,candidate,js,warm,0.00,0.00,106%,0:00.01,0,0,0,0,41848,0,0,3271,111,18,0,0,0,0,0,0,4096,0
search-65536-1024,candidate,js,1,0.00,0.00,100%,0:00.01,0,0,0,0,42096,0,0,3266,118,2,0,0,0,0,0,0,4096,0
search-65536-1024,candidate,js,2,0.01,0.00,105%,0:00.01,0,0,0,0,42048,0,0,3267,115,5,0,0,0,0,0,0,4096,0
search-65536-1024,candidate,js,3,0.00,0.00,106%,0:00.01,0,0,0,0,42184,0,0,3279,113,0,0,0,0,0,0,0,4096,0
search-65536-1024,candidate,js,4,0.01,0.00,100%,0:00.01,0,0,0,0,42048,0,0,3270,108,6,0,0,0,0,0,0,4096,0
search-65536-1024,candidate,js,5,0.01,0.00,106%,0:00.01,0,0,0,0,41992,0,0,3264,127,9,0,0,0,0,0,0,4096,0
search-65536-1024,candidate,js,6,0.01,0.00,106%,0:00.01,0,0,0,0,42308,0,0,3271,105,2,0,0,0,0,0,0,4096,0
search-65536-1024,candidate,js,7,0.00,0.00,100%,0:00.01,0,0,0,0,42248,0,0,3271,106,4,0,0,0,0,0,0,4096,0
search-65536-1024,candidate,c-counters,1,0.00,0.00,100%,0:00.00,0,0,0,0,2344,0,0,282,3,0,0,0,0,0,0,0,4096,0
search-131072-2048,base,c,warm,1.65,0.00,99%,0:01.66,0,0,0,0,7396,0,0,1504,3,49,0,0,0,0,0,0,4096,0
search-131072-2048,base,c,1,1.63,0.00,99%,0:01.64,0,0,0,0,7396,0,0,1505,3,18,0,0,0,0,0,0,4096,0
search-131072-2048,base,c,2,1.65,0.00,99%,0:01.67,0,0,0,0,7216,0,0,1506,3,178,0,0,0,0,0,0,4096,0
search-131072-2048,base,c,3,1.65,0.00,99%,0:01.67,0,0,0,0,7528,0,0,1516,9,162,0,0,0,0,0,0,4096,0
search-131072-2048,base,c,4,1.65,0.00,99%,0:01.67,0,0,0,0,7476,0,0,1506,3,29,0,0,0,0,0,0,4096,0
search-131072-2048,base,c,5,1.66,0.00,99%,0:01.68,0,0,0,0,7404,0,0,1506,3,112,0,0,0,0,0,0,4096,0
search-131072-2048,base,c,6,1.66,0.00,98%,0:01.69,0,0,0,0,7288,0,0,1503,3,350,0,0,0,0,0,0,4096,0
search-131072-2048,base,c,7,1.65,0.00,98%,0:01.68,0,0,0,0,7472,0,0,1507,3,318,0,0,0,0,0,0,4096,0
search-131072-2048,base,js,warm,0.01,0.01,108%,0:00.02,0,0,0,0,51720,0,0,5001,142,141,0,0,0,0,0,0,4096,1
search-131072-2048,base,js,1,0.01,0.01,108%,0:00.02,0,0,0,0,51904,0,0,4997,136,0,0,0,0,0,0,0,4096,1
search-131072-2048,base,js,2,0.01,0.01,109%,0:00.02,0,0,0,0,51508,0,0,5003,125,3,0,0,0,0,0,0,4096,1
search-131072-2048,base,js,3,0.00,0.01,109%,0:00.02,0,0,0,0,52032,0,0,4996,111,4,0,0,0,0,0,0,4096,1
search-131072-2048,base,js,4,0.01,0.01,109%,0:00.02,0,0,0,0,51644,0,0,5001,104,17,0,0,0,0,0,0,4096,1
search-131072-2048,base,js,5,0.01,0.01,109%,0:00.02,0,0,0,0,51900,0,0,5002,111,2,0,0,0,0,0,0,4096,1
search-131072-2048,base,js,6,0.01,0.01,113%,0:00.02,0,0,0,0,52036,0,0,4998,144,3,0,0,0,0,0,0,4096,1
search-131072-2048,base,js,7,0.01,0.01,108%,0:00.02,0,0,0,0,51908,0,0,4997,117,10,0,0,0,0,0,0,4096,1
search-131072-2048,base,c-counters,1,2.25,0.00,98%,0:02.29,0,0,0,0,7396,0,0,1508,3,426,0,0,0,0,0,0,4096,0
search-131072-2048,candidate,c,warm,0.00,0.00,50%,0:00.00,0,0,0,0,2860,0,0,347,3,0,0,0,0,0,0,0,4096,0
search-131072-2048,candidate,c,1,0.00,0.00,100%,0:00.00,0,0,0,0,2804,0,0,348,3,0,0,0,0,0,0,0,4096,0
search-131072-2048,candidate,c,2,0.00,0.00,100%,0:00.00,0,0,0,0,2660,0,0,349,3,2,0,0,0,0,0,0,4096,0
search-131072-2048,candidate,c,3,0.00,0.00,50%,0:00.00,0,0,0,0,2512,0,0,344,3,2,0,0,0,0,0,0,4096,0
search-131072-2048,candidate,c,4,0.00,0.00,100%,0:00.00,0,0,0,0,2660,0,0,351,3,0,0,0,0,0,0,0,4096,0
search-131072-2048,candidate,c,5,0.00,0.00,100%,0:00.00,0,0,0,0,2660,0,0,350,3,0,0,0,0,0,0,0,4096,0
search-131072-2048,candidate,c,6,0.00,0.00,100%,0:00.00,0,0,0,0,2608,0,0,347,3,0,0,0,0,0,0,0,4096,0
search-131072-2048,candidate,c,7,0.00,0.00,100%,0:00.00,0,0,0,0,2744,0,0,348,3,0,0,0,0,0,0,0,4096,0
search-131072-2048,candidate,js,warm,0.00,0.01,106%,0:00.01,0,0,0,0,42300,0,0,3313,103,2,0,0,0,0,0,0,4096,0
search-131072-2048,candidate,js,1,0.01,0.00,106%,0:00.01,0,0,0,0,42380,0,0,3304,119,4,0,0,0,0,0,0,4096,0
search-131072-2048,candidate,js,2,0.01,0.00,105%,0:00.01,0,0,0,0,42304,0,0,3312,116,8,0,0,0,0,0,0,4096,0
search-131072-2048,candidate,js,3,0.00,0.00,112%,0:00.01,0,0,0,0,42508,0,0,3300,109,1,0,0,0,0,0,0,4096,0
search-131072-2048,candidate,js,4,0.01,0.00,106%,0:00.01,0,0,0,0,42160,0,0,3312,114,2,0,0,0,0,0,0,4096,0
search-131072-2048,candidate,js,5,0.01,0.00,106%,0:00.01,0,0,0,0,42492,0,0,3317,129,10,0,0,0,0,0,0,4096,0
search-131072-2048,candidate,js,6,0.01,0.00,112%,0:00.01,0,0,0,0,42304,0,0,3315,114,2,0,0,0,0,0,0,4096,0
search-131072-2048,candidate,js,7,0.00,0.00,106%,0:00.01,0,0,0,0,42120,0,0,3297,122,4,0,0,0,0,0,0,4096,0
search-131072-2048,candidate,c-counters,1,0.00,0.00,100%,0:00.00,0,0,0,0,2808,0,0,349,3,0,0,0,0,0,0,0,4096,0
build-concat-1024,base,c,warm,0.00,0.00,0%,0:00.00,0,0,0,0,2276,0,0,229,3,0,0,0,0,0,0,0,4096,0
build-concat-1024,base,c,1,0.00,0.00,0%,0:00.00,0,0,0,0,2424,0,0,228,3,0,0,0,0,0,0,0,4096,0
build-concat-1024,base,c,2,0.00,0.00,0%,0:00.00,0,0,0,0,2412,0,0,231,3,0,0,0,0,0,0,0,4096,0
build-concat-1024,base,c,3,0.00,0.00,0%,0:00.00,0,0,0,0,2304,0,0,231,3,0,0,0,0,0,0,0,4096,0
build-concat-1024,base,c,4,0.00,0.00,0%,0:00.00,0,0,0,0,2420,0,0,232,3,0,0,0,0,0,0,0,4096,0
build-concat-1024,base,c,5,0.00,0.00,0%,0:00.00,0,0,0,0,2224,0,0,228,3,0,0,0,0,0,0,0,4096,0
build-concat-1024,base,c,6,0.00,0.00,100%,0:00.00,0,0,0,0,2168,0,0,227,3,1,0,0,0,0,0,0,4096,0
build-concat-1024,base,c,7,0.00,0.00,0%,0:00.00,0,0,0,0,2272,0,0,228,3,0,0,0,0,0,0,0,4096,0
build-concat-1024,base,js,warm,0.01,0.00,116%,0:00.01,0,0,0,0,46856,0,0,3717,116,7,0,0,0,0,0,0,4096,0
build-concat-1024,base,js,1,0.01,0.01,113%,0:00.02,0,0,0,0,46976,0,0,3812,134,5,0,0,0,0,0,0,4096,0
build-concat-1024,base,js,2,0.01,0.00,111%,0:00.01,0,0,0,0,47036,0,0,3821,150,15,0,0,0,0,0,0,4096,0
build-concat-1024,base,js,3,0.00,0.01,115%,0:00.02,0,0,0,0,47052,0,0,3760,117,5,0,0,0,0,0,0,4096,0
build-concat-1024,base,js,4,0.01,0.01,111%,0:00.01,0,0,0,0,46844,0,0,3818,133,10,0,0,0,0,0,0,4096,0
build-concat-1024,base,js,5,0.01,0.00,111%,0:00.01,0,0,0,0,46592,0,0,3726,127,13,0,0,0,0,0,0,4096,0
build-concat-1024,base,js,6,0.01,0.00,111%,0:00.01,0,0,0,0,46924,0,0,3851,125,2,0,0,0,0,0,0,4096,0
build-concat-1024,base,js,7,0.00,0.01,117%,0:00.01,0,0,0,0,46980,0,0,3862,126,17,0,0,0,0,0,0,4096,0
build-concat-1024,base,c-counters,1,0.00,0.00,100%,0:00.00,0,0,0,0,2412,0,0,229,3,1,0,0,0,0,0,0,4096,0
build-concat-1024,candidate,c,warm,0.00,0.00,100%,0:00.00,0,0,0,0,2344,0,0,269,3,1,0,0,0,0,0,0,4096,0
build-concat-1024,candidate,c,1,0.00,0.00,0%,0:00.00,0,0,0,0,2296,0,0,267,3,0,0,0,0,0,0,0,4096,0
build-concat-1024,candidate,c,2,0.00,0.00,100%,0:00.00,0,0,0,0,2296,0,0,268,3,0,0,0,0,0,0,0,4096,0
build-concat-1024,candidate,c,3,0.00,0.00,100%,0:00.00,0,0,0,0,2540,0,0,270,3,1,0,0,0,0,0,0,4096,0
build-concat-1024,candidate,c,4,0.00,0.00,100%,0:00.00,0,0,0,0,2352,0,0,267,3,0,0,0,0,0,0,0,4096,0
build-concat-1024,candidate,c,5,0.00,0.00,100%,0:00.00,0,0,0,0,2480,0,0,273,3,2,0,0,0,0,0,0,4096,0
build-concat-1024,candidate,c,6,0.00,0.00,0%,0:00.00,0,0,0,0,2548,0,0,269,3,0,0,0,0,0,0,0,4096,0
build-concat-1024,candidate,c,7,0.00,0.00,100%,0:00.00,0,0,0,0,2548,0,0,271,3,0,0,0,0,0,0,0,4096,0
build-concat-1024,candidate,js,warm,0.00,0.01,116%,0:00.01,0,0,0,0,47624,0,0,3947,142,5,0,0,0,0,0,0,4096,0
build-concat-1024,candidate,js,1,0.01,0.00,117%,0:00.01,0,0,0,0,47240,0,0,3944,143,8,0,0,0,0,0,0,4096,0
build-concat-1024,candidate,js,2,0.01,0.01,115%,0:00.02,0,0,0,0,47480,0,0,3956,123,3,0,0,0,0,0,0,4096,0
build-concat-1024,candidate,js,3,0.01,0.00,115%,0:00.01,0,0,0,0,47428,0,0,3923,134,5,0,0,0,0,0,0,4096,0
build-concat-1024,candidate,js,4,0.01,0.01,117%,0:00.01,0,0,0,0,47428,0,0,3948,146,1,0,0,0,0,0,0,4096,0
build-concat-1024,candidate,js,5,0.00,0.01,123%,0:00.01,0,0,0,0,47424,0,0,3950,135,3,0,0,0,0,0,0,4096,0
build-concat-1024,candidate,js,6,0.01,0.01,115%,0:00.01,0,0,0,0,47052,0,0,3920,126,3,0,0,0,0,0,0,4096,0
build-concat-1024,candidate,js,7,0.00,0.01,115%,0:00.01,0,0,0,0,47424,0,0,3938,127,5,0,0,0,0,0,0,4096,0
build-concat-1024,candidate,c-counters,1,0.00,0.00,0%,0:00.00,0,0,0,0,2344,0,0,267,3,0,0,0,0,0,0,0,4096,0
build-concat-4096,base,c,warm,0.00,0.00,100%,0:00.00,0,0,0,0,2604,0,0,305,3,0,0,0,0,0,0,0,4096,0
build-concat-4096,base,c,1,0.00,0.00,0%,0:00.00,0,0,0,0,2552,0,0,304,3,0,0,0,0,0,0,0,4096,0
build-concat-4096,base,c,2,0.00,0.00,0%,0:00.00,0,0,0,0,2676,0,0,307,3,0,0,0,0,0,0,0,4096,0
build-concat-4096,base,c,3,0.00,0.00,0%,0:00.00,0,0,0,0,2536,0,0,306,3,1,0,0,0,0,0,0,4096,0
build-concat-4096,base,c,4,0.00,0.00,0%,0:00.00,0,0,0,0,2496,0,0,302,3,1,0,0,0,0,0,0,4096,0
build-concat-4096,base,c,5,0.00,0.00,100%,0:00.00,0,0,0,0,2372,0,0,301,3,1,0,0,0,0,0,0,4096,0
build-concat-4096,base,c,6,0.00,0.00,0%,0:00.00,0,0,0,0,2612,0,0,304,3,0,0,0,0,0,0,0,4096,0
build-concat-4096,base,c,7,0.00,0.00,100%,0:00.00,0,0,0,0,2676,0,0,310,3,2,0,0,0,0,0,0,4096,0
build-concat-4096,base,js,warm,0.01,0.01,131%,0:00.01,0,0,0,0,53196,0,0,4869,130,5,0,0,0,0,0,0,4096,0
build-concat-4096,base,js,1,0.01,0.00,121%,0:00.01,0,0,0,0,53512,0,0,4842,125,5,0,0,0,0,0,0,4096,0
build-concat-4096,base,js,2,0.01,0.01,113%,0:00.02,0,0,0,0,52748,0,0,4713,129,2,0,0,0,0,0,0,4096,0
build-concat-4096,base,js,3,0.01,0.01,120%,0:00.02,0,0,0,0,53316,0,0,4814,115,12,0,0,0,0,0,0,4096,0
build-concat-4096,base,js,4,0.01,0.01,118%,0:00.02,0,0,0,0,53244,0,0,4820,144,3,0,0,0,0,0,0,4096,0
build-concat-4096,base,js,5,0.01,0.01,119%,0:00.02,0,0,0,0,53240,0,0,4820,138,2,0,0,0,0,0,0,4096,0
build-concat-4096,base,js,6,0.01,0.01,125%,0:00.02,0,0,0,0,53196,0,0,4809,122,5,0,0,0,0,0,0,4096,0
build-concat-4096,base,js,7,0.01,0.01,107%,0:00.02,0,0,0,0,53256,0,0,4833,134,9,0,0,0,0,0,0,4096,0
build-concat-4096,base,c-counters,1,0.00,0.00,100%,0:00.00,0,0,0,0,2412,0,0,302,3,1,0,0,0,0,0,0,4096,0
build-concat-4096,candidate,c,warm,0.00,0.00,0%,0:00.00,0,0,0,0,2472,0,0,305,3,0,0,0,0,0,0,0,4096,0
build-concat-4096,candidate,c,1,0.00,0.00,0%,0:00.00,0,0,0,0,2472,0,0,306,3,1,0,0,0,0,0,0,4096,0
build-concat-4096,candidate,c,2,0.00,0.00,100%,0:00.00,0,0,0,0,2612,0,0,313,3,0,0,0,0,0,0,0,4096,0
build-concat-4096,candidate,c,3,0.00,0.00,0%,0:00.00,0,0,0,0,2472,0,0,308,3,0,0,0,0,0,0,0,4096,0
build-concat-4096,candidate,c,4,0.00,0.00,0%,0:00.00,0,0,0,0,2676,0,0,311,3,1,0,0,0,0,0,0,4096,0
build-concat-4096,candidate,c,5,0.00,0.00,100%,0:00.00,0,0,0,0,2552,0,0,306,3,0,0,0,0,0,0,0,4096,0
build-concat-4096,candidate,c,6,0.00,0.00,0%,0:00.00,0,0,0,0,2676,0,0,308,3,1,0,0,0,0,0,0,4096,0
build-concat-4096,candidate,c,7,0.00,0.00,0%,0:00.00,0,0,0,0,2532,0,0,308,3,1,0,0,0,0,0,0,4096,0
build-concat-4096,candidate,js,warm,0.01,0.01,116%,0:00.02,0,0,0,0,53516,0,0,4903,123,13,0,0,0,0,0,0,4096,0
build-concat-4096,candidate,js,1,0.01,0.01,111%,0:00.02,0,0,0,0,53444,0,0,4882,133,55,0,0,0,0,0,0,4096,0
build-concat-4096,candidate,js,2,0.01,0.01,107%,0:00.02,0,0,0,0,53700,0,0,4941,146,29,0,0,0,0,0,0,4096,0
build-concat-4096,candidate,js,3,0.01,0.00,120%,0:00.02,0,0,0,0,53400,0,0,4907,124,24,0,0,0,0,0,0,4096,0
build-concat-4096,candidate,js,4,0.01,0.01,122%,0:00.02,0,0,0,0,53572,0,0,4858,152,5,0,0,0,0,0,0,4096,0
build-concat-4096,candidate,js,5,0.01,0.00,119%,0:00.02,0,0,0,0,53624,0,0,4937,129,8,0,0,0,0,0,0,4096,0
build-concat-4096,candidate,js,6,0.01,0.00,118%,0:00.02,0,0,0,0,53512,0,0,4867,138,3,0,0,0,0,0,0,4096,0
build-concat-4096,candidate,js,7,0.01,0.01,120%,0:00.02,0,0,0,0,53248,0,0,4896,141,16,0,0,0,0,0,0,4096,0
build-concat-4096,candidate,c-counters,1,0.00,0.00,0%,0:00.00,0,0,0,0,2552,0,0,307,3,0,0,0,0,0,0,0,4096,0
build-join-1024,base,c,warm,0.00,0.00,100%,0:00.00,0,0,0,0,2280,0,0,229,3,0,0,0,0,0,0,0,4096,0
build-join-1024,base,c,1,0.00,0.00,100%,0:00.00,0,0,0,0,2348,0,0,227,3,0,0,0,0,0,0,0,4096,0
build-join-1024,base,c,2,0.00,0.00,100%,0:00.00,0,0,0,0,2352,0,0,231,3,1,0,0,0,0,0,0,4096,0
build-join-1024,base,c,3,0.00,0.00,0%,0:00.00,0,0,0,0,2224,0,0,226,3,0,0,0,0,0,0,0,4096,0
build-join-1024,base,c,4,0.00,0.00,0%,0:00.00,0,0,0,0,2360,0,0,232,3,0,0,0,0,0,0,0,4096,0
build-join-1024,base,c,5,0.00,0.00,100%,0:00.00,0,0,0,0,2280,0,0,228,3,10,0,0,0,0,0,0,4096,0
build-join-1024,base,c,6,0.00,0.00,0%,0:00.00,0,0,0,0,2400,0,0,231,3,1,0,0,0,0,0,0,4096,0
build-join-1024,base,c,7,0.00,0.00,0%,0:00.00,0,0,0,0,2420,0,0,230,3,1,0,0,0,0,0,0,4096,0
build-join-1024,base,js,warm,0.01,0.01,109%,0:00.02,0,0,0,0,47496,0,0,3907,117,7,0,0,0,0,0,0,4096,0
build-join-1024,base,js,1,0.01,0.00,111%,0:00.01,0,0,0,0,47240,0,0,3821,116,14,0,0,0,0,0,0,4096,0
build-join-1024,base,js,2,0.00,0.01,111%,0:00.01,0,0,0,0,47244,0,0,3835,106,3,0,0,0,0,0,0,4096,0
build-join-1024,base,js,3,0.01,0.00,111%,0:00.01,0,0,0,0,47420,0,0,3936,132,4,0,0,0,0,0,0,4096,0
build-join-1024,base,js,4,0.00,0.01,117%,0:00.01,0,0,0,0,47556,0,0,3920,125,12,0,0,0,0,0,0,4096,0
build-join-1024,base,js,5,0.01,0.00,105%,0:00.01,0,0,0,0,47204,0,0,3843,126,9,0,0,0,0,0,0,4096,0
build-join-1024,base,js,6,0.01,0.00,109%,0:00.02,0,0,0,0,47736,0,0,3940,120,4,0,0,0,0,0,0,4096,0
build-join-1024,base,js,7,0.01,0.01,110%,0:00.02,0,0,0,0,47112,0,0,3824,119,12,0,0,0,0,0,0,4096,0
build-join-1024,base,c-counters,1,0.00,0.00,0%,0:00.00,0,0,0,0,2172,0,0,227,3,0,0,0,0,0,0,0,4096,0
build-join-1024,candidate,c,warm,0.00,0.00,0%,0:00.00,0,0,0,0,2408,0,0,269,3,1,0,0,0,0,0,0,4096,0
build-join-1024,candidate,c,1,0.00,0.00,0%,0:00.00,0,0,0,0,2404,0,0,267,3,10,0,0,0,0,0,0,4096,0
build-join-1024,candidate,c,2,0.00,0.00,100%,0:00.00,0,0,0,0,2552,0,0,273,3,0,0,0,0,0,0,0,4096,0
build-join-1024,candidate,c,3,0.00,0.00,0%,0:00.00,0,0,0,0,2276,0,0,271,3,1,0,0,0,0,0,0,4096,0
build-join-1024,candidate,c,4,0.00,0.00,0%,0:00.00,0,0,0,0,2408,0,0,268,3,3,0,0,0,0,0,0,4096,0
build-join-1024,candidate,c,5,0.00,0.00,100%,0:00.00,0,0,0,0,2352,0,0,264,3,0,0,0,0,0,0,0,4096,0
build-join-1024,candidate,c,6,0.00,0.00,100%,0:00.00,0,0,0,0,2476,0,0,270,3,0,0,0,0,0,0,0,4096,0
build-join-1024,candidate,c,7,0.00,0.00,0%,0:00.00,0,0,0,0,2480,0,0,272,3,2,0,0,0,0,0,0,4096,0
build-join-1024,candidate,js,warm,0.01,0.00,110%,0:00.02,0,0,0,0,47808,0,0,4017,112,5,0,0,0,0,0,0,4096,0
build-join-1024,candidate,js,1,0.00,0.01,111%,0:00.01,0,0,0,0,47548,0,0,4009,119,36,0,0,0,0,0,0,4096,0
build-join-1024,candidate,js,2,0.01,0.01,115%,0:00.02,0,0,0,0,47948,0,0,4011,126,6,0,0,0,0,0,0,4096,0
build-join-1024,candidate,js,3,0.01,0.00,115%,0:00.01,0,0,0,0,47676,0,0,4040,131,9,0,0,0,0,0,0,4096,0
build-join-1024,candidate,js,4,0.01,0.00,111%,0:00.01,0,0,0,0,47880,0,0,4005,135,2,0,0,0,0,0,0,4096,0
build-join-1024,candidate,js,5,0.01,0.00,117%,0:00.01,0,0,0,0,47872,0,0,3996,132,0,0,0,0,0,0,0,4096,0
build-join-1024,candidate,js,6,0.00,0.01,123%,0:00.01,0,0,0,0,47740,0,0,4010,111,7,0,0,0,0,0,0,4096,0
build-join-1024,candidate,js,7,0.01,0.01,116%,0:00.01,0,0,0,0,48008,0,0,4008,123,12,0,0,0,0,0,0,4096,0
build-join-1024,candidate,c-counters,1,0.00,0.00,0%,0:00.00,0,0,0,0,2344,0,0,268,3,0,0,0,0,0,0,0,4096,0
build-join-4096,base,c,warm,0.00,0.00,0%,0:00.00,0,0,0,0,2660,0,0,319,3,0,0,0,0,0,0,0,4096,0
build-join-4096,base,c,1,0.00,0.00,0%,0:00.00,0,0,0,0,2664,0,0,319,3,0,0,0,0,0,0,0,4096,0
build-join-4096,base,c,2,0.00,0.00,0%,0:00.00,0,0,0,0,2680,0,0,317,3,0,0,0,0,0,0,0,4096,0
build-join-4096,base,c,3,0.00,0.00,0%,0:00.00,0,0,0,0,2680,0,0,320,3,1,0,0,0,0,0,0,4096,0
build-join-4096,base,c,4,0.00,0.00,0%,0:00.00,0,0,0,0,2736,0,0,323,3,0,0,0,0,0,0,0,4096,0
build-join-4096,base,c,5,0.00,0.00,0%,0:00.00,0,0,0,0,2736,0,0,324,3,2,0,0,0,0,0,0,4096,0
build-join-4096,base,c,6,0.00,0.00,100%,0:00.00,0,0,0,0,2744,0,0,321,3,0,0,0,0,0,0,0,4096,0
build-join-4096,base,c,7,0.00,0.00,100%,0:00.00,0,0,0,0,2600,0,0,318,3,0,0,0,0,0,0,0,4096,0
build-join-4096,base,js,warm,0.01,0.01,118%,0:00.02,0,0,0,0,54412,0,0,5066,126,1,0,0,0,0,0,0,4096,0
build-join-4096,base,js,1,0.01,0.01,108%,0:00.02,0,0,0,0,53960,0,0,4975,119,11,0,0,0,0,0,0,4096,0
build-join-4096,base,js,2,0.01,0.01,116%,0:00.02,0,0,0,0,54212,0,0,5064,126,11,0,0,0,0,0,0,4096,0
build-join-4096,base,js,3,0.01,0.01,116%,0:00.02,0,0,0,0,54144,0,0,5070,121,9,0,0,0,0,0,0,4096,0
build-join-4096,base,js,4,0.01,0.00,119%,0:00.02,0,0,0,0,54028,0,0,5046,147,9,0,0,0,0,0,0,4096,0
build-join-4096,base,js,5,0.01,0.01,118%,0:00.02,0,0,0,0,54136,0,0,5024,129,8,0,0,0,0,0,0,4096,0
build-join-4096,base,js,6,0.00,0.01,130%,0:00.02,0,0,0,0,53940,0,0,5049,123,7,0,0,0,0,0,0,4096,0
build-join-4096,base,js,7,0.01,0.01,118%,0:00.02,0,0,0,0,54156,0,0,5066,123,8,0,0,0,0,0,0,4096,0
build-join-4096,base,c-counters,1,0.00,0.00,100%,0:00.00,0,0,0,0,2660,0,0,321,3,1,0,0,0,0,0,0,4096,0
build-join-4096,candidate,c,warm,0.00,0.00,100%,0:00.00,0,0,0,0,2616,0,0,310,3,0,0,0,0,0,0,0,4096,0
build-join-4096,candidate,c,1,0.00,0.00,0%,0:00.00,0,0,0,0,2668,0,0,315,3,1,0,0,0,0,0,0,4096,0
build-join-4096,candidate,c,2,0.00,0.00,0%,0:00.00,0,0,0,0,2616,0,0,312,3,0,0,0,0,0,0,0,4096,0
build-join-4096,candidate,c,3,0.00,0.00,100%,0:00.00,0,0,0,0,2532,0,0,312,3,0,0,0,0,0,0,0,4096,0
build-join-4096,candidate,c,4,0.00,0.00,0%,0:00.00,0,0,0,0,2616,0,0,312,3,1,0,0,0,0,0,0,4096,0
build-join-4096,candidate,c,5,0.00,0.00,0%,0:00.00,0,0,0,0,2676,0,0,317,3,0,0,0,0,0,0,0,4096,0
build-join-4096,candidate,c,6,0.00,0.00,0%,0:00.00,0,0,0,0,2424,0,0,311,3,0,0,0,0,0,0,0,4096,0
build-join-4096,candidate,c,7,0.00,0.00,100%,0:00.00,0,0,0,0,2604,0,0,311,3,0,0,0,0,0,0,0,4096,0
build-join-4096,candidate,js,warm,0.01,0.01,123%,0:00.02,0,0,0,0,54656,0,0,5136,115,6,0,0,0,0,0,0,4096,0
build-join-4096,candidate,js,1,0.01,0.01,119%,0:00.02,0,0,0,0,54476,0,0,5183,127,8,0,0,0,0,0,0,4096,0
build-join-4096,candidate,js,2,0.01,0.01,122%,0:00.02,0,0,0,0,55308,0,0,5191,148,5,0,0,0,0,0,0,4096,0
build-join-4096,candidate,js,3,0.01,0.00,117%,0:00.02,0,0,0,0,54716,0,0,5136,128,4,0,0,0,0,0,0,4096,0
build-join-4096,candidate,js,4,0.01,0.01,120%,0:00.02,0,0,0,0,54572,0,0,5134,118,3,0,0,0,0,0,0,4096,0
build-join-4096,candidate,js,5,0.01,0.01,117%,0:00.02,0,0,0,0,54136,0,0,5034,124,3,0,0,0,0,0,0,4096,0
build-join-4096,candidate,js,6,0.01,0.01,119%,0:00.02,0,0,0,0,54524,0,0,5124,123,4,0,0,0,0,0,0,4096,0
build-join-4096,candidate,js,7,0.01,0.01,120%,0:00.02,0,0,0,0,54608,0,0,5128,141,27,0,0,0,0,0,0,4096,0
build-join-4096,candidate,c-counters,1,0.00,0.00,0%,0:00.00,0,0,0,0,2664,0,0,313,3,0,0,0,0,0,0,0,4096,0
build-repeat-1024,base,c,warm,0.00,0.00,0%,0:00.00,0,0,0,0,2424,0,0,232,3,0,0,0,0,0,0,0,4096,0
build-repeat-1024,base,c,1,0.00,0.00,0%,0:00.00,0,0,0,0,2356,0,0,229,3,0,0,0,0,0,0,0,4096,0
build-repeat-1024,base,c,2,0.00,0.00,0%,0:00.00,0,0,0,0,2168,0,0,228,3,0,0,0,0,0,0,0,4096,0
build-repeat-1024,base,c,3,0.00,0.00,0%,0:00.00,0,0,0,0,2412,0,0,231,3,0,0,0,0,0,0,0,4096,0
build-repeat-1024,base,c,4,0.00,0.00,0%,0:00.00,0,0,0,0,2360,0,0,228,3,0,0,0,0,0,0,0,4096,0
build-repeat-1024,base,c,5,0.00,0.00,0%,0:00.00,0,0,0,0,2420,0,0,231,3,0,0,0,0,0,0,0,4096,0
build-repeat-1024,base,c,6,0.00,0.00,100%,0:00.00,0,0,0,0,2176,0,0,227,3,1,0,0,0,0,0,0,4096,0
build-repeat-1024,base,c,7,0.00,0.00,0%,0:00.00,0,0,0,0,2412,0,0,229,3,0,0,0,0,0,0,0,4096,0
build-repeat-1024,base,js,warm,0.00,0.01,114%,0:00.02,0,0,0,0,47304,0,0,3790,126,5,0,0,0,0,0,0,4096,0
build-repeat-1024,base,js,1,0.01,0.00,111%,0:00.01,0,0,0,0,47048,0,0,3802,125,4,0,0,0,0,0,0,4096,0
build-repeat-1024,base,js,2,0.00,0.01,111%,0:00.01,0,0,0,0,46856,0,0,3790,127,4,0,0,0,0,0,0,4096,0
build-repeat-1024,base,js,3,0.01,0.00,117%,0:00.01,0,0,0,0,46908,0,0,3842,128,13,0,0,0,0,0,0,4096,0
build-repeat-1024,base,js,4,0.01,0.00,118%,0:00.01,0,0,0,0,46912,0,0,3782,134,8,0,0,0,0,0,0,4096,0
build-repeat-1024,base,js,5,0.01,0.00,117%,0:00.01,0,0,0,0,46912,0,0,3842,155,4,0,0,0,0,0,0,4096,0
build-repeat-1024,base,js,6,0.01,0.00,120%,0:00.01,0,0,0,0,46524,0,0,3704,138,6,0,0,0,0,0,0,4096,0
build-repeat-1024,base,js,7,0.01,0.01,110%,0:00.01,0,0,0,0,46988,0,0,3792,104,15,0,0,0,0,0,0,4096,0
build-repeat-1024,base,c-counters,1,0.00,0.00,0%,0:00.00,0,0,0,0,2424,0,0,228,3,0,0,0,0,0,0,0,4096,0
build-repeat-1024,candidate,c,warm,0.00,0.00,0%,0:00.00,0,0,0,0,2412,0,0,228,3,0,0,0,0,0,0,0,4096,0
build-repeat-1024,candidate,c,1,0.00,0.00,0%,0:00.00,0,0,0,0,2360,0,0,227,3,0,0,0,0,0,0,0,4096,0
build-repeat-1024,candidate,c,2,0.00,0.00,0%,0:00.00,0,0,0,0,2168,0,0,227,3,0,0,0,0,0,0,0,4096,0
build-repeat-1024,candidate,c,3,0.00,0.00,0%,0:00.00,0,0,0,0,2288,0,0,225,3,0,0,0,0,0,0,0,4096,0
build-repeat-1024,candidate,c,4,0.00,0.00,0%,0:00.00,0,0,0,0,2288,0,0,226,3,0,0,0,0,0,0,0,4096,0
build-repeat-1024,candidate,c,5,0.00,0.00,0%,0:00.00,0,0,0,0,2348,0,0,228,3,2,0,0,0,0,0,0,4096,0
build-repeat-1024,candidate,c,6,0.00,0.00,0%,0:00.00,0,0,0,0,2420,0,0,230,3,0,0,0,0,0,0,0,4096,0
build-repeat-1024,candidate,c,7,0.00,0.00,0%,0:00.00,0,0,0,0,2276,0,0,226,3,2,0,0,0,0,0,0,4096,0
build-repeat-1024,candidate,js,warm,0.01,0.00,117%,0:00.01,0,0,0,0,47440,0,0,3914,130,16,0,0,0,0,0,0,4096,0
build-repeat-1024,candidate,js,1,0.01,0.00,111%,0:00.01,0,0,0,0,47552,0,0,3928,129,8,0,0,0,0,0,0,4096,0
build-repeat-1024,candidate,js,2,0.01,0.00,116%,0:00.01,0,0,0,0,47624,0,0,3922,122,5,0,0,0,0,0,0,4096,0
build-repeat-1024,candidate,js,3,0.00,0.01,116%,0:00.01,0,0,0,0,47360,0,0,3916,132,0,0,0,0,0,0,0,4096,0
build-repeat-1024,candidate,js,4,0.01,0.00,105%,0:00.01,0,0,0,0,47564,0,0,3916,136,2,0,0,0,0,0,0,4096,0
build-repeat-1024,candidate,js,5,0.01,0.00,100%,0:00.02,0,0,0,0,47168,0,0,3919,130,7,0,0,0,0,0,0,4096,0
build-repeat-1024,candidate,js,6,0.01,0.00,111%,0:00.01,0,0,0,0,46916,0,0,3873,141,3,0,0,0,0,0,0,4096,0
build-repeat-1024,candidate,js,7,0.01,0.00,118%,0:00.01,0,0,0,0,47488,0,0,3916,132,5,0,0,0,0,0,0,4096,0
build-repeat-1024,candidate,c-counters,1,0.00,0.00,100%,0:00.00,0,0,0,0,2224,0,0,224,3,0,0,0,0,0,0,0,4096,0
build-repeat-4096,base,c,warm,0.00,0.00,100%,0:00.00,0,0,0,0,2668,0,0,305,3,1,0,0,0,0,0,0,4096,0
build-repeat-4096,base,c,1,0.00,0.00,0%,0:00.00,0,0,0,0,2532,0,0,305,3,0,0,0,0,0,0,0,4096,0
build-repeat-4096,base,c,2,0.00,0.00,0%,0:00.00,0,0,0,0,2472,0,0,302,3,0,0,0,0,0,0,0,4096,0
build-repeat-4096,base,c,3,0.00,0.00,0%,0:00.00,0,0,0,0,2532,0,0,302,3,0,0,0,0,0,0,0,4096,0
build-repeat-4096,base,c,4,0.00,0.00,0%,0:00.00,0,0,0,0,2536,0,0,306,3,1,0,0,0,0,0,0,4096,0
build-repeat-4096,base,c,5,0.00,0.00,100%,0:00.00,0,0,0,0,2668,0,0,305,3,2,0,0,0,0,0,0,4096,0
build-repeat-4096,base,c,6,0.00,0.00,0%,0:00.00,0,0,0,0,2612,0,0,307,3,0,0,0,0,0,0,0,4096,0
build-repeat-4096,base,c,7,0.00,0.00,0%,0:00.00,0,0,0,0,2676,0,0,308,3,0,0,0,0,0,0,0,4096,0
build-repeat-4096,base,js,warm,0.01,0.00,115%,0:00.02,0,0,0,0,51900,0,0,4554,110,7,0,0,0,0,0,0,4096,0
build-repeat-4096,base,js,1,0.00,0.01,126%,0:00.01,0,0,0,0,51904,0,0,4556,113,5,0,0,0,0,0,0,4096,0
build-repeat-4096,base,js,2,0.01,0.00,121%,0:00.01,0,0,0,0,51904,0,0,4577,114,2,0,0,0,0,0,0,4096,0
build-repeat-4096,base,js,3,0.01,0.00,109%,0:00.02,0,0,0,0,51984,0,0,4581,128,8,0,0,0,0,0,0,4096,0
build-repeat-4096,base,js,4,0.01,0.00,115%,0:00.01,0,0,0,0,52416,0,0,4587,124,13,0,0,0,0,0,0,4096,0
build-repeat-4096,base,js,5,0.01,0.01,120%,0:00.02,0,0,0,0,52424,0,0,4682,131,4,0,0,0,0,0,0,4096,0
build-repeat-4096,base,js,6,0.01,0.01,112%,0:00.02,0,0,0,0,50048,0,0,4458,116,6,0,0,0,0,0,0,4096,0
build-repeat-4096,base,js,7,0.01,0.01,104%,0:00.02,0,0,0,0,52492,0,0,4600,89,6,0,0,0,0,0,0,4096,0
build-repeat-4096,base,c-counters,1,0.00,0.00,0%,0:00.00,0,0,0,0,2536,0,0,306,3,0,0,0,0,0,0,0,4096,0
build-repeat-4096,candidate,c,warm,0.00,0.00,0%,0:00.00,0,0,0,0,2224,0,0,233,3,1,0,0,0,0,0,0,4096,0
build-repeat-4096,candidate,c,1,0.00,0.00,0%,0:00.00,0,0,0,0,2356,0,0,238,3,0,0,0,0,0,0,0,4096,0
build-repeat-4096,candidate,c,2,0.00,0.00,100%,0:00.00,0,0,0,0,2424,0,0,238,3,0,0,0,0,0,0,0,4096,0
build-repeat-4096,candidate,c,3,0.00,0.00,0%,0:00.00,0,0,0,0,2420,0,0,241,3,3,0,0,0,0,0,0,4096,0
build-repeat-4096,candidate,c,4,0.00,0.00,0%,0:00.00,0,0,0,0,2412,0,0,240,3,0,0,0,0,0,0,0,4096,0
build-repeat-4096,candidate,c,5,0.00,0.00,100%,0:00.00,0,0,0,0,2288,0,0,235,3,0,0,0,0,0,0,0,4096,0
build-repeat-4096,candidate,c,6,0.00,0.00,100%,0:00.00,0,0,0,0,2412,0,0,234,3,1,0,0,0,0,0,0,4096,0
build-repeat-4096,candidate,c,7,0.00,0.00,0%,0:00.00,0,0,0,0,2276,0,0,235,3,1,0,0,0,0,0,0,4096,0
build-repeat-4096,candidate,js,warm,0.01,0.01,121%,0:00.01,0,0,0,0,52412,0,0,4658,132,5,0,0,0,0,0,0,4096,0
build-repeat-4096,candidate,js,1,0.01,0.00,115%,0:00.01,0,0,0,0,51684,0,0,4558,129,3,0,0,0,0,0,0,4096,0
build-repeat-4096,candidate,js,2,0.01,0.00,121%,0:00.01,0,0,0,0,52288,0,0,4642,120,9,0,0,0,0,0,0,4096,0
build-repeat-4096,candidate,js,3,0.01,0.01,127%,0:00.01,0,0,0,0,52872,0,0,4650,139,1,0,0,0,0,0,0,4096,0
build-repeat-4096,candidate,js,4,0.01,0.00,126%,0:00.01,0,0,0,0,53128,0,0,4697,132,6,0,0,0,0,0,0,4096,0
build-repeat-4096,candidate,js,5,0.01,0.01,127%,0:00.01,0,0,0,0,53000,0,0,4702,137,2,0,0,0,0,0,0,4096,0
build-repeat-4096,candidate,js,6,0.01,0.01,122%,0:00.02,0,0,0,0,52808,0,0,4693,130,4,0,0,0,0,0,0,4096,0
build-repeat-4096,candidate,js,7,0.01,0.01,120%,0:00.02,0,0,0,0,52032,0,0,4595,124,3,0,0,0,0,0,0,4096,0
build-repeat-4096,candidate,c-counters,1,0.00,0.00,0%,0:00.00,0,0,0,0,2216,0,0,236,3,0,0,0,0,0,0,0,4096,0
build-append-1024,base,c,warm,0.00,0.00,100%,0:00.00,0,0,0,0,2296,0,0,223,3,1,0,0,0,0,0,0,4096,0
build-append-1024,base,c,1,0.00,0.00,50%,0:00.00,0,0,0,0,2160,0,0,218,3,2,0,0,0,0,0,0,4096,0
build-append-1024,base,c,2,0.00,0.00,50%,0:00.00,0,0,0,0,2168,0,0,220,3,7,0,0,0,0,0,0,4096,0
build-append-1024,base,c,3,0.00,0.00,100%,0:00.00,0,0,0,0,2228,0,0,220,3,0,0,0,0,0,0,0,4096,0
build-append-1024,base,c,4,0.00,0.00,100%,0:00.00,0,0,0,0,2148,0,0,221,3,1,0,0,0,0,0,0,4096,0
build-append-1024,base,c,5,0.00,0.00,100%,0:00.00,0,0,0,0,2168,0,0,219,3,0,0,0,0,0,0,0,4096,0
build-append-1024,base,c,6,0.00,0.00,50%,0:00.00,0,0,0,0,2168,0,0,219,3,2,0,0,0,0,0,0,4096,0
build-append-1024,base,c,7,0.00,0.00,100%,0:00.00,0,0,0,0,2088,0,0,219,3,1,0,0,0,0,0,0,4096,0
build-append-1024,base,js,warm,0.00,0.01,111%,0:00.01,0,0,0,0,46524,0,0,3740,143,5,0,0,0,0,0,0,4096,0
build-append-1024,base,js,1,0.01,0.00,111%,0:00.01,0,0,0,0,46536,0,0,3727,149,6,0,0,0,0,0,0,4096,0
build-append-1024,base,js,2,0.01,0.00,117%,0:00.01,0,0,0,0,46584,0,0,3744,127,5,0,0,0,0,0,0,4096,0
build-append-1024,base,js,3,0.00,0.01,111%,0:00.01,0,0,0,0,46796,0,0,3725,127,9,0,0,0,0,0,0,4096,0
build-append-1024,base,js,4,0.00,0.01,123%,0:00.01,0,0,0,0,46476,0,0,3734,143,6,0,0,0,0,0,0,4096,0
build-append-1024,base,js,5,0.01,0.00,111%,0:00.01,0,0,0,0,46532,0,0,3753,120,1,0,0,0,0,0,0,4096,0
build-append-1024,base,js,6,0.01,0.00,117%,0:00.01,0,0,0,0,46840,0,0,3754,129,5,0,0,0,0,0,0,4096,0
build-append-1024,base,js,7,0.01,0.00,111%,0:00.01,0,0,0,0,46732,0,0,3758,124,4,0,0,0,0,0,0,4096,0
build-append-1024,base,c-counters,1,0.00,0.00,66%,0:00.00,0,0,0,0,2164,0,0,222,3,1,0,0,0,0,0,0,4096,0
build-append-1024,candidate,c,warm,0.00,0.00,0%,0:00.00,0,0,0,0,2424,0,0,256,3,0,0,0,0,0,0,0,4096,0
build-append-1024,candidate,c,1,0.00,0.00,0%,0:00.00,0,0,0,0,2548,0,0,258,3,2,0,0,0,0,0,0,4096,0
build-append-1024,candidate,c,2,0.00,0.00,0%,0:00.00,0,0,0,0,2552,0,0,260,3,0,0,0,0,0,0,0,4096,0
build-append-1024,candidate,c,3,0.00,0.00,100%,0:00.00,0,0,0,0,2548,0,0,261,3,0,0,0,0,0,0,0,4096,0
build-append-1024,candidate,c,4,0.00,0.00,0%,0:00.00,0,0,0,0,2484,0,0,261,3,0,0,0,0,0,0,0,4096,0
build-append-1024,candidate,c,5,0.00,0.00,100%,0:00.00,0,0,0,0,2548,0,0,260,3,0,0,0,0,0,0,0,4096,0
build-append-1024,candidate,c,6,0.00,0.00,0%,0:00.00,0,0,0,0,2488,0,0,260,3,2,0,0,0,0,0,0,4096,0
build-append-1024,candidate,c,7,0.00,0.00,0%,0:00.00,0,0,0,0,2540,0,0,260,3,1,0,0,0,0,0,0,4096,0
build-append-1024,candidate,js,warm,0.01,0.00,110%,0:00.01,0,0,0,0,47568,0,0,3885,129,8,0,0,0,0,0,0,4096,0
build-append-1024,candidate,js,1,0.01,0.00,111%,0:00.01,0,0,0,0,46736,0,0,3868,134,6,0,0,0,0,0,0,4096,0
build-append-1024,candidate,js,2,0.01,0.00,117%,0:00.01,0,0,0,0,47180,0,0,3895,121,2,0,0,0,0,0,0,4096,0
build-append-1024,candidate,js,3,0.00,0.01,117%,0:00.01,0,0,0,0,47112,0,0,3881,142,5,0,0,0,0,0,0,4096,0
build-append-1024,candidate,js,4,0.01,0.00,110%,0:00.01,0,0,0,0,46916,0,0,3874,120,8,0,0,0,0,0,0,4096,0
build-append-1024,candidate,js,5,0.01,0.00,116%,0:00.01,0,0,0,0,47308,0,0,3843,131,22,0,0,0,0,0,0,4096,0
build-append-1024,candidate,js,6,0.01,0.00,111%,0:00.01,0,0,0,0,46952,0,0,3879,40,3,0,0,0,0,0,0,4096,0
build-append-1024,candidate,js,7,0.01,0.00,111%,0:00.01,0,0,0,0,47040,0,0,3902,138,4,0,0,0,0,0,0,4096,0
build-append-1024,candidate,c-counters,1,0.00,0.00,0%,0:00.00,0,0,0,0,2548,0,0,260,3,0,0,0,0,0,0,0,4096,0
build-append-4096,base,c,warm,0.02,0.00,95%,0:00.02,0,0,0,0,2276,0,0,249,3,3,0,0,0,0,0,0,4096,0
build-append-4096,base,c,1,0.02,0.00,100%,0:00.02,0,0,0,0,2152,0,0,247,3,2,0,0,0,0,0,0,4096,0
build-append-4096,base,c,2,0.02,0.00,100%,0:00.02,0,0,0,0,2276,0,0,250,3,1,0,0,0,0,0,0,4096,0
build-append-4096,base,c,3,0.02,0.00,100%,0:00.02,0,0,0,0,2360,0,0,247,3,1,0,0,0,0,0,0,4096,0
build-append-4096,base,c,4,0.02,0.00,96%,0:00.02,0,0,0,0,2088,0,0,246,3,4,0,0,0,0,0,0,4096,0
build-append-4096,base,c,5,0.02,0.00,95%,0:00.02,0,0,0,0,2420,0,0,249,3,0,0,0,0,0,0,0,4096,0
build-append-4096,base,c,6,0.02,0.00,100%,0:00.02,0,0,0,0,2276,0,0,247,3,2,0,0,0,0,0,0,4096,0
build-append-4096,base,c,7,0.02,0.00,95%,0:00.02,0,0,0,0,2216,0,0,245,3,4,0,0,0,0,0,0,4096,0
build-append-4096,base,js,warm,0.01,0.01,115%,0:00.02,0,0,0,0,48520,0,0,4114,134,2,0,0,0,0,0,0,4096,0
build-append-4096,base,js,1,0.01,0.00,115%,0:00.01,0,0,0,0,50440,0,0,4185,150,5,0,0,0,0,0,0,4096,0
build-append-4096,base,js,2,0.01,0.01,116%,0:00.01,0,0,0,0,50880,0,0,4202,123,3,0,0,0,0,0,0,4096,0
build-append-4096,base,js,3,0.01,0.01,123%,0:00.01,0,0,0,0,50624,0,0,4207,116,3,0,0,0,0,0,0,4096,0
build-append-4096,base,js,4,0.01,0.01,122%,0:00.01,0,0,0,0,50884,0,0,4215,148,6,0,0,0,0,0,0,4096,0
build-append-4096,base,js,5,0.01,0.00,119%,0:00.02,0,0,0,0,50940,0,0,4191,139,3,0,0,0,0,0,0,4096,0
build-append-4096,base,js,6,0.01,0.01,121%,0:00.01,0,0,0,0,50824,0,0,4190,129,11,0,0,0,0,0,0,4096,0
build-append-4096,base,js,7,0.01,0.00,109%,0:00.02,0,0,0,0,48456,0,0,4126,139,2,0,0,0,0,0,0,4096,0
build-append-4096,base,c-counters,1,0.04,0.00,95%,0:00.04,0,0,0,0,2296,0,0,252,3,9,0,0,0,0,0,0,4096,0
build-append-4096,candidate,c,warm,0.00,0.00,0%,0:00.00,0,0,0,0,2548,0,0,267,3,0,0,0,0,0,0,0,4096,0
build-append-4096,candidate,c,1,0.00,0.00,100%,0:00.00,0,0,0,0,2404,0,0,264,3,1,0,0,0,0,0,0,4096,0
build-append-4096,candidate,c,2,0.00,0.00,0%,0:00.00,0,0,0,0,2488,0,0,266,3,0,0,0,0,0,0,0,4096,0
build-append-4096,candidate,c,3,0.00,0.00,0%,0:00.00,0,0,0,0,2296,0,0,264,3,0,0,0,0,0,0,0,4096,0
build-append-4096,candidate,c,4,0.00,0.00,0%,0:00.00,0,0,0,0,2404,0,0,266,3,1,0,0,0,0,0,0,4096,0
build-append-4096,candidate,c,5,0.00,0.00,100%,0:00.00,0,0,0,0,2296,0,0,264,3,0,0,0,0,0,0,0,4096,0
build-append-4096,candidate,c,6,0.00,0.00,0%,0:00.00,0,0,0,0,2476,0,0,263,3,2,0,0,0,0,0,0,4096,0
build-append-4096,candidate,c,7,0.00,0.00,100%,0:00.00,0,0,0,0,2548,0,0,263,3,0,0,0,0,0,0,0,4096,0
build-append-4096,candidate,js,warm,0.00,0.01,123%,0:00.01,0,0,0,0,51068,0,0,4306,130,3,0,0,0,0,0,0,4096,0
build-append-4096,candidate,js,1,0.01,0.00,122%,0:00.01,0,0,0,0,51524,0,0,4361,125,4,0,0,0,0,0,0,4096,0
build-append-4096,candidate,js,2,0.01,0.00,122%,0:00.01,0,0,0,0,51536,0,0,4360,136,2,0,0,0,0,0,0,4096,0
build-append-4096,candidate,js,3,0.01,0.01,127%,0:00.01,0,0,0,0,50936,0,0,4340,133,5,0,0,0,0,0,0,4096,0
build-append-4096,candidate,js,4,0.01,0.01,115%,0:00.01,0,0,0,0,50820,0,0,4338,135,6,0,0,0,0,0,0,4096,0
build-append-4096,candidate,js,5,0.01,0.01,119%,0:00.02,0,0,0,0,51200,0,0,4336,143,3,0,0,0,0,0,0,4096,0
build-append-4096,candidate,js,6,0.01,0.00,123%,0:00.01,0,0,0,0,51388,0,0,4327,126,7,0,0,0,0,0,0,4096,0
build-append-4096,candidate,js,7,0.01,0.00,110%,0:00.01,0,0,0,0,51256,0,0,4357,131,14,0,0,0,0,0,0,4096,0
build-append-4096,candidate,c-counters,1,0.00,0.00,0%,0:00.00,0,0,0,0,2540,0,0,265,3,0,0,0,0,0,0,0,4096,0
build-snapshots-128,base,c,warm,0.00,0.00,0%,0:00.00,0,0,0,0,2552,0,0,269,3,0,0,0,0,0,0,0,4096,0
build-snapshots-128,base,c,1,0.00,0.00,0%,0:00.00,0,0,0,0,2404,0,0,266,3,0,0,0,0,0,0,0,4096,0
build-snapshots-128,base,c,2,0.00,0.00,0%,0:00.00,0,0,0,0,2352,0,0,260,3,0,0,0,0,0,0,0,4096,0
build-snapshots-128,base,c,3,0.00,0.00,0%,0:00.00,0,0,0,0,2404,0,0,265,3,1,0,0,0,0,0,0,4096,0
build-snapshots-128,base,c,4,0.00,0.00,100%,0:00.00,0,0,0,0,2296,0,0,261,3,0,0,0,0,0,0,0,4096,0
build-snapshots-128,base,c,5,0.00,0.00,0%,0:00.00,0,0,0,0,2476,0,0,264,3,1,0,0,0,0,0,0,4096,0
build-snapshots-128,base,c,6,0.00,0.00,100%,0:00.00,0,0,0,0,2476,0,0,265,3,0,0,0,0,0,0,0,4096,0
build-snapshots-128,base,c,7,0.00,0.00,0%,0:00.00,0,0,0,0,2408,0,0,267,3,0,0,0,0,0,0,0,4096,0
build-snapshots-128,base,js,warm,0.01,0.00,115%,0:00.01,0,0,0,0,51020,0,0,4237,137,7,0,0,0,0,0,0,4096,0
build-snapshots-128,base,js,1,0.01,0.00,116%,0:00.01,0,0,0,0,51132,0,0,4252,120,16,0,0,0,0,0,0,4096,0
build-snapshots-128,base,js,2,0.01,0.00,121%,0:00.01,0,0,0,0,50828,0,0,4237,151,4,0,0,0,0,0,0,4096,0
build-snapshots-128,base,js,3,0.01,0.01,133%,0:00.01,0,0,0,0,50764,0,0,4255,131,3,0,0,0,0,0,0,4096,0
build-snapshots-128,base,js,4,0.01,0.01,120%,0:00.02,0,0,0,0,50560,0,0,4244,123,6,0,0,0,0,0,0,4096,0
build-snapshots-128,base,js,5,0.01,0.01,121%,0:00.01,0,0,0,0,50628,0,0,4222,154,5,0,0,0,0,0,0,4096,0
build-snapshots-128,base,js,6,0.01,0.01,120%,0:00.02,0,0,0,0,50768,0,0,4240,134,12,0,0,0,0,0,0,4096,0
build-snapshots-128,base,js,7,0.01,0.00,118%,0:00.02,0,0,0,0,50700,0,0,4233,138,5,0,0,0,0,0,0,4096,0
build-snapshots-128,base,c-counters,1,0.00,0.00,0%,0:00.00,0,0,0,0,2296,0,0,266,3,1,0,0,0,0,0,0,4096,0
build-snapshots-128,candidate,c,warm,0.00,0.00,0%,0:00.00,0,0,0,0,2404,0,0,264,3,0,0,0,0,0,0,0,4096,0
build-snapshots-128,candidate,c,1,0.00,0.00,0%,0:00.00,0,0,0,0,2416,0,0,264,3,0,0,0,0,0,0,0,4096,0
build-snapshots-128,candidate,c,2,0.00,0.00,0%,0:00.00,0,0,0,0,2548,0,0,268,3,0,0,0,0,0,0,0,4096,0
build-snapshots-128,candidate,c,3,0.00,0.00,0%,0:00.00,0,0,0,0,2416,0,0,264,3,1,0,0,0,0,0,0,4096,0
build-snapshots-128,candidate,c,4,0.00,0.00,100%,0:00.00,0,0,0,0,2352,0,0,262,3,0,0,0,0,0,0,0,4096,0
build-snapshots-128,candidate,c,5,0.00,0.00,0%,0:00.00,0,0,0,0,2548,0,0,266,3,0,0,0,0,0,0,0,4096,0
build-snapshots-128,candidate,c,6,0.00,0.00,0%,0:00.00,0,0,0,0,2424,0,0,265,2,7,0,0,0,0,0,0,4096,0
build-snapshots-128,candidate,c,7,0.00,0.00,0%,0:00.00,0,0,0,0,2548,0,0,264,3,1,0,0,0,0,0,0,4096,0
build-snapshots-128,candidate,js,warm,0.01,0.01,121%,0:00.01,0,0,0,0,51880,0,0,4475,134,5,0,0,0,0,0,0,4096,0
build-snapshots-128,candidate,js,1,0.01,0.01,121%,0:00.01,0,0,0,0,51344,0,0,4371,161,5,0,0,0,0,0,0,4096,0
build-snapshots-128,candidate,js,2,0.00,0.01,122%,0:00.01,0,0,0,0,51136,0,0,4344,145,5,0,0,0,0,0,0,4096,0
build-snapshots-128,candidate,js,3,0.01,0.00,126%,0:00.01,0,0,0,0,51784,0,0,4445,131,0,0,0,0,0,0,0,4096,0
build-snapshots-128,candidate,js,4,0.01,0.01,120%,0:00.02,0,0,0,0,51396,0,0,4390,145,17,0,0,0,0,0,0,4096,0
build-snapshots-128,candidate,js,5,0.01,0.01,113%,0:00.02,0,0,0,0,51388,0,0,4383,115,14,0,0,0,0,0,0,4096,0
build-snapshots-128,candidate,js,6,0.01,0.01,120%,0:00.02,0,0,0,0,51732,0,0,4451,121,9,0,0,0,0,0,0,4096,0
build-snapshots-128,candidate,js,7,0.01,0.01,122%,0:00.01,0,0,0,0,52168,0,0,4458,142,8,0,0,0,0,0,0,4096,0
build-snapshots-128,candidate,c-counters,1,0.00,0.00,0%,0:00.00,0,0,0,0,2352,0,0,259,3,0,0,0,0,0,0,0,4096,0
build-snapshots-512,base,c,warm,0.00,0.00,75%,0:00.00,0,0,0,0,5364,0,0,992,3,1,0,0,0,0,0,0,4096,0
build-snapshots-512,base,c,1,0.00,0.00,75%,0:00.00,0,0,0,0,5368,0,0,993,4,1,0,0,0,0,0,0,4096,0
build-snapshots-512,base,c,2,0.00,0.00,75%,0:00.00,0,0,0,0,5420,0,0,992,3,0,0,0,0,0,0,0,4096,0
build-snapshots-512,base,c,3,0.00,0.00,75%,0:00.00,0,0,0,0,5296,0,0,992,3,3,0,0,0,0,0,0,4096,0
build-snapshots-512,base,c,4,0.00,0.00,75%,0:00.00,0,0,0,0,5352,0,0,990,3,0,0,0,0,0,0,0,4096,0
build-snapshots-512,base,c,5,0.00,0.00,100%,0:00.00,0,0,0,0,5360,0,0,992,3,0,0,0,0,0,0,0,4096,0
build-snapshots-512,base,c,6,0.00,0.00,75%,0:00.00,0,0,0,0,5348,0,0,991,3,0,0,0,0,0,0,0,4096,0
build-snapshots-512,base,c,7,0.00,0.00,75%,0:00.00,0,0,0,0,5348,0,0,989,3,0,0,0,0,0,0,0,4096,0
build-snapshots-512,base,js,warm,0.02,0.02,117%,0:00.03,0,0,0,0,76616,0,0,10551,129,7,0,0,0,0,0,0,4096,0
build-snapshots-512,base,js,1,0.01,0.02,116%,0:00.03,0,0,0,0,76544,0,0,10487,113,1,0,0,0,0,0,0,4096,0
build-snapshots-512,base,js,2,0.02,0.02,115%,0:00.03,0,0,0,0,76304,0,0,10483,149,13,0,0,0,0,0,0,4096,0
build-snapshots-512,base,js,3,0.02,0.02,115%,0:00.03,0,0,0,0,76732,0,0,10522,135,8,0,0,0,0,0,0,4096,0
build-snapshots-512,base,js,4,0.02,0.02,118%,0:00.03,0,0,0,0,76416,0,0,10508,145,11,0,0,0,0,0,0,4096,0
build-snapshots-512,base,js,5,0.02,0.02,113%,0:00.03,0,0,0,0,76672,0,0,10473,130,1,0,0,0,0,0,0,4096,0
build-snapshots-512,base,js,6,0.01,0.02,118%,0:00.03,0,0,0,0,76484,0,0,10463,139,38,0,0,0,0,0,0,4096,0
build-snapshots-512,base,js,7,0.02,0.02,115%,0:00.03,0,0,0,0,76356,0,0,10470,129,9,0,0,0,0,0,0,4096,0
build-snapshots-512,base,c-counters,1,0.00,0.00,100%,0:00.00,0,0,0,0,5424,0,0,992,3,0,0,0,0,0,0,0,4096,0
build-snapshots-512,candidate,c,warm,0.00,0.00,100%,0:00.00,0,0,0,0,3684,0,0,583,3,10,0,0,0,0,0,0,4096,0
build-snapshots-512,candidate,c,1,0.00,0.00,100%,0:00.00,0,0,0,0,3764,0,0,589,3,1,0,0,0,0,0,0,4096,0
build-snapshots-512,candidate,c,2,0.00,0.00,100%,0:00.00,0,0,0,0,3756,0,0,587,3,1,0,0,0,0,0,0,4096,0
build-snapshots-512,candidate,c,3,0.00,0.00,100%,0:00.00,0,0,0,0,3820,0,0,589,3,0,0,0,0,0,0,0,4096,0
build-snapshots-512,candidate,c,4,0.00,0.00,100%,0:00.00,0,0,0,0,3576,0,0,582,3,1,0,0,0,0,0,0,4096,0
build-snapshots-512,candidate,c,5,0.00,0.00,100%,0:00.00,0,0,0,0,3684,0,0,586,3,0,0,0,0,0,0,0,4096,0
build-snapshots-512,candidate,c,6,0.00,0.00,100%,0:00.00,0,0,0,0,3704,0,0,585,3,12,0,0,0,0,0,0,4096,0
build-snapshots-512,candidate,c,7,0.00,0.00,33%,0:00.00,0,0,0,0,3760,0,0,585,3,1,0,0,0,0,0,0,4096,0
build-snapshots-512,candidate,js,warm,0.02,0.02,115%,0:00.03,0,0,0,0,77324,0,0,10710,134,13,0,0,0,0,0,0,4096,0
build-snapshots-512,candidate,js,1,0.02,0.02,117%,0:00.04,0,0,0,0,76864,0,0,10658,142,5,0,0,0,0,0,0,4096,0
build-snapshots-512,candidate,js,2,0.02,0.02,117%,0:00.03,0,0,0,0,77256,0,0,10704,142,5,0,0,0,0,0,0,4096,0
build-snapshots-512,candidate,js,3,0.02,0.02,120%,0:00.04,0,0,0,0,77148,0,0,10715,149,23,0,0,0,0,0,0,4096,0
build-snapshots-512,candidate,js,4,0.02,0.02,119%,0:00.04,0,0,0,0,76872,0,0,10689,166,6,0,0,0,0,0,0,4096,0
build-snapshots-512,candidate,js,5,0.02,0.02,118%,0:00.03,0,0,0,0,77000,0,0,10683,126,7,0,0,0,0,0,0,4096,0
build-snapshots-512,candidate,js,6,0.02,0.02,118%,0:00.03,0,0,0,0,77000,0,0,10664,130,7,0,0,0,0,0,0,4096,0
build-snapshots-512,candidate,js,7,0.02,0.02,121%,0:00.03,0,0,0,0,77120,0,0,10678,144,3,0,0,0,0,0,0,4096,0
build-snapshots-512,candidate,c-counters,1,0.00,0.00,100%,0:00.00,0,0,0,0,3684,0,0,583,3,1,0,0,0,0,0,0,4096,0
map-prefix-256,base,c,warm,0.00,0.00,75%,0:00.00,0,0,0,0,2544,0,0,310,3,2,0,0,0,0,0,0,4096,0
map-prefix-256,base,c,1,0.00,0.00,75%,0:00.00,0,0,0,0,2584,0,0,313,3,1,0,0,0,0,0,0,4096,0
map-prefix-256,base,c,2,0.00,0.00,100%,0:00.00,0,0,0,0,2532,0,0,314,3,0,0,0,0,0,0,0,4096,0
map-prefix-256,base,c,3,0.00,0.00,100%,0:00.00,0,0,0,0,2532,0,0,315,3,0,0,0,0,0,0,0,4096,0
map-prefix-256,base,c,4,0.00,0.00,75%,0:00.00,0,0,0,0,2544,0,0,313,2,3,0,0,0,0,0,0,4096,0
map-prefix-256,base,c,5,0.00,0.00,100%,0:00.00,0,0,0,0,2552,0,0,311,3,1,0,0,0,0,0,0,4096,0
map-prefix-256,base,c,6,0.00,0.00,100%,0:00.00,0,0,0,0,2528,0,0,313,3,0,0,0,0,0,0,0,4096,0
map-prefix-256,base,c,7,0.00,0.00,75%,0:00.00,0,0,0,0,2676,0,0,316,3,0,0,0,0,0,0,0,4096,0
map-prefix-256,base,js,warm,0.10,0.03,176%,0:00.08,0,0,0,0,100548,0,0,16398,568,14,0,0,0,0,0,0,4096,0
map-prefix-256,base,js,1,0.11,0.03,170%,0:00.08,0,0,0,0,100344,0,0,16399,557,54,0,0,0,0,0,0,4096,0
map-prefix-256,base,js,2,0.11,0.02,176%,0:00.08,0,0,0,0,100168,0,0,16396,617,25,0,0,0,0,0,0,4096,0
map-prefix-256,base,js,3,0.10,0.03,168%,0:00.08,0,0,0,0,100604,0,0,16482,583,22,0,0,0,0,0,0,4096,0
map-prefix-256,base,js,4,0.10,0.03,175%,0:00.07,0,0,0,0,100816,0,0,16486,530,47,0,0,0,0,0,0,4096,0
map-prefix-256,base,js,5,0.10,0.03,173%,0:00.08,0,0,0,0,100420,0,0,16444,595,14,0,0,0,0,0,0,4096,0
map-prefix-256,base,js,6,0.10,0.03,174%,0:00.08,0,0,0,0,100336,0,0,16392,599,29,0,0,0,0,0,0,4096,0
map-prefix-256,base,js,7,0.10,0.02,172%,0:00.07,0,0,0,0,100936,0,0,16452,610,47,0,0,0,0,0,0,4096,0
map-prefix-256,base,c-counters,1,0.00,0.00,80%,0:00.00,0,0,0,0,2424,0,0,311,3,3,0,0,0,0,0,0,4096,0
map-prefix-256,candidate,c,warm,0.00,0.00,50%,0:00.00,0,0,0,0,2424,0,0,255,3,4,0,0,0,0,0,0,4096,0
map-prefix-256,candidate,c,1,0.00,0.00,100%,0:00.00,0,0,0,0,2548,0,0,259,3,3,0,0,0,0,0,0,4096,0
map-prefix-256,candidate,c,2,0.00,0.00,100%,0:00.00,0,0,0,0,2424,0,0,257,3,0,0,0,0,0,0,0,4096,0
map-prefix-256,candidate,c,3,0.00,0.00,100%,0:00.00,0,0,0,0,2424,0,0,257,3,1,0,0,0,0,0,0,4096,0
map-prefix-256,candidate,c,4,0.00,0.00,100%,0:00.00,0,0,0,0,2404,0,0,257,3,1,0,0,0,0,0,0,4096,0
map-prefix-256,candidate,c,5,0.00,0.00,100%,0:00.00,0,0,0,0,2548,0,0,262,3,0,0,0,0,0,0,0,4096,0
map-prefix-256,candidate,c,6,0.00,0.00,100%,0:00.00,0,0,0,0,2360,0,0,260,3,3,0,0,0,0,0,0,4096,0
map-prefix-256,candidate,c,7,0.00,0.00,100%,0:00.00,0,0,0,0,2408,0,0,259,3,0,0,0,0,0,0,0,4096,0
map-prefix-256,candidate,js,warm,0.05,0.03,181%,0:00.04,0,0,0,0,83716,0,0,12231,156,6,0,0,0,0,0,0,4096,0
map-prefix-256,candidate,js,1,0.06,0.02,187%,0:00.04,0,0,0,0,83276,0,0,12178,163,21,0,0,0,0,0,0,4096,0
map-prefix-256,candidate,js,2,0.05,0.02,177%,0:00.04,0,0,0,0,82568,0,0,12018,186,41,0,0,0,0,0,0,4096,0
map-prefix-256,candidate,js,3,0.04,0.03,188%,0:00.04,0,0,0,0,83460,0,0,12214,170,7,0,0,0,0,0,0,4096,0
map-prefix-256,candidate,js,4,0.05,0.02,188%,0:00.04,0,0,0,0,83832,0,0,12249,138,5,0,0,0,0,0,0,4096,0
map-prefix-256,candidate,js,5,0.05,0.02,180%,0:00.04,0,0,0,0,83148,0,0,12043,172,21,0,0,0,0,0,0,4096,0
map-prefix-256,candidate,js,6,0.05,0.02,183%,0:00.04,0,0,0,0,83852,0,0,12269,166,17,0,0,0,0,0,0,4096,0
map-prefix-256,candidate,js,7,0.06,0.02,184%,0:00.04,0,0,0,0,83448,0,0,12164,155,52,0,0,0,0,0,0,4096,0
map-prefix-256,candidate,c-counters,1,0.00,0.00,100%,0:00.00,0,0,0,0,2552,0,0,259,3,0,0,0,0,0,0,0,4096,0
map-prefix-4096,base,c,warm,0.06,0.00,98%,0:00.06,0,0,0,0,8616,0,0,1850,3,1,0,0,0,0,0,0,4096,0
map-prefix-4096,base,c,1,0.05,0.00,98%,0:00.06,0,0,0,0,8616,0,0,1850,3,4,0,0,0,0,0,0,4096,0
map-prefix-4096,base,c,2,0.06,0.00,98%,0:00.06,0,0,0,0,8724,0,0,1850,2,2,0,0,0,0,0,0,4096,0
map-prefix-4096,base,c,3,0.05,0.00,98%,0:00.06,0,0,0,0,8600,0,0,1849,3,15,0,0,0,0,0,0,4096,0
map-prefix-4096,base,c,4,0.05,0.00,98%,0:00.06,0,0,0,0,8676,0,0,1848,3,15,0,0,0,0,0,0,4096,0
map-prefix-4096,base,c,5,0.05,0.00,98%,0:00.06,0,0,0,0,8680,0,0,1850,3,3,0,0,0,0,0,0,4096,0
map-prefix-4096,base,c,6,0.05,0.00,98%,0:00.06,0,0,0,0,8620,0,0,1851,3,6,0,0,0,0,0,0,4096,0
map-prefix-4096,base,c,7,0.05,0.00,98%,0:00.05,0,0,0,0,8568,0,0,1847,2,2,0,0,0,0,0,0,4096,0
map-prefix-4096,base,js,warm,0.78,0.10,117%,0:00.75,0,0,0,0,138300,0,0,35822,5709,135,0,0,0,0,0,0,4096,0
map-prefix-4096,base,js,1,0.75,0.10,117%,0:00.73,0,0,0,0,135976,0,0,35863,5924,214,0,0,0,0,0,0,4096,0
map-prefix-4096,base,js,2,0.78,0.09,117%,0:00.74,0,0,0,0,138408,0,0,35419,5840,173,0,0,0,0,0,0,4096,0
map-prefix-4096,base,js,3,0.78,0.09,117%,0:00.75,0,0,0,0,139248,0,0,35586,5800,481,0,0,0,0,0,0,4096,0
map-prefix-4096,base,js,4,0.77,0.08,117%,0:00.73,0,0,0,0,138720,0,0,35296,5709,98,0,0,0,0,0,0,4096,0
map-prefix-4096,base,js,5,0.79,0.07,117%,0:00.74,0,0,0,0,136192,0,0,35591,5607,226,0,0,0,0,0,0,4096,0
map-prefix-4096,base,js,6,0.77,0.11,117%,0:00.75,0,0,0,0,137988,0,0,36266,5624,218,0,0,0,0,0,0,4096,0
map-prefix-4096,base,js,7,0.75,0.11,117%,0:00.73,0,0,0,0,139776,0,0,37253,5987,282,0,0,0,0,0,0,4096,0
map-prefix-4096,base,c-counters,1,0.07,0.00,98%,0:00.07,0,0,0,0,8688,0,0,1849,3,2,0,0,0,0,0,0,4096,0
map-prefix-4096,candidate,c,warm,0.00,0.00,85%,0:00.00,0,0,0,0,3628,0,0,554,3,1,0,0,0,0,0,0,4096,0
map-prefix-4096,candidate,c,1,0.00,0.00,87%,0:00.00,0,0,0,0,3448,0,0,551,3,10,0,0,0,0,0,0,4096,0
map-prefix-4096,candidate,c,2,0.00,0.00,85%,0:00.00,0,0,0,0,3428,0,0,553,3,1,0,0,0,0,0,0,4096,0
map-prefix-4096,candidate,c,3,0.00,0.00,85%,0:00.00,0,0,0,0,3556,0,0,554,3,3,0,0,0,0,0,0,4096,0
map-prefix-4096,candidate,c,4,0.00,0.00,100%,0:00.00,0,0,0,0,3428,0,0,554,2,5,0,0,0,0,0,0,4096,0
map-prefix-4096,candidate,c,5,0.00,0.00,85%,0:00.00,0,0,0,0,3512,0,0,554,3,3,0,0,0,0,0,0,4096,0
map-prefix-4096,candidate,c,6,0.00,0.00,100%,0:00.00,0,0,0,0,3496,0,0,552,3,5,0,0,0,0,0,0,4096,0
map-prefix-4096,candidate,c,7,0.00,0.00,88%,0:00.00,0,0,0,0,3508,0,0,553,3,4,0,0,0,0,0,0,4096,0
map-prefix-4096,candidate,js,warm,0.19,0.04,124%,0:00.19,0,0,0,0,115276,0,0,20997,1163,34,0,0,0,0,0,0,4096,0
map-prefix-4096,candidate,js,1,0.18,0.05,125%,0:00.18,0,0,0,0,115716,0,0,20938,1105,76,0,0,0,0,0,0,4096,0
map-prefix-4096,candidate,js,2,0.18,0.04,124%,0:00.19,0,0,0,0,115236,0,0,20895,1108,58,0,0,0,0,0,0,4096,0
map-prefix-4096,candidate,js,3,0.19,0.03,123%,0:00.19,0,0,0,0,114876,0,0,20796,1165,55,0,0,0,0,0,0,4096,0
map-prefix-4096,candidate,js,4,0.18,0.04,126%,0:00.18,0,0,0,0,115524,0,0,21002,1115,6,0,0,0,0,0,0,4096,0
map-prefix-4096,candidate,js,5,0.20,0.04,124%,0:00.20,0,0,0,0,116084,0,0,21156,1159,26,0,0,0,0,0,0,4096,0
map-prefix-4096,candidate,js,6,0.19,0.04,125%,0:00.19,0,0,0,0,116476,0,0,21257,1144,73,0,0,0,0,0,0,4096,0
map-prefix-4096,candidate,js,7,0.19,0.04,123%,0:00.19,0,0,0,0,115272,0,0,20892,1066,140,0,0,0,0,0,0,4096,0
map-prefix-4096,candidate,c-counters,1,0.00,0.00,88%,0:00.00,0,0,0,0,3512,0,0,554,3,3,0,0,0,0,0,0,4096,0
```

</details>

<details>
<summary>base: full gprof flat and line profiles, plus seven diagnostic run reports</summary>

```text
base.flat.txt
Flat profile:

Each sample counts as 0.01 seconds.
  %   cumulative   self              self     total
 time   seconds   seconds    calls   s/call   s/call  name
 26.06      2.46     2.46   299040     0.00     0.00  heap_alloc_miss
 12.58      3.65     1.19    87388     0.00     0.00  WL_FID_WORDS_SCAN_K53
 10.15      4.62     0.96    87388     0.00     0.00  WL_FID_STRING_TAKE
  9.51      5.51     0.90 156849504     0.00     0.00  spin_3
  8.88      6.36     0.84    87388     0.00     0.00  WL_FID_STRING_SPLIT
  7.72      7.08     0.73 469762048     0.00     0.00  WL_FID_STRING_SPLIT_K25
  7.61      7.80     0.72        7     0.10     0.37  io_str
  4.86      8.27     0.46 469762048     0.00     0.00  WL_FID_STRING_TAKE_K43
  4.33      8.68     0.41 44826628     0.00     0.00  WL_FID_STRING_SPLIT_ACC
  2.54      8.91     0.24 89653256     0.00     0.00  WL_FID_STRING_TRIM_START
  1.06      9.02     0.10 44826628     0.00     0.00  WL_FID_LIST_APPEND
  0.95      9.11     0.09 67196248     0.00     0.00  WL_FID_LIST_FILTER_0_K22
  0.95      9.20     0.09 44826628     0.00     0.00  WL_FID_LIST_FILTER_0
  0.85      9.28     0.08                             _init
  0.53      9.32     0.05 44826628     0.00     0.00  WL_FID_STRING_TRIM_K27
  0.42      9.37     0.04 44914016     0.00     0.00  WL_FID_WORDS_LINES
  0.42      9.40     0.04 44826628     0.00     0.00  WL_FID_STRING_TRIM_K28
  0.21      9.43     0.02 44826628     0.00     0.00  WL_FID_STRING_WORDS
  0.11      9.44     0.01 44826628     0.00     0.00  WL_FID_WORDS_LINES_K37
  0.11      9.45     0.01 44826628     0.00     0.00  WL_FID_WORDS_LINES_K39
  0.11      9.46     0.01    87395     0.00     0.00  WL_FID_WORDS_SCAN
  0.05      9.46     0.01                             err_fail
  0.00      9.46     0.00 67108867     0.00     0.00  WL_FID_LIST_APPEND_K32
  0.00      9.46     0.00 44826628     0.00     0.00  WL_FID_STRING_TRIM
  0.00      9.46     0.00 44826628     0.00     0.00  WL_FID_STRING_WORDS_CUT
  0.00      9.46     0.00 44826628     0.00     0.00  WL_FID_STRING_WORDS_K30
  0.00      9.46     0.00 44826628     0.00     0.00  WL_FID_WORDS_LINES_K38
  0.00      9.46     0.00    98301     0.00     0.00  heap_hand
  0.00      9.46     0.00    87388     0.00     0.00  WL_FID_STRING_LINES
  0.00      9.46     0.00    87388     0.00     0.00  WL_FID_WORDS_MATERIALIZE
  0.00      9.46     0.00    87388     0.00     0.00  WL_FID_WORDS_MATERIALIZE_K45
  0.00      9.46     0.00    87388     0.00     0.00  WL_FID_WORDS_SCAN_K52
  0.00      9.46     0.00      238     0.00     0.00  WL_FID_CLO_APPLY
  0.00      9.46     0.00       63     0.00     0.00  WL_FID_ENTER
  0.00      9.46     0.00       63     0.00     0.00  WL_FID_EXIT
  0.00      9.46     0.00       63     0.00     0.11  corpus_eval
  0.00      9.46     0.00       56     0.00     0.00  WL_FID_IO_BIND
  0.00      9.46     0.00       56     0.00     0.00  WL_FID_IO_BIND_C96
  0.00      9.46     0.00       56     0.00     0.00  WL_FID_IO_BIND_K97
  0.00      9.46     0.00       56     0.00     0.00  WL_FID_STRING_APPEND_K50
  0.00      9.46     0.00       49     0.00     0.00  io_exec
  0.00      9.46     0.00       49     0.00     0.00  io_mem
  0.00      9.46     0.00       21     0.00     0.00  WL_FID_BENCH_MARK
  0.00      9.46     0.00       21     0.00     0.00  bench_mark_run
  0.00      9.46     0.00       21     0.00     0.00  io_cstr
  0.00      9.46     0.00       21     0.00     0.29  io_step
  0.00      9.46     0.00       21     0.00     0.00  io_sync
  0.00      9.46     0.00       14     0.00     0.00  WL_FID_IO_PASS_C78
  0.00      9.46     0.00       14     0.00     0.00  WL_FID_STRING_APPEND
  0.00      9.46     0.00       14     0.00     0.00  WL_FID_U32_SHOW
  0.00      9.46     0.00       14     0.00     0.00  WL_FID_U32_SHOW_GO
  0.00      9.46     0.00       14     0.00     0.00  io_out
  0.00      9.46     0.00       14     0.00     0.19  io_wait
  0.00      9.46     0.00       14     0.00     0.00  io_work
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_FILE_CLOSE
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_FILE_OPEN
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_FILE_READ
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_IO_EMIT
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_IO_PRINT
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_IO_TRY_C102
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_IO_TRY_C103
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_MAIN
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_MAIN_C100
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_MAIN_C101
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_MAIN_C104
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_MAIN_C105
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_MAIN_C106
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_MAIN_C107
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_MAIN_C108
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_MAIN_C109
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_MAIN_C110
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_MAIN_C111
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_MAIN_C112
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_MAIN_C114
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_MAIN_C115
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_MAIN_C99
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_MAIN_K113
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_MAIN_K116
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_MAIN_K117
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_MAIN_K118
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_MAIN_K119
  0.00      9.46     0.00        7     0.00     0.00  file_close_run
  0.00      9.46     0.00        7     0.00     0.00  file_open_call
  0.00      9.46     0.00        7     0.00     0.00  file_open_pack
  0.00      9.46     0.00        7     0.00     0.00  file_open_run
  0.00      9.46     0.00        7     0.00     0.00  file_read_call
  0.00      9.46     0.00        7     0.00     0.37  file_read_pack
  0.00      9.46     0.00        7     0.00     0.00  file_read_run
  0.00      9.46     0.00        7     0.00     1.34  io_loop
  0.00      9.46     0.00        7     0.00     0.00  io_print
  0.00      9.46     0.00        7     0.00     0.00  io_print_run
  0.00      9.46     0.00        7     0.00     0.00  io_spawn
  0.00      9.46     0.00        7     0.00     0.00  pool_stack
  0.00      9.46     0.00        7     0.00     0.00  term_drop
base.lines.txt
Flat profile:

Each sample counts as 0.01 seconds.
  %   cumulative   self              self     total
 time   seconds   seconds    calls  ns/call  ns/call  name
 24.42      2.31     2.31                             heap_alloc_miss (ascii-64MiB-io-scan.base.c:805 @ 401253)
  7.40      3.01     0.70                             WL_FID_STRING_TAKE (ascii-64MiB-io-scan.base.c:2443 @ 405423)
  5.66      3.54     0.54                             WL_FID_STRING_SPLIT (ascii-64MiB-io-scan.base.c:1055 @ 40410b)
  5.18      4.04     0.49                             WL_FID_WORDS_SCAN_K53 (ascii-64MiB-io-scan.base.c:1055 @ 405f90)
  3.49      4.37     0.33                             spin_3 (ascii-64MiB-io-scan.base.c:1055 @ 407cf5)
  2.22      4.58     0.21                             WL_FID_STRING_TAKE_K43 (ascii-64MiB-io-scan.base.c:816 @ 405649)
  1.80      4.75     0.17                             spin_15 (ascii-64MiB-io-scan.base.c:1055 @ 4062e6)
  1.69      4.91     0.16                             spin_3 (ascii-64MiB-io-scan.base.c:1394 @ 407cdc)
  1.64      5.06     0.15                             io_str (ascii-64MiB-io-scan.base.c:816 @ 402e73)
  1.59      5.21     0.15                             heap_alloc_miss (ascii-64MiB-io-scan.base.c:804 @ 401271)
  1.48      5.35     0.14                             WL_FID_STRING_SPLIT_K25 (ascii-64MiB-io-scan.base.c:816 @ 4045dc)
  1.22      5.46     0.12                             WL_FID_STRING_SPLIT_K25 (ascii-64MiB-io-scan.base.c:817 @ 4045e4)
  1.22      5.58     0.12                             io_str (ascii-64MiB-io-scan.base.c:4325 @ 402e8a)
  1.16      5.69     0.11                             spin_3 (ascii-64MiB-io-scan.base.c:1403 @ 407cd4)
  1.11      5.79     0.10                             io_str (ascii-64MiB-io-scan.base.c:4333 @ 402dd0)
  1.00      5.89     0.10                             WL_FID_STRING_SPLIT_K25 (ascii-64MiB-io-scan.base.c:2137 @ 40460f)
  0.95      5.98     0.09                             WL_FID_STRING_TAKE (ascii-64MiB-io-scan.base.c:2436 @ 40543e)
  0.95      6.07     0.09                             WL_FID_STRING_TAKE_K43 (ascii-64MiB-io-scan.base.c:2479 @ 40565d)
  0.90      6.16     0.09                             WL_FID_STRING_TAKE_K43 (ascii-64MiB-io-scan.base.c:2481 @ 40566f)
  0.85      6.24     0.08                             _init
  0.79      6.31     0.07                             io_str (ascii-64MiB-io-scan.base.c:4326 @ 402e8f)
  0.79      6.38     0.07                             spin_3 (ascii-64MiB-io-scan.base.c:1432 @ 407c86)
  0.74      6.46     0.07 469762048     0.15     0.15  WL_FID_STRING_SPLIT_K25 (ascii-64MiB-io-scan.base.c:2116 @ 404530)
  0.74      6.53     0.07                             WL_FID_STRING_TAKE (ascii-64MiB-io-scan.base.c:2450 @ 405444)
  0.74      6.59     0.07                             spin_3 (ascii-64MiB-io-scan.base.c:1405 @ 407cd9)
  0.69      6.66     0.07                             spin_15 (ascii-64MiB-io-scan.base.c:1668 @ 4062c0)
  0.63      6.72     0.06 156849504     0.38     0.38  spin_3 (ascii-64MiB-io-scan.base.c:1416 @ 407c30)
  0.63      6.78     0.06                             WL_FID_STRING_SPLIT (ascii-64MiB-io-scan.base.c:830 @ 4041bf)
  0.63      6.84     0.06                             WL_FID_STRING_SPLIT_ACC (ascii-64MiB-io-scan.base.c:1885 @ 403549)
  0.63      6.90     0.06                             WL_FID_WORDS_SCAN_K53 (ascii-64MiB-io-scan.base.c:1725 @ 405f73)
  0.58      6.96     0.06                             io_str (ascii-64MiB-io-scan.base.c:4336 @ 402e12)
  0.58      7.01     0.06                             io_str (ascii-64MiB-io-scan.base.c:817 @ 402e7b)
  0.53      7.06     0.05 44826628     1.12     1.12  WL_FID_STRING_SPLIT_ACC (ascii-64MiB-io-scan.base.c:1877 @ 403320)
  0.53      7.11     0.05                             WL_FID_STRING_SPLIT_K25 (ascii-64MiB-io-scan.base.c:1055 @ 404639)
  0.53      7.16     0.05                             heap_free (ascii-64MiB-io-scan.base.c:827 @ 406046)
  0.53      7.21     0.05                             heap_free (ascii-64MiB-io-scan.base.c:828 @ 406380)
  0.53      7.26     0.05                             io_str (ascii-64MiB-io-scan.base.c:4324 @ 402e86)
  0.53      7.31     0.05                             spin_0 (ascii-64MiB-io-scan.base.c:1344 @ 404540)
  0.48      7.36     0.04                             heap_free (ascii-64MiB-io-scan.base.c:829 @ 406052)
  0.48      7.40     0.04                             spin_15 (ascii-64MiB-io-scan.base.c:1659 @ 4062ca)
  0.42      7.44     0.04                             WL_FID_LIST_APPEND (ascii-64MiB-io-scan.base.c:2241 @ 404e07)
  0.42      7.48     0.04                             WL_FID_STRING_SPLIT (ascii-64MiB-io-scan.base.c:828 @ 4041a9)
  0.42      7.52     0.04                             WL_FID_STRING_SPLIT (ascii-64MiB-io-scan.base.c:2091 @ 4041d3)
  0.42      7.56     0.04                             WL_FID_STRING_SPLIT (ascii-64MiB-io-scan.base.c:2095 @ 4041e6)
  0.42      7.60     0.04                             WL_FID_STRING_SPLIT_ACC (ascii-64MiB-io-scan.base.c:1925 @ 403539)
  0.42      7.64     0.04                             WL_FID_STRING_SPLIT_ACC (ascii-64MiB-io-scan.base.c:1055 @ 403563)
  0.42      7.68     0.04                             WL_FID_STRING_SPLIT_K25 (ascii-64MiB-io-scan.base.c:814 @ 4046ea)
  0.42      7.72     0.04                             WL_FID_STRING_TRIM_START (ascii-64MiB-io-scan.base.c:1968 @ 4039b0)
  0.37      7.75     0.04                             WL_FID_STRING_SPLIT_K25 (ascii-64MiB-io-scan.base.c:1053 @ 404637)
  0.37      7.79     0.04                             WL_FID_STRING_TAKE (ascii-64MiB-io-scan.base.c:2451 @ 405448)
  0.37      7.83     0.04                             WL_FID_STRING_TAKE (ascii-64MiB-io-scan.base.c:2436 @ 405457)
  0.37      7.86     0.04                             WL_FID_STRING_TRIM_START (ascii-64MiB-io-scan.base.c:1055 @ 4039c6)
  0.37      7.89     0.04                             heap_free (ascii-64MiB-io-scan.base.c:828 @ 40604e)
  0.37      7.93     0.04                             term_rfc (ascii-64MiB-io-scan.base.c:865 @ 404634)
  0.32      7.96     0.03 89653256     0.33     0.33  WL_FID_STRING_TRIM_START (ascii-64MiB-io-scan.base.c:1964 @ 403930)
  0.32      7.99     0.03 44826628     0.67     0.67  WL_FID_STRING_TRIM_K27 (ascii-64MiB-io-scan.base.c:2162 @ 404850)
  0.32      8.02     0.03                             WL_FID_LIST_FILTER_0_K22 (ascii-64MiB-io-scan.base.c:2071 @ 404076)
  0.32      8.05     0.03                             WL_FID_STRING_SPLIT (ascii-64MiB-io-scan.base.c:2094 @ 4041e2)
  0.32      8.08     0.03                             WL_FID_STRING_SPLIT_K25 (ascii-64MiB-io-scan.base.c:1633 @ 404544)
  0.32      8.11     0.03                             WL_FID_STRING_SPLIT_K25 (ascii-64MiB-io-scan.base.c:815 @ 4046ee)
  0.32      8.14     0.03                             WL_FID_STRING_TAKE_K43 (ascii-64MiB-io-scan.base.c:814 @ 405640)
  0.32      8.17     0.03                             WL_FID_STRING_TRIM_START (ascii-64MiB-io-scan.base.c:1970 @ 403963)
  0.32      8.20     0.03                             heap_free (ascii-64MiB-io-scan.base.c:830 @ 406064)
  0.32      8.23     0.03                             io_str (ascii-64MiB-io-scan.base.c:815 @ 402e6e)
  0.32      8.26     0.03                             spin_15 (ascii-64MiB-io-scan.base.c:1055 @ 40617d)
  0.32      8.29     0.03                             spin_3 (ascii-64MiB-io-scan.base.c:1401 @ 407d01)
  0.32      8.32     0.03                             spin_5 (ascii-64MiB-io-scan.base.c:1055 @ 4037c9)
  0.32      8.35     0.03                             spin_8 (ascii-64MiB-io-scan.base.c:1515 @ 403fd4)
  0.26      8.38     0.03 67196248     0.37     0.37  WL_FID_LIST_FILTER_0_K22 (ascii-64MiB-io-scan.base.c:2051 @ 403fb0)
  0.26      8.40     0.03                             WL_FID_LIST_FILTER_0 (ascii-64MiB-io-scan.base.c:830 @ 403c8f)
  0.26      8.43     0.03                             WL_FID_STRING_SPLIT_ACC (ascii-64MiB-io-scan.base.c:1942 @ 4036c6)
  0.26      8.45     0.03                             WL_FID_STRING_TAKE (ascii-64MiB-io-scan.base.c:873 @ 4053f0)
  0.26      8.47     0.03                             WL_FID_WORDS_SCAN_K53 (ascii-64MiB-io-scan.base.c:1738 @ 405f70)
  0.26      8.50     0.03                             io_str (ascii-64MiB-io-scan.base.c:4338 @ 402e60)
  0.26      8.53     0.03                             io_str (ascii-64MiB-io-scan.base.c:814 @ 402e6a)
  0.21      8.54     0.02 469762048     0.04     0.04  WL_FID_STRING_TAKE_K43 (ascii-64MiB-io-scan.base.c:2472 @ 405630)
  0.21      8.56     0.02 44826628     0.45     0.45  WL_FID_STRING_TRIM_K28 (ascii-64MiB-io-scan.base.c:2189 @ 404910)
  0.21      8.59     0.02                             WL_FID_LIST_APPEND (ascii-64MiB-io-scan.base.c:2239 @ 404a3e)
  0.21      8.61     0.02                             WL_FID_LIST_FILTER_0 (ascii-64MiB-io-scan.base.c:2021 @ 403ba6)
  0.21      8.62     0.02                             WL_FID_LIST_FILTER_0 (ascii-64MiB-io-scan.base.c:2023 @ 403f67)
  0.21      8.64     0.02                             WL_FID_STRING_SPLIT (ascii-64MiB-io-scan.base.c:2096 @ 4041ee)
  0.21      8.66     0.02                             WL_FID_STRING_SPLIT_ACC (ascii-64MiB-io-scan.base.c:1921 @ 403534)
  0.21      8.69     0.02                             WL_FID_STRING_SPLIT_ACC (ascii-64MiB-io-scan.base.c:816 @ 403733)
  0.21      8.71     0.02                             WL_FID_STRING_SPLIT_ACC (ascii-64MiB-io-scan.base.c:817 @ 40373b)
  0.21      8.72     0.02                             WL_FID_STRING_SPLIT_ACC (ascii-64MiB-io-scan.base.c:1904 @ 4038eb)
  0.21      8.74     0.02                             WL_FID_STRING_TRIM_START (ascii-64MiB-io-scan.base.c:1984 @ 403a49)
  0.21      8.77     0.02                             WL_FID_STRING_TRIM_START (ascii-64MiB-io-scan.base.c:830 @ 403a7d)
  0.21      8.79     0.02                             WL_FID_STRING_TRIM_START (ascii-64MiB-io-scan.base.c:1987 @ 403b0d)
  0.21      8.80     0.02                             WL_FID_WORDS_LINES (ascii-64MiB-io-scan.base.c:1055 @ 405026)
  0.21      8.82     0.02                             WL_FID_WORDS_SCAN_K53 (ascii-64MiB-io-scan.base.c:1732 @ 405f9c)
  0.21      8.85     0.02                             heap_free (ascii-64MiB-io-scan.base.c:829 @ 406384)
  0.21      8.87     0.02                             io_str (ascii-64MiB-io-scan.base.c:4331 @ 402e95)
  0.21      8.88     0.02                             spin_3 (ascii-64MiB-io-scan.base.c:820 @ 407cab)
  0.16      8.90     0.01                             WL_FID_STRING_SPLIT (ascii-64MiB-io-scan.base.c:2093 @ 4040f1)
  0.16      8.91     0.01                             WL_FID_STRING_SPLIT (ascii-64MiB-io-scan.base.c:865 @ 404106)
  0.16      8.93     0.01                             WL_FID_STRING_TAKE_K43 (ascii-64MiB-io-scan.base.c:820 @ 405687)
  0.16      8.95     0.01                             spin_15 (ascii-64MiB-io-scan.base.c:829 @ 40622c)
  0.16      8.96     0.01                             spin_15 (ascii-64MiB-io-scan.base.c:830 @ 40623e)
  0.16      8.97     0.01                             spin_3 (ascii-64MiB-io-scan.base.c:1053 @ 407cf3)
  0.16      8.99     0.01                             term_rfc (ascii-64MiB-io-scan.base.c:865 @ 405f8b)
  0.16      9.01     0.01                             term_rfc (ascii-64MiB-io-scan.base.c:865 @ 407cf0)
  0.11      9.02     0.01 44914016     0.22     0.22  WL_FID_WORDS_LINES (ascii-64MiB-io-scan.base.c:2333 @ 404fc0)
  0.11      9.03     0.01 44826628     0.22     0.22  WL_FID_LIST_APPEND (ascii-64MiB-io-scan.base.c:2234 @ 404a20)
  0.11      9.04     0.01                             WL_FID_LIST_APPEND (ascii-64MiB-io-scan.base.c:828 @ 404b19)
  0.11      9.04     0.01                             WL_FID_LIST_APPEND (ascii-64MiB-io-scan.base.c:820 @ 404e27)
  0.11      9.05     0.01                             WL_FID_LIST_FILTER_0 (ascii-64MiB-io-scan.base.c:829 @ 403c7d)
  0.11      9.06     0.01                             WL_FID_STRING_SPLIT (ascii-64MiB-io-scan.base.c:1053 @ 404109)
  0.11      9.07     0.01                             WL_FID_STRING_SPLIT (ascii-64MiB-io-scan.base.c:827 @ 4041a1)
  0.11      9.09     0.01                             WL_FID_STRING_SPLIT (ascii-64MiB-io-scan.base.c:2084 @ 4044df)
  0.11      9.10     0.01                             WL_FID_STRING_SPLIT_ACC (ascii-64MiB-io-scan.base.c:1885 @ 4033c0)
  0.11      9.11     0.01                             WL_FID_STRING_SPLIT_ACC (ascii-64MiB-io-scan.base.c:1918 @ 403475)
  0.11      9.12     0.01                             WL_FID_STRING_SPLIT_ACC (ascii-64MiB-io-scan.base.c:1918 @ 4035f1)
  0.11      9.12     0.01                             WL_FID_STRING_SPLIT_ACC (ascii-64MiB-io-scan.base.c:1937 @ 4036b0)
  0.11      9.13     0.01                             WL_FID_STRING_SPLIT_ACC (ascii-64MiB-io-scan.base.c:1899 @ 403760)
  0.11      9.14     0.01                             WL_FID_STRING_SPLIT_K25 (ascii-64MiB-io-scan.base.c:816 @ 40455d)
  0.11      9.15     0.01                             WL_FID_STRING_SPLIT_K25 (ascii-64MiB-io-scan.base.c:818 @ 40456d)
  0.11      9.16     0.01                             WL_FID_STRING_SPLIT_K25 (ascii-64MiB-io-scan.base.c:1551 @ 40457f)
  0.11      9.18     0.01                             WL_FID_STRING_SPLIT_K25 (ascii-64MiB-io-scan.base.c:1566 @ 4046e5)
  0.11      9.19     0.01                             WL_FID_STRING_TAKE_K43 (ascii-64MiB-io-scan.base.c:2480 @ 40566c)
  0.11      9.20     0.01                             WL_FID_STRING_TRIM_K27 (ascii-64MiB-io-scan.base.c:2183 @ 404886)
  0.11      9.21     0.01                             WL_FID_STRING_TRIM_K28 (ascii-64MiB-io-scan.base.c:2194 @ 404924)
  0.11      9.21     0.01                             WL_FID_STRING_TRIM_K28 (ascii-64MiB-io-scan.base.c:2199 @ 404936)
  0.11      9.22     0.01                             WL_FID_STRING_TRIM_START (ascii-64MiB-io-scan.base.c:1968 @ 40394e)
  0.11      9.23     0.01                             WL_FID_STRING_TRIM_START (ascii-64MiB-io-scan.base.c:839 @ 403a52)
  0.11      9.24     0.01                             WL_FID_STRING_TRIM_START (ascii-64MiB-io-scan.base.c:1989 @ 403b1f)
  0.11      9.26     0.01                             WL_FID_STRING_WORDS (ascii-64MiB-io-scan.base.c:2208 @ 40496c)
  0.11      9.27     0.01                             WL_FID_STRING_WORDS (ascii-64MiB-io-scan.base.c:2218 @ 40497c)
  0.11      9.28     0.01                             WL_FID_WORDS_LINES (ascii-64MiB-io-scan.base.c:2360 @ 405106)
  0.11      9.29     0.01                             WL_FID_WORDS_LINES_K37 (ascii-64MiB-io-scan.base.c:2387 @ 405230)
  0.11      9.29     0.01                             WL_FID_WORDS_LINES_K39 (ascii-64MiB-io-scan.base.c:2425 @ 405394)
  0.11      9.30     0.01                             io_str (ascii-64MiB-io-scan.base.c:820 @ 402edd)
  0.11      9.31     0.01                             spin_15 (ascii-64MiB-io-scan.base.c:828 @ 406228)
  0.11      9.32     0.01                             spin_3 (ascii-64MiB-io-scan.base.c:1430 @ 407c83)
  0.11      9.34     0.01                             spin_5 (ascii-64MiB-io-scan.base.c:1440 @ 4037af)
  0.05      9.34     0.01   299040    16.72    16.72  heap_alloc_miss (ascii-64MiB-io-scan.base.c:785 @ 40110a)
  0.05      9.35     0.01                             WL_FID_LIST_APPEND (ascii-64MiB-io-scan.base.c:830 @ 404b2f)
  0.05      9.35     0.01                             WL_FID_LIST_APPEND (ascii-64MiB-io-scan.base.c:2248 @ 404b43)
  0.05      9.36     0.01                             WL_FID_LIST_FILTER_0 (ascii-64MiB-io-scan.base.c:2030 @ 403ca3)
  0.05      9.36     0.01                             WL_FID_LIST_FILTER_0 (ascii-64MiB-io-scan.base.c:2032 @ 403caf)
  0.05      9.37     0.01                             WL_FID_LIST_FILTER_0 (ascii-64MiB-io-scan.base.c:2033 @ 403cb2)
  0.05      9.37     0.01                             WL_FID_LIST_FILTER_0_K22 (ascii-64MiB-io-scan.base.c:2053 @ 403fc6)
  0.05      9.38     0.01                             WL_FID_STRING_SPLIT (ascii-64MiB-io-scan.base.c:839 @ 404117)
  0.05      9.38     0.01                             WL_FID_STRING_SPLIT (ascii-64MiB-io-scan.base.c:2093 @ 4041df)
  0.05      9.38     0.01                             WL_FID_STRING_SPLIT (ascii-64MiB-io-scan.base.c:2082 @ 4041f2)
  0.05      9.39     0.01                             WL_FID_STRING_SPLIT_ACC (ascii-64MiB-io-scan.base.c:1055 @ 4033f6)
  0.05      9.39     0.01                             WL_FID_STRING_SPLIT_ACC (ascii-64MiB-io-scan.base.c:1908 @ 403402)
  0.05      9.40     0.01                             WL_FID_STRING_SPLIT_ACC (ascii-64MiB-io-scan.base.c:1940 @ 4036c2)
  0.05      9.40     0.01                             WL_FID_STRING_SPLIT_ACC (ascii-64MiB-io-scan.base.c:1892 @ 403722)
  0.05      9.41     0.01                             WL_FID_STRING_SPLIT_ACC (ascii-64MiB-io-scan.base.c:814 @ 403726)
  0.05      9.41     0.01                             WL_FID_STRING_TAKE (ascii-64MiB-io-scan.base.c:865 @ 4053f6)
  0.05      9.42     0.01                             WL_FID_STRING_TRIM_K27 (ascii-64MiB-io-scan.base.c:2168 @ 404864)
  0.05      9.43     0.01                             WL_FID_STRING_TRIM_K27 (ascii-64MiB-io-scan.base.c:2171 @ 404872)
  0.05      9.43     0.01                             WL_FID_STRING_TRIM_START (ascii-64MiB-io-scan.base.c:1974 @ 4039d2)
  0.05      9.44     0.01                             WL_FID_STRING_TRIM_START (ascii-64MiB-io-scan.base.c:827 @ 403a5f)
  0.05      9.44     0.01                             WL_FID_STRING_TRIM_START (ascii-64MiB-io-scan.base.c:828 @ 403a67)
  0.05      9.45     0.01                             WL_FID_WORDS_SCAN (ascii-64MiB-io-scan.base.c:2600 @ 405c7c)
  0.05      9.45     0.01                             WL_FID_WORDS_SCAN (ascii-64MiB-io-scan.base.c:2601 @ 405c7f)
  0.05      9.46     0.01                             err_fail (ascii-64MiB-io-scan.base.c:605 @ 401100)
  0.05      9.46     0.01                             spin_3 (ascii-64MiB-io-scan.base.c:1394 @ 407c67)
  0.00      9.46     0.00 67108867     0.00     0.00  WL_FID_LIST_APPEND_K32 (ascii-64MiB-io-scan.base.c:2271 @ 404e50)
  0.00      9.46     0.00 44826628     0.00     0.00  WL_FID_LIST_FILTER_0 (ascii-64MiB-io-scan.base.c:2017 @ 403b90)
  0.00      9.46     0.00 44826628     0.00     0.00  WL_FID_STRING_TRIM (ascii-64MiB-io-scan.base.c:2143 @ 4047b0)
  0.00      9.46     0.00 44826628     0.00     0.00  WL_FID_STRING_WORDS (ascii-64MiB-io-scan.base.c:2205 @ 404960)
  0.00      9.46     0.00 44826628     0.00     0.00  WL_FID_STRING_WORDS_CUT (ascii-64MiB-io-scan.base.c:2003 @ 403b50)
  0.00      9.46     0.00 44826628     0.00     0.00  WL_FID_STRING_WORDS_K30 (ascii-64MiB-io-scan.base.c:2224 @ 404a00)
  0.00      9.46     0.00 44826628     0.00     0.00  WL_FID_WORDS_LINES_K37 (ascii-64MiB-io-scan.base.c:2367 @ 405210)
  0.00      9.46     0.00 44826628     0.00     0.00  WL_FID_WORDS_LINES_K38 (ascii-64MiB-io-scan.base.c:2393 @ 4052d0)
  0.00      9.46     0.00 44826628     0.00     0.00  WL_FID_WORDS_LINES_K39 (ascii-64MiB-io-scan.base.c:2418 @ 405380)
  0.00      9.46     0.00    98301     0.00     0.00  heap_hand (ascii-64MiB-io-scan.base.c:775 @ 400f3e)
  0.00      9.46     0.00    87395     0.00     0.00  WL_FID_WORDS_SCAN (ascii-64MiB-io-scan.base.c:2587 @ 405c50)
  0.00      9.46     0.00    87388     0.00     0.00  WL_FID_STRING_LINES (ascii-64MiB-io-scan.base.c:2322 @ 404fa0)
  0.00      9.46     0.00    87388     0.00     0.00  WL_FID_STRING_SPLIT (ascii-64MiB-io-scan.base.c:2077 @ 4040b0)
  0.00      9.46     0.00    87388     0.00     0.00  WL_FID_STRING_TAKE (ascii-64MiB-io-scan.base.c:2431 @ 4053a0)
  0.00      9.46     0.00    87388     0.00     0.00  WL_FID_WORDS_MATERIALIZE (ascii-64MiB-io-scan.base.c:2487 @ 4056a0)
  0.00      9.46     0.00    87388     0.00     0.00  WL_FID_WORDS_MATERIALIZE_K45 (ascii-64MiB-io-scan.base.c:2506 @ 405740)
  0.00      9.46     0.00    87388     0.00     0.00  WL_FID_WORDS_SCAN_K52 (ascii-64MiB-io-scan.base.c:2629 @ 405dc0)
  0.00      9.46     0.00    87388     0.00     0.00  WL_FID_WORDS_SCAN_K53 (ascii-64MiB-io-scan.base.c:2664 @ 405eb0)
  0.00      9.46     0.00      238     0.00     0.00  WL_FID_CLO_APPLY (ascii-64MiB-io-scan.base.c:3314 @ 407870)
  0.00      9.46     0.00       63     0.00     0.00  WL_FID_ENTER (ascii-64MiB-io-scan.base.c:3285 @ 4030a0)
  0.00      9.46     0.00       63     0.00     0.00  WL_FID_EXIT (ascii-64MiB-io-scan.base.c:3328 @ 4079d0)
  0.00      9.46     0.00       63     0.00     0.00  corpus_eval (ascii-64MiB-io-scan.base.c:4079 @ 40128f)
  0.00      9.46     0.00       56     0.00     0.00  WL_FID_IO_BIND (ascii-64MiB-io-scan.base.c:2734 @ 4065b0)
  0.00      9.46     0.00       56     0.00     0.00  WL_FID_IO_BIND_C96 (ascii-64MiB-io-scan.base.c:2750 @ 406620)
  0.00      9.46     0.00       56     0.00     0.00  WL_FID_IO_BIND_K97 (ascii-64MiB-io-scan.base.c:2774 @ 4066f0)
  0.00      9.46     0.00       56     0.00     0.00  WL_FID_STRING_APPEND_K50 (ascii-64MiB-io-scan.base.c:2572 @ 405be0)
  0.00      9.46     0.00       49     0.00     0.00  io_exec (ascii-64MiB-io-scan.base.c:4424 @ 4089e0)
  0.00      9.46     0.00       49     0.00     0.00  io_mem (ascii-64MiB-io-scan.base.c:4177 @ 400b6a)
  0.00      9.46     0.00       21     0.00     0.00  WL_FID_BENCH_MARK (ascii-64MiB-io-scan.base.c:3210 @ 407570)
  0.00      9.46     0.00       21     0.00     0.00  bench_mark_run (ascii-64MiB-io-scan.base.c:4908 @ 400660)
  0.00      9.46     0.00       21     0.00     0.00  io_cstr (ascii-64MiB-io-scan.base.c:4290 @ 400849)
  0.00      9.46     0.00       21     0.00     0.00  io_step (ascii-64MiB-io-scan.base.c:4717 @ 401bb0)
  0.00      9.46     0.00       21     0.00     0.00  io_sync (ascii-64MiB-io-scan.base.c:4273 @ 400f03)
  0.00      9.46     0.00       14     0.00     0.00  WL_FID_IO_PASS_C78 (ascii-64MiB-io-scan.base.c:2704 @ 4064c0)
  0.00      9.46     0.00       14     0.00     0.00  WL_FID_STRING_APPEND (ascii-64MiB-io-scan.base.c:2535 @ 4057b0)
  0.00      9.46     0.00       14     0.00     0.00  WL_FID_U32_SHOW (ascii-64MiB-io-scan.base.c:2517 @ 405760)
  0.00      9.46     0.00       14     0.00     0.00  WL_FID_U32_SHOW_GO (ascii-64MiB-io-scan.base.c:2286 @ 404ec0)
  0.00      9.46     0.00       14     0.00     0.00  io_out (ascii-64MiB-io-scan.base.c:4267 @ 400bdf)
  0.00      9.46     0.00       14     0.00     0.00  io_wait (ascii-64MiB-io-scan.base.c:4434 @ 401890)
  0.00      9.46     0.00       14     0.00     0.00  io_work (ascii-64MiB-io-scan.base.c:4403 @ 402160)
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_FILE_CLOSE (ascii-64MiB-io-scan.base.c:3256 @ 407710)
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_FILE_OPEN (ascii-64MiB-io-scan.base.c:3224 @ 4075f0)
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_FILE_READ (ascii-64MiB-io-scan.base.c:3240 @ 407680)
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_IO_EMIT (ascii-64MiB-io-scan.base.c:3304 @ 407810)
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_IO_PRINT (ascii-64MiB-io-scan.base.c:3270 @ 407790)
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_IO_TRY_C102 (ascii-64MiB-io-scan.base.c:2843 @ 406880)
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_IO_TRY_C103 (ascii-64MiB-io-scan.base.c:2856 @ 4068b0)
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_MAIN (ascii-64MiB-io-scan.base.c:2787 @ 406710)
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_MAIN_C100 (ascii-64MiB-io-scan.base.c:2810 @ 4067a0)
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_MAIN_C101 (ascii-64MiB-io-scan.base.c:2820 @ 4067d0)
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_MAIN_C104 (ascii-64MiB-io-scan.base.c:2893 @ 406a60)
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_MAIN_C105 (ascii-64MiB-io-scan.base.c:2905 @ 406ac0)
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_MAIN_C106 (ascii-64MiB-io-scan.base.c:2921 @ 406b40)
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_MAIN_C107 (ascii-64MiB-io-scan.base.c:2961 @ 406cf0)
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_MAIN_C108 (ascii-64MiB-io-scan.base.c:2987 @ 406e00)
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_MAIN_C109 (ascii-64MiB-io-scan.base.c:3001 @ 406e80)
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_MAIN_C110 (ascii-64MiB-io-scan.base.c:3019 @ 406f30)
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_MAIN_C111 (ascii-64MiB-io-scan.base.c:3032 @ 406f90)
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_MAIN_C112 (ascii-64MiB-io-scan.base.c:3049 @ 407040)
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_MAIN_C114 (ascii-64MiB-io-scan.base.c:3087 @ 407170)
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_MAIN_C115 (ascii-64MiB-io-scan.base.c:3106 @ 407230)
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_MAIN_C99 (ascii-64MiB-io-scan.base.c:2796 @ 406740)
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_MAIN_K113 (ascii-64MiB-io-scan.base.c:3073 @ 4070f0)
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_MAIN_K116 (ascii-64MiB-io-scan.base.c:3129 @ 4072f0)
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_MAIN_K117 (ascii-64MiB-io-scan.base.c:3152 @ 4073a0)
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_MAIN_K118 (ascii-64MiB-io-scan.base.c:3176 @ 407460)
  0.00      9.46     0.00        7     0.00     0.00  WL_FID_MAIN_K119 (ascii-64MiB-io-scan.base.c:3198 @ 407510)
  0.00      9.46     0.00        7     0.00     0.00  file_close_run (ascii-64MiB-io-scan.base.c:4992 @ 402430)
  0.00      9.46     0.00        7     0.00     0.00  file_open_call (ascii-64MiB-io-scan.base.c:4937 @ 402230)
  0.00      9.46     0.00        7     0.00     0.00  file_open_pack (ascii-64MiB-io-scan.base.c:4941 @ 4020d0)
  0.00      9.46     0.00        7     0.00     0.00  file_open_run (ascii-64MiB-io-scan.base.c:4947 @ 4006e0)
  0.00      9.46     0.00        7     0.00     0.00  file_read_call (ascii-64MiB-io-scan.base.c:4967 @ 4022c0)
  0.00      9.46     0.00        7     0.00     0.00  file_read_pack (ascii-64MiB-io-scan.base.c:4972 @ 402310)
  0.00      9.46     0.00        7     0.00     0.00  file_read_run (ascii-64MiB-io-scan.base.c:4979 @ 400b00)
  0.00      9.46     0.00        7     0.00     0.00  io_loop (ascii-64MiB-io-scan.base.c:4754 @ 400cde)
  0.00      9.46     0.00        7     0.00     0.00  io_print (ascii-64MiB-io-scan.base.c:5003 @ 400ba0)
  0.00      9.46     0.00        7     0.00     0.00  io_print_run (ascii-64MiB-io-scan.base.c:5008 @ 400c40)
  0.00      9.46     0.00        7     0.00     0.00  io_spawn (ascii-64MiB-io-scan.base.c:4246 @ 401820)
  0.00      9.46     0.00        7     0.00     0.00  io_str (ascii-64MiB-io-scan.base.c:4329 @ 402d80)
  0.00      9.46     0.00        7     0.00     0.00  pool_stack (ascii-64MiB-io-scan.base.c:3610 @ 402fb0)
  0.00      9.46     0.00        7     0.00     0.00  term_drop (ascii-64MiB-io-scan.base.c:947 @ 402930)
profile run 1
9586981:1707099817
BENCH {"phase":0,"ns":190790743266257}
BENCH {"phase":1,"ns":190791211583894}
BENCH {"phase":3,"ns":190794465313643}
	Command being timed: "profile/base --gpu off --threads 1"
	User time (seconds): 3.40
	System time (seconds): 0.35
	Percent of CPU this job got: 99%
	Elapsed (wall clock) time (h:mm:ss or m:ss): 0:03.77
	Average shared text size (kbytes): 0
	Average unshared data size (kbytes): 0
	Average stack size (kbytes): 0
	Average total size (kbytes): 0
	Maximum resident set size (kbytes): 1115896
	Average resident set size (kbytes): 0
	Major (requiring I/O) page faults: 0
	Minor (reclaiming a frame) page faults: 278726
	Voluntary context switches: 5
	Involuntary context switches: 170
	Swaps: 0
	File system inputs: 0
	File system outputs: 0
	Socket messages sent: 0
	Socket messages received: 0
	Signals delivered: 0
	Page size (bytes): 4096
	Exit status: 0
profile run 2
9586981:1707099817
BENCH {"phase":0,"ns":190794522760914}
BENCH {"phase":1,"ns":190794997246827}
BENCH {"phase":3,"ns":190798280577168}
	Command being timed: "profile/base --gpu off --threads 1"
	User time (seconds): 3.42
	System time (seconds): 0.35
	Percent of CPU this job got: 98%
	Elapsed (wall clock) time (h:mm:ss or m:ss): 0:03.81
	Average shared text size (kbytes): 0
	Average unshared data size (kbytes): 0
	Average stack size (kbytes): 0
	Average total size (kbytes): 0
	Maximum resident set size (kbytes): 1115760
	Average resident set size (kbytes): 0
	Major (requiring I/O) page faults: 0
	Minor (reclaiming a frame) page faults: 278726
	Voluntary context switches: 5
	Involuntary context switches: 517
	Swaps: 0
	File system inputs: 0
	File system outputs: 0
	Socket messages sent: 0
	Socket messages received: 0
	Signals delivered: 0
	Page size (bytes): 4096
	Exit status: 0
profile run 3
9586981:1707099817
BENCH {"phase":0,"ns":190798339845259}
BENCH {"phase":1,"ns":190798830160112}
BENCH {"phase":3,"ns":190802123574930}
	Command being timed: "profile/base --gpu off --threads 1"
	User time (seconds): 3.42
	System time (seconds): 0.37
	Percent of CPU this job got: 99%
	Elapsed (wall clock) time (h:mm:ss or m:ss): 0:03.84
	Average shared text size (kbytes): 0
	Average unshared data size (kbytes): 0
	Average stack size (kbytes): 0
	Average total size (kbytes): 0
	Maximum resident set size (kbytes): 1115948
	Average resident set size (kbytes): 0
	Major (requiring I/O) page faults: 0
	Minor (reclaiming a frame) page faults: 278729
	Voluntary context switches: 5
	Involuntary context switches: 680
	Swaps: 0
	File system inputs: 0
	File system outputs: 0
	Socket messages sent: 0
	Socket messages received: 0
	Signals delivered: 0
	Page size (bytes): 4096
	Exit status: 0
profile run 4
9586981:1707099817
BENCH {"phase":0,"ns":190802182907513}
BENCH {"phase":1,"ns":190802660148296}
BENCH {"phase":3,"ns":190805905039119}
	Command being timed: "profile/base --gpu off --threads 1"
	User time (seconds): 3.40
	System time (seconds): 0.35
	Percent of CPU this job got: 99%
	Elapsed (wall clock) time (h:mm:ss or m:ss): 0:03.78
	Average shared text size (kbytes): 0
	Average unshared data size (kbytes): 0
	Average stack size (kbytes): 0
	Average total size (kbytes): 0
	Maximum resident set size (kbytes): 1116456
	Average resident set size (kbytes): 0
	Major (requiring I/O) page faults: 0
	Minor (reclaiming a frame) page faults: 278728
	Voluntary context switches: 5
	Involuntary context switches: 606
	Swaps: 0
	File system inputs: 0
	File system outputs: 0
	Socket messages sent: 0
	Socket messages received: 0
	Signals delivered: 0
	Page size (bytes): 4096
	Exit status: 0
profile run 5
9586981:1707099817
BENCH {"phase":0,"ns":190805964815542}
BENCH {"phase":1,"ns":190806443920957}
BENCH {"phase":3,"ns":190809728402740}
	Command being timed: "profile/base --gpu off --threads 1"
	User time (seconds): 3.41
	System time (seconds): 0.37
	Percent of CPU this job got: 99%
	Elapsed (wall clock) time (h:mm:ss or m:ss): 0:03.82
	Average shared text size (kbytes): 0
	Average unshared data size (kbytes): 0
	Average stack size (kbytes): 0
	Average total size (kbytes): 0
	Maximum resident set size (kbytes): 1115816
	Average resident set size (kbytes): 0
	Major (requiring I/O) page faults: 0
	Minor (reclaiming a frame) page faults: 278728
	Voluntary context switches: 5
	Involuntary context switches: 406
	Swaps: 0
	File system inputs: 0
	File system outputs: 0
	Socket messages sent: 0
	Socket messages received: 0
	Signals delivered: 0
	Page size (bytes): 4096
	Exit status: 0
profile run 6
9586981:1707099817
BENCH {"phase":0,"ns":190809789165072}
BENCH {"phase":1,"ns":190810268399853}
BENCH {"phase":3,"ns":190813541232745}
	Command being timed: "profile/base --gpu off --threads 1"
	User time (seconds): 3.42
	System time (seconds): 0.36
	Percent of CPU this job got: 99%
	Elapsed (wall clock) time (h:mm:ss or m:ss): 0:03.81
	Average shared text size (kbytes): 0
	Average unshared data size (kbytes): 0
	Average stack size (kbytes): 0
	Average total size (kbytes): 0
	Maximum resident set size (kbytes): 1115876
	Average resident set size (kbytes): 0
	Major (requiring I/O) page faults: 0
	Minor (reclaiming a frame) page faults: 278727
	Voluntary context switches: 5
	Involuntary context switches: 484
	Swaps: 0
	File system inputs: 0
	File system outputs: 0
	Socket messages sent: 0
	Socket messages received: 0
	Signals delivered: 0
	Page size (bytes): 4096
	Exit status: 0
profile run 7
9586981:1707099817
BENCH {"phase":0,"ns":190813606550218}
BENCH {"phase":1,"ns":190814087502612}
BENCH {"phase":3,"ns":190817350974019}
	Command being timed: "profile/base --gpu off --threads 1"
	User time (seconds): 3.37
	System time (seconds): 0.40
	Percent of CPU this job got: 99%
	Elapsed (wall clock) time (h:mm:ss or m:ss): 0:03.80
	Average shared text size (kbytes): 0
	Average unshared data size (kbytes): 0
	Average stack size (kbytes): 0
	Average total size (kbytes): 0
	Maximum resident set size (kbytes): 1115896
	Average resident set size (kbytes): 0
	Major (requiring I/O) page faults: 0
	Minor (reclaiming a frame) page faults: 278727
	Voluntary context switches: 5
	Involuntary context switches: 384
	Swaps: 0
	File system inputs: 0
	File system outputs: 0
	Socket messages sent: 0
	Socket messages received: 0
	Signals delivered: 0
	Page size (bytes): 4096
	Exit status: 0
```

</details>

<details>
<summary>candidate: full gprof flat and line profiles, plus seven diagnostic run reports</summary>

```text
candidate.flat.txt
Flat profile:

Each sample counts as 0.01 seconds.
  %   cumulative   self              self     total
 time   seconds   seconds    calls  ms/call  ms/call  name
 29.75      1.94     1.94    87388     0.02     0.03  WL_FID_WORDS_SCAN_K13
 21.63      3.35     1.41 44914016     0.00     0.00  str_split_take
 16.56      4.43     1.08        7   154.29   154.29  io_str
 13.50      5.31     0.88 536958520     0.00     0.00  rfc_wrap
  7.52      5.80     0.49 112110362     0.00     0.00  term_drop
  4.45      6.09     0.29 44914016     0.00     0.00  WL_FID_WORDS_LINES
  2.76      6.27     0.18 156937039     0.00     0.00  str_view_owned
  1.84      6.39     0.12 45001537     0.00     0.00  str_take
  0.77      6.44     0.05 44826628     0.00     0.00  WL_FID_LIST_APPEND
  0.61      6.48     0.04 67108867     0.00     0.00  WL_FID_LIST_APPEND_K2
  0.61      6.52     0.04                             _init
  0.00      6.52     0.00 44826628     0.00     0.00  WL_FID_WORDS_LINES_K6
  0.00      6.52     0.00    87395     0.00     0.00  WL_FID_WORDS_SCAN
  0.00      6.52     0.00    87388     0.00     0.00  WL_FID_WORDS_MATERIALIZE
  0.00      6.52     0.00    87388     0.00     0.00  span_fade
  0.00      6.52     0.00      238     0.00     0.00  WL_FID_CLO_APPLY
  0.00      6.52     0.00      133     0.00     0.00  str_reserve
  0.00      6.52     0.00       63     0.00     0.00  WL_FID_ENTER
  0.00      6.52     0.00       63     0.00     0.00  WL_FID_EXIT
  0.00      6.52     0.00       63     0.00    85.71  corpus_eval
  0.00      6.52     0.00       56     0.00     0.00  WL_FID_IO_BIND
  0.00      6.52     0.00       56     0.00     0.00  WL_FID_IO_BIND_C50
  0.00      6.52     0.00       56     0.00     0.00  WL_FID_IO_BIND_K51
  0.00      6.52     0.00       49     0.00     0.00  io_exec
  0.00      6.52     0.00       49     0.00     0.00  io_mem
  0.00      6.52     0.00       42     0.00     0.00  heap_alloc_miss
  0.00      6.52     0.00       21     0.00     0.00  WL_FID_BENCH_MARK
  0.00      6.52     0.00       21     0.00     0.00  bench_mark_run
  0.00      6.52     0.00       21     0.00     0.00  io_cstr
  0.00      6.52     0.00       21     0.00   228.57  io_step
  0.00      6.52     0.00       21     0.00     0.00  io_sync
  0.00      6.52     0.00       14     0.00     0.00  WL_FID_IO_PASS_C34
  0.00      6.52     0.00       14     0.00     0.00  WL_FID_U32_SHOW
  0.00      6.52     0.00       14     0.00     0.00  WL_FID_U32_SHOW_GO
  0.00      6.52     0.00       14     0.00     0.00  io_out
  0.00      6.52     0.00       14     0.00    77.14  io_wait
  0.00      6.52     0.00       14     0.00     0.00  io_work
  0.00      6.52     0.00       14     0.00     0.00  str_append_take
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_FILE_CLOSE
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_FILE_OPEN
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_FILE_READ
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_IO_EMIT
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_IO_PRINT
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_IO_TRY_C56
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_IO_TRY_C57
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_MAIN
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_MAIN_C53
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_MAIN_C54
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_MAIN_C55
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_MAIN_C58
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_MAIN_C59
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_MAIN_C60
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_MAIN_C61
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_MAIN_C62
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_MAIN_C63
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_MAIN_C64
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_MAIN_C65
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_MAIN_C66
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_MAIN_C68
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_MAIN_C69
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_MAIN_K67
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_MAIN_K70
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_MAIN_K71
  0.00      6.52     0.00        7     0.00     0.00  file_close_run
  0.00      6.52     0.00        7     0.00     0.00  file_open_call
  0.00      6.52     0.00        7     0.00     0.00  file_open_pack
  0.00      6.52     0.00        7     0.00     0.00  file_open_run
  0.00      6.52     0.00        7     0.00     0.00  file_read_call
  0.00      6.52     0.00        7     0.00   154.29  file_read_pack
  0.00      6.52     0.00        7     0.00     0.00  file_read_run
  0.00      6.52     0.00        7     0.00     0.00  heap_hand
  0.00      6.52     0.00        7     0.00   925.71  io_loop
  0.00      6.52     0.00        7     0.00     0.00  io_print
  0.00      6.52     0.00        7     0.00     0.00  io_print_run
  0.00      6.52     0.00        7     0.00     0.00  io_spawn
  0.00      6.52     0.00        7     0.00     0.00  pool_stack
candidate.lines.txt
Flat profile:

Each sample counts as 0.01 seconds.
  %   cumulative   self              self     total
 time   seconds   seconds    calls  ps/call  ps/call  name
 10.12      0.66     0.66                             blk_write (ascii-64MiB-io-scan.candidate.c:1108 @ 402f21)
  6.13      1.06     0.40 536958520   744.94   744.94  rfc_wrap (ascii-64MiB-io-scan.candidate.c:864 @ 401194)
  4.14      1.33     0.27                             WL_FID_WORDS_SCAN_K13 (ascii-64MiB-io-scan.candidate.c:1345 @ 4047ac)
  3.99      1.59     0.26                             rfc_wrap (ascii-64MiB-io-scan.candidate.c:873 @ 40120f)
  3.68      1.83     0.24                             io_str (ascii-64MiB-io-scan.candidate.c:3956 @ 402f25)
  3.53      2.06     0.23                             str_split_take (ascii-64MiB-io-scan.candidate.c:1528 @ 4067ed)
  2.99      2.25     0.20                             str_split_take (ascii-64MiB-io-scan.candidate.c:799 @ 4068bf)
  2.76      2.44     0.18                             str_split_take (ascii-64MiB-io-scan.candidate.c:1522 @ 4067b6)
  2.61      2.60     0.17                             WL_FID_WORDS_SCAN_K13 (ascii-64MiB-io-scan.candidate.c:1225 @ 404671)
  2.30      2.75     0.15                             str_split_take (ascii-64MiB-io-scan.candidate.c:894 @ 406861)
  2.22      2.90     0.14                             WL_FID_WORDS_SCAN_K13 (ascii-64MiB-io-scan.candidate.c:1226 @ 404676)
  1.99      3.03     0.13                             rfc_view (ascii-64MiB-io-scan.candidate.c:885 @ 40464c)
  1.84      3.15     0.12                             rfc_view (ascii-64MiB-io-scan.candidate.c:886 @ 404770)
  1.69      3.26     0.11                             WL_FID_WORDS_SCAN_K13 (ascii-64MiB-io-scan.candidate.c:1051 @ 404539)
  1.69      3.37     0.11                             io_str (ascii-64MiB-io-scan.candidate.c:886 @ 4030c9)
  1.61      3.48     0.10                             term_drop (ascii-64MiB-io-scan.candidate.c:945 @ 402a4c)
  1.53      3.58     0.10                             rfc_wrap (ascii-64MiB-io-scan.candidate.c:872 @ 401204)
  1.07      3.65     0.07 112110362   624.38   624.38  term_drop (ascii-64MiB-io-scan.candidate.c:932 @ 4029c0)
  0.92      3.71     0.06 156937039   382.32   382.32  str_view_owned (ascii-64MiB-io-scan.candidate.c:1242 @ 403110)
  0.92      3.77     0.06                             blk_ptr (ascii-64MiB-io-scan.candidate.c:1094 @ 402f17)
  0.92      3.83     0.06                             rfc_view (ascii-64MiB-io-scan.candidate.c:886 @ 404655)
  0.92      3.88     0.06                             str_split_take (ascii-64MiB-io-scan.candidate.c:1530 @ 4067fc)
  0.92      3.94     0.06                             term_drop (ascii-64MiB-io-scan.candidate.c:941 @ 402a2e)
  0.92      4.00     0.06                             term_sink (ascii-64MiB-io-scan.candidate.c:1023 @ 404971)
  0.84      4.06     0.06                             WL_FID_WORDS_SCAN_K13 (ascii-64MiB-io-scan.candidate.c:1948 @ 4045c0)
  0.77      4.11     0.05                             WL_FID_WORDS_SCAN_K13 (ascii-64MiB-io-scan.candidate.c:813 @ 4046e0)
  0.77      4.16     0.05                             blk_read (ascii-64MiB-io-scan.candidate.c:1101 @ 4067e9)
  0.69      4.21     0.04                             WL_FID_WORDS_SCAN_K13 (ascii-64MiB-io-scan.candidate.c:1233 @ 40467a)
  0.69      4.25     0.04                             str_view_owned (ascii-64MiB-io-scan.candidate.c:1256 @ 4031d4)
  0.61      4.29     0.04 45001537   888.86   888.86  str_take (ascii-64MiB-io-scan.candidate.c:1231 @ 406410)
  0.61      4.33     0.04 44914016   890.59   890.59  str_split_take (ascii-64MiB-io-scan.candidate.c:1517 @ 4065e0)
  0.61      4.37     0.04                             WL_FID_WORDS_SCAN_K13 (ascii-64MiB-io-scan.candidate.c:885 @ 404510)
  0.61      4.41     0.04                             WL_FID_WORDS_SCAN_K13 (ascii-64MiB-io-scan.candidate.c:1248 @ 4047d1)
  0.61      4.45     0.04                             _init
  0.61      4.49     0.04                             blk_ptr (ascii-64MiB-io-scan.candidate.c:1094 @ 4067e1)
  0.61      4.53     0.04                             rfc_view (ascii-64MiB-io-scan.candidate.c:885 @ 403f4c)
  0.61      4.57     0.04                             rfc_wrap (ascii-64MiB-io-scan.candidate.c:799 @ 4011d9)
  0.61      4.61     0.04                             str_split_take (ascii-64MiB-io-scan.candidate.c:1485 @ 406794)
  0.61      4.65     0.04                             str_split_take (ascii-64MiB-io-scan.candidate.c:1532 @ 406898)
  0.61      4.69     0.04                             str_split_take (ascii-64MiB-io-scan.candidate.c:797 @ 4068b2)
  0.61      4.73     0.04                             term_drop (ascii-64MiB-io-scan.candidate.c:813 @ 402c2b)
  0.54      4.76     0.04                             WL_FID_WORDS_SCAN_K13 (ascii-64MiB-io-scan.candidate.c:822 @ 404691)
  0.54      4.80     0.04                             WL_FID_WORDS_SCAN_K13 (ascii-64MiB-io-scan.candidate.c:885 @ 404696)
  0.54      4.83     0.04                             WL_FID_WORDS_SCAN_K13 (ascii-64MiB-io-scan.candidate.c:1049 @ 4046bb)
  0.54      4.87     0.04                             str_split_take (ascii-64MiB-io-scan.candidate.c:1533 @ 4068a9)
  0.54      4.91     0.04                             str_split_take (ascii-64MiB-io-scan.candidate.c:1539 @ 406a1d)
  0.46      4.93     0.03 44914016   667.94   667.94  WL_FID_WORDS_LINES (ascii-64MiB-io-scan.candidate.c:2208 @ 403d30)
  0.46      4.96     0.03                             WL_FID_WORDS_SCAN_K13 (ascii-64MiB-io-scan.candidate.c:812 @ 4046cf)
  0.46      5.00     0.03                             blk_ptr (ascii-64MiB-io-scan.candidate.c:1094 @ 4047a3)
  0.46      5.03     0.03                             rfc_seal (ascii-64MiB-io-scan.candidate.c:876 @ 404823)
  0.46      5.05     0.03                             rfc_seal (ascii-64MiB-io-scan.candidate.c:877 @ 404835)
  0.46      5.08     0.03                             rfc_seal (ascii-64MiB-io-scan.candidate.c:880 @ 404858)
  0.46      5.12     0.03                             rfc_view (ascii-64MiB-io-scan.candidate.c:885 @ 404767)
  0.46      5.14     0.03                             rfc_wrap (ascii-64MiB-io-scan.candidate.c:871 @ 4011e9)
  0.46      5.17     0.03                             str_split_take (ascii-64MiB-io-scan.candidate.c:1526 @ 4067dc)
  0.46      5.21     0.03                             str_take (ascii-64MiB-io-scan.candidate.c:1239 @ 406472)
  0.46      5.24     0.03                             term_drop (ascii-64MiB-io-scan.candidate.c:813 @ 402a82)
  0.46      5.26     0.03                             term_drop (ascii-64MiB-io-scan.candidate.c:951 @ 402ad6)
  0.46      5.29     0.03                             term_loc (ascii-64MiB-io-scan.candidate.c:856 @ 404752)
  0.46      5.33     0.03                             term_peek (ascii-64MiB-io-scan.candidate.c:912 @ 404788)
  0.46      5.36     0.03                             term_peek (ascii-64MiB-io-scan.candidate.c:912 @ 4066ec)
  0.46      5.38     0.03                             term_tag (ascii-64MiB-io-scan.candidate.c:844 @ 4011bb)
  0.46      5.42     0.03                             term_triv (ascii-64MiB-io-scan.candidate.c:861 @ 4029fd)
  0.38      5.44     0.03                             WL_FID_WORDS_LINES (ascii-64MiB-io-scan.candidate.c:1444 @ 403f9e)
  0.38      5.46     0.03                             heap_free (ascii-64MiB-io-scan.candidate.c:810 @ 40653b)
  0.38      5.49     0.03                             str_split_take (ascii-64MiB-io-scan.candidate.c:798 @ 4068b6)
  0.31      5.51     0.02                             WL_FID_WORDS_LINES (ascii-64MiB-io-scan.candidate.c:1051 @ 403ddb)
  0.31      5.53     0.02                             WL_FID_WORDS_LINES (ascii-64MiB-io-scan.candidate.c:1444 @ 403f74)
  0.31      5.55     0.02                             WL_FID_WORDS_SCAN_K13 (ascii-64MiB-io-scan.candidate.c:886 @ 404519)
  0.31      5.57     0.02                             WL_FID_WORDS_SCAN_K13 (ascii-64MiB-io-scan.candidate.c:885 @ 40452e)
  0.31      5.59     0.02                             WL_FID_WORDS_SCAN_K13 (ascii-64MiB-io-scan.candidate.c:1940 @ 404594)
  0.31      5.61     0.02                             WL_FID_WORDS_SCAN_K13 (ascii-64MiB-io-scan.candidate.c:810 @ 40471a)
  0.31      5.63     0.02                             WL_FID_WORDS_SCAN_K13 (ascii-64MiB-io-scan.candidate.c:811 @ 404722)
  0.31      5.65     0.02                             WL_FID_WORDS_SCAN_K13 (ascii-64MiB-io-scan.candidate.c:813 @ 404738)
  0.31      5.67     0.02                             WL_FID_WORDS_SCAN_K13 (ascii-64MiB-io-scan.candidate.c:1256 @ 404807)
  0.31      5.69     0.02                             rfc_view (ascii-64MiB-io-scan.candidate.c:885 @ 403efd)
  0.31      5.71     0.02                             rfc_view (ascii-64MiB-io-scan.candidate.c:885 @ 404781)
  0.31      5.73     0.02                             rfc_view (ascii-64MiB-io-scan.candidate.c:886 @ 4066d1)
  0.31      5.75     0.02                             rfc_wrap (ascii-64MiB-io-scan.candidate.c:800 @ 4011e1)
  0.31      5.77     0.02                             str_slice_take (ascii-64MiB-io-scan.candidate.c:1333 @ 403ff7)
  0.31      5.79     0.02                             str_split_take (ascii-64MiB-io-scan.candidate.c:877 @ 406776)
  0.31      5.81     0.02                             str_split_take (ascii-64MiB-io-scan.candidate.c:1528 @ 406830)
  0.31      5.83     0.02                             str_view_owned (ascii-64MiB-io-scan.candidate.c:799 @ 4031c0)
  0.31      5.85     0.02                             term_drop (ascii-64MiB-io-scan.candidate.c:969 @ 402b8a)
  0.31      5.87     0.02                             term_triv (ascii-64MiB-io-scan.candidate.c:861 @ 402cdf)
  0.23      5.88     0.01                             WL_FID_WORDS_SCAN_K13 (ascii-64MiB-io-scan.candidate.c:885 @ 4046b4)
  0.23      5.90     0.01                             blk_read (ascii-64MiB-io-scan.candidate.c:1101 @ 403f9b)
  0.23      5.92     0.01                             str_split_take (ascii-64MiB-io-scan.candidate.c:1530 @ 406836)
  0.23      5.93     0.01                             str_split_take (ascii-64MiB-io-scan.candidate.c:900 @ 406846)
  0.23      5.95     0.01                             term_drop (ascii-64MiB-io-scan.candidate.c:810 @ 402a67)
  0.23      5.96     0.01                             term_loc (ascii-64MiB-io-scan.candidate.c:856 @ 4045f2)
  0.15      5.97     0.01 44826628   223.08   223.08  WL_FID_LIST_APPEND (ascii-64MiB-io-scan.candidate.c:2123 @ 403680)
  0.15      5.98     0.01                             WL_FID_LIST_APPEND (ascii-64MiB-io-scan.candidate.c:813 @ 40374f)
  0.15      5.99     0.01                             WL_FID_LIST_APPEND (ascii-64MiB-io-scan.candidate.c:2141 @ 4037ba)
  0.15      6.00     0.01                             WL_FID_LIST_APPEND (ascii-64MiB-io-scan.candidate.c:2130 @ 403a67)
  0.15      6.01     0.01                             WL_FID_LIST_APPEND_K2 (ascii-64MiB-io-scan.candidate.c:2162 @ 403abc)
  0.15      6.02     0.01                             WL_FID_LIST_APPEND_K2 (ascii-64MiB-io-scan.candidate.c:877 @ 403b4c)
  0.15      6.03     0.01                             WL_FID_LIST_APPEND_K2 (ascii-64MiB-io-scan.candidate.c:2169 @ 403b71)
  0.15      6.04     0.01                             WL_FID_WORDS_LINES (ascii-64MiB-io-scan.candidate.c:812 @ 403df0)
  0.15      6.05     0.01                             WL_FID_WORDS_LINES (ascii-64MiB-io-scan.candidate.c:811 @ 403e2b)
  0.15      6.06     0.01                             WL_FID_WORDS_LINES (ascii-64MiB-io-scan.candidate.c:812 @ 403e2f)
  0.15      6.07     0.01                             WL_FID_WORDS_LINES (ascii-64MiB-io-scan.candidate.c:1225 @ 403f29)
  0.15      6.08     0.01                             WL_FID_WORDS_LINES (ascii-64MiB-io-scan.candidate.c:1447 @ 403fd1)
  0.15      6.09     0.01                             WL_FID_WORDS_SCAN_K13 (ascii-64MiB-io-scan.candidate.c:813 @ 40455f)
  0.15      6.10     0.01                             WL_FID_WORDS_SCAN_K13 (ascii-64MiB-io-scan.candidate.c:1222 @ 4045e7)
  0.15      6.11     0.01                             WL_FID_WORDS_SCAN_K13 (ascii-64MiB-io-scan.candidate.c:911 @ 404605)
  0.15      6.12     0.01                             WL_FID_WORDS_SCAN_K13 (ascii-64MiB-io-scan.candidate.c:1224 @ 404607)
  0.15      6.13     0.01                             WL_FID_WORDS_SCAN_K13 (ascii-64MiB-io-scan.candidate.c:886 @ 40469f)
  0.15      6.14     0.01                             WL_FID_WORDS_SCAN_K13 (ascii-64MiB-io-scan.candidate.c:812 @ 404726)
  0.15      6.15     0.01                             WL_FID_WORDS_SCAN_K13 (ascii-64MiB-io-scan.candidate.c:813 @ 4049d5)
  0.15      6.16     0.01                             io_str (ascii-64MiB-io-scan.candidate.c:885 @ 4030c0)
  0.15      6.17     0.01                             rfc_view (ascii-64MiB-io-scan.candidate.c:886 @ 403f06)
  0.15      6.18     0.01                             rfc_view (ascii-64MiB-io-scan.candidate.c:885 @ 403f17)
  0.15      6.19     0.01                             rfc_view (ascii-64MiB-io-scan.candidate.c:886 @ 403f55)
  0.15      6.20     0.01                             rfc_view (ascii-64MiB-io-scan.candidate.c:887 @ 404662)
  0.15      6.21     0.01                             rfc_view (ascii-64MiB-io-scan.candidate.c:885 @ 404666)
  0.15      6.22     0.01                             rfc_view (ascii-64MiB-io-scan.candidate.c:886 @ 406674)
  0.15      6.23     0.01                             rfc_view (ascii-64MiB-io-scan.candidate.c:885 @ 4066c5)
  0.15      6.24     0.01                             str_peek (ascii-64MiB-io-scan.candidate.c:1222 @ 40661b)
  0.15      6.25     0.01                             str_peek (ascii-64MiB-io-scan.candidate.c:1224 @ 406692)
  0.15      6.26     0.01                             str_peek (ascii-64MiB-io-scan.candidate.c:1225 @ 406696)
  0.15      6.27     0.01                             str_split_take (ascii-64MiB-io-scan.candidate.c:1522 @ 406726)
  0.15      6.28     0.01                             str_split_take (ascii-64MiB-io-scan.candidate.c:1535 @ 4067b2)
  0.15      6.29     0.01                             str_split_take (ascii-64MiB-io-scan.candidate.c:1531 @ 406814)
  0.15      6.30     0.01                             str_take (ascii-64MiB-io-scan.candidate.c:812 @ 406503)
  0.15      6.31     0.01                             str_view_owned (ascii-64MiB-io-scan.candidate.c:1247 @ 403197)
  0.15      6.32     0.01                             str_view_owned (ascii-64MiB-io-scan.candidate.c:1248 @ 4031a2)
  0.15      6.33     0.01                             str_view_owned (ascii-64MiB-io-scan.candidate.c:1258 @ 40322a)
  0.15      6.34     0.01                             str_view_owned (ascii-64MiB-io-scan.candidate.c:803 @ 403233)
  0.15      6.35     0.01                             term_drop (ascii-64MiB-io-scan.candidate.c:861 @ 402aa0)
  0.15      6.36     0.01                             term_drop (ascii-64MiB-io-scan.candidate.c:977 @ 402bcf)
  0.15      6.37     0.01                             term_drop (ascii-64MiB-io-scan.candidate.c:812 @ 402c1b)
  0.15      6.38     0.01                             term_drop (ascii-64MiB-io-scan.candidate.c:1000 @ 402c7d)
  0.15      6.39     0.01                             term_drop (ascii-64MiB-io-scan.candidate.c:1019 @ 402d37)
  0.15      6.40     0.01                             term_loc (ascii-64MiB-io-scan.candidate.c:856 @ 402a28)
  0.15      6.41     0.01                             term_rfc (ascii-64MiB-io-scan.candidate.c:848 @ 403209)
  0.15      6.42     0.01                             term_rfc (ascii-64MiB-io-scan.candidate.c:848 @ 403b06)
  0.15      6.43     0.01                             term_triv (ascii-64MiB-io-scan.candidate.c:861 @ 4069ea)
  0.08      6.43     0.01                             WL_FID_LIST_APPEND (ascii-64MiB-io-scan.candidate.c:2140 @ 4037b2)
  0.08      6.44     0.01                             WL_FID_LIST_APPEND (ascii-64MiB-io-scan.candidate.c:2128 @ 4037be)
  0.08      6.45     0.01                             WL_FID_WORDS_LINES (ascii-64MiB-io-scan.candidate.c:2223 @ 403e5f)
  0.08      6.45     0.01                             WL_FID_WORDS_LINES (ascii-64MiB-io-scan.candidate.c:2224 @ 403e62)
  0.08      6.46     0.01                             WL_FID_WORDS_LINES (ascii-64MiB-io-scan.candidate.c:1226 @ 403f2e)
  0.08      6.46     0.01                             WL_FID_WORDS_SCAN_K13 (ascii-64MiB-io-scan.candidate.c:1940 @ 4045cb)
  0.08      6.46     0.01                             WL_FID_WORDS_SCAN_K13 (ascii-64MiB-io-scan.candidate.c:799 @ 4047f3)
  0.08      6.47     0.01                             WL_FID_WORDS_SCAN_K13 (ascii-64MiB-io-scan.candidate.c:800 @ 4047fb)
  0.08      6.47     0.01                             err_post (ascii-64MiB-io-scan.candidate.c:592 @ 406a2f)
  0.08      6.48     0.01                             heap_free (ascii-64MiB-io-scan.candidate.c:811 @ 406543)
  0.08      6.49     0.01                             str_split_take (ascii-64MiB-io-scan.candidate.c:800 @ 4068c7)
  0.08      6.49     0.01                             str_take (ascii-64MiB-io-scan.candidate.c:1225 @ 4064a2)
  0.08      6.50     0.01                             str_take (ascii-64MiB-io-scan.candidate.c:1226 @ 4064a7)
  0.08      6.50     0.01                             str_view_owned (ascii-64MiB-io-scan.candidate.c:1257 @ 4031ea)
  0.08      6.50     0.01                             term_drop (ascii-64MiB-io-scan.candidate.c:810 @ 402c04)
  0.08      6.51     0.01                             term_drop (ascii-64MiB-io-scan.candidate.c:812 @ 402c0a)
  0.08      6.51     0.01                             term_loc (ascii-64MiB-io-scan.candidate.c:856 @ 403f32)
  0.08      6.52     0.01                             term_rfc (ascii-64MiB-io-scan.candidate.c:848 @ 404602)
  0.00      6.52     0.00 67108867     0.00     0.00  WL_FID_LIST_APPEND_K2 (ascii-64MiB-io-scan.candidate.c:2160 @ 403ab0)
  0.00      6.52     0.00 44826628     0.00     0.00  WL_FID_WORDS_LINES_K6 (ascii-64MiB-io-scan.candidate.c:2241 @ 4040e0)
  0.00      6.52     0.00    87395     0.00     0.00  WL_FID_WORDS_SCAN (ascii-64MiB-io-scan.candidate.c:2283 @ 404190)
  0.00      6.52     0.00    87388     0.00     0.00  WL_FID_WORDS_MATERIALIZE (ascii-64MiB-io-scan.candidate.c:2254 @ 404100)
  0.00      6.52     0.00    87388     0.00     0.00  WL_FID_WORDS_SCAN_K13 (ascii-64MiB-io-scan.candidate.c:2325 @ 404390)
  0.00      6.52     0.00    87388     0.00     0.00  span_fade (ascii-64MiB-io-scan.candidate.c:1027 @ 401e20)
  0.00      6.52     0.00      238     0.00     0.00  WL_FID_CLO_APPLY (ascii-64MiB-io-scan.candidate.c:2923 @ 405ce0)
  0.00      6.52     0.00      133     0.00     0.00  str_reserve (ascii-64MiB-io-scan.candidate.c:1300 @ 4060a0)
  0.00      6.52     0.00       63     0.00     0.00  WL_FID_ENTER (ascii-64MiB-io-scan.candidate.c:2894 @ 403400)
  0.00      6.52     0.00       63     0.00     0.00  WL_FID_EXIT (ascii-64MiB-io-scan.candidate.c:2937 @ 405e40)
  0.00      6.52     0.00       63     0.00     0.00  corpus_eval (ascii-64MiB-io-scan.candidate.c:3688 @ 401242)
  0.00      6.52     0.00       56     0.00     0.00  WL_FID_IO_BIND (ascii-64MiB-io-scan.candidate.c:2387 @ 404b50)
  0.00      6.52     0.00       56     0.00     0.00  WL_FID_IO_BIND_C50 (ascii-64MiB-io-scan.candidate.c:2403 @ 404bc0)
  0.00      6.52     0.00       56     0.00     0.00  WL_FID_IO_BIND_K51 (ascii-64MiB-io-scan.candidate.c:2427 @ 404c90)
  0.00      6.52     0.00       49     0.00     0.00  io_exec (ascii-64MiB-io-scan.candidate.c:4033 @ 4079b0)
  0.00      6.52     0.00       49     0.00     0.00  io_mem (ascii-64MiB-io-scan.candidate.c:3786 @ 400b3a)
  0.00      6.52     0.00       42     0.00     0.00  heap_alloc_miss (ascii-64MiB-io-scan.candidate.c:768 @ 401009)
  0.00      6.52     0.00       21     0.00     0.00  WL_FID_BENCH_MARK (ascii-64MiB-io-scan.candidate.c:2819 @ 4059e0)
  0.00      6.52     0.00       21     0.00     0.00  bench_mark_run (ascii-64MiB-io-scan.candidate.c:4547 @ 400650)
  0.00      6.52     0.00       21     0.00     0.00  io_cstr (ascii-64MiB-io-scan.candidate.c:3899 @ 400839)
  0.00      6.52     0.00       21     0.00     0.00  io_step (ascii-64MiB-io-scan.candidate.c:4356 @ 401b70)
  0.00      6.52     0.00       21     0.00     0.00  io_sync (ascii-64MiB-io-scan.candidate.c:3882 @ 400ed3)
  0.00      6.52     0.00       14     0.00     0.00  WL_FID_IO_PASS_C34 (ascii-64MiB-io-scan.candidate.c:2357 @ 404a60)
  0.00      6.52     0.00       14     0.00     0.00  WL_FID_U32_SHOW (ascii-64MiB-io-scan.candidate.c:2265 @ 404140)
  0.00      6.52     0.00       14     0.00     0.00  WL_FID_U32_SHOW_GO (ascii-64MiB-io-scan.candidate.c:2175 @ 403be0)
  0.00      6.52     0.00       14     0.00     0.00  io_out (ascii-64MiB-io-scan.candidate.c:3876 @ 400baf)
  0.00      6.52     0.00       14     0.00     0.00  io_wait (ascii-64MiB-io-scan.candidate.c:4043 @ 401850)
  0.00      6.52     0.00       14     0.00     0.00  io_work (ascii-64MiB-io-scan.candidate.c:4012 @ 4021f0)
  0.00      6.52     0.00       14     0.00     0.00  str_append_take (ascii-64MiB-io-scan.candidate.c:1355 @ 406a40)
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_FILE_CLOSE (ascii-64MiB-io-scan.candidate.c:2865 @ 405b80)
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_FILE_OPEN (ascii-64MiB-io-scan.candidate.c:2833 @ 405a60)
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_FILE_READ (ascii-64MiB-io-scan.candidate.c:2849 @ 405af0)
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_IO_EMIT (ascii-64MiB-io-scan.candidate.c:2913 @ 405c80)
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_IO_PRINT (ascii-64MiB-io-scan.candidate.c:2879 @ 405c00)
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_IO_TRY_C56 (ascii-64MiB-io-scan.candidate.c:2496 @ 404e20)
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_IO_TRY_C57 (ascii-64MiB-io-scan.candidate.c:2509 @ 404e50)
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_MAIN (ascii-64MiB-io-scan.candidate.c:2440 @ 404cb0)
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_MAIN_C53 (ascii-64MiB-io-scan.candidate.c:2449 @ 404ce0)
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_MAIN_C54 (ascii-64MiB-io-scan.candidate.c:2463 @ 404d40)
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_MAIN_C55 (ascii-64MiB-io-scan.candidate.c:2473 @ 404d70)
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_MAIN_C58 (ascii-64MiB-io-scan.candidate.c:2546 @ 405000)
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_MAIN_C59 (ascii-64MiB-io-scan.candidate.c:2558 @ 405060)
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_MAIN_C60 (ascii-64MiB-io-scan.candidate.c:2574 @ 4050e0)
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_MAIN_C61 (ascii-64MiB-io-scan.candidate.c:2614 @ 405290)
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_MAIN_C62 (ascii-64MiB-io-scan.candidate.c:2640 @ 4053a0)
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_MAIN_C63 (ascii-64MiB-io-scan.candidate.c:2654 @ 405420)
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_MAIN_C64 (ascii-64MiB-io-scan.candidate.c:2672 @ 4054d0)
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_MAIN_C65 (ascii-64MiB-io-scan.candidate.c:2685 @ 405530)
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_MAIN_C66 (ascii-64MiB-io-scan.candidate.c:2702 @ 4055e0)
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_MAIN_C68 (ascii-64MiB-io-scan.candidate.c:2740 @ 405710)
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_MAIN_C69 (ascii-64MiB-io-scan.candidate.c:2759 @ 4057d0)
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_MAIN_K67 (ascii-64MiB-io-scan.candidate.c:2726 @ 405690)
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_MAIN_K70 (ascii-64MiB-io-scan.candidate.c:2782 @ 405890)
  0.00      6.52     0.00        7     0.00     0.00  WL_FID_MAIN_K71 (ascii-64MiB-io-scan.candidate.c:2805 @ 405940)
  0.00      6.52     0.00        7     0.00     0.00  file_close_run (ascii-64MiB-io-scan.candidate.c:4631 @ 4024c0)
  0.00      6.52     0.00        7     0.00     0.00  file_open_call (ascii-64MiB-io-scan.candidate.c:4576 @ 4022c0)
  0.00      6.52     0.00        7     0.00     0.00  file_open_pack (ascii-64MiB-io-scan.candidate.c:4580 @ 402160)
  0.00      6.52     0.00        7     0.00     0.00  file_open_run (ascii-64MiB-io-scan.candidate.c:4586 @ 4006d0)
  0.00      6.52     0.00        7     0.00     0.00  file_read_call (ascii-64MiB-io-scan.candidate.c:4606 @ 402350)
  0.00      6.52     0.00        7     0.00     0.00  file_read_pack (ascii-64MiB-io-scan.candidate.c:4611 @ 4023a0)
  0.00      6.52     0.00        7     0.00     0.00  file_read_run (ascii-64MiB-io-scan.candidate.c:4618 @ 400ad0)
  0.00      6.52     0.00        7     0.00     0.00  heap_hand (ascii-64MiB-io-scan.candidate.c:758 @ 400f4a)
  0.00      6.52     0.00        7     0.00     0.00  io_loop (ascii-64MiB-io-scan.candidate.c:4393 @ 400cae)
  0.00      6.52     0.00        7     0.00     0.00  io_print (ascii-64MiB-io-scan.candidate.c:4642 @ 400b70)
  0.00      6.52     0.00        7     0.00     0.00  io_print_run (ascii-64MiB-io-scan.candidate.c:4647 @ 400c10)
  0.00      6.52     0.00        7     0.00     0.00  io_spawn (ascii-64MiB-io-scan.candidate.c:3855 @ 4017e0)
  0.00      6.52     0.00        7     0.00     0.00  io_str (ascii-64MiB-io-scan.candidate.c:3937 @ 402e20)
  0.00      6.52     0.00        7     0.00     0.00  pool_stack (ascii-64MiB-io-scan.candidate.c:3219 @ 403310)
profile run 1
9586981:1707099817
BENCH {"phase":0,"ns":190817853316489}
BENCH {"phase":1,"ns":190818019237868}
BENCH {"phase":3,"ns":190819421281877}
	Command being timed: "profile/candidate --gpu off --threads 1"
	User time (seconds): 1.44
	System time (seconds): 0.12
	Percent of CPU this job got: 99%
	Elapsed (wall clock) time (h:mm:ss or m:ss): 0:01.58
	Average shared text size (kbytes): 0
	Average unshared data size (kbytes): 0
	Average stack size (kbytes): 0
	Average total size (kbytes): 0
	Maximum resident set size (kbytes): 329844
	Average resident set size (kbytes): 0
	Major (requiring I/O) page faults: 0
	Minor (reclaiming a frame) page faults: 82079
	Voluntary context switches: 5
	Involuntary context switches: 165
	Swaps: 0
	File system inputs: 0
	File system outputs: 0
	Socket messages sent: 0
	Socket messages received: 0
	Signals delivered: 0
	Page size (bytes): 4096
	Exit status: 0
profile run 2
9586981:1707099817
BENCH {"phase":0,"ns":190819438268239}
BENCH {"phase":1,"ns":190819608392692}
BENCH {"phase":3,"ns":190821055246438}
	Command being timed: "profile/candidate --gpu off --threads 1"
	User time (seconds): 1.50
	System time (seconds): 0.11
	Percent of CPU this job got: 99%
	Elapsed (wall clock) time (h:mm:ss or m:ss): 0:01.63
	Average shared text size (kbytes): 0
	Average unshared data size (kbytes): 0
	Average stack size (kbytes): 0
	Average total size (kbytes): 0
	Maximum resident set size (kbytes): 329496
	Average resident set size (kbytes): 0
	Major (requiring I/O) page faults: 0
	Minor (reclaiming a frame) page faults: 82084
	Voluntary context switches: 8
	Involuntary context switches: 137
	Swaps: 0
	File system inputs: 0
	File system outputs: 0
	Socket messages sent: 0
	Socket messages received: 0
	Signals delivered: 0
	Page size (bytes): 4096
	Exit status: 0
profile run 3
9586981:1707099817
BENCH {"phase":0,"ns":190821070743339}
BENCH {"phase":1,"ns":190821248067692}
BENCH {"phase":3,"ns":190822660190436}
	Command being timed: "profile/candidate --gpu off --threads 1"
	User time (seconds): 1.46
	System time (seconds): 0.12
	Percent of CPU this job got: 98%
	Elapsed (wall clock) time (h:mm:ss or m:ss): 0:01.60
	Average shared text size (kbytes): 0
	Average unshared data size (kbytes): 0
	Average stack size (kbytes): 0
	Average total size (kbytes): 0
	Maximum resident set size (kbytes): 329656
	Average resident set size (kbytes): 0
	Major (requiring I/O) page faults: 0
	Minor (reclaiming a frame) page faults: 82078
	Voluntary context switches: 5
	Involuntary context switches: 294
	Swaps: 0
	File system inputs: 0
	File system outputs: 0
	Socket messages sent: 0
	Socket messages received: 0
	Signals delivered: 0
	Page size (bytes): 4096
	Exit status: 0
profile run 4
9586981:1707099817
BENCH {"phase":0,"ns":190822675259866}
BENCH {"phase":1,"ns":190822843072208}
BENCH {"phase":3,"ns":190824268368300}
	Command being timed: "profile/candidate --gpu off --threads 1"
	User time (seconds): 1.33
	System time (seconds): 0.25
	Percent of CPU this job got: 98%
	Elapsed (wall clock) time (h:mm:ss or m:ss): 0:01.61
	Average shared text size (kbytes): 0
	Average unshared data size (kbytes): 0
	Average stack size (kbytes): 0
	Average total size (kbytes): 0
	Maximum resident set size (kbytes): 329572
	Average resident set size (kbytes): 0
	Major (requiring I/O) page faults: 0
	Minor (reclaiming a frame) page faults: 82076
	Voluntary context switches: 5
	Involuntary context switches: 269
	Swaps: 0
	File system inputs: 0
	File system outputs: 0
	Socket messages sent: 0
	Socket messages received: 0
	Signals delivered: 0
	Page size (bytes): 4096
	Exit status: 0
profile run 5
9586981:1707099817
BENCH {"phase":0,"ns":190824286293762}
BENCH {"phase":1,"ns":190824455290859}
BENCH {"phase":3,"ns":190825884115015}
	Command being timed: "profile/candidate --gpu off --threads 1"
	User time (seconds): 1.48
	System time (seconds): 0.11
	Percent of CPU this job got: 98%
	Elapsed (wall clock) time (h:mm:ss or m:ss): 0:01.61
	Average shared text size (kbytes): 0
	Average unshared data size (kbytes): 0
	Average stack size (kbytes): 0
	Average total size (kbytes): 0
	Maximum resident set size (kbytes): 329720
	Average resident set size (kbytes): 0
	Major (requiring I/O) page faults: 0
	Minor (reclaiming a frame) page faults: 82076
	Voluntary context switches: 5
	Involuntary context switches: 235
	Swaps: 0
	File system inputs: 0
	File system outputs: 0
	Socket messages sent: 0
	Socket messages received: 0
	Signals delivered: 0
	Page size (bytes): 4096
	Exit status: 0
profile run 6
9586981:1707099817
BENCH {"phase":0,"ns":190825905127196}
BENCH {"phase":1,"ns":190826084308687}
BENCH {"phase":3,"ns":190827483851226}
	Command being timed: "profile/candidate --gpu off --threads 1"
	User time (seconds): 1.45
	System time (seconds): 0.13
	Percent of CPU this job got: 99%
	Elapsed (wall clock) time (h:mm:ss or m:ss): 0:01.60
	Average shared text size (kbytes): 0
	Average unshared data size (kbytes): 0
	Average stack size (kbytes): 0
	Average total size (kbytes): 0
	Maximum resident set size (kbytes): 329844
	Average resident set size (kbytes): 0
	Major (requiring I/O) page faults: 0
	Minor (reclaiming a frame) page faults: 82078
	Voluntary context switches: 5
	Involuntary context switches: 298
	Swaps: 0
	File system inputs: 0
	File system outputs: 0
	Socket messages sent: 0
	Socket messages received: 0
	Signals delivered: 0
	Page size (bytes): 4096
	Exit status: 0
profile run 7
9586981:1707099817
BENCH {"phase":0,"ns":190827506686911}
BENCH {"phase":1,"ns":190827686064104}
BENCH {"phase":3,"ns":190829109460167}
	Command being timed: "profile/candidate --gpu off --threads 1"
	User time (seconds): 1.48
	System time (seconds): 0.12
	Percent of CPU this job got: 99%
	Elapsed (wall clock) time (h:mm:ss or m:ss): 0:01.62
	Average shared text size (kbytes): 0
	Average unshared data size (kbytes): 0
	Average stack size (kbytes): 0
	Average total size (kbytes): 0
	Maximum resident set size (kbytes): 329864
	Average resident set size (kbytes): 0
	Major (requiring I/O) page faults: 0
	Minor (reclaiming a frame) page faults: 82078
	Voluntary context switches: 5
	Involuntary context switches: 294
	Swaps: 0
	File system inputs: 0
	File system outputs: 0
	Socket messages sent: 0
	Socket messages received: 0
	Signals delivered: 0
	Page size (bytes): 4096
	Exit status: 0
```

</details>

```text
base /tmp/bend-strings-slice5-final: preprocessed SHA256 723f4d9968db3b832da3b6b20aec5942443388fc7855e79f8c2fcb44a6180808
base /tmp/bend-strings-slice5-acceptance: preprocessed SHA256 723f4d9968db3b832da3b6b20aec5942443388fc7855e79f8c2fcb44a6180808
base: profiled-source and acceptance-source preprocessed C are identical
candidate /tmp/bend-strings-slice5-final: preprocessed SHA256 c5fd5e87f4d90685c802f77508d0f5d5c62b1bac3dcf9ca971e9891150482c29
candidate /tmp/bend-strings-slice5-acceptance: preprocessed SHA256 c5fd5e87f4d90685c802f77508d0f5d5c62b1bac3dcf9ca971e9891150482c29
candidate: profiled-source and acceptance-source preprocessed C are identical
```

```text
tests/strings/bench.sh: OK
tests/strings/bench_words.bend: OK
bend2/base.bend: OK
bend2/comp.ts: OK
NVIDIA GeForce RTX 3090, 580.119.02, 24576 MiB
```
