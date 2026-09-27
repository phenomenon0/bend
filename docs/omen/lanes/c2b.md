# c2b — widen the loads: the blocker is the wrap, not `blk_ptr`

Outcome: **no change to `bend2/comp.ts`.** The brief's hypothesis, that
`blk_ptr`'s `may_alias` cast hides the array bounds from clang, is refuted by
measurement. The whole blocked-row gap is `blk_at`'s index mask, which is how
Bend implements its **defined** wrapping semantics for indexes (GUIDE.md: "Indexes
wrap around"; base.bend `Array.get.at`: `U32.and(i, U32.sub(n, 1))`). Removing
the mask widens the loads and closes the gap to C (0.04s vs 0.042s), but it
changes results for out-of-range indexes, so it is not shippable. None of the
semantics-preserving forms I tried widened anything. Acceptance item 4 applies:
this reports the honest residual and ships nothing.

## 1. Baseline (tip 81f12fc5, clang 21.1.7, load ~5.9)

    bench           C  bend-1T bend-16T    1T/C  1T/16T
    gemv        0.153    0.158    0.157   1.03x   1.00x
    split       0.151    0.158    0.169   1.04x   0.94x
    blocked     0.042    0.110    0.107   2.60x   1.02x

## 2. The probes

Method: emit `demos/tensor/bench_blocked.bend` to C, change one thing in the
emitted C, build it the way `bend` does (`clang -std=c11 -O3 … -lpthread -lm`),
count packed moves in `objdump -d`, and take the median of three `--threads 1`
runs. All variants print a byte-identical 4-line output (md5 `6507528b…`). For
this bench that is expected, because it never indexes out of range, so the
identical output is not evidence that the unsafe variant B is safe.

| variant | change in emitted C | safe? | packed moves | 1T time |
|---|---|---|---|---|
| tip | — | yes | 299 | 0.10s |
| A | `u32a` without `may_alias` | yes | 299 | 0.10s |
| R | A + `blk_ptr` through `u32* __restrict` + `__builtin_assume_aligned(H+loc,16)` | yes | 299 | 0.10s |
| F1 | `blk_at`: `i <= m ? i : i & m` | yes | 46 | 0.17s |
| F2 | `blk_at`: `if (expect(i > m, 0)) return cold_wrap(i)`; else `i` | yes | 138 | 0.11s |
| **B** | `blk_at`: `return i << lgs` (mask removed) | **no** | 3886 | **0.04s** |

clang's `-Rpass-analysis=loop-vectorize` output agrees. "loop not vectorized:
cannot identify array bounds" at `blk_ptr` fires **256** times at tip and
**0** times in B. The remark points at `blk_ptr` because that is where the
masked index gets dereferenced. The cast is not the cause: A and R keep the
cast's provenance clean and change nothing.

## 3. Mechanism: what the vectorizer wanted

The blocked row is widened by the **SLP** vectorizer, not the loop vectorizer.
Each strict-FP accumulator chain forbids vectorizing across iterations, so SLP
packs the four lanes `s0..s3` of one iteration instead. To turn four scalar
loads into one `movups`, SLP needs their addresses to be provably consecutive:
`base + at(p+k)` for `k = 0..3`. With the wrap, `at(p+k) = (p+k) & m`. SCEV
cannot model `and`, and the claim `((p+k) & m) == (p & m) + k` is false when
`p+k` crosses the block's end. So SLP falls back to a gather: one `and`, one
`lea` and one `movss` per element, then `unpcklps` to stitch the vector.

Tip, the hot loop (the `and %eax` is the mask, once per element):

```asm
and    %eax,%r10d
lea    0x100002(%r8),%edx
and    %eax,%edx
...
movss  (%rcx,%r10,4),%xmm2
movss  (%rcx,%rbp,4),%xmm3
unpcklps %xmm2,%xmm3
movss  (%rcx,%rdx,4),%xmm2
movss  (%rcx,%r9,4),%xmm4
unpcklps %xmm2,%xmm4
mulps  %xmm3,%xmm4
addps  %xmm4,%xmm0
```

B, the same loop (the loads widen, and so does the `map` loop below it):

```asm
movups -0x10(%rsi,%r9,1),%xmm2
movups (%rsi,%r9,1),%xmm3
movups -0x10(%rdx,%r9,1),%xmm4
mulps  %xmm2,%xmm4
addps  %xmm1,%xmm4
...
movups 0xfd0(%rsi,%rdi,4),%xmm1      ; map: 4 x movups / mulps / movups
movups 0xfe0(%rsi,%rdi,4),%xmm2
```

Why the safe forms fail: F1 and F2 guard each element separately, but SLP
needs **one** guard that covers the whole group of four ("`p..p+3` stay in
range"). Guarding each element independently never proves the group is
adjacent. F1 is worse than tip because the select blocks even the arithmetic
widening.

This corrects tensor-view.md §4. The mask **is** the cause on the blocked row.
The earlier "mask is innocent" check used one masked subscript on a plain
`float*` in the loop vectorizer. The blocked row needs four subscripts to be
adjacent in SLP, and that is a different question.

## 4. Residual and where it could go

- The residual is **2.60x on blocked** (gemv/split 1.03–1.04x, unchanged). Its
  size is measured: removing the wrap alone brings 1T from 0.10s to 0.04s, which
  matches C's 0.042s. Nothing else is in the gap.
- A fix needs a **group** range check that the emission can state once, for
  example "if `(p & m) + 3 <= m`, load four at `base + (p & m)`, else four
  wrapped scalars". The four `Array.get`s are emitted into four separate
  `spin_*` functions and only meet after clang inlines them, so no per-access
  change in `blk_at`/`blk_ptr` can express the check. The options are, all
  larger than this lane's "handful of lines" remit:
  1. the emitter recognizes adjacent gets on one array (`p`, `p+1`, …) and
     emits a guarded wide read (comp.ts, a real pass);
  2. a base-level bulk primitive (a 4-wide get, or a dot over a view) that does
     the range check once;
  3. a non-wrapping get in the language (bend.ts, off limits).
- `may_alias` on `u32a` is harmless for the loads: removing it (A) changes
  neither the code nor the time. It needs no change.

## 5. Battery

`bend2/comp.ts` is unchanged, so no code battery was run: there is no
code delta to gate. The repo gate at tip plus this doc: `PASS: 56 / 56`.
