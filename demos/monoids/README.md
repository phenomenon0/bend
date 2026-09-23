# demos/monoids — sequential in disguise

Three loops that every textbook writes one element at a time. Each one hides
an associative summary. Once you find it, Bend's fork tree runs the loop, and
the answer carries the sequential program's bits at any split, any
`--threads`, on any lane.

| program | deep dive | the loop | the hidden monoid | summary |
|---|---|---|---|---|
| `utf8.bend` | unicode × parsers | a UTF-8 validator (a DFA) | state→state maps under composition | **one U32**: 8 nibbles |
| `kulisch.bend` | floating point | `sum += x` over F32 | exact fixed-point integer addition | 10 U32 limbs (320 bits) |
| `pcg.bend` | randomness | `x = a*x + c` (PCG32) | affine maps under composition | 2 × 64-bit |

The rule behind all three: a fork leaf must not need the state its left
neighbour leaves behind. Each program swaps "the state" for something that
composes:

- **utf8**: a leaf does not know which DFA state it starts in, so it computes
  where it would end from *each* of the 8 live states (Mytkowicz et al., ASPLOS
  2014). DEAD is absorbing, so a map fits 8 nibbles. The join and the per-byte
  step are the same function. UTF-8 self-synchronizes, so after at most 4
  bytes every live start has converged. Past that point a leaf runs **one**
  DFA and carries which starts are still alive. The byte classifier is a
  telescoping sum over the 13 edges of Unicode table 3-7, with no branches.
  The first bad byte is found by descending the same tree.
- **kulisch**: F32 `+` is not associative, so a reduction that splits
  differently rounds differently (the naive columns below change with the tree
  shape). Every finite F32 is an integer multiple of 2^-149, so a 320-bit
  two's-complement integer holds any sum of up to 2^32 of them *exactly*.
  Integer addition is associative. One correct rounding happens at the root
  (ties to even, carry-out and overflow to inf included).
- **pcg**: the step is an affine map mod 2^64, and k steps are one affine map
  reached by squaring (Brown 1994, `pcg_advance_lcg_64`). A right subtree jumps
  to its exact offset in the **one** stream. The usual fix, one seed per
  worker, changes the answer with the worker count, and the last column shows
  it doing so. The 64-bit arithmetic runs on U32 pairs, so this file runs on a
  stock Bend.

## Oracles

Every `#|` line is printed by `NAME_gen.py`, which rebuilds the same data
(Threefry2x32-20 from the Random123 paper, held to its known-answer vectors).
The verdicts come from somewhere other than the Bend code:

- utf8: CPython's own `bytes.decode("utf-8")`. Validity and code-point count
  come from it, and the dead byte is read off its `UnicodeDecodeError`. A
  reference DFA only cross-checks.
- kulisch: the true sum as a `Fraction`, and the F32 picked among neighbours by
  exact distance. The fixture's naive sums use doubles rounded to F32 after
  each add, which is exactly F32 add (53 >= 2·24 + 2).
- pcg: `pcg_basic.c` transcribed onto Python ints, held to the reference demo's
  first outputs for seed (42, 54). The count is a plain loop.
  `pcg_twin.c` is that loop in C, for the 2^31-draw run.

```bash
demos/monoids/run.sh          # 3 programs x (oracle, interpret, js, c 1 thread, c 4 threads)
BIG=1 demos/monoids/run.sh    # also the *_big runs, timed per thread count
```

## Measured

Measured on a quiet 4-vCPU Xeon @ 2.10 GHz (cloud container, clang -O3,
`--gpu off`), best of 3, on the 2.0.26 sync (`BIG=1 run.sh`). Every row prints
the same line at every thread count.

| run | work | 1 thread | 2 | 4 | speedup | output |
|---|---|---:|---:|---:|---:|---|
| `utf8_big` | 2^28 synthesized bytes, 2^10 leaves | 2.96 s | 1.41 s | 0.77 s | 3.8x | `map=08888888 cps=159382215` |
| `kulisch_big` | 2^26 F32s, 65,536 cancelling giant pairs | 2.16 s | 1.09 s | 0.63 s | 3.4x | `exact 0xbe9ac177` |
| `pcg_big` | 2^31 draws of one stream | 6.05 s | 2.96 s | 1.61 s | 3.8x | `hits 843353130` |

- `pcg_twin.c` (`cc -O2`, one sequential loop) prints the same `hits 843353130`
  in 2.91 s. Bend runs 64-bit math on U32 pairs, which makes it 2.1x slower on one
  thread, but it beats the twin on 4.
- `kulisch_drift.bend`: the naive F32 sum of the same 2^26 values gives
  `0x3bdda8fe` (+0.0068) at 16 leaves and `0x3b0c3ca8` (+0.0021) at 1024. The
  exact sum is -0.302, so the naive sum has the wrong sign, and the tree shape
  moves it.
- About 1.8 s of utf8's 2.96 s is synthesizing the corpus (one Threefry block
  per 4 bytes); the validator itself costs about 1.2 s.

## What Bend asked for

- A def calls only defs above it, and never mutually. Descending to the dead
  byte therefore became one self-recursive def that picks its child with
  `Bool.pick`, not two defs that call each other.
- `match` takes parameters, not computed values. Each "open this result" step
  is a small def, which is also where the carrier records (`Sum`, `Acc`, `W`)
  come from. `U32 & U32` is kind Type and cannot be copied. A `Data` record
  can.
- On random text, the branch chain for a byte class was the hot spot: a
  mispredict per byte. The telescoping form cut the 2^28 run from 4.9 s to
  3.2 s.
