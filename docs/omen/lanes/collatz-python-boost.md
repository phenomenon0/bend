# collatz-python-boost — does the stack boost Python?

**Verdict.** Yes — **14× at one core, ~97× at sixteen, 178× on the Mac's 16** —
but only through the Bend-native channel. Both automated doors refuse the
program for the same root reason from different angles: **ints are outside the
translator's fragment**, and the VM *hosts* ints ~44× slower than CPython under
a step guard. The single missing piece that turns this table into
`collatz.py → collatz.bend → 17–178×`, automatically, is **int support inside
the translation fragment**.

Program: longest Collatz chain ≤ 200,000. Correct answer everywhere: **383**.
Reference: hand-written C, `-O3 -march=native`: **0.02 s**.

| engine | time | vs CPython | note |
|---|---|---|---|
| CPython 3.11 | 2.14 s | 1× | the baseline, as-written |
| translator (Py → Bend) | refused | — | `annotation outside the fragment (str, bool, list[T], T \| None)` |
| VM hosting the .py | refused at 200k | — | fuel guard (`fuel()` = 100M steps); at N=20k: 6.45 s ≈ **44× slower**; raised-fuel variant fail-stops |
| Bend-native · 1 thread (Ryzen) | 0.15 s | **14×** | min-of-5, box noise ±0.02 |
| Bend-native · 16 threads | 0.02–0.06 s | **~60±30×** | contention-sensitive; best observed 0.022 |
| Bend-native · 64 threads | 0.024 s | ~90× | 64 > 16 cores: no gain over 16 |
| Bend-native · CUDA (RTX 3090) | 0.38–0.45 s | slower | launch-bound at this N — needs a bigger problem to stretch |
| Bend-native · 1 thread (M3 Ultra) | 0.080 s | 27× | |
| Bend-native · 16 threads (M3 Ultra) | 0.012 s | **178×** | 793% CPU: real parallelism |
| Bend-native · Metal (M3 Ultra) | 0.42 s | slower | launch-bound, same as CUDA |

**Against C.** 7.5× off single-core — this shape is *pure call overhead* (every
Collatz step is a def call; C inlines it all), the honest weak spot versus the
1.47× single-core geomean on loop/array benches. At 16 threads Bend reaches
**C's single core** — the parallelism lever closing what codegen doesn't. C can
thread too; the real race is Bend-16T vs C-16T, still ahead of us.

**Mechanism.** The Bend program is a depth-10 fork tree over `1..200000` with
`tree!(...)` under a bang; leaves brute small ranges; `fuel` doubles as the
chain-depth bound (max chain < 200k = 383 < 500). Refusal receipts, verbatim:
the translator's fragment is `(str, bool, list[T], T | None)`; the VM's subset
is while-only (`for` refused), annotations refused.

**One catch, kept honest.** First working build printed **500** — the fuel
leaking: `ch` lacked the `n < 2` terminator so chains cycled 1→4→2→1 until the
bound. Fixed, re-verified to 383, *then* trusted.

**Provenance.** Five checker lessons paid en route are distilled into
`docs/omen/plans/bend-idioms.md` (now the preamble of every agent brief).
Files: `demos/python/collatz.py` (original), `collatz.bend` (native),
`collatz.c` (C twin).

**Reproduce.**
```
bun bend2/main.ts demos/python/collatz.bend -o /tmp/collatzb
/tmp/collatzb --gpu off --threads 1      # 383
/tmp/collatzb --gpu off --threads 16
/tmp/collatzb                            # GPU lane
gcc -O3 -march=native -o /tmp/collatz_c demos/python/collatz.c && /tmp/collatz_c
```
