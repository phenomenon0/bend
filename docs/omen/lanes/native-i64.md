# native-i64 lane — the signed 64-bit word as a native number (opus 5, 2026-09-20)

Branch `lane-native-i64`, worktree `bend-work-native-i64`, off `omen`
`5513be61` (the U64 port on the 2.0.18-2.0.21 compiler). Touched:
`bend2/base.bend` (+137, the `I64` block), `bend2/comp.ts` (+64 -23, six
hunks: `WORDS`, `tpl_w64`, the `i64_` family, `OPTIMIZED`, `emit_match`, the
Metal typedef), `tests/base/i64_ops.bend` (new),
`bench/nbench_sig.bend` + `bench/nbench_sigstr.bend` (new: the measurement
and its unregistered control), `gates/repo.ts` + `tests/caps.sh` (two caps
moved at both sites). `bend2/bend.ts` and `bend2/main.ts` untouched.
Nothing pushed.

Read `native-u64.md` first: this lane is its mirror, and everything that
report establishes about `WORDS` / `OPTIMIZED` / `OPERATIONS` being three
separate registrations holds here unchanged. Only the signed layer is new.

## Verdict

| | |
|---|---|
| `I64` is native on the **C** lane | **yes** — a signed compare is one `int64_t` machine compare; zero `CID_I64` in the emitted C |
| `I64` is native on the **JS** lane | **yes** — one BigInt cell; `grep -c '"I64"'` on the emitted JS is **0** |
| four lanes identical | **yes** — `tests/base/i64_ops.bend`, 4 printed lines carrying 20 checks, check / interpret / js / c |
| the win (10M signed test + increment) | C **14,420 ms -> 4.88 ms** (2,955x) · JS **45,452 -> 290 ms** (157x) · interpret **159,917 -> 1,320 ms** (121x) |
| gate | `bun gates/repo.ts` **PASS: 55 / 55** (unchanged denominator — the new files land on existing allow rules) |
| caps | **moved, measured**: base.bend 47,400 -> 48,700; comp.ts 83,600 -> 84,100 |

## Mechanism — what the signed layer actually is

Two's complement is why this lane is small. `add`, `sub`, `mul`, `and`,
`or`, `xor`, `not`, `inc`, the logical shifts and `is_zero` are
**bit-identical** for U64 and I64: the same machine instruction, the same
template. Only four things read the sign:

| op | C | JS |
|---|---|---|
| ordered compare (`is_lt/le/gt/ge`, `cmp`) | `(int64_t)` casts | `BigInt.asIntN(64, …)` |
| `neg` | `((u64)(-(int64_t)($0)))` | `((-$0) & 0xFFFFFFFFFFFFFFFFn)` |
| `shr.s` / `shr.s.n` (arithmetic) | `(int64_t)($0) >> n` | `asUintN(64, asIntN(64, $0) >> n)` |
| `is_neg` | `((int64_t)($0) < 0)` | `(BigInt.asIntN(64, $0) < 0n)` |

Because the shared half is literally shared, the `u64_` family became a
function and the `i64_` family is its second call site:

```ts
  ...tpl_w64("u64_"),
  ...tpl_ops("u64_", CMPS, "((u64)((u64)($0) $o (u64)($1)))", "($0 $o $1)"),
  u64_cmp: { … },
  ...tpl_w64("i64_"),
  ...tpl_ops("i64_", CMPS, "((u64)((int64_t)($0) $o (int64_t)($1)))",
    "(BigInt.asIntN(64, $0) $o BigInt.asIntN(64, $1))"),
  i64_cmp: { … }, i64_neg: { … }, i64_shr_s: { … },
  i64_shr_s_n: { … }, i64_is_neg: { … },
```

`tpl_w64` is not a new abstraction invented for two hypothetical users: it
is the *statement* that the bit-level 64-bit ops are sign-agnostic, and it
makes the upstream diff read as one change rather than two copies of the
same table. It also absorbed `u64_mul`, whose separate entry was already
identical to the `add:+ sub:- and:& or:| xor:^` group's template with
`$o = *` — U32 needs its own `mul` for `Math.imul`, U64 and I64 do not. Net
effect on `comp.ts`: the whole signed family costs **+486 ttok**, less than
the U64 family cost on its own.

### The bias, and where it goes

`bend-i64`'s pure-Bend spec compares signed by biasing both operands with
the sign bit (`x XOR 2^63`) and then doing an unsigned compare. That is what
`base.bend` says, because `base.bend` is what the theory and the
interpreter's structural path see:

```
def I64.cmp(a: I64, b: I64) -> Cmp:
  match a b:
    case I64{x} I64{y}:
      Word.cmp(64n, Word.xor(64n, x, I64.sign_mask()),
        Word.xor(64n, y, I64.sign_mask()))
```

The bias never survives to a native lane. `intr_of` replaces the whole def
with `OPERATIONS["i64_cmp"]`, so the bias — two XORs over a 64-cell word
plus a bit-walking `Word.cmp` — collapses into one `int64_t` comparison.
That collapse is the 2,955x in the table, and it is the reason the bench
measures the sign test rather than the increment: `inc` is shared with U64
and was already measured there.

`I64.sign_mask()` is `Word.not(64n, Word.shr(64n, Word.not(64n,
Word.zero(64n))))` — all ones, shifted right, negated, i.e. `2^63`. It needs
no `OPERATIONS` entry: it exists only for the structural bodies, and no
native lane ever calls it.

### Affinity forced one `+`

Bend is affine, and `shr.s` reads its argument twice — once to test the
sign, once to shift. Base's existing answer is the duplicable marker
(`U32.div(a: U32, +b: U32)`, `Nat.max(+a: Nat, +b: Nat)`), so:

```
def I64.shr.s(+a: I64) -> I64:
  I64.shr.s.put(I64.is_neg(a), I64.shr(a))
```

The same `+` appears on the bench loops' accumulator, for the same reason.

### Metal needed a typedef

`int64_t` is in `<stdint.h>` on the host and is typedef'd explicitly for
CUDA's RTC, but the `__METAL_VERSION__` branch defined only `ulong u64`.
One line, mirroring the CUDA branch:

```c
 #ifdef __METAL_VERSION__
 typedef ulong u64;
+typedef long  int64_t;
```

**Not verified on hardware**: this machine is x86_64 with no Metal
toolchain, so the Metal lane's I64 is argued from `long` being MSL's signed
64-bit type, not measured. The gate's minis are the place that gets checked.

### Naming

Base's U64 spells the counted shifts `shln` / `shrn`, and I64 mirrors that
for the logical ones. The arithmetic shift is `I64.shr.s` / `I64.shr.s.n`,
where the trailing `.s` is a qualifier on `shr` in the style of Base's own
`Word.shl.put` / `Word.shl.out`. `eff_name` flattens these to `i64_shr_s`
and `i64_shr_s_n`.

Two deviations from the lane brief, both deliberate. It named the counted
logical shift `I64.shl.n` -> `i64_shl_n`; Base's U64 block spells it `shln`
and conformance to the neighbouring block wins. And it listed four new
`OPERATIONS` entries; there are five, because `i64_shr_s_n` has to be native
too or the counted arithmetic shift would be the only op in the family that
falls back to a Nat recursion over a native one.

## Numbers (this machine, medians)

x86_64, 16 cores, Fedora 43, clang 21, bun, node. Medians of five runs
(three for the interpreter), wall clock around the whole process, taken
2026-09-20 from 17:29 local. **Load average was 4.2-5.4** — higher than the
U64 lane's 1.8-2.0, because sibling worktrees were building; the spreads
below are tight enough (the C native run spanned 4.80-4.99 ms over five)
that the medians still mean something, but the absolute floors are a touch
slower than that report's.

10M iterations of `bump(I64.is_neg(acc), acc)` — a signed sign-test plus an
increment. `bench/nbench_sig.bend` is the measurement;
`bench/nbench_sigstr.bend` is its control: `T64`, the same
`type T64{data: Word(64n)}` with the same signed bodies, declared locally
and therefore **not** in `WORDS` / `OPTIMIZED` — exactly what `I64` was
before this lane.

| | C | JS | interpret |
|---|---|---|---|
| empty main (process floor) | 0.70 ms | 14.89 ms | 233 ms |
| `I64` x10M — **native** | **4.88 ms** | **290 ms** | **1,320 ms** |
| `T64` x10M — structural | 14,420 ms | 45,452 ms | 159,917 ms |
| ratio, net of the floor | **3,450x** | **165x** | **147x** |

Unlike the U64 lane's `inc` bench, the C number here is **not** the process
floor: 4.88 ms against a 0.70 ms empty main is 4.18 ms of measured work, so
LLVM did not close this loop — the branch on the sign keeps it alive. That
makes this the better of the two measurements: it is real work, timed, not
a fold.

The JS lane's 157x is far larger than U64's 1.3x, and for a reason worth
stating: U64's `inc` bench traded a 64-cell `Word` spine for a heap BigInt
and gained little, whereas the structural *signed test* costs four
width-64 traversals per iteration (two `Word.not`, a `Word.shr`, a
`Word.cmp`) and the native one costs an `asIntN` and a compare. The gain
scales with how much bit-walking the op replaces, not with the lane.

The interpreter moves by 121x for the same reason, which also confirms it
takes the native path: a structural interpret of this loop needs 160
seconds.

## Evidence

- `tests/base/i64_ops.bend` on check / interpret / js / c — the same four
  lines on every lane:
  ```
  checks 20/20
  asr32 3221225472
  ones47 140737488355327
  I64-END
  ```
  The twenty checks are the `bend-i64` demo's seven signed cases
  (`neg(1) == -1`, `-1 + 1 == 0`, `neg(min) == min`, **signed `min < max`**,
  `min >>s 1 == -2^62`, `is_neg(min)`, `not is_neg(max)`) plus the rest of
  the family and the two width probes.
- **Three negative controls**, each a one-template pin on the C lane, which
  is what makes 20/20 a claim rather than a decoration:

  | control | checks | printed |
  |---|---|---|
  | none (the lane as landed) | 20/20 | `asr32 3221225472`, `ones47 140737488355327` |
  | `i64_` CMPS pinned **unsigned** | **17/20** | unchanged |
  | `i64_shr_s`/`_n` pinned **logical** | **18/20** | `asr32` **1073741824** |
  | `term_word` pinned to **32** | **19/20** | `ones47` **32767** |

  The unsigned pin drops exactly `is_lt(min, max)`, `is_gt(max, min)` and
  `is_ge(max, min)` — the three places where unsigned order disagrees with
  signed — and leaves `is_le(min, min)` and `is_ne(min, max)` passing,
  which is the right answer for a wrong compare.
- the emitted JS for that test contains **zero** `"I64"` nodes; the emitted
  C contains **46** `(int64_t)` casts over 24 lines and no `CID_I64`. The
  only `I64` symbols left in the C are `FID_I64_SIGN_MASK` and its four
  continuations -- the structural mask helper, which no native lane calls.
- the full battery, serial, on the lane tip. `base.bend` changed, so
  everything downstream of it ran:

  | suite | result |
  |---|---|
  | `bun gates/repo.ts` | PASS 55 / 55 |
  | `bash tests/caps.sh` | ok — 48,648 / 48,700 and 84,045 / 84,100 |
  | `bash tests/run.sh` (f64, four lanes) | PASS 19, FAIL 0 |
  | `bash tests/strings/run.sh` | PASS 102, FAIL 0 |
  | `bash tests/translator/run.sh` | PASS 40, FAIL 0 |
  | `bash tests/regex/run.sh` | PASS 49, FAIL 0 |
  | `bash tests/lint/run.sh totality` | PASS 20, FAIL 0 |
  | `bash tests/lint/run.sh alias` | PASS 16, FAIL 0 |
  | `bash tests/lint/run.sh coverage` | PASS 20, FAIL 0 |
  | `bash tests/lint/run.sh modules` | PASS 20, FAIL 0 |
  | `bash tests/parser/run.sh` | PASS 108, FAIL 0 |
  | `bash tests/codex/run.sh` | 161 PASS, 0 FAIL, 0 suite errors |
  | `bash tests/power/run.sh` | PASS 150, FAIL 0 |
  | `tests/base/*.bend`, four lanes | 100 / 116, against 96 / 112 pristine |

- `tests/base/u64_ops.bend` still **15/15** on all four lanes after the
  `tpl_w64` refactor: the U64 family's templates are byte-identical
  through the shared function, `u64_mul` included.
- both bench programs print `10000000` on C and on JS before any clock was
  read: a timing run that disagreed on the answer would not be a
  measurement.

### Two things in that table that are not what they look like

**Power needed a Python fix, not a Bend one.** The first power run answered
`PASS: 149, FAIL: 1`, the one being `FAIL assign [oracle] status=1`.
`run.sh:78` runs each specimen's CPython oracle as bare
`python3 tests/power/<name>_gen.py`, and `assign_gen.py` — the only
generator that does — imports `numpy` and `scipy`, neither of which this
machine's system python3 has. `assign_gen.py` is byte-identical to HEAD and
untouched by this lane; it fails the same way on a pristine `git archive
HEAD` tree; and all five of `assign`'s own Bend lanes (check, interpret, js,
c, c-1thread) pass in both runs. With a throwaway venv first on PATH the
oracle reproduces `tests/power/assign.bend` byte for byte and power is
**150 / 0**. The user's python was not modified.

**The base sweep's 16 are the harness's, not the lane's.** Four specimens —
`bytes_ops`, `heap_queue_deque`, `json`, `parser` — are *negative*: their
`#|` block is an `Error: - expected : a defined name` message pinning
`Bytes.encode`, `Deque.push_front`, `JSON.read` and `Parser.digits` as
undefined. `gates/test.ts` knows this (`test_probes` returns `["check"]`
alone when `want` starts with `Error:`); the throwaway local sweep used here
does not, and runs them on four lanes each. 4 x 4 = the 16. The number that
matters is the delta: the same sweep on the pristine tree gives **96 / 112**
with exactly the same sixteen, so this lane adds four passes —
`i64_ops.bend` on check, interpret, js and c — and no failures.

### A thing the `term_word` control revealed

Pinning the packer to 32 breaks `ones47` and check 14 but leaves `i_min`
(`I64{I64.sign_mask()}`) intact at `2^63`. That is not a flaky control — the
two constructors take different roads. A word that arrives as a heap `WCon`
spine (`I64{Word.not(64n, Word.zero(64n))}`, written inline) goes through
`term_word`; a word returned from a call arrives **flat in 64 registers**
(`FID_I_MIN_K34` takes `r0..r63`) and is reassembled by the layout, which
reads `WORDS` and was never width-pinned. So the control probes the
heap-spine boundary only — which is precisely the boundary the U64 lane
fixed.

## The cap move

Both files were already within 23 and 41 ttok of their caps, so any landing
is a move. It is a **measured** move, at both cap sites (`gates/repo.ts`
and `tests/caps.sh`).

| file | before | after | cap before | cap after | headroom |
|---|---|---|---|---|---|
| `bend2/base.bend` | 47,377 | 48,648 | 47,400 | 48,700 | 52 |
| `bend2/comp.ts` | 83,559 | 84,045 | 83,600 | 84,100 | 55 |

base.bend's +1,271 is the deliverable: a type, 24 ops and one helper. It
carries no `add_comm` law, no `div`, no `mod`, no `show`, no `read` and no
`to_nat` — the same austerity as the U64 block. comp.ts's +486 is smaller
than U64's own +490 despite adding a whole second family, because
`tpl_w64` paid for the new entries out of the old duplication.

## The upstream diff surface — U64 and I64 as one change

The proposal should read as **one** feature, "the 64-bit word as a native
number, unsigned and signed", not two. Ordered:

1. **`term_word` takes its width** + **`emit_match` reads `WORDS[adt.k]`** —
   the two pre-existing width bugs from the U64 lane. Still the right thing
   to offer first and alone: they fix silent truncation for every `w64` ADT,
   `F64` included, with no new type in sight.
2. **`WORDS` gains `U64: W64, I64: W64`** — one line.
3. **`OPTIMIZED` gains `U64` and `I64`** — sixteen lines, the JS lane's half
   of 2. Both entries are the same pair of conversions: the cell holds the
   raw unsigned bit pattern either way, and signedness lives in the ops.
4. **`emit_match`'s word predicate admits both.**
5. **`tpl_w64` + the `u64_` and `i64_` families in `OPERATIONS`** — the
   feature. Presenting the shared function first makes the signed half read
   as five extra entries instead of a second copy of the table.
6. **`typedef long int64_t` for Metal.**
7. **the `U64` and `I64` blocks in `base.bend`**, with
   `tests/base/u64_ops.bend` and `tests/base/i64_ops.bend`.

Not part of that surface, and this repo's bookkeeping only:
`bench/nbench*.{bend,c}`, the cap moves, and `docs/omen/`. The bench files
sit at `bench/` root rather than `bench/runtime/<name>/` for the reason the
U64 report gives: `gates/perf.ts` readdirs `bench/runtime` and grades every
dir it finds against an `apple_m4` pin this x86 machine cannot produce.

## Gaps found, deliberately not fixed

- **`main -> I64` crashes the printer on the C lane**, exactly as
  `main -> U64` and `main -> F64` do: `show_main`'s kind map has no entry,
  so it falls to kind 7 and dereferences `lay.arms![j]` on a `W64` lay whose
  `arms` is `null` — `TypeError: null is not an object`. Verified on this
  tip for I64; **pre-existing**, documented in `native-u64.md`, and it needs
  one lane that fixes all three at once. The interpreter prints it fine (as
  a 64-deep `WCon` spelling), and the tests print through `Nat.show`.
- **There is no `I64` literal**, and no `from_nat` / `to_nat`. Same gap as
  U64's, same shape of fix, same reason for not taking it here: both files
  are at their new caps.
- **No `div` / `mod`**, hence no `i64_div` / `i64_mod`. Signed division is
  not a retyped copy of the unsigned one — C truncates toward zero and the
  `INT64_MIN / -1` case traps — so it wants its own lane, not a line in
  this table.
- **No `add_comm` law.** The `bend-i64` package proves it by instantiating
  `Word.add_comm(64n, …)` and it transfers to the signed reading unchanged,
  since addition ignores the sign. It is left in the package for the same
  reason U64's is: the Base blocks carry no laws.
