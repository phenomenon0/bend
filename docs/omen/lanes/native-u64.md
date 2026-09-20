# native-u64 lane — the 64-bit word as a native number (opus 5, 2026-09-20)

Branch `lane-native-u64`, worktree `bend-work-native-u64`, off `omen`
`7ca2ed26`. Touched: `bend2/base.bend` (+104, the `U64` block),
`bend2/comp.ts` (+43 -8, six hunks: `WORDS`, the `u64_` family, `OPTIMIZED`,
`emit_ctr`, `emit_match`, `term_word`), `tests/base/u64_ops.bend` (new),
`bench/nbench.bend` + `bench/nbench_str.bend` + `bench/nbench.c` (new: the
measurement, its unregistered control and the machine baseline),
`gates/repo.ts` + `tests/caps.sh` (two caps moved at both sites, plus one
allow line for the three bench files).
`bend2/bend.ts` untouched. `bend2/main.ts` back to its baseline bytes (the
`e.stack` debug patch is reverted). Nothing pushed.

## Verdict

| | |
|---|---|
| `U64` is native on the **C** lane | **yes** — one machine `+`; 1,000,000,000 `U64.inc` in 0.00 s (LLVM closes the counted loop, which is the proof) |
| `U64` is native on the **JS** lane | **yes** — one BigInt cell; the structural 64-cell node is gone |
| four lanes identical | **yes** — `tests/base/u64_ops.bend`, 15 checks + 3 printed lines, check / interpret / js / c |
| the win | structural `Word(64n)` inc: **2,085 ms** / 10M · native: **0.62 ms** = the empty-main floor (0.60 ms) |
| gate | `bun gates/repo.ts` **PASS: 55 / 55** (the count is allow *rules*, not files; 54 before, +1 for the bench line) |
| caps | **moved, measured**: base.bend 46,470 -> 47,400; comp.ts 81,600 -> 82,100 |

## Mechanism — what "native" means here

`WORDS` is the table that says a nominal ADT is carried in a machine slot
instead of a heap node. `U64` joins it as `W64`, alongside `F64` and `Nat`:

```ts
const WORDS: Record<string, Lay> =
  { U32: W32, F32: W32, F64: W64, Nat: W64, U64: W64 };
```

`WORDS` alone is not enough, because the two emitters reach a word-typed ADT
by different roads:

- the **C** emitter reads `WORDS` through `lay_node` in `emit_ctr` /
  `emit_match`, and converts at the boundary (`term_word` in, bit-shifts
  out);
- the **JS** emitter does not read `WORDS` at all. Its native-type table is
  `OPTIMIZED`, whose `intr` is the constructor and whose `elim` is the match.

So a word ADT needs **two** registrations, and `OPERATIONS` needs a third:
the intrinsic templates that make the calls machine ops rather than library
calls. `intr_of` routes a builtin-marked def by `OPERATIONS[eff_name(k)]`,
and base.bend's defs are auto-marked at load, so `U64.add` in the prelude and
`u64_add` in the table are the same function seen from two sides.

The base.bend block mirrors U32's exactly at width 64 — 20 defs, no
`add_comm` law, no `div`/`mod`, no `show`/`read`. The bodies are the
`Word(64n)` structural definitions; they are what runs under `--check-only`
and what the theory sees. `OPERATIONS` is what runs.

## The three bugs and their fixes

### A · the JS lane's constructor built a structural node

`U64{...}` emitted `{$: "U64", ["data"]: ...}` while every `u64_*` JS
template assumed a native BigInt cell, so the first arithmetic threw
`TypeError: Invalid mix of BigInt and other type in bitwise 'and' operation`.

Fix — one `OPTIMIZED` entry, and because that table drives constructor *and*
match, one entry fixes both directions:

```ts
  U64: {
    intr: { U64: "word_to_u64($0)" },
    elim: { U64: ["u64_to_word($0)"] },
  },
```

`word_to_u64` / `u64_to_word` already existed in the emitted JS runtime for
`F64`'s bit-pattern round trip; U64 wants exactly that conversion with no
float reinterpretation on top.

### B · the C lane's constructor packed only 32 bits

`term_word` walked the `Word` spine into a `u32` with `i < 32` hardcoded, so
a constructor handed a structurally built full-width word silently dropped
the top half. Fixed at the root — the function takes its width, and the call
site reads it off the layout:

```ts
      ? `term_word(e, ${ws[0]}, ${lay.ks[0] === "w64" ? 64 : 32})`
```
```c
INLINE Term term_word(Env e, Term w, u32 n) {
  u64 x = 0;
  Term t = w;
  for (u32 i = 0; i < n && term_aux(t) == CID_WCON; i += 1) {
    Loc l = term_peek(e, t);
    x |= (u64)(e.mem[l] & 1) << i;
    t = e.mem[l + 1];
  }
  term_sink(e, w);
  return x;
}
```

This is not a U64 fix: `term_word` is the conversion for every `w64` ADT, so
`F64{...}` over a structurally built word truncated the same way before this
lane. That is reproducible with no U64 in sight — all ones is NaN, and NaN is
the one value not equal to itself:

```
def main() -> IO(Unit):
  do IO<Unit>:
    a : F64 = F64{Word.not(64n, Word.zero(64n))}
    b : F64 = F64{Word.not(64n, Word.zero(64n))}
    IO.print(String.append("nan? ", Bool.show(Bool.not(F64.is_eq(a, b)))))
```

| lane | before | after |
|---|---|---|
| interpret | `nan? True` | `nan? True` |
| c | **`nan? False`** — the low 32 bits are a denormal, equal to itself | `nan? True` |

So the C lane silently disagreed with the interpreter about a value the
theory says is NaN. `tests/run.sh` (the 19-result f64 suite) is green after
the change; the reproducer is not added to it, since that suite's count is
pinned by its own comment.

The bug is invisible to a test whose high bits come from native ops — the
first version of `u64_ops.bend` passed 13/13 with the 32-bit walk restored,
because `U64.not` and `U64.shln` never go through `term_word`. The test now
routes two checks and both printed numbers through a structurally built
all-ones word. **Negative control**, `term_word` pinned back to 32:

```
checks 13/15        <- was 15/15
hi32 0              <- was 4294967295
```

### C · the match's extraction was 32-bit too

`emit_match` recognised only `U32`/`F32` as word-typed and then hardcoded
`W32` when holding the bits, so a 64-bit scrutinee lost its top half on the
way out. Fixed by widening the predicate and reading the width from the same
table the constructor reads:

```ts
  const word = adt.k === "U32" || adt.k === "F32" || adt.k === "U64";
  const lay = word ? lay_node(fl.book, adt.k) : lay_of(fl.book, all.A);
  const bits = word
    ? val_hold(fl, val_to(fl, args[0], WORDS[adt.k]), "u").ws[0] : "";
```

`bit47 140737488355328` (= 2^47) in the test is the read-back that would
fail if extraction were 32-bit; it is printed on all four lanes.

## Numbers (this machine, medians)

x86_64, 16 cores, Fedora 43, clang 21, bun. Medians of five runs (three for
the interpreter), wall clock around the whole process, taken 2026-09-20 at
17:05 local with load average 1.8-2.0 and no competing timed job on the
machine. 10M iterations unless stated.

The three programs ship: `bench/nbench.bend` is the measurement,
`bench/nbench_str.bend` is its control — `S64`, the same
`type S64{data: Word(64n)}` declared locally and therefore *not* in `WORDS` /
`OPTIMIZED`, i.e. exactly what `U64` was before this lane — and
`bench/nbench.c` is the machine baseline.

| | C | JS | interpret |
|---|---|---|---|
| empty main (process floor) | 0.60 ms | 12.5 ms | 229 ms |
| `U64.inc` x10M — **native** | **0.62 ms** (= floor) | **694 ms** | **1,145 ms** |
| `S64.inc` x10M — structural | 2,085 ms | 881 ms | 1,423 ms |
| C control, `clang -O3`, `volatile` counter | 2.49 ms | — | — |

Spreads were tight enough that the medians are not doing much work: the C
native run spanned 0.57-0.63 ms over five, the C structural 2,074-2,134 ms.

The C lane's native number is the floor because once the operation is a
machine `+`, LLVM closes the counted loop — which is the result, not a
measurement artefact to apologise for. The proof that the work is real and
the fold is real is that the fold still computes: **1,000,000,000** `U64.inc`
runs in a median **0.57 ms** — a hundred times the iterations at the same
wall clock — and prints `u64 native sum: 1000000000`, the right answer. At
the structural rate that run would take ~209 seconds. The `volatile` in the C
control is what keeps the control at 2.49 ms rather than at its own floor;
the Bend program has no `volatile` to write, which is the honest asymmetry in
that row.

A fold-resistant microbench is not expressible here, and the reason is
worth recording: **Bend is affine**, so a loop cannot carry a constant
without re-deriving it (`U64.add(a, a)` is refused with `a (consumed more
than once)`), and re-deriving `U64{Word.zero(64n)}` per iteration allocates
64 cells — the bench would measure the allocation. Every affine map
`x -> c*x + d` expressible without a carried constant has `c` even, so it
reaches a fixed point within 64/log2(c) steps. The counted add that *is*
expressible is precisely the shape a compiler closes.

The JS lane's gain is small and honest: 694 vs 881 ms, about 1.3x. A JS
`BigInt` is a heap object, so the lane trades a 64-cell `Word` spine for a
heap BigInt allocated per operation — it removes the structural node without
reaching a machine register, and no `& 0xFFFFFFFFFFFFFFFFn` mask is free
either. The value on this lane is correctness and representation parity with
C, not speed; a JS lane that wanted speed would need `U64` split across two
53-bit doubles, which would not be the same type.

The interpreter lane moves by the same 1.3x (1,423 -> 1,145 ms, and
916 vs 1,194 ms once the 229 ms startup floor is subtracted) for a different
reason: the interpreter's own 10M-iteration `Nat` loop dominates, so the
increment is a minority of the time either way.

## Evidence

- `bun gates/repo.ts` — **PASS: 55 / 55**. The gate's denominator is its
  count of allow *rules*, not of files or tests: it was 54 at `7ca2ed26` and
  is 55 here because this lane adds one allow line for the bench files. An
  earlier draft of this report read that number as a file count and said
  "53 before, the new test is the 54th"; it was wrong, and `tests/base/
  u64_ops.bend` in fact lands on the existing `tests/<ns>/*.bend` rule
  without needing a line of its own.
- `bash tests/run.sh` (f64, four lanes) — **PASS: 19, FAIL: 0**.
- `tests/base/*.bend` (28 files) on check + interpret + js + c locally —
  **100 / 104** probes, and the four that do not match are all the single
  `parser` test, whose expected block carries the cluster harness's `exit 1`
  line that a local plain-interpret run does not print. Checked against the
  pre-lane tree (`git archive 7ca2ed26`): `parser.bend` emits byte-identical
  output there, so those four are the local runner's missing `exit N` line,
  not a regression.
- `tests/base/u64_ops.bend` on check / interpret / js / c:
  ```
  checks 15/15
  hi32 4294967295
  bit47 140737488355328
  U64-END
  ```
- the negative control above (32-bit `term_word` -> `checks 13/15`, `hi32 0`),
  which is what makes the 15 a claim rather than a decoration.
- the emitted JS for that test contains **zero** `"U64"` nodes (`grep -c` is
  0): the whole U64 surface compiled away into BigInt cells and operators.
- `bench/nbench.bend`, `bench/nbench_str.bend` and `bench/nbench.c` all print
  `10000000`, on every lane they build for, before any clock was read: a
  timing run that disagreed on the answer would not be a measurement.

## The cap move

Both files were within 34 and 28 ttok of their caps before the lane, so any
landing here is a move. It is a **measured** move: the two cap sites are
`gates/repo.ts` and `tests/caps.sh`, both edited.

| file | before | after | cap before | cap after | headroom |
|---|---|---|---|---|---|
| `bend2/base.bend` | 46,436 | 47,377 | 46,470 | 47,400 | 23 |
| `bend2/comp.ts` | 81,572 | 82,062 | 81,600 | 82,100 | 38 |

base.bend's +941 **is** the deliverable: 20 defs mirroring U32's at width 64.
There is no honest trim left in it — it already carries no law, no `div`, no
`mod`, no `show`, no `read`, and its comment is six lines. comp.ts's +490 is
six hunks, three of which are one line each.

## The upstream diff surface

Keep the proposal to these five items in `comp.ts` (six hunks — item 1 is
two) plus the `base.bend` block. The first two are bug fixes that stand on
their own and should be offered first, separately from U64:

1. **`term_word` takes its width** (runtime + the `emit_ctr` call site) —
   fixes silent truncation for **every** `w64` ADT, i.e. `F64` today: the
   four-line NaN reproducer above prints `nan? False` on C and `nan? True`
   on the interpreter, a lane disagreement with no U64 involved.
2. **`emit_match` reads `WORDS[adt.k]`** instead of hardcoding `W32` —
   same class, the other direction. Also removes a local.
3. **`WORDS` gains `U64: W64`** — one word in a literal.
4. **`OPTIMIZED` gains `U64`** — six lines, the JS lane's half of 3.
5. **the `u64_` family in `OPERATIONS`** — 26 lines, U32's entries retyped
   at 64 with `& 0xFFFFFFFFFFFFFFFFn` where U32 has `>>> 0`.

1 and 2 are defensible with no reference to U64 at all; 3-5 are the feature.

Not part of that surface: `tests/base/u64_ops.bend` goes with items 1-3 as
their test, but `bench/nbench*.{bend,c}`, the two cap moves and the bench
allow line are this repo's bookkeeping and should be dropped from the
proposal. The bench files sit at `bench/` root rather than under
`bench/runtime/<name>/` on purpose: `gates/perf.ts` readdirs `bench/runtime`
and grades every dir it finds against an `apple_m4` pin, so a bench added
there would show up as an unmeasured cell on a 48-mini gate with pins this
x86 machine cannot produce.

## Gaps found, deliberately not fixed

- **`main -> U64` (and `main -> F64`) crashes the printer.** `show_main`'s
  kind map is `{ U32: 0, F32: 1, Nat: 2, Char: 3, String: 4, Array: 6 }`;
  anything else falls to kind 7 (Data) and dereferences `lay.arms![j]` on a
  `W64` lay whose `arms` is `null` — `TypeError: null is not an object` at
  `comp.ts:1747`. **Pre-existing**: reproduces identically for `F64` on the
  untouched shared clone at `13fb2e3e`. Fixing it for `U64` alone would leave
  the `F64` sibling broken, so it belongs to its own lane. The test prints
  through `Nat.show` and is unaffected.
- **There is no `U64` literal.** `U64{Word.zero(64n)}` is the only entry
  point and it is a 64-cell structural allocation converted at the boundary,
  so a constant inside a hot loop is a heap allocation per iteration. U32 has
  `U32.from_nat` / `U32.to_nat`; U64 has neither. The shape is two defs plus
  two `OPERATIONS` entries (`u64_from_nat: { C: "$0", JS: "$0" }`,
  `u64_to_nat` the same modulo `nat_chk`) — cheap, but outside this brief's
  scope, and both files are at their new caps.
- **`u64_div` / `u64_mod` are absent** because the base block has no `div` /
  `mod`, matching what the brief asked to mirror. They are the obvious next
  two entries.
