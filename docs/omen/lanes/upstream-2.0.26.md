# upstream 2.0.26 — the merge (2026-09-23)

`upstream/main` 6a77e12 (Bend 2.0.26) merged into omen. It is 63 commits past the
last merge, 6018e28 (2.0.21). `bend.ts`, `base.bend`, `main.ts` and
`gates/test.ts` merged clean. `comp.ts` had 11 conflicting hunks and
`gates/repo.ts` had 2. Two more places merged clean but were wrong, and are the
real content of this report.

## Verdict

| | |
|---|---|
| targeted sweep, 663 tests × (check, interp, js, c) | 1,344 / 1,383 lanes green; **every red is red on a parent** (table below) |
| VM battery | `VM PASS: 34, FAIL: 0` |
| lint | `Lint PASS: 76, FAIL: 0` |
| translator | 40 / 40 in-repo items. The 16 mined demos need their source trees under `~/Documents/Project/`, which this host lacks. |
| strings, regex, power | 100/2, 48/1, 149/1. Every red is environmental: no GPU, `strings/deep`'s interp timeout (also red on omen), and no numpy for power's `assign` oracle. |
| `bun gates/repo.ts` | **PASS: 56 / 56** after one cap move (below) |
| `tsc --strict` | `comp.ts` clean. `bend.ts` has the same two errors upstream and omen already had. |

The host has x86_64, 4 cores and 15 GB. The sweep covered `tests/{base,f64,strings,regex,io,
run,compile,show,flatten}`, every test upstream touched in the range, and every
U64/I64 test. The runner reproduces `gates/test.ts`'s per-test rule, including the
`exit N` tail and check-only for an unprintable main.

## The two silent conflicts

**1 · The native-constructor descriptors changed shape (94e57ea).** Upstream moved
from `{intr: {K: …}, elim: {K: …}}` per type to `{K: {intr, elim, cond}}` per
constructor. The fork's F64, U64 and I64 rows merged textually in the old shape
inside the new table. They are restated in the new shape, as are omen's Chr `char_code` elim
and SCon `str_prepend` intro (hunks 3–4).

**2 · A 64-bit word's match lost its bits (1be5ce8 + hunk 7).** Upstream's word
match now comes from `emit_lits`, which answers only for 32-bit words. Omen's
emitter had widened the word set to U64 and I64 and exploded the word into its
constructor node's bits. After the merge, a U64 or I64 match fell to the constructor path.
It read `case U64{x}`'s field off an unexploded word, and in the C lane
`Word.to_nat(64n, x)` died with "a Nat past the largest immediate". The tests
`base/u64_ops` and `base/i64_ops` went red on C only. The fix is a `w64` branch
in `emit_match`: hold the word at its own width, explode it into the node, and
read the one constructor's fields. It is omen's code, placed in upstream's structure.
Both tests are green on four lanes.

## Hunks

1. `WORDS`: both sides — upstream's null prototype, omen's F64/U64/I64.
2. Native table: omen's `string_*`, `regex_*` and `map_bit` rows, plus upstream's compacted `array_*` rows (`swap` is now `array_rmw`).
3. Chr: omen's `char_code` elim, in the per-constructor shape.
4. SCon: omen's `str_prepend` intro, in the per-constructor shape.
5. `emit_intr`: omen's sealed-field `facts_hot` block is kept.
6. Word literal: upstream's early return for an empty literal, with omen's 32/64 width passed to `term_word`.
7. `emit_match`: upstream's structure (`adt_of`, `emit_lits`, the shared chain), plus the `w64` branch above.
8. Device prelude: `BEND_RTC` (0861851), with omen's no-fp64 Metal note kept.
9. Heap walk: upstream's compact ternary, with omen's `TAG_STR` (one cell, class 1) folded in.
10. `io_str`: omen's adaptive-width decoder and its comment. This is a known deviation.
11. `io_text`: omen's fatal-probe decoder. This is a known deviation.

`gates/repo.ts` takes the union: bend.ts at upstream's 44,000, comp.ts at omen's
84,100, upstream's hyphen-subdirectory test row, and omen's extra rows.

## Cap move

`bend2/base.bend` measured 49,777 against 48,928. The 849-token delta is all
upstream's: `Array.fork`/`join`, nine `Array.atomic.*` laws, `U32.log2`, and the
`Array.map` get/set chain. It moved to 49,777 in `gates/repo.ts` and
`tests/caps.sh`. The ledger's upstream-caps line is now current (32,000 / 44,000 /
64,000). comp.ts is 82,908 (down from omen's size) and bend.ts is 43,780. ttok here is
js-tiktoken's cl100k ranks, because ttok's BPE download is blocked on this host. It
reproduces omen's `PASS: 56 / 56` exactly before the merge.

## Reds that ride along (none new)

Red on upstream and on omen, or on upstream with the test absent from omen:
- the interp lane of 26 `io/` tests (foreign effects and marshal),
- `io/main_foreign` check, the four `io/audio*` C builds,
- the interp lane of `run/array_fork*`, `run/array_atomic_fadd`, `run/stencil3d` and `run/unsafe_mutual`.

Red on omen only, because upstream passes them. These are fork deviations carried forward:
- `io/marshal_char_scalar [js]`: omen's JS `char_new` keeps a non-scalar code as a `RawChar` (the strings lane's surrogate rule), where upstream fail-stops.
- `run/computed_match [c build]`: "two names mangle to CID_LT", from base's `LT` and the test's own constructor.

## Now removable (not done here)

- f8ce74d fixes the `../` module name inside `( … : T)`, so the three `Nat.add`/`Nat.mul` spellings in `demos/python` (c932ae0) can go back to operators.
- c2b6367 lets a module bind a local named like one of its defs. That undoes the reason behind `nodes.bend`'s `+bare`→`+many` rename.
- 942573f makes a Nat or String literal one `Lit` node. The "big literals expand unary, compose them" rule behind `fuel()` and `int_cap()` in `vm.bend` should be re-measured before it is kept.
