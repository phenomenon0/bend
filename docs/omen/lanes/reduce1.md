# R-lane #1 — reduce, S1 report (2026-09-18)

Branch `lane-reduce1`, worktree `bend-work-reduce1`, off `omen` `f9a4b7d2`.
Plan + sizing: `docs/omen/plans/reduce1.md`. Nothing pushed.

## S1 — table clusters behind `tpl_ops`

- `tpl_ops` gained a 5th arg (`call`) for the f32/f64 `show`/`read` pairs.
- 11 clusters collapsed: length/hash/from_list/splitlines · get/get_end ·
  slice/replace · take_end/drop_end · order/join/repeat/partition ·
  starts_with/ends_with · find/find_last · pad_start/pad_end · regex
  exec/match_at · f32 show/read · f64 show/read.
- Reordering-safe: `OPERATIONS` is pure lookups (no iteration order deps).

## Numbers

| file | before | after | delta | cap |
|---|---|---|---|---|
| `bend2/comp.ts` | 80,198 | **79,812** | **−386** | 81,000 — **held** (headroom 1,188) |

Diff: `+23 / −43` lines (del/ins **1.87**). No cap raise, nothing lowered.

## Evidence

- **Byte-identical emissions**: 9 fixtures × C + JS artifacts diffed against the
  `omen` tree — 18/18 identical (padding, search, split, replace, compare,
  regex exec, regex captures, f64 read_roundtrip, f64 show_specials).
- `bash tests/run.sh` **16 / 16** · `--strings` **85 / 85** ·
  `tests/regex/run.sh` **49 / 49** · `tests/codex/run.sh` **161 / 161, 0 errors** ·
  oracle **5,000 pairs: c=0 js=0 interpret=0** · `tests/caps.sh` ok ·
  `bun gates/repo.ts` **PASS 44 / 44**.

## Next

**S2 — one scratch/pack ABI for the `*_take` family** (est −1.5…−2k; the
`re_exec_take` envelope included; VM logic untouched).

---

# S1 review + S2 (fable, 2026-09-18)

## S1 review (builder of record)

- The `slice replace` cluster left the original `string_replace` row behind as a
  duplicate key (same value, so harmless, but dead ttok). Removed.
- `tpl_ops` passes `call` straight through (`{ C, JS, call }`): every `Intr.call`
  consumer tests `=== true`, so `call: false` ≡ absent. No spread/branch.
- comp.ts 79,812 → **79,757** (−55). 18/18 artifacts byte-identical vs `/tmp/emit/old-*`.

## S2 — measured first; the estimate was wrong

The plan sized S2 at −1.5…−2k by counting the *whole* `*_take` defs (6,755 ttok)
as if they were envelope. They are not: the envelope is `str_peek` on entry and
`term_sink` on exit — ~2 lines per def. A macro-pair ABI saves ~6 ttok per def
(~−120 total) and hides control flow (`break`/`return`) inside macros. **Not
built.** The defs are algorithm, and the algorithm is already tight.

What was genuinely duplicated, and is now written once:

- `re_node` → `str_node`, moved above `str_get_take`; the hand-rolled Some-boxing
  in `str_get_take` and `str_find_take` now calls it (`cls_fit(1) == 0`, same
  alloc class, same NONE-on-error).
- `str_scratch_free(e, cls, l)`: the "sticky error → recycle locally, else
  heap_free" block lived in both `str_search_close` and the `re_exec_take` tail.
- `re_exec_take`: two identical early exits merged
  (`Loc P = err_seen(e.mem) ? 0 : heap_alloc(e, cls)`). VM untouched.

## Numbers

| file | lane start | after S1 | after S1 review | after S2 | lane delta | cap |
|---|---|---|---|---|---|---|
| `bend2/comp.ts` | 80,198 | 79,812 | 79,757 | **79,625** | **−573** | 81,000 — **held** (headroom 1,375) |

S2 diff: `+27 / −38` lines (del/ins 1.41).

## Evidence (S1 review + S2 together, suites serial)

- JS artifacts 9/9 byte-identical vs the `omen` tree. C artifacts embed the
  runtime, so they differ textually by exactly the S2 edits — the byte-identical
  bar cannot apply to a runtime slice; behaviour is judged by the suites + oracle.
- `tests/run.sh` **16/16** · `--strings` **85/85** · `tests/regex/run.sh` **49/49** ·
  `tests/codex/run.sh` **161/161, 0 errors** · oracle **5,000 pairs c=0 js=0
  interpret(500)=0** · `tests/caps.sh` ok · `bun gates/repo.ts` **PASS 44/44**.
- Not run: `gates/test.ts` / `gates/perf.ts` (mini cluster).

## Next

S3 (`base.bend` sweep, 42,318 ttok) is where the real bulk is — comp.ts's
string/regex runtime has no further cheap fat. Size with a usage graph first.
The comp cap could be lowered 81,000 → 80,000 now; left for the operator.
