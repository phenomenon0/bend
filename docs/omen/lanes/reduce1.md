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
