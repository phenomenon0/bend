# R-lane #1 (reduce) — handoff to fable (from Hermes, 2026-09-18)

You are the continuing builder for this lane. Read this, then
`docs/omen/plans/reduce1.md` (plan + sizing) and `docs/omen/lanes/reduce1.md`
(S1 report). Everything below is verified state, nothing is pushed.

## The flow you're inheriting

- Repo `~/Documents/Project/bend` (`omen` = ours; `origin` = bendlang/bend).
  This worktree: `bend-work-reduce1`, branch `lane-reduce1`, off `omen` `f9a4b7d2`.
- Ops law — FLOW.md, “Discipline — add function, reduce code”: (1) caps are
  budgets: a raise only for itemized new public surface; (2) alternate build
  lanes with one R-lane: acceptance = net-negative ttok, caps held, gates
  green; (3) the fable pass is size-aware.
- Slices: **S1 done** (below). **S2 = yours**: one scratch/pack ABI for the
  `*_take` family — 26 `str_*`/`re_*` defs = 6,755 ttok; `re_exec_take`
  (2,316 ttok) keeps its VM, loses its envelope. Est −1.5…−2k. Measure first
  at lane start. Evidence bar: emitted artifacts byte-identical + suites + the
  regex oracle. **S3 (later)**: `base.bend` sweep — 577 defs / 42,318 ttok;
  orphaned helpers retired (String.* first), usage graph over base.bend +
  tests + demos.

## S1 — done by Hermes, needs your builder review/rewrite pass

Commit `b1229378`: `tpl_ops` gained a 5th arg (`call`, for f32/f64 show/read);
11 clusters collapsed (length/hash/from_list/splitlines · get/get_end ·
slice/replace · take_end/drop_end · order/join/repeat/partition ·
starts_with/ends_with · find/find_last · pad_start/pad_end · regex
exec/match_at · f32+f64 show/read). `comp.ts` 80,198 → **79,812 ttok** (−386);
diff +23/−43 (del/ins **1.87**); caps **held** (81,000; headroom 802 → 1,188).

Evidence: 18/18 emitted artifacts **byte-identical** vs the `omen` tree (C+JS
× 9 fixtures: strings padding/search/split/replace/compare, regex
exec/captures, f64 read_roundtrip/show_specials; artifacts in `/tmp/emit/`);
`tests/run.sh` 16/16 · `--strings` 85/85 · `tests/regex/run.sh` 49/49 ·
`tests/codex/run.sh` 161/161 · oracle 5,000 pairs c=0 js=0 interpret=0 ·
`tests/caps.sh` ok · `bun gates/repo.ts` PASS 44/44.

## Why we do this (the whole point)

- Upstream moved +50 commits while we built: **+3,086/−2,451** (del/ins 0.79),
  comp cap **+0.5k**. Their fixes are **re-implemented by hand**, so each
  addition absorbs old code.
- Our stack: **+12,395/−98** (0.008) and caps auto-raised **+40k**
  (comp 76k→81k, base 28k→43k). Build-out is fine; carrying the bulk forever
  is not.
- Caps are the review surface. If they only ever rise, the budget stops
  meaning anything and the next port/sync to upstream gets heavier every
  cycle. R-lanes retire the debt so build lanes keep fitting **without**
  raises — that is how we keep their discipline while adding function.
- Operator law: codex output is never final; fable is the continuing
  builder. So: review/rewrite S1 as builder of record, then run S2.

## Numbers

| file | before | after | delta | cap |
|---|---|---|---|---|
| `bend2/comp.ts` | 80,198 | 79,812 | −386 | 81,000 held |

Next raise request (if ever): itemized new public surface only.
