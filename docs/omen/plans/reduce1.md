# R-lane #1 — reduce (plan)

`lane-reduce1` @ `bend-work-reduce1`, off `omen` `f9a4b7d2`. Caps frozen:
**acceptance = net-negative ttok per target file, caps unchanged, all gates green.**
Baseline: `bun gates/repo.ts` PASS 44/44; comp.ts **80,198** ttok (cap 81,000).

## Sizing (2026-09-18, ttok CLI; reproducible via `reduce1-measure.py`)

| probe | size |
|---|---|
| comp.ts whole | 80,198 (cap 81,000) |
| OPERATIONS rows | 84 rows / 3,163 ttok |
| — string family | 44 rows / 1,595 ttok |
| table clusters n>=2 (collapse) | est **−332 ttok** |
| runtime `*_take` defs | 31 defs / 7,372 ttok |
| — `str_*`/`re_*` subset | 26 defs / **6,755 ttok** (top: `re_exec_take` 2,316) |
| base.bend | 577 defs / 42,318 ttok (String.* 84 defs) |

## Slices

**S1 — table templating (comp.ts).** Collapse shape clusters behind
`tpl_*`-style helpers: get/take/end family (flags), find/find_last,
pad_start/pad_end/zfill, trim trio, starts/ends, show/read pairs, regex pair.
Emitted C/JS must stay **byte-identical** — the suites and the regex oracle are
the judge. Est −0.3…−0.5k.

**S2 — runtime envelope (comp.ts).** One scratch/pack ABI for the `*_take`
family (C macro pair + JS helper): each def keeps only its algorithm; the
take/scratch/pack boilerplate lives once. Est −1.5…−2k. `re_exec_take` keeps
its VM, loses the envelope.

**S3 — base.bend sweep (open).** Usage graph over `base.bend` + tests + demos;
retire orphaned/superseded defs (String.* go first). Size at lane start.

## Evidence per slice (suites run alone, serially)

`bash tests/run.sh` (16) · `bash tests/run.sh --strings` (85) ·
`bash tests/regex/run.sh` (49) + `oracle.py` 0 diffs · `bash tests/codex/run.sh`
(161) · `bash tests/caps.sh` · `bun gates/repo.ts`. Report per slice: ttok
before→after per file, ins/del ratio, cap line (held / lowered).
