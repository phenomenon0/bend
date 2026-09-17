# WORKLOG — bend-f64

## 2026-09-17 — F64 v0.1: spec → ship → polish (one day)

**Goal.** First-class F64 in the Bend 2.0.4 fork ("ship doubles today"), built
to the upstream repo's own standards after studying it.

**Timeline / decisions.**

1. Read the shipped compiler (10.5k lines TS + base.bend). Mapped the exact
   surface: `WORDS` layout table, `OPERATIONS` op tables (name = law lowercased
   with dots→underscores via `eff_name`), C/JT runtime slabs, `OPTIMIZED`
   natives, parser literal rule, `lay_of`/`emit_ctr` word packing.
2. Forked to `~/Documents/Project/bend-f64`; baseline commit `82cb989`
   (byte-identical to `~/.bend/app/2.0.4`). SPEC.md (`f598f26`) = file-by-file.
3. Implementation (`299fc20` base → `8ce6114` compiler lanes → `a3b9ef2`
   literals): mirrored blocks, no checker changes (it is width-agnostic).
   First JS-lane run correct on the first try; native lane identical.
4. GPU: F64 device program built (clang 21 + CUDA/NVRTC), ran on the 3090 —
   nvidia-smi 100% spike; CPU/GPU outputs bit-identical
   (`140744525406163.47` chain; MC π `3.1415913105010986` / 13176789).
5. **codex lane**: authored an independent 161-case adversarial suite +
   Python binary64 oracle (`tests/codex/`). Integration found one real gap —
   dotless-exponent literals (`1e9d`) were not in the grammar (fixed `866aa59`)
   — and two documented C-lane `read` parity quirks (strtod hex + embedded
   NUL), pinned with F32-verified evidence. Final: 161 PASS / 0 FAIL.
6. **Taelin study** (user direction): cloned `bendlang/bend` (public, main ==
   2.0.4 file-for-file; squashed history), studied AGENTS.md, the four gates,
   1,302 tests, the bench pins, gen_pins, his LessWrong workflow notes.
   Findings distilled into `MANUAL.md` + a browsable `study/` site.
7. **Polish pass** (this): grammar comment in `bend.ts`; `tests/f64/` in the
   `#|` convention; `tests/run.sh` (four lanes, local reduction);
   `tests/caps.sh` (ttok ledger: +1,078 base / +1,656 comp → land with caps
   25k/63k); README; this log.
8. **fable lane**: independent verification session — verified show/conversion/
   read/literal behavior byte-identical across lanes and digit-identical to
   Python repr, and zero F32 regression (byte-identical vs baseline across
   JS+native). Found one real bug: **Metal has no fp64** and the added
   `typedef double f64;` would have broken every Metal build — fixed the same
   hour (typedef dropped from the Metal block, helpers guarded
   `#ifndef __METAL_VERSION__`), gates re-run green.

**State at end of day.** All lanes green; fable review folded in (one real
Metal bug found and fixed); quirks documented (MANUAL §7). F64 is a host +
CUDA type by construction (Metal has no fp64).

**Files worth keeping:** SPEC.md (design), MANUAL.md (standards),
study/index.html (browsable evidence), tests/codex/README.md (suite), plus
`~/Documents/Project/bend-upstream` (the reference checkout).
