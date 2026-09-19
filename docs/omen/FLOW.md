# FLOW — how this repo works (ours, in his style)

This is **our Bend**: a clone of `bendlang/bend` at upstream snapshot `0b7e2b11`
(2.0.5-era) plus our stack ported on top — `f64` (commit `51f01c6e`) and
`strings` (packed U32 views, ownership, KMP, Python-grade core). Nothing here is
pushed to upstream; `our` remote = `phenomenon0/bend`.

## His flow (what we're matching)

- **Upstream main is squashed release snapshots** ("Bend 2.0.5: …"), force-pushed;
  there is no merge history to follow.
- **PRs are closed, not merged**; fixes he wants get **reimplemented by hand**
  and credited "Reported by (#PR)". The repo gate (`gates/repo.ts`, ttok caps),
  the four-lane test doctrine (`gates/test.ts`), perf pins, and the ping gate
  ARE the review.
- **Rebases are 3-way patch ports** across snapshots — never merges.

## Our flow

0. **HARD RULE (operator, 2026-09-18): anything written by codex gets a fable
   review/rewrite pass before it merges. Fable is the continuing builder for
   all workstreams; codex output is never final.** Streams keep their own
   branches (`lane-strings`, `lane-regex`, `lane-parser`, …) off `omen`.

0b. **Battery carve-out — CLOSED (2026-09-18, `lane-deepfix`):** the `strings
   deep` frontend stack overflow ("the machine stack overflowed") is fixed at
   source: the fixture's last deep `Nat` literal (`4097n`, 4,097 nested `Succ`
   under the checker's check-ctr recursion) is now computed. Measured 28/240 →
   0/240 frontend runs, strings suite 11/11 serial runs green under load;
   report `docs/omen/lanes/deep-fix.md`. No carve-out remains: **any** battery
   failure blocks, this signature included — if it reappears, look for a new
   large literal before retrying. Authoring rule: big operands are computed
   (`Nat.mul(64n, 64n)`), never written as literals.

1. **Update**: `git fetch origin` (upstream); new snapshot lands on `main`.
2. **Port**: generate a patch from the source of truth and 3-way apply —
   - from a workshop branch: `git diff --binary <base> <branch> -- bend2/ tests/`;
   - `git apply -3` in this repo (needs the source blobs: `git fetch <src> …`).
   - Always `--binary` (test fixtures like `tests/strings/utf8.bin`).
3. **Commit**: snapshot-style commits on **`omen`** (our line) — f64, strings,
   gates/caps each as logical commits; caps in `gates/repo.ts` follow the
   **cap-budget rule** (see Discipline): f64+strings ported = base 27,844 → cap
   28,000; comp 75,152 → cap 76,000 — those historic raises were "measured +
   round thousand"; from 2026-09-18 that reading is Closed.
4. **Verify** (the gates decide, not prose):
   - `bun gates/repo.ts` — repo shape + caps. (Current: PASS 42/42.)
   - `bash tests/run.sh` (f64, 16 checks) and `bash tests/run.sh --strings`
     (85 checks) — four lanes each; `bash tests/codex/run.sh` (161-case
     adversarial suite); `bash tests/caps.sh` (ttok ledger).
   - Benchmarks: `tests/strings/bench.sh` (frozen-cons baseline vs ours).
5. **Push** (when asked): `git push our omen`; workshop history kept under
   `refs/heads/archive/*` (`archive/strings`, `archive/f64`).
   **Fork mirror:** keep the fork's `main` equal to upstream after each fetch —
   `git push our refs/remotes/origin/main:refs/heads/main` (add
   `--force-with-lease=refs/heads/main:<old>` when his lineage was rewritten).
   The GitHub "behind" banner concerns only this mirror; our line is `omen`.
6. **Publish upstream** (deliberate, user-approved only): his pipeline is
   close-and-fold — the artifact here is shaped so a hand-port or a
   "Reported by" fix is mechanical.

## Discipline — add function, reduce code (operator, 2026-09-18)

Upstream's snapshot delta (`0b7e2b11` → origin/main, +50 commits): 37 files,
**+3,086/−2,451** (del/ins **0.79**), comp cap **+0.5k**. Their additions absorb
old code because every fix is **re-implemented by hand**. Our stack delta: 119
files, **+12,395/−98** (0.008) — build-out; caps auto-raised (comp 76k→81k, base
28k→43k). Build-out may not buy permanent bulk; keep their discipline with
three rules:

1. **Caps are budgets, not thermometers.** A cap rises only for *new public
   surface*, itemized in the lane report (which rows/defs force it, k each).
   No surface, no raise — the lane simplifies until it fits the frozen cap.
   "Measured + margin" is not a reason.
2. **Alternate build lanes with one R-lane (reduce).** After ≤2 build lanes
   land, one R-lane runs (measure targets at lane start). Open targets:
   - `comp.ts` — collapse per-op native rows behind the `tpl_ops`-style
     templates where signatures match (string / regex / list families);
   - runtime C — one scratch ABI for the `*_take` families (`str_*_take`,
     `re_exec_take`, list natives share the take/scratch shape);
   - `base.bend` — retire superseded pure-Bend helpers the lanes replaced
     (String.* was the start); demo-only code leaves the base lib.
   Acceptance: **net-negative ttok per target file**, caps unchanged, gates green.
3. **The fable pass is size-aware.** The rule-0 rewrite accepts only when:
   gates green, every cap change itemized, duplicated helpers met by the port
   are merged or listed for the R-lane.

Bookkeeping: lane reports already table ttok before→final per file — add the
**ratio** (ins/del) and the **cap line** (raised by k, forced by which rows /
or "held"). Tracked targets: build lanes ≥0.15, R-lanes ≥0.7 (his cycle: 0.79).
Every raise books a debt row naming the R-lane that retires it.

## Layout

- `~/Documents/Project/bend` — **this repo** (canonical; `omen` branch = ours).
- `~/Documents/Project/bend-f64` — feature workshop (frozen `f64`/`strings`
  histories; source of the ported patches). Kept for provenance.
- `~/Documents/Project/bend-upstream` — reference checkout for studying
  upstream (gates, tests, papers).
- `~/Documents/Project/bend-strings` — the strings deliberation record
  (`PLAN.md`, `BUILDLOG.md`, transcripts).

## Landmines learned

- `git apply` is atomic and needs pre-image blobs; `--binary` for fixtures.
- Verification must not share a worktree with an active builder.
- Upstream force-pushes rewrite `main`; never merge, always port.
- ttok caps: the sizes above are *this tree's*; re-measure after every port.
- **Proofs:** when law/proof entries enter, gate them per
  `docs/omen/PROOF-GATE.md` — dedicated proof entry bound to shipped sources,
  dependency-closure check for `@unsafe`, exit code ≠ verdict (audit P05–P08).
