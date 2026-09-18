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

0b. **Battery carve-out (2026-09-18):** `strings deep` may fail in `[interpret]`
   or `[js build]` with a bun-frontend stack overflow ("the machine stack
   overflowed"). That exact signature is a known, measured upstream fragility
   (11–16/60 build failures, rates in `docs/omen/lanes/strings-cont.md`); it
   does not block integration when every other lane/test is green. Any other
   failure blocks. Owner: orchestrator — fixture-headroom rework or upstream
   issue (stats available).

1. **Update**: `git fetch origin` (upstream); new snapshot lands on `main`.
2. **Port**: generate a patch from the source of truth and 3-way apply —
   - from a workshop branch: `git diff --binary <base> <branch> -- bend2/ tests/`;
   - `git apply -3` in this repo (needs the source blobs: `git fetch <src> …`).
   - Always `--binary` (test fixtures like `tests/strings/utf8.bin`).
3. **Commit**: snapshot-style commits on **`omen`** (our line) — f64, strings,
   gates/caps each as logical commits; caps in `gates/repo.ts` land at the next
   round thousand above the *measured* size in THIS tree (f64+strings ported =
   base 27,844 → cap 28,000; comp 75,152 → cap 76,000).
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
