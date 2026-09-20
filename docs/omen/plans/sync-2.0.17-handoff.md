# Sync 2.0.17 + land the waiting lanes — handoff (fable, 2026-09-19)

## Mission (do end to end)

**Phase 1 — finish the in-progress upstream sync.** This checkout (`/home/omen/Documents/Project/bend`) is on `omen` with a **merge in progress**: upstream `origin/main` (bendlang/bend tip `b2791abb` — "2.0.17") merged into `omen`. Conflicted: `bend2/base.bend` (3 hunks), `bend2/comp.ts` (7 hunks), `gates/repo.ts` (2 hunks). Continue the merge (do NOT abort; the pre-sync tip is safe at ref `omen-presync-0919` = `2babbefa`). Resolve, run the full battery, commit.

**Phase 2 — land the six waiting lane branches** into `omen`, one at a time, full battery between each:
`lane-strgaps` (1 commit) → `lane-strings-demo` (1) → `lane-strings-flagship` (2) → `lane-base-fit-fold` (1) → `lane-nits-base` (2) → `lane-translator-t4` (2).
They were finished+verified when built; some will now conflict with the synced core (base.bend / caps / docs overlaps likely). Resolve keeping both intents.

**Delivery:** full battery green; `docs/omen/lanes/sync-2.0.17.md` written (decisions, deviations, cap ledger, counts); `omen` pushed to **`our`** remote (phenomenon0/bend). **NEVER push `origin`** (that's upstream). Do not touch `pr/*` branches (PR #873 rides separately).

## What this sync is for

Absorb upstream's last 120 commits (templates with `~` parameters + laws, `term_higher` reduced applications / `term_beta` gone, bare-operator diagnostics, `tools/bend-fmt-lsp`, cap raises, changelog/version craft) **without losing our strings stack** (adaptive narrow/wide buffers, streaming chunked decode, per-byte replacement recovery — PR #873's core). Upstream rewrote `io_str`/`io_text` to WHATWG-style semantics; where the two disagree, **ours stays** and the divergence is documented as a deviation.

## Conflict resolution map (Hermes' read of every hunk — verify each against the tests as you go)

### bend2/base.bend
- ~331-376: ours adds `Utf8.Dec` + `File.read_text.go/pack/read_text`; theirs adds `File.read_at`. **Keep both.**
- ~416-434: ours adds `TCP.recv_text.go/recv_text`; theirs adds `TCP.poll`. **Keep both.**
- ~2094-2104: `Char.to_upper/to_lower` — ours `Char.case_if(...)`, theirs branchless `Bool.to_u32`-mul form. Behavior identical; **take theirs** (less drift) unless something of ours pins the other form.

### bend2/comp.ts
- ~332-374 (native-op table): ours = the full `string_*` table (plus regex ops, `map_bit`); theirs adds `string_length {JS: ...}`. **Keep ours**; make sure `string_length` survives — grep for it before/after (avoid a silent duplicate key).
- ~655-707 (`f32_read` C): theirs = stricter `strtof` parse (full consume of the text, rejects `xX(`); ours adds `f64_text/f64_show/f64_read`. **Take theirs for the f32 body; keep our f64 trio untouched**; single shared `free(text); return out; }` close.
- ~2722-2766: ours adds `str_constant` / `str_static` (static SCon constant folding); theirs = new signature `emit_ctr(fl, x, ty, at: Lay | null)`. **Take theirs' signature; keep our helpers.**
- ~2771-2811 (THE hard one): ours adds the String static branch + early `vs`/`lay` + a `stat`/`lay_box` early return via `node_build`; theirs refactors the tail: `const flds = ctr_flds(...)`, `fl.hot.has(x.k) && facts_ctr(...)`, `pos = at ?? lay_of(...)`, `lay = lay_box(pos) ? lay_node(fl.book, x.k) : pos`, then `arm = lay_arm(lay, x.k)`, `vs = emit_each(fl, flds, arm.fs.map(...))`, `v = val_new(ws, lay, vs.every(stat))`, `return lay === pos ? v : val_new([ctr_build(...)], BOX, v.stat)`.
  **Proposed: adopt theirs' structure wholesale, keep only our String-static early return** (`if (adt.k === "String") { ... str_static ... }`) inside it. Their tail subsumes our `node_build`/`stat` path (`v.stat` flows through `ctr_build`). Verify with the strings battery **and the byte-identical artifact gate** — if static SCon literal emission regresses, reconcile further (our `stat` propagation must not be lost).
- ~6806-6882 (C `io_str`): ours = adaptive-width decoder (`str_alloc`/`str_fit`, 1→2→4-byte cells); theirs = WHATWG-style incremental decoder (no adaptive widths). **Keep ours** (strings lane + utf8 fixtures pin it). Semantics differ on truncated input (ours: replacement per ill-formed byte, re-read as lead; theirs: maximal-subpart). Run the FULL battery — upstream test files auto-merged alongside; if any pins WHATWG behavior, do NOT silently adapt: keep ours and record the test as a deviation in the sync report; escalate loudly in the report if it's a genuine semantic conflict.
- ~7650-7672 (JS `io_text`): ours = fatal-TextDecoder probe then manual per-byte walk (parity with our C contract); theirs = plain `TextDecoder` (non-fatal WHATWG). **Keep ours for C/JS parity**; same deviation note.

### gates/repo.ts
- ~39-50 (caps): ours `base.bend` 43400 / `bend.ts` 41000 / `comp.ts` 81000; theirs adds `flake.nix` 1500, `bend.ts` 42000, `comp.ts` 64000. Keep the `flake.nix` row; per-file caps = **measured after resolution** (don't max blindly — budgets, itemize any move; remember the merged comp.ts size).
- ~81-94 (test allowances): **union** — our rows (`f64|strings|codex`, `regex|parser|lint|translate`, `docs/omen`, `utf8.bin`, `run|caps.sh`, 8500 for tests c/js) **plus** theirs' `tools/bend-fmt-lsp/**` rows. `(c|js)` keep the larger unless measured otherwise.

## Land-order friction notes
- `base.bend` cap edits collide across `lane-strgaps` (cap 45,470), `lane-base-fit-fold` (43,400) and `lane-nits-base`: resolve to a final measured number; keep both lanes' itemization notes consistent in their `docs/omen/lanes/*.md`.
- Lane reports/doc files may conflict in `docs/omen/` — keep both sides.
- After EVERY merge (sync + each lane): repo gate + caps + the full batteries (strings, f64, regex, codex, parser, lint, translator) — the same invocations you've used for lanes. Exact counts in commit messages, house style (see `git log omen`).
- Commit the sync merge as one commit in house voice; commit each lane as `integrate lane-<name>: ...` with battery counts. `docs/omen/lanes/sync-2.0.17.md` may be a separate `docs:` commit.

## Env / house notes
- Work **in this checkout** (the merge state lives here).
- Shell in tmux is Nushell: `;` not `&&` in tmux sends; your Bash tool is unaffected.
- House discipline applies: read FLOW.md / PROOF-GATE.md before deciding; caps are budgets (raise only itemized + measured); every deviation named in the lane report.
- `tests/regex/__pycache__/` in `git status` is untracked noise — leave it alone.
- Gates take minutes. Keep going; don't stop at the first red — fix or escalate in the report.
