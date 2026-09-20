# Sync 2.0.18–2.0.21 lane report (merged in the stream; verified by the orchestrator — 2026-09-20)

What came in (21 commits past `b2791abb`, the 2.0.17 sync point):

- **2.0.18** `f38a7797` — the compiler's own names refused where it encodes them (#870/#875), a
  field named `a.b` is read by key not by dotted path (#868), a foreign def counted like
  `@unsafe` (#874), the JS chan-proof fix (#871); WONTFIX #872/#878.
- **2.0.19** `2f08170b` — a Bend binary starts in 2 ms (8 GiB arena, doubles in place), a record
  of records past 256 words is a node, **the U32 table** (a match on dense U32 literals compiles
  to a lookup table, `a4c54e02`), Metal `fast::` trig.
- **2.0.20** `a5269a6b` — the U32 table carries a bit pattern's default; the arena publishes its
  page cap; an erased let binds erased names only.
- **2.0.21** `c15a75f8` — an instance cycle is a self-call that does not decrease (#902), an unsafe
  def may call a law not yet filled, a typed let `x : T = v` binds `x` to `{v : T}` (`6018e28e`).

**Provenance.** Merged into `omen` as `13fb2e3e` (bare "Merge remote-tracking branch 'origin/main'
into omen"; recorded here) by the streaming agent. Caps were measured and moved in `29c98228` —
`bend.ts` 42,100 → **42,300** (42,264; upstream delta +164) and `comp.ts` 81,600 → **83,100**
(83,070; +1,470) — in `gates/repo.ts` and `tests/caps.sh` together, nothing else in that commit.

**Rulings survived** (orchestrator source checks on the tip): adaptive C `io_str` (`str_fit` ×7,
`StrParts` ×56), the JS `io_text` fatal-probe, `str_constant`/`str_static` ×3, the `string_length`
row still dropped, the f64 trio (`f64_text`/`f64_show`/`f64_read`), `base.bend` untouched by the
merge (`Utf8.Dec` ×24, `fold_text` ×8, the text-carry effs present), zero conflict markers.

**Verification** (orchestrator battery on the tip): repo gate **54/54**; strings **102/0**;
translator **40/0** (seventeen demos); regex **49/0**; `tests/run.sh` **19/0** (the f64 gate
included); codex **161/0**.

**Notes.** No `demos/python` ripple this round — the 2.0.16 operator-annotation context was
absorbed in the last sync, and the translator ran as-is. `BEND_NO_TELEMETRY=1` is now pinned in
every raw-capture harness (`7ffe8f04`): the daily version-check notice was folding into
byte-compared captures machine-wide (the cached check believes 2.0.21). Two upstream bugs found
while planning this work were filed as **bendlang/bend#914** (`parse_term_ns` dotted-key
prefixing) and **#915** (`+name` vs a same-file def).
