# The upstream offer: what the fork carries, and what could leave it (2026-09-23)

The fork's cost is its merge. Upstream 2.0.26 took 11 hunks of `comp.ts` and two
conflicts that git did not see (`lanes/upstream-2.0.26.md`), and upstream ships
daily. This is the inventory, measured against `upstream/main` 6a77e12. Nothing is
filed. Opening a PR on bendlang/bend is the operator's call, one PR at a time.

## The footprint (ttok, cl100k)

| file | upstream | fork | delta | upstream cap |
|---|---|---|---|---|
| `bend2/comp.ts` | 62,163 | 82,908 | +20,745 | 64,000 |
| `bend2/base.bend` | 25,406 | 49,777 | +24,371 | 32,000 |
| `bend2/bend.ts` | 43,431 | 43,780 | +349 (26 lines) | 44,000 |
| `bend2/effs/` | | +4 files, 228 lines | | 4,000 each |

These are the fork-only `base.bend` items by family, as a share of the fork's
added bytes:

| family | items | share |
|---|---|---|
| Regex (+ Re, Inst, Match) | 158 | **60%** (14,452 ttok) |
| String | 90 new, 9 changed | 24% |
| I64 / U64 / F64 | 100 | 11% |
| File, Utf8, TCP, Char (streaming text) | 19 | 5% |

**Regex is most of the `base.bend` delta, but it is not the merge cost.**
Measured on 2026-09-24:
- `base.bend` merged clean in the 2.0.26 sync. All 11 conflicts were in `comp.ts`.
- By a keyword count of the fork's added `comp.ts` lines (which undercounts lines inside larger blocks), regex is about 1.3k of 23.5k ttok. Strings are about 6.5k: the adaptive-width runtime, `str_*`, `TAG_STR`.
- Regex's native matcher closure in Base is 39 items (3,442 ttok): the types, the reference Pike VM, and `Regex.exec`/`match_at`. The other 119 items (11,010 ttok) are compile/parse/API.
- `intr_of` binds a native only to a Base def (`tld.b`) or a bodiless law. So the matcher must stay in Base, or regex silently falls back to the reference.

Moving the 119 items to a module would buy about 11k ttok of cap headroom, and nothing is short of it. The costs:
- every regex user imports it by path, including every program the translator emits for `re.search` (two emission pins move);
- the merge surface stays as it is.

**Not done.** The earlier claim here, that the move "removes most of the merge surface", was wrong.

## Upstream's stated terms

WONTFIX.txt: *"a small team keeps the language at a size it can maintain"* and
*"patches would cost us control of the codebase"*. PR #795, strings as one PR,
was offered and closed. So an offer is small, separable, and measured, or it is
not made.

## Candidates, smallest first

1. **U64 / I64 / F64 as native words.** About 7.8 KB of base and three `WORDS`
   rows, plus the 64-bit branch in `emit_match`. That branch is the one the
   2.0.26 merge had to re-derive, so keeping it forked has a cost every merge.
   Suites: `tests/f64` and `base/{u64,i64}_ops`. Upstream's own WONTFIX names
   the 2^48 Nat cap as a runtime limit, and 64-bit words are the honest answer
   to it. **Offer first.**
2. **`io_text` / `io_str` decoding of truncated UTF-8.** The C and JS lanes
   disagree with each other on upstream: WHATWG incremental vs per-byte. This
   is a bug report with a two-line reproduction, not a feature. **File as an
   issue.**
3. **Streaming text** (`File.read_text`, `Utf8.Dec`, `TCP.recv` text): four
   effect files and 19 base items. It is useful to anyone reading large files,
   but it depends on candidate 4's string representation.
4. **Strings** (views, adaptive width, code points; 24% of base plus most of
   `comp.ts`'s delta). This is #795 again. Offer it only if upstream asks.
5. **Regex.** Never offered. It stays in Base: see above for why moving it out does not pay.

## What stays forked, and why

- `docs/omen/**` and `gates/**` hold governance and are fork-only by definition.
- Known deviations carried on purpose: `marshal_char_scalar [js]` (RawChar for
  a non-scalar code) and `computed_match [c build]` (base's `LT` mangles into
  the test's constructor). Both are red on omen and green on upstream, and both
  are listed in `lanes/upstream-2.0.26.md`.
