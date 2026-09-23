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

**Regex is most of the delta, and it is a library, not a language feature.** It
belongs where `power/` lives, in Zone B: pure Bend over Base, imported by the
programs that want it. Moving it out of `base.bend` takes the fork's base from
49,777 to 35,325 ttok and removes most of the merge surface. The cost is its
seven native rows (`regex_exec`, `regex_match_at`, the Pike VM in `comp.ts`),
which must be reachable from a module rather than from Base. That is the next
lane, and it needs no one's permission.

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
5. **Regex.** Never offered. Move it to a library (above).

## What stays forked, and why

- `docs/omen/**` and `gates/**` hold governance and are fork-only by definition.
- Known deviations carried on purpose: `marshal_char_scalar [js]` (RawChar for
  a non-scalar code) and `computed_match [c build]` (base's `LT` mangles into
  the test's constructor). Both are red on omen and green on upstream, and both
  are listed in `lanes/upstream-2.0.26.md`.
