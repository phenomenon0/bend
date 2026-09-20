# The ripple map — compiler features × our surfaces (2.0.18–2.0.21, 2026-09-20)

What the sync brought, what each feature can touch, and what was measured. Method on
request: every claim below is either a source check (grep/git) or an A/B run on this
machine (old compiler = the pre-sync tip `7ffe8f04`; new = the synced tip), min-of-3.

## The features, one line each

1. **The U32 table** (`a4c54e02`, 2.0.19) — a `match` on dense U32 literal arms (arms
   filling over half of `0..max`) compiles to one CONSTV lookup table with a clamped
   `TAB_AT` (last row = default) instead of a 32-deep bit tree. Sparse arms, or a
   default that uses the scrutinee, keep the old lowering.
2. **2 ms start / 8 GiB arena doubling in place** (`d3d71cef`, 2.0.19).
3. **A record of records past 256 words is a node** (`b84b0047`, 2.0.19).
4. **Typed let** (`6018e28e`, 2.0.21): `x : T = v` binds `x` to `{v : T}`.
5. **Erased let** (`a08f1960`, `f1fc42b3`, 2.0.20–21).
6. **Instance cycle = non-decreasing self-call** (`e617921e` #902), unsafe defs may
   call unfilled laws.

## The matrix — per surface

| surface | U32 table | start/arena | let/diagnostic rules | verdict |
|---|---|---|---|---|
| parser / lexer / scanner | **0 sites** — its dense matches are **Nat** (`case 0n:`, 56 in `parser.bend`), and Nat tables predate the sync | no delta measured | battery green, no ripple | **already banked** |
| translator + demos | no sites | negligible | 40/0 unchanged | unaffected |
| strings (core) | none (C-side) | negligible | 102/0 unchanged | unaffected |
| power tools (25) | no sites | rerun below | — | **parity** |
| C kernels | none | negligible | 84/0 unchanged | unaffected |
| every binary | — | tiny binary: 0.6 ms both | — | no delta measured |

## The measured A/B

- **Dense 256-arm U32 match** (generated, popcount values): C file 0.11 → 0.12 MB;
  build **5.6–6.0 → 3.5–3.8 s (1.6×)**; runtime, 4M calls: **0.010 → 0.001 s (10×)**,
  identical checksums. (Upstream's 1.45 MB → 79 KB headline was a different arm shape;
  on a plain dense `0..255` the old lowering already compacted.)
- **Tiny binary start:** 0.6 ms vs 0.6 ms — no delta.
- **Parser** (build 18.7 → 18.3 s; stats-parse of `_pydecimal.py`, 229 KB: 109 → 108 ms)
  — no delta.
- **Power json bench:** build 0.93 → 0.89 s; run 0.335 → 0.338 s — no delta.
- **The 48-row power table, rerun on the new compiler:** parity. One row (`heap`,
  1.83 → 2.27) and one C column (`bitset`, 0.23 → 0.28) moved past noise — and **their
  C twins moved with them** (heap C 2.08 → 2.86), which is machine state, not codegen.

## The refactor ledger — natural vs refactor

- **Free, automatic:** every binary rides arena/start work; typed/erased-let and the
  instance-cycle rule are checker refinements; Nat tables already serve our dense
  matches.
- **Write-it-right, free:** NEW dense U32 dispatch written as `match` gets the table
  (10× runtime, 1.6× compile, measured). **The natural first user is the interpreter /
  dispatch layer** — opcode tables, byte→action tables — which is exactly the next
  layer.
- **Refactor that would NOT pay:** converting char classes (word / digit / space) to
  U32 matches — density ~25% over `0..max`, under the over-half trigger. Keep them.
- **Might pay if the shape appears:** dense byte→value tables (popcount-like, S-box,
  CRC) in power or kernels.

## Directions of the scale

1. **Interpreter / dispatch** — the table's intended consumer; write new dispatch as
   dense `match` and it is free.
2. **Parser** — no further compiler-side headroom here (already Nat-tabled); its
   remaining gap is the flat-string fast path (its own lane).
3. **Power tools** — parity confirmed at fleet level (above); no action.
4. **Test fleets** — start-time work is not measurable on our shapes yet; if later
   releases deepen it, every short-lived binary in the suites is the beneficiary.
