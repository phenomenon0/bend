# Slice 4 — Map.bit, IO-boundary audit, numeric-text parity

Built on `strings` from `48afbad`, 2026-09-17 (America/Chicago).
Map.bit: `e6ab38d`. Numeric text: `55b2fee`. Specimen trim: `bce08fa`. No push.

## Implemented

- Native `Map.bit(key, pos)` on C and JS. C is O(1): `str_bit_peek` borrows
  the key, computes `ci = pos / 33`, `off = pos % 33`, answers False past the
  end, True at `off == 0` for an existing cell, otherwise bit `32 - off` of
  the U32 code. JS walks to the endpoint with `str_offset` and reads
  `codePointAt`. Both rows hand the original owned key back beside the Bool
  (array-form `C: ["$0", …]`, JS `{$: "Tuple"}`), so `Map.put/ins/seek` and
  the reconstruction helpers stay source-compatible and keep the reference
  tree order. Partial application (`Map.bit("ab")`) reaches the native through
  the emitted closure on both lanes. Raw U32 cells read as-is on C/interpret.
- IO-boundary audit against the packed representation, no changes needed:
  C `io_cstr`/`io_str`/`show_val`, JS `io_bytes`/`io_text`/`str_prepend`/
  `char_new`, and every effect adapter under `effs/` (print, print_err, write,
  file_write, tcp_send, udp_send_to; file_open, get_env, tcp_connect host,
  udp_send_to host, window_open; inbound file_read, tcp_recv, udp_poll,
  udp_recv_from, get_env). Raw-value strings are rejected with the pinned
  diagnostic before any shim sees them; NUL is an ordinary element in string
  payloads and is rejected in paths, modes, hosts and env names on both lanes
  with the same errno as before. Ill-formed input bytes decode to one U+FFFD
  each. Shim signatures unchanged.
- Numeric-text parity (own commit). C `F32.read`/`F64.read` now consume the
  entire explicit extent through a shared `io_num` grammar that matches the JS
  regex: optional leading space, sign, digits with an optional point and
  exponent, or `inf`/`infinity`/`nan` in any case. An embedded NUL is a
  character, not an end; hex floats, `nan(...)`, trailing junk, a bare
  exponent and the empty string all read as `None`. The codex oracle no
  longer pins the old `Some(1)` quirk for `read_embedded_nul`/`read_hex`.

## Verification

| Gate | Result |
| --- | --- |
| Whole Base | All terms check |
| `map_keys.bend` | interpret, JS, C agree with hand-computed protocol values |
| `numeric_text.bend` | JS and C agree on all 12 spellings |
| `raw_strings.bend` | C/interpret bit and Map.get probes pass; JS rejection pinned |
| `tests/f64/read_roundtrip.bend` | C and JS still match |
| `bash tests/run.sh` | 16/16 |
| `bash tests/run.sh --strings` | STRINGS_RESULT |
| `bash tests/codex/run.sh` | 161/161, zero suite errors |

`map_keys.bend` covers shared 44-character prefixes, missing keys, the empty
key, an embedded-NUL key, a supplementary key, and partial application, then
round-trips them through `Map.set/get/has/pop/keys`. `numeric_text.bend` is
an IO main (no `F64.read` in the interpreter), so its CLI lane executes JS.

## Token ledger

Measured with `ttok` (default tokenizer); caps unchanged.

| File | Before | After | Delta |
| --- | ---: | ---: | ---: |
| `bend2/base.bend` | 27,844 | 27,844 | 0 |
| `bend2/comp.ts` | 74,220 | 74,981 | +761 |
| `bend2/bend.ts` | 40,399 | 40,399 | 0 |
| `bend2/main.ts` | 5,292 | 5,292 | 0 |

Changed/new specimens: map_keys 1,214, numeric_text 413, raw_strings 521,
`tests/codex/expected.py` 3,779 tokens. `map_keys.bend` sits above the ~800
small-specimen guideline: the checker cannot destructure a computed tuple, so
the Map round-trip needs one chained helper per intermediate value.

## Regressions and leftovers

No observed regression; no requested Slice 4 piece deferred, and none hit the
15-minute fallback. `bend.ts`, `main.ts`, Base reference definitions, effect
shim signatures, and `~/.bend` were untouched. Committed locally on `strings`;
nothing was pushed.

- `effs/window_set_title.c` on Linux passes the title to `XStoreName`, which
  truncates at an embedded NUL. The effect has no failure channel, and macOS
  uses the explicit length, so this is documented rather than changed.
- Leading whitespace in `F32.read`/`F64.read`: C accepts ASCII space and
  `\t\n\v\f\r`; JS `\s` also accepts Unicode spaces. No specimen depends on it.
