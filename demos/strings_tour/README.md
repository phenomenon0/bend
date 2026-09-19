# demos/strings_tour — one hostile log, five traps, and nothing happens

On July 20, 2016 one line of text took Stack Overflow down for 34 minutes:
a comment, then about 20,000 spaces, met by the regex that trims whitespace,
`^[\s\u200c]+|[\s\u200c]+$`. Their
[postmortem](https://stackstatus.tumblr.com/post/147710624694/outage-postmortem-july-20-2016)
counts 199,990,000 character checks for that one line. Line 3 of the log this
demo generates rebuilds it: their comment text, 20,000 spaces, one `x`. Line 2
is the textbook ReDoS bait. The rest is 283 MB of emoji usernames, é/ß, a
combining mark, NBSP, ragged whitespace and lines 13,000 code points long, and
192 of its 64 KiB chunk boundaries cut through a character.

Five acts over that one log. Each springs a real trap on Python or JS **live**
(the `^` lines), then runs Bend on the same input. Every timing and count
printed is measured by that run; `[record <date>, <lane>]` lines quote a dated
lane report. The `^` lines are the bug people write, not the best those
languages can do, and each act says what the rival does better. A tour, not a
race: the claim is no surprises, not top speed.

```sh
demos/strings_tour/selftest.sh              # first: 275 KB log, cli = js = c, oracles (~30 s)
demos/strings_tour/run_tour.sh              # the tour (generates the log on first run)
SHARED=1 GPU=1 demos/strings_tour/run_tour.sh   # + the variant that does not scale, + the GPU appendix
ONLY="1 5" BLOCKS=1024 demos/strings_tour/run_tour.sh
```

Machine for the tables: Ryzen 7 7700X (8 cores / 16 threads), 30 GB, RTX 3090,
clang 21, C lane; rivals CPython 3.14.2 and bun 1.3.4. Measured 2026-09-19
**under load** (load average 3 to 5 from other jobs); a range is two full
runs. Re-run to get your own numbers.

## 1. The fuel gauge — `fuel.bend`

Every global regex call takes its budget as an argument:

```python
Regex.scan(re, s, tank)
```

A search from code point `at` must afford its ceiling, `weight × (length + 1 −
at)` units, before it starts, whatever the text; then it pays only the span it
walked. A search that cannot afford its ceiling never starts, and the call is
an error: never a partial answer, never a hang. A call that finds matches is
one search per match on the same tank (last row below). The Stack Overflow
line has no match, so each dose is one search over the whole line: exactly
`58 × (length + 1)` units. Tank 2,000,000:

| spaces | units = 58 × (length + 1) | gauge | Bend, C | Python `re` | JS (bun) |
|---:|---:|---|---:|---:|---:|
| 5,000 | 292,378 | `▕███░░░░░░░░░░░░░░░░░▏` | 12–13 ms | 0.07 s | 0.02 s |
| 10,000 | 582,378 | `▕██████░░░░░░░░░░░░░░▏` | 21 ms | 0.26–0.27 s | 0.07–0.08 s |
| 20,000 | 1,162,378 | `▕████████████░░░░░░░░▏` | 40–53 ms | 0.84–1.03 s | 0.27–0.32 s |

Double the spaces and Bend's bill doubles. Python and JS go ×3.2 to ×4.0 per
doubling: the n²/2 behind the postmortem's 199,990,000.

| call | result |
|---|---|
| the 20,000-space line, tank 1,000,000 | `refused: budget exhausted at code point 0: needs 1162378`: the search never starts |
| `^(a+)+$` on the 4,097-code-point bait | 0 matches, 393,408 units = 96 × 4,098, 19–21 ms; `^` Python `re` on its first 22 / 24 / 26 `a` only: 0.10–0.12 / 0.39–0.48 / 1.52–1.89 s |
| `a.*b\|a` on the bait: one search per match, each a rescan | `budget exhausted at code point 14, no partial answer`, 45–47 ms |

**Honest limits.** Not the fastest regex: RE2, Go and Rust are linear too,
and far faster. The budgeted calls (`scan`, `find_all`, `split`, `replace`)
run the reference VM written in Bend on every lane; only `Regex.exec` /
`match_at` have a native implementation (C and JS), and those take no budget.
The units are the same on every lane; the clock is not: `[record 2026-09-19,
lane-strings-flagship]` the three doses take 70 / 107 / 186 ms as emitted JS
and 77 / 138 / 252 ms through the CLI (`bun bend2/main.ts`: the JS emitter,
run in-process), against C's ms column. PCRE2 has a match limit and .NET a
wall-clock timeout; both stop a search midway. Here the ceiling comes from
weight and length before the search, a search that cannot afford it never
starts, and the count is the same through the CLI, as JS and as C. CPython
3.11 `re.ASCII` semantics; no backreferences, lookaround or named groups.
Stack Overflow's fix was a substring function: for a trim, that is the right
tool here too.

On camera:
- "This line took Stack Overflow down for thirty-four minutes. Same regex. The line is rebuilt from their postmortem. Watch the gauge."
- "Double the spaces, double the bill, and I knew the ceiling before it ran. Python and JS: three to four times."
- "Give it a smaller tank and it refuses at character zero. It never starts a search it cannot finish."

## 2. A character is never torn — `codepoints.bend`, `demos/text_stream/main.bend`

```python
File.read_text(f, dec, 65536)
```

`dec` is the decoder between chunks: the bytes of the character the cut went
through, as a value. The call takes it and hands back the next one.

| | result |
|---|---|
| Bend, streamed in 64 KiB chunks | `2602567031 268435456 chars 36332633 words`, 1.74–2.35 s, peak RSS 2,532 KiB |
| Bend, one whole-file `File.read` (`whole.bend`) | the same line (the runner asserts it), peak RSS 1,295 MB |
| `^` Python, `chunk.decode()` per chunk | raises at chunk 30: `unexpected end of data`; 380 chunks would |
| `^` JS, `buf.toString()` per chunk | 420 U+FFFD that are not in the file |

And the unit is the code point: `"A😀é"` has length 3 and reverses whole (JS:
4, and `split("").reverse()` tears 😀 into lone surrogates); U+E000 sorts
below 😀 (UTF-16 order flips it).

**Honest limits.** Python and JS ship incremental decoders (the JS `^` line
runs `TextDecoder` with `stream: true` beside the bug: 0 wrong). Bend's own
`File.read` also decodes each chunk alone (one U+FFFD per byte of the cut
character): `File.read_text` is the chunked read. `[record 2026-09-18,
lane-stream]` 177,128 chunk partitions on C and 180,094 on JS equal the whole
decode; a carry cut to 2 bytes was caught on both. Constant memory is the C
lane only: JS holds 46 MiB for an empty file, 156 MiB at 64 MiB. `to_upper`,
`trim`, `words` know ASCII only (NBSP is not a space): Python wins Unicode
case outright. A combining mark is its own code point, as in Python.

On camera:
- "Cut this file every 64 K and 192 cuts land inside a character. Python raises. JS invents 420 characters that are not in the file."
- "Bend streams it in two and a half megabytes and gets the same hash as reading it whole."
- "And the honest rows: case and trim are ASCII-only. Python wins Unicode case."

## 3. Read once, view forever — `views.bend`

```python
String.slice(s, at, Nat.add(at, 15n))
```

A String is a view: payload, offset, length, and every offset counts code
points. `slice`, `take`, `drop`, `lines` make views and copy nothing (C lane);
`String.copy` is the explicit copy. Every block opens with a stamp spelling
its own number, so a slice that lands wrong breaks the checksum.

| what | measured |
|---|---|
| one `File.read` of the log (read + decode) | 834–1,163 ms |
| 3,110,547 lines, each a view, each measured | 513–533 ms |
| 1,000,000 scattered stamps: slice + parse, sum checked | 100–115 ms, all correct |
| `^` JS, `s.slice(at, at + 15)` at the same 1,000,000 offsets | 999,756 stamps wrong |
| peak RSS | 1,295–1,296 MB |

**Honest limits.** A JS string indexes UTF-16 units: the `^` line is
code-point offsets (what Python, a database or an API hands you) used as
string indices; carry UTF-16 offsets and JS is right. Python gets this right
(PEP 393), and Bend makes the same trade: one astral character makes the whole
payload 4-byte cells, 1.3 GB for this log. `[record 2026-09-18,
lane-adaptive]` pure ASCII is 2.03× the input at 64 MiB (2.26× at 8 MiB)
against a 1.5× target: a miss; adaptive width made the per-cell phase 6–13 %
slower on ASCII, 3–8 % on unicode text like this log. A view keeps its whole
payload alive: `String.copy` a small slice you mean to keep. A slice and its
parse: ~100–115 ns, so a million register. The JS lane slices in O(offset).

On camera:
- "Loading is the only step that copies the text. Three million lines, each a view, no copies."
- "A million scattered slices, each parsed, their sum checked against the blocks asked for, in 100 to 115 ms. The same offsets in JS: all but 244 land on the wrong text."

## 4. One line of thread code — `demos/parallel/knob.bend`, unchanged

```python
a b = scan(p, block, String.take(s, half)) scan(p, block, String.drop(s, half))
```

| `--threads` | scan s (median of 3) | speedup | output |
|---:|---:|---:|---|
| 1 | 2.08–2.15 | 1.00× | `36332633:4172640078`, the Python oracle |
| 4 | 0.54–0.59 | 3.66–3.86× | same |
| 16 | 0.28–0.31 | 6.97–7.29× | same |
| `^` Python threads, 1 / 4 / 16 | 0.34–0.35 / 0.34 / 0.31 s | 1.11–1.12× | `len(part.split())`, the first 64 MiB |

**Honest limits.** The `^` line is the GIL: `multiprocessing` scales (and
pays to pickle the text), and free-threaded CPython builds exist; this is the
default build. Bend's own cliff: without the leaf's `String.copy`, every core
counts references on ONE payload and the tree stops scaling: 1.36× at 16
threads (`SHARED=1`). The read is serial; the table times the scan.

On camera:
- "There is no thread code. This line says the halves are independent. Same binary, I turn the knob, same bytes."
- "Python threads, the same log split sixteen ways: 1.1 times."

## 5. The compiler catches it — `oops.bend`, `viewcap.bend`

```python
String.append(String.to_upper(line), line)
```

```
- expected : line
- observed : line (consumed more than once)
```

A String is affine: used once, or shared on purpose (`+line`). The checker
enforces it; nothing runs. `^` Python, one stream counted twice: `3110547 0`.
The second pass is silently empty.

A runtime limit the checker cannot see: a payload counts its views in 24
bits. 16,000,000 live views of one string: counted, 0.93–0.94 s. 17,000,000:
`bend: runtime fail-stop`, exit 1. Loud, never a wrong count.

**Honest limits.** A Python `str` used twice is fine; the `^` line is its
one-shot streams, the nearest thing it has to a use-once value. The fail-stop
does not name the view count. Nothing about strings here is *proved*: it is
checker-enforced and differentially tested.

On camera:
- "I used this string twice. It does not compile. Python read its stream twice: three million lines, then zero, and no error."
- "And a limit the checker cannot see, 16.7 million live views of one string, stops loudly, never wrongly."

## Appendix. The `!` GPU lane (`GPU=1`) — `demos/parallel/gputext.bend`, unchanged

Scan `--gpu off` 378 ms / `--gpu 8GB` 1,825 ms (one run), same bytes, equal
to the Python oracle (`--gpu 4GB`: out of memory at this size). **Honest
limit.** Slower here: text is branchy. The claim is same source, same bytes,
no CUDA written.

## Receipts

- `selftest.sh`: every Bend program here prints the same bytes through the
  CLI, as emitted JS and as emitted C; acts 4 and A equal an independent Python
  oracle; `oops.bend` must be rejected; the 20,000-space dose must print
  `1162378 of 2000000 units`.
- `[record 2026-09-19, lane-strings-flagship]` against CPython 3.11: 5,000
  generated (pattern, text) pairs, 0 differences on C and JS, and on 500 of
  them through the CLI. The generated distribution only: depth ≤ 3, counts
  ≤ 5, text ≤ 64 code points; no `\0`, `\r\f\v` escapes, no `max_rep` /
  `max_prog` edges, no budget exhaustion.
- `[record 2026-09-18, lane-asanfix]` 84,412,268 allocations, zero live at
  exit by the harness's allocation tracker, built with ASan + UBSan
  (LeakSanitizer off), with 83 injected allocation failures.
- `[record 2026-09-18, lane-asanfix]` suites: strings 89 pass, 0 fail; regex
  49 / 0; codex 161 / 0.

If this log ever hangs a Bend program, tears a character, or gives two lanes
two answers, that is a bug: file it.

## Files

`gen_log.py <out> <blocks>` writes the log and its oracles (`.oracle`,
`.oracle_gpu`) to `$CORPUS` (default `~/videokit-corpus`, not committed):
`BLOCKS` blocks of exactly 65,536 code points of whole lines (default 4096 =
282,789,518 bytes, 268,435,456 code points, 3,110,547 lines; `BLOCKS=1024` is
71 MB), seeded, so a cut at a block boundary never splits a word and the
chunked scans equal the whole-text oracle. Knobs: `BLOCKS N THREADS RUNS
SHARED GPU GPU_MEM ONLY`.
