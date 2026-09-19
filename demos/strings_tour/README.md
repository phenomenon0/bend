# The strings tour

A tour, not a race: five short vignettes of what Bend's first-class strings do,
all over ONE generated hostile log. Each prints only what it measures. Lines
starting `^` are one-line illustrations from Python or JS, run live; lines
tagged `[record <date>]` quote a dated lane report and are not re-measured.

```sh
demos/strings_tour/selftest.sh              # first: 277 KB log, cli = js = c, oracles (~30 s)
demos/strings_tour/run_tour.sh              # the tour (generates the log on first run)
SHARED=1 GPU=1 demos/strings_tour/run_tour.sh   # + the honest contrast, + the GPU appendix
ONLY="3 5" BLOCKS=1024 demos/strings_tour/run_tour.sh
```

The log (`gen_log.py`, seeded, into `$CORPUS`, default `~/videokit-corpus`):
`BLOCKS` blocks of exactly 65,536 code points of whole lines. Default 4096 =
282,788,890 bytes, 268,435,456 code points, 3,129,171 lines; `BLOCKS=1024` is
71 MB. It carries emoji usernames, é/ß, a combining mark, NBSP, ragged
whitespace, 13,087-code-point lines and one ReDoS-bait line. Each block opens
with a stamp spelling its own number, so a deep read proves where it landed.

| # | Vignette | Program |
|---|---|---|
| 1 | Read once, view forever | `demos/text_stream/main.bend` (stream), `views.bend` |
| 2 | Code points are the unit | `codepoints.bend` |
| 3 | The fuel gauge | `fuel.bend` |
| 4 | One line of thread code | `demos/parallel/knob.bend`, unchanged |
| 5 | The compiler catches it | `oops.bend` (must not compile), `viewcap.bend` |
| A | The `!` GPU lane (`GPU=1`) | `demos/parallel/gputext.bend`, unchanged |

## Measured

C lane, Ryzen 7 7700X (8 cores / 16 threads), 30 GB, RTX 3090. 2026-09-18,
**under load** (load average 8 to 16 from other jobs); two full runs, both shown.

| # | What | Measured |
|---|---|---|
| 1 | stream the 283 MB log in 64 KiB chunks | 1.91 to 2.70 s, peak RSS 2,532 KiB |
| 1 | one `File.read` (load: read + decode) | 1047 to 1438 ms, peak RSS 1,296 MB |
| 1 | 3,129,171 lines, each a view, measured | 544 to 840 ms |
| 1 | 1,000,000 scattered slice + parse + check | 118 to 189 ms, all correct |
| 3 | `^(a+)+$` on the 4,097-code-point bait | 21 to 39 ms, 393,408 units = 96 x 4,098 |
| 3 | `a.*b\|a`, budget 1,000,000 | `budget exhausted at code point 7` in 22 to 37 ms |
| 4 | scan, `--threads` 1 / 4 / 16 (median of 3) | 2.10 / 0.56 / 0.33 s (run 1: 2.97 / 0.94 / 0.58) |
| 4 | `SHARED=1`, no leaf copy, 1 / 4 / 16 | 3.18 / 2.07 / 1.87 s: 1.70x, does not scale |
| 5 | 16,000,000 live views / 17,000,000 | counted in 1.0 s / `bend: runtime fail-stop`, exit 1 |
| A | same scan, `--gpu off` / `--gpu 8GB` | 0.47 s / 1.86 s, same bytes (`--gpu 4GB`: out of memory) |

Every vignette-4 and appendix output equals the Python oracle
(`36272974:160058848`, `:1470932`) at every thread count and lane.

## What to say on camera

- **1**: "Two ways to read a 283-megabyte log. Streamed, the process never
  passes two and a half megabytes. Or read it once: loading is the only step
  that touches every character; after that, a slice does not register on the
  clock. Three million lines, each a view, no copies; a million scattered
  slices, each parsed and checked, in under a fifth of a second."
- **2**: "This string is three characters, and Bend says three. Reverse keeps
  the emoji whole. The footnotes are other languages, live. And the honest
  rows: case and trim are ASCII-only. Python wins Unicode case outright."
- **3**: "Every log has a line like this one. The pattern is the textbook
  catastrophe; here its cost is known before it runs. And when a pattern truly
  is quadratic, you get an error saying where the fuel ran out. Bounded by
  design. A backtracking engine spends an unbounded time right here."
- **4**: "There is no thread code. This one line says the halves are
  independent. Same binary, I only turn the knob; same bytes every time. And
  the honest part: share one buffer across all cores and it stops scaling."
- **5**: "I used this string twice. It does not compile. And the one runtime
  limit, 16.7 million live views of one string, stops loudly, never wrongly."
- **A**: "One bang and the same function runs on the 3090. Same bytes. It is
  slower here, and we say so: text is branchy."

## Honest limits

- A String with one astral character stores 4-byte cells: 1.3 GB RSS for this
  log. `[record 2026-09-18, lane-adaptive]` pure ASCII is 2.03x the input at
  64 MiB against a 1.5x target: a miss, the file buffer is the floor.
- `to_upper`, `to_lower`, `trim`, `words` know ASCII only; NBSP is not a space.
- A combining mark is its own code point: `reverse` moves it, as in Python.
- The JS lane slices in O(offset); `selftest.sh` keeps its inputs small.
- `[record 2026-09-18, 8f782000]` `find_all`, 26 KB, C: 14.2 s -> 0.02 s.
