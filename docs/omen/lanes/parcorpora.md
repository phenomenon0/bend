# Corpus parallelism lane — report (fable, 2026-09-19)

Branch `lane-parcorpora`, worktree `bend-work-parcorpora`, off `omen` @ `2babbefa`. Two demos
under `demos/parallel/`: parse a corpus of Python files, and search one. Both are one binary that
runs sequentially or as a fork/join tree; both assert the parallel run prints the sequential run's
bytes at every thread count. Everything ran in the foreground; nothing pushed. Files touched:
`demos/parallel/{parse_corpus.bend,search_corpus.bend,gen_manifest.py,_lib.sh,run_parse.sh,run_search.sh,README.md}`
and this report. `bend2/**`, `gates/**`, `tests/**` untouched; `demos/python/*.bend` imported, not
edited.

Machine: Ryzen 7 7700X, **8 cores / 16 hardware threads**, 30 GB, Fedora 43, clang, bun. **Shared
with another lane throughout: load average 2.9 at the start of the parse run, 5.2 at the end.**
Every number below is therefore pessimistic.

## What the demos are

`parse_corpus.bend` reads a manifest (one path per line), reads every file in manifest order, and
parses the whole corpus with `demos/python`'s own lexer and parser — imported, not reimplemented:

```python
import ../python/lexer.bend as L
import ../python/parser.bend as P
```

The parallel API is one line:

```python
a b = par(p, half, List.take(&2, Item, xs, half))
      par(p, Nat.sub(n, half), List.drop(&2, Item, xs, half))
```

The manifest is halved down to one file per leaf (depth `1 + floor(log2(n))`), and the halves are
appended in order, so the printed lines cannot depend on which thread finished first. One leaf is
one file: `L.lex` → `P.parse` → `S.json(S.module(m))` → the FNV hash of that JSON, printed as
`status hash path`. A file that does not parse prints its error kind and the hash of the error
text instead. The last line is a hash of all the lines together — the corpus hash.

`search_corpus.bend` is the same tree with a cheaper leaf: the lines of the file that contain
`PAR_NEEDLE`, counted the way `grep -c` counts them, carried up the tree in a `Tally` so the total
is the tree's own sum.

There is no thread code in either file. `PAR_MODE=seq` runs the same leaves one after another in
the same binary; `--threads N` is the knob.

## Methodology

- One `bun bend2/main.ts … -o …` build per binary, before any timing; the C lane, `--gpu off`.
- Per row: one untimed warm run, then **5 timed runs, median reported**. `wall_s` is the whole
  process measured from outside with `date +%s%N` — process start, manifest read, every file read,
  the tree, the printing, exit. The phase column (`parse_s` / `search_s`) is the binary's own
  `IO.now()` delta across the tree only, printed on stderr. The clock stops *after* `IO.print`,
  because printing is what forces the results — a timer taken before the print measures a thunk.
- `speedup` is against the `seq` row's wall time, not against `par --threads 1`.
- The page cache is warm for every row (the corpora are read repeatedly).
- Every run — warm and timed — is `cmp`'d against the sequential run's stdout. A single differing
  byte aborts the script.

### Corpora

`gen_manifest.py` writes three manifests and prints `name files bytes path`. A file is in a corpus
when it is a `.py` file that is not a symlink, is under 1 MiB, is not a test (no `test*` directory
on its path — NumPy vendors meson's `test cases/` — no `test_*.py`, no `conftest.py`), and the
pinned oracle's intake accepts it: `tokenize.detect_encoding` says utf-8 or utf-8-sig and it
decodes. That is the same intake rule `tests/parser/normalize.py` uses.

| corpus | root | files | bytes |
|---|---|---:|---:|
| numpy | `~/libscout/x/numpy-2.4.6` | 619 | 9,936,605 |
| pandas | `~/libscout/x/pandas-3.0.6` | 300 | 8,185,396 |
| stdlib | the pinned oracle's own `lib/python3.11`: every top-level `*.py` plus `asyncio/`, `email/`, `importlib/`, `multiprocessing/`, `unittest/` | 290 | 6,349,245 |

The stdlib root is CPython 3.11.15 as shipped with `/home/omen/.hermes/hermes-agent/venv/bin/python3`,
resolved at runtime via `sysconfig.get_path("stdlib")` — the same interpreter `tests/parser` pins.

## Demo 1 — `parse_corpus.bend`, `run_parse.sh`

```bash
demos/parallel/run_parse.sh                    # RUNS=5 THREADS="1 2 4 8 16"
PAR_MANIFEST=files.txt $OUT/parse_corpus --gpu off --threads 16
PAR_MODE=seq PAR_MANIFEST=files.txt $OUT/parse_corpus --gpu off
```

Medians of 5, load 2.9 → 5.2:

| corpus | mode | threads | wall s | parse s | speedup | files/s | MB/s |
|---|---|---:|---:|---:|---:|---:|---:|
| numpy 619 files, 9.5 MB | seq | 1 | 8.31 | 8.24 | 1.00× | 74.5 | 1.1 |
| | par | 1 | 8.29 | 8.22 | 1.00× | 74.7 | 1.1 |
| | par | 2 | 4.67 | 4.60 | 1.78× | 132.4 | 2.0 |
| | par | 4 | 3.18 | 3.10 | 2.61× | 194.4 | 3.0 |
| | par | 8 | 2.18 | 2.10 | 3.81× | 283.9 | 4.3 |
| | par | 16 | **1.56** | 1.47 | **5.34×** | 397.6 | 6.1 |
| pandas 300 files, 7.8 MB | seq | 1 | 5.56 | 5.51 | 1.00× | 54.0 | 1.4 |
| | par | 1 | 5.39 | 5.34 | 1.03× | 55.7 | 1.4 |
| | par | 2 | 2.79 | 2.75 | 1.99× | 107.4 | 2.8 |
| | par | 4 | 1.63 | 1.58 | 3.42× | 184.4 | 4.8 |
| | par | 8 | **1.04** | 1.00 | **5.32×** | 287.1 | 7.5 |
| | par | 16 | 1.13 | 1.08 | 4.93× | 266.2 | 6.9 |
| stdlib 290 files, 6.1 MB | seq | 1 | 5.04 | 5.00 | 1.00× | 57.6 | 1.2 |
| | par | 1 | 5.08 | 5.04 | 0.99× | 57.1 | 1.2 |
| | par | 2 | 2.67 | 2.62 | 1.89× | 108.8 | 2.3 |
| | par | 4 | 1.49 | 1.44 | 3.39× | 194.9 | 4.1 |
| | par | 8 | 0.94 | 0.90 | 5.34× | 307.2 | 6.4 |
| | par | 16 | **0.81** | 0.77 | **6.18×** | 355.8 | 7.4 |

### Identical output

36 runs per corpus (6 rows × [1 warm + 5 timed]), **every one byte-identical to the sequential
run**, asserted by `cmp` inside the loop — not compared afterwards. The corpus hashes: numpy
`859378188`, pandas `1889268586`, stdlib `279149589`. Verdicts: `619 ok`, `300 ok`, `290 ok` —
every file in all three corpora parses.

`par --threads 1` is the same tree on one thread, and it lands on the sequential time (1.00×,
1.03×, 0.99×): the tree itself costs nothing measurable, the speedup is the threads.

The hashes are also checked from outside the driver. For the first file of each corpus,
`run_parse.sh` runs `demos/python`'s own `main.bend` on that file, pipes the AST JSON it prints
through an independent FNV-1a written in Python, and asserts the driver's line equals
`ok <that hash> <path>`:

```
first file is the parser demo's own AST: ok 3055704504 …/numpy-2.4.6/.spin/cmds.py
first file is the parser demo's own AST: ok 1570731452 …/pandas-3.0.6/_version_meson.py
first file is the parser demo's own AST: ok  958951799 …/lib/python3.11/__future__.py
```

So the number in the table is not the driver agreeing with itself: it is the parser demo's tree,
hashed by a third implementation.

## Demo 2 — `search_corpus.bend`, `run_search.sh` (run by the orchestrator after the lane exited)

The same fork/join tree with a cheaper leaf: count the lines containing the needle
(`PAR_NEEDLE=import`), carried up the tree in a `Tally`. Two manifests: **all** (the three
corpora, 1,209 files / 23.3 MB) and **all8** (a wider walk, 9,672 files / 186.7 MB).
36 runs per manifest, every one byte-identical to the sequential run (`cmp` in the loop;
corpus hashes `1808723388`, `3571213227`).

| corpus | mode | threads | wall_s | search_s | speedup | files_s | MB_s |
|---|---|---:|---:|---:|---:|---:|---:|
| all | seq | 1 | 0.22 | 0.12 | 1.00× | 5421.5 | 104.7 |
| all | par | 8 | 0.16 | 0.06 | 1.42× | 7700.6 | 148.6 |
| all | par | 16 | 0.16 | 0.06 | 1.41× | 7651.9 | 147.7 |
| all8 | seq | 1 | 1.75 | 0.97 | 1.00× | 5517.4 | 106.5 |
| all8 | par | 2 | 1.42 | 0.63 | 1.24× | 6830.5 | 131.9 |
| all8 | par | 4 | 1.28 | 0.50 | 1.36× | 7526.8 | 145.3 |
| all8 | par | 8 | 1.23 | 0.44 | 1.42× | 7844.3 | 151.4 |
| all8 | par | 16 | 1.24 | 0.44 | 1.41× | 7793.7 | 150.4 |

**Honest reading.** Search is **IO-bound**: wall saturates at ~1.4× while the in-tree time
improves 2.0–2.2×, because reading the bytes dominates and the per-file leaf is tiny
(one warm pass, ~150 MB/s through the IO effects). `par @1 == seq` again (the tree is free).
For pure text scanning, `grep -c` on the same file list stays faster than either mode
(**0.02 s** for `all`, **0.16 s** for `all8` — one tuned C process, no tree, page-cache warm) —
that is the honest baseline, not a competitor we beat. The parallel win is for
**compute-shaped** work (parsing: 5.3–6.2×), not for IO-shaped scans; a future chunked
single-file search with a KMP carry is where search parallelism would earn more, and that
is design-noted, not claimed.
