# power — the power-tools library

Twenty-five files under `power/`, built over twenty lanes — a few lanes ship a
set rather than a single file, because `vec` / `bytes` / `bitset` are one
decision and `heap` / `topk` are another. All of it is Bend over Base and
nothing else. This is the map. Every file's own header is the long form; every
lane's report in `docs/omen/lanes/power-*.md` is the argument.

## What it is, and what it is not

It is not `base.bend`. Base is the prelude the language ships and every Bend
program imports; it is small on purpose and it is not ours to grow. `power/` is
a separate directory, separately capped in `gates/repo.ts`, separately tested by
`tests/power/run.sh`, and imported by path:

    import ../../power/radix.bend as Radix

Nothing in `power/` is imported by anything in `bend2/`, and nothing in
`bend2/` was edited to make it work. The one place the two meet is
`docs/omen/BOUNDARY.md`, which records the rule.

The files are peers, not a stack with a single entry point. `vec`, `bytes` and
`bitset` are the substrate almost everything else sits on; past that, a file
imports exactly the neighbours it needs and no more.

## The twenty-five

The **reference** column is the published algorithm the file re-implements. It
is not, in most cases, something the oracle imports — see the next section for
what the oracle actually is, and the seven exceptions marked **†**, whose
generator imports a real outside authority and compares against it directly.

Substrate — the three containers everything else is built from:

| file | what it is | reference |
|---|---|---|
| `vec.bend` | a growable packed sequence of U32 over Base's `Array`, one flat block of native cells; one owner, every write in place | — |
| `bytes.bend` | a growable byte buffer, four bytes to a U32 cell, little end first; `len` is the truth, so pop and truncate move no data | — |
| `bitset.bend` | 32 flags to a cell, a fixed `32 * 2^depth` bits; and / or / xor / andnot / count as one index loop, popcount as the SWAR ladder | — |

Order and arrangement:

| file | what it is | reference |
|---|---|---|
| `scan.bend` | running totals over a Vec, any operator: inclusive, exclusive, segmented, filter, compact, run-length. `scan_ex` over counts is offsets — the CSR row table, a partition's write positions | CUB device scan |
| `radix.bend` | counting sort by a bucket function, and the four 8-bit passes of it that sort a full U32 key; plus histogram, unique, tally, reduce-by-key | CUB radix sort |
| `heap.bend` | a binary min-heap of `(key, val)`, ordered by key then val, so equal keys leave in one fixed order | CPython `heapq` **†** |
| `topk.bend` | the K greatest entries of a stream in K entries of memory; `merge` is exact, so a fork tree's K are the whole stream's K | `heapq.nlargest` |
| `assign.bend` | the cheapest one-to-one matching of a U32 cost matrix, by Jonker–Volgenant shortest augmenting path — *and the dual prices that prove it is cheapest* | SciPy `linear_sum_assignment` **†** |

Search and retrieval:

| file | what it is | reference |
|---|---|---|
| `bm25.bend` | an inverted index whose postings carry their score already computed, so a query is one add per posting rather than arithmetic | BM25S |
| `postings.bend` | an integer set over a document universe in the two shapes that pay — sorted-unique Vec and one-bit-per-id — with and / or / andnot / not across the pair | CRoaring's array-or-bitmap choice |
| `knn.bend` | n vectors of d floats row-major, and exact K nearest neighbours by brute force, L2 and inner product | Faiss `IndexFlat` |
| `select.bend` | budgeted subset selection: score a *set* by the ground it covers, take the most new coverage per unit cost, under a lazy greedy | apricot's facility location |

Parsing and text:

| file | what it is | reference |
|---|---|---|
| `json.bend` | JSON as an event stream: one token per `next()`, a span into the caller's own Bytes, never a tree and never a copy | CPython `json`, `py_scanstring` and `NUMBER_RE` **†** |
| `grammar.bend` | a parser state that is a *value*, plus the set of next bytes it will accept — lane 5's machine with the document taken out, so it forks | XGrammar's mask; CPython `json` as the acceptance authority **†** |
| `text.bend` | identity over bytes: UTF-8 with every code point's offset, grapheme cluster boundaries, and a normalizer that hands back the map from normalized text to the original's byte ranges | UAX #29, CPython `unicodedata` **†** |

Content addressing:

| file | what it is | reference |
|---|---|---|
| `blake3.bend` | the 32-byte root hash of a byte range, and the pieces to build it in parallel — `chunk` for a leaf, `parent` for a join | the BLAKE3 spec |
| `cdc.bend` | FastCDC content-defined chunking: an inserted byte disturbs one chunk instead of every boundary after it | the FastCDC paper's normalized chunking |

Numbers and streams:

| file | what it is | reference |
|---|---|---|
| `rng.bend` | Threefry2x32-20: a pure function of (key, counter), so any draw of any rollout is addressable and no state is threaded. Uniform U32, F32, bounded, and normal | Random123 (Salmon et al.) |
| `fft.bend` | radix-2 Cooley–Tukey over F32 complex points, out of place, decimation in time, and convolution over it | numpy `fft`'s sign and scaling; CPython `cmath` **†** |
| `sketch.bend` | four constant-memory stream summaries — HyperLogLog, CountMin, MinHash, DDSketch — each with an exact-associative merge | the four source papers |
| `drift.bend` | constant-memory online statistics that say when a stream's behaviour changed and hand back what they saw rather than a bit | Welford, Chan's parallel merge; CPython `statistics` **†** |

Results that carry their own evidence — the four that are the point of the set:

| file | what it is | reference |
|---|---|---|
| `budget.bend` | the allowance as a value, not a counter someone holds: three U32 meters, kind `Data`, so it rides inside a `Result` and forks | its own four laws |
| `proof.bend` | an answer nobody has to trust: a search returns a witness, a checker here reads the witness. You trust the checker, not the search | its own checkers, mutation-tested |
| `consequence.bend` | group the readings of an ambiguous request by what they would *do*; two readings whose action traces agree are one reading | its own laws |
| `delta.bend` | DBSP's Z-sets: a collection whose elements carry signed weights, so insert and delete are one addition and every operator can be fed a change instead of a rebuild | DBSP's incremental laws |

## How every one of them is tested

`bash tests/power/run.sh [prefix]`. Per primitive, six lanes:

1. **oracle** — `tests/power/NAME_gen.py` is a CPython implementation written
   from the source paper, not from the Bend file. It prints the *whole fixture*,
   and the checked-in `tests/power/NAME.bend` must be that byte for byte. A
   fixture cannot drift from its oracle without failing.
2. **check** — the book loads and `book.hols + book.open === 0`. No holes, no
   open goals.
3. **interpret** — `bun bend2/main.ts` against the `#|` block.
4. **js** — compiled to JavaScript.
5. **c** — compiled to C, `--gpu off`.
6. **c-1thread** — the same C binary at `--threads 1`. A schedule must not
   change an answer.

Before any of that, the runner greps all of `power/` for `@unsafe` and `?TODO`
and fails every specimen if it finds either. There is no way to leave a hole in
one file and have the other twenty-four still pass.

The comparison path is itself held: the runner first runs a deliberately wrong
`#|` fixture and requires it to fail, so a broken diff cannot read as a pass.

One hazard found by mutation and worth stating where every lane can see it:
**a round-trip test is direction-blind.** Lane 14's sweep found that only 3 of
`fft`'s 11 fixture rows catch a flipped Fourier sign convention — conjugating
twice is the identity, so the round-trip rows and the convolution rows pass
either way. A fixture built only from round trips, which is the obvious way to
test a transform, would let the module ship with the wrong convention. Any
primitive whose test inverts itself — a transform, a codec, an offset map read
forward then back — needs at least one row that pins the direction against a
value the oracle computed independently.

Lane 15 then confirmed the same hole live rather than by reasoning. Shifting
`text`'s original-side offset map by one byte moves 89 of its 257 fixture rows —
but **all 76 normalization rows and all 7 dimension rows still pass**. Every row
that asks "does it normalize correctly" is blind to the map being wrong. Only
the rows that print an original byte range literally, or re-slice the original
and re-normalize that slice, catch it. Two independent lanes, so this is a
convention and not a quirk: when a test can be satisfied by a consistently wrong
pair, it is not testing the pair.

## How every one of them is measured

`flock /tmp/bend-bench.lock bash tests/power/bench/run.sh [prefix]`. Each bench
has a C twin compiled at `-O3` — either its own `twin_NAME.c` or a dispatch row
in the shared `twins.c`. **A row is only timed once the twin, the Bend binary at
`--threads 1` and the same binary at `--threads 16` all print the same
checksum.** Then medians of three each.

That rule has a limit, and lane 14 found it the hard way while benching
`postings`: **agreement across backends proves the backends match, not that the
bench measured anything.** Its first parallel run printed a checksum of exactly
0, identical on C, 1T and 16T — three implementations agreeing on a degenerate
answer. The seed generator's low six bits had period 512 while each shard spanned
256 seeds, so shards `lo` and `lo+2` built byte-identical sets, and a depth-8
tree of two alternating values walks itself to zero under `a*31+b`. The serial
row had the same defect hiding in it the whole time — 64 distinct rounds repeated
64 times — behind a healthy-looking nonzero number. The fork tree is what made it
visible; a flat fold would have absorbed it in silence.

So a checksum that combines shards associatively can be driven to a fixed point
by duplicate shards. The cheap guard: a bench whose answer is 0, or whose shards
repeat, is **unmeasured until probed** — count the distinct inputs the generator
actually produces and say the number. `postings` now claims 28,853 distinct
`(start, stride_sparse, stride_dense)` triples over 65,536 seeds, which is a
checkable statement where "the checksums agree" was not.

Two columns matter and they measure different things. `1T/C` is the language
against C on one core: how much the compiler leaves on the table. `1T/16T` is
Bend against itself: how well the primitive actually forks. A primitive can be
excellent at one and poor at the other, and several are.

The lock is not optional. Every lane's numbers were taken under it; a bench run
on a loaded machine measures the load.

### The table

All 48 rows in one run, Ryzen 7 7700X (8 cores / 16 threads), `--gpu off`,
medians of three, nothing else on the machine (load 1.8 at start). Every row
here was timed, which means its twin, its 1T run and its 16T run all agreed on
the checksum first.

    bench                 C  bend-1T bend-16T    1T/C  1T/16T
    assign             0.20     0.34     0.34    1.7x    1.0x
    assign_par         0.26     0.34     0.05    1.3x    7.0x
    bitset             0.23     0.54     0.54    2.3x    1.0x
    blake3             0.08     0.20     0.20    2.5x    1.0x
    blake3_par         0.11     0.24     0.04    2.1x    6.6x
    bm25               0.60     2.03     2.04    3.4x    1.0x
    bm25_par           0.31     0.67     0.09    2.1x    7.3x
    budget             0.15     0.33     0.35    2.2x    0.9x
    budget_par         0.15     0.31     0.05    2.1x    6.7x
    bytes              0.19     0.31     0.31    1.6x    1.0x
    cdc                0.03     0.15     0.15    4.7x    1.0x
    cdc_par            0.03     0.12     0.02    3.6x    6.1x
    consequence        0.13     0.25     0.25    1.9x    1.0x
    consequence_par    0.11     0.16     0.02    1.4x    7.3x
    delta              0.00     0.01     0.01    1.9x    1.0x
    delta_full         0.71     0.83     0.84    1.2x    1.0x
    drift              0.13     0.24     0.23    1.8x    1.0x
    drift_par          0.13     0.14     0.02    1.0x    8.7x
    fft                0.08     0.12     0.07    1.4x    1.8x
    fft_par            0.16     0.32     0.06    2.0x    5.9x
    grammar            0.29     0.75     0.75    2.6x    1.0x
    grammar_par        0.25     0.75     0.09    3.0x    8.0x
    heap               2.08     1.83     1.84    0.9x    1.0x
    json               0.06     0.34     0.33    5.9x    1.0x
    json_par           0.05     0.32     0.05    6.0x    6.7x
    knn                0.11     0.13     0.13    1.2x    1.0x
    knn_par            0.42     0.49     0.14    1.2x    3.5x
    postings           0.09     0.44     0.43    5.1x    1.0x
    postings_par       0.18     0.87     0.12    4.9x    7.2x
    proof              0.02     0.08     0.08    4.0x    1.0x
    proof_par          0.02     0.08     0.02    3.9x    4.2x
    radix              0.16     0.34     0.34    2.1x    1.0x
    radix_par          0.11     0.25     0.04    2.3x    6.2x
    rng                0.40     0.39     0.39    1.0x    1.0x
    rng_normal         0.83     0.69     0.68    0.8x    1.0x
    rng_normal_par     0.84     0.70     0.08    0.8x    8.6x
    rng_par            0.40     0.39     0.05    1.0x    8.1x
    scan               0.39     0.75     0.75    1.9x    1.0x
    scan_par           0.26     0.43     0.08    1.7x    5.7x
    select             0.11     0.37     0.37    3.2x    1.0x
    select_par         0.45     1.45     0.26    3.2x    5.6x
    sketch             0.03     0.64     0.63   19.1x    1.0x
    sketch_par         0.03     0.63     0.09   18.1x    6.6x
    text               0.07     1.01     0.99   15.4x    1.0x
    text_par           0.06     0.96     0.28   16.1x    3.5x
    topk               0.28     0.45     0.45    1.6x    1.0x
    topk_par           0.28     1.40     0.23    5.1x    6.1x
    vec                0.27     0.57     0.56    2.1x    1.0x

Three primitives beat or match their C twin on one core: `heap` at 0.9x,
`rng_normal` at 0.8x, `rng` at 1.0x. Most of the package sits between 1.2x and
3.4x. Forking works: fourteen `_par` rows clear 6x on 16 threads and four clear
8x, with `drift_par` highest at 8.7x.

**Two `1T/C` outliers, and they are the same cost.** `sketch` (19.1x) and `text`
(15.4x) are the worst ratios in the library, and both pay it for kind `Data` —
C stores into a flat register file or binary-searches a flat array, while Bend
rebuilds the nodes on the descent path each update. Lane 12 named this
exactly: the gap *is* the cost of `Data`, and what it buys is the refusal, the
free fork, and the 6.6x.

Two lane reports each claim to hold the worst ratio and **neither does**;
both are left standing as the measurement each lane actually took.
`power-5.md` calls `json`'s 5.9x "the worst 1T/C in the library", true when
written — `sketch` and `text` did not exist yet. `power-15.md` calls `text`'s
15.6x "the worst ratio in the package", which was already wrong when written:
lane 12 had reported 17.3x for `sketch`. This table is the authority; a
comparative claim made from inside one lane is not.

`delta`'s `0.00` C column is the harness hitting its two-decimal floor, not a
zero — which means the one ratio that lane is actually about cannot be formed
from this table at all on the C side, and reads only ~83x on the Bend side
(0.83 / 0.01, where the denominator is a single significant figure). Timed
properly, `power-16.md` puts incremental-over-full at **192.8x for C and 131.4x
for Bend**. A package-wide table at fixed resolution is the wrong instrument for
a per-lane question; it is here to compare primitives against C, not against
each other's alternatives.

## Five conventions that bind every file

**No float reaches a printed line.** `F32.log` is `logf` in emitted C and a
rounded `Math.log` in emitted JS — different libm rows, different digits, four
lanes that disagree. So `bm25` quantises to fixed-point U32 at 2^20, `rng.normal`
prints `z + 8` in millionths, and `sketch` has no float in the file at all.
Where a float is genuinely the answer (`fft`, `knn`) it is F32 and only the five
operations IEEE-754 requires to be correctly rounded — add, sub, mul, div, sqrt —
which all three lanes round identically.

**Kind `Data` is what makes a thing forkable.** Anything holding a Base `Array`
is kind `Type`: affine, one owner, and a fork hands it to exactly one side. That
is right for a parser and wrong for a budget. `budget`, `sketch`, `grammar`,
`consequence` and `proof`'s verdicts are all kind `Data` *deliberately*, so they
copy, drop, and ride inside a `Result`. `json` carries its allowance in its own
state instead, and `power-5.md` records why: it was never the allowance that
forced it, it was the Bytes beside it.

**A template parameter, not a runtime argument.** `~f` passes a def by
reference and the compiler specialises the loop with the operator inline.
`radix`'s four passes each compile with their shift as a literal; threaded as a
runtime `Nat`, `U32.shrn` would become a 24-step loop per element.

**One owner, every write in place.** A read hands the container back. This is
not a style choice, it is what affinity gives: no copy, no refcount, and a
compiled index loop over a flat block.

**Fuel counts down.** Every unbounded loop takes a fuel `Nat` and decrements;
exhausted fuel is a refusal with a price attached, never a partial answer and
never a hang.

## Known hazard: dropping an F64 on the C backend

Three lanes hit this independently in three shapes. An `F64` is stored
**unboxed**, so a raw IEEE-754 double rides in a slot the runtime reads as a
`Term`: the exponent becomes a heap tag and the low 40 mantissa bits a heap
address. Sinking such a slot frees a block that was never allocated — a silent
wrong answer, a blank run, `bend: out of memory`, or a memory fault, depending
on what the bogus address lands on. It is deterministic per binary, reproduces
at `--threads 1`, and `--gpu 8GB` does not help.

Exactly two surfaces put a double in that position:

1. **`Array<F64>` cells.** `lay_arr` routes any element wider than `w32` into a
   block whose cells `term_drop` / `blk_copy` / `blk_keep` walk as `Term`s.
   (`Array<Nat>` is walked too and is safe only by accident — `nat_chk` caps a
   `Nat` below `2^48` so its tag is always 0.)
2. **Polymorphic parameters.** A def's signature is memoized by name, so the one
   compiled `Bool.pick` emits `term_sink` on whatever word arrives.

Generic *containers* are fine: `List<F64>`, `Maybe<F64>`, `Pair<F64,F64>` get
real `w64` fields. Whether a given double is a landmine is exact and computable
— safe iff no mantissa bit is set below position 40 — which is why every earlier
magnitude sweep looked random. The earlier "only a *computed* F64" reading is
withdrawn; literals fail too.

Root cause, the measured tables, the bit predicate and what a real fix costs (a
third block mode across four backends, not a one-line flip) are in
`docs/omen/f64-drop-c-backend.md`. The workaround is to prefer F32 or
fixed-point U32 in arrays, and `match` rather than `Bool.pick` at F64.

The F32 workaround is a layout guarantee rather than a lucky sample: `F32` gives
cells of kind `w32`, which take the packed block and are never walked as `Term`s.
Lane 14's earlier hedge — F32 is "correct in every shape run, and it was not run
much" — was the honest thing to say while the cause was unknown, and the
derivation supersedes it.

The same derivation reclassifies the doubles that *passed*. `pi`, `8193` and
`10007` are not safe values; by the bit predicate they are landmines that did not
detonate, the bogus free having landed somewhere the run never read back. Safe is
exactly: no mantissa bit set below position 40, or zero, inf, NaN. This is why
every attempt to find a magnitude threshold failed — there is no threshold, only
the predicate.

## Not built

The packed `File.read_bytes` effect from the plan's substrate row. It needs a
row in `bend2/effs/`, no primitive here reads a file, and adding an effect would
put the whole existing battery at risk for zero consumers. Flagged rather than
silently cut.

## The reports

One per lane, in `docs/omen/lanes/`. Each carries what shipped, the decisions
worth arguing, what was verified, what was measured, the mutants run against the
fixture, and an explicit list of deliberate ceilings. `power-0.md` also holds
the counter-RNG lane, which closed inside it.

The ceiling ledger is **87 entries under `## Deliberate ceilings`, across 19 of
the 20 reports**. `power-0.md` is the one exception and not an omission: it is
the lane that set the convention — its own heading is still the older `Not done
/ next` — and all three of the things it deferred were closed inside the lane.
Sixteen `ponytail:` markers in `power/*.bend` name the corner-cuts that live in
the code rather than in a report, each with its ceiling and its upgrade path.

Every one of these is a known limit someone chose, wrote down, and can be argued
with. None of them is a surprise waiting in the source.
