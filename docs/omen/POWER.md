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
