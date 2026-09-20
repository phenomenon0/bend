# Kernels pass 2 — specs, proofs and measured bounds (2026-09-20)

Branch `lane-kernels-2`, worktree `bend-work-kernels-2`, branched from
`lane-kernels-c` at `584d803c`. Continues [kernels-c.md](kernels-c.md),
which shipped the two translations and the four-lane battery. This pass adds an independent
specification, a public law contract with a dedicated proof gate, a seeded
differential harness, a fixed-corpus benchmark, and the conversion policy
those artifacts answer to.

The codex pass stopped mid-write on a usage limit. Its three commits stayed
as they were; everything after `c6a236ba` is a fable commit, written after a
review pass over the uncommitted work. The last section says what that review
changed.

Only `demos/kernels/`, `tests/kernels/`, `docs/omen/` and one widened row in
`gates/repo.ts` are touched. No runtime, compiler, language or Base edits.
No push.

## Slices

| Slice | Commit | Content |
|---|---|---|
| Mutations + allows | `55075604` (codex) | Eight strict-valid vector mutants; two inherited repo allows repaired |
| Packed API | `5f82ca02` (codex) | Validated SHA word buffers, ChaCha word blocks, legacy compatibility |
| Fused schedule | `c6a236ba` (codex) | Sixteen named schedule registers, direct packed block reads |
| Specs + laws + gate | `8cc6886f` | `fips.bend`, `rfc8439.bend`, `spec_state.bend`, `observations.bend`, `LAWS.bend`, `PROOF.bend`, `tests/kernels/proof.ts` |
| Policy | `104aca71` | `plans/proof-policy.md` and the FLOW pointer |
| Tools | `dc8d204d` | `bench.py`, `differential.py`, `proof_mutations.py` |
| Round functions | `d21b8f9b` | `word_xor_assoc`, `u32_xor_assoc` and the five laws they close; two new proof mutants |
| Report | this commit | Law status, mutation evidence, measurements, deviations, caps |

## Law status

Sixteen laws are stated in
[demos/kernels/LAWS.bend](../../../demos/kernels/LAWS.bend) and filled in
[demos/kernels/PROOF.bend](../../../demos/kernels/PROOF.bend). The gate
reports them individually:

```text
$ bun tests/kernels/proof.ts demos/kernels/PROOF.bend
Proof PASS: 16 public laws; closure 911 definitions; no holes, open laws, unsafe or foreign definitions.
```

Receipt: [kernels-2-evidence/proof.json](kernels-2-evidence/proof.json) —
911 definitions in the book, 244 pure dependencies reached, `holes=0`,
`open=0`, eleven hashed sources including `bend2/bend.ts` and the gate
itself. Its `git_head` is `d21b8f9b`, the commit carrying those sources;
this report commit adds no `.bend` file, and `source_sha256` is the binding.

Grades are used literally, per
[plans/proof-policy.md](../plans/proof-policy.md).

| Claim | Grade | What it actually says |
|---|---|---|
| `sha_words_shape` | checked-by-Bend | For every `Array<U32>` and every `Nat` length, the observed leaf count of `B.hash(a, length)` is `Some(8)` when `length <= 4 * capacity` and `None` otherwise, where `capacity` is the `U32` that `Array.size` returns. Shape only. |
| `sha_none_iff_oversize` | checked-by-Bend | Boolean equality, so both directions: reject-all and accept-all are both excluded. |
| `sha_legacy_words_length` | checked-by-Bend | The legacy list entry `S.digest(msg)` yields exactly eight words for every message. |
| `sha_digest_order` | checked-by-Bend | Digest word order equals the independent spec's `F.digest` for an arbitrary state. |
| `sha_initial` | checked-by-Bend | The eight initial words equal the spec's. |
| `sha_constants` | checked-by-Bend | The 64 round constants equal the spec's. |
| `sha_rotation` | checked-by-Bend | `S.rotr(x, n) == F.rotate(x, n)` for arbitrary `x` and arbitrary `n`, not a fixed table. |
| `sha_choice` | checked-by-Bend | `Ch` equals the spec's. |
| `sha_majority` | checked-by-Bend | `Maj` equals the spec's — via `u32_xor_assoc`, not conversion. |
| `sha_small0` / `sha_small1` | checked-by-Bend | σ0 and σ1 equal the spec's — via `u32_xor_assoc`. |
| `sha_big0` / `sha_big1` | checked-by-Bend | Σ0 and Σ1 equal the spec's — via `u32_xor_assoc`. |
| `sha_feed` | checked-by-Bend | Feed-forward addition equals the spec's `F.add`. |
| `chacha_words_length` | checked-by-Bend | `C.words(C.block_words(...))` has exactly 16 words for every typed key, counter and nonce. |
| `chacha_block_bytes_length` | checked-by-Bend | `C.block(...)` has exactly 64 elements. Length only. |
| SHA byte conformance | differential-backed conjecture | `O.words(S.digest(msg)) = F.sha256(msg)` for every finite message. |
| SHA packed conformance | differential-backed conjecture | `B.hash(a, n)` observes `Some(F.sha256(first n bytes))` when `n <= 4 * capacity`, else `None`; trailing bytes after `n` are ignored. |
| ChaCha block conformance | differential-backed conjecture | `C.words(C.block_words(key, ctr, nonce))` equals `R.block(...)` in RFC word order. |
| SHA message schedule | **none** | No window invariant relates the sixteen fused registers to the chronological schedule. |
| SHA padding and length encoding | **none** | No proof of the 0x80 marker, the zero count, or the 64-bit big-endian length. |
| SHA block induction | **none** | No proof that the compression loop composes across blocks. |
| Packed-to-byte bridge | **none** | Nothing proves the packed `Array<U32>` reading agrees with a byte list. |
| ChaCha quarter-round, rounds, feed-forward | **none** | Not one component law. `rfc8439.bend` exists but is only used differentially. |
| ChaCha stream (`crypt`, `keystream`) | **none** | No law and no independent spec at all. Its only evidence is the pinned RFC vectors. |
| Counter exhaustion | **none** | The `None` at counter overflow is fixture-pinned, not proved. |
| Compiler correctness, constant time, security | **none** | Out of scope; the trust string in the receipt names this. |

Read the checked column narrowly. Eleven of the sixteen relate a production
*component* to the spec's component; they do not compose into algorithm
equivalence, and nothing in the table forbids a digest of eight zero words.
`Array.size` is Base's power-of-two capacity read off the left spine, not a
count of arbitrary leaves — the bounds laws name that exact operation, so
they apply to well-formed balanced storage.

### The five laws this pass added

The codex pass left `majority`, σ0, σ1, Σ0 and Σ1 with no law, and its design
note recorded why: "different grouping in independent U32 arithmetic also
needs associativity lemmas, not assumed rewrites." The production code
associates left, `fips.bend` associates right, and nothing in Base bridges
them — Base proves `Word.add_comm` but no xor law, and `Word.xor` recurses
structurally down the bit spine.

`PROOF.bend` now proves `word_xor_assoc` by induction on that spine, with
eight explicit head cases because the head bit of each side must be reduced
before `Equal.cong` applies; `u32_xor_assoc` lifts it through the wrapper.
Each of the five laws is then one application. A first attempt factored the
eight cases into a helper that called `word_xor_assoc`; Bend rejects that —
"an unfilled law is a dead claim: live code cannot use it" — so the `cong`
is inlined per case and the recursion stays self-recursion.

`sha_rotation` was already checked, so σ and Σ needed no rotation lemma.
Addition regrouping is not needed by any current law and has no lemma.

## Mutation evidence

### Vector mutants — `bash tests/kernels/mutations.sh`

Eight strict-valid implementation mutants, each typechecking cleanly and each
producing wrong output in all three execution lanes.
Evidence: [kernels-2-evidence/mutations.json](kernels-2-evidence/mutations.json).

| Kernel | Mutation | Fixture | Strict check | Rejected by |
|---|---|---|---|---|
| sha256 | initial state | `sha_abc` | passes | interpret, js, c |
| sha256 | rotation | `sha_abc` | passes | interpret, js, c |
| sha256 | padding marker | `sha_empty` | passes | interpret, js, c |
| sha256 | padding boundary | `sha_448` | passes | interpret, js, c |
| chacha20 | rotation | `chacha_quarter` | passes | interpret, js, c |
| chacha20 | round count | `chacha_block` | passes | interpret, js, c |
| chacha20 | constant | `chacha_zero` | passes | interpret, js, c |
| chacha20 | counter advance | `chacha_65` | passes | interpret, js, c |

`Mutations PASS: 8/8`.

### Proof mutants — `python3 tests/kernels/proof_mutations.py`

Eleven probes: six well-typed implementation mutations that a law must
reject, two well-typed *statement* mutations that the gate must reject
(the gate is sensitive to the law text, not only to the implementation), and
three gate-boundary probes.
Evidence: [kernels-2-evidence/proof-mutations.json](kernels-2-evidence/proof-mutations.json).

| Probe | Kind | Result |
|---|---|---|
| seven actual digest leaves | theorem | strict-valid, proof rejected |
| reject exact capacity | theorem | strict-valid, proof rejected |
| accept oversize | theorem | strict-valid, proof rejected |
| wrong initialization | theorem | strict-valid, proof rejected |
| wrong sigma0 rotation | theorem | strict-valid, proof rejected |
| majority drops a term | theorem | strict-valid, proof rejected |
| digest size claimed seven | statement | well-typed, proof rejected |
| rejection claims nothing | statement | well-typed, proof rejected |
| `@unsafe` definition in closure | gate | `Error: unsafe dependency: poison` |
| unfilled law in closure | gate | `Error: holes=0, open=1` |
| named hole in closure | gate | rejected by `book_valid` before the hole counter |

`Proof mutations PASS: 6 theorem probes, 2 statement probes, 3 gate probes`.

The falsifications are real type errors, not crashes. The shortest one, from
the mutant that replaces `Maj`'s `x AND z` term with a second `y AND z`:

```text
Error:
- expected : {U32.xor(U32.xor(U32.and(x, y), U32.and(y, z)), U32.and(y, z)) == U32.xor(U32.and(x, y), U32.xor(U32.and(x, z), U32.and(y, z))) : U32}
- observed : {U32.xor(U32.xor(U32.and(x, y), U32.and(x, z)), U32.and(y, z)) == U32.xor(U32.and(x, y), U32.xor(U32.and(x, z), U32.and(y, z))) : U32}
Location: LAWS.sha_majority
Proof FAIL
```

## Differential evidence

`python3 tests/kernels/differential.py`, seed `39224377`: 26 SHA cases with
five observations each and 11 ChaCha cases with two, every case run through
all four lanes, SHA expectations from CPython `hashlib` and ChaCha from a
separate Python RFC transcription plus the RFC's own pins. Elapsed 129.0 s,
three parallel batches, all exit codes 0, `source_stable: true`.
Evidence: [kernels-2-evidence/differential.json](kernels-2-evidence/differential.json).

The harness also asserts the spec import boundary — `fips.bend` and
`rfc8439.bend` import only `Base` and the neutral `spec_state.bend`, never an
implementation helper or table. It copies sources into a hyphen-free scratch
tree first, because emitted JS identifiers break on a hyphen in the checkout
path.

This is finite execution evidence. It does not make the three conjectures
theorems, and the report does not use it as one.

## Benchmark

`python3 tests/kernels/bench.py` on the pinned host: AMD Ryzen 7 7700X,
Fedora 6.17.12, Bun 1.3.4, clang 21.1.7, `--threads 1 --gpu off`, median of
three samples after one warmup. The timer boundary is **end-to-end process**
— input construction, hash, hex, startup and output — with compilation
excluded. Every warmup and every sample digest is checked against
`hashlib.sha256`; a case with no completed digest records a bound instead.
Measured API: `B.hex(B.hash(Array<U32>, byte_length))`.
Evidence: [kernels-2-evidence/bench.json](kernels-2-evidence/bench.json).

| Case | Bytes | Median (s) | End-to-end B/s | Digest checked |
|---|---:|---:|---:|---|
| `empty` | 0 | 0.000792 | — | yes |
| `abc` | 3 | 0.000760 | 3.9 K | yes |
| `pattern-55` | 55 | 0.000735 | 74.8 K | yes |
| `pattern-56` | 56 | 0.000839 | 66.7 K | yes |
| `pattern-64` | 64 | 0.000830 | 77.1 K | yes |
| `pattern-1024` | 1,024 | 0.000892 | 1.15 M | yes |
| `million-a` | 1,000,000 | 0.010373 | 96.4 M | yes |

The six sub-kilobyte rows are process-startup dominated: their spread is
about 0.1 ms across a 20× range of input, so they measure the binary's
fixed cost, not the kernel's throughput. Only `million-a` is large enough
for its rate to mean anything.

`bench.json` records `git_head: c6a236ba` because it was run before the
proof slices landed. The six sources it measured — `base.bend`, `bend.ts`,
`comp.ts`, `main.ts`, `buffer.bend`, `sha256.bend` — all still hash-match
this tree, verified against the receipt's `source_sha256`; the later commits
added only specs, proofs and harnesses. The source hashes are the binding,
not the head.

An earlier run overlapped with validation jobs and is retained separately as
[kernels-2-evidence/bench-exploratory.json](kernels-2-evidence/bench-exploratory.json).
It is not the reported run.

### Million-`a` as a resource bound

Re-measured on this tree under `/usr/bin/time -v`, three runs each, idle
machine. Both completing lanes print exactly the RFC 6234 pin
`"cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"`.

| Lane | Wall (s) | Max RSS (kB) | Output |
|---|---|---:|---|
| C (`--threads 1 --gpu off`) | 0.08 / 0.08 / 0.08 | 25,424 / 25,584 / 25,452 | expected digest |
| JS (bun) | 1.51 / 1.42 / 1.46 | 213,032 / 219,020 / 218,588 | expected digest |
| interpreter | killed at 120 (limit) | 4,134,768 | **empty**, exit 124 |

The lane brief's reference numbers for this fixture, taken on this host
before the fused-schedule commit, were C 0.34 s / 25.5 MB and JS 4.26 s /
264 MB. C is now roughly 4× faster at the same resident set; JS is roughly
3× faster and holds about 45 MB less. Pass 1's own report gives no wall
times for these lanes, so that is the only comparison available.

The interpreter figure is a **censored bound**, not a throughput: no digest
completed, so no rate can be quoted, and `bench.py` records it that way
(`resource_bound`, `digest_checked: false`). `bash tests/kernels/run.sh
--million` still exits 1 with `Kernels PASS: 3, FAIL: 1` at its 30 s budget;
that optional run has never been counted as a four-lane pass.

## Verification run on this tree

Every command below was run at `d21b8f9b`, in this worktree.

| Command | Result |
|---|---|
| `bash tests/kernels/run.sh` | `Kernels PASS: 96, FAIL: 0` |
| `bash tests/kernels/mutations.sh` | `Mutations PASS: 8/8` |
| `bun tests/kernels/proof.ts demos/kernels/PROOF.bend` | `Proof PASS: 16 public laws` |
| `python3 tests/kernels/proof_mutations.py` | `6 theorem probes, 2 statement probes, 3 gate probes` |
| `python3 tests/kernels/differential.py` | `status: pass`, 26 SHA + 11 ChaCha |
| `python3 tests/kernels/bench.py` | complete corpus, every digest checked |
| `bun gates/repo.ts` | `PASS: 54 / 54` |

## Deviations

1. **Fixture count.** The brief says 21 fixtures; the tree has 24, so the
   battery is 96/96, not 84/84. Pass 1's 21 were extended by `5f82ca02`.
2. **`PASS: 54 / 54` is a rule count, not a file count.** `gates/repo.ts`
   prints `RULES.length - fails / RULES.length`. The brief's "45/45" was a
   file-count reading of an older tree; no file-level total is reported by
   that gate.
3. **`run.sh --selftest`'s hole probe is weaker than its comment.** It writes
   a bare `?`, which this Bend version rejects as a *parse* error
   ("expected : a name / observed : end of input"), so the probe proves the
   suite rejects an unparseable fixture rather than a hole. It is committed
   code from pass 1 and was left alone; `proof_mutations.py` covers the real
   hole case.
4. **`bench.json` head is stale by design.** See above; the source hashes
   bind it, and they were re-verified against this tree.
5. **Interpreter lane on million-`a` still does not complete.** Reported as a
   bound in every artifact that mentions it.
6. **ChaCha has no component laws.** `rfc8439.bend` was written and is used
   differentially, but no law relates it to `chacha20.bend`. The two ChaCha
   laws are length claims only. This is the largest remaining gap and is the
   obvious next slice.

## Cap ledger

All readings are `ttok < FILE`, measured on the committed files. Every new
file matches a pre-existing allow row; **no cap was raised**.

| File | bytes | ttok | Rule | Cap |
|---|---:|---:|---|---:|
| `demos/kernels/LAWS.bend` | 2,370 | 825 | `demos/*/[A-Za-z0-9_]+.bend` | 64,000 |
| `demos/kernels/PROOF.bend` | 6,910 | 2,358 | same | 64,000 |
| `demos/kernels/fips.bend` | 4,771 | 1,971 | same | 64,000 |
| `demos/kernels/rfc8439.bend` | 2,009 | 884 | same | 64,000 |
| `demos/kernels/spec_state.bend` | 170 | 61 | same | 64,000 |
| `demos/kernels/observations.bend` | 1,032 | 306 | same | 64,000 |
| `tests/kernels/proof.ts` | 5,002 | 1,328 | `tests/kernels/(...)` | 16,000 |
| `tests/kernels/proof_mutations.py` | 6,454 | 1,592 | same | 16,000 |
| `tests/kernels/differential.py` | 11,031 | 3,005 | same | 16,000 |
| `tests/kernels/bench.py` | 13,318 | 3,144 | same | 16,000 |
| `docs/omen/plans/proof-policy.md` | 5,333 | 1,007 | `docs/omen/**` | 16,000 |
| `docs/omen/plans/kernels-2-proof-design.md` | 5,261 | 1,128 | same | 16,000 |
| `docs/omen/lanes/kernels-2-lessons.md` | 5,352 | 1,087 | same | 16,000 |
| `kernels-2-evidence/proof.json` | 1,820 | 781 | same | 16,000 |
| `kernels-2-evidence/proof-mutations.json` | 9,066 | 3,469 | same | 16,000 |
| `kernels-2-evidence/differential.json` | 1,882 | 843 | same | 16,000 |
| `kernels-2-evidence/bench.json` | 32,452 | 10,733 | same | 16,000 |
| `kernels-2-evidence/bench-exploratory.json` | 32,041 | 10,536 | same | 16,000 |
| `gates/repo.ts` | 4,726 | 1,680 | `gates/(...).ts` | 6,000 |
| This report | 20,799 | 5,982 | same | 16,000 |

The gate compares bytes when they are under the cap and falls back to `ttok`
only when they are not, so the two JSON evidence files above pass on their
token count.

The one `gates/repo.ts` edit, in `8cc6886f`, widens an existing row's
alternation to name the four new harnesses. No row was added, so the rule
count is unchanged at 54:

```diff
-allow(/^tests\/kernels\/(run\.sh|mutations\.sh|slow\/sha_million\.bend)$/, 16000);
+allow(/^tests\/kernels\/(run\.sh|mutations\.sh|proof\.ts|proof_mutations\.py|differential\.py|bench\.py|slow\/sha_million\.bend)$/, 16000);
```

## Codex pass cut short by usage limit; fable reviewed, verified, finished

The codex pass committed three slices and then stopped mid-write on its
subscription limit, leaving `LAWS.bend`, `PROOF.bend`, the four spec files,
the four harnesses, two plan documents and the lessons note uncommitted. Its
own summary claimed eleven passing laws, four rejected proof mutations, and
explicitly conjectural algorithm equivalence.

What the review found, in order of how much it mattered:

1. **`proof_mutations.py` had never been run to completion.** Its hole probe
   expected the gate to print `holes=1`, but a named hole is a type error
   that `B.book_valid` rejects before `proof.ts` ever reads `book.hols`. The
   script died on its last probe. There was no proof-mutations evidence file
   in the WIP, which is what gave it away — every other harness had one. The
   probe now expects the real marker, and the file is committed with its
   output.
2. **Five round functions had no law, and the reason was recoverable.** The
   design note named the obstacle but treated it as future work. It took one
   induction on `Word`'s bit spine plus a wrapper lift; the five laws are
   now checked, taking the contract from eleven to sixteen. Two new
   strict-valid mutants confirm the laws constrain the functions rather than
   restating them.
3. **The new laws needed their own negative probes.** A law with no falsifying
   mutant is an untested law. `wrong sigma0 rotation` and `majority drops a
   term` were added for exactly that reason.
4. **The numbers in the handoff were stale.** 21 fixtures is 24; 45/45 is
   54/54 and counts rules rather than files; the million-`a` figures predate
   the fused-schedule commit and were re-measured here.
5. **The narrative held up everywhere else.** The two plan documents and the
   lessons note were read in full against the code and the evidence, and
   their claims match what runs. `proof.ts` genuinely implements every rule
   in [PROOF-GATE.md](../PROOF-GATE.md) — dedicated entry, closure inspection
   rather than last-theorem annotation, a verdict that is not the exit code,
   source re-read to catch mid-check edits, and a receipt bound to the
   sources. The grading vocabulary in the policy is used literally in the
   table above, including where the honest grade is **none**.

Nothing in this lane was upgraded to fit the report. Where a claim could not
be proved, it is listed as a conjecture with its evidence, or as **none**
with the missing lemma named in
[plans/kernels-2-proof-design.md](../plans/kernels-2-proof-design.md).
