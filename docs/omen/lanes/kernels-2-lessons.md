# Kernels pass 2: lessons from Giulio's research loop

Read-only reference: `~/split/giulio-sha256`, HEAD `c77b76c`.
Sources: `OBJECTIVE.md`, `ORCHESTRATOR.MD`, `LAWS.bend`,
`packed_proof.bend`, `CORRECTNESS.md` and the commits below.
This is a study of checked-in contracts/history, not a reproduction of his scores.

## What the loop actually contracted

His objective names the benchmark and validation commands, protected files,
editable implementation/supporting proofs, metric, patience, repeats and deltas.
Validation precedes measurement. A candidate must preserve the unchanged public
claims and close its supporting proofs before a performance review.
The judge is read-only and treats proposer narratives, comments and logs as
untrusted. It inspects changed source, traces every public proof to the independent
specification and asks for a concrete performance mechanism.

His score is the best complete CPU-mode total: sum medians over all workloads
within one mode, then choose sequential or parallel. Across three whole reports,
compare the median score. Do not combine per-size winners or best individual
samples. Acceptance requires a repeatable gain above 3%, beyond noise.
Compilation, input preparation, presentation and startup are outside his timer.
Our pass-2 benchmark deliberately reports an end-to-end process boundary instead;
its numbers cannot be substituted into his leaderboard.

## History and the mechanics we adopt

| Evidence | Lesson and adoption |
|---|---|
| `e7790b7` | Stop after three consecutive attempts without an approved improvement; no total iteration cap. Only independent approval resets patience. |
| `6af3140` | GPU research measurements were disabled and excluded from CPU scoring. Optional GPU diagnostics are not acceptance evidence. |
| `76a3af5` | Put Clang's module cache in writable temporary scratch; setup failure is not algorithm failure. |
| `6e3be5f` | Negative probes must remain well-typed, including dependent digest wrappers. Definition ordering can otherwise reject a probe before the intended law. |
| `17961e8` | New byte-digest proofs must remain in the frozen contract; retaining an older theorem subset loses coverage. |
| `1ba9a6d` | Supporting lemmas may change, but the public claims must remain unconditional and all-input. |
| `b3159d7` | Full implementation/proof rewrites are permitted inside the editable boundary. A large diff is not itself a reason to reject. |
| `b4660d7` | Consider representation, allocation, fusion and redundant traversal before local tuning; explain concrete obstacles when choosing a small change. |
| `b3ce430` | Short measurements require trusted calibration of the whole suite; retain actual corpus sizes and normalized times. |
| `c47f5f6` | Validation must survive `python -O`; use explicit failures rather than removable Python asserts. |

Our next research loop will freeze a local objective before attempts: source
boundary, public contract, gates, fixed corpus, pinned host/compiler, timer,
repeat count, minimum meaningful gain and patience. The independent judge reads
raw samples and source diffs, recomputes the metric and traces proof coverage.
Failed, missing or inconclusive review leaves a candidate unapproved. Rejected
experiments and their exact causes remain available to later attempts.
This pass adopts the contract discipline; it does not claim to have run Giulio's
three-repeat optimization contest or beaten his results.

## Proof craft worth retaining

His `LAWS.bend` uses explicit universal equality against a separate spec. The
packed proof builds from register compression through sixteen readers, padding,
block induction, validation and digest observation. Symbolic round counts keep
large fixed computations out of intermediate proof reduction.
Affine inputs need care: his proof-only Tree/reify witness permits symbolic
reuse of an array without making the running algorithm duplicate it.
A helper's size theorem becomes a public guarantee only through a checked lift.
Our bounds/shape proof uses the ownership-threaded size pair as the lemma
boundary, avoiding any runtime proof traversal.

Latest production code has an array API, while some objective text and the
historical list theorem refer to the legacy model. Always trace the current
exported function; a surviving theorem about an unused model proves nothing
about the measured implementation. His packed-spec theorem also explicitly
leaves the universal byte-list-to-packed bridge unproved. Preserve that honesty.

## Pitfalls encountered here

The first differential harness imported a checkout path containing a hyphen;
emitted JS identifiers then failed. A private source snapshot with local imports
fixes the harness without changing the compiler. That failed run is not a pass.
A very large Nat literal in the first spec was replaced by `U32.to_nat`, following
FLOW's existing authoring rule. The final differential run checks that correction.
Base's Array.size reports power-of-two capacity from the left spine, not a count
of arbitrary tree leaves. Public bounds laws name that exact operation; packed
byte semantics require well-formed balanced storage within Base/runtime limits.
The first benchmark overlapped validation and is retained as exploratory evidence;
report timing uses a later run without our validation jobs competing for CPU.
