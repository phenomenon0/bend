# Conversion policy: specs, laws, and proof backing

Operator directive: **upgrade our conversion policy to not just code correctness
but proof backing.** This extends the existing four-lane and repository gates.
It applies to translated libraries, kernels, parsers, adapters and later rewrites.

## What every conversion ships

1. Pinned vector evidence, with a named independent source and exact outputs.
   Keep strict checking, interpretation, emitted JS and emitted C green.
   Resource probes have explicit budgets and separate, truthful results.
2. An executable independent specification where feasible. It may share Base
   and neutral data types, but must not call implementation helpers or tables.
   If a spec is infeasible, explain the obstacle and the next useful contract.
3. A law inventory naming each public function, domain, observation and status.
   Pair safety with preservation and completeness: rejecting all input cannot
   satisfy a useful validation contract merely because invalid input rejects.
4. Reproducible proof and differential commands, retained results and source
   hashes. State the trusted checker, primitives, transcription and backend.
5. Well-typed negative probes showing which broken implementations the vector
   and proof gates reject. A parse error, crash or timeout is not a caught theorem.

## Status vocabulary

**checked-by-Bend** means a named universal claim has a closed proof accepted
by our dedicated proof gate. Its imported closure has no unsafe definitions,
foreign effects, holes or unfilled laws. Evidence names the exact checked sources.
This is a grade for that claim, not a blanket certificate for the whole artifact.

**differential-backed conjecture** means an explicit unproved statement has
reproducible independent execution evidence. Record seeds, domains, boundaries,
backends, expected-value sources and failures. Keep conjectures in documentation,
outside the trusted proof entry; do not install an open law as a silent axiom.

**none** means no checked theorem or adequate differential evidence supports
that property. State it directly and give a bounded next step where useful.

Vector evidence and strict typechecking are valuable, distinct evidence tiers.
Neither is a universal equivalence proof. Concrete reductions over test vectors
are checked examples, not arbitrary-input correctness. Helper lemmas are graded
at their actual scope until explicitly lifted to the exported function.

## The proof gate is part of the artifact

Follow [PROOF-GATE.md](../PROOF-GATE.md). Check a dedicated entry without `main`;
ordinary execution does not discover neighboring laws. Inspect the parsed
import closure for unsafe/foreign definitions, then check all declarations and
bodies, reject open goals, and emit an explicit verdict with a source receipt.
Protect public claims, independent specs and evidence harnesses during research.
Review changes to these contracts separately from implementation proposals.
A stale receipt never certifies a changed implementation or changed statement.

Laws quantify over arbitrary public inputs without caller-supplied correctness
premises. State domain restrictions and units: eight SHA-256 U32 words are
32 bytes and 64 hex characters. Array capacity, encoding, ignored trailing
storage, integer bounds and exhaustion behavior are part of the contract.

## Specs → proofs → perfect program

Write the specification, challenge it with independent differential evidence,
state the laws, close their proofs, then judge the program by those contracts.
This is the longer arc toward a perfect program relative to an explicit spec;
it is not a claim that the specification or trusted machine is infallible.
An early conversion may carry graded conjectures, but its report must expose
that debt and the next missing lemma. Prefer meaningful public claims over
large counts of easy internal equalities. Preserve output order and content,
not only the output's size. Never weaken a law to fit an implementation.

## Optimization preserves the evidence boundary

The production API and measured API must be the same function covered by the
stated laws. Never present an unproved fast path as a proved production API.
If full equivalence remains conjectural, label the actual production function
accordingly; a structural shape proof does not upgrade its algorithmic grade.
Internal representations and supporting proofs may be rewritten completely,
provided every retained public claim is checked again on the shipped sources.

Freeze an objective contract: editable/protected files, validation command,
benchmark command, workload, compiler, timer boundary and acceptance threshold.
Keep raw samples, warmups, medians and an oracle check for every completed run.
Explain the architectural mechanism before accepting a speed claim. A read-only
independent judge inspects code, proof dependencies and raw evidence; proposer
narratives are untrusted. Missing or inconclusive review is not approval.
Stop an optimization loop after three consecutive attempts without an approved improvement;
retain the best validated candidate and all rejection reasons. Noisy GPU timing
or mismatched hosts/corpora cannot establish CPU gains. A resource limit remains
a measured bound, never an invented throughput or a successful digest check.
