# Kernels pass 2 execution ledger

Authorized: implement and commit in lane-kernels-2; no pushes or merges.
Scope: demos/kernels, tests/kernels, docs/omen, minimal gates/repo.ts allows.
Read: first-pass report/fixtures, gap report, Giulio c77b76c sources, laws,
packed proof, objective, orchestrator and history. Reference tree stays read-only.

- [x] 1. Mutation anchors first; strict-valid mutants, wrong pinned output;
  fix the two inherited repo allows and admit new harnesses explicitly.
- [x] 2. Packed SHA input/word output, ChaCha word block, legacy compatibility.
- [ ] 3. Sixteen named schedule registers; all retained pins in four lanes.
- [ ] 4. Independent specs, seeded differentials before laws; proof-only gate,
  closed universal claims, negative proof checks, explicit remaining conjectures.
- [ ] 5. Fixed-corpus benchmark, raw samples and hashlib checks, million-a bound.
- [ ] 6. Proof-backing policy and FLOW pointer.
- [ ] 7. Research lessons with history evidence and independent review mechanics.
- [ ] 8. Final report, exact caps, review and clean commit checkpoint.

Every slice: stage only its scoped files, run bun gates/repo.ts and diff --check,
then commit with the requested codex identity. No cap raises for existing files.
Algorithm changes: full kernels four-lane battery; proof edits: dedicated gate.
Failure: diagnose before retry; incomplete laws remain prose conjectures, never
open axioms. Benchmark timeout is a censored resource bound, never a pass.
Source-level proofs trust Bend/Base and spec transcription, not compiler/hardware.
Checkpoint 1: control 84/84; 8/8 strict-valid mutants killed in all three
execution lanes. Evidence: ../lanes/kernels-2-evidence/mutations.json.
Next action: validated packed word API; existing hex compatibility.

Checkpoint 2: packed API + ChaCha word block, 24 fixtures x four lanes = 96/96.
