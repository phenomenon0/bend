# PROOF-GATE — how "proved" claims must be gated in this repo

Source: independent Bend 2.0.4 audit (P05–P08, P12), package at
`~/Documents/Project/bend-research/bend_audit/`. Those experiments showed, executed:
`main` does not auto-discover/check neighboring LAWS/PROOF files; an `@unsafe`
false proof exits 0 with a warning; that warning disappears in run/emit modes;
exit-code-only CI therefore accepts the escape hatch; and a law with a missing
preservation clause (P12) admits absurd implementations.

## Rules (mandatory once any proof/law entry exists; binding for the lint workstream L1+)

1. **Dedicated proof entry.** The only thing whose success counts as a proof
   verdict is a proof-only entry point (no `main` semantics), checking exactly
   the sources being shipped. Bind it to the revision (hash in the receipt).
2. **Dependency-closure check, not last-theorem annotation.** Reject any
   claimed theorem whose closure contains an `@unsafe` definition, an open
   law/hole, or a missing import — structurally, not by convention.
3. **Exit code is not a verdict.** Never equate `exit 0` of run/emit/check with
   "proof valid"; the proof gate's own exit + log is the artifact.
4. **Protected law files.** Law/proof edits are reviewed like code; an agent
   prompt saying "don't touch the laws" is not access control.
5. **Write preservation, not only safety.** Pair each property with its
   completeness counterpart where intent demands (sorted ⇒ sorted + length +
   multiset intent stated; a money law needs bounds as well as conservation),
   and state explicitly in the file what is NOT guaranteed.
6. **Deployment binds to the checked revision** — the artifact carries the
   source hash the gate passed on.

## Status here

- F64 and strings sections today ship **laws-as-interface** checked by the
  type checker — claims about them say "checker-enforced", never "proved".
- These rules become hard gates when L1 (lint/verifier) lands with real
  proof obligations.
