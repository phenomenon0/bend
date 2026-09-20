# LAWS.md — the shapes behind the power laws (a registry, not a law file)

*Rationale: the power library's laws are individually owned — each module states its own, pinned to its own rows — but the laws are not 25 unique inventions. They are five recurring DIAGRAMS plus one pervasive property. This file names the shapes once so the vocabulary is shared and the assurances are legible across modules. It contains no code on purpose.*

Three rules that keep this honest:

1. **Modules own their statements.** A law lives in the file it is about, in that file's own voice, pinned to its own test rows. This registry never replaces a statement, only classifies it.
2. **New laws name their shape.** When a module states a law, it should be one of the shapes below, or it should say why it is not. Naming forces the question "have we seen this diagram before?" at the moment the law is written.
3. **Shared CODE arrives only as witnesses** (`proof.bend`-style checkers, one interface, mutation-tested) **and only pairwise first.** When a SECOND real consumer needs the same lemma, promote that pair — do not build a universal law file speculatively. The known candidate: delta's consolidation already couples `scan`/`radix`; if it needs a shared lemma, that pair goes first, and generalization happens from evidence, never from aesthetics.

## The five shapes

### 1. Roundtrip / inverse — `op₂(op₁(x)) == x` (or: two coordinates of one object must agree)
| Instance | Statement (module's voice) | Pinned |
|---|---|---|
| budget | `join(split(b)) == b` — a fork neither loses nor invents | tests/power/budget.bend |
| fft | forward ∘ inverse; "the inverse cannot disagree about a twiddle" | tests/power/fft.bend |
| text | for every normalized offset `o`, `(s,e) = back(o)`: `norm(original[s..e])` is exactly the normalized bytes of that segment | tests/power/text.bend rows |
| drift | "the inverse of merge: what the suffix saw, given the whole and its prefix" | drift_gen.py, asserted at the quantum |

### 2. Conservation / accounting — the parts sum to the whole
| Instance | Statement | Pinned |
|---|---|---|
| budget | `used(b0,b,m) + left(b,m) == left(b0,m)` — nothing leaks | tests/power/budget.bend ("law 4 in one row") |
| sketch | weighted streaming does not cost the law (mass preserved under the exact integer mapping) | tests/power/sketch.bend |
| delta | Z-set weights: insert and delete are one addition; weights survive every operator | tests/power/delta.bend |
| text | offset counts: normalized offsets partition the original spans | tests/power/text.bend |

### 3. Monotone / bounded — order is preserved; nesting cannot exceed its container
| Instance | Statement | Pinned |
|---|---|---|
| budget | `cap(outer, inner) <= outer`, meterwise — nested code cannot raise a limit | tests/power/budget.bend |
| knn | square root is monotone, so it changes no ranking | tests/power/knn.bend |
| select | both halves are monotone in the gain | tests/power/select.bend |
| delta | consolidation preserves the multiset up to radix order | tests/power/delta.bend |

### 4. Agreement of two paths — `op₁(x) == op₂(op₃(x))`; two computations of the same observable must agree
| Instance | Statement | Pinned |
|---|---|---|
| budget | `afford(b,m,n) == is_done(spend(b,m,n))` — a caller is never told yes then refused | tests/power/budget.bend |
| grammar | `allows(s,c) == live(step(s,c))` for EVERY byte of EVERY reachable state | tests/power/grammar.bend |
| consequence | two readings whose action traces agree are ONE reading (collapse keeps one representative per distinct trace) | tests/power/consequence.bend |
| text | slicing agrees with normalization by construction (the norm of a segment IS the segment of the norm) | tests/power/text.bend |

### 5. Certificate pair — an answer + a witness, TWO opposed tests, either half alone acceptable by a liar
The library's distinctive shape. One pattern, six instances: **the only shape whose shared code spine already exists — `power/proof.bend` itself.**
| Instance | The pair | Pinned |
|---|---|---|
| proof · sort | permutation AND output; plus `out[i] == in[perm[i]]` | tests/power/proof.bend |
| proof · topk | chosen indices AND the (K+1)-th threshold, checked both ways | tests/power/proof.bend |
| proof · path | feasibility (`d[v] <= d[u]+w`) AND tightness | tests/power/proof.bend |
| proof · assign | matching AND dual prices (`u[i] <= c[i][j]+w[j]` + complementary slackness) | tests/power/proof.bend |
| assign (search side) | the matching and the permutation that generates it | tests/power/assign.bend |
| blake3 | "both sides of one" — the fork law needs both halves | tests/power/blake3.bend |

**Counting/DoS rule for the shape (co-owned):** a witness is untrusted input, so every checker in this shape must be budget-bounded (`power/budget.bend`) and mutation-tested. This rule already lives in proof.bend's design; it is restated here because it binds ALL future instances.

## The pervasive property

**Determinism by construction** — same input, same output, no luck: fft ("not by luck"), drift (every law asserted at the quantum), sketch (no float in the streaming path), blake3 (tree), rng (streams). Mostly implicit; named here so it stops being invisible.

## What this registry is not

- Not a module. Not imported. No code.
- Not a claim that the remaining modules lack laws "yet" — many are oracle-pinned by design (rng, vec, bytes, bitset, heap, topk, scan, radix, json, bm25, postings, cdc); their oracle-equality across six lanes IS their assurance, and the oracle is the law where no better statement exists.
- Not closed: a future module may state a sixth shape, and that should show up here first as a question, not as a framework.
