# Kernel proof contract and remaining design work

The production functions are `buffer.hash`, `sha256.digest`/`sha256.hash`, and
`chacha20.block_words`/`block`/`crypt`. `LAWS.bend` states only closed claims;
`PROOF.bend` fills them without unsafe definitions or correctness premises.
Run `bun tests/kernels/proof.ts demos/kernels/PROOF.bend RECEIPT.json`.
The gate checks all imported terms, rejects unsafe annotations, traverses parsed
references to exclude foreign effects from pure dependencies, rejects open
laws/holes and unexpected imported-definition overrides, and hashes the sources.
Base declares unused IO effects; those declarations are not pure dependencies.

## Checked scope

`sha_words_shape` observes actual digest leaves and quantifies over every Array
and length. Its right side is Some(8) when length <= 4*Base.Array.size, else None.
`sha_none_iff_oversize` independently expresses both directions of rejection.
The proof factors through `sized(length, pair)` so the affine input is consumed
once. Boolean cases lift a state-level leaf-count proof through `checked`, then
the public theorem composes `Array.size`. No proof code runs while hashing.
These laws reject both accept-everything and reject-exact-capacity mutants.
SHA-256's eight U32 words represent 32 bytes, or 64 hexadecimal characters.

Additional checked claims cover legacy word-result size, state-to-digest word
order against the independent spec, initial state, constants, arbitrary rotation,
choice, majority, both sigma and both Sigma round functions, feed-forward, and
actual ChaCha public word/block lengths (16/64). The five round-function laws
quantify over arbitrary U32 inputs and are proved, not conversions: production
and spec associate their xor chains differently, so each one consumes the
`u32_xor_assoc` lemma below.
A zero-valued eight-word digest could still satisfy shape: content equivalence
must not be inferred from these claims. The initialization/order lemmas connect
specific components to the spec, not the entire compression/padding composition.

## Differential-backed conjectures, not theorems

1. **SHA byte conformance:** for every finite `msg : List<U32>` shorter than
   2^61 bytes, `O.words(S.digest(msg)) = F.sha256(msg)`, where each U32 contributes
   its low eight bits. The legacy hex function renders that digest in order.
2. **SHA packed conformance:** for a balanced power-of-two Array with depth <=31,
   let cap be Base.Array.size and msg its first n bytes in big-endian word order.
   If n <= 4*cap, observing `B.hash(a,n)` yields Some(F.sha256(msg)); otherwise
   it yields None. Bytes after n, including the last word's low bytes, are ignored.
   This claim additionally assumes the concrete backend can represent/allocate
   the chosen input; compiler/resource semantics have no theorem here.
3. **ChaCha block conformance:** for every typed eight-word key, U32 counter and
   three-word nonce, `C.words(C.block_words(key,counter,nonce))` equals the
   independent `R.block(key_words,counter,nonce_words)` in RFC word order.

`python3 tests/kernels/differential.py` challenges these claims with a fixed seed,
26 SHA cases and 11 ChaCha cases, across all four lanes. SHA expected words come
from CPython hashlib; ChaCha has a separate Python RFC transcription plus RFC
pins. Exact structural equality preserves every word and its order. These are
finite observations, not universally quantified evidence. See the report's
source-bound receipt and the retained corpus for exact cases and outcomes.

## Missing lemmas and the next proof attempt

The SHA spec uses a chronological list schedule and whole-message padding;
the production code uses sixteen registers and packed reads. Closing conformance
requires a window invariant relating each register to the chronological schedule,
a round-state simulation, and induction across blocks. The grouping obligation is
now discharged: `PROOF.bend` proves `word_xor_assoc` by induction on the bit
spine, with eight explicit head cases because `Word.xor` recurses structurally
and Base proves no xor law; `u32_xor_assoc` lifts it through the `U32` wrapper.
Those two lemmas close all five round-function laws with no assumed rewrites.
Addition regrouping is not needed yet and has no lemma. The schedule/padding
obligations remain: prove partial-byte masking, padding count and high/low
length encoding;
compose these with word serialization and the already-checked capacity wrapper.
The packed-to-byte bridge is its own obligation; importing a packed model's
proof would not discharge it. Preserve the public statements while replacing
supporting lemmas if a better architecture emerges.

For ChaCha, prove list-index update/lookup laws, each quarter-round wiring, then
induct over ten double rounds and feed-forward. Stream encryption additionally
needs byte-prefix, XOR, length preservation and counter-exhaustion invariants.
Full stream equivalence, compiler correctness, constant-time behavior and
cryptographic security currently have grade **none**. Existing cipher vectors
remain execution evidence, not a stream theorem.

No claim in this design note is installed as an open law. Benchmark results
refer to the same production functions and inherit these exact proof limits.
