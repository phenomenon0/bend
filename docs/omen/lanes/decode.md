# Decode lane (2026-09-20)

Branch `lane-decode`, worktree `bend-work-decode`, on `3f5f93b4`. The brief is
build #1 of `bend-parser/reports/glm-explored-ai.md`: a decode step that
returns a certificate, assembled from `power/` with no compiler work.

Result: **Decode PASS: 28, FAIL: 0** (`bash tests/decode/run.sh`). This covers
four fixtures, the demo and the bench. `bun gates/repo.ts` passes with the
new files staged.

What changed:

- new: `power/decode.bend`, `demos/decode/{main,bench}.bend`, `tests/decode/`
  and this report;
- one word in `gates/repo.ts`: `decode` joins the tests folder rule at its
  existing 16,000 cap.

Nothing in `bend2/` was touched, no cap moved, and nothing was pushed.

It found a real bug in `power/grammar.bend`: at the nesting ceiling the mask
and the step disagree. See [The real bug](#the-real-bug-depth-64). It is
pinned here and not fixed, because that file belongs to another lane.

## The API

```
decode_step(vocab, s, logits, k, at) -> Result<Bad, Step>
Step{tok: U32, st: Gr.St, cert: Cert{kept: List<Heap.Entry>, draw: U32}}
check(vocab, s, logits, k, at, step) -> Vd          # Ok{} or No{bad}
```

This maps onto the brief's `decode_step(g, logits, rng)` as follows:

- `g` is the vocabulary plus a grammar state `s`.
- `rng` is `At{seed, stream, pos}`.
- The width `k` is explicit.
- A step that cannot be taken is a `Fail{Bad}` value, not a token.

A token is at most four bytes, packed low byte first into a U32; zero bytes
are padding, which is safe because NUL is never legal JSON. Logits are one
integer weight per token, and a token's id is its position in the list. The
draw is proportional to weight among the kept tokens, which is linear, not
softmax.

The order is (weight, id), greatest first. **Of two equal weights the larger
id ranks higher.** This is `Heap.less`, TopK's own order, and `ties.bend`
pins it.

## Assembled vs written

| Piece | Source |
|---|---|
| Grammar state, `step`, `live`, `mask`/`allows`, `done`, `show` | `power/grammar.bend`, unchanged |
| The exact K heaviest (`new`, `offer`, `drain`) | `power/topk.bend`, unchanged |
| The (weight, id) order, `Entry` | `power/heap.bend`, unchanged |
| The draw, `below(seed, stream, pos, n)`; the demo's model, `u32` | `power/rng.bend`, unchanged |
| Token packing and a token's walk down both grammar paths | written, `decode.bend` |
| The frontier fold (legal and weighted, into TopK), mass, pick | written, `decode.bend` |
| `Bad`, `Vd`, the two-half check, first failure wins | written, `decode.bend` |
| 18-token JSON vocabulary, a hashed toy model, the rollout | written, `demos/decode/main.bend` |

`walk` feeds a token's bytes through the mask path, where each byte must be
allowed by the state before it, and through the step path at the same time.
It returns both. The byte law `allows(s, c) == live(step(s, c))` lifts to
tokens because a dead state stays dead.

## Certificate design

The certificate is the kept list, best first, plus the draw. It has the shape
of a LAWS pair: two opposed tests, and each one alone lets a liar through.

- **The chosen half** runs over the kept list, capped at K+1 entries. Every
  entry must satisfy all of these:
  - it is a real id (**range**);
  - it holds the weight its logit holds (**value**);
  - it is weighted and reached by the grammar's *step* path (**illegal**);
  - it is strictly below its predecessor (**order**).
  - The list also has at most K entries (**over**).

  Alone, it passes the list that skips the best token, since every entry it
  names is genuine.
- **The frontier half** runs over every token. It counts the legal, weighted
  tokens at or above the floor, and the count must equal the kept count
  (**slack**). The floor is the last kept entry when K were kept, and there is
  none when fewer were kept, since then every legal token must be in the
  list. Alone, it passes a fabricated entry swapped in for a real one, because
  the count still comes out right.

Then the draw and the new state are recomputed, since both are pure functions
of what was pinned:

- the mass fits a U32 (**heavy**);
- `draw == below(at, mass)` and the pick lands on `tok` (**draw**);
- `st == step*(s, vocab[tok])` (**state**).

The law is exercised twice. The decoder reads legality off the mask, and the
checker reads it off the step. On every token, the frontier pass also holds
the two paths against each other (**split**). The verdict is the first
failure in this order:

> shape, split, chosen half, over, slack, heavy, draw, state.

### Pinned

- **The demo:** its 14-step rollout, byte for byte, in the interpreter, JS, C,
  and C on one thread.
- **The bench:** 65,536 rollouts' totals on C, on all threads and on one.
- **`mutant.bend`:** 11 forgeries of one honest step, each with its verdict.
  Two extra rows show each half alone letting its liar through: `skip` passes
  the chosen half, and `swap` counts 4 of 4 in the frontier half.
- **`refuse.bend`:** refusals as exact values:
  - `empty` where only illegal tokens are weighted, at a dead state, with no
    weight at all, and at k = 0;
  - `shape` for short logits;
  - the `heavy` boundary: a mass of 2^32 - 1 passes and 2^32 is refused.

  It also pins the checker rejecting steps forged where the decoder refused.
- **`ties.bend`:** the tie order in the decoder, and in the checker, both
  reversed and at K = 1.
- **`rollout.bend`:** determinism. The same rollout twice gives the same
  bytes, while seed 36 and rollout 1 each give different ones. Without the
  second half, the first would prove nothing.

### Checked, per step, by `check`

These are all eleven rejections above: shape, split, range, value, illegal,
order, over, slack, heavy, draw and state. Every rollout step in the demo,
the fixtures and the bench is checked, and the bench reports the failures:
0 of 1,179,656.

### NOT covered

- **The grammar itself.** The checker trusts `grammar.bend`. Split catches the
  mask and the step disagreeing; it cannot catch both agreeing on something
  that is not JSON. During development, 40 seeds' finished documents (37 of
  40; 3 hit the step cap) were parsed by Python's `json.loads`, and all of
  them parsed. That probe is not in the battery.
- **Float logits, softmax, temperature.** Weights are integers so that every
  lane agrees bit for bit.
- **Modulo bias.** `Rng.below` reduces modulo the mass, a relative bias of up
  to mass / 2^32. With the demo's 24-bit weights and K = 4 that is under 1/64.
  This is marked `ponytail:` in the source.
- **Succinctness.** Checking re-reads every logit, so it costs about what
  decoding does. It removes trust in the decoder, not work.
- **Large vocabularies.** `nth` is an O(V) fold, so a check is O(K·V). This is
  marked `ponytail:`.
- **Tokens of 5 or more bytes.** These are out of range, also marked
  `ponytail:`.
- **The inputs.** A certificate is relative to the given vocab, logits, k and
  `At`; it says nothing about where they came from.
- **Wider runs.** The GPU lane and the mini-cluster gates were not run.

## The real bug: depth 64

`push` refuses a 65th container (`power/grammar.bend:257-265`), but `mask.at`
offers `vstart`, which includes 91 `[` and 123 `{`, for `Val` and `Vale`
regardless of depth (`power/grammar.bend:977-980`). So on a *reachable* state
`allows(s, c)` is true while `step(s, c)` is dead:

```
depth 64 vale/64 mask  9-10 13 32 34 45 48-57 91 93 102 110 116 123
depth 64, `[` weighted `[` -> dead/0 split
depth 64, `]` weighted `]` -> sep/63 split
```

`val/64` behaves the same way: 63 `[` then `{"a":` gives a mask that holds 91
and 123, and `[` steps to `dead/0`. The last case was a throwaway probe and
is not pinned.

- **Why the decoder emits `[`:** it trusts the mask.
- **What catches it:** the certificate, as split.
- **Why the `]` step splits too:** the frontier pass tests every token, not
  only the drawn one.

`tests/power/grammar` pins deep documents but no depth-64 mask. That is why
the bug went unnoticed.

**Fix:** outside this lane, one def. Drop `[` and `{` from the Val and Vale
masks when `depth(s) >= 64`, and add a depth-64 `pin` row to
`tests/power/grammar_gen.py`. When that lands, three pins in `refuse.bend`
move, as its header says: `[` refuses (`empty`), `]` passes (`ok`), and the
mask loses 91 and 123.

## Demo output

`bun bend2/main.ts demos/decode/main.bend` prints the following, with seed
35, rollout 0, K = 4, starting from `{`. Each line shows:

- the position and the token;
- the kept list as `weight@id`;
- the draw out of the total mass;
- the new state and the verdict.

```
0 `"a"` kept 15634743@6 15468670@7 11573860@13 11392035@1 draw 15119279/54069308 -> colon/1 ok
1 ` ` kept 11140507@12 2413349@5 draw 483318/13553856 -> colon/1 ok
2 `:` kept 14527481@5 10285782@12 draw 4103405/24813263 -> val/1 ok
3 `[` kept 16756538@9 14754127@2 13480422@10 13199765@6 draw 17570302/58190852 -> vale/2 ok
4 `1` kept 14974288@15 13339763@8 11841958@6 10552938@2 draw 23527677/50708947 -> int/2 ok
5 ` ` kept 14502547@12 9122507@4 8783431@8 8627454@3 draw 7943887/41035939 -> sep/2 ok
6 `,` kept 9745293@12 9651510@3 6330760@4 draw 23052648/25727563 -> val/2 ok
7 `"b"` kept 16635400@7 16133872@10 15587821@14 13526870@11 draw 1317864/61883963 -> sep/2 ok
8 ` ` kept 11571657@12 10723886@3 5457667@4 draw 7316782/27753210 -> sep/2 ok
9 `]` kept 15275906@3 6337863@12 5587899@4 draw 8470311/27201668 -> sep/1 ok
10 `,` kept 10433186@4 4792222@1 2008453@12 draw 4485536/17233861 -> key/1 ok
11 `"a":` kept 10806927@13 9937379@6 9402941@16 1926834@12 draw 10337867/32074081 -> val/1 ok
12 `23` kept 16575347@10 16465202@9 12607437@8 11875068@12 draw 27713353/57523054 -> int/1 ok
13 `}` kept 15742991@4 6822595@8 5855413@1 4879121@12 draw 25739613/33300120 -> fin/0 ok
doc {"a" :[1 ,"b" ],"a":23}
steps 14 done Y bad certs 0
```

Short kept lists are the grammar at work. After a key only ` ` and `:` are
legal, so step 1 keeps two, even with K = 4. The toy model's weight for token
`i` at position `p` is `Rng.u32(seed ^ 0x9e3779b9, rollout, 64p + i) >> 8`.

## Measured

- **Machine:** AMD Ryzen 7 7700X (8 cores, 16 threads), Linux
  `6.17.12-300.fc43.x86_64`, Bun 1.3.4, GCC 15.2.1.
- **Load:** the machine was shared. The one-minute load average was 3.4 to 5.0
  during the C runs and 6.6 after the JS runs; the 15-minute average fell from
  14.7 to 11.2 over the session.

A *step* below is `decode_step` plus `check` of its certificate, since every
rollout checks every step.

**The bench,** `demos/decode/bench.bend`: 2^16 rollouts as a fork/join tree,
1,179,656 steps, with 56,110 documents finished within 48 steps. It gave
`bad certs 0` on every run. The unfinished rollouts either hit the cap or were
refused; the bench does not separate the two.

| Lane | Wall, 3 runs | Steps/s (median) |
|---|---|---:|
| C, 16 threads (`--gpu off`) | 0.49 / 0.50 / 0.54 s, 5.8 s user | ~2.36 M |
| C, 1 thread | 3.35 / 3.37 / 3.35 s | ~352 k |
| JS (Bun), 1 run | 222.7 s | ~5.3 k |

JS is roughly linear in the work: 2^10 rollouts (18,401 steps) take 2.48 s,
about 7.4 k/s, and 2^12 (72,207 steps) take 10.12 s, about 7.1 k/s. It is
about 66x slower than one C thread. The JS lane was not investigated, and the
runner keeps the bench off it.

**The demo** (14 steps) is startup-bound, so it gives no steps/s: 0.43 to
0.44 s interpreted, 0.02 s for JS, and under 0.01 s for C, over three runs
each.

## Caps

All readings are `ttok < FILE`, and every file is under its existing cap. No
row moved, so neither `gates/repo.ts` nor `tests/caps.sh` changed a cap.
`tests/caps.sh` only lists `f64/` and `strings/` tests.

| File | ttok | Cap |
|---|---:|---:|
| `power/decode.bend` | 5,520 | 64,000 |
| `demos/decode/main.bend` | 1,716 | 64,000 |
| `demos/decode/bench.bend` | 454 | 64,000 |
| `tests/decode/*.bend` | 526–1,808 | 16,000 |
| `tests/decode/run.sh` | 1,286 | 16,000 |
| This report | 3,929 | 16,000 |

## Residuals

1. The depth-64 grammar bug above: one def and one pin row, in the grammar's
   lane.
2. The JS lane runs at about 7 k steps/s against 352 k for one C thread,
   unexplained.
3. The bench is not in `bench/runtime/` and has no perf pin; the minis,
   `gates/test.ts` and `gates/perf.ts` were not run from here.
4. `tests/decode/ties.bend` imports helpers from the sibling fixtures
   `mutant.bend` and `refuse.bend`, rather than copying them.
