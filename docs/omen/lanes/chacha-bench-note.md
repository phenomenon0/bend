# chacha bench note — throughput and the resource card (quick protocol)

*Quick protocol (not POWER): three runs, min, one machine (Ryzen 7700X,
16 threads). Benches: `demos/kernels/bench_quick{.bend,_par.bend}` and the C
twin `bench_chacha_ref.c`. 16 MB of keystream, counter 0..262143.*

## 1. The stream, verified before any number counted

Bend's stream was checked against two independent implementations before the
clock was trusted: an independent Python implementation and the portable C
twin, all summing in the same unit (byte-sum, wrapped at 32 bits).

**All three print 2139072639.** The Bend 1-thread run, the Bend forked run
(16 chunks with per-chunk counter offsets — the chunking does not corrupt the
stream), the C twin, and the Python arbiter agree exactly.

The road there cost an hour of harness forensics: three refs, three nonce
conventions, two sum units, one Rust-crate layout subtlety. The mismatches
were all in the harness, never in the stream. A note for every future
cross-language table: **pin the nonce layout and the sum unit in writing
before comparing two numbers.**

## 2. The field (16 MB keystream, one thread unless noted)

| engine | throughput | stream-verified |
|---|---|---|
| OpenSSL 3.5.4 (AVX2 assembly) | ~6,300–7,300 MB/s | n/a (different API shape) |
| Rust, RustCrypto crate | ~1,840 MB/s | no — own convention |
| C twin, portable, -O3 | ~700 MB/s | yes |
| **Bend, 1 thread** | **20.3 MB/s** | yes |
| **Bend, 16 threads** | **47.1 MB/s** | yes (same sum) |
| Bend, GPU path | 0.87 MB/s | yes — and irrelevant in this shape |
| pure Python | 1.04 MB/s | yes |

Bend is ~35× off the plain C twin at one thread, ~15× off it at sixteen —
and 20× ahead of pure Python on the identical algorithm.

## 3. The resource card — what one run costs the machine

| run | wall | CPU | peak RSS | memory amplification |
|---|---|---|---|---|
| Bend 1T | 0.91 s | 98% (one core) | **642 MiB** | **~40× the 16 MB of work** |
| Bend 16T | 0.66 s | **119%** | 177 MiB | ~11× |
| C twin | 0.02 s | 95% | 1.7 MiB | ~0.1× |

Two readings:

- **The forked run barely uses one core (119% CPU).** The per-byte cons
  allocation serializes the threads on the allocator: this shape is
  allocation-bound, so "16 threads" buys almost nothing.
- **642 MiB of resident memory for 16 MB of work.** On a shared or small
  machine this translation would, at size, be felt — exactly the question
  "does it slow down somebody else's computer" answered honestly: in this
  shape, yes.

## 4. Reading it

- The **named-reference translation is correct at scale** — that was its job,
  and it does it (84/84 on the RFC suite before this note; three engines
  agreeing on 16 MB now).
- It is **not the kernel**: per-byte recursion and a cons per byte are why it
  is 35× off C and allocation-bound.
- The fix has a name and a shape: a **words-based kernel** — U64 state in
  registers, an in-place block loop, no cons per byte — which turns the
  resource card into O(1) memory and lets the threads actually pay. That is a
  lane, not a patch.
- **Publish decision: hold.** No speed claim goes out until the kernel
  exists; this note is the receipt set for that future claim, and for the
  honesty standard of finding the harness bugs first.
