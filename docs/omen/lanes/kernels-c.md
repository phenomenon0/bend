# C kernels lane (2026-09-20)

Branch `lane-kernels-c`, worktree `bend-work-kernels`, off `omen` at
`ac994157`. Handoff: [kernels-c-brief.md](../plans/kernels-c-brief.md).

Two standalone, pure Base demos translate the reference C algorithms into
Bend. The default battery has 21 fixtures, each checked strictly, interpreted,
emitted to JS and emitted to C. Final default result: **Kernels PASS: 84, FAIL: 0**.
The optional million-`a` probe passes check, JS and C; the interpreter times
out at 30 seconds with no output. The expected digest is unchanged.

Only `demos/kernels/`, `tests/kernels/` and `docs/omen/` are changed.
No runtime, compiler, language, Base or gate edits. No push.

## References and translation

### ChaCha20

[demos/kernels/chacha20.bend](../../../demos/kernels/chacha20.bend) follows
[RFC 8439 sections 2.1, 2.3 and 2.4](https://www.rfc-editor.org/rfc/rfc8439.html#section-2.1).
Its C reference is libsodium's
[`chacha20_ref.c`](https://github.com/jedisct1/libsodium/blob/3e9d341d065dde2becdb69a2a27ea75c10d17745/src/libsodium/crypto_stream/chacha20/ref/chacha20_ref.c),
which identifies the core as D. J. Bernstein's public-domain
`chacha-merged.c`, version 20080118. The downloaded file and the pinned commit
have SHA-256 `a93ebb4cc15c590798cb095d48ed39eb5d8929fda7904ce148908485e38914c3`.

| C operation | Bend translation |
|---|---|
| `QUARTERROUND` | `quarter`: wrapping U32 add, XOR, rotations 16/12/8/7 |
| Eight calls inside the 20-round loop | `double_round`, `diagonals`, `gather`; ten iterations of `rounds` |
| `chacha_keysetup`, `chacha_ietf_ivsetup` | `initial`: four constants, eight key words, one counter, three nonce words |
| Addition of original state and `STORE32_LE` | `feed`, `little`, exposed through `block` |
| XOR with message and counter advance | `crypt_go`, exposed through `crypt` and `keystream` |

`ChaKey` holds eight U32 words and `Nonce` three, decoded little-endian by the
caller. `block(key, counter, nonce)` returns 64 octets as `List<&2, U32>`.
`crypt(key, counter, nonce, msg)` returns `Some{bytes}` or `None{}` when the
message would need a block beyond counter `4294967295`. `keystream` encrypts
zero octets. All 64 bytes of the last counter are allowed; byte 65 is refused.
This deliberately follows the RFC's 32-bit counter boundary rather than the
shared C core's carry into word 13. Neither key nor nonce can have the wrong
word count. Input message elements use their low eight bits, like `uint8_t`.

The direct demo prints the complete section 2.3.2 block as lowercase hex.
This is the stream cipher only; there is no Poly1305 or AEAD implementation.

### SHA-256

[demos/kernels/sha256.bend](../../../demos/kernels/sha256.bend) follows
[FIPS 180-4 sections 4.1.2, 4.2.2, 5.1.1, 5.3.3 and 6.2](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf).
The C reference is
[RFC 6234 section 8.2.2, `sha224-256.c`](https://www.rfc-editor.org/rfc/rfc6234.html#section-8.2.2).
The RFC text downloaded for this translation has SHA-256
`8f39f02a57bfd1da15634706724a585766e6223f77ecdaf243cad16cd3a1aa1b`.

| C operation | Bend translation |
|---|---|
| SHA-256 functions and constants | `small0/1`, `big0/1`, `choose`, `majority`, `constants` |
| `SHA256Reset` | `initial` with the eight SHA-256 initial words |
| Loading `W[0..15]`, expanding `W[16..63]` | `load`, `words`, `expand`; schedule built newest-first then reversed |
| 64 rounds and intermediate-hash addition | `step`, `rounds`, `feed`, `compress` |
| `Length_High` / `Length_Low` | `carry` and two U32 words, incremented by eight bits per octet |
| `SHA224_256PadMessage` | `finish`, `pad`, `finish_blocks`, `big_endian` |

`hash(msg)` takes octets as `List<&2, U32>` and returns the 64-character
lowercase digest. It processes a reversed buffer of at most 64 octets,
appends `0x80`, zero padding and the full big-endian 64-bit bit count, and
handles one or two final blocks. Base in this checkout has no U64, so the
length uses the C reference's high/low pair. The count wraps modulo 2^64;
the supported FIPS domain is messages shorter than 2^64 bits.

`octets(s)` is a convenience for octet-valued characters, taking their low
eight bits; it is not a UTF-8 encoder. Binary input should use a byte list.
The direct demo hashes `abc`. The implementation accepts byte-aligned
messages, not the partial-final-byte `FinalBits` API of the C reference.

Both files import only Base. Every self-call passes the strict decreasing
recursion check; there are no holes, open goals, unsafe annotations, foreign
imports or new native operations. U32 arithmetic is the existing Base API.
This is checked code with vector evidence, not a proof of cryptographic
correctness or a claim about constant-time machine code.

## Fixtures

All expected outputs live in literal `#|` pins in the fixture files, with a
source comment naming the vector. They are not generated from the Bend
implementation during a run. String results include the printer's quotes.

| Fixture | Pin / property |
|---|---|
| `chacha_quarter` | RFC 8439 2.1.1, all four result words serialized little-endian |
| `chacha_block` | RFC 8439 2.3.2, all 64 serialized bytes |
| `chacha_encrypt` | RFC 8439 2.4.2, all 114 ciphertext bytes |
| `chacha_decrypt` | The same RFC ciphertext supplied as literal input; exact plaintext octets |
| `chacha_counter` | Both full post-addition block states in RFC 8439 2.4.2, serialized little-endian (128 bytes) |
| `chacha_counter2` | The second RFC block obtained directly from initial counter 2 |
| `chacha_65` | First 65 bytes of that same stream, crossing the block boundary |
| `chacha_zero` | RFC 8439 A.1, vector 1: zero key, nonce and counter |
| `chacha_empty` | Supplemental contract: empty input consumes no counter |
| `chacha_last` | Supplemental contract: final counter permits exactly 64 bytes |
| `chacha_exhausted` | Supplemental contract: a 65th byte refuses counter wrap |
| `sha_empty` | NIST CAVS SHA256ShortMsg, Len=0; the `Msg=00` placeholder is not a message byte |
| `sha_abc` | RFC 6234 8.5, SHA256 test 1 |
| `sha_448` | RFC 6234 8.5, SHA256 test 2, 56-byte `abcdbc...nopq` message |
| `sha_cavs_8` | NIST CAVS Len=8, binary octet `d3` |
| `sha_cavs_440`, `sha_cavs_448` | NIST CAVS 55/56-byte padding boundary |
| `sha_cavs_504`, `sha_cavs_512` | NIST CAVS 63/64-byte block boundary |
| `sha_carry`, `sha_length` | Supplemental contracts: low-word length carry and all eight big-endian length bytes |
| `slow/sha_million` | RFC 6234 8.5, SHA256 test 3: 1,000,000 actual `0x61` octets |

The NIST fixtures are copied from `shabytetestvectors/SHA256ShortMsg.rsp`
(CAVS 11.0, byte-oriented, generated 2011-03-15), in the official
[SHA byte test-vector archive](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/shs/shabytetestvectors.zip).
The downloaded ZIP has SHA-256
`929ef80b7b3418aca026643f6f248815913b60e01741a44bba9e118067f4c9b8`.
RFC 6234's SHA256 tests are the source of the `abc`, 448-bit and million-`a`
pins; FIPS 180-4 specifies the algorithm. Supplemental contracts are labeled
separately from official vectors.

## Battery and measured results

```sh
bash tests/kernels/run.sh
bash tests/kernels/run.sh --selftest
KERNELS_BUILD_TIMEOUT=30 bash tests/kernels/run.sh --million
```

The runner follows `tests/regex/run.sh` and `tests/run.sh`. The brief's
`tests/f64/run.sh` does not exist at this base commit; `tests/run.sh` is the
local f64 battery. Strict checking loads the fixture and its imports, calls
`book_valid`, and rejects `book.hols + book.open`. The interpreter is
`bun bend2/main.ts FILE`, JS is emitted with `-o test.js` and run with Bun,
and C is emitted with `-o test` and run with `--threads 1 --gpu off`.

The harness compares exact output and exit status. A missing pin, empty
fixture directory, timeout, build error or runtime error fails the suite.
Every failure names its fixture and lane and includes the actual output or
build diagnostic. Compiler errors in the strict lane are formatted through
`err_show`, avoiding a dump of the entire checker book. Temporary builds are
isolated with `mktemp` and removed on exit.

| Run | Strict check | Interpreter | Emitted JS | Emitted C | Total |
|---|---:|---:|---:|---:|---|
| Default, 21 fixtures | 21/21 | 21/21 | 21/21 | 21/21 | 84 pass / 0 fail |
| Optional million-`a` | pass | timeout, exit 124 | pass | pass | 3 pass / 1 fail |

`--selftest` passes: a wrong pin is detected independently by all three run
lanes while its strict check passes; a hole is rejected by strict checking;
an empty suite is rejected. `bash -n tests/kernels/run.sh` and
`git diff --cached --check` pass. Both standalone demos were also compiled
and executed with `--threads 1 --gpu off` and printed their `#|` pins.

Measured here: Linux `6.17.12-300.fc43.x86_64`, x86_64, Bun `1.3.4`,
GCC `15.2.1 20260123`. These are local CPU results, not mini-cluster or GPU
results. No performance comparison or release-readiness claim is made.

### Million-`a` deviation

The final optional fixture constructs all one million octets with a
structurally decreasing, tail-recursive producer and feeds the same `hash`
entry point as every short fixture. It does not precompute the digest or
replace message blocks with known intermediate states.

Exact expected output:

```text
"cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"
```

Final interpreter actual stdout/stderr: **empty**; status **124**, timed out
at **30 seconds**. JS and C produced exactly the expected output. The
optional run exits 1 and reports `Kernels PASS: 3, FAIL: 1`; it is never
counted as a four-lane pass. The default run identifies the separate optional
command. The slow fixture is below `slow/`, outside the cluster gate's usual
one-level test discovery.

An initial producer using Base's `List.replicate` failed in JS with
`RangeError: Maximum call stack size exceeded.` The fixture now uses the
tail-recursive producer so that input construction does not mask the kernel's
result. No Base or compiler fix was made. Default run-lane timeout is 300s;
`--million` uses 30s; build timeout is 120s. `KERNELS_TIMEOUT` and
`KERNELS_BUILD_TIMEOUT` override these budgets, and `KERNELS_DIR` selects an
isolated fixture directory for harness checks.

## Cap ledger and the scope conflict

All readings below are `ttok < FILE`, measured after implementation.

| Files | ttok | Existing cap |
|---|---:|---:|
| `demos/kernels/chacha20.bend` | 2,174 | 64,000 |
| `demos/kernels/sha256.bend` | 2,793 | 64,000 |
| Each ordinary `tests/kernels/*.bend` | 92–634 (largest: `chacha_decrypt.bend`) | 16,000 |
| `tests/kernels/run.sh` | 1,299 | no matching row |
| `tests/kernels/slow/sha_million.bend` | 204 | no matching row |
| `docs/omen/plans/kernels-c-brief.md` | 628 | 16,000 |
| This report | 3,428 | 16,000 |

The actual repo gate, with the new files staged, reports:

```text
FAIL tests/kernels/run.sh: not in the allow list
FAIL tests/kernels/slow/sha_million.bend: not in the allow list
PASS: 51 / 53
```

Despite the gate's final `PASS:` wording, it exits nonzero. These are the
only repo-gate failures. All existing rows and all matching new files fit.
The brief suggests a minimal new row if necessary, but the user's explicit
scope excludes `gates/repo.ts`. It is therefore unchanged. The exact one-row
integration change needed outside this lane is:

```ts
allow(/^tests\/kernels\/(run\.sh|slow\/sha_million\.bend)$/, 16000);
```

No cap increases are needed. This proposed row is documentation, not an
applied gate edit. The four-lane kernel battery and the repo-shape gate are
reported separately.

## Commits

| Slice | Commit | Content |
|---|---|---|
| Kernels | `a0b63905` | Pure Base translations and standalone demo pins |
| Tests | `fa580a5d` | Official fixtures, four lanes, harness controls, optional million-a probe |
| Report | this commit | Reference pins, measured lane results, caps, deviations and unchanged handoff |
