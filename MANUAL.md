# MANUAL — working on bend2 the way bendlang/bend does

How Victor Taelin tests, reviews, and refactors his compiler — distilled from the
public repo (`github.com/bendlang/bend`, cloned 2026-09-17, main == the 2.0.4 we
forked: every tracked file byte-identical to our `82cb989` baseline) and from his
public writing. This manual is the standard the F64 fork's final polish pass is
held to.

Sources studied: `AGENTS.md`, `gates/{repo,test,perf,ping,_lib,_run}.ts`,
`gen_pins.ts` + the bench pins, all 24 test namespaces (1,302 tests), the
compiler sources themselves, `README.md`, and his LessWrong note on Gemini 3.
The repo publishes **squashed release commits** (one commit, "Bend 2.0.4"), so
the craft is visible in the artifact's shape, not in a diff history.

## 1. Repo shape — the allow list and the ttok caps

`gates/repo.ts`: *every tracked file must match one allow line*, and every
**text file stays under a ttok token cap** (binaries under a byte cap). Anything
else in the tree is a gate failure. `evals/` is exempt — "the models' arena,
not the repo's shape".

The caps are hand-maintained ceilings that ride just above the file
(base.bend 23,890 → cap 24,000; comp.ts 60,588 → 61,000; bend.ts 40,050 →
41,000 — measured, 2026-09-17). A feature that legitimately grows a file raises
its cap in the same edit, to the next round number; a refactor pass re-tightens.

**Consequences, taken seriously:**
- Source size is a CI-enforced quantity. "Make it smaller" is not taste, it is
  policy — and it is why the code reads the way it does.
- Nothing enters the tree that the allow list does not name. New files get a
  matching `allow(...)` line with a chosen cap, or they fail.

**Our fork's ledger (F64 v0.1, ttok):**

| file | baseline | patched | delta | upstream cap | fits? |
|---|---|---|---|---|---|
| bend2/base.bend | 23,890 | 24,968 | +1,078 | 24,000 | no → bump 25,000 |
| bend2/comp.ts | 60,588 | 62,244 | +1,656 | 61,000 | no → bump 63,000 |
| bend2/bend.ts | 40,050 | 40,368 | +318 | 41,000 | yes |

The cap bumps are the honest, conventional move: F64 is ~3k tokens of new
language surface, and it is syntax, laws, ops and runtimes — not redundancy.
`tests/caps.sh` re-checks this ledger.

## 2. Testing doctrine

**Every test is a Bend file that ends in the `#|` lines its run must print.**

```bend
# wrap-around arithmetic chains: xorshift32, a modular-inverse round trip, ...
# ported from bend3: shift counts become Nat (U32.shln/shrn), ...
import Base

law xorshift:
  for +x: U32
  U32

def xorshift(x):
  +a = {U32.xor(x, U32.shln(x, 13n)) : U32}
  ...

law main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))

#|4
```

Every rule of the form, observed across the 1,302 tests:

- **`law` then `def` pairs.** The law declares the type; the def body is
  checked against it. `main` gets `law main:` too.
- **The `#|` block is the exact bytes** each run must print — whole lines,
  `exit 1` included. Negative tests pin the compiler's **error text verbatim**
  (see `tests/run/array_bounds_000.bend`: `#|Error:` … `#|exit 1`).
- **Four lanes.** `gates/test.ts`: a test passes when its check, its
  *interpreted* run (`bend --checkup`), its *JS* run (bun) and its *C* run
  (clang -O3, Metal) all print the `#|` lines. Lane drops are explicit: no
  external/IO use → lanes; a foreign def with no twin for a lane drops that
  lane; the compiler refusing to print a `main` (a function, a Type, an erased
  or dependent field) downgrades to check+interpret only.
- **First `!` run is untimed** (a fresh binary compiles its GPU shader, the
  node caches it by source); timed runs are 5 s alarm per lane.
- **Sharded one-per-mini** across the cluster; aggregators import their tests.
- **Provenance lives in the header comment** ("ported from bend3:", "bend3's X
  becomes a local LE"). Tests document where they came from and what changed.
- **Namespaces** (`tests/<ns>/`) are the taxonomy: `run` (execution),
  `reg` (regressions), `spec` (checker semantics), `proof` (proof checking),
  `state` (type-state eval), `show`/`printer`/`parse` (text I/O),
  `io`/`import`/`halt`/`page` (platforms), `stuck` (stuck terms), `stats`/`cost`
  (measurement), `grade` (graded behaviors), `gfx`, `flatten`, `base`, `check`,
  `compile`, `comptime`, `eval`, `rfc`. Variants are numbered
  (`array_bounds_000`, `_001`).
- **Cap: 16,000 ttok per test.** Tests are specimens, not suites.

## 3. Review doctrine

- **`bend2/bend.ts` is human-written: agents must not edit it.** The language
  (parser, theory, checker) is Taelin's own hand. `comp.ts`, `base.bend`,
  tests, demos are agent-editable — under the caps and the gates. (Checkers are
  not a place where delegation is allowed; the rest of the system is built for
  delegation.)
- **The gates are the reviewer.** There is no CONTRIBUTING, no PR template, no
  CI config: review = `gates/repo.ts` (shape) + `gates/test.ts` (behavior, four
  lanes) + `gates/perf.ts` (numbers vs pins, "medians of three runs", timed
  cells alone on a quiet machine) + `gates/ping.ts` (the delivery path). Four
  verdicts, run "with --gate" on the mini cluster.
- **Numbers are produced by the same run that writes them down.** `gen_pins.ts`
  "writes nothing it did not measure in the same run"; unmeasurable columns are
  carried forward `--keep` and "the stamp says so". No hand-typed benchmarks,
  ever.
- **His AI-review method** (LessWrong, Gemini 3 notes): give the model the hard
  file to rewrite with a few core changes, *then inspect the trickiest
  functions*. Models are graded on "refactoring files without logical
  mistakes" and on novel hard problems (the λ-calculus vibe tests); the winner
  is the one whose output survives inspection, not the one whose diff is
  prettier. Apply the same posture here: an agent's self-report is not a
  review; the gate run is.

## 4. Refactoring doctrine — the moves

Distilled from the sources; each is visible in the code with many witnesses.

1. **Sections with banner comments.** `// Operations` `// ----------`,
   `// Types` `// =====`, `// Caches` — every region of every file opens with
   a name and a rule of `=`/`-`. A file is a table of contents.
2. **Table-driven over branching.** `OPERATIONS`, `OPTIMIZED`, `WORDS`, the
   `tpl_ops`/`tpl`/`tpl_nat` template functions: data describing behavior,
   code doing one thing. Adding a type = adding rows. (Our F64 work is
   exactly "add the mirrored rows" — that is the designed extension path.)
3. **Per-type mirrors over premature generalization.** `u32_*`, `f32_*`,
   `nat_*` are complete, parallel mirrors; `f32_text`/`f64_text` are written as
   one another's twins rather than forced through a shared abstraction. The
   duplication is *structural* — it keeps each lane independently auditable —
   and the caps are set per file so this stays affordable. Do not "DRY" a
   mirror unless the gate demands it.
4. **Comments state the invariant or the why**, lowercase, sentence-fragment:
   "the last wins", "a point before an e", "a Nat past the largest immediate",
   "one idea per bench: main.bend and its twins". Never restate the code.
5. **Symmetry as style.** Tables align `C:`/`JS:`/`call:` columns; wrappers
   (`hah`) and judges fail on asymmetry. When you add a row, align it.
6. **Zero dead weight.** The allow list admits nothing; `evals/` is outside
   the shape; every tracked byte is load-bearing or capped out.
7. **The cap is the refactor.** Compression has a number: a file is "done"
   when it fits its cap and every gate's verdict is green. Refactoring is not
   a phase, it is the standing price of the caps.
8. **Error text is API.** Tests pin exact messages and `exit 1`; changing an
   error without updating its tests is a gate failure. (Same discipline as
   docconform: the documentation of failure is executable.)
9. **The module graph is the architecture.** AGENTS.md lists what each path
   *is*; if a file's definition stops being true, the AGENTS.md line is part
   of the change. Docs and shape move together.

## 5. The F64 polish checklist (this fork)

- [x] Lands as mirrored rows/blocks (base laws, ops tables, runtimes, natives)
- [x] Grammar comment for the new literal form in `bend.ts` (`// F64 | ...`)
- [ ] `tests/f64/` in the `#|` convention (law/def pairs, provenance headers)
- [ ] One local reduction of the four-lane gate: `tests/run.sh`
- [ ] `tests/caps.sh` — the ttok ledger vs upstream caps
- [ ] Cap-bump notes for upstream landing (25,000 / 63,000)
- [x] Quirks documented (C-lane `read` parity; `F64.bits` Nat cap caveat)
- [ ] `bend-lang` skill updated with the fork + repo facts

## 6. Running things in this fork

```
bun bend2/main.ts t.bend                 # check + interpret (lane 1-2)
bun bend2/main.ts t.bend -o /tmp/t.js    # js build;  bun /tmp/t.js   (lane 3)
bun bend2/main.ts t.bend -o /tmp/t       # native;     /tmp/t         (lane 4)
bash tests/run.sh                        # all four lanes over tests/f64/
bash tests/caps.sh                       # the ttok ledger
```

## 7. Known quirks (documented, not hidden)

- `F64.bits` returns `Nat`; bit patterns above `NAT_IMM` (2^48-1) are checked
  by `nat_chk` at runtime if fed to Nat ops. Normal magnitudes (exponent < 2^11)
  never trip it; extreme exponents / NaN payloads can, by design (same class of
  caveat as any Nat-immediate boundary).
- C-lane `F64.read` shares `strtod`'s behavior with F32: it accepts C99 hex
  floats and truncates at an embedded NUL. Verified F32-identical; the JS lane
  rejects both. Pinned in `tests/codex/expected.py` as parity quirks.
- Metal has **no fp64 at all** (Apple GPUs lack double precision): F64 is a
  host + CUDA type by construction — the Metal typedef block carries no
  `double`, and the f64 helpers are `#ifndef __METAL_VERSION__`-guarded, so a
  program that never uses F64 compiles for Metal exactly as before (found in
  the fable review pass, fixed same day; no Metal hardware here to re-verify).
