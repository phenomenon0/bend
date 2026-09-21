# regex-upstream lane: the regex slice, sized for upstream (opus 5, 2026-09-20)

Branch `regex-upstream` (worktree `bend-work-regex-up`), off upstream `main`
`75cb8f3e`, which is v2.0.23 plus two literal commits. It was pushed to
`our/regex-upstream` at `72d20d7f`. No PR is open: the title and body are in
`~/Documents/Project/bend-upstream-prep/regex-PR.md`.

| commit | content |
|---|---|
| `f5137b6b` Base compiles a regex and runs it on a Pike VM | `bend2/base.bend` +485 lines: 4 types in `# Data`, a `# Regex` section after `# Text` |
| `b6c8df9c` tests/regex: the slice against CPython 3.11 | 6 tests (the oracle's 160 rows are 369 lines) |
| `72d20d7f` tests/regex: laws see a later start overtake a known match | 1 laws row, found by the mutation pass below |

It is standalone. It does not depend on `pr/strings` or on any helper that
upstream lacks. `bend2/{comp,bend,main}.ts` and `gates/` are byte-identical
to `75cb8f3e`, and no cap moved. The total is +1,061 lines over 7 files.

## The slice

The semantic pin is CPython 3.11 `re` under `re.ASCII`.

- **Types:**
  - `Regex.Node` is the tree.
  - `Regex.Inst` is the VM's code: `ISet`, `ISplit`, `IJmp`, `ISave`, `IAsr`, `IMatch`.
  - `Regex` is the code plus the group count.
  - `Regex.Match` holds the span and the groups, each `Maybe` a span.
- **API:**
  - `Regex.compile(p) -> Result<String, Regex>`
  - `Regex.exec(re, s, at)` is `search(s, at)`.
  - `Regex.match_at(re, s, at)` is `match(s, at)`.
  - `Regex.fullmatch(re, s)` is `fullmatch(s)`.
  - `Regex.group(s, m, k) -> Maybe<String>`
- **Grammar:**
  - literals and `.`
  - sets with ranges and negation
  - `\d \w \s \D \W \S \b \B` and the control escapes
  - `^ $`, groups and `(?:`, `|`
  - `* + ?`, greedy or lazy
- **Semantics matched to CPython (each pinned by a row):**
  - `$` matches at the end or before a final `\n`.
  - `^` matches only at the real start, even when `at > 0`.
  - `\b`/`\B` read the real char before `at`.
  - An `at` past the end clamps to the end.
  - A group keeps its last value, and a group that took no part is `None`.
  - Offsets count code points.
- **VM:**
  - Threads stay in priority order, and a pc is visited once per step (a `seen` list).
  - A match cuts every thread below it.
  - A fresh start thread is added each step until a match is known.
  - Closure fuel is `3·(1+|code|)`.

### Naming

The types are `Regex.*` because a top-level `type Match` in Base collided
with `def Match` in `evals/hell.glob_backtrack_match.bend`: "duplicate
declaration: Match". Base names are global to every `import Base` file. The
constructor `Match{}` stays, because constructor names don't clash with defs.

## What was cut, and why each is a later step

Each cut is a compile error, never a silent mis-parse. parse.bend pins one
row per kind.

| cut | behaviour here | why it's later |
|---|---|---|
| flags `i m s` (`Regex.compile` takes no flags argument) | `(?i)`: "unsupported group extension" | Case folding changes the set representation. Flags are their own step. |
| counted repeats `{m}` `{m,}` `{m,n}` | "counted repeats are not supported". **Any** `{` outside a set fails, although CPython reads a lone `{` as a literal. | Needs the counted-repeat parser (telling `{` literal from `{2}`) and a node expansion in emit. |
| `\x \u \U \N \0`, octal, backrefs, `\A \Z` | "bad escape" | Backrefs are not regular, so the Pike VM can't run them. The rest is parser surface. |
| group extensions: named groups, lookarounds, atomic groups, inline flags | "unsupported group extension" | Lookarounds need sub-VM runs. Named groups need a name table in `Regex`. |
| possessive `*+ ++ ?+` (3.11 accepts them) | "multiple repeat" | Needs atomic semantics in the VM. |
| `*`/`+` on a body that can match empty, e.g. `(a*)*`, `(?:)+` (CPython accepts) | "repeat of a pattern that can match empty" | Needs an empty-iteration check in the VM. |
| the offending text in CPython's error messages | Ours is the message without it (`bad escape` vs `bad escape \q`). One kind differs: `[z-a` gives "unterminated character set" here, "bad character range z-a" in CPython. | Both sides fail. Error payloads are a later step. |
| `finditer`/`findall`, `split`, `sub`, a step budget | not present | The derived API, each its own step. |
| `endpos` | not present | small, and later |
| Unicode `\w \d \s \b` (CPython's default without `re.ASCII`) | ASCII classes only | The slice pins `re.ASCII`. Unicode tables won't fit in base's 551 ttok. |
| a native VM in the runtime | the VM is pure Base | `comp.ts` is at 64,936 / 65,000 ttok, so a native row needs a cap decision. That is upstream's call, not this PR's. |

## Measured

Every number comes from a command run this session, on x86_64 Linux
(Fedora 43) with an RTX 3090 and CUDA 13.1, using CPython 3.11.14.

**Caps** (`bun gates/repo.ts`: PASS 46 / 46 at each commit; the 46 counts allow rules):

| file | ttok | cap | headroom |
|---|---|---|---|
| `bend2/base.bend` | 31,449 (was 25,423) | 32,000 | **551** |
| `tests/regex/oracle.bend` | 5,707 | 16,000 | 10,293 |
| `tests/regex/laws.bend` | 1,173 | 16,000 | 14,827 |
| `tests/regex/captures.bend` | 866 | 16,000 | 15,134 |
| `tests/regex/exec.bend` | 758 | 16,000 | 15,242 |
| `tests/regex/parse.bend` | 703 | 16,000 | 15,297 |
| `tests/regex/smoke.bend` | 582 | 16,000 | 15,418 |

The slice spends 6,026 of the 6,577 ttok that base had free, 624 of them on
comments.

**Tests:** `tests/regex` 6 / 6, each passing its check, interp, C and JS runs
against its `#|` lines. This used `~/.cache/regex-up/lanes.sh`, a local copy
of `gates/test.ts`'s procedure: `--checkup`, a build to C and JS, and each
binary under the 5 s alarm, with a `!` test run once first. The times are
from one run and move by a few ms between runs.

| test | rows | C | JS |
|---|---|---|---|
| parse | 24 compiles: 6 codes, 9 shared errors, 9 cuts | 0.003 s | 0.016 s |
| exec | 20 (search, match_at, fullmatch) | 0.003 s | 0.018 s |
| captures | 10 matches, 8 group texts | 0.007 s | 0.021 s |
| laws | 15 × 3 laws | 0.003 s | 0.024 s |
| oracle | 160 (seed 7) | 0.004 s | 0.035 s |
| smoke | 7 subjects × 2 across one `!` | 0.178 s | 0.021 s |

- **The hand pins are CPython's.** A script extracts the rows from the
  test's source, runs them through `re` under `re.ASCII` in the same print
  format, and compares the result to the `#|` line. It gives equal output for
  exec (20 rows), captures (10 + 8) and smoke (7 × 2).
  - One nuance: `Regex.group` past the group count is `None`, where CPython
    raises `IndexError: no such group`. captures pins one such row.
- **Laws can fail (mutation, on a scratch copy of base):**

  | mutant | killed by |
  |---|---|
  | `match_at` unanchored | law 2 |
  | `fullmatch` without its end assertion | law 3 |
  | the fresh start ranked above older threads | law 1 |
  | fresh starts kept after a match is known | law 1, since `72d20d7f` |

  The fourth mutant first survived the laws, and I wrongly guessed it was
  equivalent. It is not: on `abcd|a` against `"abab"` it returns 2-3, while
  CPython and the slice return 0-1. The oracle killed it. The laws needed that
  row, and `72d20d7f` adds it. Now 4 / 4 are killed, and the unmutated base
  passes.
- **`!` smoke on the GPU:**
  - The build took the CUDA lane (nvrtc present), and gdb shows
    `cuLaunchKernel` called from `cube_run`.
  - Output equals the pin with `--gpu on` (244 ms) and `--gpu off` (9 ms).
  - **Metal is not verified**, though it's the gate's lane on the minis.

**Differential against CPython 3.11** (generator:
`docs/omen/lanes/regex-upstream-oracle.py`, kept here because the allow list
forbids `.py` in `tests/`; `python3.11 regex-upstream-oracle.py --rows 160
--seed 7` writes the in-repo file):

- In-repo 160 rows (seed 7, 22 err rows): **0 diffs** on interp, C and JS.
- Offline 5 seeds × 1,000 rows, rebuilt against the committed base: **0
  diffs** on C and JS for every seed, and 0 on interp for seed 1 (3.2 s).
- Err rows per seed: 101, 81, 91, 97, 93.
- Coverage over the 5,000 rows:

  | measure | count |
  |---|---|
  | compiled | 4,537 |
  | search hits | 3,011 |
  | hits with groups | 1,038 |
  | rows with an unset group | 817 |
  | fullmatch hits | 527 |

**No regression elsewhere:**
- `--checkup` (check and interp) over all 1,412 upstream tests in 8 shards:
  output byte-identical between HEAD's base and this base.
- C and JS emitted for all 1,413 tracked tests, of which 623 build: all
  byte-identical except `tests/base/list_fold`. There, `List.contains`'s
  specialization `_0` becomes `_1`, because `Regex.close` takes the first.
  That is a rename only.
- `--check-only` over the 70 demo and eval files: byte-identical after the
  rename. This check is what caught the `Match` collision.

**Linear run** (C binary, 3 runs each, medians):
- Patterns: `(a|b)*c` on `"ab"×n` and `^(a+)+$` on `"a"×n + "b"`, both failing,
  in one binary.
- n = 2,000 / 4,000 / 8,000 / 16,000 gives 12 / 20 / 43 / 85 ms.

**Not run:**
- `gates/test.ts` on the cluster: host `cluster` doesn't resolve from here, and
  the gates can't be edited. The local emulation above stands in for it.
- ASan: the runtime is untouched (`comp.ts` byte-identical).
- `gates/perf.ts`: no bench was added.

## Residuals

- **Base is nearly full.** 551 ttok are left under the 32,000 cap. The next
  Base addition upstream will need a trim or a cap decision.
- **Metal.** The `!` smoke ran on CUDA and the cores, not on an M4's Metal
  lane. The first cluster gate run is where that gets measured.
- **Speed.** It is a list-based VM in Base. `seen` membership is `O(|code|)`,
  so a step is `O(|code|²)`. That is fine for a slice and slow for a hot path.
  The native row is the fix, gated on comp.ts's cap.
- **Size.** +1,061 lines over 7 files, against #931's +525 / −9 over 5. The
  core (base) is +485, and 369 of the tests' lines are oracle data.
- **Error text.** Ours is CPython's message without the offending text, and
  one error kind differs (see the cuts table).
- **The cuts refuse.** Each is a compile error, never a wrong match. The
  refusal a user will hit most is the lone `{`.
- **Three commits.** The laws fix is its own commit, rather than a force-push
  over the pushed `b6c8df9c`. Squash it into that commit if upstream wants
  two.
