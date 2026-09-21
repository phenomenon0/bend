# C kernels → Bend (brief for a Codex lane, 2026-09-20)

Worktree `bend-work-kernels`, branch `lane-kernels-c`, off `omen` @ `ac994157`.

## Mission

Translate two famous, test-vector-pinned C kernels into **pure Bend** (no native ops; no changes to `bend2/**`), each with a four-lane test battery:

1. **`demos/kernels/chacha20.bend`** — RFC 8439 ChaCha20: the block function, and keystream/encryption over a message. Vectors: RFC 8439 §2.3.2 block test, the §2.4.2 encryption example; a counter-stepping check.
2. **`demos/kernels/sha256.bend`** — FIPS 180-4 SHA-256. Vectors: `""`, `"abc"`, the 448-bit two-block message, and (if the runtime tolerates it) the 1,000,000-`a` vector.

Pure `Base` only (U32/U64 arithmetic, List, String — read `demos/text/*.bend` for the house way of writing pure helpers). No imports beyond Base; **no edits outside `demos/kernels/`, `tests/kernels/`, `docs/omen/`**.

## How to build and run Bend here

```
bun bend2/main.ts demos/kernels/chacha20.bend -o /tmp/kc20 && /tmp/kc20 --threads 1 --gpu off
```

Read `tests/f64/run.sh` and `tests/regex/run.sh` first: they show the four-lane discipline (strict check / interpreter / emitted JS / emitted C) and how a suite is wired. Your `tests/kernels/run.sh` should follow that shape, with the vectors as fixtures; a failing vector must print which vector and which lane.

## Deliverables

- The two kernels + `tests/kernels/run.sh` (four lanes; vectors as fixtures).
- `docs/omen/lanes/kernels-c.md` report: what each kernel covers, vectors used, lane results, and cap readings. New files should fit the existing `gates/repo.ts` rows (`demos/<name>/<File>.bend`, `tests/<dir>/...`); if one new row is truly needed, add it minimal and itemized and name it in the report.
- Commits in the repo's lane style (see `git log --oneline -20`).
- **Do not push.** Do not touch anything else in the tree.

## Rules

- If a vector cannot pass, do **not** weaken it: record it as a deviation with the exact lane and the actual value.
- Pure and total where possible; 2-space indent; house comment voice.
- Keep the kernels honest to their references — name the reference and the exact section in a comment at the top of each file.
