# PLAN — regex · parser · lint · translator (synthesized, 2026-09-18)

Status: **locked for build.** Synthesis of the fable×astra deliberation (phase 1 drafts →
phase 2 critiques + v2s, `plan-{fable,astra}-v2.md` both read in full). The arbitration calls
below are final for v1; everything marked [Q→CALL] is my decision with rationale. Doctrine:
writes nothing it did not measure; four lanes byte-identical; semantics-first slices; caps move
by measurement, never by negotiation.

## 0. Ground truth (measured this deliberation)

- Caps [M]: base 27,844/28,000 · comp 75,152/76,000 · bend.ts 40,399/41,000 · main 5,353/10,000.
  Regex lands with cap bumps in the same edit; **`bend.ts` untouched** (no literal syntax).
- No mutual recursion; structural descent; `match` on parameters/binders only [GUIDE].
- Strings are code-point addressed in every lane; JS positional helpers scan prefixes — never
  index JS strings in a loop.
- Sibling `import` inside `demos/` is real [M, `demos/app_pong_game_2d/LAWS.bend`]; demo `.bend`
  cap 64k, test `.bend` cap 16k [M, `gates/repo.ts`]. Parser/lint/translator are **programs in
  `demos/python/`**; only regex touches the core.
- Oracle pins: **CPython 3.11** (`python3.11`; exact executable + library hashes recorded at P0),
  `ast.parse(..., feature_version=(3,11), type_comments=False)`; oracle bound: nesting > 200
  rejected, chained-unary/binoop RecursionError — those are oracle-failures, not parser verdicts.
- Corpus [M]: 15,090 `.py` under `~/Documents` (venvs excluded) + 168 stdlib top-level; manifest
  with per-file sha256 + exclusion reasons; ladder llm-wiki/tools → Project → stdlib.

## 1. REGEX — first-class, in `bend2/base.bend` (`# Regex` after `# String`)

### 1.1 Semantics — one pinning story
- **v1 = CPython 3.11 `re` under `re.ASCII`, restricted to the v1 syntax, minus unbounded
  nullable-body repeats.** Every pinned rule oracle-verified: leftmost-first priority; repeated
  groups retain the last participating capture (`(a(b)?)+` on `aba` ⇒ group 2 `b` [M]); `$` also
  matches before a final `\n`; `.` excludes only `\n`; `m` splits on `\n` only; empty-match
  iteration per Python 3.7+ (same-position retry: after an empty match at `p`, retry non-empty at
  `p` with empty acceptance suppressed, advance only if that fails — [M] `|a` on `a` ⇒ spans
  (0,0),(0,1),(1,1)); `split` keeps empties, cuts at every match position.
- **ECMAScript-divergence table is documented, not blurred** (capture reset, `$`/final-LF, line
  terminators, split empties). bun is an optional priority-only cross-check (R4b), never an
  authority. Divergences are v2 material with their own pinning; never partial/accidental.
- Syntax v1: literals; `.`; classes `[..]`/`[^..]` with explicit ranges (reversed ⇒ `RErr`);
  ASCII `\d\w\s` + negations; escapes `\n\r\t\f\v\0\xHH\uXXXX\UHHHHHHHH` (scalar-checked) +
  escaped metachars; groups `( )` `(?: )`; `|`; quantifiers `? * + {m} {m,} {m,n}` + lazy `?`;
  anchors `^ $`; `\b \B` (ASCII). Flags `i` (ASCII fold) `m` `s` — duplicate/unknown ⇒ error.
- **Rejected with pinned `RErr` texts:** backrefs (non-regular — permanent), lookaround,
  `\p{}`, named groups, `{,n}`, unknown escapes, and **unbounded nullable-body quantification**
  (`(?:a?)*`, `(a*)*`) [Q→CALL: reject; visited-set termination ≠ correct captures — verified by
  astra]. **Allowed: finite nullable via bounded acyclic expansion** (`(?:a?){0,2}`, `a*?`) — the
  grammar-derived bound makes it safe; distinct error code `NullableRepeat` for the rejected case.
- Constants: `max_rep = 256`, `max_prog = 4096` insts; exceed ⇒ `RErr`. Offsets = **code-point
  indices**; captures feed `String.slice` (O(1) on C).
- **Complexity, stated honestly:** one `exec` is O(n·m); global iteration is O(n·m) per match,
  worst O(n²·m) on `a.*b|a`-class patterns — never exponential, same class as RE2/Go/Rust. The
  rescan constant is pinned by `bench.bend --case rescan`.

### 1.2 Data shapes (base.bend)
```
type Re is Data:   RLit{c} RAny{} RSet{neg, rs: List<Char & Char>} RCat{a,b} RAlt{a,b}
  RRep{r, lo: Nat, hi: Maybe<Nat>, greedy: Bool} RCap{n, r} RBol{} REol{} RWordB{neg} REmpty{}
type Inst is Data: IChr{c: U32} IAny{} ISet{neg, rs} ISplit{x,y} IJmp{x} ISave{slot}
  IBol{} IEol{} IWordB{neg} IMatch{}
type Regex is Data:  Regex{prog: List<Inst>, ngroups: Nat}
type Match is Data:  Match{start: Nat, end: Nat, groups: List<Maybe<Nat & Nat>>}
type Regex.Error is Data:  RErr{pos: Nat, msg: String}
```
[Q→CALL] **`Match` does not retain its source** (fable) — `group(s, m, k) = String.slice(s, ...)`
takes the string explicitly; fewer retained references under the affine discipline. Absent capture
≠ empty capture (both `Maybe<Span>`). Flags fold into the program at compile. Out-of-range
jump/slot in a forged `Regex` = **dead thread in the reference VM** (`List.get → Maybe`); natives
do one cheap bounds pass on entry — forged values can never crash a lane, no `InvalidProgram`
surface type.

### 1.3 Functions
- All total, in base: `Regex.parse` (precedence climbing, `fuel = String.length(p)`, single def
  with a level `Nat`), `Regex.nullable`, `Regex.emit`, `Regex.compile(p, flags) ->
  Result<Regex.Error, Regex>`, `Regex.exec(re, s, at) -> Maybe<Match>` (first match at/after `at`),
  `Regex.match_at` (anchored — the lexer's entry), `Regex.fullmatch` (absolute `IEol` guard).
  Derived in Bend over `exec`: `is_match find find_all split replace(re, s, by)` (literal `by`).
  Only `compile / exec / match_at` go native — that bounds comp.ts.
- **Globals = budgeted [Q→CALL, astra's design adopted]:** one budget covers all searches, retries,
  capture copies, class probes and output — never reset per result, no partial success (budget
  exhaustion = explicit `Result` error). Driver follows Python finditer order including the
  same-position retry (1.1). `split` = unmatched gaps only (empties preserved, separators
  omitted); `find_all` returns `Match` records (unlike Python `findall` — documented). Oracle
  reconstructs gaps from `finditer` spans; replacement via `re.sub(p, lambda _: literal, s)`.
  Laws (R3): `is_match ⇔ is_some(find)`; `join(split(re,s),"") = replace(re,s,"")`;
  `replace(re,s,"") = join(split(re,s),"")`; group-0 = source slice; `match_at ⇒ start = at`;
  `find_all` starts strictly increase or empty-then-advance per the retry rule;
  `fullmatch ⇒ end = length`.
- Reference VM: `Regex.exec.step(prog, clist, c)`, `Thread = Nat & List<Maybe<Nat>>`; ε-closure
  with `fuel = length(prog)` + visited list; outer loop structurally recurses on the string.
  Slow on every lane — it is the oracle's twin, not a fast path.
- comp.ts rows `regex_compile / regex_exec / regex_match_at`: C program packed as u64
  (`op:8|a:24|b:24`), sets in a side block; two thread banks + slot block + generation-stamped
  visited; `err_spun` polling like KMP; same source compiles for CUDA. JS: **the same VM** over
  `Int32Array`, iterating by `codePointAt`; `at` costs one prefix scan (documented). **No host
  `RegExp` anywhere.**
- GPU v1 [Q→CALL, reconciled]: `exec!` over a `List<String>` of independent subjects (specimen in
  the `tests/strings/gpu.bend` shape), ordered results, task-local scratch. **Chunked single-string
  matching = tier-2 research only** — astra's counterexamples (`[^x]*`, `\s+`, chunk-local `^`)
  defeat naive LF-chunking; no "measured overlap" shortcuts. Device evidence + scratch measured
  before any speed claim.

### 1.4 Slices
- **R0** `tests/regex/run.sh` (strings clone) + allow lines + caps rows + **self-test: a
  deliberately wrong `#|` fixture must be detected as failing.**
- **R1** types + parser + nullable + errors. Accept: `parse.bend` pins 14 `Re` dumps;
  `errors.bend` pins 9 `RErr` texts (incl. `NullableRepeat`, `{,n}`, reversed range).
- **R2** compile + reference VM + fullmatch. Accept: `exec.bend` (`a|ab`; `^(a+)+$` on `aaab` →
  None; `(a|b)*?c`; `a$` on `a\n`), `captures.bend` (`(a(b)?)+` on `aba` ⇒ `Some(b)`; unmatched ⇒
  None; supplementary chars), `flags.bend`, `wordb.bend`. **Measure base ttok.**
- **R3** derived API + budgeted globals + laws (1.3). Accept: `laws.bend` green; rescan-case
  budget behavior pinned.
- **R4** `tests/regex/oracle.py`: 5,000 generated (pattern, text ≤ 64 cp) pairs vs CPython
  `re.ASCII` — search/fullmatch/findall/split/sub, span + all groups, generator excludes nullable
  bodies. Accept: **0 diffs on C + JS**; 500-pair interpret sample. **R4b** (optional): 1,000-pair
  bun priority-only cross-check.
- **R5** natives C + JS + rows; `tests/regex/runtime.py` (ASan/UBSan, allocation counters,
  reference/native parity); `bench.bend` (1 MiB, 4 patterns, medians of 7; doubling at fixed m;
  `--case rescan` constant). **Measure comp ttok.**
- **R6** caps → next round thousand on measurement; AGENTS.md line.

### 1.5 Size
| file | today [M] | +regex [E, fable/astra range] | plan |
|---|---|---|---|
| base.bend | 27,844 | +4,000 … +9,000 | **cap set at R2 measurement** (next round thousand; expect ~32–36k). If R2 measures > +5k, reopen fable's Q7 (separate `Regex.bend` module) *before* R3 — the feature does not shrink, the layout may change. |
| comp.ts | 75,152 | +4,000 … +7,000 | cap set at R5 (expect ~80–83k). |
| bend.ts | 40,399 | **+0, prohibited** | no literal syntax. |

## 2. PARSER — Python subset, `demos/python/`

- Files: `syntax.bend` (Pos/Tok/Expr/Stmt/Module/Py.Error + canonical JSON encoder), `lexer.bend`,
  `parser.bend`, `main.bend` (IO: strict `File.read` → lex → parse → print JSON or
  `error <kind> <line> <col> <msg>`, exit 1; multi-MB read verified at P0).
- `Py.Error = PErr{kind: Syntax | Unsupported | Limit, pos, msg}` — the harness classifies by
  kind; `Unsupported` is never a mismatch; `Limit` at `max_nest = 200` mirrors the oracle's own
  bound. Every `Name/Attribute/Subscript/Tuple/List/Starred` carries `ctx: Load | Store | Del`.
- **Parser shape [Q→CALL]: one `Py.parse.go(fuel, mode, toks)` with precedence climbing, direct
  recursion** (no frames in v1). Fuel `K × (length(toks) + 1)`, K = mode count (~10), **derived
  at P2 and asserted by fuzz: no `Limit` on any oracle-accepted input**. Escalation trigger: if
  any lane fails `deep_nesting` below the oracle's own limit (200), switch to explicit
  ParseTask/Frame continuations (astra's design, held in reserve — not built speculatively).
- Lexer v1 hand-written (INDENT/DEDENT stack, tab stops 8, bracket NL suppression, `\` continuation,
  CRLF/form-feed fixtures; string prefixes/triple quotes + numbers as raw text — no `F64.read`).
  Lexer v2 (P3, needs R3): NAME/NUMBER via compiled `Regex.match_at`, kept only if measured ≥ hand
  lexer on the corpus. Strict UTF-8/UTF-8-BOM intake; coding cookies/invalid bytes excluded by the
  wrapper before decode. Error recovery v1: first error; v2 (P7) recover to next `TNl` at the
  enclosing indent, must consume a token or exhaust fuel.
- **Canonical JSON [Q→CALL, merged]:** node tag, fields in CPython order, `ctx`, operators as
  tags, list order preserved; trivia/incidental parens omitted. **Constants value-normalized
  `repr(literal_eval(raw))` on both sides** (handles implicit concatenation, incl. comments
  between parts) — spelling differences are already caught at the lexer layer (`lexdiff.py` vs
  `tokenize`, 0 kind/text diffs), and locations are compared in a **separate pass** (CPython byte
  cols → code points via per-line UTF-8 boundary maps; separate diff counter). No sampling away
  of spans.
- `diff.py`: C binary per file (JS on 5% sample), `ast.parse` (3.11) → structural diff + location
  diff → `harness/RESULTS.md` (written by the run): `total · eligible · supported · parsed ·
  exact · unsupported · limit · error · oracle-failure · p50/p95 ms`, full denominators, manifest
  `corpus.jsonl` (path, sha256, size, exclusion reason). Adversarial set (checked in, pure,
  embedded inputs): nesting 200/201, 5,000 unary, 100k binops, 10 MB line, mixed tabs, NUL,
  invalid UTF-8 (lossy → must not crash), unterminated triple quote, dedent to no level, token
  soup — accept `Done`/`Fail` within bound on all lanes, **no fail-stops**.
- Slices: **P0** skeleton+harness self-tests; **P1** lexer (+`lexdiff.py` 200 files, 0 diffs);
  **P2** expressions + simple statements (+`deep_nesting` + fuel fuzz; llm-wiki 0 diffs);
  **P3** regex lexer (measured); **P4** functions/`for`/`lambda`/`global`/`del`/`assert`/`raise`/
  `try`/`with`/decorators (Project ≥ 60% fully parsed [E], 0 diffs); **P5** classes/imports/
  comprehensions/f-strings-as-text/walrus/slices (stdlib ≥ 40% [E], 0 diffs); **P6** `match`;
  **P7** recovery. Size [E]: 10–14k ttok P1–P5 under the 64k demo cap.

## 3. LINT-AS-PROOFS — `demos/python/lint.bend`

- `Diag{rule, pos, grade: Proven | Refuted | Unknown | Advisory, msg}`; `Lint.run(Module) ->
  List<Diag>` sorted by `(line, col, rule)`, byte-identical across lanes (pure Bend). Every rule
  ships fixtures (ok/bad/unknown) + a SOUNDNESS.md row (fragment · guarantee · NOT guaranteed).
- **[Q→CALL, staged — astra's small-verifier with fable's scope]:** certificates + an independent
  `Lint.verify` for **T (totality)** now and **X (module closure)** later; syntactic rules ship
  fixtures + properties only. A certificate is forgeable data — the verifier recomputes fragment
  membership, resolution and witness conditions against the actual AST; **forged-certificate
  fixtures must be rejected**. A `law` signature is never counted as a theorem.
  - **T** (Proven on fragment): closed pure functions on exact finite built-ins, acyclic resolved
    calls, `for` over parameters/literals/`range`, verified primitive contracts; no `while`,
    `yield/await`, self-call, attribute/subscript call. Otherwise `Unknown` — never "not total".
    Guarantee: terminates (not: returns without exception).
  - **A** (Advisory always for Python; Proven only inside the translator's ownership IR): fresh
    container aliased and mutated. Never "consumed twice".
  - **U** (Proven): statement after unconditional transfer.
  - **X** (Proven on a closed manifest, after P5): unused import; use-before-assign in
    straight-line module code; missing/cyclic → `Unknown`.
  - **M** (Proven on finite closed domains, after P6): coverage + duplicate unguarded constants;
    `True`/`1` overlap handled explicitly; guarded/class patterns `Unknown`.
- Order: T, A, U after P4; X after P5; M after P6. Size [E] 4–6k.

## 4. TRANSLATOR — `demos/python/translate.bend`

- Py AST → `IR` (`Fn`, `Let/Branch/Fold/Call/Return`, `Ty = TStr | TNat | TBool | TList | TMaybe |
  TUnknown`) → Bend text. `for` accumulator → fold; early-`return` loops → fold over `Either`
  (tier-2); `while` → `go` with proved rank; `if` → `match` on Bool; short-circuit preserved via
  helper matches (never eager bools). Python `int` ≠ `Nat` without a range contract. Judge loop:
  emit → `bun bend2/main.ts` check → four-lane run → bounded repairs (type/fold choice only),
  3 rounds; `tests/translator/judge.py` extracts allow-listed functions only, never imports them.
- Demos: **T1** `wiki.py:92 normalize_stem` (bring-up, right after P4 + Lint T; ASCII contract —
  no Unicode case parity claim); **T2** `overview.py:15 repo_of` (primary: prefix matching,
  longest-on-tie, early None, `split(maxsplit=1)` → fold + Maybe); **T3** `synapse.py:77
  fm_sources` (regex-integration: `re.S`, lazy `*?`, capture, splitlines — after R4 + P4c
  slicing/comprehensions; uses one search, not globals). No original doctests exist in any
  candidate [M] — **labeled contract fixtures** become the `#|` lines, never invented provenance.
  If exactly two showcases ship: repo_of + fm_sources, with normalize_stem retained as bring-up.

## 5. Dependency order

```
R0 → R1 → R2 (measure base) → R3 → R4(+R4b) → R5 (measure comp) → R6 → (tier-2: R7 research)
P0 → P1 → P2 → P3(needs R3; measured) → P4 → P5 → P6 → P7
Lint: T,A,U after P4 · X after P5 · M after P6
T1 after P4+Lint T · T2 after P4 · T3 after R4+P4c
```
P0–P2 run alongside R0–R4: different files, no cap contention.

## 6. Acceptance (all green before "done")

- `bun gates/repo.ts` n/n with new allow lines (`tests/(regex|parser|lint|translate)/`,
  `demos/python/`, harness scripts) + caps set by measurement; `bash tests/caps.sh` green.
- Unchanged: `bash tests/run.sh` · `--strings` 85/85 · `tests/codex/run.sh` 161/161.
- `bash tests/run.sh --regex` four lanes + gpu; `oracle.py` 0 diffs; `runtime.py` clean under
  ASan/UBSan; `bench.bend` doubling linear + rescan constant recorded.
- `bash tests/parser/run.sh`; `diff.py --corpus <tier>` writes RESULTS.md with full denominator;
  adversarial **0 fail-stops**. `bash tests/lint/run.sh`; forged certificates rejected.
  T1/T2 (T3 if R5) pass four lanes.
- Every namespace runner includes a **harness self-test with a deliberately wrong fixture that
  must fail** — the gate proves it can fail.

## 7. Risks (carried, each with its mitigation)

1. Cap estimates are [E] until R2/R5 — gates decide; layout (not feature) may shift if base > +5k.
2. Reference VM is slow on interpret — oracle texts ≤ 64 cp; 500-pair interpret sample only.
3. Interpreter stack on deep ASTs (strings overflowed at 45 KB [M]) — corpus runs on the C lane;
   adversarial depth bounded by the oracle's own 200.
4. JS `find_all` adds O(k·n) prefix scans — documented; bulk native path if the bench demands.
5. Oracle quirk classes (backtracking timeouts, `$`/LF subtleties, pos-clamping) — oracle-failures
   are recorded as such, never converted into parser verdicts or silently normalized away.
6. [A] to verify at P0: multi-MB `File.read` on C; `exit 1` from an IO main; K measured.

## 8. Arbitration calls — the ledger (fable × astra → decision)

1. **Global APIs v1:** fable ship-with-laws vs astra block-then-budget → **ship budgeted** (one
   budget, no partial success, rescan constant measured). The three most-used functions don't
   wait; the worst case is bounded and stated.
2. **Nullable repeats:** fable full reject vs astra reject-unbounded-only → **astra's finer
   policy**: finite/nullable bounded expansion allowed, unbounded rejected with its own error.
3. **Semantics pin:** fable Python-re empty-match vs astra ECMAScript RepeatMatcher → **CPython
   3.11 `re.ASCII` is the single pin**; ECMAScript divergences documented; bun a cross-check only.
4. **Parser shape:** fable direct recursion vs astra pre-built frames → **direct recursion +
   measured fuel + fuzz criterion**; frames held as escalation trigger, not built speculatively.
5. **Constants canonicalization:** fable value-normalized vs astra spelling-preserved → **value-
   normalized at AST (concatenation-safe), spelling already gated at the lexer (`lexdiff`)**,
   locations separate pass.
6. **`Match` retains source?** astra yes vs fable no → **no** (explicit `s` parameter; fewer
   retained refs; affine discipline).
7. **Lint scope:** fable laws+fixtures vs astra certificates-for-everything → **small verifier:
   certificates for T now, X later; everything else fixtures + labels; forged-cert tests
   mandatory.**
8. **GPU scope:** fable LF-chunk tier-2 vs astra independent-records (with counterexamples) →
   **independent records v1; chunking = tier-2 research only** (astra's `[^x]*`/`\s+`/`^` cases
   are the counterexamples that killed the naive version).
9. **Sizes:** measure at R2/R5; cap = next round thousand; separate-module trigger if base > +5k.
10. **Both v2s' remaining agreements adopted as-is:** split = gaps-only; find_all returns Match
    records; no host RegExp; code-point offsets; program-size constants; harness self-tests;
    corpus manifests with hashes; separate evidence tiers for every claim class.
