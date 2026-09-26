# translator-census — a coverage number anyone can reproduce, and the five blockers it ranked (2026-09-25)

The fuzzer (`translator-join.md`) proves soundness and says nothing about coverage: it
generates inside the fragment by construction. Coverage was measured once before, by
stubs1: 33 of 480 candidates on the author's own tree, so nobody else could
reproduce it. This lane adds the census and closes the blockers it and stubs1 ranked
that need no new kernel rule.

## The census

`python3 tests/translator/census.py [TREE] [--jobs 4] [--json OUT]`

The tree defaults to CPython's own standard library, which every machine with the
oracle has.
- Every distinct top-level def is translated alone. An unannotated def is probed with
  stubs: its parameters all `str`, all `list[str]` or all `bool`, crossed with the four
  return types. The search stops at the first stub that emits, and tries another only
  when the refusal is about types. "Emits (stub)" is an upper bound under an
  unreviewed claim, never a certification.
- A def is counted by its **first** refusal. Removing a blocker therefore moves defs to
  their next refusal, as well as into "emits".
- The detail column names the statement, expression, callee (read off the def's own
  AST by position) or missing method, so the table says which calls and contracts
  would pay.

## Baseline

On `/usr/lib/python3.11`, 2,962 distinct defs, **11 emit (0.4%)**. The first refusals:

| refusal | defs |
|---|---|
| header with **default values only** | **576** |
| header `*args`/`**kwargs`, or keyword-only / positional-only | 243 |
| a call (`isinstance` 87, `getattr` 24, `.CodecInfo` 120, …) | 563 |
| unresolved module name | 155 |
| bare expression statement / `try` / `import` / `global` | 123 / 101 / 70 / 61 |
| a join the fragment does not cover (several names, or `return` in an arm) | 120 |

The standard library is harder than application code (stubs1's tree): it is dense
with dynamic Python (`isinstance`, `getattr`, `type`), module state and `try`, which
a typed fragment excludes by design. Default values were the one large blocker that
is cheap and exact.

## What this lane closed, none of it a new kernel rule

| blocker | how | evidence it is exact |
|---|---|---|
| **literal default values** | pre-pass: a def whose defaults are all literals loses them from its header; each call in the module that omits trailing arguments gets the header's literals appended | a literal default is one immutable value, evaluated once, so `f(s)` means `f(s, "-")`. A non-literal default and a keyword call stay refused. |
| **truthiness in an `if` test** | `cond`: `if s:`, `not s`, and `and`/`or` inside the test read a `str` or `list[str]` as non-empty (contracted `__bool__`); `and`/`or` stay branches, so the right side runs only where Python runs it | a value position (`x = s or "d"`, a `str` in Python) is not a test and stays refused. An Optional `str`'s truth mixes `None` and `""` and stays refused. All three are pinned. |
| **`+=` on a `str` local** | rewritten to `x = x + e` | `str` is immutable, so `+=` rebinds as `=` does. A list `+=` mutates in place, visible through an alias, so it is not rewritten (pinned). |
| **contracts** | `str` `<` `<=` `>` `>=` (code-point order, as CPython); `endswith`, `upper`, `lstrip()`, `rstrip()`, `sep.join(xs)`; `int` `==` `<` `<=` `>=` `+` on naturals | each is a Base function equal to CPython on the value contract. `upper` is ASCII in Base and Unicode in CPython, which agree on printable ASCII. A natural past 2^48 fail-stops (upstream WONTFIX), so it never wraps silently. |
| **`for c in s`, `[… for c in s]`** | a `str` iterated becomes `Py.chars(s)`, the list of its one-character strings (a contracted `__iter__`), so it reaches the one list fold the kernel already checks | no renderer or kernel change: the trust surface stays the same size. |
| **module constants** | pre-pass: a top-level `NAME = literal` (or a list of `str` literals), assigned once, is substituted at each read in a def that does not bind `NAME`, and the assignment leaves the module | inside the fragment nothing mutates, so a read is the literal. A binding anywhere in a def makes the name local to all of it, so that def is left alone. Assigned twice, or computed, it stays and is refused (pinned). The assumption added beside A2: no importer rebinds or mutates it. |

`refuse.bend` moved in exactly the lines these change: `default`, `truthy if`,
`truthy or`, `augassign`, `for over str` and `comprehension over str` now emit, each
checked against CPython. Six new cases pin the refusals kept: list `+=`, `or` as a
value, a truthy Optional, and a constant that is assigned twice or computed, with the
accepted constant beside them.

## After

- **Census:** 20 of 2,962 emit (0.7%, from 11). `default values only` fell from 576
  to 0 as a first refusal (the 127 non-literal defaults now refuse as "header must be
  plain"), and those defs moved to their bodies' refusals.
- **Fuzz:** the generator also writes defaults and short calls, truth tests, `+=`,
  `for` over a `str`, and module constants. Seeds 1–3 × 300: 267, 276 and 275 emitted,
  every one holding C1 and C2. `TFUZZ PASS: 300, FAIL: 0` three times, so no soundness
  finding.
- **Suite:** `Translator PASS: 45` in-repo, with `refuse` moved and reviewed as above.
  The 16 mined demos need their trees, and are SKIP after the portability commit.

## What the tables rank next

| blocker | where it shows | what it takes |
|---|---|---|
| a loop that returns **and** accumulates; two accumulators; a join over several names; a tuple return | fuzz: now the top refusal (26 per 300). Census: 173 joins, 35 tuples | **one** new IR type, a pair, in the kernel. It is the largest remaining unlock that stays inside typed Python, and it changes what the kernel grants, so it is its own lane |
| `int` beyond naturals | stubs1: arithmetic never reached the stub stage | a design decision: I64 with overflow refusal, or bigints |
| uppercase local names (`SEP = s` inside a def) | refused by the kernel's `ident`, since a Bend capital is a constructor | rename on emission (`SEP` → `v_SEP`), with the span map keeping the Python name |
| `None` for an Optional parameter in the census's own stubs | 71 "`is None` on a name that is not Optional" | the census should also try `str \| None` parameters: this is an accuracy fix to the census, not to the translator |
| `isinstance`, `getattr`, classes, `try`, dicts | most of the census | outside a typed fragment by design |
