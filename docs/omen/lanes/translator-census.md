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

## What-if census: what would unlock how much (2026-09-26)

`python3 tests/translator/features.py [TREE] [--methods]` reads each distinct def's AST
once and records **every** feature it uses that the fragment lacks, not only the
first refusal. A def is unlocked by a feature set F when all its missing features
are in F. It is static and an upper bound: 179 stdlib defs have no missing feature
syntactically, while 20 actually translate, so real gains are several times smaller
than the counts below. It ranks work; the translator certifies it.

Missing features by share of the 2,962 stdlib defs: calls into another module 37%,
tuples 37%, records (`self.x`, class instances) 32%, string methods without a
contract 31%, `int` 28%, subscripting 28%, keyword arguments at a call 23%,
`raise` 22%, `try` 20%, f-strings 20%.

**The plan's first ordering was wrong.** Generic types, then records, then sums
and exceptions tops out at 20% of top-level defs. The type system is not the
largest limit. Library surface (other modules' functions, string and list
methods) and cheap syntax (f-strings, keyword arguments) are. Reordered by
payoff, cumulative, top-level defs (with methods in brackets):

| tier | adds | top-level | with methods |
|---|---|---|---|
| 0 cheap syntax | f-strings, keyword args at calls, uppercase names | 6.5% | 1.5% |
| 1 int + tuples | signed int, tuples/pairs, loops that return or keep two accumulators | 10.4% | 2.5% |
| 2 library surface | more str/list methods, `range`/`enumerate`/`zip`/`sorted`, indexing, slicing | 17.7% | 4.2% |
| 3 records | dataclass/`NamedTuple` records, methods on them | 20.2% | 31.6% |
| 4 dict/set/while | | 22.3% | 34.0% |
| 5 sums + exceptions | `isinstance` on closed unions, `raise`/`try` as a result | 31.1% | 45.1% |
| 6 other-module contracts | `os.path`, `re`, `sys`, `codecs`, … as contracted calls | 47.1% | 54.3% |

What stays out after all of it is dynamic Python by design: reflection
(`getattr`, `type`), aliasing mutation, `*args`, generators, closures, `with`, I/O.
In the CPython-host model those defs simply stay in CPython.

Records are the largest single step once methods count (4% to 32%): most
Python lives in classes. Tier 6 is the other large one, and it is a library
effort, not a kernel one: each module function is one contract, ranked by use
(`os`, `os.path`, `codecs`, `sys`, `re`, `warnings` lead).

## Tier 0: cheap syntax (2026-09-26)

Three untrusted rewrites in the pre-pass (`defaulted`), before elaboration. The
kernel then checks each result as written, so none of them adds a rule the
kernel grants.

| form | rewrite | why it is exact | kept refused |
|---|---|---|---|
| `f"a{s}b"` | `"a" + s + "b"` | `str(s)` is `s` for a `str`; `+` on a `str` demands a `str` on both sides, so a field of another type is a type mismatch, never a silent format | `!r`/`!s`/`!a`, `:spec`, a non-`str` field (`f"{len(s)}"`), a raw piece, a `"`, newline or trailing backslash in a piece |
| `g(s, end="?")` | `g(s, "-", "?")`: positional, then keywords, then the header's literal defaults, in parameter order | every expression in the fragment is pure, so evaluating in parameter order rather than written order is unobservable | a keyword naming no parameter, or one already given positionally (a `TypeError` in CPython), `**kw`, a keyword to a method or builtin |
| `SEP = s` | `u_s_e_p = s` (each capital becomes `_` + lower case, after `u`) | the fragment has no nested scope, so the def is the whole scope of the name; reads and writes are renamed together | a def that already uses a mangled name, or two names that mangle alike (renaming would merge two variables) |

`DefD` now records every module def (its parameters, and its defaults only when
all are literals), so keyword ordering and default filling are one function,
`kw_args`.

Evidence:
- `refuse.bend`: `keyword call` (`g(s=s)`) moves to emitted. Seven new cases pin
  what stays refused: keyword duplicate, keyword unknown, f-string conversion,
  f-string spec, an f-string field of type Nat, a capital local (emitted), and a
  capital collision (refused).
- `emit_sugar.bend` (new) pins all three rewrites in one module.
- The fuzzer now also writes f-strings of plain fields, keyword calls in shuffled
  order over a tail of the arguments, and capital locals (127 f-strings, 42
  keyword calls and 65 modules with capital locals per 300). Seeds 1–3 × 300:
  264, 276 and 270 emitted, all holding C1+C2, `TFUZZ PASS: 300, FAIL: 0` three
  times.
- What-if census (tier-0 forms now counted as supported): the syntactic upper
  bound goes from 179 to 187 of 2,962 stdlib defs. Tier 0 is small, as the
  table predicted. Its value is the idioms it unblocks inside bigger tiers.

Next is tier 1: `int` and tuples. Base's `I64` wraps on overflow and CPython's
`int` does not, so `int` needs checked `add`/`sub`/`mul` that fail-stop past
64 bits (as a Nat past 2^48 fail-stops today). It also needs floor `//` and `%`
matching CPython on negatives, a nonzero-divisor guard, and `str(int)` for
f-strings. Tuples need the kernel's pair type.

## Tier 1b: tuples (2026-09-26)

`tuple[A, B]` is `Tup<A, Tup<B, Unit>>`: a cons chain of the item types, closed
by `Unit`. `Tup` is a two-field Data type the emitted prelude declares, along
with `Tup.fst`/`Tup.snd`, only when the module uses it.

Why not Bend's own pair `A & B`: it is a `Type` (a Sigma), not `Data`, so a
binding of it cannot be marked `+` and read twice. A tuple is read as often as
a `str` is (`s, ok = p` and then `p[0]`), so it has to be duplicable.

Why a chain closed by `Unit` rather than a right-nested pair: the arity has to
live in the type. `tuple[A, tuple[B, C]]` and `tuple[A, B, C]` are different
Python types, and `a, b, c = x` raises on the first one. With a plain nested
pair the two spell the same type, and the kernel would grant an unpack that
CPython refuses.

| form | IR | kernel rule | kept refused |
|---|---|---|---|
| `(a, b)`, `return a, b` | `IPair{a, IPair{b, Unit}}` | the type is a well-formed chain; each item has its component type | `()` in an annotation (`tuple[()]`), `tuple[A, ...]`, bare `tuple` |
| `t[i]`, i a decimal literal | i × `IProj{rest}`, then `IProj{first}` | the operand's type is a chain; the result is the chosen component | an index past the end, a subscript on anything but a tuple (list/str indexing needs the IndexError story) |
| `a, b = e` (nested targets too) | `tup_L_C_L_C = e`, then `a = tup[0]`, `b = tup[1]` (a rewrite; each line is checked as written) | the ordinary let/projection rules | arity ≠ the tuple's, a list or str on the right (length unknown), `*rest`, a temp name the def already uses |
| `for a, b in xs:` | `for it_L_C in xs:` whose step begins `a, b = it_L_C` | the ordinary fold rule | the same as the unpack |

The temporary is the point. `a, b = b, a` builds the tuple from the old values
before binding either name. Binding straight from the display would read the
new `a`.

Not in this step: `==`/`<` on tuples (no contract), a tuple's truth value, and
`len(t)`. A loop with two accumulators (`multi-accumulator`) is also out. The
census shows it unlocks 0 defs on its own, so it waits until the tiers it
co-occurs with are in.

Evidence:
- Hand test against CPython: swap, unpack, a `for k, v` fold and `t[1]`
  through a user call give byte-equal output.
- `refuse.bend`: `tuple target` moves to emitted. Two new pins are emitted:
  `tuple` and `for tuple target`. Eleven new pins stay refused: unpack arity,
  list, str, star, and a taken temp name; tuple index out of range, equality
  and truthiness; a `for` target with the wrong arity; `tuple[str, ...]` and
  `tuple[()]`.
- `emit_tuple.bend` (new) pins the module shape and span map.
- The fuzzer now has `tuple[str, bool]` as a parameter and return type. It
  also writes displays, `t[0]`/`t[1]` (and now and then an out-of-range
  `t[2]`), unpacks (and now and then a wrong arity), swaps, and `for k, q in
  [...]` folds. Per 200 modules: 189 tuple signatures, 36 unpacks, 27 tuple
  folds.
- What-if census: the syntactic upper bound goes from 187 to 212 of 2,962.
- Found on the way: `Nat.read` never finishes on the interpreter lane (its bound
  is the unary 2^48, built out in full), so `t[i]` hung there while JS and C
  passed. An index is now read by a three-digit fold (`dec`).
