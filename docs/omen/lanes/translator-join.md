# translator-join — the translator's fuzzer, and the join it asked for first (2026-09-24)

Touched:
- `tests/translator/fuzz.py` (new)
- `demos/python/translate.bend`: `last_stmt`, `ends`, `one_name`, `same_ty`, `var_name`, `unlet`, and one new arm in `block`
- `tests/translator/emit_join.bend` (new)
- `tests/translator/refuse.bend` (three pinned lines, reviewed below)

`bend2/` and `gates/` were not touched.

## The fuzzer

`python3 tests/translator/fuzz.py [--n 200] [--seed s] [--jobs 4] [--inputs 12] [--interp k]`

It generates typed modules of one to three defs in and around the fragment:
- types `str`, `bool`, `list[str]`, `str | None`;
- the contracted primitives;
- `if`/`else`, joins, the fold shape of `for`, the guarded `split(sep, 1)[1]`, `is None`, and calls down the rank.

`translate.bend` is built once to JS (0.25 s a module). A module the translator refuses is counted by its first diagnostic. An emitted module owes C1 (it checks) and C2 (on twelve generated calls per def inside the value contract, every lane prints CPython's result). A call on which CPython *raises* while the translation returns anything is a soundness hole: the kernel granted a partial operation. Findings shrink line by line and replay from `(seed, i)`.

**Before the change** (seed 1, 300 modules): 222 emitted, **all 222 held C1 and C2** on JS and C, with the interpreter sampled on 1 in 30. There were no soundness findings: the kernel's grants held on every generated input. The refusal table ranked the fragment's gaps:

| refusal | per 300 |
|---|---|
| no return: falling off the end | **51** |
| None outside an Optional return type | 10 |
| for: a loop that returns must not also assign | 6 |
| no def ranked below this one takes (…) | 6 |
| for: the body must assign exactly one accumulator | 4 |

## The join

The top row was not about returns. `if c: t = a else: t = b` is the idiom it refused, and the diagnostic blamed the wrong statement. An `if` arm was elaborated alone, and it had to end every path in `return`. The statements after the `if` were chained onto the else side only.

Now, where the old rules refused (an arm that does not end every path, and not the old case of a last `if` in a fold step), the `if` is a **join**:
- the arms together assign exactly one name `x`, and contain no `return` and no `break`;
- each arm is elaborated as a block whose accumulator is `x`, the way a fold step yields its accumulator;
- the arms must give `x` one type;
- the result is `let x = (yes if c else no)`, and the statements after the `if` are elaborated **once**, with `x` bound.

An arm with no statement for `x` yields `x` as bound before the `if`. If it was unbound there, the join is refused: *"x is unbound after the if on the path that does not assign it"*, which is the path where CPython raises. Two names joined are refused with a message that says so.

Two designs were tried before this one, and both are recorded because both failed on something real:
1. **Duplicating the continuation into each arm.** It was correct, but helper defs are named by source span, so a duplicated `if` collided (`two helper defs share a name`). It was also exponential over sequential joins.
2. **The first version of `ends`** used Bend's strict `||`/`&&` around its two recursive calls, so both ran at every level: 2^fuel. The file's own header warns against strict `||`, and it now uses `S.choose`.

**The kernel was not changed.** It refuses a `let` in argument position, and the join's branch is a let's value. So an arm's `let x = e in x` is reduced to `e` (`unlet`) before the IR reaches the kernel. Elaboration is untrusted, and the kernel re-derives the whole result. An arm of several statements keeps its lets and is refused, which is the safe direction.

**Emissions that did not change.** No existing emission changed: the join fires only where the old rules refused. The five `emit_*` pins held byte for byte. `refuse.bend` changed in exactly three lines, each checked against CPython:

| case | was | now |
|---|---|---|
| after if in loop (`if x == s: a = x`, then `a = None`) | refused | emitted (a join on `a`, then the rebind) |
| path falls (`if s == 'a': s = 'b'`, then `return s`) | refused ("no return") | emitted |
| if falls then return (`y = x` in one arm, then `return [x]`) | refused ("falls through") | refused: `y is unbound after the if on the path that does not assign it` |

## After

Fuzz seeds 1, 2 and 3 (300 modules each, interpreter sampled on 1 in 30): **268, 268 and 270 emitted** (from 222 on seed 1), and every one holds C1 and C2: `TFUZZ PASS: 300, FAIL: 0` three times. That is 806 translated modules and no finding.
Suite: `Translator PASS: 44` (the 40 in-repo items and `emit_join` on four lanes). The 16 mined demos need their source trees, as before. `bun gates/repo.ts` passes 56 / 56.

Next, by the table: `None` in an Optional position other than a return (10 per 300); a loop that returns and also accumulates (7); `str` passed where `str | None` is declared, which needs an implicit `Some` at the call (6).
