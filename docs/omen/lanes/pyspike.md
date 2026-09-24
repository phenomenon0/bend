# pyspike lane — a Python subset on a Bend stack VM (opus 5, 2026-09-20)

Branch `lane-pyspike`, worktree `bend-work-pyspike`, off `5513be61`. Touched:
`demos/python/vm.bend` (new, 1,323 lines), `demos/python/vm_{arith,logic,flow,
calls,print}.py` (new, the fixtures), `demos/python/vm_run.sh` (new, the
battery), `.gitignore` (+1 line, `tests/vm/_out/`). 1,530 insertions, nothing
deleted. **`bend2/` and `gates/` untouched**, which is the lane's constraint and
also the reason one deliverable is not where the brief put it (see Deviations).
Nothing pushed.

## Verdict

| | |
|---|---|
| the three handed-off faults | **fixed** — and two of them were not the family the handoff named |
| four lanes agree with CPython 3.11.15 | **yes** — 5 fixtures x (interpret, js, c), byte for byte |
| battery | `bash demos/python/vm_run.sh` — **VM PASS: 20, FAIL: 0** |
| controls | a mutated expectation is caught; three out-of-subset programs are refused with an exact message and a non-zero exit |
| gate | `bun gates/repo.ts` — **PASS: 55 / 55** |
| caps | **none moved**: vm.bend 17,789 / 64,000 ttok, vm_run.sh 1,451 / 4,000 |
| the headline claim — "the dense U32 dispatch lowers to the new table" | **no.** The match is dense and contiguous `0..26`; it emits a 32-bit tree, not a `TAB_AT`. Measured, with a two-file probe. See *The dispatch*. |

## The subset

Source -> the house lexer (`lexer.bend`) -> the house parser (`parser.bend`) ->
`S.Json`, the typed AST -> bytecode -> a stack VM. The front end is **reused,
not rewritten**: `syntax.bend`, `intake.bend`, `lexer.bend`, `parser.bend` and
`nodes.bend` are ~2,100 lines that already shipped for the lint and translate
demos, and `vm.bend` is only the two new halves, the compiler and the machine.

In: non-negative int literals, `True`/`False`/`None`, `+ - * // %`, the six
comparisons, `and`/`or`/`not` with Python's *operand* semantics (`1 and 2` is
`2`, `0 or 7` is `7`), bools as ints (`True + True` is `2`), assignment and
augmented assignment, `if`/`elif`/`else`, `while`, the conditional expression,
`def` with positional parameters, calls, recursion, `return`, `pass`, and
`print` with any number of arguments.

Out, and *refused by name* rather than miscompiled — sixteen messages, of which
the three the subset leans on hardest are:

```
chained comparisons are outside the subset
strings are outside the subset
a negative result is outside the subset
```

and the rest cover floats, `*args`/`**kwargs`/keyword-only, keyword arguments,
decorators, unary minus and `~`, multiple assignment targets, calling a
non-name, and one catch-all each for an unhandled expression, statement,
operator, comparison, assignment target and augmented operator. A refusal is a
`fault` string threaded through the compile; it compiles to nothing and rides
out to the top, so the first refusal wins and nothing downstream runs.

`3 - 9` is refused because an int is a `Nat`. That is a subset hole with a
shape, not a bug: signed ints want a sign on `VInt` and a sign rule on all five
arithmetic ops, which is a second lane.

## The bytecode

27 opcodes, dense and contiguous, `op: U32`, two `Nat` operands:

```
  0 CONST a      6 ADD      11 LT     17 NOT      23 CALL a b
  1 LOAD_L a     7 SUB      12 LTE    18 JUMP a   24 RET
  2 STORE_L a    8 MUL      13 GT     19 JIF a    25 PRINT b
  3 LOAD_G a     9 DIV      14 GTE    20 JIT a    26 HALT
  4 STORE_G a   10 MOD      15 EQ     21 JIFK a
  5 POP                     16 NEQ    22 JITK a
```

`JIFK`/`JITK` are CPython's `JUMP_IF_FALSE_OR_POP` pair: they pop only on the
path that does *not* jump, which is what makes `and`/`or` yield an operand
rather than a bool. `CALL a b` is function `a` with `b` arguments; `PRINT b` is
`b` arguments, not `b` instructions — that distinction cost a bug.

`x = 1 + 2 * 3` then `if x > 5: print(x)` compiles to:

```
k 0 = 1   k 1 = 2   k 2 = 3   k 3 = 5

 0  CONST 0        5  STORE_G 0    10  LOAD_G 0
 1  CONST 1        6  LOAD_G 0     11  PRINT 1
 2  CONST 2        7  CONST 3      12  POP
 3  MUL            8  GT           13  JUMP 14
 4  ADD            9  JIF 14       14  HALT
```

A fragment is held **reversed** — `Cx{code, len, env, fault}`, latest
instruction at the head — so that appending is one cons, and jump targets are
absolute positions arithmetic'd out of the sub-lengths plus a `base`. That
representation is the whole lane's bug surface; see below.

## The dispatch — dense, and it does not table

The brief's headline was that the interpreter loop is the natural first user of
the 2.0.19 dense-`U32` lookup table (`docs/omen/RIPPLE.md`), and `op_kind` was
written for it: a `match op: U32` with 27 literal arms `0..26`, no gaps.

It does not fire. In the emitted C for `vm.bend`, `TAB_AT` appears **once** —
its own `#define` — and every `CONSTV` table is one of the compiler's own
(`FID_ARITY_T`, `FID_FLAG_T`, `FID_RESW_T`, `CID_ARITY_T`, `CID_HOT_T`). What
the dispatch actually gets is the 32-bit walk: **67** sites in `vm.c` where a
word scrutinee is exploded into all 32 `((s >> i) & 1)` bits and matched down a
tree.

The gate is not density and not the scrutinee. It is the **return type**, at
`bend2/comp.ts:3195`:

```ts
function emit_row(fl: File, t: HTerm, ty: HTerm | null): string | null {
  if (ty !== null && WORDS[ty_adt(fl.book, ty)?.k ?? ""] === undefined) {
    return null;
  }
```

`emit_match` asks `emit_lits` for the rows and `emit_tab` for the table; every
row goes through `emit_row`, and `emit_row` refuses anything whose type is not
a machine word. The table is `CONSTV u64 TAB_n[]`, so its cells have to *be*
numbers. `op_kind : U32 -> OpKind` returns a `Data` ADT of 27 nullary
constructors, so row one is `null` and `emit_tab` returns `null` before it
looks at anything else.

Measured rather than read — two probes, same shape, same density, differing
only in the arms' type:

| probe | `kind(op: U32) -> ...` returns | emitted C |
|---|---|---|
| `tabw` | `U32` (`100..105`, default `999`) | `CONSTV u64 TAB_0[] = { 100ull, 101ull, 102ull, 103ull, 104ull, 105ull, 999ull };` + one `TAB_AT` use |
| `tabc` | a 7-constructor `Data` ADT | no `TAB_n` at all, no `TAB_AT` use |

So the feature works exactly as documented and the dispatch is simply not a
case of it. **A dispatch cannot be**: the point of an interpreter's `match` is
that each arm runs different code, and a lookup table can only hold a value.
The table's users are word-valued classifications — arities, precedences,
character classes — not the step function. The claim in the brief ("state it is
dense -> table") is reported here as false, because it is.

The ripple worth filing, if any: `emit_row` could admit **nullary** constructor
arms, which are constants too — a `Data` ADT with no fields is a tag, and a tag
fits in a `u64` cell. That would turn `op_kind` into one table lookup and cut
one 32-way tree out of the hot loop. It is a `comp.ts` change and this lane may
not make it.

## The stack accounting — what was actually wrong

The handoff named three faults and one family: "compile-time stack accounting
vs runtime pops". Two of the three were not that. The diagnostic that cost the
most time is worth recording first:

> **"a non-number in `*`" is what an underflow looks like from inside
> `pop_args`.** `pop_args` returns as many values as it finds; short a value,
> the missing operand reads back as a `VNone` and `nums_ok` fails on it. The
> error says *type*, the cause is *depth*. Every "a non-number in X" in this VM
> should be read as "the stack was one short at X".

Seven distinct faults, in the order they fell:

**1 · `join` reversed its later half** (the root cause of `print(1 + 2 * 3)`).
The code is held reversed, so `earlier ++ later` in program order is a plain
append in the held order. The body re-consed instead:

```
case Con{h, t}:
  Con{h, join(t, earlier)}        # was: join(t, Con{h, earlier})
```

Every call site passes a single instruction as `later` — except a nested
sub-expression. That is why `2 * 3`, `2 * 3 + 1` and `1 + 2 + 3` all passed and
only a `Mul` nested as a *right* operand failed: it was the only `later` long
enough to notice being reversed. It emitted `CONST 1; MUL; CONST 3; CONST 2;
ADD`.

**2 · `cmp_put` and `bop_put` passed the halves the wrong way round.** Both walk
their fragments last-to-first and prepend, so the accumulator is the *later*
half. `cmp_put`'s leftmost arm called `join(c, acc)` and put the operand after
its opcode — `print(1 < 2)`, fault [1] of three.

**3 · `build` shipped the wrong const pool** (`tests/vm/calls.py`, "stack
underflow"). `compile_defs` runs *after* the module body and keeps growing the
pool, but `build` took consts and `nglobals` from `cx_env(main)`, the snapshot
before it. Function-body constants at indices 6..10 read back out of a pool of
6 as `VNone`. Fixed by taking both from `bu_env(done)`.

**4 · `PRINT`'s operand was the fragment length**, not the argument count.
Correct by accident at one argument, which is every `print` a human writes
while debugging.

**5 · two reversals cancelling.** `take_def` built parameter names reversed
*and* `KCall` bound the popped values reversed, so `add(3, 4)` worked and
fixing either one alone broke it. Both fixed, plus the padding `None`s for
locals past the parameters, which sat *after* the arguments and pushed the
parameters to slots `nlocals - nparams ..`.

**6 · `and`/`or` popped twice** — the one fault that really is the named family,
and the fixtures found it, not the handoff. `bop_put` emitted a `POP` after
`JIFK`/`JITK`, which already pop on the non-deciding path. `True or False` hid
it because the jump is taken. Removing the `POP` moved `extra` from `2n - 2` to
`n - 1` and the next operand's `base` step from `+2n` to `+1n`.

**7 · the VM's own output carried a newline of its own.** `finish` used
`IO.print` on text whose lines already end in `"\n"`, so every fixture was one
blank line longer than CPython. `IO.write`.

And one cut: **chained comparisons are refused.** `a < b < c` has to evaluate
its middles twice, the `3n - 2` length accounting has no room for it, and the
brief says cut what fights for more than a round. It is a one-line refusal with
a control in the battery.

## The battery

`demos/python/vm_run.sh` — the four lanes, plus two controls:

```
ok   vm           [check]                     1   strict check, once: the VM is one
ok   vm_arith     [interpret|js|c]            3   program and the fixtures are its data
ok   vm_calls     [interpret|js|c]            3
ok   vm_flow      [interpret|js|c]            3
ok   vm_logic     [interpret|js|c]            3
ok   vm_print     [interpret|js|c]            3
ok   mutation_control  [caught]               1
ok   refusal_control   [x3]                   3

VM PASS: 20, FAIL: 0
```

Every fixture's expectation is **CPython's own stdout**, produced by
`python3 "$f"` in the same run — the oracle is pinned to 3.11.15 and the script
fails loudly on any other version, because CPython's `print` formatting *is*
the specification for `True`, `False`, `None` and the separator.

The fixtures are small on purpose and each one owns a hazard: `vm_arith`
precedence, parens, `//`, `%`, left-associativity and augmented assign;
`vm_logic` the six comparisons and the operand-value rule; `vm_flow`
`if`/`elif`/`else`, two `while`s, an `if` with no `else` and the conditional
expression; `vm_calls` two-argument calls, nested calls, `fib(10)`, a `while`
loop over locals past the parameter list, and a `pass` body returning `None`;
`vm_print` multi-argument, empty, and the three non-int values.

Control 1 hands the *same comparison path* an expectation that is off by one
line and requires it to go red — a green lane that cannot go red proves
nothing. Control 2 requires three out-of-subset programs to be **refused**,
exact message, non-zero exit: a miscompile that happened to print something
plausible would otherwise pass as silence.

## Numbers

x86_64, 16 cores, Fedora 43, clang 21, bun. `fib(24)` = 46368, the same answer
on every lane, medians of three:

| | C | JS | CPython 3.11.15 |
|---|---|---|---|
| `fib(24)` | 0.24 s | 1.41 s | 0.02 s |

About **12x slower than CPython on the C lane** and 70x on JS. That is the
honest starting point for a bytecode VM whose dispatch is a 32-way bit tree per
instruction and whose stack is a cons list — and it is the number the table
ripple above would move first. The five shipped fixtures are far too small to
time (every lane is at its process floor), which is why the measurement is an
off-fixture program and is reported as one.

Build cost, for the next agent's planning: the C build of `vm.bend` is ~70 s,
the JS build ~19 s, and one interpret lane ~19 s, so the battery is about eight
minutes wall clock.

## Caps

Nothing moved.

| file | ttok | cap | rule |
|---|---|---|---|
| `demos/python/vm.bend` | 17,789 | 64,000 | `demos/[a-z0-9_]+/[A-Za-z0-9_]+\.bend` |
| `demos/python/vm_run.sh` | 1,451 | 4,000 | `demos/[a-z0-9_]+/[A-Za-z_]+\.(c\|sh\|md)` |
| `demos/python/vm_*.py` (5) | 42-130 | 8,000 | `demos/[a-z0-9_]+/[A-Za-z0-9_]+\.py` |

## Deviations

**The battery is at `demos/python/vm_run.sh`, not `tests/vm/run.sh`.** The
brief asked for `tests/vm/run.sh`. `gates/repo.ts` has no allow row that any
path under `tests/vm/` matches except `tests/[a-z]+/[a-z0-9_]+\.bend`, so
`tests/vm/run.sh` and `tests/vm/*.py` both fail the gate with `not in the allow
list`, and this lane may not edit `gates/`. Per the brief — *if a row is
missing, STOP and note it in the report* — this is that note. The **minimal**
fix is one word in an existing alternation:

```ts
allow(/^tests\/(regex|parser|lint|translate|translator|power|vm)\/[A-Za-z0-9_\/.-]+$/, 16000);
```

which covers `run.sh` and the fixtures in one row at the cap its siblings use.
With that line landed, `git mv demos/python/vm_run.sh tests/vm/run.sh` and the
five `vm_*.py` into `tests/vm/`, and change the script's `for f in
demos/python/vm_*.py` glob; nothing else in it is path-dependent. The header of
`vm_run.sh` carries the same note so the file explains itself in place.

**Scratch lives in `tests/vm/_out/`, not `/tmp`.** `/tmp` was closed to this
agent, so the battery cannot follow `tests/translator/run.sh`'s `mktemp -d
/tmp/bend-translator.XXXXXX` house pattern. It uses a fixed in-repo directory
and `.gitignore` gained one line for it. The cost is that the battery is not
safe to run twice concurrently in the same worktree; the translator's is.

**Chained comparisons are cut**, as above.

**Untracked scratch left in place.** `demos/python/{vm_B,vm_C,vm_D,vm_E,vm_rt,
vm_small,vm_stub,vm_dbg}.bend` and `_cstmt_arm.txt` predate this lane and are
not mine to delete. `gates/repo.ts` reads `git ls-files`, so untracked files
cannot fail it. One of them earns its keep: **`vm_dbg.bend`** is `vm.bend` plus
a `dump_prog` that prints the const pool, every function and `main` as
`i op a b` — it produced the listing in *The bytecode* above and it is the
fastest way into any future accounting bug. It is generated from `vm.bend` and
will drift; regenerate rather than trust it.

## Gaps, deliberately not fixed

- **The dispatch does not table**, above. The fix is in `comp.ts`, which is out
  of this lane's reach, and it is the single change most likely to move the
  0.24 s.
- **Ints are `Nat`.** `3 - 9` refuses. Signed ints are a sign flag on `VInt`
  plus a rule on five ops, and would change every arithmetic fixture's oracle
  surface at once.
- **The stack and the code are cons lists.** `Instr` fetch walks; an `Array`
  of instructions with an index would make dispatch O(1) rather than O(1)
  amortised-by-luck, but Bend's `Array` fork/rebuild copies, so that is a
  measurement, not an obvious win.
- **No `for`, no strings, no containers, no exceptions, no classes.** Each is
  refused by name rather than silently mis-run, which is the property worth
  keeping as the subset grows.

## Review round (2026-09-23)

A deep review against CPython 3.11.15 found five programs the VM ran to exit 0
with the wrong output, which is the one thing a refusal-first lane may not do.
Each one now faults or matches CPython, and each has a control in the battery:

| program | before | now |
|---|---|---|
| `print(x)` with `x` never bound | `None` | `vm: a name read before assignment (NameError)` |
| a local read before its store | `None` | `... (UnboundLocalError)` |
| `print(f(1))` above `def f` | `1` | NameError: a module-level def is a store of `VFunc{k}` into its global where it stands, and a call loads its callee as `LOAD_GLOBAL` does |
| `print(f)` | `None` | refused: functions as values are outside the subset |
| `None == None` | `False` | `True` (`val_eq`: str by text, num by value, None with None) |

Other fixes in the same round:
- `0xbeef` and `0xE` were refused as floats. The literal walk now takes a digit of the base before the float markers.
- Ints are capped at 2**48 − 1 on every lane. Past that, the JS lane died inside the runtime and the C lane would have wrapped at 2**64. The cap is checked on literals, `+` and `*`.
- A def rebound to a non-function (`f = 3; f()`) faults at the call. Before, it silently called the def. Redefinition now binds in source order: `print(f())` between two `def f` prints `1`, then `2`.

**The C lane did not build on a 15 GB host.** The emitter peaked above 14 GB on
`vm.bend` and was OOM-killed. Bisecting by stubbing defs showed the cause:
- `cexp`'s `match tag:` over eleven string literals. A string-literal match is emitted as a per-character 32-bit bit tree, with the arm bodies under it.
- `prewalk`'s five-arm string match. After the first fix it nested past clang's 256-bracket limit.

Both now classify the tag once with an `S.choose` chain into a nullary constructor (`EK`, `PK`) and match on that. The emitter now peaks at 2.4 GB, and C emission takes 15 s instead of never finishing.

Battery: `VM PASS: 34, FAIL: 0` (7 fixtures × 3 lanes + check + mutation + 12
refusals), on x86_64 with 4 cores and 15 GB. `fib(24)` on the C lane takes 0.95 s on this host. There is no pre-change C number on the same host, because the old file could not build here.
Caps: `vm.bend` 27,059 / 64,000 ttok (25,453 before this round, so +1,606) and `vm_run.sh` 1,744 / 4,000. These were measured with
js-tiktoken's cl100k ranks, because ttok's own BPE download is blocked on this host.
They match `gates/repo.ts` exactly on the unmerged tree.

## The fuzzer (2026-09-23)

`python3 demos/python/fuzz_vm.py [--n 300] [--seed s] [--jobs 4] [--interp k]`
checks the lane's contract instead of fixtures. It generates random programs in
the subset and just past it. A program the VM runs to exit 0 must print
CPython's bytes, and CPython must also exit 0. Every lane must agree. A non-zero
exit must be the VM's own refusal or fault, never the runtime dying under it.
Any finding is shrunk line by line and written to `tests/vm/_out/fuzz/`. Each
program is a pure function of `(seed, index)`, so a finding replays.
`VM_FUZZ=n bash demos/python/vm_run.sh` runs `n` programs after the battery.
The file is `fuzz_vm.py`, not `vm_fuzz.py`, because the battery treats every
`vm_*.py` as a fixture.

About half the generated programs run cleanly on CPython. The rest raise on
purpose (TypeError, IndexError, ZeroDivisionError, NameError, RecursionError),
so the fault paths are exercised too. The first 300 programs found four problems
that the fixtures had never reached:

| finding | cause | now |
|---|---|---|
| `"\x41\101hi"` printed `AAihi` (a MISCOMPILE) | after a three-digit octal escape, the decoder dropped the next char | one exit for "octal ended" that handles the char in hand as MBody would; `vm_escapes.py` |
| unbounded recursion ran for 56 s on C and timed out on JS | there was no depth limit; CPython raises at 999 calls in flight | a depth field on `VFrame`; call 1000 faults with `(RecursionError)`; `vm_deep.py` pins 998, a control pins 999 |
| `u = print` reported a NameError that CPython never raises | a builtin read as a value fell through to an unset global | the 149 names of 3.11's `builtins` are refused by name |
| `print("\x4")` ran | a one-digit `\x` escape was accepted; CPython rejects it | refused, with two controls |

Found along the way, then implemented because they were cheap: string ordering
(`<`, `<=`, `>`, `>=`, compared code point by code point as CPython does,
`vm_order.py`), and `str * int` repetition (`vm_repeat.py`). A string stops at
2**24 characters, whether it grows by `*` or by `+`, so an exponentially growing
string is refused rather than exhausting memory.

After the fixes, seeds 1 to 4 × 300 programs report `FUZZ PASS: 300, FAIL: 0`
on the C and JS lanes, with the interpreter sampled on every 25th program for
seeds 3 and 4. Battery: `VM PASS: 53, FAIL: 0`.

What the table says comes next. Per 300 programs, these are the ones CPython
ran and the VM refused:

| refusal | per 300 | the fix |
|---|---|---|
| a negative result | 15–28 | signed ints (I64 with overflow checks) |
| an int past 2**48 − 1 | 15–24 | the same move, up to 2**63; bigints stay later |
| chained comparisons | 5–15 | a `DUP`/`ROT` pair so the middle operand is evaluated once |
| the builtin print as a value | 3–6 | functions as values (`VFunc` is already there) |
| wrong arity in a branch never taken | 1–5 | CPython checks arity at the call, so this check should move to runtime |
