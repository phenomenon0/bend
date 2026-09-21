# hvm5-num — the numeric machine and its laws

Slice S1 of the hvm5 lane: hvm4's numeric rules ported into
`demos/pure_hvm5_mini`, with laws that hold and tests that measure.
Editable set was `demos/pure_hvm5_mini/*` only; `bend2/bend.ts` was
not touched. `bun gates/repo.ts` is green at 56 / 56 and no cap was
raised — `main.bend` sits at 29861 ttok against a 64000 cap.

Check the whole lane with `bash demos/pure_hvm5_mini/run.sh`:

    ok   laws
    ok   demo
    ok   tests
    PASS: 3 / 3

## What was ported

One term, `Val{+n: U32}`, is a number — hvm5.c's `Num` is the free
list's link, so the term takes the other name. One node, `Op2{+o, a,
b}`, is every operator: `o` is hvm4's, `0..16` its OP2 opcodes in its
own order (add sub mul div mod and or xor lsh rsh not eq ne lt le gt
ge), and `17`, `18`, `19` name the three nodes that are no OP2 at all
— `===`, `.&.`, `.|.`. `Inc{x}` is hvm4's `↑`.

All four operator families are strict in the left operand and share
its rules, so OP2-ERA, OP2-SUP and OP2-INC-X are one rewrite each
(`opl`), and only `op_kind` parts them once a number arrives. Those
that do differ:

| doc | port | note |
|---|---|---|
| `op2_num_num` | `opn` `Val` → `op_u32` | the 17-code table |
| `op2_era`, `and_era`, `or_era`, `eql_era` (L) | `opl` `Era` | one rewrite; the right operand is freed |
| `op2_num_era` | `opn` `Era` | |
| `op2_sup`, `and_sup`, `or_sup`, `eql_sup` (L) | `opl_sup` | takes one cell to share the right operand |
| `op2_num_sup` | `opn` `Sup` | takes **no** cell: a word copies free |
| `op2_inc`, `and_inc`, `or_inc`, `eql_inc` (L/X) | `opl` `Inc` | |
| `op2_inc` (Y), `eql_inc` (R) | `opn` `Inc`, `eqr` `Inc` | |
| `and_num` | `opl_zo` with `z = 0` | AND-ZER answers 0 and frees; AND-ONE re-enters the right operand |
| `or_num` | `opl_zo` with `z = 1` | OR-ZER re-enters; OR-ONE answers 1 and frees |
| `eql_era` (R), `eql_sup` (R) | `eqr`, `eqr_sup` | |
| `eql_num`, `eql_nam` | `eql_go` `Val`/`Val`, `Nam`/`Nam` | |
| `eql_ctr` | `eql_go` `One`, `Tup`, `Pak`/`Won` | see below |
| `eql_lam` | `eql_lam` | both binders take one fresh display name |
| `eql_use`, `eql_mat` | `eql_go` `Use`/`Use`, `Mat`/`Mat` | |
| EQL-NOT / mismatch | `eql_go` default | answers 0, frees both operands |
| `app_inc`, `use_inc`, `mat_inc` | `app`, `use`, `mat` `Inc` | every eliminator lifts itself through INC |
| `dup_nod` over numbers | `dup` `Val` / `Inc` / `Op2` | a `Val` settles both sides with the same word and takes no cell |

`eql_ctr` is the one place the docs and the C disagree, and the port
follows the C. `docs/hvm/interactions/eql_ctr.md` says a non-SUC,
non-CON constructor compares field-wise with no INC, but the binary
gives `#Pair{1,2} === #Pair{1,2}` → `↑↑1` and `#Foo{1,2,3} === …` →
`↑↑↑1`: the CON shape, `↑(f0 & ↑(f1 & …))`, at every arity. The port
writes that shape for a pair, and for a constructor run it compares
one bit at a time, which is the same rewrite once the run is
unpacked: equal outermost bits give `↑(rest === rest)`, unequal ones
give 0.

Surface syntax reuses hvm4's own parenthesized infix — `(a + b)`,
`↑x`, a decimal literal — read inside the existing `PAt{HApp{}}`
branch through one new parser phase (`POp`). No precedence climbing:
`1 + 2 + 3 + 4` is hand-bridged to `(((1 + 2) + 3) + 4)`, which is
faithful because hvm4's equal-precedence operators associate left.
The longest token wins, so a lone `&` is still a superposition and a
lone `!` still a duplication — `op_tok_longest` is that claim.

## The laws

Six new laws in `LAWS.bend`, filled in `PROOF.bend`. `bun
bend2/main.ts demos/pure_hvm5_mini/PROOF.bend` prints `All terms
check.`

| law | what it says | proof shape |
|---|---|---|
| `op_add_comm` | an operator code *is* the U32 primitive it names, so it carries the primitive's algebra: code 0 is addition, and addition commutes | the pick chain reduces on the literal code, then `U32.add_comm(a, b)` lifts through |
| `op_cmp_reflect` | code 11 is `==` and code 13 is `<`, reflected into hvm4's 1 and 0 — this pins the numbering | unfolding (`{==}`) |
| `op_edges_zero` | the edges answer zero where the C reference is undefined or platform-shaped: a zero divisor for `/` and `%`, a shift of 32 or wider | `match a: case U32{w}` opens the word so `U32.is_zero` on the divisor can fire, then unfolding |
| `op2_num_sup` | OP2-NUM-SUP distributes for free: the word goes into both sides, the env, the free list and the fresh counter come out untouched, and it costs exactly one interaction | unfolding of the `Sup` arm of `opn`, universally quantified in the env, book, continuation, registers, label and both branches |
| `op_kind_splits` | the four kinds split the codes where hvm4 splits its nodes: 0..16 read on as an OP2, 17 is `===`, 18 `.&.`, 19 `.|.` | closed, computes |
| `op_tok_longest` | the longest token wins and the operator lexer takes neither a lone `&` nor a lone `!` | closed, computes |

The bundle refuses on corruption. Seven mutations of `main.bend`,
each tried alone, each making `PROOF.bend` fail to check:

| mutation | law that catches it |
|---|---|
| `op_kind`'s boundary 17 → 18 | `op_kind_splits` |
| code 11 `is_eq` → `is_ne` | `op_cmp_reflect` |
| drop the `%` zero-divisor guard | `op_edges_zero` |
| code 0 `U32.add` → `U32.sub` | `op_add_comm` |
| OP2-NUM-SUP charges nothing (`c` for `c + 1`) | `op2_num_sup` |
| OP2-NUM-SUP takes a cell (`fh + 1`) | `op2_num_sup` |
| the lexer reads `&` as an operator | `op_tok_longest` |

## The tests

`demos/pure_hvm5_mini/TESTS.bend` — 21 programs, each parsed,
normalized and printed by this evaluator exactly as `main.bend` runs
its own, against the `#|` block the repo's test convention expects.
Ten files of hvm4's `devs/test` are hand-bridged across six of the
cases (marked); the rest were run against the reference as one-line
programs. Reference column: `~/scratch/hvm-diff/hvm4/src/hvm <file>
-s`.

| case | program (port) | hvm4 twin | normal form | hvm4 | port |
|---|---|---|---|---|---|
| `add` | `(((1 + 2) + 3) + 4)` | `devs/test/op2_add.hvm` | `10` | 3 | 4 |
| `mul` | `((2 * 3) + (4 * 5))` | `devs/test/op2_mul.hvm` | `26` | 3 | 4 |
| `divmod` | `((20 / 4) + (17 % 5))` | `op2_div.hvm` + `op2_mod.hvm` | `7` | 3 | 4 |
| `xor` | `(12 ^ 10)` | `devs/test/op2_xor.hvm` | `6` | 1 | 2 |
| `shift` | `((3 << 4) >> 2)` | `op2_lsh.hvm` + `op2_rsh.hvm` | `12` | 2 | 3 |
| `cmp` | `((2 + 3) == (1 * 5))` | `devs/test/op2_eq_t.hvm` | `1` | 3 | 4 |
| `andor` | `((12 .&. 10) .|. 0)` | — | `1` | 2 | 3 |
| `eql_num` | `(42 === 42)` | `devs/test/eql_num_t.hvm` | `1` | 1 | 2 |
| `eql_pak` | `(#(1,2) === #(1,2))` | `devs/test/eql_ctr_t.hvm` | `↑↑1` | 4 | 5 |
| `eql_lam` | `(λx.x === λy.y)` | — | `1` | 2 | 3 |
| `eql_era` | `(1 === &{})` | — | `&{}` | 1 | 2 |
| `op2_era` | `(&{} + 1)` | — | `&{}` | 1 | 2 |
| `num_era` | `(1 + &{})` | — | `&{}` | 1 | 2 |
| `op2_sup` | `(&A{1,2} + 10)` | — | `&A{11,12}` | 4 | 5 |
| `num_sup` | `(10 + &A{1,2})` | — | `&A{11,12}` | 3 | 4 |
| `op2_inc` | `(↑3 + 4)` | — | `↑7` | 2 | 3 |
| `dup_num` | `! &A{a,b} = 7; (a + b)` | — | `14` | 2 | 3 |
| `dup_op2` | `! &A{a,b} = (3 + 4); (a * b)` | — | `49` | 3 | 4 |
| `dup_inc` | `! &A{a,b} = ↑7; (a + b)` | — | `↑↑14` | 5 | 6 |
| `two_ref` | `@f = (1 + 2); @main = (@f * 10)` | — | `30` | 2 | **4** |
| `show_lam` | `λx.x` | — | `λa.a` | 0 | 1 |

Every normal form is hvm4's, byte for byte. The demo's own built-in
program is unchanged: `&S{#0{()},#1{()}}` and `- Itrs: 79
interactions`.

## Divergences, explained

**The counter's floor: one per `@ref`.** Every case reads exactly one
higher than hvm4 per reference it expands. hvm4 charges nothing for a
dereference — it has no REF interaction at all, and `@f = 1 + 2; @main
= @f` costs it 1, the one OP2. hvm5.c charges one, which is where the
demo's 79 comes from and why it must keep charging one. `two_ref` is
in the table to make this measurable rather than asserted: it expands
two references and reads two higher, not one. Nothing else in the
column differs.

**hvm4's `~` has no spelling here.** hvm5.c's lexer counts `~` a
blank (`str_ws`: `c <= ' ' || c == '~'`), hvm4's does not
(`parse_is_space`: space, tab, newline, return). The port's lexer is
hvm5.c's, so opcode 10 (bitwise NOT) cannot be written. It is a real
residual: `devs/test/op2_not.hvm` has no bridged case, and `~` was
removed from `op_tok.one` rather than left there pretending. The
opcode itself stays complete in `op_u32` and `op_show`, so nothing in
the table is a lie about the opcode set.

**The shift count clamps at 32.** `op_sh` is `U32.to_nat(U32.min(b,
32))`, because the count becomes a unary `Nat` and a 32-bit one would
not terminate. So a shift of 32 or wider answers 0 where hvm4 on x86
computes `a << (b & 31)`. Pinned by `op_edges_zero`, not hidden.

**`%` by zero.** Bend's `U32.mod(a, 0)` is `a`; hvm4's is 0. The port
guards it to 0 in `op_u32`, matching the reference. `U32.div(a, 0)`
is already 0 in both. Also pinned by `op_edges_zero`.

**Collapse.** hvm4's `-C10` enumerates a superposition's branches;
this evaluator prints one normal form. The `op2_sup` and `num_sup`
rows use hvm4 *without* `-C`, so both sides print the same
superposition and the counts are comparable.

## Named residuals — what could not be ported faithfully

- **ANY / EQL-ANY** (`*`). hvm4's wildcard has no HVM5 term, so
  `(* === b) → 1` has no counterpart.
- **DRY / EQL-DRY** (`^(f x)`). HVM5 unwinds a stuck application
  through `Sk` and never delivers one to `eql_go`, so the "compare two
  stuck applications field-wise" rule is unreachable. A stuck
  application reaching `===` falls to EQL-NOT instead.
- **DSU-NUM, DSU-INC, DDU-NUM, DDU-INC.** These are dynamic-label
  rules: a superposition or duplication whose *label* is an expression
  that reduces to a number or an INC. HVM5's labels are static codes
  in the term, so there is no label to reduce and no rule to port.
  DUP over a number, an INC or an OP2 node — the `dup_nod` shape — is
  ported and tested (`dup_num`, `dup_inc`, `dup_op2`).
- **APP-MAT-NUM.** hvm4 dispatches a tagged `λ{#a:h; m}` on a number;
  HVM5's constructor eliminator is the two-branch `λ{#0:f; #1:g}` over
  a bit run. Different eliminator, not a missing rule.
- **USE-VAL.** hvm4's `λ{f}` passes any value through to `f`. HVM5's
  `λ() f` is strictly the unit eliminator: applied to a number it is
  stuck. Different operator, not a missing rule.
- **GET-INC.** hvm4 has no rule for its pair eliminator against an
  INC, so the port has none either; the term stays stuck. Listed
  because it is the one INC-lifting rule that is *absent* rather than
  present, and its absence is deliberate.
- **EQL-CTR's SUC and CON special cases.** Subsumed: the n-ary CON
  shape is what the binary does at every arity (see above), so the
  port writes the one shape and does not branch on a tag it has no
  representation for.

## Two bugs found in the existing demo, and fixed

`lam()` returned `SCon{Chr{206}, SCon{Chr{187}, ""}}`, the UTF-8
*bytes* of `λ`, on a comment claiming `IO.print` writes one byte per
`Char`. It does not: `io_cstr` in `bend2/comp.ts` UTF-8-encodes every
code point, so the demo would have printed `Îŧ` for any normal form
containing a lambda — which the built-in program never does, so it
had never shown. My `inc()` copied the same convention and the
`eql_pak` test made it visible as `ââ1`. Both are now the character
literal (`"λ"`, `"↑"`) and the stale comment is gone. `show_lam` is
the regression test: `λa.a`, correct bytes. The demo's own output is
byte-identical either way.

## Next slices

**S2 — frontend.** The parser reads hvm4's infix only inside
parentheses and has no precedence. A real frontend would want
precedence climbing over the 20 codes, unary `-`, and character and
string literals, all of which fit the existing `Ph` phase machinery
without touching the machine. Worth doing after S3, not before: the
laws should outnumber the syntax.

**S3 — fusion laws.** The interesting claims are about `inst`'s
fusion loop (`FRoot`/`FLam`/`FOff`) now that numbers ride through it:
that copying a template under pending arguments costs no more than
copying it and then applying, and that a numeric argument reaching a
root eliminator waits (K_DISP) rather than being copied. Both are
statements about `inst`, which is pure, so they are reachable in the
same style as `op2_num_sup` — universally quantified over the env and
the registers, proved by unfolding the arm.

**Also open.** `op2_sup` takes a cell and `op2_num_sup` does not; the
asymmetry is hvm4's and is worth a law of its own, stating that
`opl_sup` allocates exactly one and shares the right operand through
it. It needs `alloc` to be reasoned about, which the existing laws do
not yet do.
