# tests/fuzz -- the compiler, differentially

Bend's proofs are about a program's meaning; the compiler (bend2/comp.ts,
source to C and JS) is trusted, not proven. This fuzzer checks it the way
two of its bugs were found by hand: the same program in every lane must
print the same thing.

    bun tests/fuzz/fuzz.ts --ci                  # CI: seed 1, 60 programs (~2 min)
    bun tests/fuzz/fuzz.ts --n 2000 --san 5      # a campaign, ASan+UBSan on every 5th
    bun tests/fuzz/fuzz.ts --time 3600 --reduce  # an hour, each new difference shrunk
    bun tests/fuzz/fuzz.ts --one 1100007 --reduce   # one program again (SEED[:io|:f64])
    bun tests/fuzz/fuzz.ts --file x.bend         # the lanes on any file

## Generate (gen.ts)

A program is a datatype `T0` (four constructors, one recursive twice),
the prelude helpers it names, one to five generated defs and a `main`.
The defs are plain, match a parameter (nested patterns, `_` and named
default arms, literal arms, `+` fields) or recurse structurally on a
`Nat`, a list, a string (`SCon{Chr{c}, t}`, `SCon{+h, +t}`) or the
datatype. Their bodies are lets (`+x`, affine, parallel `a b = f(x)
g(y)`) and expressions over U32 (wraps, division by zero, shifts past
31), small Nats, Bool, String and its natives (split, find, replace,
pad, case, trim, ...), the packed Bytes reads (get, span, find_byte,
find_any, word_le, push, often of a value built at the call), lists
(sort, filter and map templates), Maybe, U64 and I64 (built bit by bit,
shown bit by bit), closures (applied once, picked, returned by a def),
erased parameters and `Bool.pick` everywhere, whose heavy arms the
compiler lifts into a def. Every variable is tracked with its quantity,
so an affine one is used at most once (a match's arms each start from
the same uses) and many go unused, to be dropped. `main` shows every
def's result and a few values of each type, through each type's show.
A quarter of the programs are IO (`IO.print`, binds of `IO.pure`); a
seventh use F64.

## Run (fuzz.ts)

Workers load Base once and, per program, check it (a refusal counts as a
reject), emit its JS and C and normalize its `main`. The lanes:

- interp, the reference: a pure `main` normalized by the checker; for
  an IO program, its pure twin (each bind a let, the prints one string),
  since an IO `main` run by `bend` is the JS runtime, not a second
  opinion. F64 is opaque to the normalizer: those programs compare JS
  against C.
- js: `bun p.js`. c: `clang -O3`, as `bend -o` builds it; c1: the same
  binary on one thread (`--threads 1`), where a parallel let runs inline.
- san (`--san [K]`): the C again at -O0 with `-fsanitize=address,undefined`
  (every Kth program); a sanitizer report is a difference on its own.

A difference is named by its signature (`c:out`, `js:exit`,
`san:report`, ...). `--reduce` shrinks one program per signature: it
removes main's parts, defs, lets and match arms, puts each type's
smallest value in a node's place or hoists a same-typed child, and keeps
an edit when the program still checks and still differs the same way.

Kept out, by design and counted as agreement: a Char past U+10FFFF or a
surrogate in a string (the JS lane refuses it, and says so), a JS stack
overflow in a deep non-tail recursion (WONTFIX.txt's SOON, #798: a string
of 84034 cells through `Bytes.to_list` was one), Nats past a
few thousand (the normalizer counts in unary, UPSTREAM U16),
`List.map` on a `List<&2, _>` (UPSTREAM F05).

## Found

- UPSTREAM U19: a `U32{w}` handed on whole and walked to a default arm;
  the C emitter lays a `WNil` whose id it never declared, and clang
  refuses the file (`tests/base/word_unpack.bend`; also on canon).
- `I64.neg` of I64's minimum negated through `int64_t` in C: undefined,
  seen by UBSan, and at -O3 clang folds `neg(x) == x` to `x == 0`
  (`tests/base/i64_neg_min.bend`; I64 is ours, not canon's).
- Reverting either known fix (a peek argument evaluated twice, c823679d)
  or breaking `U32.mul` on one lane is found in under a hundred programs.
