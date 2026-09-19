# Python syntax service: P0–P4

`main.bend` reads the path in `PY_SOURCE`. `PY_MODE=lex` prints tokens;
`PY_MODE=stats` reports tokens and consumed parser fuel; the default prints
the module AST. Compile from this worktree:

```sh
bun bend2/main.ts demos/python/main.bend -o tests/parser/_out/parser
PY_SOURCE=/path/to/input.py tests/parser/_out/parser --gpu off
bash tests/parser/run.sh
python3 tests/parser/lexdiff.py --files 200
python3 tests/parser/diff.py --corpus 1
```

The implementation is pure, checked Bend. `intake.bend` uses the existing byte
read effect and validates UTF-8 incrementally, including split multibyte
sequences. It accepts a leading BOM, loops over short reads, and bounds input
at 32 MiB. The corpus wrapper excludes non-UTF-8 coding cookies before decode.
`File.read` is separately tested with a 3 MiB regular file because that effect
decodes invalid bytes with replacement and cannot enforce strict intake.

The hand lexer handles indentation and alternate tab columns, comments,
bracket-suppressed newlines, explicit continuations, CRLF, form feed, keywords,
raw number spellings, and prefixed/single/triple strings. Unicode word ranges
are frozen from the pinned CPython 3.11.15 Unicode database. The parser defers
Unicode identifier normalization and f-strings to later slices.

The parser supports expressions, calls, attributes, subscripts without slices,
tuple/list/set/dict displays and unpacking, `lambda`, assignment and augmented
assignment, expression statements, `if/elif/else`, `while/else`, `for/else`,
`def` with the full parameter grammar, annotations and decorators,
`try/except/else/finally`, `with` (both item-list forms), `global`, `nonlocal`,
`del`, `assert`, `raise`, `return`, `pass`, `break`, `continue`, and `import` /
`from … import` (dotted names, `as`, relative levels, `*`, parenthesized lists), and
`class` (bases, keywords, `**kwds`, decorators, nested), and slices
(`a[i:j:k]`, any bound omitted, slice tuples `a[:, 1]`, in Load/Store/Del). It follows
`ast.parse`'s syntax acceptance rather than Python compilation's additional
scope checks (`*a = 1` parses). `async`/`await`, `yield`,
`except*`, comprehensions, annotated assignment, walrus, non-ASCII
identifiers, and other later-slice
productions report `Unsupported`. Syntax failures and limits have distinct
`Syntax` and `Limit` kinds. Failure prints `error KIND LINE COL MESSAGE` and
exits 1. Bracket nesting is bounded at the oracle's 200; 201 is `Limit`.

`syntax.bend` carries scalar positions, token spans, `Load/Store/Del`, expression,
statement, module, error and JSON ADTs. AST nodes carry separate semantic spans
and syntactic covers, plus a grouping bit: this preserves the oracle's spans
for `(a)+b`, `(a,b)`, and `((a,b))`. Context rewriting changes only target
containers; the base of an attribute or subscript remains `Load`.

The wire JSON has node tags, CPython field order, operator/context tags, and
`_loc: [start_line,start_col,end_line,end_col]`. Constants retain `_raw` until
the harness applies `repr(ast.literal_eval(raw))` to both sides, wrapping
adjacent literal text in parentheses and a final newline. This preserves
implicit concatenation across comments without requiring floating-point
conversion in Bend. `normalize.py` separates every location from structural
comparison and maps CPython UTF-8 byte columns to code points per LF-delimited
physical line. Trivia is dropped; there is no span sampling.

One directly recursive `go` dispatches 39 grammar modes with precedence
climbing. Every mode entry decrements a residual global budget. The first
structurally decreasing Nat proves termination independently of the residual
budget. Sequential parses thread the residual state, never replenish it
(except the `with (` header retry below).
The default is `32 * (token_count + 1)`: a conservative bound for the
dispatch graph plus its repeated Rest/collection exits. Every cycle consumes
a token, and no chain of modes between two token consumptions reaches 32
dispatches (measured highwater: 3.25 per token). The one backtracking point,
the `with (` header, restarts its second alternative from the saved budget, so
a header is metered at most twice; bodies are outside the choice. The EOF allowance
covers the final Block entry. The deterministic fuzz harness measures actual
consumption and rejects any `Limit` on an oracle-accepted generated input.
This is an implementation bound with regression evidence, not a mechanized
proof of Python grammar completeness or a bound on hardware memory/time.

No parser continuation/frame machine is used: nesting 200/201 passes the
checker, interpreter, emitted JS and C. JSON output uses an affine tail
continuation and an accumulating output buffer; token counting uses a local
tail loop. Those avoid JS stack and C repeated-copy failures on long inputs.

Run evidence and frozen manifests are written only under `tests/parser/_out/`.
`reference_probe.py` separately measures known large pure-interpreter failures
and exits nonzero when they occur; it is deliberately not relabeled as a
successful parser test. See `docs/omen/lanes/parser.md` for measured results,
the whole-file corpus denominator, and the interpreter limitation.
