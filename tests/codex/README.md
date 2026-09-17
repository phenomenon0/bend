# Adversarial F64 tests

Six standalone Bend programs, **161 cases**, and a Python standard-library oracle.
Every program has `main() -> IO(Unit)` and prints one `case_id value` per line.
These tests target the F64 v0.1 contract in the repository's `SPEC.md`.

| Program | Cases | Coverage |
| --- | ---: | --- |
| `t_rounding.bend` | 25 | 0.1 + 0.2, thirds, square-root power, swallowed additions, cancellation, ties to even, subnormal arithmetic, normal/subnormal boundary, max finite, overflow, integer precision, literal spellings. |
| `t_special.bend` | 33 | Signed zero, reciprocal signs, infinities, invalid operations, NaN propagation and all unordered comparisons, signed remainder zero. |
| `t_conversions.bend` | 26 | U32 boundaries and invalid inputs, F32 widening, narrowing ties/overflow/underflow/negative zero, Nat conversions, low-valued raw bit patterns. |
| `t_math.bend` | 34 | All math laws, signed remainders, negative rounding, pi, and finite comparisons. |
| `t_text.bend` | 39 | Shortest formatting thresholds, valid/invalid reads, decimal ties, overflow/underflow, embedded NUL and hex rejection, show/read round trips. |
| `t_precision.bend` | 4 | The same ten-term Machin pi series with F64 and F32 arithmetic, plus their decimal accuracy counts. |

## Run after F64 lands

From the repository root:

```sh
bash tests/codex/run.sh
```

Requires Bun, Python 3.9+, Bash, `diff`, GNU `timeout`, and the compiler's native
build prerequisites (including Clang). The script changes into this directory,
then builds each program with:

```sh
bun ../../bend2/main.ts t_rounding.bend -o /tmp/cx_t_rounding
```

It runs the binary, diffs its complete stdout against `expected.py`, reports
PASS/FAIL for each case, and exits nonzero on any build, execution, or output
failure. Other programs still run after a failure. Binaries remain at
`/tmp/cx_t_*`; temporary logs are printed on failure and removed on exit. Run
one suite invocation at a time because these binary paths are fixed. Build and
execution timeouts default to 120 and 30 seconds per program; override with
`BUILD_TIMEOUT=300 RUN_TIMEOUT=60 bash tests/codex/run.sh`.

Verify or inspect the oracle without invoking Bend:

```sh
python3 tests/codex/expected.py
python3 tests/codex/expected.py t_precision
python3 tests/codex/expected.py --count
bash -n tests/codex/run.sh
```

## Oracle and interpretation

All expected numeric values are computed independently with Python binary64
`float`, `math`, and `struct`. F32 calculations round to IEEE binary32 after
every operation, including literal conversion. No Bend execution, generated C,
or implementation output is used to obtain expectations. The formatter uses
`repr()` shortest digits, expands to fixed notation for `1e-6 <= abs(x) < 1e21`,
removes `.0` and exponent-leading zeros, and retains a positive exponent's `+`.
The Bend spellings are `inf`, `-inf`, `nan`, and `-0`; preserving negative zero
is an explicit difference from JavaScript's `String(-0)`. Booleans use Base's
`True`/`False`; reads expose the constructor as `Some(value)` or `None`.

The nontrivial transcendental cases with `_scaled` names print
`trunc(result * 1e9)`, allowing harmless last-bit libm differences while testing
nine decimal places. Arithmetic, square root/power, conversions, and show/read
cases compare full shortest representations. Invalid reads must reject the
whole input: a numeric prefix before junk or NUL is insufficient. The tests do
not prescribe optional leading/trailing whitespace handling for valid numbers.
`F64.pow` is used for exponentiation because `**` is not guide-defined syntax.
Integer-exponent literals such as `5e-324d` deliberately test the promised
literal interface even if an initial parser patch only handles `1.5e3d`.

The pi demo evaluates `16*atan(1/5) - 4*atan(1/239)`, using ten Taylor terms in
each arctangent and sequential, explicitly rounded operations. F32's result is
widened only for display and accuracy measurement. Digit counts are
`floor(-log10(abs((estimate - pi) / pi)))` against nearest binary64 pi, not
counts of printed characters: the oracle yields **15 versus 7**. Both series
retain a nonzero error, avoiding `log10(0)`.

`F64.bits` cases use zero and positive subnormals whose raw patterns fit Nat's
48-bit immediate range. Ordinary doubles' raw patterns generally exceed that
range; this suite does not claim full-width Nat support or NaN-payload coverage.
It tests native CPU execution only; JS, CUDA, and performance need separate runs.

Authorship validation runs the Python oracle and shell syntax checks. Bend
compilation/execution is intentionally deferred until the F64 implementation lands.
