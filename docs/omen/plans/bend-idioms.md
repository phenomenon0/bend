# Bend idioms — read before writing (the compile-friction card)

Every lesson here cost a compile round once. They never should again.
Paste this card into every agent brief that touches .bend code.

## The eight rules

1. **Defs are read top-to-bottom.** A def may not use a name defined below
   it — self-recursion is fine, mutual recursion is not. Restructure with a
   self-recursive worker plus a thin wrapper.
2. **The shrinking argument goes first, and everything before it must pass
   unchanged.** `def walk(+fuel: Nat, x: T)` — recursion on `fuel`; do not
   compute a new value for any argument that precedes the shrinking one.
3. **A `match` may not scrutinize computed values or locals** — only
   parameters and pattern bindings. Give it its own def (a worker taking the
   value as a parameter), or use multi-scrutinee `match a b:`.
4. **Matching consumes the scrutinee.** In an arm, rebuild what you need
   (`Nat.add(h, 1n)` for the old `hi`) or destructure.
5. **`++` on a pattern binding makes it reusable** (`case 1n++p:`), and `+`
   on a def parameter or local makes it reusable. Unmarked values are
   single-use (affine). A value used twice without a mark = compile error.
6. **Nested matches are not allowed inside one another** — flatten with
   multi-scrutinee matches (`match fuel stop b:`), wildcards `_` per column.
7. **No bare operators; no imaginary names.** `1n + x` needs `(1n + x : Nat)`
   outside literals contexts; `Nat.inc` does not exist (`Nat.add(x, 1n)`);
   check names against base.bend: `grep "def Nat\\." bend2/base.bend`.
8. **Small literals compose.** `100000000n` unary-expands and dies; write
   `Nat.mul(Nat.mul(100n, 100n), Nat.mul(100n, 100n))`.

## The loop that works

Write → compile → read the FIRST error only → fix → repeat. The checker's
messages name the rule; they are honest, not adversarial. If a shape fought
more than two rounds, the shape is wrong — restructure, don't patch.

## Error → fix FAQ (grows every lane)

| Error | Means | Fix |
|---|---|---|
| `expected: a defined name` | name below, or nonexistent | reorder; grep base |
| `a decreasing self-call` | shrink not first / earlier arg changed | reorder args, pass unchanged |
| `match cannot scrutinize computed` | match on call/local | own def, or multi-match |
| `consumed more than once` | missing `+`/`++` mark | mark it |
| `a match on a parameter or field` | nested/late match | multi-scrutinee |
| `operator needs annotation` | bare `+ - * /` | wrap `( ... : T)` |
| `literal ... unary-expands` | huge literal | compose from smalls |
