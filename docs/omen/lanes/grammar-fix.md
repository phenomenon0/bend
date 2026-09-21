# Grammar fix (2026-09-21): the mask at the nesting ceiling

Branch `lane-grammar-fix`, worktree `bend-work-grammar-fix`, on `18577c99`.
This fixes the bug the [decode lane](decode.md#the-real-bug-depth-64) found
and pinned: at 64 open containers, `mask(s)` offered `[` and `{`, but `step`
killed the state on either one.

Result:

- **Power PASS: 150, FAIL: 0** (`bash tests/power/run.sh`, full);
- **Decode PASS: 28, FAIL: 0** (`bash tests/decode/run.sh`);
- `bun gates/repo.ts` passes.

Nothing in `bend2/` was touched, no cap moved, and nothing was pushed.

## The fix: one def

`push` refuses a 65th container (`power/grammar.bend:257-265`). The mask now
refuses the two bytes that would push one. `mask.val` is the new def
(`power/grammar.bend:975`), and the Val and Vale arms of `mask.at` call it
where they used to read `M.vstart()`:

```
def mask.val(deep: Bool) -> Mask:
  match deep:
    case True{}:
      Mask{0, 67051524, 0, 1065024, 0, 0, 0, 0}
    case False{}:
      M.vstart()
```

The deep mask is vstart less two bits. Both are bit 27: `[` (91) is the whole
of word 2, and `{` (123) comes out of word 3, which leaves `f`, `n` and `t`
(64 + 16,384 + 1,048,576 = 1,065,024).

The ceiling, `U32.is_ge(depth(s), 64)`, is now written twice, once in `push`
and once in `mask.at`. That is the module's design, not a shortcut. The mask
reads the node and the stack, the step runs the transition, and the two are
kept apart so that the law `allows(s, c) == live(step(s, c))` tests something.
If the mask asked the step, the fixture could not catch them disagreeing. What
was missing was a fixture row at the ceiling, and it has one now.

## The oracle rows

`tests/power/grammar_gen.py` gets two extra prefixes in its pin list, one for
each arm the fix touches:

| Prefix | State | Mask, derived and brute-forced |
|---|---|---|
| 64 `[` | `vale/64` | ` 9-10 13 32 34 45 48-57 93 102 110 116` |
| 63 `[`, then `{"a":` | `val/64` | ` 9-10 13 32 34 45 48-57 102 110 116` |

The brief asked for a depth-64 row. There are two because Val and Vale are
separate arms, and one row would leave one of them unpinned. The second row
also puts an object at the top of the stack, since word `k1` holds the kind
bit of containers 33 through 64.

The fixture was regenerated as its header says: `python3 grammar_gen.py >
grammar.bend`. It now has 179 `#|` rows (72 pins), up from 177.

- **Before the fix** (the new fixture, the old `grammar.bend`, interpreted):
  2 of the 179 rows differ, exactly the two new ones. In each, Bend's own
  256-byte probe agrees with Python and only the derived column is wrong:

  ```
  vale/64 | 9-10 13 32 34 45 48-57 91 93 102 110 116 123 | 9-10 13 32 34 45 48-57 93 102 110 116 |
  val/64 | 9-10 13 32 34 45 48-57 91 102 110 116 123 | 9-10 13 32 34 45 48-57 102 110 116 |
  ```

- **After:** 0 rows differ, on all five lanes (check, interpreter, JS, C, and
  C on one thread). The generator's output matches the checked-in file byte
  for byte, which is the `[oracle]` lane.

## The decode pins

Each of the three pins in `tests/decode/refuse.bend` moved as that file's
header predicted. The header now describes the ceiling instead of the bug.

| Row | Before | After |
|---|---|---|
| `depth 64` mask | `vale/64 mask  9-10 13 32 34 45 48-57 91 93 102 110 116 123` | `vale/64 mask  9-10 13 32 34 45 48-57 93 102 110 116` |
| `depth 64, [ weighted` | `` `[` -> dead/0 split `` | `refused empty` |
| `depth 64, ] weighted` | `` `]` -> sep/63 split `` | `` `]` -> sep/63 ok `` |

None of them got weaker. The `[` row is now the same refusal as `illegal only`
above it: the one weighted token is illegal, so the decoder refuses rather
than emit anything. The `]` row passes because the frontier pass checks the
law on all 18 tokens, `[` and `{` included, and they now agree.

## Measured

- **Machine:** AMD Ryzen 7 7700X, Linux `6.17.12-300.fc43.x86_64`, Bun 1.3.4.
- **Load:** shared. The one-minute load average was 5 to 6 during the timed
  runs.

**The suites:**

- `tests/power/run.sh`: 1:34.6 wall (186.8 s user);
- `tests/decode/run.sh`: 29.8 s wall (56.4 s user).

**The decoder's hot loop:** `tests/power/bench/grammar.bend` derives a mask
before every byte, 85,983,692 times. It was built to C from the old and the
new `grammar.bend` and run three times each, alternating, with `--gpu off
--threads 1`.

| | Wall, 3 runs | Checksum |
|---|---|---|
| Before | 0.81 / 0.81 / 0.81 s | 3230437634 |
| After | 0.81 / 0.81 / 0.82 s | 3230437634 |

The checksum folds all eight mask words at every position, and it did not
move. That is expected, since the bench nests only 8 deep. The fix's extra
depth compare costs nothing measurable here.

## Notes

- **The power oracle for `assign`** imports numpy and scipy, and this
  machine's `python3` has neither. The first full run reported `FAIL assign
  [oracle]` with a `ModuleNotFoundError`, while all five of `assign`'s Bend
  lanes passed. The run above put a throwaway venv under `$HOME` first on
  `PATH`, and that venv reproduces `assign.bend` and `grammar.bend` byte for
  byte. It is an environment gap, not something this lane caused or fixed.
- **Caps**, all `ttok < FILE` against the existing rules, none moved:

  | File | Before | After | Cap |
  |---|---:|---:|---:|
  | `power/grammar.bend` | 9,862 | 9,979 | 64,000 |
  | `tests/power/grammar.bend` | 6,165 | 6,353 | 16,000 |
  | `tests/power/grammar_gen.py` | 4,640 | 4,688 | 16,000 |
  | `tests/decode/refuse.bend` | 1,766 | 1,744 | 16,000 |
  | `docs/omen/lanes/decode.md` | 3,941 | 3,982 | 16,000 |
  | this report | | 1,885 | 16,000 |
- **Not run:** the mini-cluster gates (`gates/test.ts`, `gates/perf.ts`) and
  the GPU lanes.
