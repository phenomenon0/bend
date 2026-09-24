# Dropping an `F64` on the C backend

**Status.** Surface 2 below (a polymorphic parameter), and the same word in a
generic field or in a slot another arm boxes, is fixed: comp.ts boxes a full
64-bit word there (`X64`, `x64_box`), held by `tests/base/x64_boxed.bend`.
Surface 1 (`Array` cells) is still open. See POWER.md's hazard section.

A defect found while porting the power lanes. **Not filed as a fix** — not for
lack of permission (`comp.ts` is editable; only `bend.ts` is not) but because
the fix is a new block mode in the memory manager, across four backends. See
"What a fix has to do" below. This is the measurement and the root cause, so
the next agent does not pay for either twice.

Everything below was run on this box (Ryzen 7 7700X, 8c/16t) against the
checked-out tree. Nothing here is inferred.

## The claim

On the **C backend only**, dropping an `F64` whose bit pattern is
indistinguishable from a heap pointer makes the runtime free memory it does not
own: a wrong number, a blank line, `out of memory`, or
`memory fault (machine stack overflow?)`.

The same file is correct under `check`, `interpret` and the emitted JS in every
case. `Array<U32>` and `Array<F32>` are correct in every shape run.

## The root cause

A `Term` is a tagged 64-bit word:

```c
#define term_make(tag, aux, loc) \
  (((u64)(tag) << 56) | ((u64)(aux) << 40) | (u64)(loc))
#define LOC_MASK ((1ull << 40) - 1)

INLINE bool term_triv(Term t) {
  return term_tag(t) <= TAG_PAK || t == TERM_HOLE || term_loc(t) < HEAP_OFF;
}
```

`term_sink` frees anything that is not `term_triv`. An `F64` is stored
**unboxed** — its raw IEEE-754 bits ride in a `Term`-shaped slot — so the
runtime reads a double's exponent as a tag and its low 40 mantissa bits as a
heap address. A double lands in a slot the runtime walks in two places:

**1. `Array` cells.** `comp.ts:1468`:

```ts
function lay_arr(lay: Lay): { arr: boolean; lgs: number } {
  return { arr: lay.ks.some((k) => k !== "w32"), ... };
}
```

`arr` selects a `TAG_ARR` block, whose cells `term_drop`, `blk_copy` and
`blk_keep` each walk *as `Term`s*. The packed alternative (`TAG_BUF`) is
hard-wired to 32-bit cells — `blk_ptr` returns `u32a*`, `blk_write` truncates
with `(u32)v`, `blk_node` packs two cells per word — so a 64-bit element cannot
use it and has to fall into the walked path. Hence:

| element | layout | block | cells walked as `Term`? | safe |
|---|---|---|---|---|
| `U32`, `F32` | `w32` | BUF | no | yes |
| `Nat` | `w64` | ARR | yes | yes, **by accident** — `nat_chk` caps a `Nat` at `2^48-1`, so its tag is 0 and it is always `term_triv` |
| `F64` | `w64` | ARR | yes | **no** |

The design already assumes every `w64` cell keeps `term_triv` true. `Nat` holds
up its end of that bargain by construction. `F64` is the one type that cannot.

**2. Polymorphic parameters.** `lay_of` gives a type variable layout `BOX`, and
`sig_def` is memoized by def *name*, so a polymorphic def is compiled once for
every instantiation and cannot know `A` is `F64`. `Bool.pick(F64, c, a, b)`
emits, verbatim:

```c
if (c_0 == 0) {
  term_sink(e, a_0);   // a_0 is a raw double's bits
  v_1 = b_0;
} else {
  term_sink(e, b_0);
  v_1 = a_0;
}
```

`Array.set` is an instance of both at once: `Array.swap(-T: Type, …, v: T)` is
polymorphic and `Array.set.fin(-T: Type, r: Array<T> & T) -> Array<T>` drops the
displaced element.

### Which doubles are landmines

A double is safe iff `term_triv` holds for its bits — in practice, iff **no
mantissa bit is set below position 40**, i.e. the value is representable in 12
bits of mantissa. Zero, the infinities and NaN are safe (mantissa 0); so are
`0.5`, `4096.0`, `16777216.0`, `100000.0` (`= 2^5 · 3125`, 12 bits).
`0.1`, `π`, `12291.0`, `1000000.0` (`= 2^6 · 15625`, 14 bits) are not.

```python
b = struct.unpack('<Q', struct.pack('<d', x))[0]
safe = (b >> 56) & 0x7f <= 1 or (b & ((1 << 40) - 1)) < HEAP_OFF
```

Predicted against eleven literals driven through the drop shape below, the
predicate was right on ten and conservative on the eleventh: **every value it
calls safe was correct, and every failure was a value it calls a landmine.**
`π` is a landmine that did not detonate. That asymmetry is the whole reason the
earlier magnitude sweeps looked random — whether a bogus pointer does visible
damage depends on what it happens to point at, but whether a value *is* a bogus
pointer is exact and computable.

### What is *not* a surface

Generic **containers** are fine. `lay_pack` instantiates a constructor's fields
through `ctr_doms(book, c, t.x)`, so the field gets a real `w64` slot rather than
a boxed one, and nothing walks it as a pointer. Measured clean on the C backend:
`List<F64>`, `Maybe<F64>`, `Pair<F64,F64>`, and — the case lane 12 hit — a
monomorphic record with a **mixed** layout, `Zs{z: F64, v: U32}` (`ks =
["w64","w32"]`), built from a computed `F64.mul` and dropped 2,000 times, which
returns the exact sum. That last one is quoted in full under "Smallest
reproducer" below, as the negative control.

### The three lanes against the mechanism

- **this one** — `Array<F64>`: surface 1, directly.
- **lane 13** — a guarding `Bool.pick` at `F64`: surface 2, directly. Its own
  report read this as *strictness* (a dead arm's value computed and dropped).
  Strictness is real and is a good reason to prefer `match` anyway, but it is
  not the defect: strictness only decides *which* of the two doubles gets sunk,
  and either one is equally fatal. [lanes/power-13.md](lanes/power-13.md) has
  been corrected.
- **lane 12** — a kind-`Data` record `Zs{z: F64, v: U32}` threaded through a
  fold, no `Array` anywhere: `bend: memory fault (machine stack overflow?)` on
  `c` and `c-1thread` only, dependent on how many times the `F64` path is
  evaluated. **Unisolated.** The record shape itself is now measured clean
  (above), so the drop was elsewhere in that estimator — a guarding `Bool.pick`
  is the only candidate its shape admits — but the F64 version of the file was
  replaced by an integer one and no longer exists. Recorded as unresolved
  rather than guessed.

## Retractions

Earlier in this session I broadcast two characterisations to several lanes.
Both are **wrong** and were withdrawn on measurement:

- ~~"symptoms vary run to run, so it is memory corruption"~~ — **no.** The same
  binary run five times gives byte-identical output, and three fresh rebuilds
  of the same source give identical output. Every failing case is deterministic
  *per binary*. What varies is which failure mode a given *program* lands on
  (wrong value vs. out-of-memory), not what one program does twice.
- ~~"values needing about 13 or more significant mantissa bits corrupt"~~ —
  **half right, and retracted as stated.** There *is* a threshold, but it is a
  bit position, not a count of significant digits: a mantissa bit set below
  position 40. That is why `4097` (mantissa bit 40, safe) sat on the wrong side
  of a "13 significant bits" reading while `3 · 4097 = 12291` (bit 39) fails.
  Magnitude correlates with nothing; the *bit pattern* correlates exactly.

A third characterisation, from the first version of this document, is also
withdrawn:

- ~~"it is not an `Array` bug — the trigger is a **computed** `F64` rather than
  a literal one"~~ — **no.** The original discriminating pair confounded two
  variables: its literal was `100000.0d` (12 mantissa bits, safe) and its
  computed values were multiples of `4097` (14 bits, landmines). Driving
  *literals* through the same runtime-built array separates them, and literals
  fail: `12291.0d`, `24579.0d`, `1000000.0d` all blank the output and `0.1d`
  and `1048577.0d` both take a memory fault, with not one computed value
  anywhere in the file. Literal-vs-computed predicts none of this; the bit
  predicate predicts all of it. It *is* an `Array` bug, and separately a
  polymorphic-parameter bug, for the one reason given above.

The practical advice given to the lanes — *use `F32` or `U32`* — is unchanged
and still holds for every shape tested here.

## Smallest reproducer

Builds eight `F64` slots, reads slot 3, drops the array.

```bend
import Base

def v(+i: U32) -> F64:
  F64.mul(U32.to_f64(i), U32.to_f64(4097))

def f(fuel: Nat, +i: U32, a: Array<F64>) -> Array<F64>:
  match fuel:
    case 0n:
      a
    case 1n++p:
      f(p, U32.inc(i), Array.set(F64, a, i, v(i)))

def read(r: Array<F64> & F64) -> U32:
  (a, x) = r          # `a` has zero further uses: the array is dropped here
  F64.to_u32(x)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(U32.show(read(Array.get(F64, f(8n, 0, [0.0d : F64^3n]), 3))))
```

`3 * 4097 = 12291`.

| lane | output |
|---|---|
| `check` | All terms check. |
| interpret | `12291` |
| emitted JS | `12291` |
| emitted C (16 threads) | `1` |
| emitted C `--threads 1` | `1` |

It reproduces identically at one thread, so it is a codegen defect, not a
schedule-dependent race.

An even smaller one never reads the array at all — it builds it and throws it
away — and that is enough:

```bend
def sink(a: Array<F64>) -> U32:
  7

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(U32.show(sink(f(8n, 0, [0.0d : F64^3n]))))
```

interpret `7`, C `bend: out of memory: run again with a bigger span, as in --gpu 8GB`.

For the second surface — no `Array`, no fork, twelve lines:

```bend
import Base

def one(+i: U32) -> F64:
  Bool.pick(F64, U32.is_eq(U32.and(i, 1), 1), 1000000.0d, 1.0d)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(F64.show(F64.add(F64.add(one(0), one(1)), one(2))))
```

interpret `1000002`, C *(blank)*. Two calls instead of three print `1000001`
correctly on both; `Bool.pick` at `U32`, `F32` or `Nat` is correct at three;
and the same three calls written as a `match` on the `Bool` are correct. The
emitted `spin_0` for this file is quoted under "The root cause" above.

And the **negative** control — the same computed double, dropped 2,000 times
out of a mixed-layout record instead of an array or a boxed parameter:

```bend
type Zs is Data:
  Zs{z: F64, v: U32}

def mk(+i: U32) -> Zs:
  Zs{F64.mul(U32.to_f64(i), 1000000.0d), i}

def take(s: Zs) -> U32:            # drops z
  match s:
    case Zs{z, v}:
      v

def loop(fuel: Nat, +i: U32, acc: U32) -> U32:
  match fuel:
    case 0n:      acc
    case 1n++p:   loop(p, U32.inc(i), U32.add(acc, take(mk(i))))

def main() -> U32:
  loop(2000n, 1, 0)
```

`1000000.0d` is a landmine by the predicate and every iteration drops one, yet
the native binary returns `2001000`, the exact sum. Constructor fields get real
`w64` slots. This is the control that rules containers out.

## The measurements

**Element type, holding the shape fixed.** Same loop, same drop, multiplier
`100000`, read slot 3, want `300000`:

| element | interpret | C, five consecutive runs of one binary |
|---|---|---|
| `Array<U32>` | 300000 | 300000 300000 300000 300000 300000 |
| `Array<F32>` | 300000 | 300000 300000 300000 300000 300000 |
| `Array<F64>` | 300000 | out of memory ×5 |

That is three shapes for `F32` in the wider sweep below plus this one, and two
for `U32`. It is not "always correct" — it is "correct everywhere it was run",
and it was not run much.

**Drop vs. keep.** The *only* difference between these two files is whether
`read` returns the array alongside the value or lets it go:

| | want | interpret | C | C `--threads 1` |
|---|---|---|---|---|
| drop the array | 12291 | 12291 | **1** | **1** |
| keep it alive | 12291 | 12291 | 12291 | 12291 |

**Values, in the drop shape.** From the eleven-case sweep:

| case | interpret | JS | C 16T | C 1T |
|---|---|---|---|---|
| u32 ×10007 | 30021 | 30021 | 30021 | 30021 |
| f64 ×0.5 | 3 | 3 | 3 | 3 |
| f64 ×10000 | 30000 | 30000 | 30000 | 30000 |
| f64 ×4097 | 12291 | 12291 | **1** | **1** |
| f64 ×8193 | 24579 | 24579 | 24579 | 24579 |
| f64 ×10007 | 30021 | 30021 | 30021 | 30021 |
| f64 ×π | 9424777 | 9424777 | 9424777 | 9424777 |
| f64 ×0.1 | 300000 | 300000 | **303** | **303** |
| f32 ×10007 | 30021 | 30021 | 30021 | 30021 |
| f32 ×π | 9424778 | 9424778 | 9424778 | 9424778 |
| f32 ×0.1 | 300000 | 300000 | 300000 | 300000 |

Within the drop shape the stored value decides whether it fires. `4097` passing
and `8193` failing is what made this look random; it is not, once the value
read is the one actually stored (`3 · 4097 = 12291`, not `4097`).

**Literals, in the drop shape, against the bit predicate.** Same file each
time, filling eight heap slots with one `F64` *literal* and dropping the array
unread — no computed value anywhere:

| literal | predicate | C |
|---|---|---|
| `0.0d` | safe | `7` |
| `0.5d` | safe | `7` |
| `4096.0d` | safe | `7` |
| `100000.0d` | safe | `7` |
| `16777216.0d` | safe | `7` |
| `12291.0d` | landmine | *(blank)* |
| `24579.0d` | landmine | *(blank)* |
| `1000000.0d` | landmine | *(blank)* |
| `0.1d` | landmine | `bend: memory fault (machine stack overflow?)` |
| `1048577.0d` | landmine | `bend: memory fault (machine stack overflow?)` |
| `3.14159265358979d` | landmine | `7` |

Ten of eleven exact, one conservative, and no safe value wrong. This is the
table that retires both the literal-vs-computed reading and the magnitude
reading at once.

**Controls that rule things out.**

- *Not plain `F64` codegen.* Two files compute the identical `F64` arithmetic
  with no `Array` at all and C is correct: 12291 and 300000.
- *Not the `Array`, and not `F64` storage.* Filling the eight slots with the
  **literal** `100000.0d` and dropping the array unread is correct (`7`);
  allocating an `Array<F64>` and dropping it without writing anything is
  correct (`7`). Only the computed value fails. This is the control that moved
  the diagnosis off `Array` entirely.
- *Not the heap span.* `--gpu 8GB` does not rescue any out-of-memory case; all
  three still die. So it is unbounded allocation or corruption, not sizing.
- *Not nondeterminism.* Five runs of one binary, then three fresh rebuilds:
  identical every time.
- *Not every read.* A probe that reads **all eight slots** in a loop, keeping
  the array threaded through, prints `28679 24582 20485 16388 12291 8194 4097 0`
  correctly on all four lanes — including slot 3, the slot the reproducer gets
  wrong.

## What a fix has to do

Not a one-line predicate flip. Widening `lay_arr`'s test to
`ks.some((k) => k === "box")` is the *right* condition — only a box cell holds a
reference — but it routes `Array<F64>` into `TAG_BUF`, which cannot store it:
`blk_ptr` is a `u32a*`, `blk_write` truncates with `(u32)v`, and `blk_node`
packs two cells into one word. Flipping it alone silently halves every double.

The fix is a **third block mode**: cells one `Term` wide, as `TAG_ARR` already
stores them, but opaque — never walked, kept, or sunk per cell, and freed
shallow. That means a flag on the block term (tags 0–7 are taken; `term_blk`
builds `TAG_ARR` as `term_buf | arr << 57`, so it needs a spare bit or a new
tag) plus the matching arm in `term_drop`, `blk_copy`, `blk_keep`, `blk_node`
and `blk_half` — in the C runtime, the JS emitter, Metal and CUDA. It also
retires the accident that keeps `Array<Nat>` correct today.

The second surface needs its own fix: either box a `w64` when `val_to` converts
it into a `BOX` slot (and unbox on the way out), or key `SIGS`/`BRWS` by the
instantiated type arguments so a polymorphic def is emitted once per layout.
`emit_native` *already* keys each spin by `[def, ...erased arg layouts]`
(`comp.ts:2607`), so the specialization exists — it just never feeds back into
the parameter layouts `sig_def` hands out.

Both are real changes to the memory manager of the language, with leaks and
double-frees as the failure mode. That is why these lanes measured it and
routed around it instead.

## Working around it

Three lanes converged on the same three answers, in ascending order of how much
they cost:

1. **Never pass an `F64` through a polymorphic parameter.** Branch with `match`
   on a `Bool`, not `Bool.pick`. Lane 13 went green on all six lanes with this
   change alone, and read it as strictness — `Bool.pick` is a function, so the
   losing arm is built and discarded. That is true and is a good reason to
   prefer `match` anyway, but it is not this defect: the losing arm is
   discarded by a `term_sink` on a raw double inside a def that was compiled
   once for all `A`. A `match` has no polymorphic slot to drop through, which
   is why it works even when both arms are large computed doubles.
2. **Use `F32` or `U32`.** Correct in every shape run here, including the exact
   shapes where `F64` fails.
3. **Remove the floats.** Lane 12's HyperLogLog harmonic sum became an integer
   sum of `2^(k-min(r,k))` terms and `log2` a fixed-point squaring ladder at
   scale 2^15, exact and identical on all four backends, asserted against
   CPython's `math.log2` to under 0.002 in log2 space. Whenever the floats are
   only ever compared or ranked, this removes the question instead of narrowing
   it.

## If you are bisecting one of these

Run the failing binary under `stdbuf -o0`. Lane 13 lost time to this: stdout
buffering swallows the rows already written when the process dies, so the
failure looks like it happened later in the fixture than it did. With the
buffer off, the last printed row is the real one.

Do not conclude "not reproducible" from a small standalone probe. Lane 12's
`Zs{z: F64, v: U32}` record reproduced inside its module and not outside it —
which makes sense under the computed-value reading, since whether an `F64` is
genuinely computed and then discarded depends on the surrounding program. A
probe small enough to fold the arithmetic away shows nothing.

## Reproducing

The scratch files are `/tmp/f64/*.bend` and are not in the repo. Every one of
them is reproduced verbatim above or is a one-line edit of one that is.
