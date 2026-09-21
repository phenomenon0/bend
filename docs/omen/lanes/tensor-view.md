# tensor-view lane — flat F32 storage and borrowed view descriptors (opus 5, 2026-09-20)

Branch `lane-tensor-view`, worktree `bend-work-tensor`, off `omen` `8f9b4105`
(native I64 in). **Userland only** — `bend2/` is untouched, every line of this
lane is a module and its tests over Base as it already is. New files:

    demos/tensor/tensor.bend          the module: Ten, View, gemv, map
    demos/tensor/bench_gemv.bend      the decode skeleton on flat views
    demos/tensor/bench_split.bend     the control: the same work, three owners
    demos/tensor/bench_blocked.bend   the probe: the same work, four accumulators
    demos/tensor/twin.c               the C twin of all three rows
    demos/tensor/bench.sh             the POWER.md harness
    demos/tensor/run.sh               the four lanes over tests/tensor
    tests/tensor/gemv.bend            y <- A x through three views, by hand
    tests/tensor/views.bend           the aliasing, overlap and size evidence

`bun gates/repo.ts` **PASS: 55 / 55** (every new path lands on an existing
allow rule; no cap moved). Nothing pushed.

## Verdict

| | |
|---|---|
| a flat F32 block works over Base as-is | **yes**, as `Array<F32>` — and *only* as `Array<F32>`, see below |
| views are free of the data | **yes** — `View` is kind `Data` with four `U32` fields and no cells, so a copy is not expressible |
| gemv on flat views vs the C twin, 1T | **1.02x** — the bar was 1.1x |
| flat views vs three separate owners | **1.02x vs 1.02x** — *no difference*; the premise does not survive the measurement |
| four lanes on the semantic tests | **10 / 10** — check, interpret, js, c, c on one thread, two files |
| did clang widen the loads? | **no, and neither did it for C** on the serial row; on the blocked row **C widens the loads and Bend does not** |
| the real ceiling found | the F32 accumulator chain, not the layout: both sides run the serial row at **one add-latency per element** |

## 1. The representation, and the thing that decided it

The brief left the choice open: packed `U32` lanes or `Array<F32>` cells.
**`Array<F32>`, and the alternative is not merely worse — it is unreachable
from userland.** Packing floats into `U32` lanes needs a reinterpretation in
both directions. Base gives one:

    F32.bits : F32 -> U32

and nothing going back. `U32.to_f32` is a *numeric conversion* (3 becomes
3.0), not a reinterpretation, so a packed lane can be written and never read.
That is the whole argument; no `U32 -> F32` bit cast exists to build on.

This costs nothing, because `Array<F32>` is already the flat block the lane
wanted. `lay_arr` in `bend2/comp.ts:1569`:

```ts
return { arr: lay.ks.some((k) => k !== "w32"), lgs: ... };
```

An element whose layout is the single kind `w32` — which `F32` is — sets
`arr` **false**, and a non-`arr` block is never walked as `Term`s. Reads and
writes go through `blk_ptr`, which is one cast and one index:

```c
INLINE DEV u32a* blk_ptr(Corpus H, Loc loc, u32 i) {
  return (DEV u32a*)(H + loc) + i;
}
```

So `Array<F32>` *is* one contiguous machine block of 32-bit words. There was
nothing to build. (`Array<F64>` is the one to keep away from — see
`docs/omen/f64-drop-c-backend.md`.)

## 2. The views

```bend
type Ten  is Type:  Ten{n: U32, depth: Nat, xs: Array<F32>}
type View is Data:  View{off: U32, rows: U32, cols: U32, stride: U32}
```

`Ten` is kind `Type` because it holds an `Array`: one owner, linear, every
write in place. `View` is kind `Data`: four `U32`s, **no cell of any kind**,
so it forks, copies and drops freely and the affine discipline never has to
mention it. The strongest statement this lane can make about "a view does not
copy" is not a measurement — it is that a `View` has nowhere to put a copy.

One addressing rule covers everything the kernels need:

    (r, c)  |->  off + r * stride + c

A contiguous run is `rows = 1` (`vec`), a matrix column is `cols = 1`
(`col`), a matrix is itself (`mat`); `row` and `col` are two adds and a
multiply on the descriptor and touch no memory.

`tests/tensor/views.bend` measures the part a type cannot: that a view really
is a window on the owner's live bytes. `map` is run with `src = vec(0, 4)`
into `dst = vec(2, 4)`, which **overlap** in cells 2 and 3, over a block
holding 1..8:

| | cell 4 |
|---|---|
| a view that aliases the owner | **4** — `src[2]` is `dst[2]`, already written this walk |
| a view that had copied its source | 6 |

It reads 4, on all four lanes, and the `alias` line reads that same cell
through a view constructed *before* `map` ran. The owner's size is 16 before
a thousand views are taken and 16 after.

## 3. The numbers

`bash demos/tensor/bench.sh`. POWER.md protocol: one bench at a time under
`/tmp/bend-bench.lock`, every row timed only after C, one thread and sixteen
print the **same four lines**, medians of three, load recorded. 1024x1024
matrix, 256 rounds of `y <- A x` then `x <- 9y/64`, one 2^21-cell block
holding A, x and y; 268,435,456 multiply-adds per run.

    load 4.12 3.55 4.32   clang 21.1.7   AMD Ryzen 7 7700X @ 5.19 GHz
    bench           C  bend-1T  bend-16T    1T/C  1T/16T
    gemv        0.154    0.158     0.162   1.02x   0.97x
    split       0.155    0.161     0.161   1.04x   0.99x
    blocked     0.041    0.109     0.106   2.63x   1.03x

Three separate harness invocations gave 1.02-1.03x, 1.02-1.04x and
2.63-2.64x. **The machine was not quiet** — another lane's `bun` and
`clang-21` were resident throughout (load average 3.1 to 4.2 on 16 hardware
threads). The rows are single-threaded and the spread across invocations is
under 2%, but this is a shared mini and the numbers are reported as such.

`1T/16T` near 1.00 is not a defect: the kernel is a fold over rows with in-place
writes into one owner, which forks nowhere, so there is nothing for the other
fifteen threads to take.

**Against the 1.1x baseline the acceptance asked to beat: 1.02x. The bar is
met.** What the acceptance did not ask, and what matters more:

| row | per element | what it says |
|---|---|---|
| C, serial | 2.98 cycles | Zen 4's `addss` latency is **3** |
| Bend, serial | 3.05 cycles | the same chain, plus 2% |
| C, blocked | 0.79 cycles | the chain broken, loads widened |
| Bend, blocked | 2.11 cycles | the chain broken, loads **not** widened |

The serial row is not memory-bound and cannot be. A dependent chain of F32
adds runs at one add-latency per element whatever the layout, which here is
1.74 G elements/s — about **7 GB/s**, a sixth of what this box's DRAM will
give and a small fraction of what L3 will. The 1.02x is a tie at a floor both
sides are pinned to.

`split` is the control that settles the lane's premise: the same arithmetic in
the same order over **three separate `Array<F32>` owners**, A, x and y each in
its own block. It measures 1.02-1.04x — *the same as flat views*. The
marshalling difference is real and visible in the emitted C (the flat dot's
inner spin pushes **2** words, `o[0]` the `Array` term and `o[1]` the F32
accumulator; the two-owner L2 accumulator step of `power/knn.bend`, `spin_45`
in its emitted C, pushes **9** and takes eleven register parameters), but at one
add-latency per element there are ~3 cycles of shadow per element for it to
hide in, and it hides completely. Layout was not the residual margin here.

## 4. Vectorization — what clang actually did

Asked honestly, because the answer is not the flattering one.

**The serial row: neither side vectorizes.** The C twin's hot loop is
`mulss`/`addss` unrolled four deep with a serial chain
`xmm1 -> xmm2 -> xmm3 -> xmm4 -> xmm1`. Bend's is the same shape unrolled two
deep. clang says why, of its own accord, on both:

    loop not vectorized: cannot prove it is safe to reorder floating-point
    operations

A row sum written as one accumulator *is* its summation order, and strict IEEE
forbids reassociating it. Nothing about Bend is at fault here and nothing
about a layout can fix it.

**The elementwise `map`, where widening is legal: C widens, Bend does not.**
The twin's `scale` is four `movups` into four `mulps`. The whole Bend binary
for the same bench contains **zero** packed float instructions. clang's reason,
pointed at `blk_ptr`:

    bg.c:1078:31: remark: loop not vectorized: cannot identify array bounds

(The obvious suspect is wrong and was checked: `blk_at`'s wrap-around mask,
`(i & ((1 << (cls - lgs)) - 1)) << lgs`, does **not** defeat the vectorizer.
The same masked subscript written over a plain `float*` widens to `mulps`
without complaint. It is the `(u32a*)(H + loc) + i` cast — a `may_alias` u32
pointer manufactured from a `u64*` base — that leaves clang unable to bound
the object being walked.)

**The blocked row, which breaks the chain on both sides: the arithmetic
widens on both, the loads widen only for C.** `bench_blocked.bend` keeps four
accumulators, lane `c` into `s[c mod 4]`, and finishes `(s0+s1)+(s2+s3)`; the
twin does the identical thing, and the two still agree bit for bit. C's inner
loop becomes

```asm
movups (%rdx,%r8,4),%xmm3          ; four of A, one load
movups 0x400010(%rdi,%r8,4),%xmm5  ; four of x, one load
mulps  %xmm3,%xmm5
addps  %xmm2,%xmm5
```

Bend's becomes

```asm
movss  (%rcx,%r10,4),%xmm2         ; one element
movss  (%rcx,%rbp,4),%xmm3         ; one element
unpcklps %xmm2,%xmm3               ; stitch two into a vector
movss  (%rcx,%rdx,4),%xmm2
movss  (%rcx,%r9,4),%xmm4
unpcklps %xmm2,%xmm4
mulps  %xmm3,%xmm4
addps  %xmm4,%xmm0
```

Both are `mulps`/`addps`. Only one of them *loads* four at a time. Bend pays
four `movss`, four `lea`, four `and` and two `unpcklps` per vector where C
pays one `movups` — which is the whole of the 2.63x, and is exactly the
"cannot identify array bounds" remark showing up as instructions.

So the lane's flat block is genuinely contiguous, and clang can be made to
vectorise the arithmetic over it, but it will not widen a load through
`blk_ptr`.

## 5. A bench that measured nothing, and the probe that caught it

Worth recording because it fired. The first draft scaled by 1/16 each round.
A's spectral radius here is about 6.9, so the vector decayed by 0.43x per
round and was **identically zero by round 144** — at 256 rounds the bench was
timing multiplications by zero, and C, Bend on one thread and Bend on sixteen
all agreed perfectly on a checksum of 0.

Per POWER.md, agreement across backends proves the backends match and nothing
else. Every row therefore prints four lines, not one: the checksum, and `or`,
`and` and a non-finite fold over the same 1024 result words. `bench.sh` fails
a row when `or == and` (all 1024 words one value) or when the non-finite fold
is nonzero, *before* it times anything. The scale is now 9/64, which holds the
mean magnitude inside [0.83, 9116] across all 256 rounds — no denormals, no
infinities.

## 6. What remains for a decode loop

The next gap is **not** softmax, and it is not layout. In order:

1. **Widening the loads through `blk_ptr`** (`bend2/comp.ts`). This is the
   measured 2.63x and the only item here with a number attached. The blocked
   row proves the arithmetic vectorizes fine once the chain is broken; what
   stays scalar is the load, for a reason clang states in one line. A
   `__restrict` on the block base, or a helper that hands the vectorizer a
   bounded `float*` for a run of cells, is the shape of the fix. Compiler
   work, not userland.
2. **A reduction that is allowed to go fast.** A library gemv should sum a row
   with several accumulators, not one, and say so — the serial form costs 3.8x
   on the C side alone. This is an API decision (a `dot` whose summation order
   is blocked and documented) before it is a performance one.
3. **Threads.** `1T/16T` is 1.00 because the row fold forks nowhere. A gemv
   over rows is embarrassingly parallel and nothing in the view design
   prevents splitting it; it was not attempted in this lane.
4. Only then the nonlinearities.

## 7. Reproducing

```sh
bash demos/tensor/run.sh     # 10 / 10: check, interpret, js, c, c-1thread
bash demos/tensor/bench.sh   # the table above, under the bench lock
bun gates/repo.ts            # PASS: 55 / 55
```
