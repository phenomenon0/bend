# WGSL: the flat-kernel lane (`bend -o x.wgsl`)

A WGSL emitter and a WebGPU host runtime for the part of Bend that fits a GPU
kernel with no heap: scalar defs, folds, flat tail loops, fork trees under a
bang (`guide/SHADERS.md`'s shape), cubes and maps. This is the backbone, not an
inference engine: it holds no model, matrix or attention kernels.

**Status.** On the fork's `main` it builds against the fork's `comp.ts`. On the
`wgsl-flat-emitter-canon` branch it builds against clean `bendlang/bend` `main`
(5e70819) through `bend2/wgsl/canon-compat.ts`, and its four tests run on the
GPU (`tests/wgsl/run.mjs`, Deno WebGPU); see `INTEGRATION.md` (INTEGRATION-2).
`F64` programs are out of scope there. The upstream policy
(`WONTFIX.txt`: Metal and CUDA only) is why this lives on a fork.

## Files

| file | role |
|---|---|
| `bend2/wgsl.ts` | the emitter: terms to a `.wgsl` module plus a manifest (`bend-wgsl/2`) |
| `bend2/webgpu.js` | the host runtime: `gpu_open`, `pipes`, `entry_run`, `fork_run`, `cube_pipe`, `cube_run` |
| `bend2/webgpu_probe.js` | load-time self-test (`gpu_selftest`): 1008 cases through the emitted arithmetic |
| `bend2/x32a.ts` | integer IEEE binary32 add, subtract, multiply (subnormal-exact) |
| `bend2/x32w.ts` | integer `exp sin cos pow softplus div sqrt`; **generated**, never edit |
| `bend2/x32/` | generator for `x32w.ts`: `node bend2/x32/build.mjs` (sources, `x32.h` tables) |
| `bend2/wgsl/canon-compat.ts` | canon branch only: the shim `wgsl.ts` reads the compiler through |
| `tests/wgsl/run.mjs` | emits and runs the four tests on the GPU (`deno run --unstable-webgpu -A`) |
| `tests/wgsl/` | four programs with their expected output (`#|` lines; `cubes.expected`) |

## What it takes in

Defs over `F32 / U32 / Bool / Nat` words, plus `Bytes` buffers:

- scalar defs, `match` on Bool and Nat, word reinterprets;
- a **fold** (one self call on the Nat predecessor) or a flat tail **spin** loop;
- a recursion on a Nat that a call gives as a **literal** is unrolled, one WGSL
  fn per (def, literal), since WGSL has no recursion;
- **entries**, which the host dispatches; the first line of the `.wgsl` is the
  manifest listing them:
  - a fork tree: `f(d, xs)`, one lane a leaf, joins as the perfect tree over lanes;
  - a cube: `cube.<name>.{n,leaf,join,fin,out,len,pad,bind}`, a workgroup a row, n up to 2^20;
  - a map: `map.<name>.{f,len,rowlen,bind}`, one invocation an element.

Outside the envelope the emitter dies naming the construct: F64, heap data
(lists, trees, strings, arrays), closures, IO, general recursion on a Nat that
is not a literal. Those programs keep the C and JS lanes. A Nat is a u32 that
flags overflow: the run answers "past the envelope", never a wrong number.

## Two findings worth keeping

**The GPU fuses `a*b+c`.** The device compiler contracts to fma, reassociates
sums of more than a few terms, and loses the sign of a zero product. On one
adapter 9110 of 65536 random `a*b+c` tuples differed from the C lane without a
barrier. The emitter writes f32 `+ - *` as calls the compiler cannot see through
(`fma(1,a,b)`, `fma(-1,b,a)`, `bmul` = `fma(a,b,-0.0)` plus a zero-sign select),
and later versions as the integer forms in `x32a.ts`. *Measured on one Apple
GPU (M3 Ultra, Chrome 154 and Safari 27); other vendors may fuse differently or
not at all.* That is why `webgpu_probe.js` exists: run it on the adapter you
get before trusting a result. It is a bounded probe, not a certification.

**GPUs flush subnormals.** Hardware `fma` flushes subnormal operands and
results. `x32a.ts` does add, subtract and multiply in u32/i32 so subnormals,
signed zeros and rounding survive.

## The exact-math layer

`x32w.ts` computes `(f32)fn((f64)x)` for exp, sin, cos, pow and softplus, and
IEEE `/` and `sqrt` (Apple's GPU misses by one ulp on both), in integers.
Gate, recorded in the originating tree (not in this package): every one of the
2^32 inputs per function, in Chrome and Safari, 0 wrong; pow and div by 2^32
random pairs and a stratified 3.76e10 set; a negative control that flips one
bit is caught. **The reference is one Mac's libm** (`-ffp-contract=off`), so
"exact" means "equal to that libm on that gate", not a proof. softplus on a
signalling NaN gives 88.0 in WGSL and NaN from clang -O3 (recorded).

## Runtime notes

- WebKit exposes no `subgroups`; the emitted kernels use none, so they run in
  Safari. (Chrome-only subgroup trees were studied separately and are not here.)
- `entry_run` allocates, submits, maps and destroys per call. Fine for a gate,
  slow for a loop; there is no dispatch-graph recorder in this package.
- `webgpu.js` has no unit tests of its own; the four programs in `tests/wgsl/`
  and the probe exercise it.

## Scope, honestly

Flat kernels only; no term runtime. The limits are the ones in the `wgsl.ts`
header plus `DEVIATIONS.md`. Not tested on any GPU vendor but Apple. I did not
re-run the browser gates when assembling this branch (see `PACKAGE.md`
outside the tree for what was and was not run).
