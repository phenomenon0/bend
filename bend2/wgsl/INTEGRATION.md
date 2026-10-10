# Integration with canon's `comp.ts` / `main.ts`

> **Status on `wgsl-flat-emitter-canon`: builds and passes against canon `main`
> (5e70819). See INTEGRATION-2 at the end. §1-§4 below are the analysis that
> led to it, kept as written for the fork tree.**

Honest result first: **this does not compile against `bendlang/bend` `main`
(5e70819, 2026-10-09) unchanged.** An earlier estimate that the emitter "touches
`comp.ts` very little" holds for *edits*, not for *surface*: it reads about 36
`comp.ts` names, and canon exports five functions from `comp.ts`.

## 1. Names `wgsl.ts` takes from `comp.ts` (`import * as C`)

Counts are uses in `wgsl.ts`. "private" = defined in canon's `comp.ts` but not
exported (an `export` keyword away). "absent" = not in canon's `comp.ts`.

| name | uses | canon |
|---|---|---|
| `file_push` | 22 | private (comp.ts:1493) |
| `block` | 9 | private (comp.ts:1497) |
| `term_strip` | 6 | private (comp.ts:640) |
| `sig_def` | 6 | **absent** |
| `call_kind` | 6 | **absent** |
| `eff_name` | 5 | **absent** |
| `ty_peel` | 4 | private (comp.ts:844) |
| `ty_all` | 4 | private (comp.ts:840) |
| `quant_live` | 4 | private (comp.ts:802) |
| `name_local` | 4 | private (comp.ts:543) |
| `adt_of` | 4 | private (comp.ts:858) |
| `term_spine` | 2 | private (comp.ts:664) |
| `term_kids` | 2 | private (comp.ts:716) |
| `mat_head` | 2 | private (comp.ts:1089) |
| `mat_ctrs` | 2 | private (comp.ts:1167) |
| `HLet` | 2 | **absent** |
| `file_new` | 2 | private (comp.ts:1325) |
| `emit_nats` | 2 | **absent** |
| `ctr_adt` | 2 | private (comp.ts:1013) |
| `carb_book` | 2 | **absent** |
| `tpl` | 1 | private (comp.ts:583) |
| `Of` | 1 | private (comp.ts:107) |
| `Name` | 1 | private (comp.ts:52) |
| `memo_gc` | 1 | private (comp.ts:1873) |
| `let_live` | 1 | private (comp.ts:658) |
| `intr_of` | 1 | private (comp.ts:809) |
| `HTerm` | 1 | private (comp.ts:50) |
| `File` | 1 | private (comp.ts:54) |
| `DUMMY` | 1 | private (comp.ts:529) |
| `die` | 1 | private (comp.ts:1858) |
| `def_foreign` | 1 | private (comp.ts:1233) |
| `Def` | 1 | **absent** |
| `ctr_flds` | 1 | private (comp.ts:1039) |
| `CMPS` | 1 | private (comp.ts:173) |
| `Carb` | 1 | **absent** |
| `call_eta` | 1 | private (comp.ts:706) |

Canon's only exports from `comp.ts`: `io_type`, `io_run`, `compile_book`,
`js_lib`, `js_book`. From `bend.ts` the emitter uses `Book`, `Var`, `ctx_nil`,
`tele_fill`, all exported in canon. `bend.ts` is not edited.

The eight **absent** names (`sig_def`, `call_kind`, `eff_name`, `HLet`,
`emit_nats`, `carb_book`, `Def`, `Carb`) belong to the compiler this package was
written against and have no canon counterpart in `comp.ts`; each needs a port,
not an `export`. The rest need only `export`, but `gates/repo.ts` caps
`comp.ts` at 64k ttok and the signatures were not re-checked against canon's.

## 2. Language features the emitter assumes

Not in canon's `base.bend` / `comp.ts`: the `Bytes` type with `Bytes.get` and
`Bytes.word_le`, the `F64` type (`F64.exp`, `F64.to_f32`, `F32.to_f64`, used by
the x32 chain recognition), and the `f32_is_ne` intrinsic. In canon,
`tests/wgsl/spin_collatz.bend` and `spec_tree.bend` run and print the expected
values; `bytes_hash.bend` and `cubes.bend` fail to check (`Bytes` is not a
defined name). Their expected output comes from the fork compiler this code was
developed on.

## 3. `main.ts`

A `-o x.wgsl` output would need `main.ts` to call `wgsl_book(book)` (the
exported entry in `wgsl.ts`) and write the file. That is the whole CLI surface;
`main.ts` has a 16k ttok cap.

## 4. What a port is

Re-export or re-implement the §1 names, add `Bytes`/`F64` or drop those
features from the emitter, wire `-o x.wgsl`, and either add the files to
`gates/repo.ts` or keep them on a fork. None of this is done here; this
branch ships the emitter as it works on its source compiler.

# INTEGRATION-2: the canon branch (`wgsl-flat-emitter-canon`)

Base: `bendlang/bend` `main` 5e70819. `comp.ts` is **not edited** (it sits 95
ttok under its 64k cap).

**Shim.** `bend2/wgsl/canon-compat.ts` is what `wgsl.ts` imports as `C`. It
loads a copy of `comp.ts`'s text with one `export` line and two small functions
appended (`file_open`, `file_srcs`, because `FL` is a module `let`), written to
the temp dir by content hash, and importing this repo's `bend.ts`. The old API
took the file/book as arguments; canon keeps it in module state `FL`, so the
shim's wrappers drop that argument. `emit_nats` is rebuilt from the Nat loop in
canon's `mat_rows`; `carb_book` raises each live def through `fun_of` so `.n`
and `.h` are what the old `def_body` gave. `term_spine`/`call_kind` map canon's
`Spine` to the old `{k,args,all,bang}` call.

**Bytes: implemented.** In pure Bend in `base.bend` (a `Bytes` is a `String`
of Chars < 256): `Bytes`, `Bytes.byte`, `Bytes.get`, `Bytes.push`,
`Bytes.word_le`. The host run gives the fork's values. The emitter still reads
`Bytes.get`/`Bytes.word_le` **by name** as buffer reads (the shim's `intr_of`
answers `{JS:""}` for them so canon's checker/emit paths treat them as
operations).

**F64: out of scope.** canon's `base.bend` has no `F64`. The emitter's F64
chain recognition (`F64.to_f32 (F64.exp (F32.to_f64 x))` and siblings -> the x32
integer forms) is therefore unreachable in canon: such a program cannot be
written. The x32 generator and `x32w.ts` ship unchanged and are exercised by
`gpu_selftest` (1008/1008 exact on the 3090). Adding `F64` to canon is a
language decision, not an adapter job.

**Other edits.** `main.ts`: `-o x.wgsl` calls `wgsl_book` (a few lines).
`wgsl.ts`: `import ... C from "./wgsl/canon-compat.ts"`, plus a
`return T();` after a spin loop (Deno/naga rejects a function whose loop has no
break and no trailing return; the fork tree only saw Chrome/tint).

**Limits.** `-o x.wgsl` needs the source tree (`bun bend2/main.ts`); the shim
reads `comp.ts` text at runtime, so it will not work from a compiled binary.
`gates/repo.ts` fails 19 of 54 on files not in its allow list (the new ones);
no cap failed. Adding allow lines is Taelin's call, so none were added.

**Receipts** (canon 5e70819 + this branch, RTX 3090 via Deno WebGPU):
`deno run --unstable-webgpu -A tests/wgsl/run.mjs` ->
`spin_collatz 61317`, `spec_tree 512271840`, `bytes_hash 913564336`, cubes 1345
words bit-equal to `cubes.expected`. Host (`bun bend2/main.ts`) prints the same.
A browser run of `webgpu.js` was not done.
