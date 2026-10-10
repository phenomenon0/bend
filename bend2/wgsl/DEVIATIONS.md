# Where this package departs from the repo's style

1. **One 1,364-line file.** `wgsl.ts` holds defs, entries and runtime text.
   The entry emitters could split into `wgsl_entries.ts`.
2. **Module-level mutable state.** `FOLD`, `SPIN`, `MODES`, `INSTS`, `QUEUE`,
   `BUFS`, `SCAT`, `TRIAL`, reset in `wgsl_book`. `comp.ts` keeps such state on
   `File`; moving it there is a `comp.ts` edit (which has a size cap).
3. **Trial emission by truncation.** `mode_of` tries fold, then spin, else
   rec, and discards the lines of a failed try by truncating `fl.seg.lines`.
4. **Entries are found by def name** (`cube.<name>.*`, `map.<name>.*`), with
   reserved parameter names `row`, `i`, `col`, `s`, and a `bind` String-literal
   def. An annotation would be the upstream-shaped alternative.
5. **A generated file is checked in.** `x32w.ts` comes from `bend2/x32/`;
   inlining the sources as template strings would remove it.
6. **It does not fit the repo gate.** `gates/repo.ts` allow-lists every file and
   caps `comp.ts` and `main.ts`; none of these files are on the list.
7. **JS, not TS, for the host runtime** (`webgpu.js`, `webgpu_probe.js`), as the
   effect sources under `bend2/effs/` are.
8. **No per-file license header.** Canon source files carry none; `LICENSE`
   (Apache-2.0) covers the repo, so none was added here either.
