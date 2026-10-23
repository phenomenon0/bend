# bend2 — core-language snapshot

Pinned compiler snapshot `240ecef4` (content record; the commit object no longer exists in any
local clone or on any remote). Published so the language work is readable and cloneable.

What this tree has, verified by inspection:

- Native 64-bit lowering in the C emitter: `tpl_w64("u64_")`, `tpl_ops("u64_", …)`, `u64_cmp`,
  `i64_` over `(int64_t)`, `typedef uint64_t u64` (`bend2/comp.ts`).
- `type U64 is Data: U64{data: Word(64n)}` (base.bend:2545) and `type I64` (:2662).
- `type F64 is Data: F64{data: Word(64n)}` (base.bend:60) — **type only**: the API is
  clamp/from_nat/hypot/lerp/max/min/pi/pick/round/square/to_nat. No add/sub/mul/div, no
  sqrt/fma, no comparisons, no U64 bit-casts, so no IEEE round-to-nearest semantics yet.
- Arrays: `Array.get/set/swap/new/size/clone/fork/map/join/get4/to_list`, in-place via the
  linear `Array.set.fin`.
- Streaming IO: `File.fold_text` folds over a `Utf8.Dec` with explicit eof handling.

Not in this tree: any proof layer for F64 facts (`law` checks are runtime, not proofs).

Upstream `bendlang/bend@main` has neither `F64` nor `U64`; `phenomenon0/bend@main` likewise.
This snapshot is the only tree carrying the native 64-bit lowering.
