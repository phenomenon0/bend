# SPEC — F64 for Bend 2.0.4 (fork at ~/Documents/Project/bend-f64)

Goal: first-class 64-bit float `F64` in the local Bend toolchain — type, laws,
literals, all three lanes (JS interpreter, native C, CUDA device), conversions,
show/read — without touching the checker core (it is width-agnostic).

Baseline: commit `82cb989` ("baseline: Bend 2.0.4 toolchain as shipped").
Dev run: `bun ~/Documents/Project/bend-f64/bend2/main.ts <file.bend> [...]`.
The installed `~/.bend` 2.0.4 stays untouched.

## 0. Design decisions

- `F64{data: Word(64n)}` mirrors `F32{data: Word(32n)}` exactly (Data type,
  one word field). Represented in-word; C cell = the double's 8 bytes as u64.
- Lane mapping: `WORDS` table gains `F64: W64` (same lane class as `Nat`).
- Op names auto-derive: `F64.add` → `f64_add` via `eff_name` (lowercase,
  `.`→`_`). No naming work needed beyond adding table rows.
- Literals: `1.5d`, `2d`, `1.5e3d` → F64 (suffix `d`). Old forms unchanged:
  bare = U32, `n` = Nat, plain decimal = F32.
- New conversions: `U32.to_f64` (law), `F32.to_f64`, `F64.to_f32` (laws);
  defs `F64.from_nat`, `F64.to_nat` mirror F32's.
- No changes to: checker/termination/proofs, `bend.ts` type machinery,
  parser beyond the numeric literal, main.ts, WORDS consumers.
- `F64.bits` returns **Nat** (F32.bits returns U32; there is no U64 type).
  Caveat: bit patterns above 2^48-1 trigger the Nat immediate check at
  runtime (`nat_chk`); normal numbers have exponent < 2^11 so the top 16
  bits are small; values with exponent+sign bits high are fine in practice,
  documented in README. (Edge: NaNs with payload could trip it; acceptable
  for v0.1, noted.)
- CUDA: `double` is a first-class device type; math funcs overload for
  double in device code; the Metal-only `precise::` SHIMS are not touched.
  Perf caveat (3090 FP64 ≈ 1/64 FP32) documented, not engineered around.

## 1. `bend2/base.bend` (+~230 lines)

1a. After `type F32` (line ~58):
```
type F64 is Data:
  F64{data: Word(64n)}
```

1b. Next to `law U32.to_f32` (line ~1449), add:
```
law U32.to_f64:
  for a: U32
  F64
```

1c. After the F32 section (after `def F32.to_nat`, line ~1638), add the F64
section, mirroring 1:1 (laws then defs):

Laws (copy F32 block, s/F32/F64/):
  to_u32, add, sub, mul, div, mod, pow, atan2, neg, abs, sqrt, exp, log,
  log2, log10, sin, cos, tan, asin, acos, atan, sinh, cosh, tanh, floor,
  ceil, trunc, is_eq, is_ne, is_lt, is_le, is_gt, is_ge, show (+a),
  bits (ret Nat), read (Maybe<&2, F64>)

New cross laws (place beside F32/F64):
```
law F32.to_f64:
  for a: F32
  F64

law F64.to_f32:
  for a: F64
  F32
```

Defs (mirror F32.min/max/clamp/lerp/square/hypot/round/pi):
```
def F64.min(+a: F64, +b: F64) -> F64: Bool.pick(F64, F64.is_lt(a, b), a, b)
def F64.max(+a: F64, +b: F64) -> F64: Bool.pick(F64, F64.is_lt(a, b), b, a)
def F64.clamp(x: F64, lo: F64, hi: F64) -> F64: F64.min(F64.max(x, lo), hi)
def F64.lerp(+a: F64, b: F64, t: F64) -> F64: F64.add(a, F64.mul(F64.sub(b, a), t))
def F64.square(+a: F64) -> F64: F64.mul(a, a)
def F64.hypot(+x: F64, +y: F64) -> F64: F64.sqrt(F64.add(F64.mul(x, x), F64.mul(y, y)))
def F64.round(a: F64) -> F64: F64.floor(F64.add(a, 0.5))   # NOTE: 0.5 is F32!
def F64.pi() -> F64: <literal — see 3; write 3.141592653589793d once parser lands>
def F64.from_nat(n: Nat) -> F64: U32.to_f64(U32.from_nat(n))
def F64.to_nat(a: F64) -> Nat: U32.to_nat(F64.to_u32(a))
```
`F64.round` uses `F64.add(a, 0.5d)`; `F64.pi` needs the parser change, so land
it last (or temporarily via from bits: `F64.read("3.141592653589793")`).

## 2. `bend2/comp.ts` (+~180 lines)

2a. `WORDS` (line 161): add `F64: W64`.

2b. `OPERATIONS` after the f32 block (ends line ~253), mirror with C/JS:

- binops tpl: `f64_rewrap(f64_unbox($0) $o f64_unbox($1))` /
  JS `($0 $o $1)`        [add sub mul div]  ← JS has no fround: doubles native
- `f64_neg`: C `f64_rewrap(-f64_unbox($0))` / JS `(-$0)`
- CMPS tpl: C `((u64)(f64_unbox($0) $o f64_unbox($1)))` / JS `($0 $o $1)`
- math tpl (`sqrt exp log log2 log10 sin cos tan asin acos atan sinh cosh
  tanh floor ceil trunc abs:fabs:abs`):
  C `f64_rewrap((double)$o(f64_unbox($0)))` / JS `Math.$o($0)`  ← no fround
- `f64_pow`/`f64_atan2`: C `f64_rewrap((double)$o(f64_unbox($0), f64_unbox($1)))`
  / JS `Math.$o($0, $1)`
- `f64_mod`: C `f64_rewrap(fmod(f64_unbox($0), f64_unbox($1)))` / JS `($0 % $1)`
- `f64_to_u32`: C `f64_to_u32($0)` / JS `($0 >= 1 && $0 < 4294967296 ?
  Math.floor($0) : 0)`
- `f64_bits`: C `$0` / JS `f64_bits($0)` (returns BigInt)
- `f64_show`: C `f64_show(e, $0)` call:true / JS `f64_show($0)`
- `f64_read`: C `f64_read(e, $0)` call:true / JS `f64_read($0)`
- `u32_to_f64`: C `f64_rewrap((double)(u32)($0))` / JS `($0)`
- `f32_to_f64`: C `f64_rewrap((double)f32_unbox($0))` / JS `($0)`
- `f64_to_f32`: C `f32_rewrap((f32)f64_unbox($0))` / JS `Math.fround($0)`

2c. NATIVE C slab (after `f32_to_u32`, line ~430):
```
INLINE f64 f64_unbox(u64 x) { union { u64 u; f64 f; } p = { x }; return p.f; }
INLINE u64 f64_rewrap(f64 x) { union { f64 f; u64 u; } p = { x }; return p.u; }
INLINE U32 f64_to_u32(U32 a) {
  f64 v = f64_unbox(a);
  return v >= 0.0 && v < 4294967296.0 ? (u32)v : 0;
}
```
(Note: `f64` must be defined — add `typedef double f64;` near the typedefs if
absent; search for existing `typedef` of u64/u32 first.)

2d. IO C slab: DEVICE guard mirror + full impls:
```
#define f64_show(e, x) (err_post(e.mem, ERR_FIDS), 0)
#define f64_read(e, s) (err_post(e.mem, ERR_FIDS), 0)
...
static int f64_text(char* buf, f64 v) { ... mirror f32_text with %.*e p<=17,
  strtod roundtrip, exponent formatting identical ... }
static Term f64_show(...) { char buf[40]; io_str(e, buf, f64_text(buf, f64_unbox(x))); }
static Term f64_read(...) { strtod; io_box CID_SOME f64_rewrap(v) ... }
```
(Bump buf sizes: 40 is fine for doubles with %.17e.)

2e. JS slab (after f32 helpers ~line 565): word_to_u64(BigInt), u64_to_word,
f64_bits (DataView8→BigInt), f64_from_bits (BigInt→number), f64_show
(17-iteration loop, no fround), f64_read (same regex, no fround).

2f. OPTIMIZED: after F32 entry (line ~350):
```
F64: {
  intr: { F64: "f64_from_bits(word_to_u64($0))" },
  elim: { F64: ["u64_to_word(f64_bits($0))"] },
},
```
(word_to_u64/u64_to_word here = the JS helpers from 2e.)

2g. Check `lay_of`/`emit_ctr` behavior for the F64 ctor: single word field of
64 bits — mirror of F32; verify by build, adjust only if the pack branch
behaves differently (the `vs[0].ws.length > 1` pack path should already
handle 2×32 words; if F64's Word(64n) field emits as one `w64` lane vs
32/64 bit-words, error messages will say).

## 3. `bend2/bend.ts` (+~45 lines)

3a. Helpers next to f32_to_bits (line ~1173):
```
const F64_VIEW = new DataView(new ArrayBuffer(8));
export function f64_to_bits(v: number): { hi: U32; lo: U32 } { ... }
export function word_to_term64(hi: U32, lo: U32, s?: Span): LTerm {
  let out: LTerm = Ctr("WNil", [], s);
  for (let i = 63; i >= 0; i--) {
    const bit = i >= 32 ? (hi >>> (i - 32)) & 1 : (lo >>> i) & 1;
    out = Ctr("WCon", [Ctr(bit ? "True" : "False", [], s), out], s);
  }
  return out;
}
```

3b. NUMBER (line 2208):
`const NUMBER = /(\d+)(n|d|\.\d+([eE][+-]?\d+)?d?)?/y;`
Branch in parse_term_num: `m[2] === "d" || m[2]?.endsWith("d")` → F64:
strip trailing `d`, `Number(...)` finite check (message: "a float literal
with a finite f64 value"), `Ctr("F64", [word_to_term64(hi, lo, spn)], spn)`.
Else existing F32 path.

## 4. Tests (`tests/` in bend-f64; also run from bend-experiments)

- `t_arith.bend` — known values: 0.1d+0.2d shows 0.30000000000000004;
  sqrt(2.0d), pi literal, neg/abs/mod, comparisons, clamp/lerp/round.
- `t_conv.bend` — U32.to_f64, F64.to_u32 (3.9d→3), F32.to_f64 precision
  widening (0.1 f32 → 0.10000000149011612), F64.to_f32 narrowing, from_nat.
- `t_show_read.bend` — show/read round-trips incl. subnormals (5e-324d),
  ±inf, nan, -0.
- `t_mc.bend` — Monte Carlo π 2^24 samples in F64; CPU + GPU; checksum.
- `t_mandel.bend` — 512² escape-count checksum in F64 (device double math).
- Lane matrix: JS (`bun main.ts t_x.bend`), native (`-o` + run), GPU where `!`.
- Accuracy: expected values computed independently in Python `float` (
  compare printed strings/ints).

## 5. Acceptance

1. All t_* green on JS lane AND native binary; GPU runs on the 3090 with
   nvidia-smi receipt for t_mc.
2. Existing suite (`bend-experiments` mcp/mandel CPU+GPU binaries rebuild and
   byte-identical checksums — no regression from WORDS/table additions).
3. `bend guide` untouched; `bend base F64` prints the new blocks (cli_base
   is generic — verify).
4. No changes required in checker/termination paths (they never see widths).
5. Commit series in bend-f64: `f64: base types+laws`, `f64: compiler lanes`,
   `f64: literals`, `f64: tests`, README+WORKLOG.

## 6. Risks / unknowns (resolve by build)

- R1: word-field packing of `Word(64n)` under `F64` ctor (emit_ctr 2209)
- R2: `%e` printf in device f64_text — device guards hide show/read, fine
- R3: NVRTC `double` default-arch sm_86 — fine on 3090
- R4: JS integer-word helpers need BigInt (word_to_u64) — implemented
- R5: numeric literal regex backtracking — extended pattern stays simple

## 7. Out of scope (v0.1)

- Metal double verification (no Apple GPU on omen; code paths mirrored only)
- Proofs for new laws (laws ship as axioms like F32's)
- F64 in Base's own UI/audio/Image APIs
- Upstreaming (fork-only today)
