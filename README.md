# bend-f64 — a fork of bendlang/bend with first-class F64

A working tree of the Bend 2.0.4 compiler (`bend2/` + `guide/`, byte-identical
to the shipped release at `82cb989`) with 64-bit floats added: the type, its
laws, literals, all three lanes (interpreter, native C, CUDA device) and
conversions — ~3k tokens of new language surface, built to the conventions of
the upstream repo (see `MANUAL.md`, distilled from `github.com/bendlang/bend`;
raw reference checkout at `~/Documents/Project/bend-upstream`).

## Layout

```
bend2/            the compiler (base.bend, bend.ts, comp.ts, main.ts, effs/)
guide/            GUIDE.md
tests/f64/        the upstream-shaped tests: every file ends in its `#|` lines
tests/run.sh      the four lanes, reduced to one machine (check+interpret, JS, C, GPU)
tests/caps.sh     the ttok ledger against the caps this patch lands with
tests/codex/      161-case adversarial suite with an independent Python oracle
tests/f64 + codex run on every lane; codex pins two C-lane read parity quirks
docs: SPEC.md     the design (file-by-file) · MANUAL.md · study/ (browsable)
study/index.html  the browsable study of the upstream standards
```

## Use

```
bun bend2/main.ts prog.bend            # check + interpret
bun bend2/main.ts prog.bend -o prog    # native build (clang); prog.gpu rides beside
./prog --threads 16                    # CPU parallel;  ./prog --gpu 4GB  for !
./prog --gpu 4GB                       # the CUDA lane (RTX 3090: FP64 is 1/64 rate)
```

```bend
import Base

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(F64.show(F64.add(0.1d, 0.2d)))   # 0.30000000000000004
    IO.print(F64.show(F64.pi()))              # 3.141592653589793

#|0.30000000000000004
#|3.141592653589793
```

Literals: `2d`, `1.5d`, `1.5e3d`, `1e-6d` (the `d` suffix; the F32 grammar is
untouched). Conversions: `U32.to_f64`, `F64.to_u32`, `F32.to_f64` (exact
widening), `F64.to_f32`, `F64.from_nat`, `F64.to_nat`. `F64.bits` returns
`Nat` — bit patterns past the Nat immediate (2^48-1) are a documented boundary.

## Status

Green: `tests/run.sh` (all four lanes, identical output everywhere; GPU receipt:
100% utilization on the 3090 during the F64 device run), `tests/caps.sh`
(24,968/40,399/62,244 tok against the landing caps 25k/41k/63k), and the
161-case adversarial suite (`tests/codex/run.sh`). F32 behavior byte-identical
to the stock compiler (regression-checked). Metal note: Apple GPUs have no
fp64, so F64 is a host + CUDA type by construction (guarded; F32-only programs
compile for Metal unchanged — fable review finding, fixed). Quirks and
non-goals: see `MANUAL.md` §7.

## Landing notes (upstream shape)

- Caps: `gates/repo.ts` would take `base.bend 25000`, `comp.ts 63000` with this
  patch (measured; `tests/caps.sh`).
- Tests: `tests/f64/` files are already in the `#|` convention for upstream.
- `bend.ts` is the human-written core — changes there (the literal grammar
  line included) are for Victor's hand, per AGENTS.md; everything else is
  built for delegation.
