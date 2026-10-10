# Cubes and a map, the row shape of a reduction (leaf, perfect tree of joins, finish, map)
# and an elementwise map, several to one module (bend-wgsl/2). The cube.<name>.* and map.<name>.* defs are the
# lane's entries; main is the native reference: the same defs, run as a recursive perfect tree over the lcg inputs.
#   ctr:   y = x - mean(x)            n 128, rows of 128
#   amax:  y = max |x|                n 256, one word a row
#   padsq: y = sqrt(sum x^2)          n 64, only 50 real leaves a row, the rest pad (0.0)
#   bdot:  y = row . x                n 32, the rows are raw bytes (unaligned f32 words), x shared
#   clamp: y = min(max(v, 0), hi) + i * 0.001      a map, hi a scalar
import Base

def f32_from_bits(w: U32) -> F32:
  match w:
    case U32{d}:
      F32{d}

def lcg(+s: U32) -> U32:
  ((s * 1664525 : U32) + 1013904223 : U32)

# the lane's input generator: 24 random bits in [-1, 1), exact in F32
def xval(+r: U32, +i: U32, +salt: U32) -> F32:
  +u = lcg(lcg(((r * 4099 : U32) + (i + salt : U32) : U32)))
  ((((U32.to_f32((u >> 8n : U32)) * f32_from_bits(864026624) : F32) * 2.0 : F32) - 1.0 : F32))

def pow2(d: Nat) -> Nat:
  match d:
    case 0n:
      1n
    case 1n+p:
      +h = pow2(p)
      Nat.add(h, h)

# ctr
def cube.ctr.n() -> U32:
  128

def cube.ctr.bind() -> String:
  "x=row"

def cube.ctr.leaf(+x: F32) -> F32:
  x

def cube.ctr.join(a: F32, b: F32) -> F32:
  (a + b : F32)

def cube.ctr.fin(t: F32) -> F32:
  (t / 128.0 : F32)

def cube.ctr.out(x: F32, s: F32) -> F32:
  (x - s : F32)

# amax
def cube.amax.n() -> U32:
  256

def cube.amax.leaf(+x: F32) -> F32:
  F32.abs(x)

def cube.amax.join(a: F32, b: F32) -> F32:
  F32.max(a, b)

def cube.amax.fin(t: F32) -> F32:
  t

# padsq
def cube.padsq.n() -> U32:
  64

def cube.padsq.len() -> U32:
  50

def cube.padsq.leaf(+x: F32) -> F32:
  (x * x : F32)

def cube.padsq.join(a: F32, b: F32) -> F32:
  (a + b : F32)

def cube.padsq.fin(t: F32) -> F32:
  F32.sqrt(t)

# bdot: row r's f32 words start at byte 136 r + 2
def cube.bdot.n() -> U32:
  32

def cube.bdot.bind() -> String:
  "x=shared"

def cube.bdot.leaf(row: U32, i: U32, +wb: Bytes(), +x: F32) -> F32:
  (f32_from_bits(Bytes.word_le(wb, U32.to_nat(((row * 136 : U32) + ((i * 4 : U32) + 2 : U32) : U32)))) * x : F32)

def cube.bdot.join(a: F32, b: F32) -> F32:
  (a + b : F32)

def cube.bdot.fin(t: F32) -> F32:
  t

# clamp
def map.clamp.bind() -> String:
  "hi=scalar"

def map.clamp.f(i: U32, v: F32, hi: F32) -> F32:
  (F32.min(F32.max(v, 0.0), hi) + (U32.to_f32(i) * 0.001 : F32) : F32)

# native reference: the defs as a recursive perfect tree
def red_ctr(d: Nat, +r: U32, +lo: U32) -> F32:
  match d:
    case 0n:
      cube.ctr.leaf(xval(r, lo, 1))
    case 1n++p:
      a b = red_ctr(p, r, lo) red_ctr(p, r, (lo + U32.from_nat(pow2(p)) : U32))
      cube.ctr.join(a, b)

def red_amax(d: Nat, +r: U32, +lo: U32) -> F32:
  match d:
    case 0n:
      cube.amax.leaf(xval(r, lo, 2))
    case 1n++p:
      a b = red_amax(p, r, lo) red_amax(p, r, (lo + U32.from_nat(pow2(p)) : U32))
      cube.amax.join(a, b)

def red_padsq(d: Nat, +r: U32, +lo: U32) -> F32:
  match d:
    case 0n:
      Bool.pick(F32, U32.is_lt(lo, 50), cube.padsq.leaf(xval(r, lo, 3)), 0.0)
    case 1n++p:
      a b = red_padsq(p, r, lo) red_padsq(p, r, (lo + U32.from_nat(pow2(p)) : U32))
      cube.padsq.join(a, b)

# the matrix as bytes: a row is [2 zero][32 f32 words][6 zero] = 136 bytes, word i of row r from xval(r, i, 4)
def put4(bs: Bytes(), +w: U32) -> Bytes():
  Bytes.push(Bytes.push(Bytes.push(Bytes.push(bs, U32.and(w, 255)), U32.and((w >> 8n : U32), 255)),
    U32.and((w >> 16n : U32), 255)), (w >> 24n : U32))

def zeros(k: Nat, bs: Bytes()) -> Bytes():
  match k:
    case 0n:
      bs
    case 1n+m:
      zeros(m, Bytes.push(bs, 0))

def words(k: Nat, +r: U32, +i: U32, bs: Bytes()) -> Bytes():
  match k:
    case 0n:
      bs
    case 1n+m:
      words(m, r, (i + 1 : U32), put4(bs, F32.bits(xval(r, i, 4))))

def rows_b(k: Nat, +r: U32, bs: Bytes()) -> Bytes():
  match k:
    case 0n:
      bs
    case 1n+m:
      rows_b(m, (r + 1 : U32), zeros(6n, words(32n, r, 0, zeros(2n, bs))))

def red_bdot(d: Nat, +r: U32, +lo: U32, +wb: Bytes()) -> F32:
  match d:
    case 0n:
      cube.bdot.leaf(r, lo, wb, xval(0, lo, 5))
    case 1n++p:
      a b = red_bdot(p, r, lo, wb) red_bdot(p, r, (lo + U32.from_nat(pow2(p)) : U32), wb)
      cube.bdot.join(a, b)

# one word a line (the F32 bits)
def show(+v: F32) -> IO(Unit):
  IO.print(U32.show(F32.bits(v)))

def p_ctr(k: Nat, +r: U32, +i: U32) -> IO(Unit):
  match k:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+m:
      do IO<Unit>:
        show(cube.ctr.out(xval(r, i, 1), cube.ctr.fin(red_ctr(7n, r, 0))))
        p_ctr(m, Bool.pick(U32, U32.is_eq(i, 127), (r + 1 : U32), r),
          Bool.pick(U32, U32.is_eq(i, 127), 0, (i + 1 : U32)))

def p_rows(k: Nat, +r: U32, +w: Bytes()) -> IO(Unit):
  match k:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+m:
      do IO<Unit>:
        show(cube.amax.fin(red_amax(8n, r, 0)))
        show(cube.padsq.fin(red_padsq(6n, r, 0)))
        show(cube.bdot.fin(red_bdot(5n, r, 0, w)))
        p_rows(m, (r + 1 : U32), w)

def p_map(k: Nat, +i: U32) -> IO(Unit):
  match k:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+m:
      do IO<Unit>:
        show(map.clamp.f(i, xval(0, i, 6), 0.5))
        p_map(m, (i + 1 : U32))

def main() -> IO(Unit):
  do IO<Unit>:
    p_ctr(1024n, 0, 0)
    p_rows(7n, 0, rows_b(7n, 0, ""))
    p_map(300n, 0)
