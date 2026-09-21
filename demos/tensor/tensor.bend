# Tensor: one flat block of F32, and read-only descriptors over it.
import Base

type Ten is Type:
  Ten{n: U32, depth: Nat, xs: Array<F32>}

type View is Data:
  View{off: U32, rows: U32, cols: U32, stride: U32}

def zeros(+depth: Nat) -> Ten:
  Ten{U32.shln(1, depth), depth, [0.0 : F32^depth]}

def size(t: Ten) -> Ten & U32:
  match t:
    case Ten{+n, d, xs}:
      (Ten{n, d, xs}, n)

def get.fin(n: U32, d: Nat, r: Array<F32> & F32) -> Ten & F32:
  (xs, x) = r
  (Ten{n, d, xs}, x)

def get(t: Ten, +i: U32) -> Ten & F32:
  match t:
    case Ten{n, d, xs}:
      get.fin(n, d, Array.get(F32, xs, i))

def put(t: Ten, +i: U32, +x: F32) -> Ten:
  match t:
    case Ten{n, d, xs}:
      Ten{n, d, Array.set(F32, xs, i, x)}

# -- the views ---------------------------------------------------------------

def vec(+off: U32, +len: U32) -> View:
  View{off, 1, len, len}

def mat(+off: U32, +rows: U32, +cols: U32, +stride: U32) -> View:
  View{off, rows, cols, stride}

def count(v: View) -> U32:
  match v:
    case View{off, +rows, +cols, stride}:
      U32.mul(rows, cols)

def row(v: View, +i: U32) -> View:
  match v:
    case View{+off, rows, +cols, +stride}:
      View{U32.add(off, U32.mul(i, stride)), 1, cols, stride}

def col(v: View, +j: U32) -> View:
  match v:
    case View{+off, +rows, cols, +stride}:
      View{U32.add(off, j), rows, 1, stride}

def index(v: View, +r: U32, +c: U32) -> U32:
  match v:
    case View{+off, rows, cols, +stride}:
      U32.add(off, U32.add(U32.mul(r, stride), c))

# -- gemv --------------------------------------------------------------------

def dot.mul(+a: F32, +s: F32, r: Array<F32> & F32) -> Array<F32> & F32:
  (xs, b) = r
  (xs, F32.add(s, F32.mul(a, b)))

def dot.pair(+q: U32, +s: F32, r: Array<F32> & F32) -> Array<F32> & F32:
  (xs, a) = r
  dot.mul(a, s, Array.get(F32, xs, q))

def dot.step(+p: U32, +q: U32, r: Array<F32> & F32) -> Array<F32> & F32:
  (xs, s) = r
  dot.pair(q, s, Array.get(F32, xs, p))

def dot.go(fuel: Nat, +p: U32, +q: U32, r: Array<F32> & F32) -> Array<F32> & F32:
  match fuel:
    case 0n:
      r
    case 1n++k:
      dot.go(k, U32.inc(p), U32.inc(q), dot.step(p, q, r))

def gemv.set(+iy: U32, r: Array<F32> & F32) -> Array<F32>:
  (xs, s) = r
  Array.set(F32, xs, iy, s)

def gemv.row(+pa: U32, +px: U32, +iy: U32, cols: Nat, xs: Array<F32>) -> Array<F32>:
  gemv.set(iy, dot.go(cols, pa, px, (xs, 0.0)))

def gemv.go(fuel: Nat, +pa: U32, +sa: U32, +px: U32, +iy: U32, +cols: Nat, xs: Array<F32>) -> Array<F32>:
  match fuel:
    case 0n:
      xs
    case 1n++k:
      gemv.go(k, U32.add(pa, sa), sa, px, U32.inc(iy), cols, gemv.row(pa, px, iy, cols, xs))

def gemv.at(+oa: U32, +ra: U32, +ca: U32, +sa: U32, +ox: U32, +oy: U32, n: U32, d: Nat, xs: Array<F32>) -> Ten:
  Ten{n, d, gemv.go(U32.to_nat(ra), oa, sa, ox, oy, U32.to_nat(ca), xs)}

def gemv.x(a: View, +ox: U32, +oy: U32, n: U32, d: Nat, xs: Array<F32>) -> Ten:
  match a:
    case View{+oa, +ra, +ca, +sa}:
      gemv.at(oa, ra, ca, sa, ox, oy, n, d, xs)

def gemv.v(a: View, x: View, y: View, n: U32, d: Nat, xs: Array<F32>) -> Ten:
  match x:
    case View{+ox, rx, cx, sx}:
      match y:
        case View{+oy, ry, cy, sy}:
          gemv.x(a, ox, oy, n, d, xs)

# y <- A x, all three inside one owner's block: A is rows x cols with a row
# stride, x and y are contiguous runs. Nothing is copied and nothing is
# allocated -- the three views say where the numbers already are.
def gemv(t: Ten, a: View, x: View, y: View) -> Ten:
  match t:
    case Ten{n, d, xs}:
      gemv.v(a, x, y, n, d, xs)

# -- map ---------------------------------------------------------------------

def map.put(~f: F32 -> F32, +q: U32, r: Array<F32> & F32) -> Array<F32>:
  (xs, x) = r
  Array.set(F32, xs, q, f(x))

def map.step(~f: F32 -> F32, +p: U32, +q: U32, xs: Array<F32>) -> Array<F32>:
  map.put(~f, q, Array.get(F32, xs, p))

def map.run(~f: F32 -> F32, fuel: Nat, +p: U32, +q: U32, xs: Array<F32>) -> Array<F32>:
  match fuel:
    case 0n:
      xs
    case 1n++k:
      map.run(~f, k, U32.inc(p), U32.inc(q), map.step(~f, p, q, xs))

def map.go(~f: F32 -> F32, fuel: Nat, +p: U32, +q: U32, +sp: U32, +sq: U32, +cols: Nat, xs: Array<F32>) -> Array<F32>:
  match fuel:
    case 0n:
      xs
    case 1n++k:
      map.go(~f, k, U32.add(p, sp), U32.add(q, sq), sp, sq, cols, map.run(~f, cols, p, q, xs))

def map.at(~f: F32 -> F32, +op: U32, +rp: U32, +cp: U32, +sp: U32, +oq: U32, +sq: U32, n: U32, d: Nat, xs: Array<F32>) -> Ten:
  Ten{n, d, map.go(~f, U32.to_nat(rp), op, oq, sp, sq, U32.to_nat(cp), xs)}

def map.d(~f: F32 -> F32, +op: U32, +rp: U32, +cp: U32, +sp: U32, dst: View, n: U32, d: Nat, xs: Array<F32>) -> Ten:
  match dst:
    case View{+oq, rq, cq, +sq}:
      map.at(~f, op, rp, cp, sp, oq, sq, n, d, xs)

def map.s(~f: F32 -> F32, src: View, dst: View, n: U32, d: Nat, xs: Array<F32>) -> Ten:
  match src:
    case View{+op, +rp, +cp, +sp}:
      map.d(~f, op, rp, cp, sp, dst, n, d, xs)

# dst[r, c] <- f(src[r, c]), over one owner's block. src and dst may be the
# same view (in place) or overlap: the walk is row by row, left to right, and
# a caller that overlaps them backwards gets what that order gives.
def map(~f: F32 -> F32, t: Ten, src: View, dst: View) -> Ten:
  match t:
    case Ten{n, d, xs}:
      map.s(~f, src, dst, n, d, xs)
