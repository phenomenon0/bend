# The control: the same decode skeleton over THREE Array<F32> owners -- A, x
# and y each in their own block, which is how it reads before views exist.
# Same arithmetic, same order, same checksum; the only difference is how many
# owners the loop has to carry.
import Base

type Dot is Type:
  Dot{a: Array<F32>, x: Array<F32>, s: F32}

type Sep is Type:
  Sep{a: Array<F32>, x: Array<F32>, y: Array<F32>}

def h(+p: U32) -> U32:
  U32.xor(U32.mul(U32.inc(p), 2654435761), U32.shrn(p, 3n))

def v(+p: U32) -> F32:
  F32.div(F32.sub(U32.to_f32(U32.shrn(h(p), 19n)), 4096.0), 4096.0)

def fill.a(fuel: Nat, +i: U32, a: Array<F32>) -> Array<F32>:
  match fuel:
    case 0n:
      a
    case 1n++k:
      fill.a(k, U32.inc(i), Array.set(F32, a, i, v(i)))

def fill.x(fuel: Nat, +i: U32, x: Array<F32>) -> Array<F32>:
  match fuel:
    case 0n:
      x
    case 1n++k:
      fill.x(k, U32.inc(i), Array.set(F32, x, i, v(U32.add(i, 1048576))))

def d.y(a: Array<F32>, +u: F32, +s: F32, r: Array<F32> & F32) -> Dot:
  (x, w) = r
  Dot{a, x, F32.add(s, F32.mul(u, w))}

def d.x(x: Array<F32>, +i: U32, +s: F32, r: Array<F32> & F32) -> Dot:
  (a, u) = r
  d.y(a, u, s, Array.get(F32, x, i))

def d.go(fuel: Nat, +p: U32, +i: U32, st: Dot) -> Dot:
  match fuel:
    case 0n:
      st
    case 1n++k:
      match st:
        case Dot{a, x, s}:
          d.go(k, U32.inc(p), U32.inc(i), d.x(x, i, s, Array.get(F32, a, p)))

def row.fin(+r: U32, y: Array<F32>, st: Dot) -> Sep:
  match st:
    case Dot{a, x, s}:
      Sep{a, x, Array.set(F32, y, r, s)}

def g.go(fuel: Nat, +p: U32, +r: U32, +cols: Nat, sp: Sep) -> Sep:
  match fuel:
    case 0n:
      sp
    case 1n++k:
      match sp:
        case Sep{a, x, y}:
          g.go(k, U32.add(p, 1024), U32.inc(r), cols,
            row.fin(r, y, d.go(cols, p, 0, Dot{a, x, 0.0})))

def sc.put(x: Array<F32>, +i: U32, r: Array<F32> & F32) -> Array<F32> & Array<F32>:
  (y, w) = r
  (Array.set(F32, x, i, F32.mul(w, 0.140625)), y)

def sc.step(+i: U32, r: Array<F32> & Array<F32>) -> Array<F32> & Array<F32>:
  (x, y) = r
  sc.put(x, i, Array.get(F32, y, i))

def sc.go(fuel: Nat, +i: U32, r: Array<F32> & Array<F32>) -> Array<F32> & Array<F32>:
  match fuel:
    case 0n:
      r
    case 1n++k:
      sc.go(k, U32.inc(i), sc.step(i, r))

def sc.fin(a: Array<F32>, r: Array<F32> & Array<F32>) -> Sep:
  (x, y) = r
  Sep{a, x, y}

def scale(sp: Sep) -> Sep:
  match sp:
    case Sep{a, x, y}:
      sc.fin(a, sc.go(1024n, 0, (x, y)))

def step(sp: Sep) -> Sep:
  scale(g.go(1024n, 0, 0, 1024n, sp))

def reps(fuel: Nat, sp: Sep) -> Sep:
  match fuel:
    case 0n:
      sp
    case 1n++k:
      reps(k, step(sp))

# the probes of bench_gemv.bend, folded the same way over the same 1024 words
def nonfin(+b: U32) -> U32:
  U32.and(U32.add(U32.and(b, 2139095040), 8388608), 2147483648)

def rot7(+v: U32) -> U32:
  U32.or(U32.shln(v, 7n), U32.shrn(v, 25n))

def mix(+acc: U32, +x: U32) -> U32:
  rot7(U32.add(U32.mul(acc, 31), x))

type Sum is Type:
  Sum{sp: Sep, acc: U32, orb: U32, andb: U32, nf: U32}

def sum.bits(sp: Sep, +acc: U32, +orb: U32, +andb: U32, +nf: U32, +b: U32) -> Sum:
  Sum{sp, mix(acc, b), U32.or(orb, b), U32.and(andb, b), U32.or(nf, nonfin(b))}

def sum.add(a: Array<F32>, y: Array<F32>, +acc: U32, +orb: U32, +andb: U32,
  +nf: U32, r: Array<F32> & F32) -> Sum:
  (x, w) = r
  sum.bits(Sep{a, x, y}, acc, orb, andb, nf, F32.bits(w))

def sum.one(+i: U32, +acc: U32, +orb: U32, +andb: U32, +nf: U32, sp: Sep) -> Sum:
  match sp:
    case Sep{a, x, y}:
      sum.add(a, y, acc, orb, andb, nf, Array.get(F32, x, i))

def sum.go(fuel: Nat, +i: U32, s: Sum) -> Sum:
  match fuel:
    case 0n:
      s
    case 1n++k:
      match s:
        case Sum{sp, acc, orb, andb, nf}:
          sum.go(k, U32.inc(i), sum.one(i, acc, orb, andb, nf, sp))

def sum.four(s: Sum) -> String:
  match s:
    case Sum{sp, acc, orb, andb, nf}:
      String.join([U32.show(acc), U32.show(orb), U32.show(andb),
        U32.show(nf)], "\n")

def start() -> Sep:
  Sep{fill.a(1048576n, 0, [0.0 : F32^20n]), fill.x(1024n, 0, [0.0 : F32^10n]),
    [0.0 : F32^10n]}

law main:
  IO(Unit)

def main():
  do IO<Unit>:
    IO.print(sum.four(sum.go(1024n, 0,
      Sum{reps(256n, start()), 0, 0, 4294967295, 0})))
