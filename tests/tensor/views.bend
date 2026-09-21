# A view is a descriptor, not a copy. `View` holds four U32s and no cells, so
# it CANNOT carry data -- the only thing it can do is say where in the owner's
# one flat block the numbers already are. These four lines measure that.
#
# The overlap line is the proof that costs something to fake. `map` walks
# src 0..3 into dst 2..5, which overlap in cells 2 and 3, left to right:
#
#   i=0  dst[2] <- 2*src[0] = 2*1 = 2
#   i=1  dst[3] <- 2*src[1] = 2*2 = 4
#   i=2  dst[4] <- 2*src[2] = 2*2 = 4   <- src[2] IS dst[2], already written
#   i=3  dst[5] <- 2*src[3] = 2*4 = 8   <- src[3] IS dst[3], already written
#
# so cells 0..7 read 1 2 2 4 4 8 7 8. Had `map` copied its source first, they
# would read 1 2 2 4 6 8 7 8: cell 4 is 4 when the view aliases the owner and
# 6 when it does not. The `alias` line reads that cell through a view taken
# BEFORE the map ran, and sees the write.
import Base
import ../../demos/tensor/tensor.bend as T

def fill(fuel: Nat, +i: U32, t: T.Ten) -> T.Ten:
  match fuel:
    case 0n:
      t
    case 1n++k:
      fill(k, U32.inc(i), T.put(t, i, U32.to_f32(U32.inc(i))))

def dbl(x: F32) -> F32:
  F32.mul(x, 2.0)

type Out is Type:
  Out{t: T.Ten, v: U32}

def out.fin(r: T.Ten & F32) -> Out:
  (t, x) = r
  Out{t, F32.to_u32(x)}

def at(t: T.Ten, +i: U32) -> Out:
  out.fin(T.get(t, i))

def pack.add(+acc: U32, r: T.Ten & F32) -> Out:
  (t, x) = r
  Out{t, U32.add(U32.mul(acc, 10), F32.to_u32(x))}

def pack.go(fuel: Nat, +v: T.View, +i: U32, o: Out) -> Out:
  match fuel:
    case 0n:
      o
    case 1n++k:
      match o:
        case Out{t, acc}:
          pack.go(k, v, U32.inc(i), pack.add(acc, T.get(t, T.index(v, 0, i))))

def out.v(o: Out) -> U32:
  match o:
    case Out{t, acc}:
      acc

# one owner, one view over the whole of it, taken before anything is written
def worked() -> Out:
  pack.go(8n, T.vec(0, 8), 0,
    Out{T.map(~dbl, fill(8n, 0, T.zeros(4n)), T.vec(0, 4), T.vec(2, 4)), 0})

# the same run, read at cell 4 only, through a view taken before the map
def aliased() -> U32:
  out.v(at(T.map(~dbl, fill(8n, 0, T.zeros(4n)), T.vec(0, 4), T.vec(2, 4)),
    T.index(T.vec(0, 8), 0, 4)))

# taking a view allocates a four-word descriptor and reads nothing: the count
# folded here is the view's own, so the length stays live, and the owner is
# never touched. 1000 views of length 4 fold to 4000.
def many(fuel: Nat, +off: U32, +acc: U32) -> U32:
  match fuel:
    case 0n:
      acc
    case 1n++k:
      many(k, U32.and(U32.inc(off), 15),
        U32.add(acc, T.count(T.vec(off, 4))))

# the owner's size before and after a thousand views of it are taken
def sized.fin(+n: U32, r: T.Ten & U32) -> U32:
  (t, m) = r
  U32.add(U32.mul(n, 100), m)

def sized.mid(+n: U32, t: T.Ten) -> U32:
  sized.fin(U32.add(n, U32.mul(0, many(1000n, 0, 0))), T.size(t))

def sized.one(r: T.Ten & U32) -> U32:
  (t, n) = r
  sized.mid(n, t)

def sized() -> U32:
  sized.one(T.size(T.zeros(4n)))

def main() -> IO(Unit):
  do IO<Unit>:
    a : Unit <- IO.print(String.append("overlap ", U32.show(out.v(worked()))))
    b : Unit <- IO.print(String.append("alias ", U32.show(aliased())))
    c : Unit <- IO.print(String.append("views ", U32.show(many(1000n, 0, 0))))
    IO.print(String.append("size ", U32.show(sized())))

#|overlap 12244878
#|alias 4
#|views 4000
#|size 1616
