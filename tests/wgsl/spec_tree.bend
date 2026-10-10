# Shape specialisation: a non-tail binary recursion on a Nat depth that the leaf gives as a literal. WGSL has no
# recursion; the lane unrolls it, one fn per (def, literal depth). Two depths in one program (4 and 2).
#   spec!(d, i) = sum over lanes of ptree(4, lane x, lane c) ^ ptree(2, ...)
import Base

def pow2(d: Nat) -> Nat:
  match d:
    case 0n:
      1n
    case 1n+p:
      +h = pow2(p)
      Nat.add(h, h)

# 2^dp leaves: a mixing tree, children given their own (x, c)
def ptree(dp: Nat, +x: U32, +c: U32) -> U32:
  match dp:
    case 0n:
      ((((x * c : U32) + 1 : U32) .^. (c >> 3n : U32)) : U32)
    case 1n++p:
      a b = ptree(p, (x + 1 : U32), ((c * 3 : U32) + 1 : U32)) ptree(p, (x * 5 : U32), ((c * 5 : U32) + 2 : U32))
      ((((a .^. (b << 1n : U32)) : U32) + c : U32) + x : U32)

def lane(+i: U32) -> U32:
  ((ptree(4n, i, 7) .^. ptree(2n, (i + 3 : U32), (i * 11 : U32))) : U32)

def spec(d: Nat, +i: U32) -> U32:
  match d:
    case 0n:
      lane(i)
    case 1n++p:
      a b = spec(p, i) spec(p, (i + U32.from_nat(pow2(p)) : U32))
      (a + b : U32)

def main() -> IO(Unit):
  IO.print(U32.show(spec!(8n, 0)))

#|512271840
