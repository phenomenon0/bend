# Base64 (RFC 4648) over bytes, in Bend: three bytes in, four
# characters out, '=' for what the last group lacks. LAWS.bend holds
# the RFC vectors as laws. It runs once per WebSocket handshake.
import Base

def sh(k: Nat, x: U32) -> U32:
  match k:
    case 0n:
      x
    case 1n+j:
      sh(j, U32.shl(x))

def sr(k: Nat, x: U32) -> U32:
  match k:
    case 0n:
      x
    case 1n+j:
      sr(j, U32.shr(x))

# the alphabet: A-Z, a-z, 0-9, '+', '/'
def tab.go(+i: U32, az: Bool, lower: Bool, digit: Bool, plus: Bool) -> U32:
  match az lower digit plus:
    case True{} _ _ _:
      (i + 65 : U32)
    case False{} True{} _ _:
      (i + 71 : U32)
    case False{} False{} True{} _:
      (i - 4 : U32)
    case False{} False{} False{} True{}:
      43
    case False{} False{} False{} False{}:
      47

def tab(+i: U32) -> U32:
  tab.go(i, U32.is_lt(i, 26), U32.is_lt(i, 52), U32.is_lt(i, 62), U32.is_eq(i, 62))

# the four sextets of three bytes, and the shorter groups
def c1(+a: U32) -> U32:
  tab(sr(2n, a))

def c2(a: U32, b: U32) -> U32:
  tab(U32.or(sh(4n, U32.and(a, 3)), sr(4n, b)))

def c3(b: U32, c: U32) -> U32:
  tab(U32.or(sh(2n, U32.and(b, 15)), sr(6n, c)))

def c4(c: U32) -> U32:
  tab(U32.and(c, 63))

def enc(bs: List<&2, U32>) -> List<&2, U32>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{+a, t1}:
      match t1:
        case Nil{}:
          [c1(a), c2(a, 0), 61, 61]
        case Con{+b, t2}:
          match t2:
            case Nil{}:
              [c1(a), c2(a, b), c3(b, 0), 61]
            case Con{+c, t}:
              Con{c1(a), Con{c2(a, b), Con{c3(b, c), Con{c4(c), enc(t)}}}}
