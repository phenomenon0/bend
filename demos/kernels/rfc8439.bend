# Executable RFC 8439 sections 2.1-2.3, independent list-index specification.
# https://www.rfc-editor.org/rfc/rfc8439#section-2.3
# The block contract uses eight key words and three nonce words, little-endian.
# This reference specifies the block; it makes no counter-exhaustion claim.
import Base

def at(xs: List<&2, U32>, i: Nat) -> U32:
  Maybe.default(&2, U32, List.get(&2, U32, xs, i), 0)

def sum_at(+xs: List<&2, U32>, +i: Nat, j: Nat) -> List<&2, U32>:
  List.set(&2, U32, xs, i, U32.add(at(xs, i), at(xs, j)))

def mix_at(+xs: List<&2, U32>, +i: Nat, j: Nat, +bits: Nat) -> List<&2, U32>:
  +v = U32.xor(at(xs, i), at(xs, j))
  List.set(&2, U32, xs, i,
    U32.or(U32.shln(v, bits), U32.shrn(v, Nat.sub(32n, bits))))

def quarter(xs: List<&2, U32>, +a: Nat, +b: Nat, +c: Nat, +d: Nat) -> List<&2, U32>:
  s1 = sum_at(xs, a, b)
  s2 = mix_at(s1, d, a, 16n)
  s3 = sum_at(s2, c, d)
  s4 = mix_at(s3, b, c, 12n)
  s5 = sum_at(s4, a, b)
  s6 = mix_at(s5, d, a, 8n)
  s7 = sum_at(s6, c, d)
  mix_at(s7, b, c, 7n)

def double_round(xs: List<&2, U32>) -> List<&2, U32>:
  s1 = quarter(xs, 0n, 4n, 8n, 12n)
  s2 = quarter(s1, 1n, 5n, 9n, 13n)
  s3 = quarter(s2, 2n, 6n, 10n, 14n)
  s4 = quarter(s3, 3n, 7n, 11n, 15n)
  s5 = quarter(s4, 0n, 5n, 10n, 15n)
  s6 = quarter(s5, 1n, 6n, 11n, 12n)
  s7 = quarter(s6, 2n, 7n, 8n, 13n)
  quarter(s7, 3n, 4n, 9n, 14n)

def rounds(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n: xs
    case 1n+p: rounds(p, double_round(xs))

def initial(key: List<&2, U32>, counter: U32, nonce: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, [1634760805,857760878,2036477234,1797285236],
    List.append(&2, U32, key, counter <> nonce))

def add_words(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  match xs ys:
    case x <> xt y <> yt: U32.add(x, y) <> add_words(xt, yt)
    case _ _: []

def block(key: List<&2, U32>, counter: U32, nonce: List<&2, U32>) -> List<&2, U32>:
  +s = initial(key, counter, nonce)
  add_words(s, rounds(10n, s))
