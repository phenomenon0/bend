# Packed big-endian SHA-256. Unused capacity and low bytes are ignored.
# Array.get wraps its index in Base; padding replaces any wrapped value.
import Base
import ./sha256.bend as S

# The marker occupies the first unused byte without retaining trailing storage.
def partial(+w: U32, n: Nat) -> U32:
  match n:
    case 0n: 2147483648
    case 1n: U32.or(U32.and(w, 4278190080), 8388608)
    case 2n: U32.or(U32.and(w, 4294901760), 32768)
    case 3n: U32.or(U32.and(w, 4294967040), 128)
    case _: w

def pad_select(order: Cmp, w: U32, remaining: Nat) -> U32:
  match order:
    case GT{}: 0
    case EQ{}: 2147483648
    case LT{}: partial(w, remaining)

def length_hi(total: Nat) -> U32:
  U32.from_nat(Nat.div(total, U32.to_nat(536870912)))

def length_lo(total: Nat) -> U32:
  U32.shln(U32.from_nat(total), 3n)

def tail_word(short: Bool, pos: Nat, padded: U32, +total: Nat) -> U32:
  match short pos:
    case True{} 56n: length_hi(total)
    case True{} 60n: length_lo(total)
    case _ _: padded

def input_word(final: Bool, w: U32, +pos: Nat, +remain: Nat, total: Nat) -> U32:
  match final:
    case False{}: w
    case True{}:
      tail_word(Nat.is_lt(remain, 56n), pos,
        pad_select(Nat.cmp(pos, remain), w, Nat.sub(remain, pos)), total)

def read16(+final: Bool, +index: U32, +remain: Nat, +total: Nat, st: S.Hash, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, pair: Array<U32> & U32) -> Array<U32> & S.Hash:
  (a, word) = pair
  w15 = input_word(final, word, 60n, remain, total)
  (a, S.compress16(w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, st))

def read15(+final: Bool, +index: U32, +remain: Nat, +total: Nat, st: S.Hash, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, pair: Array<U32> & U32) -> Array<U32> & S.Hash:
  (a, word) = pair
  w14 = input_word(final, word, 56n, remain, total)
  read16(final, U32.inc(index), remain, total, st, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, Array.get(U32, a, U32.inc(index)))

def read14(+final: Bool, +index: U32, +remain: Nat, +total: Nat, st: S.Hash, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, pair: Array<U32> & U32) -> Array<U32> & S.Hash:
  (a, word) = pair
  w13 = input_word(final, word, 52n, remain, total)
  read15(final, U32.inc(index), remain, total, st, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, Array.get(U32, a, U32.inc(index)))

def read13(+final: Bool, +index: U32, +remain: Nat, +total: Nat, st: S.Hash, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, w11: U32, pair: Array<U32> & U32) -> Array<U32> & S.Hash:
  (a, word) = pair
  w12 = input_word(final, word, 48n, remain, total)
  read14(final, U32.inc(index), remain, total, st, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, Array.get(U32, a, U32.inc(index)))

def read12(+final: Bool, +index: U32, +remain: Nat, +total: Nat, st: S.Hash, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, w10: U32, pair: Array<U32> & U32) -> Array<U32> & S.Hash:
  (a, word) = pair
  w11 = input_word(final, word, 44n, remain, total)
  read13(final, U32.inc(index), remain, total, st, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, Array.get(U32, a, U32.inc(index)))

def read11(+final: Bool, +index: U32, +remain: Nat, +total: Nat, st: S.Hash, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, w9: U32, pair: Array<U32> & U32) -> Array<U32> & S.Hash:
  (a, word) = pair
  w10 = input_word(final, word, 40n, remain, total)
  read12(final, U32.inc(index), remain, total, st, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, Array.get(U32, a, U32.inc(index)))

def read10(+final: Bool, +index: U32, +remain: Nat, +total: Nat, st: S.Hash, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, w8: U32, pair: Array<U32> & U32) -> Array<U32> & S.Hash:
  (a, word) = pair
  w9 = input_word(final, word, 36n, remain, total)
  read11(final, U32.inc(index), remain, total, st, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, Array.get(U32, a, U32.inc(index)))

def read9(+final: Bool, +index: U32, +remain: Nat, +total: Nat, st: S.Hash, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32, pair: Array<U32> & U32) -> Array<U32> & S.Hash:
  (a, word) = pair
  w8 = input_word(final, word, 32n, remain, total)
  read10(final, U32.inc(index), remain, total, st, w0, w1, w2, w3, w4, w5, w6, w7, w8, Array.get(U32, a, U32.inc(index)))

def read8(+final: Bool, +index: U32, +remain: Nat, +total: Nat, st: S.Hash, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, pair: Array<U32> & U32) -> Array<U32> & S.Hash:
  (a, word) = pair
  w7 = input_word(final, word, 28n, remain, total)
  read9(final, U32.inc(index), remain, total, st, w0, w1, w2, w3, w4, w5, w6, w7, Array.get(U32, a, U32.inc(index)))

def read7(+final: Bool, +index: U32, +remain: Nat, +total: Nat, st: S.Hash, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, pair: Array<U32> & U32) -> Array<U32> & S.Hash:
  (a, word) = pair
  w6 = input_word(final, word, 24n, remain, total)
  read8(final, U32.inc(index), remain, total, st, w0, w1, w2, w3, w4, w5, w6, Array.get(U32, a, U32.inc(index)))

def read6(+final: Bool, +index: U32, +remain: Nat, +total: Nat, st: S.Hash, w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, pair: Array<U32> & U32) -> Array<U32> & S.Hash:
  (a, word) = pair
  w5 = input_word(final, word, 20n, remain, total)
  read7(final, U32.inc(index), remain, total, st, w0, w1, w2, w3, w4, w5, Array.get(U32, a, U32.inc(index)))

def read5(+final: Bool, +index: U32, +remain: Nat, +total: Nat, st: S.Hash, w0: U32, w1: U32, w2: U32, w3: U32, pair: Array<U32> & U32) -> Array<U32> & S.Hash:
  (a, word) = pair
  w4 = input_word(final, word, 16n, remain, total)
  read6(final, U32.inc(index), remain, total, st, w0, w1, w2, w3, w4, Array.get(U32, a, U32.inc(index)))

def read4(+final: Bool, +index: U32, +remain: Nat, +total: Nat, st: S.Hash, w0: U32, w1: U32, w2: U32, pair: Array<U32> & U32) -> Array<U32> & S.Hash:
  (a, word) = pair
  w3 = input_word(final, word, 12n, remain, total)
  read5(final, U32.inc(index), remain, total, st, w0, w1, w2, w3, Array.get(U32, a, U32.inc(index)))

def read3(+final: Bool, +index: U32, +remain: Nat, +total: Nat, st: S.Hash, w0: U32, w1: U32, pair: Array<U32> & U32) -> Array<U32> & S.Hash:
  (a, word) = pair
  w2 = input_word(final, word, 8n, remain, total)
  read4(final, U32.inc(index), remain, total, st, w0, w1, w2, Array.get(U32, a, U32.inc(index)))

def read2(+final: Bool, +index: U32, +remain: Nat, +total: Nat, st: S.Hash, w0: U32, pair: Array<U32> & U32) -> Array<U32> & S.Hash:
  (a, word) = pair
  w1 = input_word(final, word, 4n, remain, total)
  read3(final, U32.inc(index), remain, total, st, w0, w1, Array.get(U32, a, U32.inc(index)))

def read1(+final: Bool, +index: U32, +remain: Nat, +total: Nat, st: S.Hash, pair: Array<U32> & U32) -> Array<U32> & S.Hash:
  (a, word) = pair
  w0 = input_word(final, word, 0n, remain, total)
  read2(final, U32.inc(index), remain, total, st, w0, Array.get(U32, a, U32.inc(index)))

def extra_block(more: Bool, +total: Nat, pair: Array<U32> & S.Hash) -> Array<U32> & S.Hash:
  match more pair:
    case False{} Tuple{a, st}:
      (a, st)
    case True{} Tuple{a, st}:
      (a, S.compress16(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        length_hi(total), length_lo(total), st))

# Only the block count decreases; final padding is always one or two blocks.
def blocks(n: Nat, +index: U32, +remain: Nat, +total: Nat,
  pair: Array<U32> & S.Hash) -> Array<U32> & S.Hash:
  match n pair:
    case 0n Tuple{a, st}:
      extra_block(Nat.is_ge(remain, 56n), total,
        read1(True{}, index, remain, total, st, Array.get(U32, a, index)))
    case 1n+p Tuple{a, st}:
      blocks(p, U32.add(index, 16), remain, total,
        read1(False{}, index, remain, total, st, Array.get(U32, a, index)))

# Internal: the public wrapper below establishes the capacity precondition.
def raw(a: Array<U32>, +length: Nat) -> S.Hash:
  Pair.snd(Array<U32>, S.Hash,
    blocks(Nat.div(length, 64n), 0, Nat.mod(length, 64n), length, (a, S.initial())))

def checked(valid: Bool, a: Array<U32>, length: Nat) -> Maybe<&1, Array<U32>>:
  match valid:
    case False{}:
      None{}
    case True{}:
      Some{S.digest_state(raw(a, length))}

def sized(+length: Nat, pair: Array<U32> & U32) -> Maybe<&1, Array<U32>>:
  (a, capacity) = pair
  checked(Nat.is_le(length, Nat.mul(4n, U32.to_nat(capacity))), a, length)

# Array.size is Base's capacity contract (balanced power-of-two storage).
def hash(a: Array<U32>, length: Nat) -> Maybe<&1, Array<U32>>:
  sized(length, Array.size(U32, a))

def hex_words(a: Array<U32>) -> String:
  match a:
    case ALeaf{x}:
      S.hex_word(8n, x, "")
    case ANode{l, r}:
      String.concat([hex_words(l), hex_words(r)])

def hex(result: Maybe<&1, Array<U32>>) -> String:
  match result:
    case None{}:
      "invalid length"
    case Some{a}:
      hex_words(a)
