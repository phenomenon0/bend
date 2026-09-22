# SHA-1 (RFC 3174) over bytes, in Bend. It is written for the reader,
# not the clock: every shift is a single-bit shift repeated, a rotate
# is thirty-two of them, and a block is eighty rounds of that. It runs
# once per WebSocket handshake, where the accept key needs it, and
# LAWS.bend holds the RFC vectors as laws that the checker computes.
# Messages are bounded by U32 arithmetic on the bit length: under
# 512 MiB, which a handshake key is.
import Base

# Words
# =====

# shift left and right by k bits, one bit at a time
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

def rotl(+k: Nat, +x: U32) -> U32:
  U32.or(sh(k, x), sr(Nat.sub(32n, k), x))

def byte(x: U32) -> U32:
  U32.and(x, 255)

# four bytes, big-endian, into a word and back
def word(a: U32, b: U32, c: U32, d: U32) -> U32:
  U32.or(sh(24n, a), U32.or(sh(16n, b), U32.or(sh(8n, c), d)))

def unword(+w: U32) -> List<&2, U32>:
  [byte(sr(24n, w)), byte(sr(16n, w)),
   byte(sr(8n, w)), byte(w)]

# Padding
# =======

def zeros(k: Nat) -> List<&2, U32>:
  match k:
    case 0n:
      Nil{}
    case 1n+j:
      Con{0, zeros(j)}

# the zero bytes that bring n + 1 + z to 56 modulo 64
def gap(n: U32) -> U32:
  U32.and((119 - U32.and(n, 63) : U32), 63)

# the bit length, eight bytes big-endian; the high word is n >> 29
def tail(+n: U32) -> List<&2, U32>:
  List.append(&2, U32, unword(sr(29n, n)), unword(sh(3n, n)))

def pad.go(bs: List<&2, U32>, +n: U32) -> List<&2, U32>:
  List.append(&2, U32, bs,
    Con{128, List.append(&2, U32, zeros(U32.to_nat(gap(n))), tail(n))})

# the message, 0x80, zeros to the block boundary, the bit length
def pad(+bs: List<&2, U32>) -> List<&2, U32>:
  pad.go(bs, U32.from_nat(List.length(&2, U32, bs)))

# Blocks
# ======

# The padded message cut into blocks of sixteen words, four bytes to a
# word. The cutter's state is the word being read (reversed), how many
# words the current block has, and the blocks done (reversed).
type Cs is Data:
  Cs{cur: List<&2, U32>, n: U32, acc: List<&2, List<&2, U32>>}

def cs.go(cur: List<&2, U32>, n: U32, acc: List<&2, List<&2, U32>>, full: Bool) -> Cs:
  match full:
    case True{}:
      Cs{Nil{}, 0, Con{List.reverse(&2, U32, cur), acc}}
    case False{}:
      Cs{cur, n, acc}

def cs.push(cs: Cs, w: U32) -> Cs:
  match cs:
    case Cs{cur, +n, acc}:
      cs.go(Con{w, cur}, (n + 1 : U32), acc, U32.is_eq(n, 15))

def cs.blocks(cs: Cs) -> List<&2, List<&2, U32>>:
  match cs:
    case Cs{cur, n, acc}:
      List.reverse(&2, List<&2, U32>, acc)

# k words to read; a short tail (which padding rules out) is dropped
def chunks(k: Nat, bs: List<&2, U32>, cs: Cs) -> Cs:
  match k:
    case 0n:
      cs
    case 1n+j:
      match bs:
        case Nil{}:
          chunks(j, Nil{}, cs)
        case Con{a, t1}:
          match t1:
            case Nil{}:
              chunks(j, Nil{}, cs)
            case Con{b, t2}:
              match t2:
                case Nil{}:
                  chunks(j, Nil{}, cs)
                case Con{c, t3}:
                  match t3:
                    case Nil{}:
                      chunks(j, Nil{}, cs)
                    case Con{d, t}:
                      chunks(j, t, cs.push(cs, word(a, b, c, d)))

# Schedule
# ========

def nth(i: Nat, xs: List<&2, U32>) -> U32:
  match i xs:
    case 0n Nil{}:
      0
    case 0n Con{h, t}:
      h
    case 1n+j Nil{}:
      0
    case 1n+j Con{h, t}:
      nth(j, t)

# the sixteen words of a block grown to eighty, newest first: each new
# word is the rotate of the xor of the ones 3, 8, 14 and 16 back
def sched(k: Nat, +rws: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      rws
    case 1n+j:
      sched(j, Con{rotl(1n, U32.xor(nth(2n, rws),
        U32.xor(nth(7n, rws), U32.xor(nth(13n, rws), nth(15n, rws))))), rws})

# Rounds
# ======

type H is Data:
  H{a: U32, b: U32, c: U32, d: U32, e: U32}

# which of the three functions a round mixes with, and its constant
type Mix is Data:
  Ch{}
  Par{}
  Maj{}

type Mk is Data:
  Mk{m: Mix, k: U32}

def f(m: Mix, +b: U32, +c: U32, +d: U32) -> U32:
  match m:
    case Ch{}:
      U32.or(U32.and(b, c), U32.and(U32.not(b), d))
    case Par{}:
      U32.xor(b, U32.xor(c, d))
    case Maj{}:
      U32.or(U32.and(b, c), U32.or(U32.and(b, d), U32.and(c, d)))

def mk.go(lt20: Bool, lt40: Bool, lt60: Bool) -> Mk:
  match lt20 lt40 lt60:
    case True{} _ _:
      Mk{Ch{}, 1518500249}
    case False{} True{} _:
      Mk{Par{}, 1859775393}
    case False{} False{} True{}:
      Mk{Maj{}, 2400959708}
    case False{} False{} False{}:
      Mk{Par{}, 3395469782}

def mk(+t: U32) -> Mk:
  mk.go(U32.is_lt(t, 20), U32.is_lt(t, 40), U32.is_lt(t, 60))

def step(st: H, m: Mix, k: U32, w: U32) -> H:
  match st:
    case H{+a, +b, +c, +d, e}:
      H{U32.add(rotl(5n, a), U32.add(f(m, b, c, d), U32.add(e, U32.add(k, w)))),
        a, rotl(30n, b), c, d}

def step.mk(st: H, mk: Mk, w: U32) -> H:
  match mk:
    case Mk{m, k}:
      step(st, m, k, w)

# the eighty rounds, t counting them
def rounds(ws: List<&2, U32>, st: H, +t: U32) -> H:
  match ws:
    case Nil{}:
      st
    case Con{w, rest}:
      rounds(rest, step.mk(st, mk(t), w), (t + 1 : U32))

def plus(x: H, y: H) -> H:
  match x y:
    case H{a, b, c, d, e} H{a2, b2, c2, d2, e2}:
      H{U32.add(a, a2), U32.add(b, b2), U32.add(c, c2), U32.add(d, d2), U32.add(e, e2)}

# one block: schedule it, run it from the running hash, add it back in
def compress(+st: H, ws: List<&2, U32>) -> H:
  plus(st, rounds(
    List.reverse(&2, U32, sched(64n, List.reverse(&2, U32, ws))), st, 0))

def fold(blocks: List<&2, List<&2, U32>>, st: H) -> H:
  match blocks:
    case Nil{}:
      st
    case Con{ws, rest}:
      fold(rest, compress(st, ws))

# Hash
# ====

def init() -> H:
  H{1732584193, 4023233417, 2562383102, 271733878, 3285377520}

def out(st: H) -> List<&2, U32>:
  match st:
    case H{a, b, c, d, e}:
      List.append(&2, U32, unword(a), List.append(&2, U32, unword(b),
        List.append(&2, U32, unword(c), List.append(&2, U32, unword(d),
        unword(e)))))

# words in the padded message: (n + 1 + gap + 8) / 4
def nwords(+n: U32) -> Nat:
  U32.to_nat(U32.shr(U32.shr(((n + 9 : U32) + gap(n) : U32))))

# the twenty bytes of the digest
def hash(+bs: List<&2, U32>) -> List<&2, U32>:
  out(fold(cs.blocks(chunks(
    nwords(U32.from_nat(List.length(&2, U32, bs))), pad(bs), Cs{Nil{}, 0, Nil{}})),
    init()))
