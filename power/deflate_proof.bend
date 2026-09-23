# The proofs of power/deflate_laws.bend.
import Base
import ../wire/reader.bend as Wr
import ./deflate.bend as D
import ./gzip.bend as Z
import ./deflate_laws.bend as Laws

# The reads
# =========
#
# The inflate machine and the gunzip machine are byte-step readers; the
# reader kit (wire/reader.bend) proves chunking once for every such
# reader, and a one-byte move needs no obligation but the kit's own.

def Laws.inflate_split(a, b, st):
  Wr.feed_split(~Unit, ~D.St, ~D.wstep, Unit{}, a, b, st)

def adv_ok(+e: Unit, +s: Bytes(), p: D.St) ->
  {Wr.feed_buf.last(~Unit, ~D.St, ~D.wstep, e, D.wadv(e, s, p)) ==
    Wr.feed_buf.slow(~Unit, ~D.St, ~D.wstep, e, s, p) : D.St}:
  Wr.one.step_ok(~Unit, ~D.St, ~D.wstep, e, s, p)

def Laws.inflate_buf(s, st):
  Wr.feed_buf_is_feed(~Unit, ~D.St, ~D.wstep, ~D.wadv, ~adv_ok, Unit{}, s, st)

def Laws.inflate_buf_split(a, b, st):
  Wr.feed_buf_split(~Unit, ~D.St, ~D.wstep, ~D.wadv, ~adv_ok, Unit{}, a, b, st)

def Laws.gunzip_split(a, b, g):
  Wr.feed_split(~Unit, ~Z.G, ~Z.wstep, Unit{}, a, b, g)

def gz_adv_ok(+e: Unit, +s: Bytes(), p: Z.G) ->
  {Wr.feed_buf.last(~Unit, ~Z.G, ~Z.wstep, e, Z.wadv(e, s, p)) ==
    Wr.feed_buf.slow(~Unit, ~Z.G, ~Z.wstep, e, s, p) : Z.G}:
  Wr.one.step_ok(~Unit, ~Z.G, ~Z.wstep, e, s, p)

def Laws.gunzip_buf(s, g):
  Wr.feed_buf_is_feed(~Unit, ~Z.G, ~Z.wstep, ~Z.wadv, ~gz_adv_ok, Unit{}, s, g)

# The fixed points
# ----------------
#
# A byte is eight steps and the bit offset goes round once: from any of
# the eight offsets a refused (or ended) machine is where it was.

type B8 is Data:
  O0{}
  O1{}
  O2{}
  O3{}
  O4{}
  O5{}
  O6{}
  O7{}

def b8n(k: B8) -> Nat:
  match k:
    case O0{}:
      0n
    case O1{}:
      1n
    case O2{}:
      2n
    case O3{}:
      3n
    case O4{}:
      4n
    case O5{}:
      5n
    case O6{}:
      6n
    case O7{}:
      7n

type Held is Data:
  HBad{why: D.Why, o: D.O, k: B8}
  HEnd{o: D.O, k: B8}

def held(x: Held) -> D.St:
  match x:
    case HBad{why, o, k}:
      D.St{D.Bad{why}, o, b8n(k)}
    case HEnd{o, k}:
      D.St{D.End{}, o, b8n(k)}

def held_fix(+e: Unit, +x: Held, +c: U32) -> {D.wstep(e, held(x), c) == held(x) : D.St}:
  match x:
    case HBad{why, o, k}:
      match k:
        case O0{}:
          {==}
        case O1{}:
          {==}
        case O2{}:
          {==}
        case O3{}:
          {==}
        case O4{}:
          {==}
        case O5{}:
          {==}
        case O6{}:
          {==}
        case O7{}:
          {==}
    case HEnd{o, k}:
      match k:
        case O0{}:
          {==}
        case O1{}:
          {==}
        case O2{}:
          {==}
        case O3{}:
          {==}
        case O4{}:
          {==}
        case O5{}:
          {==}
        case O6{}:
          {==}
        case O7{}:
          {==}

def held_feeds(+s: List<&2, U32>, +x: Held) ->
  {D.feed_list(s, held(x)) == held(x) : D.St}:
  Wr.bad_feeds(~Unit, ~D.St, ~D.wstep, ~Held, ~held, ~held_fix, Unit{}, s, x)

def bad_at(+s: List<&2, U32>, +why: D.Why, +o: D.O, +bp: Nat) ->
  {Nat.is_lt(bp, 8n) == True{} : Bool} -> {D.feed_list(s, D.St{D.Bad{why}, o, bp}) == D.St{D.Bad{why}, o, bp} : D.St}:
  match bp:
    case 0n:
      lt => held_feeds(s, HBad{why, o, O0{}})
    case 1n+p0:
      match p0:
        case 0n:
          lt => held_feeds(s, HBad{why, o, O1{}})
        case 1n+p1:
          match p1:
            case 0n:
              lt => held_feeds(s, HBad{why, o, O2{}})
            case 1n+p2:
              match p2:
                case 0n:
                  lt => held_feeds(s, HBad{why, o, O3{}})
                case 1n+p3:
                  match p3:
                    case 0n:
                      lt => held_feeds(s, HBad{why, o, O4{}})
                    case 1n+p4:
                      match p4:
                        case 0n:
                          lt => held_feeds(s, HBad{why, o, O5{}})
                        case 1n+p5:
                          match p5:
                            case 0n:
                              lt => held_feeds(s, HBad{why, o, O6{}})
                            case 1n+p6:
                              match p6:
                                case 0n:
                                  lt => held_feeds(s, HBad{why, o, O7{}})
                                case 1n+p7:
                                  lt => Nat.lt_zero({D.feed_list(s, D.St{D.Bad{why}, o, 8n+p7}) == D.St{D.Bad{why}, o, 8n+p7} : D.St}, p7, lt)

def end_at(+s: List<&2, U32>, +o: D.O, +bp: Nat) ->
  {Nat.is_lt(bp, 8n) == True{} : Bool} -> {D.feed_list(s, D.St{D.End{}, o, bp}) == D.St{D.End{}, o, bp} : D.St}:
  match bp:
    case 0n:
      lt => held_feeds(s, HEnd{o, O0{}})
    case 1n+p0:
      match p0:
        case 0n:
          lt => held_feeds(s, HEnd{o, O1{}})
        case 1n+p1:
          match p1:
            case 0n:
              lt => held_feeds(s, HEnd{o, O2{}})
            case 1n+p2:
              match p2:
                case 0n:
                  lt => held_feeds(s, HEnd{o, O3{}})
                case 1n+p3:
                  match p3:
                    case 0n:
                      lt => held_feeds(s, HEnd{o, O4{}})
                    case 1n+p4:
                      match p4:
                        case 0n:
                          lt => held_feeds(s, HEnd{o, O5{}})
                        case 1n+p5:
                          match p5:
                            case 0n:
                              lt => held_feeds(s, HEnd{o, O6{}})
                            case 1n+p6:
                              match p6:
                                case 0n:
                                  lt => held_feeds(s, HEnd{o, O7{}})
                                case 1n+p7:
                                  lt => Nat.lt_zero({D.feed_list(s, D.St{D.End{}, o, 8n+p7}) == D.St{D.End{}, o, 8n+p7} : D.St}, p7, lt)

def Laws.inflate_bad(s, why, o, bp, lt):
  bad_at(s, why, o, bp)(lt)

def Laws.inflate_end(s, o, bp, lt):
  end_at(s, o, bp)(lt)

type GB is Data:
  GB{at: Nat, why: Z.Why, done: Bytes(), crc: U32, cap: Nat, pos: Nat}

def gb(x: GB) -> Z.G:
  match x:
    case GB{at, why, done, crc, cap, pos}:
      Z.G{Z.Bad{at, why}, done, crc, cap, pos}

def gb_fix(+e: Unit, +x: GB, +c: U32) -> {Z.wstep(e, gb(x), c) == gb(x) : Z.G}:
  match x:
    case GB{at, why, done, crc, cap, pos}:
      {==}

def Laws.gunzip_bad(s, at, why, done, crc, cap, pos):
  Wr.bad_feeds(~Unit, ~Z.G, ~Z.wstep, ~GB, ~gb, ~gb_fix, Unit{}, s, GB{at, why, done, crc, cap, pos})


# CRC-32
# ======
#
# The table method is right because the CRC's bit step is linear over
# xor (lin): eight steps of the register z are eight steps of its low
# byte, which the table holds (tab, cell by cell), xor eight steps of
# the rest, which has no bit to fold in and so is only shifted (hi8).
# U32 is Word(32n), 32 Bools low bit first; the lemmas are on words.

# Words
# -----

def bx_comm(+a: Bool, +b: Bool) -> {Bool.xor(a, b) == Bool.xor(b, a) : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def wcon_eq(-p: Nat, -a: Bool, -b: Bool, -s: Word(p), -t: Word(p), e1: {a == b : Bool},
  e2: {s == t : Word(p)}) -> {WCon{a, s} == WCon{b, t} : Word(1n+p)}:
  %Equal.sym(Bool, a, b, e1) : {WCon{_, s} == WCon{b, t} : Word(1n+p)}
  %Equal.sym(Word(p), s, t, e2) : {WCon{b, _} == WCon{b, t} : Word(1n+p)}
  {==}

def x_comm(+n: Nat, +a: Word(n), +b: Word(n)) -> {Word.xor(n, a, b) == Word.xor(n, b, a) : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{+ah, +at} WCon{+bh, +bt}:
          wcon_eq(p, Bool.xor(ah, bh), Bool.xor(bh, ah), Word.xor(p, at, bt), Word.xor(p, bt, at),
            bx_comm(ah, bh), x_comm(p, at, bt))

def bx_assoc(+a: Bool, +b: Bool, +c: Bool) ->
  {Bool.xor(Bool.xor(a, b), c) == Bool.xor(a, Bool.xor(b, c)) : Bool}:
  match a b c:
    case False{} False{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} True{} True{}:
      {==}

def x_assoc(+n: Nat, +a: Word(n), +b: Word(n), +c: Word(n)) ->
  {Word.xor(n, Word.xor(n, a, b), c) == Word.xor(n, a, Word.xor(n, b, c)) : Word(n)}:
  match n:
    case 0n:
      match a b c:
        case WNil{} WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b c:
        case WCon{+ah, +at} WCon{+bh, +bt} WCon{+ch, +ct}:
          wcon_eq(p, Bool.xor(Bool.xor(ah, bh), ch), Bool.xor(ah, Bool.xor(bh, ch)),
            Word.xor(p, Word.xor(p, at, bt), ct), Word.xor(p, at, Word.xor(p, bt, ct)),
            bx_assoc(ah, bh, ch), x_assoc(p, at, bt, ct))

def bx_self(+a: Bool) -> {Bool.xor(a, a) == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def x_self(+n: Nat, +a: Word(n)) -> {Word.xor(n, a, a) == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+p:
      match a:
        case WCon{+ah, +at}:
          wcon_eq(p, Bool.xor(ah, ah), False{}, Word.xor(p, at, at), Word.zero(p), bx_self(ah),
            x_self(p, at))

def x_zero(+n: Nat, +a: Word(n)) -> {Word.xor(n, Word.zero(n), a) == a : Word(n)}:
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+p:
      match a:
        case WCon{+ah, +at}:
          wcon_eq(p, ah, ah, Word.xor(p, Word.zero(p), at), at, {==}, x_zero(p, at))

def pad_xor(+n: Nat, +a: Word(n), +b: Word(n)) ->
  {Word.shr.pad(n, Word.xor(n, a, b)) == Word.xor(1n+n, Word.shr.pad(n, a), Word.shr.pad(n, b)) :
    Word(1n+n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{+ah, +at} WCon{+bh, +bt}:
          wcon_eq(1n+p, Bool.xor(ah, bh), Bool.xor(ah, bh), Word.shr.pad(p, Word.xor(p, at, bt)),
            Word.xor(1n+p, Word.shr.pad(p, at), Word.shr.pad(p, bt)), {==}, pad_xor(p, at, bt))

def band_f(+a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def and_zero(+n: Nat, +a: Word(n)) -> {Word.and(n, a, Word.zero(n)) == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+p:
      match a:
        case WCon{+ah, +at}:
          wcon_eq(p, Bool.and(ah, False{}), False{}, Word.and(p, at, Word.zero(p)), Word.zero(p),
            band_f(ah), and_zero(p, at))

# U32
# ---

def ux_comm(+a: U32, +b: U32) -> {U32.xor(a, b) == U32.xor(b, a) : U32}:
  match a b:
    case U32{+x} U32{+y}:
      Equal.cong(Word(32n), U32, w => U32{w}, Word.xor(32n, x, y), Word.xor(32n, y, x),
        x_comm(32n, x, y))

def ux_assoc(+a: U32, +b: U32, +c: U32) ->
  {U32.xor(U32.xor(a, b), c) == U32.xor(a, U32.xor(b, c)) : U32}:
  match a b c:
    case U32{+x} U32{+y} U32{+z}:
      Equal.cong(Word(32n), U32, w => U32{w}, Word.xor(32n, Word.xor(32n, x, y), z),
        Word.xor(32n, x, Word.xor(32n, y, z)), x_assoc(32n, x, y, z))

def ux_self(+a: U32) -> {U32.xor(a, a) == U32{Word.zero(32n)} : U32}:
  match a:
    case U32{+x}:
      Equal.cong(Word(32n), U32, w => U32{w}, Word.xor(32n, x, x), Word.zero(32n), x_self(32n, x))

def ux_zero(+a: U32) -> {U32.xor(U32{Word.zero(32n)}, a) == a : U32}:
  match a:
    case U32{+x}:
      Equal.cong(Word(32n), U32, w => U32{w}, Word.xor(32n, Word.zero(32n), x), x, x_zero(32n, x))

# (a ^ p) ^ b is (a ^ b) ^ p
def ux_swap(+a: U32, +p: U32, +b: U32) ->
  {U32.xor(U32.xor(a, p), b) == U32.xor(U32.xor(a, b), p) : U32}:
  %Equal.sym(U32, U32.xor(U32.xor(a, p), b), U32.xor(a, U32.xor(p, b)), ux_assoc(a, p, b)) :
    {_ == U32.xor(U32.xor(a, b), p) : U32}
  %ux_comm(b, p) : {U32.xor(a, _) == U32.xor(U32.xor(a, b), p) : U32}
  Equal.sym(U32, U32.xor(U32.xor(a, b), p), U32.xor(a, U32.xor(b, p)), ux_assoc(a, b, p))

# The CRC's one bit, read off the word
# -----------------------------------

def shr1(t: Word(31n)) -> U32:
  U32{Word.shr.pad(31n, t)}

def cbit(b: Bool, +t: Word(31n)) -> U32:
  D.u32.pick(b, U32.xor(shr1(t), D.POLY()), shr1(t))

def bitc(+b: Bool, +t: Word(31n)) -> {D.crc.bit(U32{WCon{b, t}}) == cbit(b, t) : U32}:
  match b:
    case False{}:
      %Equal.sym(Word(31n), Word.and(31n, t, Word.zero(31n)), Word.zero(31n), and_zero(31n, t)) :
        {D.u32.pick(U32.is_eq(U32{WCon{False{}, _}}, 1), U32.xor(shr1(t), D.POLY()), shr1(t)) ==
          cbit(False{}, t) : U32}
      {==}
    case True{}:
      %Equal.sym(Word(31n), Word.and(31n, t, Word.zero(31n)), Word.zero(31n), and_zero(31n, t)) :
        {D.u32.pick(U32.is_eq(U32{WCon{True{}, _}}, 1), U32.xor(shr1(t), D.POLY()), shr1(t)) ==
          cbit(True{}, t) : U32}
      {==}

def sh_x(+s: Word(31n), +t: Word(31n)) ->
  {shr1(Word.xor(31n, s, t)) == U32.xor(shr1(s), shr1(t)) : U32}:
  Equal.cong(Word(32n), U32, w => U32{w}, Word.shr.pad(31n, Word.xor(31n, s, t)),
    Word.xor(32n, Word.shr.pad(31n, s), Word.shr.pad(31n, t)), pad_xor(31n, s, t))

# (a ^ p) ^ (b ^ p) is a ^ b
def ux_cancel(+a: U32, +p: U32, +b: U32) ->
  {U32.xor(U32.xor(a, p), U32.xor(b, p)) == U32.xor(a, b) : U32}:
  %ux_assoc(U32.xor(a, p), b, p) : {_ == U32.xor(a, b) : U32}
  %Equal.sym(U32, U32.xor(U32.xor(a, p), b), U32.xor(U32.xor(a, b), p), ux_swap(a, p, b)) :
    {U32.xor(_, p) == U32.xor(a, b) : U32}
  %Equal.sym(U32, U32.xor(U32.xor(U32.xor(a, b), p), p), U32.xor(U32.xor(a, b), U32.xor(p, p)),
    ux_assoc(U32.xor(a, b), p, p)) : {_ == U32.xor(a, b) : U32}
  %Equal.sym(U32, U32.xor(p, p), U32{Word.zero(32n)}, ux_self(p)) :
    {U32.xor(U32.xor(a, b), _) == U32.xor(a, b) : U32}
  %ux_comm(U32{Word.zero(32n)}, U32.xor(a, b)) : {_ == U32.xor(a, b) : U32}
  ux_zero(U32.xor(a, b))

# one CRC bit of a ^ b is the bit of a ^ the bit of b: the step is linear
def lin(+a: Bool, +b: Bool, +s: Word(31n), +t: Word(31n)) ->
  {cbit(Bool.xor(a, b), Word.xor(31n, s, t)) == U32.xor(cbit(a, s), cbit(b, t)) : U32}:
  match a b:
    case False{} False{}:
      sh_x(s, t)
    case True{} False{}:
      %Equal.sym(U32, shr1(Word.xor(31n, s, t)), U32.xor(shr1(s), shr1(t)), sh_x(s, t)) :
        {U32.xor(_, D.POLY()) == U32.xor(U32.xor(shr1(s), D.POLY()), shr1(t)) : U32}
      Equal.sym(U32, U32.xor(U32.xor(shr1(s), D.POLY()), shr1(t)),
        U32.xor(U32.xor(shr1(s), shr1(t)), D.POLY()), ux_swap(shr1(s), D.POLY(), shr1(t)))
    case False{} True{}:
      %Equal.sym(U32, shr1(Word.xor(31n, s, t)), U32.xor(shr1(s), shr1(t)), sh_x(s, t)) :
        {U32.xor(_, D.POLY()) == U32.xor(shr1(s), U32.xor(shr1(t), D.POLY())) : U32}
      ux_assoc(shr1(s), shr1(t), D.POLY())
    case True{} True{}:
      %Equal.sym(U32, shr1(Word.xor(31n, s, t)), U32.xor(shr1(s), shr1(t)), sh_x(s, t)) :
        {_ == U32.xor(U32.xor(shr1(s), D.POLY()), U32.xor(shr1(t), D.POLY())) : U32}
      Equal.sym(U32, U32.xor(U32.xor(shr1(s), D.POLY()), U32.xor(shr1(t), D.POLY())),
        U32.xor(shr1(s), shr1(t)), ux_cancel(shr1(s), D.POLY(), shr1(t)))

def bit_lin(+x: U32, +y: U32) ->
  {D.crc.bit(U32.xor(x, y)) == U32.xor(D.crc.bit(x), D.crc.bit(y)) : U32}:
  match x y:
    case U32{WCon{+a, +s}} U32{WCon{+b, +t}}:
      %Equal.sym(U32, D.crc.bit(U32{WCon{Bool.xor(a, b), Word.xor(31n, s, t)}}),
        cbit(Bool.xor(a, b), Word.xor(31n, s, t)), bitc(Bool.xor(a, b), Word.xor(31n, s, t))) :
        {_ == U32.xor(D.crc.bit(U32{WCon{a, s}}), D.crc.bit(U32{WCon{b, t}})) : U32}
      %Equal.sym(U32, D.crc.bit(U32{WCon{a, s}}), cbit(a, s), bitc(a, s)) :
        {cbit(Bool.xor(a, b), Word.xor(31n, s, t)) == U32.xor(_, D.crc.bit(U32{WCon{b, t}})) : U32}
      %Equal.sym(U32, D.crc.bit(U32{WCon{b, t}}), cbit(b, t), bitc(b, t)) :
        {cbit(Bool.xor(a, b), Word.xor(31n, s, t)) == U32.xor(cbit(a, s), _) : U32}
      lin(a, b, s, t)

def bits_lin(+n: Nat, +x: U32, +y: U32) ->
  {D.crc.bits(n, U32.xor(x, y)) == U32.xor(D.crc.bits(n, x), D.crc.bits(n, y)) : U32}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(U32, D.crc.bit(U32.xor(x, y)), U32.xor(D.crc.bit(x), D.crc.bit(y)), bit_lin(x, y)) :
        {D.crc.bits(p, _) == U32.xor(D.crc.bits(p, D.crc.bit(x)), D.crc.bits(p, D.crc.bit(y))) : U32}
      bits_lin(p, D.crc.bit(x), D.crc.bit(y))

def bx_f(+a: Bool) -> {Bool.xor(a, False{}) == a : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def band_t(+a: Bool) -> {Bool.and(a, True{}) == a : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

# the low byte of a word, and the rest
def lo(z0: Bool, z1: Bool, z2: Bool, z3: Bool, z4: Bool, z5: Bool, z6: Bool, z7: Bool) -> U32:
  U32{WCon{z0, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WCon{z6, WCon{z7, Word.zero(24n)}}}}}}}}}

def hi(+r: Word(24n)) -> U32:
  U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, r}}}}}}}}}

def split(+z0: Bool, +z1: Bool, +z2: Bool, +z3: Bool, +z4: Bool, +z5: Bool, +z6: Bool, +z7: Bool, +r: Word(24n)) ->
  {U32.xor(lo(z0, z1, z2, z3, z4, z5, z6, z7), hi(r)) == U32{WCon{z0, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WCon{z6, WCon{z7, r}}}}}}}}} : U32}:
  Equal.cong(Word(32n), U32, w => U32{w}, WCon{Bool.xor(z0, False{}), WCon{Bool.xor(z1, False{}), WCon{Bool.xor(z2, False{}), WCon{Bool.xor(z3, False{}), WCon{Bool.xor(z4, False{}), WCon{Bool.xor(z5, False{}), WCon{Bool.xor(z6, False{}), WCon{Bool.xor(z7, False{}), Word.xor(24n, Word.zero(24n), r)}}}}}}}}, WCon{z0, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WCon{z6, WCon{z7, r}}}}}}}},
    wcon_eq(31n, Bool.xor(z0, False{}), z0, WCon{Bool.xor(z1, False{}), WCon{Bool.xor(z2, False{}), WCon{Bool.xor(z3, False{}), WCon{Bool.xor(z4, False{}), WCon{Bool.xor(z5, False{}), WCon{Bool.xor(z6, False{}), WCon{Bool.xor(z7, False{}), Word.xor(24n, Word.zero(24n), r)}}}}}}}, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WCon{z6, WCon{z7, r}}}}}}}, bx_f(z0), wcon_eq(30n, Bool.xor(z1, False{}), z1, WCon{Bool.xor(z2, False{}), WCon{Bool.xor(z3, False{}), WCon{Bool.xor(z4, False{}), WCon{Bool.xor(z5, False{}), WCon{Bool.xor(z6, False{}), WCon{Bool.xor(z7, False{}), Word.xor(24n, Word.zero(24n), r)}}}}}}, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WCon{z6, WCon{z7, r}}}}}}, bx_f(z1), wcon_eq(29n, Bool.xor(z2, False{}), z2, WCon{Bool.xor(z3, False{}), WCon{Bool.xor(z4, False{}), WCon{Bool.xor(z5, False{}), WCon{Bool.xor(z6, False{}), WCon{Bool.xor(z7, False{}), Word.xor(24n, Word.zero(24n), r)}}}}}, WCon{z3, WCon{z4, WCon{z5, WCon{z6, WCon{z7, r}}}}}, bx_f(z2), wcon_eq(28n, Bool.xor(z3, False{}), z3, WCon{Bool.xor(z4, False{}), WCon{Bool.xor(z5, False{}), WCon{Bool.xor(z6, False{}), WCon{Bool.xor(z7, False{}), Word.xor(24n, Word.zero(24n), r)}}}}, WCon{z4, WCon{z5, WCon{z6, WCon{z7, r}}}}, bx_f(z3), wcon_eq(27n, Bool.xor(z4, False{}), z4, WCon{Bool.xor(z5, False{}), WCon{Bool.xor(z6, False{}), WCon{Bool.xor(z7, False{}), Word.xor(24n, Word.zero(24n), r)}}}, WCon{z5, WCon{z6, WCon{z7, r}}}, bx_f(z4), wcon_eq(26n, Bool.xor(z5, False{}), z5, WCon{Bool.xor(z6, False{}), WCon{Bool.xor(z7, False{}), Word.xor(24n, Word.zero(24n), r)}}, WCon{z6, WCon{z7, r}}, bx_f(z5), wcon_eq(25n, Bool.xor(z6, False{}), z6, WCon{Bool.xor(z7, False{}), Word.xor(24n, Word.zero(24n), r)}, WCon{z7, r}, bx_f(z6), wcon_eq(24n, Bool.xor(z7, False{}), z7, Word.xor(24n, Word.zero(24n), r), r, bx_f(z7), x_zero(24n, r))))))))))

def low(+z0: Bool, +z1: Bool, +z2: Bool, +z3: Bool, +z4: Bool, +z5: Bool, +z6: Bool, +z7: Bool, +r: Word(24n)) ->
  {U32.and(U32{WCon{z0, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WCon{z6, WCon{z7, r}}}}}}}}}, 255) == lo(z0, z1, z2, z3, z4, z5, z6, z7) : U32}:
  Equal.cong(Word(32n), U32, w => U32{w}, WCon{Bool.and(z0, True{}), WCon{Bool.and(z1, True{}), WCon{Bool.and(z2, True{}), WCon{Bool.and(z3, True{}), WCon{Bool.and(z4, True{}), WCon{Bool.and(z5, True{}), WCon{Bool.and(z6, True{}), WCon{Bool.and(z7, True{}), Word.and(24n, r, Word.zero(24n))}}}}}}}}, WCon{z0, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WCon{z6, WCon{z7, Word.zero(24n)}}}}}}}},
    wcon_eq(31n, Bool.and(z0, True{}), z0, WCon{Bool.and(z1, True{}), WCon{Bool.and(z2, True{}), WCon{Bool.and(z3, True{}), WCon{Bool.and(z4, True{}), WCon{Bool.and(z5, True{}), WCon{Bool.and(z6, True{}), WCon{Bool.and(z7, True{}), Word.and(24n, r, Word.zero(24n))}}}}}}}, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WCon{z6, WCon{z7, Word.zero(24n)}}}}}}}, band_t(z0), wcon_eq(30n, Bool.and(z1, True{}), z1, WCon{Bool.and(z2, True{}), WCon{Bool.and(z3, True{}), WCon{Bool.and(z4, True{}), WCon{Bool.and(z5, True{}), WCon{Bool.and(z6, True{}), WCon{Bool.and(z7, True{}), Word.and(24n, r, Word.zero(24n))}}}}}}, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WCon{z6, WCon{z7, Word.zero(24n)}}}}}}, band_t(z1), wcon_eq(29n, Bool.and(z2, True{}), z2, WCon{Bool.and(z3, True{}), WCon{Bool.and(z4, True{}), WCon{Bool.and(z5, True{}), WCon{Bool.and(z6, True{}), WCon{Bool.and(z7, True{}), Word.and(24n, r, Word.zero(24n))}}}}}, WCon{z3, WCon{z4, WCon{z5, WCon{z6, WCon{z7, Word.zero(24n)}}}}}, band_t(z2), wcon_eq(28n, Bool.and(z3, True{}), z3, WCon{Bool.and(z4, True{}), WCon{Bool.and(z5, True{}), WCon{Bool.and(z6, True{}), WCon{Bool.and(z7, True{}), Word.and(24n, r, Word.zero(24n))}}}}, WCon{z4, WCon{z5, WCon{z6, WCon{z7, Word.zero(24n)}}}}, band_t(z3), wcon_eq(27n, Bool.and(z4, True{}), z4, WCon{Bool.and(z5, True{}), WCon{Bool.and(z6, True{}), WCon{Bool.and(z7, True{}), Word.and(24n, r, Word.zero(24n))}}}, WCon{z5, WCon{z6, WCon{z7, Word.zero(24n)}}}, band_t(z4), wcon_eq(26n, Bool.and(z5, True{}), z5, WCon{Bool.and(z6, True{}), WCon{Bool.and(z7, True{}), Word.and(24n, r, Word.zero(24n))}}, WCon{z6, WCon{z7, Word.zero(24n)}}, band_t(z5), wcon_eq(25n, Bool.and(z6, True{}), z6, WCon{Bool.and(z7, True{}), Word.and(24n, r, Word.zero(24n))}, WCon{z7, Word.zero(24n)}, band_t(z6), wcon_eq(24n, Bool.and(z7, True{}), z7, Word.and(24n, r, Word.zero(24n)), Word.zero(24n), band_t(z7), and_zero(24n, r))))))))))

def hi8(+r: Word(24n), +z0: Bool, +z1: Bool, +z2: Bool, +z3: Bool, +z4: Bool, +z5: Bool, +z6: Bool, +z7: Bool) ->
  {D.crc.bits(8n, hi(r)) == U32.shrn(U32{WCon{z0, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WCon{z6, WCon{z7, r}}}}}}}}}, 8n) : U32}:
  %Equal.sym(U32, D.crc.bit(U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, r}}}}}}}}}), U32{Word.shr.pad(31n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, r}}}}}}})}, bitc(False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, r}}}}}}})) :
    {D.crc.bits(7n, _) == U32.shrn(U32{WCon{z0, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WCon{z6, WCon{z7, r}}}}}}}}}, 8n) : U32}
  %Equal.sym(U32, D.crc.bit(U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, Word.shr.pad(24n, r)}}}}}}}}), U32{Word.shr.pad(31n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, Word.shr.pad(24n, r)}}}}}})}, bitc(False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, Word.shr.pad(24n, r)}}}}}})) :
    {D.crc.bits(6n, _) == U32.shrn(U32{WCon{z0, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WCon{z6, WCon{z7, r}}}}}}}}}, 8n) : U32}
  %Equal.sym(U32, D.crc.bit(U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, Word.shr.pad(25n, Word.shr.pad(24n, r))}}}}}}}), U32{Word.shr.pad(31n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, Word.shr.pad(25n, Word.shr.pad(24n, r))}}}}})}, bitc(False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, Word.shr.pad(25n, Word.shr.pad(24n, r))}}}}})) :
    {D.crc.bits(5n, _) == U32.shrn(U32{WCon{z0, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WCon{z6, WCon{z7, r}}}}}}}}}, 8n) : U32}
  %Equal.sym(U32, D.crc.bit(U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, Word.shr.pad(26n, Word.shr.pad(25n, Word.shr.pad(24n, r)))}}}}}}), U32{Word.shr.pad(31n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, Word.shr.pad(26n, Word.shr.pad(25n, Word.shr.pad(24n, r)))}}}})}, bitc(False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, Word.shr.pad(26n, Word.shr.pad(25n, Word.shr.pad(24n, r)))}}}})) :
    {D.crc.bits(4n, _) == U32.shrn(U32{WCon{z0, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WCon{z6, WCon{z7, r}}}}}}}}}, 8n) : U32}
  %Equal.sym(U32, D.crc.bit(U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, Word.shr.pad(27n, Word.shr.pad(26n, Word.shr.pad(25n, Word.shr.pad(24n, r))))}}}}}), U32{Word.shr.pad(31n, WCon{False{}, WCon{False{}, WCon{False{}, Word.shr.pad(27n, Word.shr.pad(26n, Word.shr.pad(25n, Word.shr.pad(24n, r))))}}})}, bitc(False{}, WCon{False{}, WCon{False{}, WCon{False{}, Word.shr.pad(27n, Word.shr.pad(26n, Word.shr.pad(25n, Word.shr.pad(24n, r))))}}})) :
    {D.crc.bits(3n, _) == U32.shrn(U32{WCon{z0, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WCon{z6, WCon{z7, r}}}}}}}}}, 8n) : U32}
  %Equal.sym(U32, D.crc.bit(U32{WCon{False{}, WCon{False{}, WCon{False{}, Word.shr.pad(28n, Word.shr.pad(27n, Word.shr.pad(26n, Word.shr.pad(25n, Word.shr.pad(24n, r)))))}}}}), U32{Word.shr.pad(31n, WCon{False{}, WCon{False{}, Word.shr.pad(28n, Word.shr.pad(27n, Word.shr.pad(26n, Word.shr.pad(25n, Word.shr.pad(24n, r)))))}})}, bitc(False{}, WCon{False{}, WCon{False{}, Word.shr.pad(28n, Word.shr.pad(27n, Word.shr.pad(26n, Word.shr.pad(25n, Word.shr.pad(24n, r)))))}})) :
    {D.crc.bits(2n, _) == U32.shrn(U32{WCon{z0, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WCon{z6, WCon{z7, r}}}}}}}}}, 8n) : U32}
  %Equal.sym(U32, D.crc.bit(U32{WCon{False{}, WCon{False{}, Word.shr.pad(29n, Word.shr.pad(28n, Word.shr.pad(27n, Word.shr.pad(26n, Word.shr.pad(25n, Word.shr.pad(24n, r))))))}}}), U32{Word.shr.pad(31n, WCon{False{}, Word.shr.pad(29n, Word.shr.pad(28n, Word.shr.pad(27n, Word.shr.pad(26n, Word.shr.pad(25n, Word.shr.pad(24n, r))))))})}, bitc(False{}, WCon{False{}, Word.shr.pad(29n, Word.shr.pad(28n, Word.shr.pad(27n, Word.shr.pad(26n, Word.shr.pad(25n, Word.shr.pad(24n, r))))))})) :
    {D.crc.bits(1n, _) == U32.shrn(U32{WCon{z0, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WCon{z6, WCon{z7, r}}}}}}}}}, 8n) : U32}
  %Equal.sym(U32, D.crc.bit(U32{WCon{False{}, Word.shr.pad(30n, Word.shr.pad(29n, Word.shr.pad(28n, Word.shr.pad(27n, Word.shr.pad(26n, Word.shr.pad(25n, Word.shr.pad(24n, r)))))))}}), U32{Word.shr.pad(31n, Word.shr.pad(30n, Word.shr.pad(29n, Word.shr.pad(28n, Word.shr.pad(27n, Word.shr.pad(26n, Word.shr.pad(25n, Word.shr.pad(24n, r))))))))}, bitc(False{}, Word.shr.pad(30n, Word.shr.pad(29n, Word.shr.pad(28n, Word.shr.pad(27n, Word.shr.pad(26n, Word.shr.pad(25n, Word.shr.pad(24n, r))))))))) :
    {D.crc.bits(0n, _) == U32.shrn(U32{WCon{z0, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WCon{z6, WCon{z7, r}}}}}}}}}, 8n) : U32}
  {==}


# the table's cell at each byte is the byte's eight CRC bits
def tab(+z0: Bool, +z1: Bool, +z2: Bool, +z3: Bool, +z4: Bool, +z5: Bool, +z6: Bool, +z7: Bool) ->
  {D.crc.cell(D.crc.tab(), lo(z0, z1, z2, z3, z4, z5, z6, z7)) == D.crc.entry(lo(z0, z1, z2, z3, z4, z5, z6, z7)) : U32}:
  match z0 z1 z2 z3 z4 z5 z6 z7:
    case False{} False{} False{} False{} False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} False{} False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} False{} False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} False{} False{} False{} True{} True{}:
      {==}
    case False{} False{} False{} False{} False{} True{} False{} False{}:
      {==}
    case False{} False{} False{} False{} False{} True{} False{} True{}:
      {==}
    case False{} False{} False{} False{} False{} True{} True{} False{}:
      {==}
    case False{} False{} False{} False{} False{} True{} True{} True{}:
      {==}
    case False{} False{} False{} False{} True{} False{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{} False{} False{} True{}:
      {==}
    case False{} False{} False{} False{} True{} False{} True{} False{}:
      {==}
    case False{} False{} False{} False{} True{} False{} True{} True{}:
      {==}
    case False{} False{} False{} False{} True{} True{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{} True{} False{} True{}:
      {==}
    case False{} False{} False{} False{} True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} False{} True{} True{} True{} True{}:
      {==}
    case False{} False{} False{} True{} False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{} False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{} False{} False{} True{} True{}:
      {==}
    case False{} False{} False{} True{} False{} True{} False{} False{}:
      {==}
    case False{} False{} False{} True{} False{} True{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{} False{} True{} True{} True{}:
      {==}
    case False{} False{} False{} True{} True{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{} True{} False{} False{} True{}:
      {==}
    case False{} False{} False{} True{} True{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{} True{} False{} True{} True{}:
      {==}
    case False{} False{} False{} True{} True{} True{} False{} False{}:
      {==}
    case False{} False{} False{} True{} True{} True{} False{} True{}:
      {==}
    case False{} False{} False{} True{} True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{} True{} True{} True{} True{}:
      {==}
    case False{} False{} True{} False{} False{} False{} False{} False{}:
      {==}
    case False{} False{} True{} False{} False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{} False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} False{} False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} False{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} False{} False{} True{} True{} True{}:
      {==}
    case False{} False{} True{} False{} True{} False{} False{} False{}:
      {==}
    case False{} False{} True{} False{} True{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{} True{} False{} True{} False{}:
      {==}
    case False{} False{} True{} False{} True{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{} True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{} True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} False{} True{} True{} True{} False{}:
      {==}
    case False{} False{} True{} False{} True{} True{} True{} True{}:
      {==}
    case False{} False{} True{} True{} False{} False{} False{} False{}:
      {==}
    case False{} False{} True{} True{} False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{} False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} True{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} True{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} True{} False{} True{} True{} True{}:
      {==}
    case False{} False{} True{} True{} True{} False{} False{} False{}:
      {==}
    case False{} False{} True{} True{} True{} False{} False{} True{}:
      {==}
    case False{} False{} True{} True{} True{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{} True{} False{} True{} True{}:
      {==}
    case False{} False{} True{} True{} True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} True{} True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} True{} True{} True{} False{}:
      {==}
    case False{} False{} True{} True{} True{} True{} True{} True{}:
      {==}
    case False{} True{} False{} False{} False{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} False{} False{} False{} True{}:
      {==}
    case False{} True{} False{} False{} False{} False{} True{} False{}:
      {==}
    case False{} True{} False{} False{} False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{} False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} False{} False{} True{} False{} True{}:
      {==}
    case False{} True{} False{} False{} False{} True{} True{} False{}:
      {==}
    case False{} True{} False{} False{} False{} True{} True{} True{}:
      {==}
    case False{} True{} False{} False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} False{} False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} False{} False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} False{} False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} False{} False{} True{} True{} True{} True{}:
      {==}
    case False{} True{} False{} True{} False{} False{} False{} False{}:
      {==}
    case False{} True{} False{} True{} False{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{} False{} True{} False{}:
      {==}
    case False{} True{} False{} True{} False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} True{} False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{} False{} True{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{} True{} True{} False{}:
      {==}
    case False{} True{} False{} True{} False{} True{} True{} True{}:
      {==}
    case False{} True{} False{} True{} True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} True{} True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{} True{} False{} True{} False{}:
      {==}
    case False{} True{} False{} True{} True{} False{} True{} True{}:
      {==}
    case False{} True{} False{} True{} True{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{} True{} True{} False{} True{}:
      {==}
    case False{} True{} False{} True{} True{} True{} True{} False{}:
      {==}
    case False{} True{} False{} True{} True{} True{} True{} True{}:
      {==}
    case False{} True{} True{} False{} False{} False{} False{} False{}:
      {==}
    case False{} True{} True{} False{} False{} False{} False{} True{}:
      {==}
    case False{} True{} True{} False{} False{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{} False{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} False{} True{} False{} False{}:
      {==}
    case False{} True{} True{} False{} False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{} False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} False{} False{} True{} True{} True{}:
      {==}
    case False{} True{} True{} False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} True{} False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} True{} False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} False{} True{} True{} True{} True{}:
      {==}
    case False{} True{} True{} True{} False{} False{} False{} False{}:
      {==}
    case False{} True{} True{} True{} False{} False{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{} False{} True{} False{}:
      {==}
    case False{} True{} True{} True{} False{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{} False{} True{} False{} False{}:
      {==}
    case False{} True{} True{} True{} False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} False{} True{} True{} True{}:
      {==}
    case False{} True{} True{} True{} True{} False{} False{} False{}:
      {==}
    case False{} True{} True{} True{} True{} False{} False{} True{}:
      {==}
    case False{} True{} True{} True{} True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} True{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} True{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} True{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{} False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} False{} False{} False{} True{} True{}:
      {==}
    case True{} False{} False{} False{} False{} True{} False{} False{}:
      {==}
    case True{} False{} False{} False{} False{} True{} False{} True{}:
      {==}
    case True{} False{} False{} False{} False{} True{} True{} False{}:
      {==}
    case True{} False{} False{} False{} False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{} True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{} True{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{} True{} False{} True{} False{}:
      {==}
    case True{} False{} False{} False{} True{} False{} True{} True{}:
      {==}
    case True{} False{} False{} False{} True{} True{} False{} False{}:
      {==}
    case True{} False{} False{} False{} True{} True{} False{} True{}:
      {==}
    case True{} False{} False{} False{} True{} True{} True{} False{}:
      {==}
    case True{} False{} False{} False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} False{} True{} False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{} False{} False{} True{} True{}:
      {==}
    case True{} False{} False{} True{} False{} True{} False{} False{}:
      {==}
    case True{} False{} False{} True{} False{} True{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{} True{} True{} False{}:
      {==}
    case True{} False{} False{} True{} False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} True{} True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{} True{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{} True{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{} True{} False{} True{} True{}:
      {==}
    case True{} False{} False{} True{} True{} True{} False{} False{}:
      {==}
    case True{} False{} False{} True{} True{} True{} False{} True{}:
      {==}
    case True{} False{} False{} True{} True{} True{} True{} False{}:
      {==}
    case True{} False{} False{} True{} True{} True{} True{} True{}:
      {==}
    case True{} False{} True{} False{} False{} False{} False{} False{}:
      {==}
    case True{} False{} True{} False{} False{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{} False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{} False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} False{} True{} False{} False{}:
      {==}
    case True{} False{} True{} False{} False{} True{} False{} True{}:
      {==}
    case True{} False{} True{} False{} False{} True{} True{} False{}:
      {==}
    case True{} False{} True{} False{} False{} True{} True{} True{}:
      {==}
    case True{} False{} True{} False{} True{} False{} False{} False{}:
      {==}
    case True{} False{} True{} False{} True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{} True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{} True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} True{} True{} False{} False{}:
      {==}
    case True{} False{} True{} False{} True{} True{} False{} True{}:
      {==}
    case True{} False{} True{} False{} True{} True{} True{} False{}:
      {==}
    case True{} False{} True{} False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} True{} True{} False{} False{} False{} False{}:
      {==}
    case True{} False{} True{} True{} False{} False{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{} False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{} False{} True{} False{} False{}:
      {==}
    case True{} False{} True{} True{} False{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} False{} True{} True{} True{}:
      {==}
    case True{} False{} True{} True{} True{} False{} False{} False{}:
      {==}
    case True{} False{} True{} True{} True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} True{} True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{} True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{} True{} True{} False{} False{}:
      {==}
    case True{} False{} True{} True{} True{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} True{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} True{} True{} True{} True{}:
      {==}
    case True{} True{} False{} False{} False{} False{} False{} False{}:
      {==}
    case True{} True{} False{} False{} False{} False{} False{} True{}:
      {==}
    case True{} True{} False{} False{} False{} False{} True{} False{}:
      {==}
    case True{} True{} False{} False{} False{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{} False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{} False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} False{} False{} True{} True{} False{}:
      {==}
    case True{} True{} False{} False{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} False{} True{} False{} False{} False{}:
      {==}
    case True{} True{} False{} False{} True{} False{} False{} True{}:
      {==}
    case True{} True{} False{} False{} True{} False{} True{} False{}:
      {==}
    case True{} True{} False{} False{} True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{} True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{} True{} True{} False{} True{}:
      {==}
    case True{} True{} False{} False{} True{} True{} True{} False{}:
      {==}
    case True{} True{} False{} False{} True{} True{} True{} True{}:
      {==}
    case True{} True{} False{} True{} False{} False{} False{} False{}:
      {==}
    case True{} True{} False{} True{} False{} False{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{} False{} True{} False{}:
      {==}
    case True{} True{} False{} True{} False{} False{} True{} True{}:
      {==}
    case True{} True{} False{} True{} False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{} False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{} True{} True{} False{}:
      {==}
    case True{} True{} False{} True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} True{} True{} False{} False{} False{}:
      {==}
    case True{} True{} False{} True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} False{} True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} False{} True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} False{} True{} True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} False{} False{} False{} False{} False{}:
      {==}
    case True{} True{} True{} False{} False{} False{} False{} True{}:
      {==}
    case True{} True{} True{} False{} False{} False{} True{} False{}:
      {==}
    case True{} True{} True{} False{} False{} False{} True{} True{}:
      {==}
    case True{} True{} True{} False{} False{} True{} False{} False{}:
      {==}
    case True{} True{} True{} False{} False{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{} False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{} False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} False{} True{} False{} False{} False{}:
      {==}
    case True{} True{} True{} False{} True{} False{} False{} True{}:
      {==}
    case True{} True{} True{} False{} True{} False{} True{} False{}:
      {==}
    case True{} True{} True{} False{} True{} False{} True{} True{}:
      {==}
    case True{} True{} True{} False{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} False{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{} True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{} False{} False{} False{} False{}:
      {==}
    case True{} True{} True{} True{} False{} False{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{} False{} True{} False{}:
      {==}
    case True{} True{} True{} True{} False{} False{} True{} True{}:
      {==}
    case True{} True{} True{} True{} False{} True{} False{} False{}:
      {==}
    case True{} True{} True{} True{} False{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{} True{} False{} False{} False{}:
      {==}
    case True{} True{} True{} True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} True{} True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} True{} True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} True{} True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} True{} True{} True{} True{}:
      {==}

def zz(z0: Bool, z1: Bool, z2: Bool, z3: Bool, z4: Bool, z5: Bool, z6: Bool, z7: Bool,
  r: Word(24n)) -> U32:
  U32{WCon{z0, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WCon{z6, WCon{z7, r}}}}}}}}}

# a byte by the table is the byte a bit at a time: z is its low byte and
# the rest; the table gives the low byte's eight bits, and since the
# step is linear the rest's eight bits are the rest shifted
# (tb, a table right at every byte, as crc.tab is by tab)
def byte_z(+tb: Bytes(), h: @+z0: Bool -> @+z1: Bool -> @+z2: Bool -> @+z3: Bool -> @+z4: Bool ->
  @+z5: Bool -> @+z6: Bool -> @+z7: Bool ->
  {D.crc.cell(tb, lo(z0, z1, z2, z3, z4, z5, z6, z7)) == D.crc.entry(lo(z0, z1, z2, z3, z4, z5, z6, z7)) : U32},
  +z: U32) -> {D.crc.byte.z(tb, z) == D.crc.bits(8n, z) : U32}:
  match z:
    case U32{WCon{+z0, WCon{+z1, WCon{+z2, WCon{+z3, WCon{+z4, WCon{+z5, WCon{+z6, WCon{+z7, +r}}}}}}}}}:
      +w = zz(z0, z1, z2, z3, z4, z5, z6, z7, r)
      +l = lo(z0, z1, z2, z3, z4, z5, z6, z7)
      %Equal.sym(U32, U32.and(w, 255), l, low(z0, z1, z2, z3, z4, z5, z6, z7, r)) :
        {U32.xor(D.crc.cell(tb, _), U32.shrn(w, 8n)) == D.crc.bits(8n, w) : U32}
      %Equal.sym(U32, D.crc.cell(tb, l), D.crc.entry(l), h(z0, z1, z2, z3, z4, z5, z6, z7)) :
        {U32.xor(_, U32.shrn(w, 8n)) == D.crc.bits(8n, w) : U32}
      %split(z0, z1, z2, z3, z4, z5, z6, z7, r) :
        {U32.xor(D.crc.entry(l), U32.shrn(w, 8n)) == D.crc.bits(8n, _) : U32}
      %Equal.sym(U32, D.crc.bits(8n, U32.xor(l, hi(r))), U32.xor(D.crc.bits(8n, l), D.crc.bits(8n, hi(r))),
        bits_lin(8n, l, hi(r))) :
        {U32.xor(D.crc.entry(l), U32.shrn(w, 8n)) == _ : U32}
      %Equal.sym(U32, D.crc.bits(8n, hi(r)), U32.shrn(w, 8n), hi8(r, z0, z1, z2, z3, z4, z5, z6, z7)) :
        {U32.xor(D.crc.entry(l), U32.shrn(w, 8n)) == U32.xor(D.crc.bits(8n, l), _) : U32}
      {==}

# the table's CRC is the bit-at-a-time CRC, for every input and start
def run_spec(+x: Bytes(), +c: U32) -> {D.crc.run(x, D.crc.tab(), c) == Laws.crc_ref(x, c) : U32}:
  match x:
    case SNil{}:
      {==}
    case SCon{Chr{+b}, +t}:
      %Equal.sym(U32, D.crc.byte.z(D.crc.tab(), U32.xor(c, U32.and(b, 255))),
        D.crc.bits(8n, U32.xor(c, U32.and(b, 255))), byte_z(D.crc.tab(), tab, U32.xor(c, U32.and(b, 255)))) :
        {D.crc.run(t, D.crc.tab(), _) == Laws.crc_ref(t, D.crc.bits(8n, U32.xor(c, U32.and(b, 255)))) : U32}
      run_spec(t, D.crc.bits(8n, U32.xor(c, U32.and(b, 255))))

def Laws.crc32_ref(x, prev):
  %Equal.sym(U32, D.crc.run(x, D.crc.tab(), U32.not(prev)), Laws.crc_ref(x, U32.not(prev)),
    run_spec(x, U32.not(prev))) : {U32.not(_) == U32.not(Laws.crc_ref(x, U32.not(prev))) : U32}
  {==}

# The stored round trip
# =====================
#
# deflate(x, 0) writes x as stored blocks of 65535 bytes and one of the
# rest; the proof runs both machines over bits. wbits is what the bit
# writer holds (its whole bytes, then its pending bits), bitsof what a
# stream is, bit by bit as the reader takes it; bfeed is the inflate
# machine a bit at a time, which feeding a byte is (feed_bits). A block
# written at a byte (stored_bits) is its header, LEN and NLEN from its
# count's bits, and its bytes; read at a header (block) it lands at the
# next header with the bytes out, the count read back as the length,
# NLEN as its complement, every byte as itself (byte_back) and each
# under the cap. run strings the blocks together.

# Numbers
# -------

def add_zero(+a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, 0n), p, add_zero(p))

def add_succ(+a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, 1n+b), 1n+Nat.add(p, b), add_succ(p, b))

def lt_one(+x: Nat) -> {Nat.is_lt(x, 1n) == True{} : Bool} -> {x == 0n : Nat}:
  match x:
    case 0n:
      e => {==}
    case 1n+p:
      match p:
        case 0n:
          e => Bool.no({1n == 0n : Nat}, e)
        case 1n+q:
          e => Bool.no({2n+q == 0n : Nat}, e)

# the bits of a number from high first, after v
def V(bs: List<&2, Bool>, +v: Nat) -> Nat:
  match bs:
    case Nil{}:
      v
    case Con{b, t}:
      Nat.bit(b, V(t, v))

def V_val(+bs: List<&2, Bool>) -> {V(bs, 0n) == D.val(bs) : Nat}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      Equal.cong(Nat, Nat, x => Nat.bit(b, x), V(t, 0n), D.val(t), V_val(t))

def hval_rev.go(+bs: List<&2, Bool>, +a: List<&2, Bool>, +v: Nat) ->
  {D.hval(D.revapp(bs, a), v) == D.hval(a, V(bs, v)) : Nat}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      hval_rev.go(t, Con{b, a}, v)

# what the reader collects, newest first, read back
def hval_rev(+bs: List<&2, Bool>) -> {D.hval(D.revapp(bs, Nil{}), 0n) == D.val(bs) : Nat}:
  Equal.trans(Nat, D.hval(D.revapp(bs, Nil{}), 0n), V(bs, 0n), D.val(bs), hval_rev.go(bs, Nil{}, 0n),
    V_val(bs))

# a byte made of eight bits gives them back, low first
def unbyte_of(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool) ->
  {D.unbyte(D.byte_of([b7, b6, b5, b4, b3, b2, b1, b0])) == [b0, b1, b2, b3, b4, b5, b6, b7] : List<&2, Bool>}:
  match b0 b1 b2 b3 b4 b5 b6 b7:
    case False{} False{} False{} False{} False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} False{} False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} False{} False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} False{} False{} False{} True{} True{}:
      {==}
    case False{} False{} False{} False{} False{} True{} False{} False{}:
      {==}
    case False{} False{} False{} False{} False{} True{} False{} True{}:
      {==}
    case False{} False{} False{} False{} False{} True{} True{} False{}:
      {==}
    case False{} False{} False{} False{} False{} True{} True{} True{}:
      {==}
    case False{} False{} False{} False{} True{} False{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{} False{} False{} True{}:
      {==}
    case False{} False{} False{} False{} True{} False{} True{} False{}:
      {==}
    case False{} False{} False{} False{} True{} False{} True{} True{}:
      {==}
    case False{} False{} False{} False{} True{} True{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{} True{} False{} True{}:
      {==}
    case False{} False{} False{} False{} True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} False{} True{} True{} True{} True{}:
      {==}
    case False{} False{} False{} True{} False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{} False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{} False{} False{} True{} True{}:
      {==}
    case False{} False{} False{} True{} False{} True{} False{} False{}:
      {==}
    case False{} False{} False{} True{} False{} True{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{} False{} True{} True{} True{}:
      {==}
    case False{} False{} False{} True{} True{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{} True{} False{} False{} True{}:
      {==}
    case False{} False{} False{} True{} True{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{} True{} False{} True{} True{}:
      {==}
    case False{} False{} False{} True{} True{} True{} False{} False{}:
      {==}
    case False{} False{} False{} True{} True{} True{} False{} True{}:
      {==}
    case False{} False{} False{} True{} True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{} True{} True{} True{} True{}:
      {==}
    case False{} False{} True{} False{} False{} False{} False{} False{}:
      {==}
    case False{} False{} True{} False{} False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{} False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} False{} False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} False{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} False{} False{} True{} True{} True{}:
      {==}
    case False{} False{} True{} False{} True{} False{} False{} False{}:
      {==}
    case False{} False{} True{} False{} True{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{} True{} False{} True{} False{}:
      {==}
    case False{} False{} True{} False{} True{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{} True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{} True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} False{} True{} True{} True{} False{}:
      {==}
    case False{} False{} True{} False{} True{} True{} True{} True{}:
      {==}
    case False{} False{} True{} True{} False{} False{} False{} False{}:
      {==}
    case False{} False{} True{} True{} False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{} False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} True{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} True{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} True{} False{} True{} True{} True{}:
      {==}
    case False{} False{} True{} True{} True{} False{} False{} False{}:
      {==}
    case False{} False{} True{} True{} True{} False{} False{} True{}:
      {==}
    case False{} False{} True{} True{} True{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{} True{} False{} True{} True{}:
      {==}
    case False{} False{} True{} True{} True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} True{} True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} True{} True{} True{} False{}:
      {==}
    case False{} False{} True{} True{} True{} True{} True{} True{}:
      {==}
    case False{} True{} False{} False{} False{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} False{} False{} False{} True{}:
      {==}
    case False{} True{} False{} False{} False{} False{} True{} False{}:
      {==}
    case False{} True{} False{} False{} False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{} False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} False{} False{} True{} False{} True{}:
      {==}
    case False{} True{} False{} False{} False{} True{} True{} False{}:
      {==}
    case False{} True{} False{} False{} False{} True{} True{} True{}:
      {==}
    case False{} True{} False{} False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} False{} False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} False{} False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} False{} False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} False{} False{} True{} True{} True{} True{}:
      {==}
    case False{} True{} False{} True{} False{} False{} False{} False{}:
      {==}
    case False{} True{} False{} True{} False{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{} False{} True{} False{}:
      {==}
    case False{} True{} False{} True{} False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} True{} False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{} False{} True{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{} True{} True{} False{}:
      {==}
    case False{} True{} False{} True{} False{} True{} True{} True{}:
      {==}
    case False{} True{} False{} True{} True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} True{} True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{} True{} False{} True{} False{}:
      {==}
    case False{} True{} False{} True{} True{} False{} True{} True{}:
      {==}
    case False{} True{} False{} True{} True{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{} True{} True{} False{} True{}:
      {==}
    case False{} True{} False{} True{} True{} True{} True{} False{}:
      {==}
    case False{} True{} False{} True{} True{} True{} True{} True{}:
      {==}
    case False{} True{} True{} False{} False{} False{} False{} False{}:
      {==}
    case False{} True{} True{} False{} False{} False{} False{} True{}:
      {==}
    case False{} True{} True{} False{} False{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{} False{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} False{} True{} False{} False{}:
      {==}
    case False{} True{} True{} False{} False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{} False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} False{} False{} True{} True{} True{}:
      {==}
    case False{} True{} True{} False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} True{} False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} True{} False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} False{} True{} True{} True{} True{}:
      {==}
    case False{} True{} True{} True{} False{} False{} False{} False{}:
      {==}
    case False{} True{} True{} True{} False{} False{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{} False{} True{} False{}:
      {==}
    case False{} True{} True{} True{} False{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{} False{} True{} False{} False{}:
      {==}
    case False{} True{} True{} True{} False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} False{} True{} True{} True{}:
      {==}
    case False{} True{} True{} True{} True{} False{} False{} False{}:
      {==}
    case False{} True{} True{} True{} True{} False{} False{} True{}:
      {==}
    case False{} True{} True{} True{} True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} True{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} True{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} True{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{} False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} False{} False{} False{} True{} True{}:
      {==}
    case True{} False{} False{} False{} False{} True{} False{} False{}:
      {==}
    case True{} False{} False{} False{} False{} True{} False{} True{}:
      {==}
    case True{} False{} False{} False{} False{} True{} True{} False{}:
      {==}
    case True{} False{} False{} False{} False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{} True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{} True{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{} True{} False{} True{} False{}:
      {==}
    case True{} False{} False{} False{} True{} False{} True{} True{}:
      {==}
    case True{} False{} False{} False{} True{} True{} False{} False{}:
      {==}
    case True{} False{} False{} False{} True{} True{} False{} True{}:
      {==}
    case True{} False{} False{} False{} True{} True{} True{} False{}:
      {==}
    case True{} False{} False{} False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} False{} True{} False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{} False{} False{} True{} True{}:
      {==}
    case True{} False{} False{} True{} False{} True{} False{} False{}:
      {==}
    case True{} False{} False{} True{} False{} True{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{} True{} True{} False{}:
      {==}
    case True{} False{} False{} True{} False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} True{} True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{} True{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{} True{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{} True{} False{} True{} True{}:
      {==}
    case True{} False{} False{} True{} True{} True{} False{} False{}:
      {==}
    case True{} False{} False{} True{} True{} True{} False{} True{}:
      {==}
    case True{} False{} False{} True{} True{} True{} True{} False{}:
      {==}
    case True{} False{} False{} True{} True{} True{} True{} True{}:
      {==}
    case True{} False{} True{} False{} False{} False{} False{} False{}:
      {==}
    case True{} False{} True{} False{} False{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{} False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{} False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} False{} True{} False{} False{}:
      {==}
    case True{} False{} True{} False{} False{} True{} False{} True{}:
      {==}
    case True{} False{} True{} False{} False{} True{} True{} False{}:
      {==}
    case True{} False{} True{} False{} False{} True{} True{} True{}:
      {==}
    case True{} False{} True{} False{} True{} False{} False{} False{}:
      {==}
    case True{} False{} True{} False{} True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{} True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{} True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} True{} True{} False{} False{}:
      {==}
    case True{} False{} True{} False{} True{} True{} False{} True{}:
      {==}
    case True{} False{} True{} False{} True{} True{} True{} False{}:
      {==}
    case True{} False{} True{} False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} True{} True{} False{} False{} False{} False{}:
      {==}
    case True{} False{} True{} True{} False{} False{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{} False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{} False{} True{} False{} False{}:
      {==}
    case True{} False{} True{} True{} False{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} False{} True{} True{} True{}:
      {==}
    case True{} False{} True{} True{} True{} False{} False{} False{}:
      {==}
    case True{} False{} True{} True{} True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} True{} True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{} True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{} True{} True{} False{} False{}:
      {==}
    case True{} False{} True{} True{} True{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} True{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} True{} True{} True{} True{}:
      {==}
    case True{} True{} False{} False{} False{} False{} False{} False{}:
      {==}
    case True{} True{} False{} False{} False{} False{} False{} True{}:
      {==}
    case True{} True{} False{} False{} False{} False{} True{} False{}:
      {==}
    case True{} True{} False{} False{} False{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{} False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{} False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} False{} False{} True{} True{} False{}:
      {==}
    case True{} True{} False{} False{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} False{} True{} False{} False{} False{}:
      {==}
    case True{} True{} False{} False{} True{} False{} False{} True{}:
      {==}
    case True{} True{} False{} False{} True{} False{} True{} False{}:
      {==}
    case True{} True{} False{} False{} True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{} True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{} True{} True{} False{} True{}:
      {==}
    case True{} True{} False{} False{} True{} True{} True{} False{}:
      {==}
    case True{} True{} False{} False{} True{} True{} True{} True{}:
      {==}
    case True{} True{} False{} True{} False{} False{} False{} False{}:
      {==}
    case True{} True{} False{} True{} False{} False{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{} False{} True{} False{}:
      {==}
    case True{} True{} False{} True{} False{} False{} True{} True{}:
      {==}
    case True{} True{} False{} True{} False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{} False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{} True{} True{} False{}:
      {==}
    case True{} True{} False{} True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} True{} True{} False{} False{} False{}:
      {==}
    case True{} True{} False{} True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} False{} True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} False{} True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} False{} True{} True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} False{} False{} False{} False{} False{}:
      {==}
    case True{} True{} True{} False{} False{} False{} False{} True{}:
      {==}
    case True{} True{} True{} False{} False{} False{} True{} False{}:
      {==}
    case True{} True{} True{} False{} False{} False{} True{} True{}:
      {==}
    case True{} True{} True{} False{} False{} True{} False{} False{}:
      {==}
    case True{} True{} True{} False{} False{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{} False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{} False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} False{} True{} False{} False{} False{}:
      {==}
    case True{} True{} True{} False{} True{} False{} False{} True{}:
      {==}
    case True{} True{} True{} False{} True{} False{} True{} False{}:
      {==}
    case True{} True{} True{} False{} True{} False{} True{} True{}:
      {==}
    case True{} True{} True{} False{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} False{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{} True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{} False{} False{} False{} False{}:
      {==}
    case True{} True{} True{} True{} False{} False{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{} False{} True{} False{}:
      {==}
    case True{} True{} True{} True{} False{} False{} True{} True{}:
      {==}
    case True{} True{} True{} True{} False{} True{} False{} False{}:
      {==}
    case True{} True{} True{} True{} False{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{} True{} False{} False{} False{}:
      {==}
    case True{} True{} True{} True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} True{} True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} True{} True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} True{} True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} True{} True{} True{} True{}:
      {==}

# Bits
# ----

def app(a: List<&2, Bool>, b: List<&2, Bool>) -> List<&2, Bool>:
  List.append(&2, Bool, a, b)

def app_nil(+a: List<&2, Bool>) -> {app(a, Nil{}) == a : List<&2, Bool>}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.cong(List<&2, Bool>, List<&2, Bool>, x => Con{h, x}, app(t, Nil{}), t, app_nil(t))

def app_assoc(+a: List<&2, Bool>, +b: List<&2, Bool>, +c: List<&2, Bool>) ->
  {app(app(a, b), c) == app(a, app(b, c)) : List<&2, Bool>}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.cong(List<&2, Bool>, List<&2, Bool>, x => Con{h, x}, app(app(t, b), c), app(t, app(b, c)),
        app_assoc(t, b, c))

# the bits of a stream, each byte's low first
def bitsof(s: Bytes()) -> List<&2, Bool>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{Chr{c}, t}:
      app(D.unbyte(c), bitsof(t))

def bitsof_app(+a: Bytes(), +b: Bytes()) ->
  {bitsof(String.append(a, b)) == app(bitsof(a), bitsof(b)) : List<&2, Bool>}:
  match a:
    case SNil{}:
      {==}
    case SCon{Chr{+c}, +t}:
      %Equal.sym(List<&2, Bool>, bitsof(String.append(t, b)), app(bitsof(t), bitsof(b)), bitsof_app(t, b)) :
        {app(D.unbyte(c), _) == app(app(D.unbyte(c), bitsof(t)), bitsof(b)) : List<&2, Bool>}
      Equal.sym(List<&2, Bool>, app(app(D.unbyte(c), bitsof(t)), bitsof(b)),
        app(D.unbyte(c), app(bitsof(t), bitsof(b))), app_assoc(D.unbyte(c), bitsof(t), bitsof(b)))

def bitsof_push(+a: Bytes(), +c: U32) ->
  {bitsof(Bytes.push(a, c)) == app(bitsof(a), D.unbyte(c)) : List<&2, Bool>}:
  %Equal.sym(List<&2, Bool>, bitsof(String.append(a, SCon{Chr{c}, SNil{}})),
    app(bitsof(a), bitsof(SCon{Chr{c}, SNil{}})), bitsof_app(a, SCon{Chr{c}, SNil{}})) :
    {_ == app(bitsof(a), D.unbyte(c)) : List<&2, Bool>}
  %Equal.sym(List<&2, Bool>, app(D.unbyte(c), Nil{}), D.unbyte(c), app_nil(D.unbyte(c))) :
    {app(bitsof(a), _) == app(bitsof(a), D.unbyte(c)) : List<&2, Bool>}
  {==}

# the machine over bits
def bfeed(bs: List<&2, Bool>, st: D.St) -> D.St:
  match bs:
    case Nil{}:
      st
    case Con{b, t}:
      bfeed(t, D.bstep(st, b))

def bfeed_app(+a: List<&2, Bool>, +b: List<&2, Bool>, +st: D.St) ->
  {bfeed(app(a, b), st) == bfeed(b, bfeed(a, st)) : D.St}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      bfeed_app(t, b, D.bstep(st, h))

# a stream's bytes, fed, are its bits fed
def feed_bits(+s: Bytes(), +st: D.St) -> {D.feed_list(Bytes.to_list(s), st) == bfeed(bitsof(s), st) : D.St}:
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{+c}, +t}:
      %Equal.sym(D.St, bfeed(app(D.unbyte(c), bitsof(t)), st), bfeed(bitsof(t), bfeed(D.unbyte(c), st)),
        bfeed_app(D.unbyte(c), bitsof(t), st)) :
        {D.feed_list(Bytes.to_list(t), D.step(st, c)) == _ : D.St}
      feed_bits(t, D.step(st, c))

# The writer's bits
# -----------------

def wbits(w: D.W) -> List<&2, Bool>:
  match w:
    case D.W{out, pend}:
      app(bitsof(out), D.revapp(pend, Nil{}))

def revapp_app(+p: List<&2, Bool>, +a: List<&2, Bool>, +c: List<&2, Bool>) ->
  {D.revapp(p, app(a, c)) == app(D.revapp(p, a), c) : List<&2, Bool>}:
  match p:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      revapp_app(t, Con{h, a}, c)

# a bit onto the pending ones
def cons_bits(+out: Bytes(), +pend: List<&2, Bool>, +b: Bool) ->
  {wbits(D.W{out, Con{b, pend}}) == app(wbits(D.W{out, pend}), [b]) : List<&2, Bool>}:
  %Equal.sym(List<&2, Bool>, D.revapp(pend, app(Nil{}, [b])), app(D.revapp(pend, Nil{}), [b]),
    revapp_app(pend, Nil{}, [b])) :
    {app(bitsof(out), _) == app(app(bitsof(out), D.revapp(pend, Nil{})), [b]) : List<&2, Bool>}
  Equal.sym(List<&2, Bool>, app(app(bitsof(out), D.revapp(pend, Nil{})), [b]),
    app(bitsof(out), app(D.revapp(pend, Nil{}), [b])), app_assoc(bitsof(out), D.revapp(pend, Nil{}), [b]))

# a bit put is a bit after the writer's
def put_bits(+w: D.W, +b: Bool) -> {wbits(D.put(w, b)) == app(wbits(w), [b]) : List<&2, Bool>}:
  match w:
    case D.W{+out, +pend}:
      match pend:
        case Nil{}:
          cons_bits(out, Nil{}, b)
        case Con{+p6, +t0}:
          match t0:
            case Nil{}:
              cons_bits(out, Con{p6, Nil{}}, b)
            case Con{+p5, +t1}:
              match t1:
                case Nil{}:
                  cons_bits(out, Con{p6, Con{p5, Nil{}}}, b)
                case Con{+p4, +t2}:
                  match t2:
                    case Nil{}:
                      cons_bits(out, Con{p6, Con{p5, Con{p4, Nil{}}}}, b)
                    case Con{+p3, +t3}:
                      match t3:
                        case Nil{}:
                          cons_bits(out, Con{p6, Con{p5, Con{p4, Con{p3, Nil{}}}}}, b)
                        case Con{+p2, +t4}:
                          match t4:
                            case Nil{}:
                              cons_bits(out, Con{p6, Con{p5, Con{p4, Con{p3, Con{p2, Nil{}}}}}}, b)
                            case Con{+p1, +t5}:
                              match t5:
                                case Nil{}:
                                  cons_bits(out, Con{p6, Con{p5, Con{p4, Con{p3, Con{p2, Con{p1, Nil{}}}}}}}, b)
                                case Con{+p0, +t6}:
                                  match t6:
                                    case Nil{}:
                                      Equal.trans(List<&2, Bool>, app(bitsof(Bytes.push(out, D.byte_of([b, p6, p5, p4, p3, p2, p1, p0]))), Nil{}), bitsof(Bytes.push(out, D.byte_of([b, p6, p5, p4, p3, p2, p1, p0]))), app(app(bitsof(out), [p0, p1, p2, p3, p4, p5, p6]), [b]),
                                        app_nil(bitsof(Bytes.push(out, D.byte_of([b, p6, p5, p4, p3, p2, p1, p0])))),
                                        Equal.trans(List<&2, Bool>, bitsof(Bytes.push(out, D.byte_of([b, p6, p5, p4, p3, p2, p1, p0]))), app(bitsof(out), D.unbyte(D.byte_of([b, p6, p5, p4, p3, p2, p1, p0]))), app(app(bitsof(out), [p0, p1, p2, p3, p4, p5, p6]), [b]),
                                          bitsof_push(out, D.byte_of([b, p6, p5, p4, p3, p2, p1, p0])),
                                          Equal.trans(List<&2, Bool>, app(bitsof(out), D.unbyte(D.byte_of([b, p6, p5, p4, p3, p2, p1, p0]))), app(bitsof(out), [p0, p1, p2, p3, p4, p5, p6, b]), app(app(bitsof(out), [p0, p1, p2, p3, p4, p5, p6]), [b]),
                                            Equal.cong(List<&2, Bool>, List<&2, Bool>, y => app(bitsof(out), y), D.unbyte(D.byte_of([b, p6, p5, p4, p3, p2, p1, p0])), [p0, p1, p2, p3, p4, p5, p6, b],
                                              unbyte_of(p0, p1, p2, p3, p4, p5, p6, b)),
                                            Equal.sym(List<&2, Bool>, app(app(bitsof(out), [p0, p1, p2, p3, p4, p5, p6]), [b]), app(bitsof(out), app([p0, p1, p2, p3, p4, p5, p6], [b])), app_assoc(bitsof(out), [p0, p1, p2, p3, p4, p5, p6], [b])))))
                                    case Con{+q, +r}:
                                      cons_bits(out, Con{p6, Con{p5, Con{p4, Con{p3, Con{p2, Con{p1, Con{p0, Con{q, r}}}}}}}}, b)

# the same, before any bits
def put_k(+w: D.W, +b: Bool, +s: List<&2, Bool>) ->
  {app(wbits(D.put(w, b)), s) == app(wbits(w), Con{b, s}) : List<&2, Bool>}:
  Equal.trans(List<&2, Bool>, app(wbits(D.put(w, b)), s), app(app(wbits(w), [b]), s),
    app(wbits(w), Con{b, s}),
    Equal.cong(List<&2, Bool>, List<&2, Bool>, y => app(y, s), wbits(D.put(w, b)), app(wbits(w), [b]),
      put_bits(w, b)),
    app_assoc(wbits(w), [b], s))

# a field put is its bits, low first, after the writer's
def putx_k(+n: Nat, +w: D.W, +v: Nat, +s: List<&2, Bool>) ->
  {app(wbits(D.putx(n, w, v)), s) == app(wbits(w), app(D.xbits(n, v), s)) : List<&2, Bool>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      +b0 = Nat.is_eq(Nat.mod(v, 2n), 1n)
      +v2 = Nat.div(v, 2n)
      Equal.trans(List<&2, Bool>, app(wbits(D.putx(p, D.put(w, b0), v2)), s),
        app(wbits(D.put(w, b0)), app(D.xbits(p, v2), s)), app(wbits(w), Con{b0, app(D.xbits(p, v2), s)}),
        putx_k(p, D.put(w, b0), v2, s), put_k(w, b0, app(D.xbits(p, v2), s)))

# bytes put at a byte are their bits after the writer's
def raw_bits(+out: Bytes(), +b: Bytes()) ->
  {wbits(D.put_raw(D.W{out, Nil{}}, b)) == app(wbits(D.W{out, Nil{}}), bitsof(b)) : List<&2, Bool>}:
  Equal.trans(List<&2, Bool>, app(bitsof(String.append(out, b)), Nil{}), bitsof(String.append(out, b)),
    app(app(bitsof(out), Nil{}), bitsof(b)), app_nil(bitsof(String.append(out, b))),
    Equal.trans(List<&2, Bool>, bitsof(String.append(out, b)), app(bitsof(out), bitsof(b)),
      app(app(bitsof(out), Nil{}), bitsof(b)), bitsof_app(out, b),
      Equal.cong(List<&2, Bool>, List<&2, Bool>, y => app(y, bitsof(b)), bitsof(out), app(bitsof(out), Nil{}),
        Equal.sym(List<&2, Bool>, app(bitsof(out), Nil{}), bitsof(out), app_nil(bitsof(out))))))

# the first n bits of bs as the writer takes them
def takeN(n: Nat, +bs: List<&2, Bool>) -> List<&2, Bool>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{D.hd(bs), takeN(p, D.tl(bs))}

# n bits put from a list are its first n after the writer's
def putn_k(+n: Nat, +bs: List<&2, Bool>, +w: D.W, +s: List<&2, Bool>) ->
  {app(wbits(D.putn(n, bs, w)), s) == app(wbits(w), app(takeN(n, bs), s)) : List<&2, Bool>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(List<&2, Bool>, app(wbits(D.putn(p, D.tl(bs), D.put(w, D.hd(bs)))), s),
        app(wbits(D.put(w, D.hd(bs))), app(takeN(p, D.tl(bs)), s)),
        app(wbits(w), Con{D.hd(bs), app(takeN(p, D.tl(bs)), s)}),
        putn_k(p, D.tl(bs), D.put(w, D.hd(bs)), s), put_k(w, D.hd(bs), app(takeN(p, D.tl(bs)), s)))

def pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

# no length is both 0 and more
def len_no(-g: Type, +n: Nat, e: {0n == 1n+n : Nat}) -> g:
  Bool.no(g, Equal.sym(Bool, True{}, False{}, Equal.cong(Nat, Bool, x => Nat.is_eq(x, 0n), 0n, 1n+n, e)))

# a list of n bits, its first n: itself
def take_all(+bs: List<&2, Bool>, +n: Nat, e: {List.length(&2, Bool, bs) == n : Nat}) ->
  {takeN(n, bs) == bs : List<&2, Bool>}:
  match bs n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      len_no({takeN(1n+p, Nil{}) == Nil{} : List<&2, Bool>}, p, e)
    case Con{+h, +t} 0n:
      len_no({takeN(0n, Con{h, t}) == Con{h, t} : List<&2, Bool>}, List.length(&2, Bool, t),
        Equal.sym(Nat, 1n+List.length(&2, Bool, t), 0n, e))
    case Con{+h, +t} 1n+p:
      Equal.cong(List<&2, Bool>, List<&2, Bool>, y => Con{h, y}, takeN(p, t), t,
        take_all(t, p, Equal.cong(Nat, Nat, pred, 1n+List.length(&2, Bool, t), 1n+p, e)))

def len_nots(+bs: List<&2, Bool>) ->
  {List.length(&2, Bool, D.nots(bs)) == List.length(&2, Bool, bs) : Nat}:
  match bs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.cong(Nat, Nat, y => 1n+y, List.length(&2, Bool, D.nots(t)), List.length(&2, Bool, t),
        len_nots(t))

# a stored block's bits: the header, zeros to the byte, LEN, NLEN, the bytes
def SB(+cur: Bytes(), +cnt: List<&2, Bool>, last: Bool) -> List<&2, Bool>:
  app([last, False{}, False{}, False{}, False{}, False{}, False{}, False{}],
    app(takeN(16n, cnt), app(takeN(16n, D.nots(cnt)), bitsof(cur))))

def A3(+ow: Bytes(), last: Bool) -> D.W:
  D.W{ow, [False{}, False{}, last]}

def P1(+ow: Bytes(), +cnt: List<&2, Bool>, last: Bool) -> D.W:
  D.putn(16n, cnt, D.align(D.put(D.put(D.put(D.W{ow, Nil{}}, last), False{}), False{})))

def P2(+ow: Bytes(), +cnt: List<&2, Bool>, last: Bool) -> D.W:
  D.putn(16n, D.nots(cnt), P1(ow, cnt, last))

# a stored block written at a byte
def stored_bits(+ow: Bytes(), +cur: Bytes(), +cnt: List<&2, Bool>, +last: Bool) ->
  {wbits(D.stored_one(D.W{ow, Nil{}}, cur, cnt, last)) == app(bitsof(ow), SB(cur, cnt, last)) :
    List<&2, Bool>}:
  +xs = takeN(16n, D.nots(cnt))
  +bc = bitsof(cur)
  +a3 = A3(ow, last)
  Equal.trans(List<&2, Bool>, wbits(D.put_raw(D.W{D.w_out(P2(ow, cnt, last)), Nil{}}, cur)),
    app(wbits(P2(ow, cnt, last)), bc), app(bitsof(ow), SB(cur, cnt, last)),
    raw_bits(D.w_out(P2(ow, cnt, last)), cur),
    Equal.trans(List<&2, Bool>, app(wbits(P2(ow, cnt, last)), bc), app(wbits(P1(ow, cnt, last)), app(xs, bc)),
      app(bitsof(ow), SB(cur, cnt, last)),
      putn_k(16n, D.nots(cnt), P1(ow, cnt, last), bc),
      Equal.trans(List<&2, Bool>, app(wbits(P1(ow, cnt, last)), app(xs, bc)),
        app(wbits(D.putx(5n, a3, 0n)), app(takeN(16n, cnt), app(xs, bc))), app(bitsof(ow), SB(cur, cnt, last)),
        putn_k(16n, cnt, D.putx(5n, a3, 0n), app(xs, bc)),
        Equal.trans(List<&2, Bool>, app(wbits(D.putx(5n, a3, 0n)), app(takeN(16n, cnt), app(xs, bc))),
          app(wbits(a3), app(D.xbits(5n, 0n), app(takeN(16n, cnt), app(xs, bc)))),
          app(bitsof(ow), SB(cur, cnt, last)),
          putx_k(5n, a3, 0n, app(takeN(16n, cnt), app(xs, bc))),
          app_assoc(bitsof(ow), [last, False{}, False{}],
            app(D.xbits(5n, 0n), app(takeN(16n, cnt), app(xs, bc))))))))

# the n-bit word of k: k increments of zero
def it(+n: Nat, k: Nat) -> Word(n):
  match k:
    case 0n:
      Word.zero(n)
    case 1n+j:
      Word.inc(n, it(n, j))

# two increments of a word whose low bit is clear step the rest once
def it_double(+p: Nat, +m: Nat) -> {it(1n+p, Nat.double(m)) == WCon{False{}, it(p, m)} : Word(1n+p)}:
  match m:
    case 0n:
      {==}
    case 1n+j:
      %Equal.sym(Word(1n+p), it(1n+p, Nat.double(j)), WCon{False{}, it(p, j)}, it_double(p, j)) :
        {Word.inc(1n+p, Word.inc(1n+p, _)) == WCon{False{}, Word.inc(p, it(p, j))} : Word(1n+p)}
      {==}

def it_bit(+p: Nat, +b: Bool, +m: Nat) -> {it(1n+p, Nat.bit(b, m)) == WCon{b, it(p, m)} : Word(1n+p)}:
  match b:
    case False{}:
      it_double(p, m)
    case True{}:
      %Equal.sym(Word(1n+p), it(1n+p, Nat.double(m)), WCon{False{}, it(p, m)}, it_double(p, m)) :
        {Word.inc(1n+p, _) == WCon{True{}, it(p, m)} : Word(1n+p)}
      {==}

# a word is its value's word
def it_val(+n: Nat, +w: Word(n)) -> {it(n, Word.to_nat(n, w)) == w : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{+b, +t}:
          %Equal.sym(Nat, Word.to_nat(1n+p, WCon{b, t}), Nat.bit(b, Word.to_nat(p, t)),
            Word.to_nat_bit(p, b, t)) : {it(1n+p, _) == WCon{b, t} : Word(1n+p)}
          %Equal.sym(Word(1n+p), it(1n+p, Nat.bit(b, Word.to_nat(p, t))), WCon{b, it(p, Word.to_nat(p, t))},
            it_bit(p, b, Word.to_nat(p, t))) : {_ == WCon{b, t} : Word(1n+p)}
          %Equal.sym(Word(p), it(p, Word.to_nat(p, t)), t, it_val(p, t)) :
            {WCon{b, _} == WCon{b, t} : Word(1n+p)}
          {==}


# the byte of eight bits
def b8(b0: Bool, b1: Bool, b2: Bool, b3: Bool, b4: Bool, b5: Bool, b6: Bool, b7: Bool) -> U32:
  U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}}}

# a clear low bit of the right side decides nothing a < b does not
def peel(+b: Bool, +x: Cmp) -> {Cmp.is_lt(Word.cmp.fin(b, False{}, x)) == Cmp.is_lt(x) : Bool}:
  match b x:
    case False{} LT{}:
      {==}
    case False{} EQ{}:
      {==}
    case False{} GT{}:
      {==}
    case True{} LT{}:
      {==}
    case True{} EQ{}:
      {==}
    case True{} GT{}:
      {==}

def peel.go(+b: Bool, +x: Cmp, e: {Cmp.is_lt(Word.cmp.fin(b, False{}, x)) == True{} : Bool}) ->
  {Cmp.is_lt(x) == True{} : Bool}:
  Equal.trans(Bool, Cmp.is_lt(x), Cmp.is_lt(Word.cmp.fin(b, False{}, x)), True{},
    Equal.sym(Bool, Cmp.is_lt(Word.cmp.fin(b, False{}, x)), Cmp.is_lt(x), peel(b, x)), e)

def high0.at(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool,
  +r: Word(24n), lt: {Cmp.is_lt(Word.cmp.fin(b0, False{}, Word.cmp.fin(b1, False{},
    Word.cmp.fin(b2, False{}, Word.cmp.fin(b3, False{}, Word.cmp.fin(b4, False{},
    Word.cmp.fin(b5, False{}, Word.cmp.fin(b6, False{}, Word.cmp.fin(b7, False{},
    Word.cmp(24n, r, it(24n, 1n))))))))))) == True{} : Bool}) -> {r == Word.zero(24n) : Word(24n)}:
  +t8 = Word.cmp(24n, r, it(24n, 1n))
  +t7 = Word.cmp.fin(b7, False{}, t8)
  +t6 = Word.cmp.fin(b6, False{}, t7)
  +t5 = Word.cmp.fin(b5, False{}, t6)
  +t4 = Word.cmp.fin(b4, False{}, t5)
  +t3 = Word.cmp.fin(b3, False{}, t4)
  +t2 = Word.cmp.fin(b2, False{}, t3)
  +t1 = Word.cmp.fin(b1, False{}, t2)
  e8 = peel.go(b7, t8, peel.go(b6, t7, peel.go(b5, t6, peel.go(b4, t5, peel.go(b3, t4,
    peel.go(b2, t3, peel.go(b1, t2, peel.go(b0, t1, lt))))))))
  e9 = Equal.trans(Bool, Nat.is_lt(Word.to_nat(24n, r), 1n), Cmp.is_lt(t8), True{},
    Equal.cong(Cmp, Bool, Cmp.is_lt, Nat.cmp(Word.to_nat(24n, r), 1n), t8,
      Equal.sym(Cmp, t8, Nat.cmp(Word.to_nat(24n, r), 1n), Word.cmp_nat(24n, r, it(24n, 1n)))), e8)
  %it_val(24n, r) : {_ == Word.zero(24n) : Word(24n)}
  %Equal.sym(Nat, Word.to_nat(24n, r), 0n, lt_one(Word.to_nat(24n, r))(e9)) :
    {it(24n, _) == Word.zero(24n) : Word(24n)}
  {==}

# below 256: the three high bytes are 0
def high0(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool,
  +r: Word(24n)) ->
  {U32.is_lt(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, r}}}}}}}}},
    256) == True{} : Bool} -> {r == Word.zero(24n) : Word(24n)}:
  lt => high0.at(b0, b1, b2, b3, b4, b5, b6, b7, r, lt)

# a byte read back from its bits, eight bits at a time
def byte_back.at(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool) ->
  {U32.from_nat(D.hval(D.revapp(D.unbyte(b8(b0, b1, b2, b3, b4, b5, b6, b7)), Nil{}), 0n)) == b8(b0, b1, b2, b3, b4, b5, b6, b7) : U32}:
  match b0 b1 b2 b3 b4 b5 b6 b7:
    case False{} False{} False{} False{} False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} False{} False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} False{} False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} False{} False{} False{} True{} True{}:
      {==}
    case False{} False{} False{} False{} False{} True{} False{} False{}:
      {==}
    case False{} False{} False{} False{} False{} True{} False{} True{}:
      {==}
    case False{} False{} False{} False{} False{} True{} True{} False{}:
      {==}
    case False{} False{} False{} False{} False{} True{} True{} True{}:
      {==}
    case False{} False{} False{} False{} True{} False{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{} False{} False{} True{}:
      {==}
    case False{} False{} False{} False{} True{} False{} True{} False{}:
      {==}
    case False{} False{} False{} False{} True{} False{} True{} True{}:
      {==}
    case False{} False{} False{} False{} True{} True{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{} True{} False{} True{}:
      {==}
    case False{} False{} False{} False{} True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} False{} True{} True{} True{} True{}:
      {==}
    case False{} False{} False{} True{} False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{} False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{} False{} False{} True{} True{}:
      {==}
    case False{} False{} False{} True{} False{} True{} False{} False{}:
      {==}
    case False{} False{} False{} True{} False{} True{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{} False{} True{} True{} True{}:
      {==}
    case False{} False{} False{} True{} True{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{} True{} False{} False{} True{}:
      {==}
    case False{} False{} False{} True{} True{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{} True{} False{} True{} True{}:
      {==}
    case False{} False{} False{} True{} True{} True{} False{} False{}:
      {==}
    case False{} False{} False{} True{} True{} True{} False{} True{}:
      {==}
    case False{} False{} False{} True{} True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{} True{} True{} True{} True{}:
      {==}
    case False{} False{} True{} False{} False{} False{} False{} False{}:
      {==}
    case False{} False{} True{} False{} False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{} False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} False{} False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} False{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} False{} False{} True{} True{} True{}:
      {==}
    case False{} False{} True{} False{} True{} False{} False{} False{}:
      {==}
    case False{} False{} True{} False{} True{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{} True{} False{} True{} False{}:
      {==}
    case False{} False{} True{} False{} True{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{} True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{} True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} False{} True{} True{} True{} False{}:
      {==}
    case False{} False{} True{} False{} True{} True{} True{} True{}:
      {==}
    case False{} False{} True{} True{} False{} False{} False{} False{}:
      {==}
    case False{} False{} True{} True{} False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{} False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} True{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} True{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} True{} False{} True{} True{} True{}:
      {==}
    case False{} False{} True{} True{} True{} False{} False{} False{}:
      {==}
    case False{} False{} True{} True{} True{} False{} False{} True{}:
      {==}
    case False{} False{} True{} True{} True{} False{} True{} False{}:
      {==}
    case False{} False{} True{} True{} True{} False{} True{} True{}:
      {==}
    case False{} False{} True{} True{} True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} True{} True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} True{} True{} True{} False{}:
      {==}
    case False{} False{} True{} True{} True{} True{} True{} True{}:
      {==}
    case False{} True{} False{} False{} False{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} False{} False{} False{} True{}:
      {==}
    case False{} True{} False{} False{} False{} False{} True{} False{}:
      {==}
    case False{} True{} False{} False{} False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{} False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} False{} False{} True{} False{} True{}:
      {==}
    case False{} True{} False{} False{} False{} True{} True{} False{}:
      {==}
    case False{} True{} False{} False{} False{} True{} True{} True{}:
      {==}
    case False{} True{} False{} False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} False{} False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} False{} False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} False{} False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} False{} False{} True{} True{} True{} True{}:
      {==}
    case False{} True{} False{} True{} False{} False{} False{} False{}:
      {==}
    case False{} True{} False{} True{} False{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{} False{} True{} False{}:
      {==}
    case False{} True{} False{} True{} False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} True{} False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{} False{} True{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{} True{} True{} False{}:
      {==}
    case False{} True{} False{} True{} False{} True{} True{} True{}:
      {==}
    case False{} True{} False{} True{} True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} True{} True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{} True{} False{} True{} False{}:
      {==}
    case False{} True{} False{} True{} True{} False{} True{} True{}:
      {==}
    case False{} True{} False{} True{} True{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{} True{} True{} False{} True{}:
      {==}
    case False{} True{} False{} True{} True{} True{} True{} False{}:
      {==}
    case False{} True{} False{} True{} True{} True{} True{} True{}:
      {==}
    case False{} True{} True{} False{} False{} False{} False{} False{}:
      {==}
    case False{} True{} True{} False{} False{} False{} False{} True{}:
      {==}
    case False{} True{} True{} False{} False{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{} False{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} False{} True{} False{} False{}:
      {==}
    case False{} True{} True{} False{} False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{} False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} False{} False{} True{} True{} True{}:
      {==}
    case False{} True{} True{} False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} True{} False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} True{} False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} False{} True{} True{} True{} True{}:
      {==}
    case False{} True{} True{} True{} False{} False{} False{} False{}:
      {==}
    case False{} True{} True{} True{} False{} False{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{} False{} True{} False{}:
      {==}
    case False{} True{} True{} True{} False{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{} False{} True{} False{} False{}:
      {==}
    case False{} True{} True{} True{} False{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} False{} True{} True{} True{}:
      {==}
    case False{} True{} True{} True{} True{} False{} False{} False{}:
      {==}
    case False{} True{} True{} True{} True{} False{} False{} True{}:
      {==}
    case False{} True{} True{} True{} True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} True{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} True{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} True{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{} False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} False{} False{} False{} True{} True{}:
      {==}
    case True{} False{} False{} False{} False{} True{} False{} False{}:
      {==}
    case True{} False{} False{} False{} False{} True{} False{} True{}:
      {==}
    case True{} False{} False{} False{} False{} True{} True{} False{}:
      {==}
    case True{} False{} False{} False{} False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{} True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{} True{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{} True{} False{} True{} False{}:
      {==}
    case True{} False{} False{} False{} True{} False{} True{} True{}:
      {==}
    case True{} False{} False{} False{} True{} True{} False{} False{}:
      {==}
    case True{} False{} False{} False{} True{} True{} False{} True{}:
      {==}
    case True{} False{} False{} False{} True{} True{} True{} False{}:
      {==}
    case True{} False{} False{} False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} False{} True{} False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{} False{} False{} True{} True{}:
      {==}
    case True{} False{} False{} True{} False{} True{} False{} False{}:
      {==}
    case True{} False{} False{} True{} False{} True{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{} True{} True{} False{}:
      {==}
    case True{} False{} False{} True{} False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} True{} True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{} True{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{} True{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{} True{} False{} True{} True{}:
      {==}
    case True{} False{} False{} True{} True{} True{} False{} False{}:
      {==}
    case True{} False{} False{} True{} True{} True{} False{} True{}:
      {==}
    case True{} False{} False{} True{} True{} True{} True{} False{}:
      {==}
    case True{} False{} False{} True{} True{} True{} True{} True{}:
      {==}
    case True{} False{} True{} False{} False{} False{} False{} False{}:
      {==}
    case True{} False{} True{} False{} False{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{} False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{} False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} False{} True{} False{} False{}:
      {==}
    case True{} False{} True{} False{} False{} True{} False{} True{}:
      {==}
    case True{} False{} True{} False{} False{} True{} True{} False{}:
      {==}
    case True{} False{} True{} False{} False{} True{} True{} True{}:
      {==}
    case True{} False{} True{} False{} True{} False{} False{} False{}:
      {==}
    case True{} False{} True{} False{} True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{} True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{} True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} True{} True{} False{} False{}:
      {==}
    case True{} False{} True{} False{} True{} True{} False{} True{}:
      {==}
    case True{} False{} True{} False{} True{} True{} True{} False{}:
      {==}
    case True{} False{} True{} False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} True{} True{} False{} False{} False{} False{}:
      {==}
    case True{} False{} True{} True{} False{} False{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{} False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{} False{} True{} False{} False{}:
      {==}
    case True{} False{} True{} True{} False{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} False{} True{} True{} True{}:
      {==}
    case True{} False{} True{} True{} True{} False{} False{} False{}:
      {==}
    case True{} False{} True{} True{} True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} True{} True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} True{} True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{} True{} True{} False{} False{}:
      {==}
    case True{} False{} True{} True{} True{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} True{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} True{} True{} True{} True{}:
      {==}
    case True{} True{} False{} False{} False{} False{} False{} False{}:
      {==}
    case True{} True{} False{} False{} False{} False{} False{} True{}:
      {==}
    case True{} True{} False{} False{} False{} False{} True{} False{}:
      {==}
    case True{} True{} False{} False{} False{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{} False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{} False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} False{} False{} True{} True{} False{}:
      {==}
    case True{} True{} False{} False{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} False{} True{} False{} False{} False{}:
      {==}
    case True{} True{} False{} False{} True{} False{} False{} True{}:
      {==}
    case True{} True{} False{} False{} True{} False{} True{} False{}:
      {==}
    case True{} True{} False{} False{} True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{} True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{} True{} True{} False{} True{}:
      {==}
    case True{} True{} False{} False{} True{} True{} True{} False{}:
      {==}
    case True{} True{} False{} False{} True{} True{} True{} True{}:
      {==}
    case True{} True{} False{} True{} False{} False{} False{} False{}:
      {==}
    case True{} True{} False{} True{} False{} False{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{} False{} True{} False{}:
      {==}
    case True{} True{} False{} True{} False{} False{} True{} True{}:
      {==}
    case True{} True{} False{} True{} False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{} False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{} True{} True{} False{}:
      {==}
    case True{} True{} False{} True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} True{} True{} False{} False{} False{}:
      {==}
    case True{} True{} False{} True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} False{} True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} False{} True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} False{} True{} True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} False{} False{} False{} False{} False{}:
      {==}
    case True{} True{} True{} False{} False{} False{} False{} True{}:
      {==}
    case True{} True{} True{} False{} False{} False{} True{} False{}:
      {==}
    case True{} True{} True{} False{} False{} False{} True{} True{}:
      {==}
    case True{} True{} True{} False{} False{} True{} False{} False{}:
      {==}
    case True{} True{} True{} False{} False{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{} False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{} False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} False{} True{} False{} False{} False{}:
      {==}
    case True{} True{} True{} False{} True{} False{} False{} True{}:
      {==}
    case True{} True{} True{} False{} True{} False{} True{} False{}:
      {==}
    case True{} True{} True{} False{} True{} False{} True{} True{}:
      {==}
    case True{} True{} True{} False{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} False{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{} True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{} False{} False{} False{} False{}:
      {==}
    case True{} True{} True{} True{} False{} False{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{} False{} True{} False{}:
      {==}
    case True{} True{} True{} True{} False{} False{} True{} True{}:
      {==}
    case True{} True{} True{} True{} False{} True{} False{} False{}:
      {==}
    case True{} True{} True{} True{} False{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{} True{} False{} False{} False{}:
      {==}
    case True{} True{} True{} True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} True{} True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} True{} True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} True{} True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} True{} True{} True{} True{}:
      {==}

# a byte read back from its bits
def byte_back(+c: U32) -> {U32.is_lt(c, 256) == True{} : Bool} ->
  {U32.from_nat(D.hval(D.revapp(D.unbyte(c), Nil{}), 0n)) == c : U32}:
  match c:
    case U32{WCon{+b0, WCon{+b1, WCon{+b2, WCon{+b3, WCon{+b4, WCon{+b5, WCon{+b6, WCon{+b7, +r}}}}}}}}}:
      lt =>
        %Equal.sym(Word(24n), r, Word.zero(24n), high0(b0, b1, b2, b3, b4, b5, b6, b7, r)(lt)) :
          {U32.from_nat(D.hval(D.revapp(D.unbyte(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, _}}}}}}}}}), Nil{}), 0n)) == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, _}}}}}}}}} : U32}
        byte_back.at(b0, b1, b2, b3, b4, b5, b6, b7)

# Reading a stored block
# ----------------------

def bl(s: Bytes()) -> Nat:
  match s:
    case SNil{}:
      0n
    case SCon{h, t}:
      1n+bl(t)

def le_pred(+x: Nat, +c: Nat) -> {Nat.is_le(1n+x, c) == True{} : Bool} -> {Nat.is_le(x, c) == True{} : Bool}:
  match x c:
    case 0n 0n:
      e => Bool.no({Nat.is_le(0n, 0n) == True{} : Bool}, e)
    case 0n 1n+d:
      e => {==}
    case 1n+p 0n:
      e => Bool.no({Nat.is_le(1n+p, 0n) == True{} : Bool}, e)
    case 1n+p 1n+d:
      e => le_pred(p, d)(e)

def le_lt(+x: Nat, +c: Nat) -> {Nat.is_le(1n+x, c) == True{} : Bool} -> {Nat.is_lt(x, c) == True{} : Bool}:
  match x c:
    case 0n 0n:
      e => Bool.no({Nat.is_lt(0n, 0n) == True{} : Bool}, e)
    case 0n 1n+d:
      e => {==}
    case 1n+p 0n:
      e => Bool.no({Nat.is_lt(1n+p, 0n) == True{} : Bool}, e)
    case 1n+p 1n+d:
      e => le_lt(p, d)(e)

# room for a+1 more after m: room for one
def room_lt(+a: Nat, +m: Nat, +cap: Nat) -> {Nat.is_le(Nat.add(1n+a, m), cap) == True{} : Bool} ->
  {Nat.is_lt(m, cap) == True{} : Bool}:
  match a:
    case 0n:
      e => le_lt(m, cap)(e)
    case 1n+p:
      e => room_lt(p, m, cap)(le_pred(Nat.add(1n+p, m), cap)(e))

def push_app(+a: Bytes(), +c: U32, +r: Bytes()) ->
  {String.append(Bytes.push(a, c), r) == String.append(a, SCon{Chr{c}, r}) : Bytes()}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.cong(Bytes(), Bytes(), y => SCon{h, y}, String.append(Bytes.push(t, c), r),
        String.append(t, SCon{Chr{c}, r}), push_app(t, c, r))

def sc(+c: U32, +t: Bytes()) -> Bytes():
  SCon{Chr{c}, t}

def Ob(+dd: Bytes(), +m: Nat, +cap: Nat, +tb: D.Tabs) -> D.O:
  D.O{dd, 0n, m, cap, tb}

def SBy(+last: Bool, +left: Nat, +dd: Bytes(), +m: Nat, +cap: Nat, +tb: D.Tabs) -> D.St:
  D.St{D.Get{7n, Nil{}, D.KByte{last, left}}, Ob(dd, m, cap, tb), 0n}

def Aft(+last: Bool, +dd: Bytes(), +m: Nat, +cap: Nat, +tb: D.Tabs) -> D.St:
  D.next_block(last, Ob(dd, m, cap, tb), 0n)

def RB(+c: U32) -> U32:
  U32.from_nat(D.hval(D.revapp(D.unbyte(c), Nil{}), 0n))

# the rest of a stored block's bytes, read
def data(+last: Bool, +t: Bytes(), +c: U32, +dd: Bytes(), +m: Nat, +cap: Nat, +tb: D.Tabs,
  vc: {U32.is_lt(c, 256) == True{} : Bool}, +vt: {D.valid(t) == True{} : Bool},
  +room: {Nat.is_le(Nat.add(1n+bl(t), m), cap) == True{} : Bool}) ->
  {bfeed(bitsof(SCon{Chr{c}, t}), SBy(last, bl(t), dd, m, cap, tb)) ==
    Aft(last, String.append(dd, SCon{Chr{c}, t}), Nat.add(1n+bl(t), m), cap, tb) : D.St}:
  match last t:
    case True{} SNil{}:
      %Equal.sym(Bool, Nat.is_lt(m, cap), True{}, room_lt(0n, m, cap)(room)) :
        {D.emit.if(_, dd, 0n, m, cap, tb, RB(c), D.End{}, 0n) ==
          D.St{D.End{}, Ob(Bytes.push(dd, c), 1n+m, cap, tb), 0n} : D.St}
      %Equal.sym(U32, RB(c), c, byte_back(c)(vc)) :
        {D.St{D.End{}, Ob(Bytes.push(dd, _), 1n+m, cap, tb), 0n} ==
          D.St{D.End{}, Ob(Bytes.push(dd, c), 1n+m, cap, tb), 0n} : D.St}
      {==}
    case False{} SNil{}:
      %Equal.sym(Bool, Nat.is_lt(m, cap), True{}, room_lt(0n, m, cap)(room)) :
        {D.emit.if(_, dd, 0n, m, cap, tb, RB(c), D.Get{2n, Nil{}, D.KHead{}}, 0n) ==
          D.St{D.Get{2n, Nil{}, D.KHead{}}, Ob(Bytes.push(dd, c), 1n+m, cap, tb), 0n} : D.St}
      %Equal.sym(U32, RB(c), c, byte_back(c)(vc)) :
        {D.St{D.Get{2n, Nil{}, D.KHead{}}, Ob(Bytes.push(dd, _), 1n+m, cap, tb), 0n} ==
          D.St{D.Get{2n, Nil{}, D.KHead{}}, Ob(Bytes.push(dd, c), 1n+m, cap, tb), 0n} : D.St}
      {==}
    case True{} SCon{Chr{+c2}, +t2}:
      +r = sc(c2, t2)
      +b = bl(t2)
      +out = Aft(True{}, String.append(dd, SCon{Chr{c}, r}), Nat.add(2n+b, m), cap, tb)
      %Equal.sym(Bool, Nat.is_lt(m, cap), True{}, room_lt(1n+b, m, cap)(room)) :
        {bfeed(bitsof(r), D.emit.if(_, dd, 0n, m, cap, tb, RB(c), D.Get{7n, Nil{}, D.KByte{True{}, b}}, 0n))
          == out : D.St}
      %Equal.sym(U32, RB(c), c, byte_back(c)(vc)) :
        {bfeed(bitsof(r), SBy(True{}, b, Bytes.push(dd, _), 1n+m, cap, tb)) == out : D.St}
      %push_app(dd, c, r) : {bfeed(bitsof(r), SBy(True{}, b, Bytes.push(dd, c), 1n+m, cap, tb)) ==
        Aft(True{}, _, Nat.add(2n+b, m), cap, tb) : D.St}
      %add_succ(1n+b, m) : {bfeed(bitsof(r), SBy(True{}, b, Bytes.push(dd, c), 1n+m, cap, tb)) ==
        Aft(True{}, String.append(Bytes.push(dd, c), r), _, cap, tb) : D.St}
      data(True{}, t2, c2, Bytes.push(dd, c), 1n+m, cap, tb, Bool.and_l(U32.is_lt(c2, 256), D.valid(t2), vt),
        Bool.and_r(U32.is_lt(c2, 256), D.valid(t2), vt),
        Equal.trans(Bool, Nat.is_le(Nat.add(1n+b, 1n+m), cap), Nat.is_le(Nat.add(2n+b, m), cap), True{},
          Equal.cong(Nat, Bool, y => Nat.is_le(y, cap), Nat.add(1n+b, 1n+m), Nat.add(2n+b, m),
            add_succ(1n+b, m)), room))
    case False{} SCon{Chr{+c2}, +t2}:
      +r = sc(c2, t2)
      +b = bl(t2)
      +out = Aft(False{}, String.append(dd, SCon{Chr{c}, r}), Nat.add(2n+b, m), cap, tb)
      %Equal.sym(Bool, Nat.is_lt(m, cap), True{}, room_lt(1n+b, m, cap)(room)) :
        {bfeed(bitsof(r), D.emit.if(_, dd, 0n, m, cap, tb, RB(c), D.Get{7n, Nil{}, D.KByte{False{}, b}}, 0n))
          == out : D.St}
      %Equal.sym(U32, RB(c), c, byte_back(c)(vc)) :
        {bfeed(bitsof(r), SBy(False{}, b, Bytes.push(dd, _), 1n+m, cap, tb)) == out : D.St}
      %push_app(dd, c, r) : {bfeed(bitsof(r), SBy(False{}, b, Bytes.push(dd, c), 1n+m, cap, tb)) ==
        Aft(False{}, _, Nat.add(2n+b, m), cap, tb) : D.St}
      %add_succ(1n+b, m) : {bfeed(bitsof(r), SBy(False{}, b, Bytes.push(dd, c), 1n+m, cap, tb)) ==
        Aft(False{}, String.append(Bytes.push(dd, c), r), _, cap, tb) : D.St}
      data(False{}, t2, c2, Bytes.push(dd, c), 1n+m, cap, tb, Bool.and_l(U32.is_lt(c2, 256), D.valid(t2), vt),
        Bool.and_r(U32.is_lt(c2, 256), D.valid(t2), vt),
        Equal.trans(Bool, Nat.is_le(Nat.add(1n+b, 1n+m), cap), Nat.is_le(Nat.add(2n+b, m), cap), True{},
          Equal.cong(Nat, Bool, y => Nat.is_le(y, cap), Nat.add(1n+b, 1n+m), Nat.add(2n+b, m),
            add_succ(1n+b, m)), room))

def str_nil(+a: Bytes()) -> {String.append(a, "") == a : Bytes()}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.cong(Bytes(), Bytes(), y => SCon{h, y}, String.append(t, ""), t, str_nil(t))

def str_assoc(+a: Bytes(), +b: Bytes(), +c: Bytes()) ->
  {String.append(String.append(a, b), c) == String.append(a, String.append(b, c)) : Bytes()}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.cong(Bytes(), Bytes(), y => SCon{h, y}, String.append(String.append(t, b), c),
        String.append(t, String.append(b, c)), str_assoc(t, b, c))

# NLEN, read against LEN: every bit its complement
def compl_nots(+bs: List<&2, Bool>, +a: List<&2, Bool>, +b: List<&2, Bool>) ->
  {D.compl(D.revapp(bs, a), D.revapp(D.nots(bs), b)) == D.compl(a, b) : Bool}:
  match bs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      match h:
        case True{}:
          compl_nots(t, Con{True{}, a}, Con{False{}, b})
        case False{}:
          compl_nots(t, Con{False{}, a}, Con{True{}, b})

# the stream a stored block is read from: at a header, at a byte
def Dec(+dd: Bytes(), +m: Nat, +cap: Nat, +tb: D.Tabs) -> D.St:
  D.St{D.Get{2n, Nil{}, D.KHead{}}, Ob(dd, m, cap, tb), 0n}

# a stored block's bytes, LEN of them
def body(+last: Bool, +cur: Bytes(), +dd: Bytes(), +m: Nat, +cap: Nat, +tb: D.Tabs,
  +vcur: {D.valid(cur) == True{} : Bool}, +room: {Nat.is_le(Nat.add(bl(cur), m), cap) == True{} : Bool}) ->
  {bfeed(bitsof(cur), D.stored_body(last, bl(cur), Ob(dd, m, cap, tb), 0n)) ==
    Aft(last, String.append(dd, cur), Nat.add(bl(cur), m), cap, tb) : D.St}:
  match cur:
    case SNil{}:
      %Equal.sym(Bytes(), String.append(dd, ""), dd, str_nil(dd)) :
        {Aft(last, dd, m, cap, tb) == Aft(last, _, m, cap, tb) : D.St}
      {==}
    case SCon{Chr{+c}, +t}:
      data(last, t, c, dd, m, cap, tb, Bool.and_l(U32.is_lt(c, 256), D.valid(t), vcur),
        Bool.and_r(U32.is_lt(c, 256), D.valid(t), vcur), room)

# a stored block, read at a header
def block(+last: Bool, +cur: Bytes(), +cnt: List<&2, Bool>, +dd: Bytes(), +m: Nat, +cap: Nat, +tb: D.Tabs,
  +el: {List.length(&2, Bool, cnt) == 16n : Nat}, ev: {D.val(cnt) == bl(cur) : Nat},
  +vcur: {D.valid(cur) == True{} : Bool}, +room: {Nat.is_le(Nat.add(bl(cur), m), cap) == True{} : Bool}) ->
  {bfeed(SB(cur, cnt, last), Dec(dd, m, cap, tb)) ==
    Aft(last, String.append(dd, cur), Nat.add(bl(cur), m), cap, tb) : D.St}:
  +out = Aft(last, String.append(dd, cur), Nat.add(bl(cur), m), cap, tb)
  +o = Ob(dd, m, cap, tb)
  +t2 = takeN(16n, D.nots(cnt))
  +el2 = Equal.trans(Nat, List.length(&2, Bool, D.nots(cnt)), List.length(&2, Bool, cnt), 16n, len_nots(cnt), el)
  %Equal.sym(List<&2, Bool>, takeN(16n, cnt), cnt, take_all(cnt, 16n, el)) :
    {bfeed(bitsof(cur), D.stored_nlen(D.compl(D.revapp(_, Nil{}), D.revapp(t2, Nil{})), last,
      D.hval(D.revapp(_, Nil{}), 0n), o, 0n)) == out : D.St}
  %Equal.sym(List<&2, Bool>, t2, D.nots(cnt), take_all(D.nots(cnt), 16n, el2)) :
    {bfeed(bitsof(cur), D.stored_nlen(D.compl(D.revapp(cnt, Nil{}), D.revapp(_, Nil{})), last,
      D.hval(D.revapp(cnt, Nil{}), 0n), o, 0n)) == out : D.St}
  %Equal.sym(Bool, D.compl(D.revapp(cnt, Nil{}), D.revapp(D.nots(cnt), Nil{})), True{},
    compl_nots(cnt, Nil{}, Nil{})) :
    {bfeed(bitsof(cur), D.stored_nlen(_, last, D.hval(D.revapp(cnt, Nil{}), 0n), o, 0n)) == out : D.St}
  %Equal.sym(Nat, D.hval(D.revapp(cnt, Nil{}), 0n), D.val(cnt), hval_rev(cnt)) :
    {bfeed(bitsof(cur), D.stored_body(last, _, o, 0n)) == out : D.St}
  %Equal.sym(Nat, D.val(cnt), bl(cur), ev) :
    {bfeed(bitsof(cur), D.stored_body(last, _, o, 0n)) == out : D.St}
  body(last, cur, dd, m, cap, tb, vcur, room)

# The count
# ---------

def len_inc(+bs: List<&2, Bool>) -> {List.length(&2, Bool, D.inc(bs)) == List.length(&2, Bool, bs) : Nat}:
  match bs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      match h:
        case True{}:
          Equal.cong(Nat, Nat, y => 1n+y, List.length(&2, Bool, D.inc(t)), List.length(&2, Bool, t),
            len_inc(t))
        case False{}:
          {==}

# a count not yet full, one more
def val_inc(+bs: List<&2, Bool>) -> {D.all1(bs) == False{} : Bool} -> {D.val(D.inc(bs)) == 1n+D.val(bs) : Nat}:
  match bs:
    case Nil{}:
      e => Bool.no({D.val(D.inc(Nil{})) == 1n+D.val(Nil{}) : Nat}, Equal.sym(Bool, True{}, False{}, e))
    case Con{+h, +t}:
      match h:
        case True{}:
          e => Equal.cong(Nat, Nat, Nat.double, D.val(D.inc(t)), 1n+D.val(t), val_inc(t)(e))
        case False{}:
          e => {==}

def bl_push(+a: Bytes(), +c: U32) -> {bl(Bytes.push(a, c)) == 1n+bl(a) : Nat}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.cong(Nat, Nat, y => 1n+y, bl(Bytes.push(t, c)), 1n+bl(t), bl_push(t, c))

def valid_push(+a: Bytes(), +c: U32, +va: {D.valid(a) == True{} : Bool},
  +vc: {U32.is_lt(c, 256) == True{} : Bool}) -> {D.valid(Bytes.push(a, c)) == True{} : Bool}:
  match a:
    case SNil{}:
      %Equal.sym(Bool, U32.is_lt(c, 256), True{}, vc) : {Bool.and(_, True{}) == True{} : Bool}
      {==}
    case SCon{Chr{+h}, +t}:
      %Equal.sym(Bool, U32.is_lt(h, 256), True{}, Bool.and_l(U32.is_lt(h, 256), D.valid(t), va)) :
        {Bool.and(_, D.valid(Bytes.push(t, c))) == True{} : Bool}
      valid_push(t, c, Bool.and_r(U32.is_lt(h, 256), D.valid(t), va), vc)

def add_swap(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Nat, 1n+Nat.add(p, Nat.add(b, c)), 1n+Nat.add(b, Nat.add(p, c)), Nat.add(b, 1n+Nat.add(p, c)),
        Equal.cong(Nat, Nat, y => 1n+y, Nat.add(p, Nat.add(b, c)), Nat.add(b, Nat.add(p, c)), add_swap(p, b, c)),
        Equal.sym(Nat, Nat.add(b, 1n+Nat.add(p, c)), 1n+Nat.add(b, Nat.add(p, c)), add_succ(b, Nat.add(p, c))))

def le_addl(+b: Nat, +y: Nat, +cap: Nat) -> {Nat.is_le(Nat.add(b, y), cap) == True{} : Bool} ->
  {Nat.is_le(y, cap) == True{} : Bool}:
  match b:
    case 0n:
      e => e
    case 1n+p:
      e => le_addl(p, y, cap)(le_pred(Nat.add(p, y), cap)(e))

def le_by(+a: Nat, +b: Nat, +cap: Nat, e: {a == b : Nat}, le: {Nat.is_le(b, cap) == True{} : Bool}) ->
  {Nat.is_le(a, cap) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_le(a, cap), Nat.is_le(b, cap), True{},
    Equal.cong(Nat, Bool, y => Nat.is_le(y, cap), a, b, e), le)

# The blocks, one after another
# -----------------------------

# a block written at a byte, read at a header
def flush(+last: Bool, +cur: Bytes(), +cnt: List<&2, Bool>, +ow: Bytes(), +dd: Bytes(), +m: Nat, +cap: Nat,
  +tb: D.Tabs, +s0: D.St, +el: {List.length(&2, Bool, cnt) == 16n : Nat}, ev: {D.val(cnt) == bl(cur) : Nat},
  hdec: {bfeed(bitsof(ow), s0) == Dec(dd, m, cap, tb) : D.St}, +vcur: {D.valid(cur) == True{} : Bool},
  +room: {Nat.is_le(Nat.add(bl(cur), m), cap) == True{} : Bool}) ->
  {bfeed(bitsof(D.w_out(D.stored_one(D.W{ow, Nil{}}, cur, cnt, last))), s0) ==
    Aft(last, String.append(dd, cur), Nat.add(bl(cur), m), cap, tb) : D.St}:
  +so = D.stored_one(D.W{ow, Nil{}}, cur, cnt, last)
  +sb = SB(cur, cnt, last)
  +e1 = Equal.trans(List<&2, Bool>, bitsof(D.w_out(so)), app(bitsof(D.w_out(so)), Nil{}), app(bitsof(ow), sb),
    Equal.sym(List<&2, Bool>, app(bitsof(D.w_out(so)), Nil{}), bitsof(D.w_out(so)), app_nil(bitsof(D.w_out(so)))),
    stored_bits(ow, cur, cnt, last))
  Equal.trans(D.St, bfeed(bitsof(D.w_out(so)), s0), bfeed(app(bitsof(ow), sb), s0),
    Aft(last, String.append(dd, cur), Nat.add(bl(cur), m), cap, tb),
    Equal.cong(List<&2, Bool>, D.St, y => bfeed(y, s0), bitsof(D.w_out(so)), app(bitsof(ow), sb), e1),
    Equal.trans(D.St, bfeed(app(bitsof(ow), sb), s0), bfeed(sb, bfeed(bitsof(ow), s0)),
      Aft(last, String.append(dd, cur), Nat.add(bl(cur), m), cap, tb),
      bfeed_app(bitsof(ow), sb, s0),
      Equal.trans(D.St, bfeed(sb, bfeed(bitsof(ow), s0)), bfeed(sb, Dec(dd, m, cap, tb)),
        Aft(last, String.append(dd, cur), Nat.add(bl(cur), m), cap, tb),
        Equal.cong(D.St, D.St, y => bfeed(sb, y), bfeed(bitsof(ow), s0), Dec(dd, m, cap, tb), hdec),
        block(last, cur, cnt, dd, m, cap, tb, el, ev, vcur, room))))

# the stored blocks of the rest of x, cur filling with cnt its count,
# the stream so far read to dd, m written
def run(+x: Bytes(), +full: Bool, +last: Bool, +cur: Bytes(), +cnt: List<&2, Bool>, +ow: Bytes(), +dd: Bytes(),
  +m: Nat, +cap: Nat, +tb: D.Tabs, +s0: D.St, +ef: {D.all1(cnt) == full : Bool},
  +el: {List.length(&2, Bool, cnt) == 16n : Nat}, +ev: {D.val(cnt) == bl(cur) : Nat},
  +hdec: {bfeed(bitsof(ow), s0) == Dec(dd, m, cap, tb) : D.St}, +vcur: {D.valid(cur) == True{} : Bool},
  +vx: {D.valid(x) == True{} : Bool},
  +room: {Nat.is_le(Nat.add(bl(cur), Nat.add(bl(x), m)), cap) == True{} : Bool}) ->
  {bfeed(bitsof(D.w_out(D.stored.go(x, last, D.SS{cur, cnt, D.W{ow, Nil{}}}))), s0) ==
    Aft(last, String.append(dd, String.append(cur, x)), Nat.add(bl(cur), Nat.add(bl(x), m)), cap, tb) : D.St}:
  match x full:
    case SNil{} _:
      %Equal.sym(Bytes(), String.append(cur, ""), cur, str_nil(cur)) :
        {bfeed(bitsof(D.w_out(D.stored_one(D.W{ow, Nil{}}, cur, cnt, last))), s0) ==
          Aft(last, String.append(dd, _), Nat.add(bl(cur), m), cap, tb) : D.St}
      flush(last, cur, cnt, ow, dd, m, cap, tb, s0, el, ev, hdec, vcur, room)
    case SCon{Chr{+c}, +t} True{}:
      +so = D.stored_one(D.W{ow, Nil{}}, cur, cnt, False{})
      +r = sc(c, t)
      +bc = bl(cur)
      +bt = bl(t)
      +vc = Bool.and_l(U32.is_lt(c, 256), D.valid(t), vx)
      +n1 = Equal.trans(Nat, Nat.add(bc, 1n+Nat.add(bt, m)), 1n+Nat.add(bc, Nat.add(bt, m)),
        1n+Nat.add(bt, Nat.add(bc, m)), add_succ(bc, Nat.add(bt, m)),
        Equal.cong(Nat, Nat, y => 1n+y, Nat.add(bc, Nat.add(bt, m)), Nat.add(bt, Nat.add(bc, m)),
          add_swap(bc, bt, m)))
      %Equal.sym(Bool, D.all1(cnt), True{}, ef) :
        {bfeed(bitsof(D.w_out(D.stored.go(t, last, D.stored.add.at(_, cur, cnt, D.W{ow, Nil{}}, c)))), s0) ==
          Aft(last, String.append(dd, String.append(cur, r)), Nat.add(bc, 1n+Nat.add(bt, m)), cap, tb) : D.St}
      %str_assoc(dd, cur, r) :
        {bfeed(bitsof(D.w_out(D.stored.go(t, last, D.SS{Bytes.push("", c), D.one16(), so}))), s0) ==
          Aft(last, _, Nat.add(bc, 1n+Nat.add(bt, m)), cap, tb) : D.St}
      %Equal.sym(Nat, Nat.add(bc, 1n+Nat.add(bt, m)), 1n+Nat.add(bt, Nat.add(bc, m)), n1) :
        {bfeed(bitsof(D.w_out(D.stored.go(t, last, D.SS{Bytes.push("", c), D.one16(), so}))), s0) ==
          Aft(last, String.append(String.append(dd, cur), r), _, cap, tb) : D.St}
      run(t, False{}, last, Bytes.push("", c), D.one16(), D.w_out(so), String.append(dd, cur), Nat.add(bc, m), cap,
        tb, s0, {==}, {==}, {==},
        flush(False{}, cur, cnt, ow, dd, m, cap, tb, s0, el, ev, hdec, vcur,
          le_addl(1n+bt, Nat.add(bc, m), cap)(le_by(Nat.add(1n+bt, Nat.add(bc, m)), Nat.add(bc, Nat.add(1n+bt, m)),
            cap, add_swap(1n+bt, bc, m), room))),
        valid_push("", c, {==}, vc), Bool.and_r(U32.is_lt(c, 256), D.valid(t), vx),
        le_by(1n+Nat.add(bt, Nat.add(bc, m)), Nat.add(bc, 1n+Nat.add(bt, m)), cap,
          Equal.sym(Nat, Nat.add(bc, 1n+Nat.add(bt, m)), 1n+Nat.add(bt, Nat.add(bc, m)), n1), room))
    case SCon{Chr{+c}, +t} False{}:
      +r = sc(c, t)
      +bt = bl(t)
      +n2 = Equal.trans(Nat, Nat.add(bl(Bytes.push(cur, c)), Nat.add(bt, m)), 1n+Nat.add(bl(cur), Nat.add(bt, m)),
        Nat.add(bl(cur), 1n+Nat.add(bt, m)),
        Equal.cong(Nat, Nat, y => Nat.add(y, Nat.add(bt, m)), bl(Bytes.push(cur, c)), 1n+bl(cur), bl_push(cur, c)),
        Equal.sym(Nat, Nat.add(bl(cur), 1n+Nat.add(bt, m)), 1n+Nat.add(bl(cur), Nat.add(bt, m)),
          add_succ(bl(cur), Nat.add(bt, m))))
      %Equal.sym(Bool, D.all1(cnt), False{}, ef) :
        {bfeed(bitsof(D.w_out(D.stored.go(t, last, D.stored.add.at(_, cur, cnt, D.W{ow, Nil{}}, c)))), s0) ==
          Aft(last, String.append(dd, String.append(cur, r)), Nat.add(bl(cur), 1n+Nat.add(bt, m)), cap, tb) : D.St}
      %push_app(cur, c, t) :
        {bfeed(bitsof(D.w_out(D.stored.go(t, last, D.SS{Bytes.push(cur, c), D.inc(cnt), D.W{ow, Nil{}}}))), s0) ==
          Aft(last, String.append(dd, _), Nat.add(bl(cur), 1n+Nat.add(bt, m)), cap, tb) : D.St}
      %n2 :
        {bfeed(bitsof(D.w_out(D.stored.go(t, last, D.SS{Bytes.push(cur, c), D.inc(cnt), D.W{ow, Nil{}}}))), s0) ==
          Aft(last, String.append(dd, String.append(Bytes.push(cur, c), t)), _, cap, tb) : D.St}
      run(t, D.all1(D.inc(cnt)), last, Bytes.push(cur, c), D.inc(cnt), ow, dd, m, cap, tb, s0, {==},
        Equal.trans(Nat, List.length(&2, Bool, D.inc(cnt)), List.length(&2, Bool, cnt), 16n, len_inc(cnt), el),
        Equal.trans(Nat, D.val(D.inc(cnt)), 1n+D.val(cnt), bl(Bytes.push(cur, c)), val_inc(cnt)(ef),
          Equal.trans(Nat, 1n+D.val(cnt), 1n+bl(cur), bl(Bytes.push(cur, c)),
            Equal.cong(Nat, Nat, y => 1n+y, D.val(cnt), bl(cur), ev),
            Equal.sym(Nat, bl(Bytes.push(cur, c)), 1n+bl(cur), bl_push(cur, c)))),
        hdec, valid_push(cur, c, vcur, Bool.and_l(U32.is_lt(c, 256), D.valid(t), vx)),
        Bool.and_r(U32.is_lt(c, 256), D.valid(t), vx),
        le_by(Nat.add(bl(Bytes.push(cur, c)), Nat.add(bt, m)), Nat.add(bl(cur), 1n+Nat.add(bt, m)), cap, n2, room))

# The stream
# ----------

def blen(+s: Bytes()) -> {Bytes.len(s) == bl(s) : Nat}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.trans(Nat, String.length.go(t, 1n), 1n+String.length.go(t, 0n), 1n+bl(t), Bytes.len.shift(t, 0n),
        Equal.cong(Nat, Nat, y => 1n+y, String.length.go(t, 0n), bl(t), blen(t)))

def drop0(+s: Bytes()) -> {Bytes.drop(s, 0n) == s : Bytes()}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      {==}

# the stored stream of x, read bit by bit, whatever the tables
def stored_read(+x: Bytes(), +cap: Nat, +tb: D.Tabs, +vx: {D.valid(x) == True{} : Bool},
  fits: {Nat.is_le(Bytes.len(x), cap) == True{} : Bool}) ->
  {bfeed(bitsof(D.deflate(x, 0n)), Dec("", 0n, cap, tb)) ==
    D.St{D.End{}, D.O{x, 0n, Nat.add(bl(x), 0n), cap, tb}, 0n} : D.St}:
  run(x, False{}, True{}, "", D.z16(), "", "", 0n, cap, tb, Dec("", 0n, cap, tb), {==}, {==}, {==}, {==}, {==}, vx,
    le_by(Nat.add(bl(x), 0n), bl(x), cap, add_zero(bl(x)),
      le_by(bl(x), Bytes.len(x), cap, Equal.sym(Nat, Bytes.len(x), bl(x), blen(x)), fits)))

# the machine at the end of the stored stream of x
def ended_at(+x: Bytes(), +cap: Nat, +tb: D.Tabs) -> D.St:
  D.St{D.End{}, Ob(x, Nat.add(bl(x), 0n), cap, tb), 0n}

# the stored stream of x, inflated, whatever the tables
def round_trip(+x: Bytes(), +cap: Nat, +tb: D.Tabs, +vx: {D.valid(x) == True{} : Bool},
  +fits: {Nat.is_le(Bytes.len(x), cap) == True{} : Bool}) ->
  {D.finish(D.feed(D.deflate(x, 0n), Dec("", 0n, cap, tb))) == Done{x} : Result<&2, &2, D.Why, Bytes()>}:
  +d = D.deflate(x, 0n)
  +s0 = Dec("", 0n, cap, tb)
  +fin = ended_at(x, cap, tb)
  +e = Equal.trans(D.St, D.feed(d, s0), D.feed_list(Bytes.to_list(d), s0), fin,
    Laws.inflate_buf(d, s0),
    Equal.trans(D.St, D.feed_list(Bytes.to_list(d), s0), bfeed(bitsof(d), s0), fin,
      feed_bits(d, s0), stored_read(x, cap, tb, vx, fits)))
  %Equal.sym(D.St, D.feed(d, s0), fin, e) : {D.finish(_) == Done{x} : Result<&2, &2, D.Why, Bytes()>}
  Equal.cong(Bytes(), Result<&2, &2, D.Why, Bytes()>, y => Done{y}, Bytes.drop(x, 0n), x, drop0(x))

def Laws.stored_round_trip(x, cap, vx, fits):
  round_trip(x, cap, D.tabs(), vx, fits)
