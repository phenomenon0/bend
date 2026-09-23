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
