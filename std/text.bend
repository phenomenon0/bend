# Text: the string helpers a program reaching for std/ wants, on any Bend.
#
# Two kinds of String meet in std/. A byte string (what files, sockets,
# Csv and Json hand back) holds one byte a Char; text holds one code
# point a Char, which is what a literal is and what IO.print writes as
# UTF-8. decode turns the first into the second, encode the second into
# the first, so a field read from a file prints as it was written:
#
#   IO.print(Text.decode(field))     # "café", not "cafÃ©"
#
# The rest work on either kind: numbers out of text (nat, u32, f32),
# padding, replace, split_on a string, a stable hash. Every loop is one
# self-recursive def and walks its input once.
import Base
import ./bytes.bend as By

# Building text
# =============

# the chars of acc (newest first) in front of s: a loop, not a deep stack
def rev(acc: List<&2, Char>, s: String) -> String:
  match acc:
    case Nil{}:
      s
    case Con{c, t}:
      rev(t, SCon{c, s})

# UTF-8
# =====

# A decoder's state: between characters (Lead), or need more continuation
# bytes of a character whose code point so far is cp, the next byte in
# [lo, hi] (RFC 3629's table, which refuses overlongs and surrogates).
type Ds is Data:
  Lead{}
  Cont{need: U32, cp: U32, lo: U32, hi: U32}

type Dx is Data:
  Dx{st: Ds, acc: List<&2, Char>, ok: Bool}

def rep() -> Char:
  Chr{65533}

def in(+c: U32, lo: U32, hi: U32) -> Bool:
  U32.is_le(lo, c) && U32.is_le(c, hi)

# what a lead byte starts: an ASCII character, a longer one (its state), or
# nothing (U+FFFD)
type Lk is Data:
  Ascii{}
  Start{st: Ds}
  Stray{}

def lead.kind(+c: U32) -> Lk:
  Bool.pick(Lk, U32.is_lt(c, 128), Ascii{},
  Bool.pick(Lk, in(c, 194, 223), Start{Cont{1, U32.and(c, 31), 128, 191}},
  Bool.pick(Lk, U32.is_eq(c, 224), Start{Cont{2, 0, 160, 191}},
  Bool.pick(Lk, U32.is_eq(c, 237), Start{Cont{2, 13, 128, 159}},
  Bool.pick(Lk, in(c, 225, 239), Start{Cont{2, U32.and(c, 15), 128, 191}},
  Bool.pick(Lk, U32.is_eq(c, 240), Start{Cont{3, 0, 144, 191}},
  Bool.pick(Lk, in(c, 241, 243), Start{Cont{3, U32.and(c, 7), 128, 191}},
  Bool.pick(Lk, U32.is_eq(c, 244), Start{Cont{3, 4, 128, 143}}, Stray{}))))))))

def lead.put(k: Lk, c: U32, acc: List<&2, Char>, ok: Bool) -> Dx:
  match k:
    case Ascii{}:
      Dx{Lead{}, Con{Chr{c}, acc}, ok}
    case Start{st}:
      Dx{st, acc, ok}
    case Stray{}:
      Dx{Lead{}, Con{rep(), acc}, False{}}

# a lead byte: an ASCII character, the start of a longer one, or U+FFFD
def lead.at(+c: U32, acc: List<&2, Char>, ok: Bool) -> Dx:
  lead.put(lead.kind(c), c, acc, ok)

def cont.fit(last: Bool, +need: U32, cp: U32, acc: List<&2, Char>, ok: Bool) -> Dx:
  match last:
    case True{}:
      Dx{Lead{}, Con{Chr{cp}, acc}, ok}
    case False{}:
      Dx{Cont{U32.sub(need, 1), cp, 128, 191}, acc, ok}

# a byte after a lead: it continues the character, or the character was
# cut short (U+FFFD) and the byte is read again as a lead
def cont.at(+c: U32, +need: U32, +cp: U32, fits: Bool, acc: List<&2, Char>, ok: Bool) -> Dx:
  match fits:
    case True{}:
      cont.fit(U32.is_eq(need, 1), need, U32.or(U32.shln(cp, 6n), U32.and(c, 63)), acc, ok)
    case False{}:
      lead.at(c, Con{rep(), acc}, False{})

def step(x: Dx, +c: U32) -> Dx:
  match x:
    case Dx{st, acc, ok}:
      match st:
        case Lead{}:
          lead.at(c, acc, ok)
        case Cont{+need, +cp, +lo, +hi}:
          cont.at(c, need, cp, in(c, lo, hi), acc, ok)

def decode.go(b: String, x: Dx) -> Dx:
  match b:
    case SNil{}:
      x
    case SCon{Chr{+c}, t}:
      decode.go(t, step(x, c))

# the end of the input: a character still open is cut short
def decode.end(x: Dx) -> Dx:
  match x:
    case Dx{st, acc, ok}:
      match st:
        case Lead{}:
          Dx{Lead{}, acc, ok}
        case Cont{need, cp, lo, hi}:
          Dx{Lead{}, Con{rep(), acc}, False{}}

def decode.fin(x: Dx) -> String:
  match x:
    case Dx{st, acc, ok}:
      rev(acc, SNil{})

# a byte string as text: every UTF-8 character its code point, and each
# ill-formed stretch (a stray byte, a character cut short, an overlong or a
# surrogate) U+FFFD, as WHATWG's decoder replaces them
def decode(b: String) -> String:
  decode.fin(decode.end(decode.go(b, Dx{Lead{}, Nil{}, True{}})))

def valid.fin(x: Dx) -> Bool:
  match x:
    case Dx{st, acc, ok}:
      ok

# every byte of b belongs to a well-formed UTF-8 character
def valid(b: String) -> Bool:
  valid.fin(decode.end(decode.go(b, Dx{Lead{}, Nil{}, True{}})))

def cont.byte(+cp: U32, s: Nat) -> U32:
  U32.or(128, U32.and(U32.shrn(cp, s), 63))

def enc.four(o: By.Out(), +cp: U32) -> By.Out():
  By.out.push(By.out.push(By.out.push(By.out.push(o, U32.or(240, U32.shrn(cp, 18n))),
    cont.byte(cp, 12n)), cont.byte(cp, 6n)), cont.byte(cp, 0n))

def enc.three(o: By.Out(), +cp: U32) -> By.Out():
  By.out.push(By.out.push(By.out.push(o, U32.or(224, U32.shrn(cp, 12n))), cont.byte(cp, 6n)),
    cont.byte(cp, 0n))

def enc.two(o: By.Out(), +cp: U32) -> By.Out():
  By.out.push(By.out.push(o, U32.or(192, U32.shrn(cp, 6n))), cont.byte(cp, 0n))

def enc.len(+cp: U32) -> U32:
  Bool.pick(U32, U32.is_lt(cp, 128), 1, Bool.pick(U32, U32.is_lt(cp, 2048), 2,
    Bool.pick(U32, U32.is_lt(cp, 65536), 3, 4)))

def enc.at(k: Nat, o: By.Out(), +cp: U32) -> By.Out():
  match k:
    case 1n:
      By.out.push(o, cp)
    case 2n:
      enc.two(o, cp)
    case 3n:
      enc.three(o, cp)
    case _:
      enc.four(o, cp)

def enc.one(o: By.Out(), +cp: U32) -> By.Out():
  enc.at(U32.to_nat(enc.len(cp)), o, cp)

def encode.go(s: String, o: By.Out()) -> By.Out():
  match s:
    case SNil{}:
      o
    case SCon{Chr{+c}, t}:
      encode.go(t, enc.one(o, c))

# text as its UTF-8 bytes, what a file or a socket should be handed
def encode(s: String) -> String:
  By.out.done(encode.go(s, By.out.new()))

# Numbers
# =======

# the decimal digits of s as a Nat (below 2^48); None for anything else
def nat(s: String) -> Maybe<&2, Nat>:
  Nat.read(s)

# the decimal digits of s as a U32; None for anything else or past 2^32 - 1
def u32(s: String) -> Maybe<&2, U32>:
  U32.read(s)

# a decimal number, with a fraction and an exponent if it has them, as an F32
def f32(s: String) -> Maybe<&2, F32>:
  F32.read(s)

# Strings
# =======

def fill(k: Nat, +c: Char, s: String) -> String:
  match k:
    case 0n:
      s
    case 1n+j:
      fill(j, c, SCon{c, s})

# s with c in front to w chars (none if it has w already)
def pad_start(+s: String, w: Nat, c: Char) -> String:
  fill(Nat.sub(w, String.length(s)), c, s)

# s with c after it to w chars
def pad_end(+s: String, w: Nat, c: Char) -> String:
  String.append(s, fill(Nat.sub(w, String.length(s)), c, SNil{}))

type Rp is Data:
  Rp{rest: String, acc: List<&2, String>, cur: List<&2, Char>}

# one step of a scan for p: at a match, the chars so far go out as a piece
# and the scan skips p; else one char joins the piece
def rp.at(hit: Bool, +k: Nat, h: Char, t: String, acc: List<&2, String>, cur: List<&2, Char>) -> Rp:
  match hit:
    case True{}:
      Rp{String.drop(SCon{h, t}, k), Con{rev(cur, SNil{}), acc}, Nil{}}
    case False{}:
      Rp{t, acc, Con{h, cur}}

def rp.step(+p: String, +k: Nat, r: Rp) -> Rp:
  match r:
    case Rp{rest, acc, cur}:
      match rest:
        case SNil{}:
          Rp{SNil{}, acc, cur}
        case SCon{+h, +t}:
          rp.at(String.starts_with(SCon{h, t}, p), k, h, t, acc, cur)

def rp.go(fuel: Nat, +p: String, +k: Nat, r: Rp) -> Rp:
  match fuel:
    case 0n:
      r
    case 1n+f:
      rp.go(f, p, k, rp.step(p, k, r))

def rp.fin(r: Rp) -> List<&2, String>:
  match r:
    case Rp{rest, acc, cur}:
      List.reverse(&2, String, Con{rev(cur, SNil{}), acc})

# s cut at every p, p itself dropped: split_on("a, b, c", ", ") is
# ["a", "b", "c"]; the empty p does not cut
def split_on.at(empty: Bool, +s: String, +p: String) -> List<&2, String>:
  match empty:
    case True{}:
      [s]
    case False{}:
      rp.fin(rp.go(1n+String.length(s), p, String.length(p), Rp{s, Nil{}, Nil{}}))

def split_on(+s: String, +p: String) -> List<&2, String>:
  split_on.at(String.is_empty(p), s, p)

# every p in s replaced by r, left to right, none overlapping
def replace(+s: String, +p: String, r: String) -> String:
  String.join(split_on(s, p), r)

def hash.byte(h: U32, b: U32) -> U32:
  U32.mul(U32.xor(h, b), 16777619)

def hash.cell(h: U32, +x: U32) -> U32:
  hash.byte(hash.byte(hash.byte(hash.byte(h, U32.and(x, 255)), U32.and(U32.shrn(x, 8n), 255)),
    U32.and(U32.shrn(x, 16n), 255)), U32.shrn(x, 24n))

def hash.go(s: String, h: U32) -> U32:
  match s:
    case SNil{}:
      h
    case SCon{Chr{x}, t}:
      hash.go(t, hash.cell(h, x))

# FNV-1a (32-bit) over four little-endian bytes a char: this repo's
# String.hash, the same number on every Bend
def hash(s: String) -> U32:
  hash.go(s, 2166136261)

# The laws
# ========
#
# Closed instances the checker computes: text through encode and back is
# the text (a char of each length, U+FFFD itself, the largest code point);
# the bytes encode writes are UTF-8's; ill-formed bytes decode to U+FFFD,
# one for a stray byte and one for a cut character whose next byte is
# read again; valid tells the two apart.

law round_trip:
  {decode(encode("aé€\u{1d11e}\u{fffd}\u{10ffff}")) == "aé€\u{1d11e}\u{fffd}\u{10ffff}" : String}

def round_trip():
  {==}

law encode_bytes:
  {By.to_list(encode("é€\u{1d11e}")) == [195, 169, 226, 130, 172, 240, 157, 132, 158] : List<&2, U32>}

def encode_bytes():
  {==}

law decode_bad:
  {decode(By.from_list([97, 128, 195, 40, 237, 160, 128, 240, 159])) ==
    "a\u{fffd}\u{fffd}(\u{fffd}\u{fffd}\u{fffd}\u{fffd}" : String}

def decode_bad():
  {==}

law valid_tells:
  {(valid(encode("€x")), (valid(By.from_list([192, 128])), valid(""))) ==
    (True{}, (False{}, True{})) : Bool & (Bool & Bool)}

def valid_tells():
  {==}

law split_replace:
  {(split_on("a, b,, c", ", "), replace("a-b--c", "--", "+")) ==
    (["a", "b,", "c"], "a-b+c") : List<&2, String> & String}

def split_replace():
  {==}
