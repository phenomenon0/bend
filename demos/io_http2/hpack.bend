# HPACK (RFC 7541), read and written.
#
# The decoder is a reader in bend-wire's sense (wire/reader.bend): one
# byte-step machine over a header block, the whole state in one value,
# never stopping, a refusal absorbing. A header block arrives in pieces
# -- a HEADERS frame and the CONTINUATION frames after it -- and each
# piece is fed in turn, so the kit's feed_split says the pieces never
# matter: the machine lands where it would on the block whole. Nothing
# of the block is kept but the machine.
#
# What the step reads beside the state (the kit's E) is the Huffman
# tree: a server builds it once and every connection shares it.
#
# The encoder writes what the decoder reads. LAWS.bend states the round
# trips (an integer, a Huffman string), the table's bound, the refusals
# of RFC 7541's malformed inputs, and Appendix C's examples.
import Base
import ../../wire/reader.bend as Wr
import ./huff.bend as H

# Fields
# ======

# a header field: a name and a value, both bytes
type Fld is Data:
  Fld{name: Bytes(), value: Bytes()}

# RFC 7541 4.1: a field's size is its name's and value's lengths, plus 32
def fld.size(f: Fld) -> Nat:
  match f:
    case Fld{n, v}:
      Nat.add(Bytes.len(n), Nat.add(Bytes.len(v), 32n))

# the static table (RFC 7541 Appendix A), index 1 first
def static() -> List<&2, Fld>:
  [Fld{":authority", ""}, Fld{":method", "GET"}, Fld{":method", "POST"},
   Fld{":path", "/"}, Fld{":path", "/index.html"}, Fld{":scheme", "http"},
   Fld{":scheme", "https"}, Fld{":status", "200"}, Fld{":status", "204"},
   Fld{":status", "206"}, Fld{":status", "304"}, Fld{":status", "400"},
   Fld{":status", "404"}, Fld{":status", "500"}, Fld{"accept-charset", ""},
   Fld{"accept-encoding", "gzip, deflate"}, Fld{"accept-language", ""},
   Fld{"accept-ranges", ""}, Fld{"accept", ""}, Fld{"access-control-allow-origin", ""},
   Fld{"age", ""}, Fld{"allow", ""}, Fld{"authorization", ""}, Fld{"cache-control", ""},
   Fld{"content-disposition", ""}, Fld{"content-encoding", ""}, Fld{"content-language", ""},
   Fld{"content-length", ""}, Fld{"content-location", ""}, Fld{"content-range", ""},
   Fld{"content-type", ""}, Fld{"cookie", ""}, Fld{"date", ""}, Fld{"etag", ""},
   Fld{"expect", ""}, Fld{"expires", ""}, Fld{"from", ""}, Fld{"host", ""},
   Fld{"if-match", ""}, Fld{"if-modified-since", ""}, Fld{"if-none-match", ""},
   Fld{"if-range", ""}, Fld{"if-unmodified-since", ""}, Fld{"last-modified", ""},
   Fld{"link", ""}, Fld{"location", ""}, Fld{"max-forwards", ""},
   Fld{"proxy-authenticate", ""}, Fld{"proxy-authorization", ""}, Fld{"range", ""},
   Fld{"referer", ""}, Fld{"refresh", ""}, Fld{"retry-after", ""}, Fld{"server", ""},
   Fld{"set-cookie", ""}, Fld{"strict-transport-security", ""},
   Fld{"transfer-encoding", ""}, Fld{"user-agent", ""}, Fld{"vary", ""}, Fld{"via", ""},
   Fld{"www-authenticate", ""}]

# The dynamic table
# =================

# RFC 7541 2.3.2, 4: the entries, newest first, and the most their sizes
# may sum to. Every change keeps the newest entries that fit and evicts
# the rest, so the sum never passes the maximum (LAWS.bend: tbl_fits).
type Tbl is Data:
  Tbl{es: List<&2, Fld>, max: Nat}

def sizes(es: List<&2, Fld>) -> Nat:
  match es:
    case Nil{}:
      0n
    case Con{e, t}:
      Nat.add(fld.size(e), sizes(t))

# the newest entries whose sizes fit in b: an entry that does not fit
# evicts it and everything older (RFC 7541 4.3, 4.4)
def fit.pick(e: Fld, rest: List<&2, Fld>, ok: Bool) -> List<&2, Fld>:
  match ok:
    case True{}:
      Con{e, rest}
    case False{}:
      Nil{}

def fit(es: List<&2, Fld>, +b: Nat) -> List<&2, Fld>:
  match es:
    case Nil{}:
      Nil{}
    case Con{+e, t}:
      +s = fld.size(e)
      fit.pick(e, fit(t, Nat.sub(b, s)), Nat.is_le(s, b))

def tbl.new(max: Nat) -> Tbl:
  Tbl{Nil{}, max}

# an entry added (RFC 7541 4.4): one larger than the table empties it
def tbl.add(t: Tbl, f: Fld) -> Tbl:
  match t:
    case Tbl{es, +max}:
      Tbl{fit(Con{f, es}, max), max}

# a new maximum (RFC 7541 4.3)
def tbl.resize(t: Tbl, +max: Nat) -> Tbl:
  match t:
    case Tbl{es, old}:
      Tbl{fit(es, max), max}

def tbl.max(t: Tbl) -> Nat:
  match t:
    case Tbl{es, max}:
      max

# Index i (RFC 7541 2.3.3): 1 to 61 the static table, 62 on the dynamic
# table, newest first; 0 and past the end are no entry.
def at.go(st: List<&2, Fld>, j: Nat, dy: List<&2, Fld>) -> Maybe<&2, Fld>:
  match st j:
    case Con{f, t} 0n:
      Some{f}
    case Con{f, t} 1n+k:
      at.go(t, k, dy)
    case Nil{} _:
      List.get(&2, Fld, dy, j)

def at(i: Nat, t: Tbl) -> Maybe<&2, Fld>:
  match i t:
    case 0n _:
      None{}
    case 1n+j Tbl{es, max}:
      at.go(static(), j, es)

# Integers (RFC 7541 5.1)
# =======================

# the prefixes HPACK uses: 7 bits (indexed fields, string lengths),
# 6 (literals with indexing), 5 (size updates), 4 (other literals)
type Pfx is Data:
  P4{}
  P5{}
  P6{}
  P7{}

def pfx.max(p: Pfx) -> Nat:
  match p:
    case P4{}:
      15n
    case P5{}:
      31n
    case P6{}:
      63n
    case P7{}:
      127n

# An integer being read: the value so far, the weight of the next
# digit, and how many more continuation bytes may come. Four at most
# (28 bits past the prefix, RFC 7541 5.1's "implementation limits"):
# a fifth that is not the last is refused before anything grows.
type Ist is Data:
  ICont{acc: Nat, mul: Nat, left: Nat}
  IDone{v: Nat}
  IOver{}

def int.cap() -> Nat:
  4n

def int.first.go(max: Nat, p: Nat, lt: Bool) -> Ist:
  match lt:
    case True{}:
      IDone{p}
    case False{}:
      ICont{max, 1n, int.cap()}

# the prefix bits hold the value, or say more follows
def int.first(+max: Nat, +p: Nat) -> Ist:
  int.first.go(max, p, Nat.is_lt(p, max))

def int.more(acc: Nat, +mul: Nat, left: Nat, d: Nat) -> Ist:
  match left:
    case 0n:
      IOver{}
    case 1n+l:
      match l:
        case 0n:
          IOver{}
        case 1n+k:
          ICont{Nat.add(acc, Nat.mul(d, mul)), Nat.mul(mul, 128n), 1n+k}

def int.byte(acc: Nat, +mul: Nat, left: Nat, +b: Nat, hi: Bool) -> Ist:
  match hi:
    case True{}:
      int.more(acc, mul, left, Nat.sub(b, 128n))
    case False{}:
      IDone{Nat.add(acc, Nat.mul(b, mul))}

# one continuation byte: its low seven bits are the next digit, its high
# bit says another follows
def int.step(i: Ist, c: U32) -> Ist:
  match i:
    case ICont{acc, mul, left}:
      +b = U32.to_nat(c)
      int.byte(acc, mul, left, b, Nat.is_le(128n, b))
    case IDone{v}:
      IDone{v}
    case IOver{}:
      IOver{}

def int.feed(bs: List<&2, U32>, i: Ist) -> Ist:
  match bs:
    case Nil{}:
      i
    case Con{c, t}:
      int.feed(t, int.step(i, c))

# an integer read whole: its first byte (prefix bits only), the rest
def int.dec(p: Pfx, bs: List<&2, U32>) -> Ist:
  match bs:
    case Nil{}:
      IOver{}
    case Con{c, t}:
      int.feed(t, int.first(pfx.max(p), U32.to_nat(c)))

# Writing an integer: the prefix bits (flags are the byte's other bits),
# then the rest in base 128, least significant first, the last digit
# without its high bit. k bounds the digits: four, the decoder's cap.
def int.cont(k: Nat, qr: Nat & Nat) -> List<&2, U32>:
  match k:
    case 0n:
      Nil{}
    case 1n+j:
      match qr:
        case (q, r):
          match q:
            case 0n:
              [U32.from_nat(r)]
            case 1n+p:
              Con{U32.from_nat(Nat.add(128n, r)), int.cont(j, Nat.divmod(1n+p, 128n))}

def int.enc.go(+flags: Nat, +max: Nat, +v: Nat, lt: Bool) -> List<&2, U32>:
  match lt:
    case True{}:
      [U32.from_nat(Nat.add(flags, v))]
    case False{}:
      Con{U32.from_nat(Nat.add(flags, max)), int.cont(int.cap(), Nat.divmod(Nat.sub(v, max), 128n))}

def int.enc(p: Pfx, +flags: Nat, +v: Nat) -> List<&2, U32>:
  +max = pfx.max(p)
  int.enc.go(flags, max, v, Nat.is_lt(v, max))

# whether x has at most k digits in base 128: what the continuation
# bytes of an integer can carry under the decoder's cap
def int.fits(k: Nat, x: Nat) -> Bool:
  match k:
    case 0n:
      match x:
        case 0n:
          True{}
        case 1n+y:
          False{}
    case 1n+j:
      int.fits(j, Nat.div(x, 128n))

# Huffman strings (RFC 7541 5.2, Appendix B)
# ==========================================

# A string being decoded: the node the bits so far lead to, and the
# bytes so far; or refused, on EOS in the string.
type Hf is Data:
  HfAt{node: H.Ht, acc: Bytes()}
  HfBad{}

def hf.sym(+root: H.Ht, acc: Bytes(), +sym: U32, eos: Bool) -> Hf:
  match eos:
    case True{}:
      HfBad{}
    case False{}:
      HfAt{root, Bytes.push(acc, sym)}

def hf.leaf(+root: H.Ht, acc: Bytes(), +sym: U32) -> Hf:
  hf.sym(root, acc, sym, U32.is_eq(sym, 256))

def hf.to(+root: H.Ht, next: H.Ht, acc: Bytes()) -> Hf:
  match next:
    case H.HLeaf{sym}:
      hf.leaf(root, acc, sym)
    case H.HNode{end, z, o}:
      HfAt{H.HNode{end, z, o}, acc}

def hf.child(node: H.Ht, bit: Bool) -> H.Ht:
  match node:
    case H.HLeaf{sym}:
      H.HLeaf{256}
    case H.HNode{end, z, o}:
      match bit:
        case False{}:
          z
        case True{}:
          o

# one bit: down the tree, and back to the root with a symbol at a leaf
def hf.bit(+root: H.Ht, h: Hf, bit: Bool) -> Hf:
  match h:
    case HfAt{node, acc}:
      hf.to(root, hf.child(node, bit), acc)
    case HfBad{}:
      HfBad{}

# a byte's bit, from the most significant
def bit(+c: U32, m: U32) -> Bool:
  Bool.not(U32.is_zero(U32.and(c, m)))

# one byte: its eight bits, most significant first
def hf.byte(+root: H.Ht, h: Hf, +c: U32) -> Hf:
  hf.bit(root, hf.bit(root, hf.bit(root, hf.bit(root, hf.bit(root, hf.bit(root, hf.bit(root,
    hf.bit(root, h, bit(c, 128)), bit(c, 64)), bit(c, 32)), bit(c, 16)), bit(c, 8)),
    bit(c, 4)), bit(c, 2)), bit(c, 1))

# the end of the string: at the root, or in padding -- at most seven
# bits, every one a one (EOS's most significant bits)
def hf.end(h: Hf) -> Maybe<&2, Bytes()>:
  match h:
    case HfAt{node, acc}:
      match node:
        case H.HNode{end, z, o}:
          match end:
            case True{}:
              Some{acc}
            case False{}:
              None{}
        case H.HLeaf{s}:
          None{}
    case HfBad{}:
      None{}

def hf.feed(+root: H.Ht, bs: List<&2, U32>, h: Hf) -> Hf:
  match bs:
    case Nil{}:
      h
    case Con{c, t}:
      hf.feed(root, t, hf.byte(root, h, c))

# a whole Huffman string, decoded
def huff.dec(+root: H.Ht, bs: List<&2, U32>) -> Maybe<&2, Bytes()>:
  hf.end(hf.feed(root, bs, HfAt{root, ""}))

# Encoding: each byte's code, the bits packed eight to a byte, the last
# byte padded with ones.
def code(+c: U32) -> List<&2, Bool>:
  H.code8(bit(c, 128), bit(c, 64), bit(c, 32), bit(c, 16), bit(c, 8), bit(c, 4), bit(c, 2),
    bit(c, 1))

def huff.bits(s: Bytes()) -> List<&2, Bool>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{Chr{c}, t}:
      List.append(&2, Bool, code(c), huff.bits(t))

def b2n(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# eight bits, most significant first, as a byte
def pack8(b7: Bool, b6: Bool, b5: Bool, b4: Bool, b3: Bool, b2: Bool, b1: Bool, b0: Bool) -> U32:
  U32.from_nat(Nat.add(Nat.mul(b2n(b7), 128n), Nat.add(Nat.mul(b2n(b6), 64n),
    Nat.add(Nat.mul(b2n(b5), 32n), Nat.add(Nat.mul(b2n(b4), 16n), Nat.add(Nat.mul(b2n(b3), 8n),
    Nat.add(Nat.mul(b2n(b2), 4n), Nat.add(Nat.mul(b2n(b1), 2n), b2n(b0)))))))))

def pad.t() -> Bool:
  True{}

def chunk8(bs: List<&2, Bool>) -> List<&2, U32>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{a, Nil{}}:
      [pack8(a, pad.t(), pad.t(), pad.t(), pad.t(), pad.t(), pad.t(), pad.t())]
    case Con{a, Con{b, Nil{}}}:
      [pack8(a, b, pad.t(), pad.t(), pad.t(), pad.t(), pad.t(), pad.t())]
    case Con{a, Con{b, Con{c, Nil{}}}}:
      [pack8(a, b, c, pad.t(), pad.t(), pad.t(), pad.t(), pad.t())]
    case Con{a, Con{b, Con{c, Con{d, Nil{}}}}}:
      [pack8(a, b, c, d, pad.t(), pad.t(), pad.t(), pad.t())]
    case Con{a, Con{b, Con{c, Con{d, Con{e, Nil{}}}}}}:
      [pack8(a, b, c, d, e, pad.t(), pad.t(), pad.t())]
    case Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, Nil{}}}}}}}:
      [pack8(a, b, c, d, e, f, pad.t(), pad.t())]
    case Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, Con{g, Nil{}}}}}}}}:
      [pack8(a, b, c, d, e, f, g, pad.t())]
    case Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, Con{g, Con{h, t}}}}}}}}:
      Con{pack8(a, b, c, d, e, f, g, h), chunk8(t)}

def huff.enc(s: Bytes()) -> List<&2, U32>:
  chunk8(huff.bits(s))

# Strings (RFC 7541 5.2)
# ======================

# a string: its length (7-bit prefix, the high bit set for Huffman),
# then its bytes, Huffman coded or as they are
def str.go(+h: List<&2, U32>, +raw: Bytes(), huff: Bool) -> List<&2, U32>:
  match huff:
    case True{}:
      List.append(&2, U32, int.enc(P7{}, 128n, List.length(&2, U32, h)), h)
    case False{}:
      List.append(&2, U32, int.enc(P7{}, 0n, Bytes.len(raw)), Bytes.to_list(raw))

def str.enc(+s: Bytes(), huff: Bool) -> List<&2, U32>:
  match huff:
    case True{}:
      str.go(huff.enc(s), s, True{})
    case False{}:
      str.go(Nil{}, s, False{})


# The decoder
# ===========

# what a literal does to the table: adds itself (incremental indexing),
# or not (without indexing, never indexed)
type Rep is Data:
  KInc{}
  KNot{}
  KNever{}

# why a block was refused, each a decoding error (RFC 7541 3.1): an
# index with no entry, an integer past the cap, a Huffman string with
# EOS or bad padding, a size update past the limit or after a field, a
# string or a field list past the cap, a block cut off mid-field
type Err is Data:
  EIdx{}
  EInt{}
  EHuff{}
  ESize{}
  EStr{}
  EList{}
  ECut{}

# what a string is being read for
type For is Data:
  FName{k: Rep}
  FVal{k: Rep, name: Bytes()}

# what an integer is being read for
type To is Data:
  TIdx{}
  TName{k: Rep}
  TSize{}
  TLen{fo: For, h: Bool}

# a string's bytes as they come: as they are, or Huffman coded
type Sb is Data:
  SRaw{acc: Bytes()}
  SHuf{hf: Hf}

# ATop   a representation's first byte
# ALen   a string's first byte: the Huffman bit, its length's prefix
# AInt   an integer's continuation bytes
# AStr   a string's bytes, left more after the next
# ABad   refused; absorbing, never left
type At is Data:
  ATop{}
  ALen{fo: For}
  AInt{to: To, i: Ist}
  AStr{fo: For, left: Nat, sb: Sb}
  ABad{why: Err}

# The limits the decoder keeps: the most a size update may set the
# table to (our SETTINGS_HEADER_TABLE_SIZE, RFC 7541 4.2), and the most
# a block's fields may sum to (our SETTINGS_MAX_HEADER_LIST_SIZE, RFC
# 9113 6.5.2), which also caps any one string.
type Lim is Data:
  Lim{tmax: Nat, lmax: Nat}

def lim.t(l: Lim) -> Nat:
  match l:
    case Lim{tmax, lmax}:
      tmax

def lim.l(l: Lim) -> Nat:
  match l:
    case Lim{tmax, lmax}:
      lmax

# The whole decoder: where it is, the table, the fields of this block
# (newest first) and their sizes' sum, whether a field has come yet in
# this block (a size update must come first), and the limits.
type Dec is Data:
  Dc{at: At, t: Tbl, out: List<&2, Fld>, sz: Nat, any: Bool, lim: Lim}

def dec.new(+tmax: Nat, lmax: Nat) -> Dec:
  Dc{ATop{}, tbl.new(tmax), Nil{}, 0n, False{}, Lim{tmax, lmax}}

def bad(t: Tbl, out: List<&2, Fld>, sz: Nat, any: Bool, lim: Lim, why: Err) -> Dec:
  Dc{ABad{why}, t, out, sz, any, lim}

# A field decoded: into the block's list, under the list's cap, and
# into the table when its kind says so.
def field.kind(k: Rep, t: Tbl, +f: Fld) -> Tbl:
  match k:
    case KInc{}:
      tbl.add(t, f)
    case KNot{}:
      t
    case KNever{}:
      t

def field.cap(k: Rep, t: Tbl, out: List<&2, Fld>, sz: Nat, s2: Nat, lim: Lim, +f: Fld, ok: Bool) -> Dec:
  match ok:
    case True{}:
      Dc{ATop{}, field.kind(k, t, f), Con{f, out}, s2, True{}, lim}
    case False{}:
      bad(t, out, sz, True{}, lim, EList{})

def field(k: Rep, t: Tbl, out: List<&2, Fld>, +sz: Nat, +lim: Lim, +f: Fld) -> Dec:
  +s2 = Nat.add(sz, fld.size(f))
  field.cap(k, t, out, sz, s2, lim, f, Nat.is_le(s2, lim.l(lim)))

# an indexed field (RFC 7541 6.1)
def got.idx(t: Tbl, out: List<&2, Fld>, sz: Nat, lim: Lim, m: Maybe<&2, Fld>) -> Dec:
  match m:
    case None{}:
      bad(t, out, sz, True{}, lim, EIdx{})
    case Some{f}:
      field(KNot{}, t, out, sz, lim, f)

# a literal's indexed name (RFC 7541 6.2): its value's string is next
def got.name(k: Rep, t: Tbl, out: List<&2, Fld>, sz: Nat, lim: Lim, m: Maybe<&2, Fld>) -> Dec:
  match m:
    case None{}:
      bad(t, out, sz, True{}, lim, EIdx{})
    case Some{f}:
      match f:
        case Fld{n, v}:
          Dc{ALen{FVal{k, n}}, t, out, sz, True{}, lim}

# A size update (RFC 7541 6.3): only before the block's first field,
# and never past the limit our settings allow.
def got.size(t: Tbl, out: List<&2, Fld>, sz: Nat, any: Bool, lim: Lim, +v: Nat, ok: Bool) -> Dec:
  match ok:
    case True{}:
      Dc{ATop{}, tbl.resize(t, v), out, sz, any, lim}
    case False{}:
      bad(t, out, sz, any, lim, ESize{})

# a string complete: a name goes on to its value, a value completes
# its field
def str.done(fo: For, m: Maybe<&2, Bytes()>, t: Tbl, out: List<&2, Fld>, sz: Nat, lim: Lim) -> Dec:
  match fo m:
    case _ None{}:
      bad(t, out, sz, True{}, lim, EHuff{})
    case FName{k} Some{s}:
      Dc{ALen{FVal{k, s}}, t, out, sz, True{}, lim}
    case FVal{k, name} Some{s}:
      field(k, t, out, sz, lim, Fld{name, s})

def str.sb(+root: H.Ht, h: Bool) -> Sb:
  match h:
    case True{}:
      SHuf{HfAt{root, ""}}
    case False{}:
      SRaw{""}

# a string's bytes read whole: as they are, or decoded and its padding
# checked
def str.fin(sb: Sb) -> Maybe<&2, Bytes()>:
  match sb:
    case SRaw{acc}:
      Some{acc}
    case SHuf{hf}:
      hf.end(hf)

# a string's length: an empty string is complete at once; one past the
# list's cap is refused before a byte of it is kept, so a string that
# claims to be huge costs nothing
def str.len(+root: H.Ht, fo: For, h: Bool, t: Tbl, out: List<&2, Fld>, sz: Nat, lim: Lim, n: Nat) -> Dec:
  match n:
    case 0n:
      str.done(fo, str.fin(str.sb(root, h)), t, out, sz, lim)
    case 1n+m:
      Dc{AStr{fo, m, str.sb(root, h)}, t, out, sz, True{}, lim}

def str.start(+root: H.Ht, fo: For, h: Bool, t: Tbl, out: List<&2, Fld>, sz: Nat, +lim: Lim, +n: Nat, ok: Bool) -> Dec:
  match ok:
    case True{}:
      str.len(root, fo, h, t, out, sz, lim, n)
    case False{}:
      bad(t, out, sz, True{}, lim, EStr{})

# an integer complete
def int.done(+root: H.Ht, to: To, +v: Nat, +t: Tbl, out: List<&2, Fld>, sz: Nat, +any: Bool, +lim: Lim) -> Dec:
  match to:
    case TIdx{}:
      got.idx(t, out, sz, lim, at(v, t))
    case TName{k}:
      got.name(k, t, out, sz, lim, at(v, t))
    case TSize{}:
      got.size(t, out, sz, any, lim, v, Bool.not(any) && Nat.is_le(v, lim.t(lim)))
    case TLen{fo, h}:
      str.start(root, fo, h, t, out, sz, lim, v, Nat.is_le(v, lim.l(lim)))

def int.at(+root: H.Ht, to: To, i: Ist, t: Tbl, out: List<&2, Fld>, sz: Nat, any: Bool, lim: Lim) -> Dec:
  match i:
    case IDone{v}:
      int.done(root, to, v, t, out, sz, any, lim)
    case ICont{acc, mul, left}:
      Dc{AInt{to, ICont{acc, mul, left}}, t, out, sz, any, lim}
    case IOver{}:
      bad(t, out, sz, any, lim, EInt{})

# A literal's first byte: index 0 is a new name, a string next; any
# other names a table entry.
def lit(+root: H.Ht, k: Rep, p: Pfx, v: Nat, t: Tbl, out: List<&2, Fld>, sz: Nat, lim: Lim) -> Dec:
  match v:
    case 0n:
      Dc{ALen{FName{k}}, t, out, sz, True{}, lim}
    case 1n+j:
      int.at(root, TName{k}, int.first(pfx.max(p), 1n+j), t, out, sz, True{}, lim)

# A representation's first byte (RFC 7541 6): 1xxxxxxx indexed,
# 01xxxxxx literal with incremental indexing, 001xxxxx a size update,
# 0001xxxx never indexed, 0000xxxx without indexing.
def top.go(+root: H.Ht, +b: Nat, t: Tbl, out: List<&2, Fld>, sz: Nat, any: Bool, lim: Lim,
  ix: Bool, inc: Bool, up: Bool, nev: Bool) -> Dec:
  match ix inc up nev:
    case True{} _ _ _:
      int.at(root, TIdx{}, int.first(127n, Nat.sub(b, 128n)), t, out, sz, True{}, lim)
    case False{} True{} _ _:
      lit(root, KInc{}, P6{}, Nat.sub(b, 64n), t, out, sz, lim)
    case False{} False{} True{} _:
      int.at(root, TSize{}, int.first(31n, Nat.sub(b, 32n)), t, out, sz, any, lim)
    case False{} False{} False{} True{}:
      lit(root, KNever{}, P4{}, Nat.sub(b, 16n), t, out, sz, lim)
    case False{} False{} False{} False{}:
      lit(root, KNot{}, P4{}, b, t, out, sz, lim)

def top(+root: H.Ht, +b: Nat, t: Tbl, out: List<&2, Fld>, sz: Nat, any: Bool, lim: Lim) -> Dec:
  top.go(root, b, t, out, sz, any, lim, Nat.is_le(128n, b), Nat.is_le(64n, b), Nat.is_le(32n, b),
    Nat.is_le(16n, b))

# a string's first byte: the Huffman bit, and its length's prefix
def len.go(+root: H.Ht, fo: For, +b: Nat, t: Tbl, out: List<&2, Fld>, sz: Nat, lim: Lim, h: Bool) -> Dec:
  match h:
    case True{}:
      int.at(root, TLen{fo, True{}}, int.first(127n, Nat.sub(b, 128n)), t, out, sz, True{}, lim)
    case False{}:
      int.at(root, TLen{fo, False{}}, int.first(127n, b), t, out, sz, True{}, lim)

# the string's bytes so far, with one more
def sb.byte(+root: H.Ht, sb: Sb, +c: U32) -> Sb:
  match sb:
    case SRaw{acc}:
      SRaw{Bytes.push(acc, c)}
    case SHuf{hf}:
      SHuf{hf.byte(root, hf, c)}

def str.byte(fo: For, left: Nat, sb: Sb, t: Tbl, out: List<&2, Fld>, sz: Nat, lim: Lim) -> Dec:
  match left:
    case 0n:
      str.done(fo, str.fin(sb), t, out, sz, lim)
    case 1n+m:
      Dc{AStr{fo, m, sb}, t, out, sz, True{}, lim}

def step.at(+root: H.Ht, at: At, t: Tbl, out: List<&2, Fld>, sz: Nat, any: Bool, lim: Lim, +c: U32) -> Dec:
  match at:
    case ATop{}:
      top(root, U32.to_nat(c), t, out, sz, any, lim)
    case ALen{fo}:
      +b = U32.to_nat(c)
      len.go(root, fo, b, t, out, sz, lim, Nat.is_le(128n, b))
    case AInt{to, i}:
      int.at(root, to, int.step(i, c), t, out, sz, any, lim)
    case AStr{fo, left, sb}:
      str.byte(fo, left, sb.byte(root, sb, c), t, out, sz, lim)
    case ABad{why}:
      Dc{ABad{why}, t, out, sz, any, lim}

# one byte of a header block
def step(+root: H.Ht, d: Dec, c: U32) -> Dec:
  match d:
    case Dc{at, t, out, sz, any, lim}:
      step.at(root, at, t, out, sz, any, lim, c)

# The walk, from the kit: the Huffman tree beside the state, one byte a
# move (a raw string's run could be taken whole; a block is small).
def wstep(root: H.Ht, d: Dec, c: U32) -> Dec:
  step(root, d, c)

def wadv(root: H.Ht, s: Bytes(), d: Dec) -> Dec & Bytes():
  Wr.one.step(~H.Ht, ~Dec, ~wstep, root, s, d)

def feed(+root: H.Ht, bs: List<&2, U32>, d: Dec) -> Dec:
  Wr.feed(~H.Ht, ~Dec, ~wstep, root, bs, d)

def feed_buf(+root: H.Ht, +s: Bytes(), d: Dec) -> Dec:
  Wr.feed_buf(~H.Ht, ~Dec, ~wstep, ~wadv, root, s, d)

# A header block begins: its fields and their sizes start empty, and a
# size update may come first again.
def dec.begin(d: Dec) -> Dec:
  match d:
    case Dc{at, t, out, sz, any, lim}:
      Dc{at, t, Nil{}, 0n, False{}, lim}

# A header block ends (END_HEADERS): it must end between fields; what
# it decoded comes out oldest first, and the table goes on.
type Blk is Data:
  BOk{d: Dec, fs: List<&2, Fld>}
  BBad{why: Err}

def dec.end(d: Dec) -> Blk:
  match d:
    case Dc{at, t, out, sz, any, lim}:
      match at:
        case ATop{}:
          BOk{Dc{ATop{}, t, Nil{}, 0n, False{}, lim}, List.reverse(&2, Fld, out)}
        case ABad{why}:
          BBad{why}
        case _:
          BBad{ECut{}}

# a whole block
def block(+root: H.Ht, d: Dec, bs: List<&2, U32>) -> Blk:
  dec.end(feed(root, bs, dec.begin(d)))

# The encoder
# ===========

# two byte strings equal, read where they are
def beq.go(k: Nat, +a: Bytes(), +b: Bytes(), +i: Nat, same: Bool) -> Bool:
  match k same:
    case _ False{}:
      False{}
    case 0n True{}:
      True{}
    case 1n+j True{}:
      beq.go(j, a, b, 1n+i, U32.is_eq(Bytes.get(a, i), Bytes.get(b, i)))

def beq(+a: Bytes(), +b: Bytes()) -> Bool:
  beq.go(Bytes.len(a), a, b, 0n, Nat.is_eq(Bytes.len(a), Bytes.len(b)))

# The static table by name, for the encoder: a search tree on a name's
# length, first byte and last byte (which tell every name in the table
# apart), each node the name, the index of its first entry and the
# values of its entries in order. LAWS.bend (static_index) checks it
# against the table, entry by entry.
type Sx is Data:
  SxNil{}
  SxAt{key: U32, name: Bytes(), at: Nat, vals: List<&2, Bytes()>, lo: Sx, hi: Sx}

def static.names() -> Sx:
  SxAt{685428, "user-agent", 58n, [""],
    SxAt{419188, "expect", 35n, [""],
      SxAt{289899, "link", 45n, [""],
        SxAt{288103, "etag", 34n, [""],
          SxAt{226913, "via", 60n, [""],
            SxAt{221541, "age", 21n, [""], SxNil{}, SxNil{}},
            SxAt{287845, "date", 33n, [""], SxNil{}, SxNil{}}},
          SxAt{288884, "host", 38n, [""],
            SxAt{288365, "from", 37n, [""], SxNil{}, SxNil{}},
            SxNil{}}},
        SxAt{356965, "range", 50n, [""],
          SxAt{342632, ":path", 4n, ["/", "/index.html"],
            SxAt{292473, "vary", 59n, [""], SxNil{}, SxNil{}},
            SxAt{352631, "allow", 22n, [""], SxNil{}, SxNil{}}},
          SxAt{418661, "cookie", 32n, [""],
            SxAt{418164, "accept", 19n, [""], SxNil{}, SxNil{}},
            SxNil{}}}},
      SxAt{488050, "referer", 51n, [""],
        SxAt{473715, ":status", 8n, ["200", "204", "206", "304", "400", "404", "500"],
          SxAt{473700, ":method", 2n, ["GET", "POST"],
            SxAt{422770, "server", 54n, [""], SxNil{}, SxNil{}},
            SxAt{473701, ":scheme", 6n, ["http", "https"], SxNil{}, SxNil{}}},
          SxAt{488040, "refresh", 52n, [""],
            SxAt{484723, "expires", 36n, [""], SxNil{}, SxNil{}},
            SxNil{}}},
        SxAt{552046, "location", 46n, [""],
          SxAt{551272, "if-match", 39n, [""],
            SxAt{551269, "if-range", 42n, [""], SxNil{}, SxNil{}},
            SxNil{}},
          SxAt{684901, "set-cookie", 55n, [""],
            SxAt{670329, ":authority", 1n, [""], SxNil{}, SxNil{}},
            SxNil{}}}}},
    SxAt{1007975, "accept-encoding", 16n, ["gzip, deflate"],
      SxAt{877420, "cache-control", 24n, [""],
        SxAt{876910, "authorization", 23n, [""],
          SxAt{811877, "content-type", 31n, [""],
            SxAt{750194, "retry-after", 53n, [""], SxNil{}, SxNil{}},
            SxAt{814451, "max-forwards", 47n, [""], SxNil{}, SxNil{}}},
          SxAt{877413, "content-range", 30n, [""],
            SxAt{876915, "accept-ranges", 18n, [""], SxNil{}, SxNil{}},
            SxNil{}}},
        SxAt{942452, "accept-charset", 15n, [""],
          SxAt{879716, "last-modified", 44n, [""],
            SxAt{878952, "if-none-match", 41n, [""], SxNil{}, SxNil{}},
            SxNil{}},
          SxAt{1007973, "accept-language", 17n, [""],
            SxAt{942952, "content-length", 28n, [""], SxNil{}, SxNil{}},
            SxNil{}}}},
      SxAt{1208421, "proxy-authenticate", 48n, [""],
        SxAt{1079141, "www-authenticate", 61n, [""],
          SxAt{1074023, "content-encoding", 26n, [""],
            SxAt{1074021, "content-language", 27n, [""], SxNil{}, SxNil{}},
            SxAt{1074030, "content-location", 29n, [""], SxNil{}, SxNil{}}},
          SxAt{1143911, "transfer-encoding", 57n, [""],
            SxAt{1141093, "if-modified-since", 40n, [""], SxNil{}, SxNil{}},
            SxNil{}}},
        SxAt{1273966, "proxy-authorization", 49n, [""],
          SxAt{1272165, "if-unmodified-since", 43n, [""],
            SxAt{1270638, "content-disposition", 25n, [""], SxNil{}, SxNil{}},
            SxNil{}},
          SxAt{1794414, "access-control-allow-origin", 20n, [""],
            SxAt{1667961, "strict-transport-security", 56n, [""], SxNil{}, SxNil{}},
            SxNil{}}}}}}

def name.key(+n: Bytes()) -> U32:
  U32.add(U32.shln(U32.from_nat(Bytes.len(n)), 16n),
    U32.add(U32.shln(Bytes.get(n, 0n), 8n), Bytes.get(n, Nat.sub(Bytes.len(n), 1n))))

# the first index (from i on) whose entry is exactly f, and the first
# whose name is f's
type Hit is Data:
  Hit{full: Maybe<&2, Nat>, name: Maybe<&2, Nat>}

def hit.or(m: Maybe<&2, Nat>, +i: Nat, ok: Bool) -> Maybe<&2, Nat>:
  match m:
    case Some{j}:
      Some{j}
    case None{}:
      match ok:
        case True{}:
          Some{i}
        case False{}:
          None{}

def hit.one(h: Hit, +i: Nat, e: Fld, f: Fld) -> Hit:
  match h e f:
    case Hit{full, name} Fld{+en, ev} Fld{+fn, fv}:
      Hit{hit.or(full, i, beq(en, fn) && beq(ev, fv)), hit.or(name, i, beq(en, fn))}

# where a name's key sits against a node's
def sx.cmp(+t: Sx, +k: U32) -> Cmp:
  match t:
    case SxNil{}:
      EQ{}
    case SxAt{key, name, at, vals, lo, hi}:
      U32.cmp(k, key)

def sx.head(+vs: List<&2, Bytes()>, +v: Bytes()) -> Bool:
  match vs:
    case Nil{}:
      False{}
    case Con{+x, t}:
      beq(x, v)

# the index of the first of a name's values that is v (hit: the head is)
def sx.vals(vs: List<&2, Bytes()>, +i: Nat, +v: Bytes(), hit: Bool) -> Maybe<&2, Nat>:
  match vs hit:
    case Nil{} _:
      None{}
    case Con{x, t} True{}:
      Some{i}
    case Con{x, +t} False{}:
      sx.vals(t, 1n+i, v, sx.head(t, v))

def sx.hit(ok: Bool, +at: Nat, +vals: List<&2, Bytes()>, +v: Bytes()) -> Hit:
  match ok:
    case False{}:
      Hit{None{}, None{}}
    case True{}:
      Hit{sx.vals(vals, at, v, sx.head(vals, v)), Some{at}}

def sx.find(t: Sx, +k: U32, +n: Bytes(), +v: Bytes(), c: Cmp) -> Hit:
  match t c:
    case SxNil{} _:
      Hit{None{}, None{}}
    case SxAt{key, name, at, vals, +lo, hi} LT{}:
      sx.find(lo, k, n, v, sx.cmp(lo, k))
    case SxAt{key, name, at, vals, lo, +hi} GT{}:
      sx.find(hi, k, n, v, sx.cmp(hi, k))
    case SxAt{key, +name, +at, +vals, lo, hi} EQ{}:
      sx.hit(beq(name, n), at, vals, v)

# what a scan of the static table would find for f: the first entry
# exactly f, and the first with f's name (a name's entries are next to
# each other there)
def static.find(+f: Fld) -> Hit:
  match f:
    case Fld{+n, +v}:
      +k = name.key(n)
      sx.find(static.names(), k, n, v, sx.cmp(static.names(), k))

# The scan stops at the first entry exactly equal: by then the first
# entry with f's name is already found (it is that one, or earlier), so
# the answer is the one a scan to the end would give.
def find(es: List<&2, Fld>, +i: Nat, +f: Fld, h: Hit) -> Hit:
  match es:
    case Nil{}:
      h
    case Con{e, t}:
      match h:
        case Hit{full, name}:
          match full:
            case Some{j}:
              Hit{Some{j}, name}
            case None{}:
              find(t, 1n+i, f, hit.one(Hit{None{}, name}, i, e, f))

# A field written against the encoder's own table, as RFC 7541 Appendix
# C's encoder writes it: an entry exactly equal is indexed; a name in
# the table is a literal with incremental indexing naming it; anything
# else a literal with incremental indexing and a new name. The table
# takes what the decoder's will.
type Enc is Data:
  Enc{t: Tbl, out: List<&2, U32>}

def enc.lit(t: Tbl, out: List<&2, U32>, f: Fld, name: Maybe<&2, Nat>, +huff: Bool) -> Enc:
  match f:
    case Fld{+fname, +fval}:
      match name:
        case Some{n}:
          Enc{tbl.add(t, Fld{fname, fval}), List.append(&2, U32, out,
            List.append(&2, U32, int.enc(P6{}, 64n, n), str.enc(fval, huff)))}
        case None{}:
          Enc{tbl.add(t, Fld{fname, fval}), List.append(&2, U32, out,
            Con{64, List.append(&2, U32, str.enc(fname, huff), str.enc(fval, huff))})}

def enc.hit(t: Tbl, out: List<&2, U32>, f: Fld, h: Hit, huff: Bool) -> Enc:
  match h:
    case Hit{full, name}:
      match full:
        case Some{i}:
          Enc{t, List.append(&2, U32, out, int.enc(P7{}, 128n, i))}
        case None{}:
          enc.lit(t, out, f, name, huff)

def enc.field(e: Enc, +f: Fld, huff: Bool) -> Enc:
  match e:
    case Enc{t, out}:
      match t:
        case Tbl{+es, max}:
          enc.hit(Tbl{es, max}, out, f, find(es, 62n, f, static.find(f)), huff)

def enc.fields(fs: List<&2, Fld>, e: Enc, +huff: Bool) -> Enc:
  match fs:
    case Nil{}:
      e
    case Con{f, t}:
      enc.fields(t, enc.field(e, f, huff), huff)

# a header block for fs, and the table after it
def encode(t: Tbl, fs: List<&2, Fld>, +huff: Bool) -> Enc:
  enc.fields(fs, Enc{t, Nil{}}, huff)
