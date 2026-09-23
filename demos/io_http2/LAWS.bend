# The laws of the HTTP/2 server: what HPACK (RFC 7541) and the frame
# layer (RFC 9113) must do, stated for every input where the claim is
# universal, and on the RFCs' own vectors where it is a fact about them.
# PROOF.bend proves each one.
import Base
import ../../wire/reader.bend as Wr
import ./huff.bend as H
import ./hpack.bend as K
import ./vectors.bend as V
import ./frame.bend as Fm
import ./spec.bend as Sp

# HPACK: integers (RFC 7541 5.1)
# ==============================

# LAW: an integer written with any prefix reads back as itself, for
# every value the decoder's cap admits: what is past the prefix fits in
# its four continuation bytes (below 2^28).
law int_rt:
  for +p: K.Pfx
  for +v: Nat
  for h: {K.int.fits(K.int.cap(), Nat.sub(v, K.pfx.max(p))) == True{} : Bool}
  {K.int.dec(p, K.int.enc(p, 0n, v)) == K.IDone{v} : K.Ist}

# RFC 7541 C.1: 10 in a 5-bit prefix, 1337 in a 5-bit prefix, 42 at an
# octet boundary
law int_c1_1:
  {K.int.enc(K.P5{}, 0n, 10n) == [10] : List<&2, U32>}

law int_c1_2:
  {K.int.enc(K.P5{}, 0n, 1337n) == [31, 154, 10] : List<&2, U32>}

law int_c1_3:
  {K.int.dec(K.P7{}, [42]) == K.IDone{42n} : K.Ist}

# LAW: past the cap, refused: a fifth continuation byte that is not the
# last is an error, before any value grows
law int_over:
  {K.int.dec(K.P7{}, [127, 255, 255, 255, 255, 1]) == K.IOver{} : K.Ist}

# HPACK: Huffman strings (RFC 7541 5.2, Appendix B)
# =================================================

# a byte as eight bits, least significant first: every byte is one
def byte(w: Word(8n)) -> U32:
  match w:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WNil{}}}}}}}}}:
      U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7,
        Word.zero(24n)}}}}}}}}}

def bytes(ws: List<&2, Word(8n)>) -> Bytes():
  match ws:
    case Nil{}:
      SNil{}
    case Con{w, t}:
      SCon{Chr{byte(w)}, bytes(t)}

# LAW: every byte string, Huffman coded, decodes to itself: the code is
# RFC 7541's (the tree and the codes are one table, gen.py's), the last
# byte's padding is EOS's high bits, and the decoder accepts it.
law huff_rt:
  for +ws: List<&2, Word(8n)>
  {K.huff.dec(H.tree(), K.huff.enc(bytes(ws))) == Some{bytes(ws)} : Maybe<&2, Bytes()>}

# LAW: EOS in a string is refused, and so is padding that is longer
# than seven bits or not all ones (RFC 7541 5.2)
law huff_eos:
  {K.huff.dec(H.tree(), [255, 255, 255, 255]) == None{} : Maybe<&2, Bytes()>}

law huff_pad_long:
  {K.huff.dec(H.tree(), [31, 255]) == None{} : Maybe<&2, Bytes()>}

law huff_pad_zero:
  {K.huff.dec(H.tree(), [24]) == None{} : Maybe<&2, Bytes()>}

# HPACK: the dynamic table (RFC 7541 4)
# =====================================

def fits(t: K.Tbl) -> Bool:
  match t:
    case K.Tbl{es, max}:
      Nat.is_le(K.sizes(es), max)

# LAW: the entries kept always fit: whatever the entries and the
# budget, what fit keeps sums to at most the budget ...
law fit_le:
  for es: List<&2, K.Fld>
  for +b: Nat
  {Nat.is_le(K.sizes(K.fit(es, b)), b) == True{} : Bool}

# ... so every table an entry is added to, or resized, fits its maximum,
# whatever it held before
law tbl_add_fits:
  for t: K.Tbl
  for f: K.Fld
  {fits(K.tbl.add(t, f)) == True{} : Bool}

law tbl_resize_fits:
  for t: K.Tbl
  for m: Nat
  {fits(K.tbl.resize(t, m)) == True{} : Bool}

# HPACK: the decoder's refusals (RFC 7541 3.1, 5, 6)
# ==================================================

def fresh() -> K.Dec:
  K.dec.new(4096n, 65536n)

def blk(bs: List<&2, U32>) -> K.Blk:
  K.block(H.tree(), fresh(), bs)

# index 0 (6.1), and an index past both tables (2.3.3)
law refuse_idx0:
  {blk([128]) == K.BBad{K.EIdx{}} : K.Blk}

law refuse_idx_past:
  {blk([190]) == K.BBad{K.EIdx{}} : K.Blk}

law refuse_name_past:
  {blk([126, 1, 97]) == K.BBad{K.EIdx{}} : K.Blk}

# an integer past the cap (5.1)
law refuse_int:
  {blk([255, 255, 255, 255, 255, 1]) == K.BBad{K.EInt{}} : K.Blk}

# a Huffman string with EOS, and one padded with zeros (5.2)
law refuse_huff_eos:
  {blk([64, 1, 97, 132, 255, 255, 255, 255]) == K.BBad{K.EHuff{}} : K.Blk}

law refuse_huff_pad:
  {blk([64, 1, 97, 129, 24]) == K.BBad{K.EHuff{}} : K.Blk}

# a size update past SETTINGS_HEADER_TABLE_SIZE, and one after a field
# (4.2, 6.3)
law refuse_size_big:
  {blk([63, 226, 31]) == K.BBad{K.ESize{}} : K.Blk}

law refuse_size_late:
  {blk([130, 32]) == K.BBad{K.ESize{}} : K.Blk}

# a size update first is taken
law size_first:
  {blk([32, 130]) == K.BOk{K.Dc{K.ATop{}, K.Tbl{Nil{}, 0n}, Nil{}, 0n, False{},
    K.Lim{4096n, 65536n}}, [K.Fld{":method", "GET"}]} : K.Blk}

# a block cut off inside a field
law refuse_cut:
  {blk([64, 5, 97]) == K.BBad{K.ECut{}} : K.Blk}

# a string that claims more than the field list may hold is refused at
# its length, before a byte of it is kept
law refuse_str_big:
  {blk([64, 127, 255, 255, 3]) == K.BBad{K.EStr{}} : K.Blk}

# LAW: an HPACK bomb -- one small entry named again and again -- is
# refused once the decoded list passes SETTINGS_MAX_HEADER_LIST_SIZE:
# here a cap of 100, and three 42-byte :method GET fields
law refuse_bomb:
  {K.block(H.tree(), K.dec.new(4096n, 100n), [130, 130, 130]) == K.BBad{K.EList{}} : K.Blk}

# HPACK: RFC 7541 Appendix C
# ==========================

# a sequence of blocks decoded, each on the table the last left
type Run is Data:
  RAt{d: K.Dec, fss: List<&2, List<&2, K.Fld>>}
  RBad{why: K.Err}

def run.blk(b: K.Blk, fss: List<&2, List<&2, K.Fld>>) -> Run:
  match b:
    case K.BOk{d, fs}:
      RAt{d, Con{fs, fss}}
    case K.BBad{why}:
      RBad{why}

def run.one(r: Run, bs: List<&2, U32>) -> Run:
  match r:
    case RAt{d, fss}:
      run.blk(K.block(H.tree(), d, bs), fss)
    case RBad{why}:
      RBad{why}

def run(bss: List<&2, List<&2, U32>>, r: Run) -> Run:
  match bss:
    case Nil{}:
      r
    case Con{bs, t}:
      run(t, run.one(r, bs))

def ran(+tmax: Nat, es: List<&2, K.Fld>, fss: List<&2, List<&2, K.Fld>>) -> Run:
  RAt{K.Dc{K.ATop{}, K.Tbl{es, tmax}, Nil{}, 0n, False{}, K.Lim{tmax, 65536n}}, fss}

def from(+tmax: Nat) -> Run:
  RAt{K.dec.new(tmax, 65536n), Nil{}}

# the blocks encoded in turn, each on the table the last left (newest
# first in the accumulator)
def encs.push(e: K.Enc, acc: List<&2, List<&2, U32>>) -> K.Tbl & List<&2, List<&2, U32>>:
  match e:
    case K.Enc{t2, out}:
      (t2, Con{out, acc})

def encs.go(fss: List<&2, List<&2, K.Fld>>, +huff: Bool, st: K.Tbl & List<&2, List<&2, U32>>) ->
  K.Tbl & List<&2, List<&2, U32>>:
  match fss:
    case Nil{}:
      st
    case Con{fs, rest}:
      match st:
        case (t, acc):
          encs.go(rest, huff, encs.push(K.encode(t, fs, huff), acc))

def encs.fin(st: K.Tbl & List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>> & K.Tbl:
  match st:
    case (t, acc):
      (List.reverse(&2, List<&2, U32>, acc), t)

def encs(fss: List<&2, List<&2, K.Fld>>, t: K.Tbl, +huff: Bool) -> List<&2, List<&2, U32>> & K.Tbl:
  encs.fin(encs.go(fss, huff, (t, Nil{})))

def req1() -> List<&2, K.Fld>:
  [K.Fld{":method", "GET"}, K.Fld{":scheme", "http"}, K.Fld{":path", "/"},
   K.Fld{":authority", "www.example.com"}]

def req2() -> List<&2, K.Fld>:
  [K.Fld{":method", "GET"}, K.Fld{":scheme", "http"}, K.Fld{":path", "/"},
   K.Fld{":authority", "www.example.com"}, K.Fld{"cache-control", "no-cache"}]

def req3() -> List<&2, K.Fld>:
  [K.Fld{":method", "GET"}, K.Fld{":scheme", "https"}, K.Fld{":path", "/index.html"},
   K.Fld{":authority", "www.example.com"}, K.Fld{"custom-key", "custom-value"}]

def req.tbl() -> List<&2, K.Fld>:
  [K.Fld{"custom-key", "custom-value"}, K.Fld{"cache-control", "no-cache"},
   K.Fld{":authority", "www.example.com"}]

def rsp1() -> List<&2, K.Fld>:
  [K.Fld{":status", "302"}, K.Fld{"cache-control", "private"},
   K.Fld{"date", "Mon, 21 Oct 2013 20:13:21 GMT"}, K.Fld{"location", "https://www.example.com"}]

def rsp2() -> List<&2, K.Fld>:
  [K.Fld{":status", "307"}, K.Fld{"cache-control", "private"},
   K.Fld{"date", "Mon, 21 Oct 2013 20:13:21 GMT"}, K.Fld{"location", "https://www.example.com"}]

def rsp3() -> List<&2, K.Fld>:
  [K.Fld{":status", "200"}, K.Fld{"cache-control", "private"},
   K.Fld{"date", "Mon, 21 Oct 2013 20:13:22 GMT"}, K.Fld{"location", "https://www.example.com"},
   K.Fld{"content-encoding", "gzip"},
   K.Fld{"set-cookie", "foo=ASDJKHQKBZXOQWEOPIUAXQWEOIU; max-age=3600; version=1"}]

def rsp.tbl() -> List<&2, K.Fld>:
  [K.Fld{"set-cookie", "foo=ASDJKHQKBZXOQWEOPIUAXQWEOIU; max-age=3600; version=1"},
   K.Fld{"content-encoding", "gzip"}, K.Fld{"date", "Mon, 21 Oct 2013 20:13:22 GMT"}]

# C.2: a literal with indexing, without, never indexed, and an indexed field
law c2_1:
  {run([V.c21()], from(4096n)) ==
    ran(4096n, [K.Fld{"custom-key", "custom-header"}], [[K.Fld{"custom-key", "custom-header"}]]) : Run}

law c2_2:
  {run([V.c22()], from(4096n)) == ran(4096n, Nil{}, [[K.Fld{":path", "/sample/path"}]]) : Run}

law c2_3:
  {run([V.c23()], from(4096n)) == ran(4096n, Nil{}, [[K.Fld{"password", "secret"}]]) : Run}

law c2_4:
  {run([V.c24()], from(4096n)) == ran(4096n, Nil{}, [[K.Fld{":method", "GET"}]]) : Run}

# C.3 and C.4: three requests on one table, without and with Huffman
law c3_dec:
  {run([V.c31(), V.c32(), V.c33()], from(4096n)) == ran(4096n, req.tbl(), [req3(), req2(), req1()]) : Run}

law c4_dec:
  {run([V.c41(), V.c42(), V.c43()], from(4096n)) == ran(4096n, req.tbl(), [req3(), req2(), req1()]) : Run}

# C.5 and C.6: three responses on a 256-byte table, entries evicted
law c5_dec:
  {run([V.c51(), V.c52(), V.c53()], from(256n)) == ran(256n, rsp.tbl(), [rsp3(), rsp2(), rsp1()]) : Run}

law c6_dec:
  {run([V.c61(), V.c62(), V.c63()], from(256n)) == ran(256n, rsp.tbl(), [rsp3(), rsp2(), rsp1()]) : Run}

# and the encoder writes exactly the RFC's bytes for the same fields
law c3_enc:
  {encs([req1(), req2(), req3()], K.tbl.new(4096n), False{}) ==
    ([V.c31(), V.c32(), V.c33()], K.Tbl{req.tbl(), 4096n}) : List<&2, List<&2, U32>> & K.Tbl}

law c4_enc:
  {encs([req1(), req2(), req3()], K.tbl.new(4096n), True{}) ==
    ([V.c41(), V.c42(), V.c43()], K.Tbl{req.tbl(), 4096n}) : List<&2, List<&2, U32>> & K.Tbl}

law c5_enc:
  {encs([rsp1(), rsp2(), rsp3()], K.tbl.new(256n), False{}) ==
    ([V.c51(), V.c52(), V.c53()], K.Tbl{rsp.tbl(), 256n}) : List<&2, List<&2, U32>> & K.Tbl}

law c6_enc:
  {encs([rsp1(), rsp2(), rsp3()], K.tbl.new(256n), True{}) ==
    ([V.c61(), V.c62(), V.c63()], K.Tbl{rsp.tbl(), 256n}) : List<&2, List<&2, U32>> & K.Tbl}

# Frames (RFC 9113 3.4, 4.1, 4.2)
# ===============================

# The reader seen from outside: the frames it has completed, newest
# first, and whether it is reading or has refused (and why).
type Look is Data:
  Reading{}
  Refusing{why: Fm.Why}

def look.at(at: Fm.Fs) -> Look:
  match at:
    case Fm.FBad{why}:
      Refusing{why}
    case _:
      Reading{}

def look(r: Fm.Rd) -> List<&2, Fm.Frm> & Look:
  match r:
    case Fm.Rd{at, max, out}:
      (out, look.at(at))

# a reader at a frame's first byte, with these frames behind it
def start(+max: Nat, out: List<&2, Fm.Frm>) -> Fm.Rd:
  Fm.Rd{Fm.hd.start(), max, out}

# A reader agrees with the reference when it has completed exactly the
# reference's frames and then: inside the preface, it is still reading;
# where the reference is open, it is reading, and is exactly a reader
# at a frame's first byte fed the bytes since the last whole frame;
# where the reference refuses, it has refused, for the same reason.
def agree.end(-r: Fm.Rd, +max: Nat, +fs: List<&2, Fm.Frm>, e: Sp.End) -> Type:
  match e:
    case Sp.Pre{rest}:
      {look(r) == (fs, Reading{}) : List<&2, Fm.Frm> & Look}
    case Sp.Open{rest}:
      {look(r) == (fs, Reading{}) : List<&2, Fm.Frm> & Look} &
        {r == Fm.feed(rest, start(max, fs)) : Fm.Rd}
    case Sp.Refused{why}:
      {look(r) == (fs, Refusing{why}) : List<&2, Fm.Frm> & Look}

def agree(-r: Fm.Rd, +max: Nat, f: Sp.Frames) -> Type:
  match f:
    case Sp.Frames{fs, e}:
      agree.end(r, max, fs, e)

# LAW: the reader is the framing. For every maximum frame size and every
# input, a fresh reader fed the input agrees with RFC 9113's framing of
# it (spec.bend): the same frames at the same boundaries, the preface
# checked byte by byte, a frame past the maximum refused at its header.
law frame_sim:
  for +max: Nat
  for +bs: List<&2, U32>
  agree(Fm.feed(bs, Fm.new(max)), max, Sp.frames(max, bs))

# LAW: the same for the walk the server runs over one read ...
law frame_sim_buf:
  for +max: Nat
  for +b: Bytes()
  agree(Fm.feed_buf(b, Fm.new(max)), max, Sp.frames(max, Bytes.to_list(b)))

# ... and over a connection's reads however TCP cut them
def reads(rs: List<&2, Bytes()>, r: Fm.Rd) -> Fm.Rd:
  Wr.reads(~Unit, ~Fm.Rd, ~Fm.wstep, ~Fm.wadv, Unit{}, rs, r)

law frame_sim_reads:
  for +max: Nat
  for +rs: List<&2, Bytes()>
  agree(reads(rs, Fm.new(max)), max, Sp.frames(max, Bytes.to_list(Bytes.concat(rs))))

# LAW: chunking never changes a read (the kit's, at the frame reader)
law frame_split:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +r: Fm.Rd
  {Fm.feed(List.append(&2, U32, a, b), r) == Fm.feed(b, Fm.feed(a, r)) : Fm.Rd}

# The reference on vectors: the preface then an empty SETTINGS; a
# preface with one byte wrong; a frame one byte past a 16-byte maximum;
# and a PING cut after its header.
def pfx() -> List<&2, U32>:
  Wr.bytes("PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n")

law frame_settings:
  {Sp.frames(16384n, List.append(&2, U32, pfx(), [0, 0, 0, 4, 0, 0, 0, 0, 0])) ==
    Sp.Frames{[Fm.Frm{4, 0, 0, ""}], Sp.Open{Nil{}}} : Sp.Frames}

law frame_bad_preface:
  {Sp.frames(16384n, Wr.bytes("PRI * HTTP/1.1\r\n\r\nSM\r\n\r\n")) ==
    Sp.Frames{Nil{}, Sp.Refused{Fm.WPre{}}} : Sp.Frames}

law frame_too_big:
  {Sp.frames(16n, List.append(&2, U32, pfx(), [0, 0, 17, 0, 0, 0, 0, 0, 1])) ==
    Sp.Frames{Nil{}, Sp.Refused{Fm.WSize{}}} : Sp.Frames}

law frame_cut:
  {Sp.frames(16384n, List.append(&2, U32, pfx(), [0, 0, 8, 6, 0, 0, 0, 0, 0, 1, 2])) ==
    Sp.Frames{Nil{}, Sp.Open{[0, 0, 8, 6, 0, 0, 0, 0, 0, 1, 2]}} : Sp.Frames}

# the stream identifier's reserved bit is dropped, and the length is
# the three octets big-endian
law frame_fields:
  {Sp.frames(16384n, List.append(&2, U32, pfx(), [0, 0, 0, 6, 1, 128, 0, 1, 3])) ==
    Sp.Frames{[Fm.Frm{6, 1, 259, ""}], Sp.Open{Nil{}}} : Sp.Frames}
