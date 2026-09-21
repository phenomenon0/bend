# The store: content-defined chunks, a content address per chunk, a Merkle
# tree over those addresses, and a checker that reads an inclusion proof and
# says yes or no. Nothing here does IO -- main.bend is the socket, this file
# is the store -- so every claim below is testable without a port.
#
# The shape of the thing. A PUT cuts its body with FastCDC (power/cdc.bend),
# addresses each piece with BLAKE3 (power/blake3.bend), and keeps a piece only
# if its address is new. The blob's manifest is the list of piece ids, and the
# blob's own address is the root of a Merkle tree whose leaves are the piece
# addresses and whose joins are BLAKE3's own `parent`. A GET re-reads the
# pieces it is about to serve, re-hashes them, and folds the proof: the bytes
# on the wire are the bytes that hash to the root, or the response is a 500.
#
# The leaf and the join are domain-separated by BLAKE3's own flags -- a leaf
# carries ROOT from `hash`, a join carries PARENT from `parent` -- so the tree
# needs no extra tagging to stop a leaf from being read as a join.
import Base
import ../../power/vec.bend as Vec
import ../../power/bytes.bend as Bytes
import ../../power/blake3.bend as B3
import ../../power/cdc.bend as Cdc

# -- the records -------------------------------------------------------------

# a stored chunk: its address and its bytes. Every field is Data, so the whole
# store is a value the accept loop can thread through itself.
type Chk is Data:
  Chk{cv: B3.Cv, data: String}

# a blob: the Merkle root over its chunk addresses, how many chunks, how many
# bytes, and the ids of those chunks in the store's chunk table
type Blob is Data:
  Blob{root: B3.Cv, n: U32, size: U32, ids: List<&2, U32>}

# the store. chks is the dedup table, in order of first sight, so a chunk's id
# is its position. seen counts every chunk ever cut, kept counts the unique
# ones, and dupb is the bytes the dedup did not store.
type Store is Data:
  Store{chks: List<&2, Chk>, kept: U32, seen: U32, dupb: U32,
        blobs: List<&2, Blob>}

def new() -> Store:
  Store{[], 0, 0, 0, []}

# -- bytes -------------------------------------------------------------------

# The socket edge is UTF-8 (io_str/io_cstr in comp.ts), so a byte above 0x7f
# does not survive a round trip through String. The daemon refuses a body that
# is not ASCII (Base's String.is_ascii) rather than storing a mangled one; the
# report says what that costs.
def to_bytes(s: String, b: Bytes.Bytes) -> Bytes.Bytes:
  match s:
    case SNil{}:
      b
    case SCon{h, t}:
      to_bytes(t, Bytes.push(b, Char.to_u32(h)))

def bytes_of(s: String) -> Bytes.Bytes:
  to_bytes(s, Bytes.new())

def hash.out(r: Bytes.Bytes & B3.Cv) -> B3.Cv:
  (b, c) = r
  c

# the BLAKE3 root of a string's bytes -- the content address of a chunk
def hash_str(s: String) -> B3.Cv:
  hash.out(B3.hash_all(bytes_of(s)))

def cveq.r(a0: U32, a1: U32, a2: U32, a3: U32, a4: U32, a5: U32, a6: U32, a7: U32,
           b: B3.Cv) -> Bool:
  match b:
    case B3.Cv{b0, b1, b2, b3, b4, b5, b6, b7}:
      Bool.and(Bool.and(Bool.and(U32.is_eq(a0, b0), U32.is_eq(a1, b1)),
                        Bool.and(U32.is_eq(a2, b2), U32.is_eq(a3, b3))),
               Bool.and(Bool.and(U32.is_eq(a4, b4), U32.is_eq(a5, b5)),
                        Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7))))

def cveq(a: B3.Cv, b: B3.Cv) -> Bool:
  match a:
    case B3.Cv{a0, a1, a2, a3, a4, a5, a6, a7}:
      cveq.r(a0, a1, a2, a3, a4, a5, a6, a7, b)

# -- the Merkle tree over chunk addresses ------------------------------------

# one level up: adjacent pairs join, a lone last node is promoted unchanged.
# Promotion rather than duplication -- duplicating the last leaf is the classic
# way a Merkle tree stops being injective.
def up(xs: List<&2, B3.Cv>) -> List<&2, B3.Cv>:
  match xs:
    case Nil{}:
      []
    case Con{a, t}:
      match t:
        case Nil{}:
          [a]
        case Con{b, t2}:
          Con{B3.parent(a, b, 0), up(t2)}

# the root of the tree over xs. One leaf is its own root: a leaf address comes
# out of `hash`, which set ROOT on it, and a join comes out of `parent`, which
# set PARENT, so the two can never be confused for one another.
def root.go(fuel: Nat, xs: List<&2, B3.Cv>, z: B3.Cv) -> B3.Cv:
  match fuel:
    case 0n:
      z
    case 1n++f:
      match xs:
        case Nil{}:
          z
        case Con{h, t}:
          match t:
            case Nil{}:
              h
            case Con{h2, t2}:
              root.go(f, up(Con{h, Con{h2, t2}}), z)

def root(xs: List<&2, B3.Cv>, n: U32) -> B3.Cv:
  root.go(U32.to_nat(U32.add(n, 1)), xs, B3.iv())

# -- the witness -------------------------------------------------------------

# the sibling hashes on the path from leaf i to the root, bottom level first.
# A level where the node is promoted contributes nothing, which is why the
# checker has to derive the schedule from (i, n) and cannot read it off the
# witness's length.
type Pv is Data:
  PGo{i: U32, size: U32, xs: List<&2, B3.Cv>, acc: List<&2, B3.Cv>}
  PEnd{acc: List<&2, B3.Cv>}

def pv.sib(+i: U32, +size: U32, xs: List<&2, B3.Cv>, acc: List<&2, B3.Cv>,
           m: Maybe<&2, B3.Cv>) -> Pv:
  match m:
    case None{}:
      PGo{U32.shrn(i, 1n), U32.shrn(U32.inc(size), 1n), up(xs), acc}
    case Some{s}:
      PGo{U32.shrn(i, 1n), U32.shrn(U32.inc(size), 1n), up(xs), Con{s, acc}}

def pv.lvl(+i: U32, +size: U32, +xs: List<&2, B3.Cv>, acc: List<&2, B3.Cv>,
           here: Bool) -> Pv:
  match here:
    case True{}:
      pv.sib(i, size, xs, acc, List.get(&2, B3.Cv, xs, U32.to_nat(U32.xor(i, 1))))
    case False{}:
      pv.sib(i, size, xs, acc, None{})

def pv.on(+i: U32, +size: U32, xs: List<&2, B3.Cv>, acc: List<&2, B3.Cv>,
          more: Bool) -> Pv:
  match more:
    case True{}:
      pv.lvl(i, size, xs, acc, U32.is_lt(U32.xor(i, 1), size))
    case False{}:
      PEnd{acc}

def pv.step(s: Pv) -> Pv:
  match s:
    case PEnd{acc}:
      PEnd{acc}
    case PGo{+i, +size, xs, acc}:
      pv.on(i, size, xs, acc, U32.is_lt(1, size))

def pv.go(fuel: Nat, s: Pv) -> Pv:
  match fuel:
    case 0n:
      s
    case 1n++f:
      match s:
        case PEnd{acc}:
          PEnd{acc}
        case PGo{i, size, xs, acc}:
          pv.go(f, pv.step(PGo{i, size, xs, acc}))

def pv.out(s: Pv) -> List<&2, B3.Cv>:
  match s:
    case PEnd{acc}:
      List.reverse(&2, B3.Cv, acc)
    case PGo{i, size, xs, acc}:
      List.reverse(&2, B3.Cv, acc)

# prove: the witness for leaf i of the tree whose leaves are xs
def prove(xs: List<&2, B3.Cv>, +i: U32, +n: U32) -> List<&2, B3.Cv>:
  pv.out(pv.go(33n, PGo{i, n, xs, []}))

# -- the checker -------------------------------------------------------------

# The checker never sees the tree. It is given the root, the leaf count, the
# index, the address the served bytes actually hash to, and the siblings, and
# it rebuilds the path. Every rejection is a refusal to send.
type Ck is Data:
  CGo{i: U32, size: U32, cv: B3.Cv, sibs: List<&2, B3.Cv>}
  CEnd{cv: B3.Cv, sibs: List<&2, B3.Cv>}
  CBad{}

def ck.join(+i: U32, +size: U32, cv: B3.Cv, s: B3.Cv, t: List<&2, B3.Cv>,
            left: Bool) -> Ck:
  match left:
    case True{}:
      CGo{U32.shrn(i, 1n), U32.shrn(U32.inc(size), 1n), B3.parent(cv, s, 0), t}
    case False{}:
      CGo{U32.shrn(i, 1n), U32.shrn(U32.inc(size), 1n), B3.parent(s, cv, 0), t}

# a level that needs a sibling and has none is a refusal, not a promotion:
# otherwise a witness could shorten itself into a different tree
def ck.eat(+i: U32, +size: U32, cv: B3.Cv, sibs: List<&2, B3.Cv>) -> Ck:
  match sibs:
    case Nil{}:
      CBad{}
    case Con{s, t}:
      ck.join(i, size, cv, s, t, U32.is_zero(U32.and(i, 1)))

def ck.lvl(+i: U32, +size: U32, cv: B3.Cv, sibs: List<&2, B3.Cv>,
           paired: Bool) -> Ck:
  match paired:
    case True{}:
      ck.eat(i, size, cv, sibs)
    case False{}:
      CGo{U32.shrn(i, 1n), U32.shrn(U32.inc(size), 1n), cv, sibs}

def ck.on(+i: U32, +size: U32, cv: B3.Cv, sibs: List<&2, B3.Cv>,
          more: Bool) -> Ck:
  match more:
    case True{}:
      ck.lvl(i, size, cv, sibs, U32.is_lt(U32.xor(i, 1), size))
    case False{}:
      CEnd{cv, sibs}

def ck.step(s: Ck) -> Ck:
  match s:
    case CBad{}:
      CBad{}
    case CEnd{cv, sibs}:
      CEnd{cv, sibs}
    case CGo{+i, +size, cv, sibs}:
      ck.on(i, size, cv, sibs, U32.is_lt(1, size))

def ck.go(fuel: Nat, s: Ck) -> Ck:
  match fuel:
    case 0n:
      s
    case 1n++f:
      match s:
        case CBad{}:
          CBad{}
        case CEnd{cv, sibs}:
          CEnd{cv, sibs}
        case CGo{i, size, cv, sibs}:
          ck.go(f, ck.step(CGo{i, size, cv, sibs}))

# a leftover sibling is a refusal too: the witness proved a path this tree
# does not have
def ck.out(s: Ck, r: B3.Cv) -> Bool:
  match s:
    case CBad{}:
      False{}
    case CGo{i, size, cv, sibs}:
      False{}
    case CEnd{cv, sibs}:
      match sibs:
        case Nil{}:
          cveq(cv, r)
        case Con{h, t}:
          False{}

# the budget, taken before a single join runs: a witness names its own length,
# and a checker that believes it can be made to fold for as long as the
# witness likes. A tree over 2^32 leaves has at most 32 siblings on a path.
def check.run(r: B3.Cv, +n: U32, +i: U32, leaf: B3.Cv,
              sibs: List<&2, B3.Cv>) -> Bool:
  ck.out(ck.go(33n, CGo{i, n, leaf, sibs}), r)

def check.if(r: B3.Cv, +n: U32, +i: U32, leaf: B3.Cv, sibs: List<&2, B3.Cv>,
             ok: Bool) -> Bool:
  match ok:
    case True{}:
      check.run(r, n, i, leaf, sibs)
    case False{}:
      False{}

# check: does `leaf` sit at index i of the tree of n leaves rooted at r?
def check(r: B3.Cv, +n: U32, +i: U32, leaf: B3.Cv, +sibs: List<&2, B3.Cv>) -> Bool:
  check.if(r, n, i, leaf, sibs,
    Bool.and(U32.is_lt(i, n),
      Nat.is_lt(List.length(&2, B3.Cv, sibs), 33n)))

# -- the chunk table ---------------------------------------------------------

def store.chks(s: Store) -> List<&2, Chk>:
  match s:
    case Store{chks, kept, seen, dupb, blobs}:
      chks

def store.blobs(s: Store) -> List<&2, Blob>:
  match s:
    case Store{chks, kept, seen, dupb, blobs}:
      blobs

def store.kept(s: Store) -> U32:
  match s:
    case Store{chks, kept, seen, dupb, blobs}:
      kept

def store.seen(s: Store) -> U32:
  match s:
    case Store{chks, kept, seen, dupb, blobs}:
      seen

def store.dupb(s: Store) -> U32:
  match s:
    case Store{chks, kept, seen, dupb, blobs}:
      dupb

def chk.cv(c: Chk) -> B3.Cv:
  match c:
    case Chk{cv, data}:
      cv

def chk.data(c: Chk) -> String:
  match c:
    case Chk{cv, data}:
      data

def at.cv(m: Maybe<&2, Chk>) -> B3.Cv:
  match m:
    case None{}:
      B3.iv()
    case Some{c}:
      chk.cv(c)

def at.data(m: Maybe<&2, Chk>) -> String:
  match m:
    case None{}:
      ""
    case Some{c}:
      chk.data(c)

def chk_at(cs: List<&2, Chk>, +id: U32) -> Maybe<&2, Chk>:
  List.get(&2, Chk, cs, U32.to_nat(id))

# ponytail: the dedup table is a list walked front to back, so a lookup is
# O(unique chunks). A hash-keyed map is the upgrade when a store outgrows a
# demo; nothing else in this file changes when it lands.
type Fd is Data:
  FGo{cv: B3.Cv, i: U32, cs: List<&2, Chk>}
  FHit{i: U32}
  FNo{}

def fd.on(+cv: B3.Cv, +i: U32, t: List<&2, Chk>, same: Bool) -> Fd:
  match same:
    case True{}:
      FHit{i}
    case False{}:
      FGo{cv, U32.inc(i), t}

def fd.step(s: Fd) -> Fd:
  match s:
    case FHit{i}:
      FHit{i}
    case FNo{}:
      FNo{}
    case FGo{+cv, +i, cs}:
      match cs:
        case Nil{}:
          FNo{}
        case Con{h, t}:
          fd.on(cv, i, t, cveq(chk.cv(h), cv))

def fd.go(fuel: Nat, s: Fd) -> Fd:
  match fuel:
    case 0n:
      s
    case 1n++f:
      match s:
        case FHit{i}:
          FHit{i}
        case FNo{}:
          FNo{}
        case FGo{cv, i, cs}:
          fd.go(f, fd.step(FGo{cv, i, cs}))

def fd.out(s: Fd) -> Maybe<&2, U32>:
  match s:
    case FHit{i}:
      Some{i}
    case FNo{}:
      None{}
    case FGo{cv, i, cs}:
      None{}

# find: the id of the chunk whose address is cv, if the store has it
def find(+cs: List<&2, Chk>, cv: B3.Cv) -> Maybe<&2, U32>:
  fd.out(fd.go((1n + List.length(&2, Chk, cs) : Nat), FGo{cv, 0, cs}))

# -- PUT ---------------------------------------------------------------------

# the walk over one body's cut points. Each chunk is addressed, looked up, and
# either stored or dropped; either way its id joins the manifest and its
# address joins the leaf list the Merkle root is built from.
type Pt is Data:
  PtGo{prev: U32, cuts: List<&2, U32>, body: String,
       ids: List<&2, U32>, lv: List<&2, B3.Cv>, nch: U32, st: Store}
  PtEnd{ids: List<&2, U32>, lv: List<&2, B3.Cv>, nch: U32, st: Store}

def pt.keep.on(chks: List<&2, Chk>, +kept: U32, +seen: U32, +dupb: U32,
               blobs: List<&2, Blob>, cv: B3.Cv, data: String, +len: U32,
               m: Maybe<&2, U32>) -> Store & U32:
  match m:
    case Some{id}:
      (Store{chks, kept, U32.inc(seen), U32.add(dupb, len), blobs}, id)
    case None{}:
      (Store{List.append(&2, Chk, chks, [Chk{cv, data}]), U32.inc(kept),
             U32.inc(seen), dupb, blobs}, kept)

def pt.keep(cv: B3.Cv, data: String, len: U32, m: Maybe<&2, U32>, s: Store)
    -> Store & U32:
  match s:
    case Store{chks, kept, seen, dupb, blobs}:
      pt.keep.on(chks, kept, seen, dupb, blobs, cv, data, len, m)

def pt.set(+end: U32, cuts: List<&2, U32>, body: String, ids: List<&2, U32>,
           lv: List<&2, B3.Cv>, +nch: U32, cv: B3.Cv, r: Store & U32) -> Pt:
  (st, id) = r
  PtGo{end, cuts, body, Con{id, ids}, Con{cv, lv}, U32.inc(nch), st}

def pt.one(+prev: U32, +end: U32, cuts: List<&2, U32>, body: String,
           ids: List<&2, U32>, lv: List<&2, B3.Cv>, +nch: U32,
           +data: String, +st: Store) -> Pt:
  +cv = hash_str(data)
  pt.set(end, cuts, body, ids, lv, nch, cv,
    pt.keep(cv, data, U32.sub(end, prev), find(store.chks(st), cv), st))

def pt.step(s: Pt) -> Pt:
  match s:
    case PtEnd{ids, lv, nch, st}:
      PtEnd{ids, lv, nch, st}
    case PtGo{+prev, cuts, +body, ids, lv, nch, st}:
      match cuts:
        case Nil{}:
          PtEnd{ids, lv, nch, st}
        case Con{+end, t}:
          pt.one(prev, end, t, body, ids, lv, nch,
            String.take(String.drop(body, U32.to_nat(prev)),
              U32.to_nat(U32.sub(end, prev))), st)

def pt.go(fuel: Nat, s: Pt) -> Pt:
  match fuel:
    case 0n:
      s
    case 1n++f:
      match s:
        case PtEnd{ids, lv, nch, st}:
          PtEnd{ids, lv, nch, st}
        case PtGo{prev, cuts, body, ids, lv, nch, st}:
          pt.go(f, pt.step(PtGo{prev, cuts, body, ids, lv, nch, st}))

def put.cuts(r: Cdc.Cdc & List<&2, U32>) -> List<&2, U32>:
  (c, xs) = r
  xs

def put.file(+b: Blob, chks: List<&2, Chk>, kept: U32, seen: U32, dupb: U32,
             blobs: List<&2, Blob>) -> Store & Blob:
  (Store{chks, kept, seen, dupb, List.append(&2, Blob, blobs, [b])}, b)

def put.add(+size: U32, +nch: U32, ids: List<&2, U32>, lv: List<&2, B3.Cv>,
            s: Store) -> Store & Blob:
  match s:
    case Store{chks, kept, seen, dupb, blobs}:
      put.file(Blob{root(List.reverse(&2, B3.Cv, lv), nch), nch, size,
        List.reverse(&2, U32, ids)}, chks, kept, seen, dupb, blobs)

# the walk is over when the cut points run out, so PtGo here means the fuel
# was short -- impossible, the fuel is the cut count -- and files what it has
def put.fin(+size: U32, s: Pt) -> Store & Blob:
  match s:
    case PtGo{prev, cuts, body, ids, lv, nch, st}:
      put.add(size, nch, ids, lv, st)
    case PtEnd{ids, lv, nch, st}:
      put.add(size, nch, ids, lv, st)

def put.run(st: Store, +body: String, +size: U32, +cuts: List<&2, U32>)
    -> Store & Blob:
  put.fin(size, pt.go((1n + List.length(&2, U32, cuts) : Nat),
    PtGo{0, cuts, body, [], [], 0, st}))

# put: cut the body, address every piece, store the pieces the table has not
# seen, and file the manifest under the Merkle root of the piece addresses.
# bits is log2 of the target chunk size, as power/cdc.bend takes it.
def put(st: Store, +body: String, +bits: U32) -> Store & Blob:
  +size = U32.from_nat(String.length(body))
  put.run(st, body, size,
    put.cuts(Cdc.split(Cdc.new(bytes_of(body)), 0, size, bits)))

# -- GET ---------------------------------------------------------------------

def blob.root(b: Blob) -> B3.Cv:
  match b:
    case Blob{r, k, z, xs}:
      r

def blob.n(b: Blob) -> U32:
  match b:
    case Blob{r, k, z, xs}:
      k

def blob.size(b: Blob) -> U32:
  match b:
    case Blob{r, k, z, xs}:
      z

def blob.ids(b: Blob) -> List<&2, U32>:
  match b:
    case Blob{r, k, z, xs}:
      xs

# the blob whose address is the 64 hex digits `a`. Comparing the text rather
# than parsing it back into eight words keeps the address one thing, not two.
type Fb is Data:
  FbGo{a: String, bs: List<&2, Blob>}
  FbHit{b: Blob}
  FbNo{}

def fb.on(+a: String, h: Blob, t: List<&2, Blob>, same: Bool) -> Fb:
  match same:
    case True{}:
      FbHit{h}
    case False{}:
      FbGo{a, t}

def fb.step(s: Fb) -> Fb:
  match s:
    case FbHit{b}:
      FbHit{b}
    case FbNo{}:
      FbNo{}
    case FbGo{+a, bs}:
      match bs:
        case Nil{}:
          FbNo{}
        case Con{+h, t}:
          fb.on(a, h, t, String.eq(B3.hex(blob.root(h)), a))

def fb.go(fuel: Nat, s: Fb) -> Fb:
  match fuel:
    case 0n:
      s
    case 1n++f:
      match s:
        case FbHit{b}:
          FbHit{b}
        case FbNo{}:
          FbNo{}
        case FbGo{a, bs}:
          fb.go(f, fb.step(FbGo{a, bs}))

def fb.out(s: Fb) -> Maybe<&2, Blob>:
  match s:
    case FbHit{b}:
      Some{b}
    case FbNo{}:
      None{}
    case FbGo{a, bs}:
      None{}

def blob_of(st: Store, a: String) -> Maybe<&2, Blob>:
  +bs = store.blobs(st)
  fb.out(fb.go((1n + List.length(&2, Blob, bs) : Nat), FbGo{a, bs}))

# the leaf addresses of a blob, in manifest order: this is the prover's view
# of the tree, read out of the chunk table
def leaves(+cs: List<&2, Chk>, ids: List<&2, U32>) -> List<&2, B3.Cv>:
  match ids:
    case Nil{}:
      []
    case Con{h, t}:
      Con{at.cv(chk_at(cs, h)), leaves(cs, t)}

# where each chunk of a blob sits in the blob's own byte space
type Part is Data:
  Part{i: U32, id: U32, off: U32, len: U32}

def parts(+cs: List<&2, Chk>, ids: List<&2, U32>, +i: U32, +off: U32)
    -> List<&2, Part>:
  match ids:
    case Nil{}:
      []
    case Con{+h, t}:
      +len = U32.from_nat(String.length(at.data(chk_at(cs, h))))
      Con{Part{i, h, off, len}, parts(cs, t, U32.inc(i), U32.add(off, len))}

def hexes(xs: List<&2, B3.Cv>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, t}:
      " " ++ (B3.hex(h) ++ hexes(t))

# -- serving a range, proof first --------------------------------------------

# the answer of a GET: the text to send, or the reason there is nothing to
# send. A body only ever leaves this file inside Ok, and the only way to reach
# Ok is through a walk that checked every part it emitted.
type Rsp is Data:
  Ok{text: String}
  No{why: String}

# the walk over the parts a range touches. lo/hi are the byte range, lv is the
# leaf list the witness is cut from, and cnt is both the part count and the
# budget: a range wide enough to touch more than MAXP chunks is refused rather
# than served, because each part costs a re-hash and a fold.
type Gs is Data:
  GsGo{ps: List<&2, Part>, lo: U32, hi: U32, n: U32, rt: B3.Cv,
       lv: List<&2, B3.Cv>, cs: List<&2, Chk>, out: String, cnt: U32}
  GsNo{why: String}
  GsEnd{out: String, cnt: U32}

def MAXP() -> U32:
  64

def gs.line(+i: U32, +o: U32, +len: U32, leaf: B3.Cv, +sibs: List<&2, B3.Cv>,
            data: String) -> String:
  String.concat(["part ", U32.show(i), " ", B3.hex(leaf), " off ", U32.show(o),
    " len ", U32.show(len), " sibs ",
    U32.show(U32.from_nat(List.length(&2, B3.Cv, sibs))), hexes(sibs),
    " verified\n", data, "\n"])

# the refusal is the point: the bytes are hashed here, and if that hash does
# not fold up the witness to the blob's root the walk dies with nothing
# written. No caller can skip this and reach Ok.
def gs.send(ps: List<&2, Part>, +lo: U32, +hi: U32, +n: U32, +rt: B3.Cv,
            +lv: List<&2, B3.Cv>, +cs: List<&2, Chk>, out: String, +cnt: U32,
            +i: U32, +o: U32, +len: U32, data: String, leaf: B3.Cv,
            sibs: List<&2, B3.Cv>, ok: Bool) -> Gs:
  match ok:
    case True{}:
      GsGo{ps, lo, hi, n, rt, lv, cs,
        out ++ gs.line(i, o, len, leaf, sibs, data), U32.inc(cnt)}
    case False{}:
      GsNo{"proof refused at part " ++ U32.show(i)}

def gs.part(ps: List<&2, Part>, +lo: U32, +hi: U32, +n: U32, +rt: B3.Cv,
            +lv: List<&2, B3.Cv>, +cs: List<&2, Chk>, out: String, +cnt: U32,
            +i: U32, +id: U32, +o: U32, +len: U32) -> Gs:
  +data = at.data(chk_at(cs, id))
  +leaf = hash_str(data)
  +sibs = prove(lv, i, n)
  gs.send(ps, lo, hi, n, rt, lv, cs, out, cnt, i, o, len, data, leaf, sibs,
    check(rt, n, i, leaf, sibs))

def gs.cap(ps: List<&2, Part>, +lo: U32, +hi: U32, +n: U32, +rt: B3.Cv,
           +lv: List<&2, B3.Cv>, +cs: List<&2, Chk>, out: String, +cnt: U32,
           +i: U32, +id: U32, +o: U32, +len: U32, room: Bool) -> Gs:
  match room:
    case True{}:
      gs.part(ps, lo, hi, n, rt, lv, cs, out, cnt, i, id, o, len)
    case False{}:
      GsNo{"range spans more than " ++ (U32.show(MAXP()) ++ " chunks")}

def gs.take(ps: List<&2, Part>, +lo: U32, +hi: U32, +n: U32, +rt: B3.Cv,
            +lv: List<&2, B3.Cv>, +cs: List<&2, Chk>, out: String, +cnt: U32,
            +i: U32, +id: U32, +o: U32, +len: U32, over: Bool) -> Gs:
  match over:
    case True{}:
      GsEnd{out, cnt}
    case False{}:
      gs.cap(ps, lo, hi, n, rt, lv, cs, out, cnt, i, id, o, len,
        U32.is_lt(cnt, MAXP()))

def gs.skip(ps: List<&2, Part>, +lo: U32, +hi: U32, +n: U32, +rt: B3.Cv,
            +lv: List<&2, B3.Cv>, +cs: List<&2, Chk>, out: String, +cnt: U32,
            +i: U32, +id: U32, +o: U32, +len: U32, before: Bool) -> Gs:
  match before:
    case True{}:
      GsGo{ps, lo, hi, n, rt, lv, cs, out, cnt}
    case False{}:
      gs.take(ps, lo, hi, n, rt, lv, cs, out, cnt, i, id, o, len,
        U32.is_le(hi, o))

def gs.on(p: Part, ps: List<&2, Part>, +lo: U32, +hi: U32, +n: U32, +rt: B3.Cv,
          +lv: List<&2, B3.Cv>, +cs: List<&2, Chk>, out: String, +cnt: U32)
    -> Gs:
  match p:
    case Part{+i, +id, +o, +len}:
      gs.skip(ps, lo, hi, n, rt, lv, cs, out, cnt, i, id, o, len,
        U32.is_le(U32.add(o, len), lo))

def gs.step(s: Gs) -> Gs:
  match s:
    case GsNo{why}:
      GsNo{why}
    case GsEnd{out, cnt}:
      GsEnd{out, cnt}
    case GsGo{ps, lo, hi, n, rt, lv, cs, out, cnt}:
      match ps:
        case Nil{}:
          GsEnd{out, cnt}
        case Con{p, t}:
          gs.on(p, t, lo, hi, n, rt, lv, cs, out, cnt)

def gs.go(fuel: Nat, s: Gs) -> Gs:
  match fuel:
    case 0n:
      s
    case 1n++f:
      match s:
        case GsNo{why}:
          GsNo{why}
        case GsEnd{out, cnt}:
          GsEnd{out, cnt}
        case GsGo{ps, lo, hi, n, rt, lv, cs, out, cnt}:
          gs.go(f, gs.step(GsGo{ps, lo, hi, n, rt, lv, cs, out, cnt}))

def gs.out(+a: String, +n: U32, +size: U32, +lo: U32, +hi: U32, s: Gs) -> Rsp:
  match s:
    case GsNo{why}:
      No{why}
    case GsGo{ps, lo2, hi2, n2, rt, lv, cs, out, cnt}:
      No{"out of fuel"}
    case GsEnd{out, +cnt}:
      Ok{String.concat(["blob ", a, "\nchunks ", U32.show(n), " size ",
        U32.show(size), "\nrange ", U32.show(lo), " ", U32.show(U32.sub(hi, lo)),
        " parts ", U32.show(cnt), "\n", out, "end\n"])}

def gs.run(+a: String, +n: U32, +size: U32, +lo: U32, +hi: U32, rt: B3.Cv,
           +cs: List<&2, Chk>, +ids: List<&2, U32>) -> Rsp:
  gs.out(a, n, size, lo, hi,
    gs.go((2n + List.length(&2, U32, ids) : Nat),
      GsGo{parts(cs, ids, 0, 0), lo, hi, n, rt, leaves(cs, ids), cs, "", 0}))

def get.has(st: Store, +b: Blob, +off: U32, +len: U32, inside: Bool) -> Rsp:
  match inside:
    case True{}:
      gs.run(B3.hex(blob.root(b)), blob.n(b), blob.size(b), off,
        U32.min(U32.add(off, len), blob.size(b)), blob.root(b),
        store.chks(st), blob.ids(b))
    case False{}:
      No{"range past the end of the blob"}

def get.of(st: Store, +off: U32, +len: U32, m: Maybe<&2, Blob>) -> Rsp:
  match m:
    case None{}:
      No{"no blob with that address"}
    case Some{+b}:
      get.has(st, b, off, len, U32.is_lt(off, blob.size(b)))

# get: the bytes of a byte range, one block per chunk the range touches, each
# block carrying the witness that puts its chunk at its index of the tree the
# blob's address is the root of -- and each witness already folded, here,
# against the address the bytes themselves hash to.
def get(+st: Store, a: String, +off: U32, +len: U32) -> Rsp:
  get.of(st, off, len, blob_of(st, a))
