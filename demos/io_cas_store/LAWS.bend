# The laws of the CAS store. They pin the two pure shapes the daemon's
# honesty rests on: what a level of the Merkle tree does with the node it
# cannot pair, and where a response stops being head and starts being body.
# PROOF.bend must prove them.
import Base
import ../../power/blake3.bend as B3
import ./cas.bend as Cas
import ./serve.bend as Srv

# LAW: a level with one node left PROMOTES it. The classic way to get a
# Merkle tree wrong is to duplicate the odd node instead, which gives two
# different leaf lists one root -- and an address that is not an address.
law promote_alone:
  for +a: B3.Cv
  {Cas.up([a]) == [a] : List<&2, B3.Cv>}

# LAW: a level with two nodes joins them, with the PARENT flag clear of ROOT.
# blake3 already separates a leaf from a join by that flag, so a witness
# cannot present a chunk address where a join belongs.
law pair_joins:
  for +a: B3.Cv
  for +b: B3.Cv
  {Cas.up([a, b]) == [B3.parent(a, b, 0)] : List<&2, B3.Cv>}

# LAW: one leaf is its own root. A single-chunk blob is addressed by that
# chunk, with nothing interposed, which is what makes the empty witness the
# right witness for it.
law root_of_one:
  for +a: B3.Cv
  {Cas.root([a], 1) == a : B3.Cv}

# LAW: every response is some head, then a blank line, then the body -- a
# client that cuts at the blank line reads exactly the bytes it was sent,
# whatever the status was.
law body_after_blank:
  for +code: U32
  for +reason: String
  for +body: String
  exs head: String
  {head ++ ("\r\n\r\n" ++ body) == Srv.resp(code, reason, body) : String}
