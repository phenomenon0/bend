# The proofs of the CAS store laws. The three tree laws are one step of `up`
# or of `root.go` each, so they compute; the response law names the head that
# resp builds in front of the blank line and computes too.
import Base
import ../../power/blake3.bend as B3
import ./cas.bend as Cas
import ./serve.bend as Srv
import ./LAWS.bend as Laws

def Laws.promote_alone(a):
  {==}

def Laws.pair_joins(a, b):
  {==}

def Laws.root_of_one(a):
  {==}

def Laws.body_after_blank(code, reason, body):
  (Srv.resp.head(code, reason, U32.from_nat(String.length(body))), {==})
