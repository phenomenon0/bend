# cas (chunk): a PUT, end to end and small. The payload is one 16-byte phrase
# eight times over, so the content-defined cuts land on the same content twice
# and the store has to notice: the manifest is eight chunk ids, the table
# behind them is shorter than eight, and the bytes the second copy did not
# cost are counted. The address is the Merkle root over the chunks' addresses,
# not a hash of the file, so it is stable under a store that already holds
# some of those chunks.
import Base
import ../../power/blake3.bend as B3
import ../../demos/io_cas_store/cas.bend as Cas

def ids(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{i, t}:
      (" " ++ U32.show(i)) ++ ids(t)

def say(+st: Cas.Store, +b: Cas.Blob) -> IO(Unit):
  do IO<Unit>:
    u : Unit <- IO.print("root " ++ B3.hex(Cas.blob.root(b)))
    v : Unit <- IO.print(String.concat(["chunks ", U32.show(Cas.blob.n(b)),
      " size ", U32.show(Cas.blob.size(b))]))
    w : Unit <- IO.print(String.concat(["seen ", U32.show(Cas.store.seen(st)),
      " kept ", U32.show(Cas.store.kept(st)),
      " dupbytes ", U32.show(Cas.store.dupb(st))]))
    IO.print("manifest" ++ ids(Cas.blob.ids(b)))

def go(r: Cas.Store & Cas.Blob) -> IO(Unit):
  (st, b) = r
  say(st, b)

def main() -> IO(Unit):
  go(Cas.put(Cas.new(), String.repeat("abcdefghijklmnop", 8n), 4))
#|root 6df1d7a6113d4c7037c4740e5cdf31dbb3715df03f9e8a549b83f5f4c2455476
#|chunks 10 size 128
#|seen 10 kept 7 dupbytes 41
#|manifest 0 1 2 3 4 5 1 2 3 6
