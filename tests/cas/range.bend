# cas (range): a GET, and the two ways it says no. The daemon re-hashes the
# bytes it is about to serve and folds the witness against the blob's address
# BEFORE the response text exists -- so a store that hands back the wrong
# chunk cannot be served, only refused. The second half of this file is that
# store: the same chunks, the same address, two manifest entries swapped, the
# kind of lie a bit of rot or a bad peer would tell. Nothing downstream has to
# be trusted for the refusal to happen; it happens here.
import Base
import ../../power/blake3.bend as B3
import ../../demos/io_cas_store/cas.bend as Cas

def say(r: Cas.Rsp) -> String:
  match r:
    case Cas.Ok{text}:
      text
    case Cas.No{why}:
      "refused: " ++ why

# the manifest with its first two entries swapped: chunk 1's bytes now sit
# where the tree says chunk 0's do
def swap(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      []
    case Con{a, t}:
      match t:
        case Nil{}:
          [a]
        case Con{b, t2}:
          Con{b, Con{a, t2}}

def lie(+st: Cas.Store, +b: Cas.Blob) -> Cas.Store:
  Cas.Store{Cas.store.chks(st), Cas.store.kept(st), Cas.store.seen(st),
    Cas.store.dupb(st),
    [Cas.Blob{Cas.blob.root(b), Cas.blob.n(b), Cas.blob.size(b),
      swap(Cas.blob.ids(b))}]}

def go(+st: Cas.Store, +b: Cas.Blob) -> IO(Unit):
  +a = B3.hex(Cas.blob.root(b))
  do IO<Unit>:
    u : Unit <- IO.print(say(Cas.get(st, a, 20, 18)))
    v : Unit <- IO.print(say(Cas.get(st, a, 900, 4)))
    w : Unit <- IO.print(say(Cas.get(st, "00", 0, 4)))
    IO.print(say(Cas.get(lie(st, b), a, 0, 4)))

def put(r: Cas.Store & Cas.Blob) -> IO(Unit):
  (st, b) = r
  go(st, b)

def main() -> IO(Unit):
  put(Cas.put(Cas.new(), String.repeat("abcdefghijklmnop", 8n), 4))
#|blob 6df1d7a6113d4c7037c4740e5cdf31dbb3715df03f9e8a549b83f5f4c2455476
#|chunks 10 size 128
#|range 20 18 parts 2
#|part 2 555ef87a08b186d325dd10ddc5f1c75cd443bdd7a8506097f1f5f8baa1826690 off 10 len 18 sibs 4 aa4edeadbf4ba8bf6852a2a223100f5a405071c5c5312d447fa94147e4f730c7 27b9a87955607d1a090069739394c27aa82fa2d85aafeef53c06b27984d98070 cfe667ba8e4ccda5511ae7ebe726d30b39369bce5ae249426da07d8346a8fdda 8be0e9c7c3022a4b9c27041ac5dae61069931b418dcbfc82be29ca319b88b168 verified
#|klmnopabcdefghijkl
#|part 3 aa4edeadbf4ba8bf6852a2a223100f5a405071c5c5312d447fa94147e4f730c7 off 28 len 18 sibs 4 555ef87a08b186d325dd10ddc5f1c75cd443bdd7a8506097f1f5f8baa1826690 27b9a87955607d1a090069739394c27aa82fa2d85aafeef53c06b27984d98070 cfe667ba8e4ccda5511ae7ebe726d30b39369bce5ae249426da07d8346a8fdda 8be0e9c7c3022a4b9c27041ac5dae61069931b418dcbfc82be29ca319b88b168 verified
#|mnopabcdefghijklmn
#|end
#|
#|refused: range past the end of the blob
#|refused: no blob with that address
#|refused: proof refused at part 0
