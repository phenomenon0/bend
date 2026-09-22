import Base
# HTTP/1.1 head parser: the suite's protocol stress case. A request
# head is generated per line index and then parsed byte by byte by a
# mode machine, the way an HTTP server parses what a socket hands it.
# Bend's String is a cons list, one node per character, so the parser
# walks a linked list where C walks bytes; that gap is the point, and
# the program is spelled the natural way anyway.
# 2^size requests fork as a balanced batch tree. Leaf i builds one
# realistic keep-alive GET, with the line index folded into the target
# and into two header values so no request is constant, and runs the
# machine over it. The machine has ten modes: the method token, the
# target token, the version token, CR seen, a line start, a header
# name, the optional whitespace after its colon, a header value, the
# CR of the final blank line, and done; a tenth, Bad, absorbs any byte
# that breaks the grammar and never leaves. Each completed token folds
# into the request checksum in order, acc = acc * 2654435761 ^ (kind *
# 40503 + payload), with the token's FNV-1a hash as the payload: the
# method is kind 1, the target 2, a header name 3, a header value 4.
# Request checksums sum up the fork tree, and a head that does not end
# in Done{} folds in as zero, so a parser that accepts everything and
# one that accepts nothing both miss the expected output.
#
# Sizes: small size = 8n (expect 3752284517), big size = 19n (expect
# 191409467); both verified against the C twin.

type Cls is Data:
  KSp{}
  KCr{}
  KLf{}
  KCo{}
  KCh{}

type St is Data:
  InM{h: U32}
  InT{h: U32}
  InV{}
  CrM{}
  Lin{}
  InN{h: U32}
  Ows{}
  InL{h: U32}
  CrL{}
  Don{}
  Bad{}

# the class of a head byte: the four delimiters, then anything else
def cls.go(sp: Bool, cr: Bool, lf: Bool, co: Bool) -> Cls:
  match sp cr lf co:
    case True{} _ _ _:
      KSp{}
    case _ True{} _ _:
      KCr{}
    case _ _ True{} _:
      KLf{}
    case _ _ _ True{}:
      KCo{}
    case _ _ _ _:
      KCh{}

def cls(+c: U32) -> Cls:
  cls.go(U32.is_eq(c, 32), U32.is_eq(c, 13), U32.is_eq(c, 10), U32.is_eq(c, 58))

# FNV-1a: one byte into a token hash
def fnv(h: U32, c: U32) -> U32:
  (U32.xor(h, c) * 16777619 : U32)

def fnv.new() -> U32:
  2166136261

# one completed token into the request checksum
def mix(acc: U32, kind: U32, x: U32) -> U32:
  U32.xor((acc * 2654435761 : U32), (kind * 40503 + x : U32))

# the machine: (mode, acc) steps over one classified byte. A token
# mode extends its hash until its delimiter arrives, then folds the
# hash in and hands over to the mode the delimiter begins.
def step.at(st: St, k: Cls, c: U32, acc: U32) -> St & U32:
  match st k:
    case InM{h} KSp{}:
      (InT{fnv.new()}, mix(acc, 1, h))
    case InM{h} _:
      (InM{fnv(h, c)}, acc)
    case InT{h} KSp{}:
      (InV{}, mix(acc, 2, h))
    case InT{h} _:
      (InT{fnv(h, c)}, acc)
    case InV{} KCr{}:
      (CrM{}, acc)
    case InV{} _:
      (InV{}, acc)
    case CrM{} KLf{}:
      (Lin{}, acc)
    case CrM{} _:
      (Bad{}, acc)
    case Lin{} KCr{}:
      (CrL{}, acc)
    case Lin{} _:
      (InN{fnv(fnv.new(), c)}, acc)
    case InN{h} KCo{}:
      (Ows{}, mix(acc, 3, h))
    case InN{h} _:
      (InN{fnv(h, c)}, acc)
    case Ows{} KSp{}:
      (Ows{}, acc)
    case Ows{} KCr{}:
      (CrM{}, acc)
    case Ows{} _:
      (InL{fnv(fnv.new(), c)}, acc)
    case InL{h} KCr{}:
      (CrM{}, mix(acc, 4, h))
    case InL{h} _:
      (InL{fnv(h, c)}, acc)
    case CrL{} KLf{}:
      (Don{}, acc)
    case CrL{} _:
      (Bad{}, acc)
    case Don{} _:
      (Don{}, acc)
    case Bad{} _:
      (Bad{}, acc)

def step(st: St, +c: U32, acc: U32) -> St & U32:
  step.at(st, cls(c), c, acc)

# the parser: one step per byte, (mode, acc) riding as r
def parse(s: String, r: St & U32) -> St & U32:
  match s:
    case SNil{}:
      r
    case SCon{Chr{c}, t}:
      (st, acc) = r
      parse(t, step(st, c, acc))

# only a head that reached Done{} counts; anything else scores zero
def fin.at(st: St, acc: U32) -> U32:
  match st:
    case Don{}:
      acc
    case InM{h}:
      0
    case InT{h}:
      0
    case InV{}:
      0
    case CrM{}:
      0
    case Lin{}:
      0
    case InN{h}:
      0
    case Ows{}:
      0
    case InL{h}:
      0
    case CrL{}:
      0
    case Bad{}:
      0

def fin(r: St & U32) -> U32:
  (st, acc) = r
  fin.at(st, acc)

# one request head, the line index folded into the target and into the
# two header values that a proxy would vary
def req(+i: U32) -> String:
  "GET /v1/items/" ++ U32.show(i) ++ "?page=" ++ U32.show((i % 97 : U32)) ++
  " HTTP/1.1\r\nHost: bench.example\r\nUser-Agent: bend-http/1.0\r\nAccept: */*\r\nAccept-Encoding: identity\r\nX-Request-Id: " ++
  U32.show((i * 2654435761 : U32)) ++
  "\r\nContent-Length: 0\r\nConnection: keep-alive\r\n\r\n"

# one request: build the head, then run the machine over it
def one(+i: U32) -> U32:
  fin(parse(req(i), (InM{fnv.new()}, 0)))

# batch tree over the request index space; checksums sum
def batch(+d: Nat, +i: U32) -> U32:
  match d:
    case 0n:
      one(i)
    case 1n+p:
      a b = batch(p, i) batch(p, (i + U32.shln(1, p) : U32))
      (a + b : U32)

def size.small() -> Nat:
  8n

def size.big() -> Nat:
  19n

def main() -> IO(Unit):
  IO.print(U32.show(batch!(size.big(), 0)))
