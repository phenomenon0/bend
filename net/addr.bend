# bend-net: addresses.
#
#   Addr.canon("0:0:0:0:0:0:0:1")    Some{"::1"}
#   Addr.literal("2001:DB8::0:1")    Done{"[2001:db8::1]"}   a URL's IP-literal
#   Addr.connect(host, dial, ms)     a connection to one of host's addresses
#
# IPv6's text form, read as RFC 4291 2.2 writes it (RFC 3986 3.2.2's
# IPv6address: eight groups of one to four hex digits, one run of them
# "::", the last two groups perhaps a dotted IPv4 address) and written as
# RFC 5952 4 says: lowercase, no leading zero, the longest run of two or
# more zero groups (the first of equals) as "::" and a lone zero group
# not, and an IPv4-mapped address (::ffff:0:0/96) as ::ffff: and the
# dotted address (RFC 5952 5). A URL's host that is an IPv6 address is in
# brackets, an IP-literal; bend-net keeps it so, written canonically, so
# the Host field, the origin a pool is keyed by and a URL written back
# all carry the brackets, and two spellings of one address are one
# origin. IPvFuture and zone IDs (RFC 6874) are refused. LAWS.bend holds
# the text to the RFCs' vectors.
#
# connect: the addresses DNS.resolve_all has for the host, tried one
# after another in the order it answers them (getaddrinfo's, RFC 6724's
# sort, which puts IPv6 first where it is reachable), each given an equal
# share of what is left of the deadline, the last one all of it; the
# first to connect is the connection, and when none does, the last one's
# failure is the answer. An address that cannot be reached at once (no
# IPv6 route: ENETUNREACH, EAFNOSUPPORT) costs nothing, and one that
# never answers costs its share. Not Happy Eyeballs (RFC 8305): the
# attempts are never raced.
import Base

# IPv6 text
# =========

# a hex digit's value, or 16 for a byte that is not one
def hex.of(+c: U32) -> U32:
  Bool.pick(U32, U32.is_le(48, c) && U32.is_le(c, 57), (c - 48 : U32),
    Bool.pick(U32, U32.is_le(97, c) && U32.is_le(c, 102), (c - 87 : U32),
      Bool.pick(U32, U32.is_le(65, c) && U32.is_le(c, 70), (c - 55 : U32), 16)))

def digits.at(ok: Bool, +v: U32, +acc: U32, +base: U32, go: U32 -> Maybe<&2, U32>) -> Maybe<&2, U32>:
  match ok:
    case True{}:
      go(((acc * base : U32) + v : U32))
    case False{}:
      None{}

# the value of s's digits in base (10 or 16), or None for a byte that is
# not one
def digits(s: Bytes(), +base: U32, +acc: U32) -> Maybe<&2, U32>:
  match s:
    case SNil{}:
      Some{acc}
    case SCon{Chr{+c}, t}:
      digits.at(U32.is_lt(hex.of(c), base), hex.of(c), acc, base, a => digits(t, base, a))

# a group: one to four hex digits
def h16(+s: Bytes()) -> Maybe<&2, U32>:
  Bool.pick(Maybe<&2, U32>, Nat.is_lt(0n, Bytes.len(s)) && Nat.is_le(Bytes.len(s), 4n), digits(s, 16, 0), None{})

def octet.max(m: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match m:
    case None{}:
      None{}
    case Some{+v}:
      Bool.pick(Maybe<&2, U32>, U32.is_le(v, 255), Some{v}, None{})

# a dec-octet (RFC 3986 3.2.2): 0 to 255 in one to three digits, no
# leading zero
def octet(+s: Bytes()) -> Maybe<&2, U32>:
  +n = Bytes.len(s)
  Bool.pick(Maybe<&2, U32>, Nat.is_lt(0n, n) && Nat.is_le(n, 3n)
    && (Nat.is_eq(n, 1n) || Bool.not(U32.is_eq(Bytes.get(s, 0n), 48))), octet.max(digits(s, 10, 0)), None{})

# s cut at every byte x
def split.at(cut: Bool, +s: Bytes(), +i: Nat, go: Bytes() -> List<&2, Bytes()>) -> List<&2, Bytes()>:
  match cut:
    case True{}:
      Con{String.take(s, i), go(String.drop(s, 1n+i))}
    case False{}:
      [s]

def split.go(k: Nat, +s: Bytes(), +x: U32) -> List<&2, Bytes()>:
  match k:
    case 0n:
      [s]
    case 1n+j:
      +i = Bytes.find_byte(s, 0n, x)
      split.at(Nat.is_lt(i, Bytes.len(s)), s, i, t => split.go(j, t, x))

def split(+s: Bytes(), +x: U32) -> List<&2, Bytes()>:
  split.go(Bytes.len(s), s, x)

def v4.four(+a: Bytes(), +b: Bytes(), +c: Bytes(), +d: Bytes()) -> Maybe<&2, List<&2, U32>>:
  do Maybe<&2, List<&2, U32>>:
    +w : U32 <- octet(a)
    +x : U32 <- octet(b)
    +y : U32 <- octet(c)
    +z : U32 <- octet(d)
    return [((w * 256 : U32) + x : U32), ((y * 256 : U32) + z : U32)]

def v4.list(xs: List<&2, Bytes()>) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Con{a, Con{b, Con{c, Con{d, Nil{}}}}}:
      v4.four(a, b, c, d)
    case _:
      None{}

# a dotted IPv4 address as the two groups it fills
def v4(+s: Bytes()) -> Maybe<&2, List<&2, U32>>:
  v4.list(split(s, 46))

def one.group(m: Maybe<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}:
      None{}
    case Some{g}:
      Some{[g]}

def one(dotted: Bool, +p: Bytes()) -> Maybe<&2, List<&2, U32>>:
  match dotted:
    case True{}:
      v4(p)
    case False{}:
      one.group(h16(p))

def side.cons(a: Maybe<&2, List<&2, U32>>, b: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match a b:
    case Some{x} Some{y}:
      Some{List.append(&2, U32, x, y)}
    case _ _:
      None{}

# the groups of pieces cut at ':', the last perhaps a dotted IPv4
# address when tail (only the address's end may be one)
def side.go(xs: List<&2, Bytes()>, +tail: Bool) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case Con{+p, +t}:
      side.cons(one(tail && List.is_empty(&2, Bytes(), t) && Nat.is_lt(Bytes.find_byte(p, 0n, 46), Bytes.len(p)), p),
        side.go(t, tail))

# one side of "::" (or the whole address when it has none): its groups,
# none when it is empty
def side(+s: Bytes(), +tail: Bool) -> Maybe<&2, List<&2, U32>>:
  Bool.pick(Maybe<&2, List<&2, U32>>, String.is_empty(s), Some{Nil{}}, side.go(split(s, 58), tail))

def eight(m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}:
      None{}
    case Some{+gs}:
      Bool.pick(Maybe<&2, List<&2, U32>>, Nat.is_eq(List.length(&2, U32, gs), 8n), Some{gs}, None{})

# "::" stands for one or more zero groups: the sides hold at most seven
def fill(l: Maybe<&2, List<&2, U32>>, r: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match l r:
    case Some{+x} Some{+y}:
      +n = Nat.add(List.length(&2, U32, x), List.length(&2, U32, y))
      Bool.pick(Maybe<&2, List<&2, U32>>, Nat.is_le(n, 7n),
        Some{List.concat(&2, U32, [x, List.replicate(U32, Nat.sub(8n, n), 0), y])}, None{})
    case _ _:
      None{}

def groups.of(two: Maybe<&2, Nat>, +s: Bytes()) -> Maybe<&2, List<&2, U32>>:
  match two:
    case None{}:
      eight(side(s, True{}))
    case Some{+i}:
      fill(side(String.take(s, i), False{}), side(String.drop(s, Nat.add(i, 2n)), True{}))

# an IPv6 address's eight groups, or None: RFC 4291 2.2's text (no
# brackets, no zone); a second "::" leaves an empty piece, which no group is
def parse(+s: Bytes()) -> Maybe<&2, List<&2, U32>>:
  groups.of(Bytes.find(s, "::"), s)

def hexd(+v: U32) -> U32:
  Bool.pick(U32, U32.is_lt(v, 10), (v + 48 : U32), (v + 87 : U32))

def nib(+g: U32, n: Nat) -> U32:
  hexd(U32.and(U32.shrn(g, n), 15))

# a group in hex, lowercase, without leading zeros
def h16.show(+g: U32) -> Bytes():
  Bool.pick(Bytes(), U32.is_le(4096, g), Bytes.from_list([nib(g, 12n), nib(g, 8n), nib(g, 4n), nib(g, 0n)]),
    Bool.pick(Bytes(), U32.is_le(256, g), Bytes.from_list([nib(g, 8n), nib(g, 4n), nib(g, 0n)]),
      Bool.pick(Bytes(), U32.is_le(16, g), Bytes.from_list([nib(g, 4n), nib(g, 0n)]), Bytes.from_list([nib(g, 0n)]))))

def join.go(xs: List<&2, U32>, acc: Bytes()) -> Bytes():
  match xs:
    case Nil{}:
      acc
    case Con{x, t}:
      join.go(t, Bytes.concat([acc, ":", h16.show(x)]))

# groups in hex, a ':' between each
def join(xs: List<&2, U32>) -> Bytes():
  match xs:
    case Nil{}:
      ""
    case Con{x, t}:
      join.go(t, h16.show(x))

# the longest run of zero groups (its start and length; the first of
# equals): i the index, cs and cl the run under way, bs and bl the best
def run.go(xs: List<&2, U32>, +i: Nat, +cs: Nat, +cl: Nat, +bs: Nat, +bl: Nat) -> Nat & Nat:
  match xs:
    case Nil{}:
      +gt = Nat.is_lt(bl, cl)
      (Bool.pick(Nat, gt, cs, bs), Bool.pick(Nat, gt, cl, bl))
    case Con{+x, t}:
      +z = U32.is_eq(x, 0)
      +end = Nat.is_lt(bl, cl) && Bool.not(z)
      run.go(t, 1n+i, Bool.pick(Nat, z, Bool.pick(Nat, Nat.is_eq(cl, 0n), i, cs), 0n), Bool.pick(Nat, z, 1n+cl, 0n),
        Bool.pick(Nat, end, cs, bs), Bool.pick(Nat, end, cl, bl))

def show.at(r: Nat & Nat, +gs: List<&2, U32>) -> Bytes():
  (+bs, +bl) = r
  Bool.pick(Bytes(), Nat.is_lt(bl, 2n), join(gs),
    Bytes.concat([join(List.take(&2, U32, gs, bs)), "::", join(List.drop(&2, U32, gs, Nat.add(bs, bl)))]))

def v4.show(xs: List<&2, U32>) -> Bytes():
  match xs:
    case Con{+x, Con{+y, Nil{}}}:
      Bytes.concat([U32.show(U32.shrn(x, 8n)), ".", U32.show(U32.and(x, 255)), ".", U32.show(U32.shrn(y, 8n)), ".",
        U32.show(U32.and(y, 255))])
    case _:
      ""

# eight groups as RFC 5952 writes them
def show(+gs: List<&2, U32>) -> Bytes():
  Bool.pick(Bytes(), String.eq(join(List.take(&2, U32, gs, 6n)), "0:0:0:0:0:ffff"),
    Bytes.append("::ffff:", v4.show(List.drop(&2, U32, gs, 6n))), show.at(run.go(gs, 0n, 0n, 0n, 0n, 0n), gs))

def canon.of(m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, Bytes()>:
  match m:
    case None{}:
      None{}
    case Some{gs}:
      Some{show(gs)}

# an IPv6 address's canonical text, or None when s is not one
def canon(+s: Bytes()) -> Maybe<&2, Bytes()>:
  canon.of(parse(s))

# Hosts
# =====

def literal.at(fut: Bool, zone: Bool, m: Maybe<&2, List<&2, U32>>) -> Result<&2, &2, Bytes(), Bytes()>:
  match fut zone m:
    case True{} _ _:
      Fail{"IPvFuture addresses are not supported"}
    case False{} True{} _:
      Fail{"IPv6 zone IDs are not supported"}
    case False{} False{} None{}:
      Fail{"bad IPv6 address"}
    case False{} False{} Some{gs}:
      Done{Bytes.concat(["[", show(gs), "]"])}

# what is between an IP-literal's brackets (RFC 3986 3.2.2), as the host
# a URL keeps: the IPv6 address, canonical, in its brackets; an
# IPvFuture ("v1.x") or a zone ID ("%25eth0", RFC 6874) is refused
def literal(+s: Bytes()) -> Result<&2, &2, Bytes(), Bytes()>:
  +c = Bytes.get(s, 0n)
  literal.at(U32.is_eq(c, 118) || U32.is_eq(c, 86), Nat.is_lt(Bytes.find_byte(s, 0n, 37), Bytes.len(s)), parse(s))

# a URL's host as the resolver and the connect take it: an IP-literal
# without its brackets, a name as it is
def bare(+h: Bytes()) -> Bytes():
  Bool.pick(Bytes(), U32.is_eq(Bytes.get(h, 0n), 91), String.take(String.drop(h, 1n), Nat.sub(Bytes.len(h), 2n)), h)

# an address as a URL or a banner writes it: an IPv6 one (it has a ':')
# in brackets
def bracket(+h: Bytes()) -> Bytes():
  Bool.pick(Bytes(), Nat.is_lt(Bytes.find_byte(h, 0n, 58), Bytes.len(h)) && Bool.not(U32.is_eq(Bytes.get(h, 0n), 91)),
    Bytes.concat(["[", h, "]"]), h)

# Connecting
# ==========

# how to connect: TLS (to name, the name the certificate must carry,
# bare; offering alpn; trusting ca) or plain TCP, to port
type Dial is Data:
  Dial{tls: Bool, port: U32, name: String, alpn: String, ca: String}

def Got() -> Type:
  Result<&1, &1, U32 & String, Socket & String>

# a host's connection: its name did not resolve (the resolver's code and
# reason), or what the attempts came to
type Dialed is Type:
  NoName{code: U32, msg: String}
  Tried{r: Got()}

def one.plain(r: Result<&1, &1, U32 & String, Socket>) -> IO(Got()):
  match r:
    case Done{s}:
      IO.pure(Got(), Done{(s, "")})
    case Fail{e}:
      IO.pure(Got(), Fail{e})

# one attempt, to one address, under ms
def attempt(d: Dial, addr: String, ms: U32) -> IO(Got()):
  match d:
    case Dial{tls, port, name, alpn, ca}:
      match tls:
        case True{}:
          TLS.connect(addr, port, name, alpn, ca, ms)
        case False{}:
          IO.bind(Result<&1, &1, U32 & String, Socket>, Got(), TCP.connect_poll(addr, port, ms), one.plain)

# an attempt's share of what is left before until, among n
def share(+now: Nat, +until: Nat, +n: Nat) -> U32:
  U32.from_nat(Nat.div(Nat.sub(until, now), n))

def then(r: Got(), next: (U32 & String) -> IO(Got())) -> IO(Got()):
  match r:
    case Done{sp}:
      IO.pure(Got(), Done{sp})
    case Fail{e}:
      next(e)

def tries(xs: List<&2, String>, +d: Dial, +until: Nat, last: U32 & String) -> IO(Got()):
  match xs:
    case Nil{}:
      IO.pure(Got(), Fail{last})
    case Con{a, +t}:
      IO.bind(Nat, Got(), IO.now(), +now =>
        IO.bind(Got(), Got(), attempt(d, a, share(now, until, 1n+List.length(&2, String, t))),
          r => then(r, e => tries(t, d, until, e))))

def resolved(+d: Dial, +until: Nat, r: Result<&1, &1, U32 & String, String>) -> IO(Dialed):
  match r:
    case Fail{e}:
      (code, msg) = e
      IO.pure(Dialed, NoName{code, msg})
    case Done{+addrs}:
      IO.bind(Got(), Dialed, tries(split(addrs, 44), d, until, (22, "no address")), g => IO.pure(Dialed, Tried{g}))

# a connection to one of host's addresses (host as a URL has it: an
# IP-literal in brackets, a name, a dotted address) under ms, as the
# head of this file says
def connect(+host: String, +d: Dial, +ms: U32) -> IO(Dialed):
  do IO<Dialed>:
    +now : Nat <- IO.now()
    r : Result<&1, &1, U32 & String, String> <- DNS.resolve_all(bare(host))
    resolved(d, Nat.add(now, U32.to_nat(ms)), r)
