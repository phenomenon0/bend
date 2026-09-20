# Executable SHA-256 specification from FIPS 180-4, sections 4 through 6.2.
# https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf
# The full padded message and chronological schedule favor inspection over speed.
# Inputs denote low-eight-bit octets; the standard domain is below 2^61 bytes.
import Base
import ./spec_state.bend as S

def rotate(+x: U32, +n: Nat) -> U32:
  U32.or(U32.shrn(x, n), U32.shln(x, Nat.sub(32n, n)))

def sigma0(+x: U32) -> U32:
  U32.xor(rotate(x, 7n), U32.xor(rotate(x, 18n), U32.shrn(x, 3n)))

def sigma1(+x: U32) -> U32:
  U32.xor(rotate(x, 17n), U32.xor(rotate(x, 19n), U32.shrn(x, 10n)))

def sum0(+x: U32) -> U32:
  U32.xor(rotate(x, 2n), U32.xor(rotate(x, 13n), rotate(x, 22n)))

def sum1(+x: U32) -> U32:
  U32.xor(rotate(x, 6n), U32.xor(rotate(x, 11n), rotate(x, 25n)))

def choice(+x: U32, y: U32, z: U32) -> U32:
  U32.xor(U32.and(x, y), U32.and(U32.not(x), z))

def majority(+x: U32, +y: U32, +z: U32) -> U32:
  U32.xor(U32.and(x, y), U32.xor(U32.and(x, z), U32.and(y, z)))

def initial() -> S.State:
  S.H{1779033703, 3144134277, 1013904242, 2773480762,
    1359893119, 2600822924, 528734635, 1541459225}

def constants() -> List<&2, U32>:
  [1116352408, 1899447441, 3049323471, 3921009573,
   961987163, 1508970993, 2453635748, 2870763221,
   3624381080, 310598401, 607225278, 1426881987,
   1925078388, 2162078206, 2614888103, 3248222580,
   3835390401, 4022224774, 264347078, 604807628,
   770255983, 1249150122, 1555081692, 1996064986,
   2554220882, 2821834349, 2952996808, 3210313671,
   3336571891, 3584528711, 113926993, 338241895,
   666307205, 773529912, 1294757372, 1396182291,
   1695183700, 1986661051, 2177026350, 2456956037,
   2730485921, 2820302411, 3259730800, 3345764771,
   3516065817, 3600352804, 4094571909, 275423344,
   430227734, 506948616, 659060556, 883997877,
   958139571, 1322822218, 1537002063, 1747873779,
   1955562222, 2024104815, 2227730452, 2361852424,
   2428436474, 2756734187, 3204031479, 3329325298]

def octets(bs: List<&2, U32>) -> List<&2, U32>:
  match bs:
    case Nil{}: []
    case b <> tail: U32.and(b, 255) <> octets(tail)

def word_bytes(+w: U32) -> List<&2, U32>:
  [U32.and(U32.shrn(w, 24n), 255), U32.and(U32.shrn(w, 16n), 255),
   U32.and(U32.shrn(w, 8n), 255), U32.and(w, 255)]

def length_bytes(+n: Nat) -> List<&2, U32>:
  List.append(&2, U32, word_bytes(U32.from_nat(Nat.div(n, U32.to_nat(536870912)))),
    word_bytes(U32.shln(U32.from_nat(n), 3n)))

def padding(+n: Nat) -> List<&2, U32>:
  128 <> List.append(&2, U32,
    List.replicate(U32, Nat.mod(Nat.sub(119n, Nat.mod(n, 64n)), 64n), 0),
    length_bytes(n))

def pad(+bs: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, octets(bs), padding(List.length(&2, U32, bs)))

def decode(bs: List<&2, U32>) -> List<&2, U32>:
  match bs:
    case a <> b <> c <> d <> tail:
      U32.or(U32.shln(a, 24n), U32.or(U32.shln(b, 16n),
        U32.or(U32.shln(c, 8n), d))) <> decode(tail)
    case _: []

def at(ws: List<&2, U32>, i: Nat) -> U32:
  Maybe.default(&2, U32, List.get(&2, U32, ws, i), 0)

# Absolute indices preserve the standard's chronological recurrence directly.
def extend(n: Nat, +t: Nat, +ws: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n: ws
    case 1n+p:
      w = U32.add(sigma1(at(ws, Nat.sub(t, 2n))),
        U32.add(at(ws, Nat.sub(t, 7n)),
          U32.add(sigma0(at(ws, Nat.sub(t, 15n))), at(ws, Nat.sub(t, 16n)))))
      extend(p, 1n+t, List.append(&2, U32, ws, [w]))

def step(k: U32, w: U32, state: S.State) -> S.State:
  match state:
    case S.H{+a, +b, +c, d, +e, +f, +g, h}:
      +t1 = U32.add(h, U32.add(sum1(e), U32.add(choice(e, f, g), U32.add(k, w))))
      t2 = U32.add(sum0(a), majority(a, b, c))
      S.H{U32.add(t1, t2), a, b, c, U32.add(d, t1), e, f, g}

def rounds(ks: List<&2, U32>, ws: List<&2, U32>, state: S.State) -> S.State:
  match ks ws:
    case k <> kt w <> wt: rounds(kt, wt, step(k, w, state))
    case _ _: state

def add(x: S.State, y: S.State) -> S.State:
  match x y:
    case S.H{a,b,c,d,e,f,g,h} S.H{i,j,k,l,m,n,o,p}:
      S.H{U32.add(a,i),U32.add(b,j),U32.add(c,k),U32.add(d,l),
        U32.add(e,m),U32.add(f,n),U32.add(g,o),U32.add(h,p)}

def compression(ws: List<&2, U32>, +state: S.State) -> S.State:
  add(state, rounds(constants(), extend(48n, 16n, ws), state))

def blocks(n: Nat, +ws: List<&2, U32>, state: S.State) -> S.State:
  match n:
    case 0n: state
    case 1n+p:
      blocks(p, List.drop(&2, U32, ws, 16n),
        compression(List.take(&2, U32, ws, 16n), state))

def digest(state: S.State) -> List<&2, U32>:
  match state:
    case S.H{a,b,c,d,e,f,g,h}: [a,b,c,d,e,f,g,h]

def sha256(bs: List<&2, U32>) -> List<&2, U32>:
  +ws = decode(pad(bs))
  digest(blocks(Nat.div(List.length(&2, U32, ws), 16n), ws, initial()))
