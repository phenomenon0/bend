# The proofs of bend-net's laws.
#
# handler_framed leans on bend-proxy's scan_is_spec and frames_agree:
# the server's scan is the proxy's, so its reads frame a stream as the
# reference walk does, and the walk's requests are frame()'s. What is
# left is that the adapter is the one LAWS.bend spells out, field by
# field. respond_framed leans on bend-proxy's rr.h: a response that
# passes rvalid, written by rser, is read back by wire/http1's spec as
# exactly itself; the server's check either is rvalid or passes only
# where rvalid does (fast.sound: the status table, the known names and a
# value's one scan each imply their part of rvalid), and the 500 passes
# by computation. route_first is an induction on the table with the
# allowed methods gathered on the way; the reference's nub is union
# started empty. pool_clean is wire/client.bend's reuse_clean, read at
# the client's own decision. The redirect laws are one induction on the
# chain's budget, with the scripted peer's count and the cleanliness of
# the request about to go carried along; follow's request is clean
# because it keeps the credentials only for the first origin. The
# streamed bodies' laws lean on wire/http1's: drain_reads, reads_split,
# feed_buf_is_feed, and walk.lem, the simulation resp_sim is made of.
# stream_head leans on the engine's: STEP, the step of the simulation
# frame_sim is made of, carried over every byte, and read where it ends.
import Base
import ../wire/reader.bend as Wr
import ../wire/client.bend as C
import ../wire/world.bend as W
import ../wire/http1/resp.bend as R
import ../wire/http1/spec.bend as RS
import ../demos/io_http_engine/main.bend as Eng
import ../demos/io_http_engine/spec.bend as Spec
import ../demos/io_proxy/core.bend as X
import ../demos/io_proxy/LAWS.bend as PL
import ../demos/io_proxy/PROOF.bend as PP
import ../demos/io_http_engine/LAWS.bend as EL
import ../demos/io_http_engine/PROOF.bend as EP
import ../wire/http1/LAWS.bend as HL
import ../wire/http1/PROOF.bend as HP
import ./http.bend as Http
import ./url.bend as U
import ./server.bend as Server
import ./client.bend as Client
import ./stream.bend as Stream
import ./LAWS.bend as Laws

# Booleans
# ========

def tt(a: Bool, b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      hb
    case False{}:
      Bool.no({Bool.and(False{}, b) == True{} : Bool}, ha)

# a disjunction that holds: one side or the other does
def or.at(-g: Type, a: Bool, -b: Bool, h: {Bool.or(a, b) == True{} : Bool}, ha: {a == True{} : Bool} -> g,
  hb: {b == True{} : Bool} -> g) -> g:
  match a:
    case True{}:
      ha({==})
    case False{}:
      hb(h)

# String equality is equality
def str.step(x: U32, y: U32, -xt: String, -yt: String, c: Cmp, ec: {U32.cmp(x, y) == c : Cmp},
  h: {Cmp.is_eq(String.order.step(xt, yt, c)) == True{} : Bool},
  ih: {String.eq(xt, yt) == True{} : Bool} -> {xt == yt : String}) ->
  {SCon{Chr{x}, xt} == SCon{Chr{y}, yt} : String}:
  match c:
    case LT{}:
      Bool.no({SCon{Chr{x}, xt} == SCon{Chr{y}, yt} : String}, h)
    case GT{}:
      Bool.no({SCon{Chr{x}, xt} == SCon{Chr{y}, yt} : String}, h)
    case EQ{}:
      %PP.u32.eq(x, y, Equal.cong(Cmp, Bool, k => Cmp.is_eq(k), U32.cmp(x, y), EQ{}, ec)) :
        {SCon{Chr{x}, xt} == SCon{Chr{_}, yt} : String}
      %ih(h) : {SCon{Chr{x}, xt} == SCon{Chr{x}, _} : String}
      {==}

def str.eq(a: String, b: String, h: {String.eq(a, b) == True{} : Bool}) -> {a == b : String}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{y, yt}:
      Bool.no({SNil{} == SCon{y, yt} : String}, h)
    case SCon{Chr{x}, xt} SNil{}:
      Bool.no({SCon{Chr{x}, xt} == SNil{} : String}, h)
    case SCon{Chr{+x}, xt} SCon{Chr{+y}, yt}:
      str.step(x, y, xt, yt, U32.cmp(x, y), {==}, h, e => str.eq(xt, yt, e))

# The vectors
# ===========
#
# closed: each is the checker's own computation

def Laws.check_vectors():
  {==}

def Laws.route_vectors():
  {==}

def Laws.pct_round_trip():
  {==}

def Laws.pct_vectors():
  {==}

def Laws.query_vectors():
  {==}

def Laws.url_vectors():
  {==}

def Laws.resolve_vectors():
  {==}

# IPv6: the text, the IP-literals, the Host field and the origin, by
# computation

def Laws.ip6_vectors():
  {==}

def Laws.ip6_round_trip():
  {==}

def Laws.literal_vectors():
  {==}

def Laws.literal_round_trip():
  {==}

def Laws.host_vectors():
  {==}

def Laws.origin_vectors():
  {==}

# The pool
# ========

def pc.at(m: C.Out(W.World), h: {C.ok.of(m) == True{} : Bool}) -> {Laws.kept(m) == True{} : Bool}:
  match m:
    case (s, r):
      match r:
        case Fail{w}:
          {==}
        case Done{g}:
          match g:
            case C.Got{i, x, extra, reuse}:
              h

def Laws.pool_clean(e, b, req, s):
  pc.at(C.sim.exchange(e, b, req, s), C.reuse_clean(e, b, req, s))

# Handlers see what the RFC framed
# ================================

def reads.at.eq(s: X.Scanned, -t: List<&2, Bytes()>,
  ih: @sc: X.Scan -> {Laws.reads.go(t, sc) == PL.reads.go(t, sc) : PL.Conn}) ->
  {PL.reads.at(s, s2 => Laws.reads.go(t, s2)) == PL.reads.at(s, s2 => PL.reads.go(t, s2)) : PL.Conn}:
  match s:
    case X.Scanned{+ts, tl}:
      match tl:
        case X.TWait{sc}:
          Equal.cong(PL.Conn, PL.Conn, c => PL.conn.more(ts, c), Laws.reads.go(t, sc), PL.reads.go(t, sc), ih(sc))
        case X.TBad{}:
          Equal.trans(PL.Conn, PL.reads.at(X.Scanned{ts, X.TBad{}}, s2 => Laws.reads.go(t, s2)), PL.Conn{ts, X.TBad{}},
            PL.reads.at(X.Scanned{ts, X.TBad{}}, s2 => PL.reads.go(t, s2)), {==}, {==})
        case X.TUp{}:
          Equal.trans(PL.Conn, PL.reads.at(X.Scanned{ts, X.TUp{}}, s2 => Laws.reads.go(t, s2)), PL.Conn{ts, X.TUp{}},
            PL.reads.at(X.Scanned{ts, X.TUp{}}, s2 => PL.reads.go(t, s2)), {==}, {==})

# the server's reads are the proxy's
def reads.eq(rs: List<&2, Bytes()>, sc: X.Scan) -> {Laws.reads.go(rs, sc) == PL.reads.go(rs, sc) : PL.Conn}:
  match rs:
    case Nil{}:
      {==}
    case Con{+r, t}:
      reads.at.eq(X.scan(r, sc), t, sc2 => reads.eq(t, sc2))

def took.of(c: PL.Conn, f: PL.PScanned, h: PL.Conns(c, f)) ->
  {PL.conn.took(c) == PL.took.reqs(PL.scanned.took(f)) : List<&2, Eng.Req>}:
  match c f:
    case PL.Conn{ts, t} PL.PScanned{us, u}:
      (e1, e2) = h
      e1

def agree.of(f: PL.PScanned, g: Spec.Frames, h: PL.Agrees(f, g)) ->
  {PL.took.reqs(PL.scanned.took(f)) == Laws.framed(g) : List<&2, Eng.Req>}:
  match f g:
    case PL.PScanned{us, u} Spec.Frames{rs, e}:
      (e1, e2) = h
      e1

# A value with no blank at either end is its own trim: the fast path
# of the adapter hands the value as it is exactly when the trim would.
def or.false(+a: Bool, +b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      Bool.no({True{} == False{} : Bool}, Equal.sym(Bool, True{}, False{}, h))
    case False{}:
      {==}

def or.false_r(+a: Bool, +b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      Bool.no({b == False{} : Bool}, Equal.sym(Bool, True{}, False{}, h))
    case False{}:
      h

def sub.zero(+a: Nat) -> {Nat.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def take.all(+s: Bytes()) -> {String.take(s, String.length.go(s, 0n)) == s : Bytes()}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %Equal.sym(Nat, String.length.go(t, 1n), 1n+String.length.go(t, 0n), Bytes.len.shift(t, 0n)) :
        {String.take(SCon{h, t}, _) == SCon{h, t} : Bytes()}
      %Equal.sym(Bytes(), String.take(t, String.length.go(t, 0n)), t, take.all(t)) :
        {SCon{h, _} == SCon{h, t} : Bytes()}
      {==}

def lead.keep(+x: Bytes(), +c: U32) -> {X.trim.lead(x, False{}, c) == SCon{Chr{c}, x} : Bytes()}:
  match x:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      match h:
        case Chr{+d}:
          {==}

def end.keep(+k: Nat, +s: Bytes()) -> {X.trim.end(k, s, False{}) == 1n+k : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      {==}

# the last byte's index, one less than the length
def last.at(+t: Bytes()) -> {Nat.sub(String.length.go(t, 1n), 1n) == String.length.go(t, 0n) : Nat}:
  %Equal.sym(Nat, String.length.go(t, 1n), 1n+String.length.go(t, 0n), Bytes.len.shift(t, 0n)) :
    {Nat.sub(_, 1n) == String.length.go(t, 0n) : Nat}
  sub.zero(String.length.go(t, 0n))

def last.ok(+t: Bytes(), +c: U32,
  h1: {X.ows(Bytes.get(SCon{Chr{c}, t}, Nat.sub(String.length.go(t, 1n), 1n))) == False{} : Bool}) ->
  {X.ows(Bytes.get(SCon{Chr{c}, t}, String.length.go(t, 0n))) == False{} : Bool}:
  %last.at(t) : {X.ows(Bytes.get(SCon{Chr{c}, t}, _)) == False{} : Bool}
  h1

def trim.cut.none(+t: Bytes(), +c: U32,
  h1: {X.ows(Bytes.get(SCon{Chr{c}, t}, String.length.go(t, 0n))) == False{} : Bool}) ->
  {X.trim.cut(String.length.go(t, 1n), SCon{Chr{c}, t}) == SCon{Chr{c}, t} : Bytes()}:
  %Equal.sym(Nat, String.length.go(t, 1n), 1n+String.length.go(t, 0n), Bytes.len.shift(t, 0n)) :
    {X.trim.cut(_, SCon{Chr{c}, t}) == SCon{Chr{c}, t} : Bytes()}
  %Equal.sym(Bool, X.ows(Bytes.get(SCon{Chr{c}, t}, String.length.go(t, 0n))), False{}, h1) :
    {String.take(SCon{Chr{c}, t}, X.trim.end(String.length.go(t, 0n), SCon{Chr{c}, t}, _)) == SCon{Chr{c}, t} : Bytes()}
  %Equal.sym(Nat, X.trim.end(String.length.go(t, 0n), SCon{Chr{c}, t}, False{}), 1n+String.length.go(t, 0n),
      end.keep(String.length.go(t, 0n), SCon{Chr{c}, t})) :
    {String.take(SCon{Chr{c}, t}, _) == SCon{Chr{c}, t} : Bytes()}
  %Equal.sym(Bytes(), String.take(t, String.length.go(t, 0n)), t, take.all(t)) :
    {SCon{Chr{c}, _} == SCon{Chr{c}, t} : Bytes()}
  {==}

def trim.none(+v: Bytes(), h0: {X.ows(Bytes.get(v, 0n)) == False{} : Bool},
  h1: {X.ows(Bytes.get(v, Nat.sub(Bytes.len(v), 1n))) == False{} : Bool}) -> {X.trim(v) == v : Bytes()}:
  match v:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      match h:
        case Chr{+c}:
          %Equal.sym(Bool, X.ows(c), False{}, h0) :
            {X.trim.cut(Bytes.len(X.trim.lead(t, _, c)), X.trim.lead(t, _, c)) == SCon{Chr{c}, t} : Bytes()}
          %Equal.sym(Bytes(), X.trim.lead(t, False{}, c), SCon{Chr{c}, t}, lead.keep(t, c)) :
            {X.trim.cut(Bytes.len(_), _) == SCon{Chr{c}, t} : Bytes()}
          trim.cut.none(t, c, last.ok(t, c, h1))

def tf.at(+e: Bool, +v: Bytes(),
  +h: {Bool.or(X.ows(Bytes.get(v, 0n)), X.ows(Bytes.get(v, Nat.sub(Bytes.len(v), 1n)))) == e : Bool}) ->
  {Http.trim.at(e, v) == X.trim(v) : Bytes()}:
  match e:
    case True{}:
      {==}
    case False{}:
      +a = X.ows(Bytes.get(v, 0n))
      +b = X.ows(Bytes.get(v, Nat.sub(Bytes.len(v), 1n)))
      Equal.sym(Bytes(), X.trim(v), v, trim.none(v, or.false(a, b, h), or.false_r(a, b, h)))

def trim.fast.eq(+v: Bytes()) -> {Http.trim.fast(v) == X.trim(v) : Bytes()}:
  tf.at(Bool.or(X.ows(Bytes.get(v, 0n)), X.ows(Bytes.get(v, Nat.sub(Bytes.len(v), 1n)))), v, {==})

def fields.eq(fs: List<&2, Wr.Field>) -> {Http.fields.of(fs) == Laws.spec.fields(fs) : List<&2, Http.Header>}:
  match fs:
    case Nil{}:
      {==}
    case Con{f, t}:
      match f:
        case Wr.Field{+n, +v}:
          %Equal.sym(Bytes(), Http.trim.fast(v), X.trim(v), trim.fast.eq(v)) :
            {Con{Http.Header{n, _}, Http.fields.of(t)} == Con{Http.Header{n, X.trim(v)}, Laws.spec.fields(t)} :
              List<&2, Http.Header>}
          Equal.cong(List<&2, Http.Header>, List<&2, Http.Header>, xs => Con{Http.Header{n, X.trim(v)}, xs},
            Http.fields.of(t), Laws.spec.fields(t), fields.eq(t))

def req.eq(+ip: Bytes(), r: Eng.Req) -> {Http.req.of(ip, r) == Laws.spec.req(ip, r) : Http.Request}:
  match r:
    case Eng.Req{meth, +t, +body, close, ws, key, hd}:
      match hd:
        case Eng.Hd{+m, v10, fs, cn}:
          Equal.cong(List<&2, Http.Header>, Http.Request,
            xs => Http.Request{m, String.take(t, Bytes.find_byte(t, 0n, 63)), String.drop(t, 1n+Bytes.find_byte(t, 0n, 63)),
              xs, body, ip, Nil{}}, Http.fields.of(fs), Laws.spec.fields(fs), fields.eq(fs))

def handed.eq(+ip: Bytes(), rs: List<&2, Eng.Req>) -> {Laws.handed(ip, rs) == Laws.spec.reqs(ip, rs) : List<&2, Http.Request>}:
  match rs:
    case Nil{}:
      {==}
    case Con{+r, t}:
      %Equal.sym(Http.Request, Http.req.of(ip, r), Laws.spec.req(ip, r), req.eq(ip, r)) : {Con{_, Laws.handed(ip, t)} == Con{Laws.spec.req(ip, r), Laws.spec.reqs(ip, t)} : List<&2, Http.Request>}
      Equal.cong(List<&2, Http.Request>, List<&2, Http.Request>, xs => Con{Laws.spec.req(ip, r), xs},
        Laws.handed(ip, t), Laws.spec.reqs(ip, t), handed.eq(ip, t))

def Laws.handler_framed(ip, rs):
  +l = Bytes.to_list(Bytes.concat(rs))
  +took = PL.conn.took(Laws.reads(rs))
  Equal.trans(List<&2, Http.Request>, Laws.handed(ip, took), Laws.spec.reqs(ip, took),
    Laws.spec.reqs(ip, Laws.framed(Spec.frame(l))), handed.eq(ip, took),
    Equal.cong(List<&2, Eng.Req>, List<&2, Http.Request>, xs => Laws.spec.reqs(ip, xs), took, Laws.framed(Spec.frame(l)),
      Equal.trans(List<&2, Eng.Req>, took, PL.conn.took(PL.reads(rs)), Laws.framed(Spec.frame(l)),
        Equal.cong(PL.Conn, List<&2, Eng.Req>, c => PL.conn.took(c), Laws.reads(rs), PL.reads(rs),
          reads.eq(rs, X.scan.new())),
        Equal.trans(List<&2, Eng.Req>, PL.conn.took(PL.reads(rs)), PL.took.reqs(PL.scanned.took(PL.frame(l))),
          Laws.framed(Spec.frame(l)), took.of(PL.reads(rs), PL.frame(l), PL.scan_is_spec(rs)),
          agree.of(PL.frame(l), Spec.frame(l), PL.frames_agree(l))))))

# Every response is framed
# ========================

# the statuses and the names the fast check knows, each as rvalid wants it
def st.good(t: Http.St) -> Bool:
  match t:
    case Http.St{k, +cd, +why}:
      X.rok.code(cd, k) && X.rok.all(RS.TVal{}, why)

def st.all(ts: List<&2, Http.St>) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case Con{t, r}:
      st.good(t) && st.all(r)

def name.ok(+n: Bytes()) -> Bool:
  X.full(n) && X.rok.all(RS.TName{}, n) && X.ris.other(RS.field(RS.lows(Bytes.to_list(n))))

def names.all(ks: List<&2, Bytes()>) -> Bool:
  match ks:
    case Nil{}:
      True{}
    case Con{+k, t}:
      name.ok(k) && names.all(t)

def st.known() -> {st.all(Http.statuses()) == True{} : Bool}:
  {==}

def names.known() -> {names.all(Http.known()) == True{} : Bool}:
  {==}

# a status the table has is one rvalid takes, its code and its reason
def st.hit(+k: U32, +tc: Bytes(), +tw: Bytes(), +c: U32, +cd: Bytes(), +why: Bytes(),
  ek: {U32.is_eq(k, c) == True{} : Bool}, +hit: {Bool.and(String.eq(tc, cd), String.eq(tw, why)) == True{} : Bool},
  g: {st.good(Http.St{k, tc, tw}) == True{} : Bool}) ->
  {Bool.and(X.rok.code(cd, c), X.rok.all(RS.TVal{}, why)) == True{} : Bool}:
  +e1 = PP.u32.eq(k, c, ek)
  +e2 = str.eq(tc, cd, Bool.and_l(String.eq(tc, cd), String.eq(tw, why), hit))
  +e3 = str.eq(tw, why, Bool.and_r(String.eq(tc, cd), String.eq(tw, why), hit))
  %e1 : {Bool.and(X.rok.code(cd, _), X.rok.all(RS.TVal{}, why)) == True{} : Bool}
  %e2 : {Bool.and(X.rok.code(_, k), X.rok.all(RS.TVal{}, why)) == True{} : Bool}
  %e3 : {Bool.and(X.rok.code(tc, k), X.rok.all(RS.TVal{}, _)) == True{} : Bool}
  g

def st.eqs(e: Bool, +k: U32, +tc: Bytes(), +tw: Bytes(), +c: U32, +cd: Bytes(), +why: Bytes(), -r: List<&2, Http.St>,
  ek: {U32.is_eq(k, c) == True{} : Bool}, ee: {Bool.and(String.eq(tc, cd), String.eq(tw, why)) == e : Bool},
  h: {Http.known.at(e, u => Http.st.in(r, c, cd, why)) == True{} : Bool},
  g: {st.good(Http.St{k, tc, tw}) == True{} : Bool},
  ih: {Http.st.in(r, c, cd, why) == True{} : Bool} -> {Bool.and(X.rok.code(cd, c), X.rok.all(RS.TVal{}, why)) == True{} : Bool}) ->
  {Bool.and(X.rok.code(cd, c), X.rok.all(RS.TVal{}, why)) == True{} : Bool}:
  match e:
    case True{}:
      st.hit(k, tc, tw, c, cd, why, ek, ee, g)
    case False{}:
      ih(h)

def st.at(b: Bool, +k: U32, +tc: Bytes(), +tw: Bytes(), +c: U32, +cd: Bytes(), +why: Bytes(), -r: List<&2, Http.St>,
  eb: {U32.is_eq(k, c) == b : Bool},
  h: {Http.st.in.at(b, cd, why, tc, tw, u => Http.st.in(r, c, cd, why)) == True{} : Bool},
  g: {st.good(Http.St{k, tc, tw}) == True{} : Bool},
  ih: {Http.st.in(r, c, cd, why) == True{} : Bool} -> {Bool.and(X.rok.code(cd, c), X.rok.all(RS.TVal{}, why)) == True{} : Bool}) ->
  {Bool.and(X.rok.code(cd, c), X.rok.all(RS.TVal{}, why)) == True{} : Bool}:
  match b:
    case True{}:
      st.eqs(Bool.and(String.eq(tc, cd), String.eq(tw, why)), k, tc, tw, c, cd, why, r, eb, {==}, h, g, ih)
    case False{}:
      ih(h)

def st.sound(ts: List<&2, Http.St>, +c: U32, +cd: Bytes(), +why: Bytes(), +all: {st.all(ts) == True{} : Bool},
  h: {Http.st.in(ts, c, cd, why) == True{} : Bool}) ->
  {Bool.and(X.rok.code(cd, c), X.rok.all(RS.TVal{}, why)) == True{} : Bool}:
  match ts:
    case Nil{}:
      Bool.no({Bool.and(X.rok.code(cd, c), X.rok.all(RS.TVal{}, why)) == True{} : Bool}, h)
    case Con{t, +r}:
      match t:
        case Http.St{+k, +tc, +tw}:
          st.at(U32.is_eq(k, c), k, tc, tw, c, cd, why, r, {==}, h, Bool.and_l(st.good(Http.St{k, tc, tw}), st.all(r), all),
            hr => st.sound(r, c, cd, why, Bool.and_r(st.good(Http.St{k, tc, tw}), st.all(r), all), hr))

def name.hit(+n: Bytes(), +k: Bytes(), e: {n == k : Bytes()}, g: {name.ok(k) == True{} : Bool}) ->
  {name.ok(n) == True{} : Bool}:
  %Equal.sym(Bytes(), n, k, e) : {name.ok(_) == True{} : Bool}
  g

def name.at(b: Bool, +n: Bytes(), +k: Bytes(), -t: List<&2, Bytes()>, eb: {String.eq(n, k) == b : Bool},
  h: {Http.known.at(b, u => Http.known.has(n, t)) == True{} : Bool}, g: {name.ok(k) == True{} : Bool},
  ih: {Http.known.has(n, t) == True{} : Bool} -> {name.ok(n) == True{} : Bool}) -> {name.ok(n) == True{} : Bool}:
  match b:
    case True{}:
      name.hit(n, k, str.eq(n, k, eb), g)
    case False{}:
      ih(h)

# a name the table knows is one rvalid takes
def name.sound(ks: List<&2, Bytes()>, +n: Bytes(), +all: {names.all(ks) == True{} : Bool},
  h: {Http.known.has(n, ks) == True{} : Bool}) -> {name.ok(n) == True{} : Bool}:
  match ks:
    case Nil{}:
      Bool.no({name.ok(n) == True{} : Bool}, h)
    case Con{+k, +t}:
      name.at(String.eq(n, k), n, k, t, {==}, h, Bool.and_l(name.ok(k), names.all(t), all),
        hr => name.sound(t, n, Bool.and_r(name.ok(k), names.all(t), all), hr))

# a value of space and visible ASCII, by one scan, is one rvalid takes
def val.sound(+v: Bytes(), h: {X.all.in(v, 32, 127) == True{} : Bool}) -> {X.rok.all(RS.TVal{}, v) == True{} : Bool}:
  %Equal.sym(Bool, X.all.in(v, 32, 127), True{}, h) : {X.rok.all.at(_, RS.TVal{}, v) == True{} : Bool}
  {==}

def fields.sound(fs: List<&2, Wr.Field>, +h: {Http.fields.fast(fs) == True{} : Bool}) ->
  {X.rok.fields(fs) == True{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case Con{f, +t}:
      match f:
        case Wr.Field{+n, +v}:
          +hnv = Bool.and_l(Bool.and(Http.known.has(n, Http.known()), X.all.in(v, 32, 127)), Http.fields.fast(t), h)
          tt(X.rok.field(Wr.Field{n, v}), X.rok.fields(t),
            tt(name.ok(n), X.rok.all(RS.TVal{}, v),
              name.sound(Http.known(), n, names.known(), Bool.and_l(Http.known.has(n, Http.known()), X.all.in(v, 32, 127), hnv)),
              val.sound(v, Bool.and_r(Http.known.has(n, Http.known()), X.all.in(v, 32, 127), hnv))),
            fields.sound(t, Bool.and_r(Bool.and(Http.known.has(n, Http.known()), X.all.in(v, 32, 127)), Http.fields.fast(t), h)))

# The length's walk reads what RS.len.view reads. lv.g is len.run with
# the digits' value started at acc: a digit pushed onto a span is one
# step of the value, a blank pushed onto one changes nothing len.view
# reads, and each walk, a byte at a time, is the spec's over the list.
def lv.g(+e: R.Ask, sp: RS.Span, +acc: U32) -> RS.FLine:
  match sp:
    case RS.Span{d, s}:
      RS.len.digits(RS.len.num.go(e, d, acc), s)

def lv.push(+e: R.Ask, +x: U32, sp: RS.Span, +acc: U32) ->
  {lv.g(e, RS.span.push(x, sp), acc) == lv.g(e, sp, Http.lv.num(e, acc, x)) : RS.FLine}:
  match sp:
    case RS.Span{d, s}:
      {==}

def lv.run(+e: R.Ask, sp: RS.Span) -> {RS.len.run(e, sp) == lv.g(e, sp, 0) : RS.FLine}:
  match sp:
    case RS.Span{d, s}:
      {==}

def lv.dig.step(+b: Bool, +e: R.Ask, +x: U32, +w: Bytes(), +acc: U32,
  ih: {Http.lv.dig(e, w, Http.lv.num(e, acc, x)) ==
    lv.g(e, RS.span(RS.TDig{}, Bytes.to_list(w)), Http.lv.num(e, acc, x)) : RS.FLine}) ->
  {Http.lv.dig.at(b, acc, R.cls(x), x, w, Http.lv.dig(e, w, Http.lv.num(e, acc, x))) ==
    lv.g(e, RS.span.pick(b, R.cls(x), x, Bytes.to_list(w), RS.span(RS.TDig{}, Bytes.to_list(w))), acc) : RS.FLine}:
  match b:
    case True{}:
      Equal.trans(RS.FLine, Http.lv.dig(e, w, Http.lv.num(e, acc, x)),
        lv.g(e, RS.span(RS.TDig{}, Bytes.to_list(w)), Http.lv.num(e, acc, x)),
        lv.g(e, RS.span.push(x, RS.span(RS.TDig{}, Bytes.to_list(w))), acc), ih,
        Equal.sym(RS.FLine, lv.g(e, RS.span.push(x, RS.span(RS.TDig{}, Bytes.to_list(w))), acc),
          lv.g(e, RS.span(RS.TDig{}, Bytes.to_list(w)), Http.lv.num(e, acc, x)),
          lv.push(e, x, RS.span(RS.TDig{}, Bytes.to_list(w)), acc)))
    case False{}:
      {==}

def lv.dig.eq(+e: R.Ask, +v: Bytes(), +acc: U32) ->
  {Http.lv.dig(e, v, acc) == lv.g(e, RS.span(RS.TDig{}, Bytes.to_list(v)), acc) : RS.FLine}:
  match v:
    case SNil{}:
      {==}
    case SCon{+h, +w}:
      match h:
        case Chr{+x}:
          lv.dig.step(RS.allows(RS.TDig{}, R.cls(x)), e, x, w, acc, lv.dig.eq(e, w, Http.lv.num(e, acc, x)))

def lv.vpush(+e: R.Ask, +x: U32, sp: RS.Span) -> {RS.len.view(e, RS.span.push(x, sp)) == RS.len.view(e, sp) : RS.FLine}:
  match sp:
    case RS.Span{r, s}:
      match s:
        case RS.SEnd{}:
          {==}
        case RS.SAt{k, c, rest}:
          match k:
            case R.KSp{}:
              {==}
            case R.KHt{}:
              {==}
            case R.KCr{}:
              {==}
            case R.KLf{}:
              {==}
            case R.KCo{}:
              {==}
            case R.KCm{}:
              {==}
            case R.KDg{}:
              {==}
            case R.KTk{}:
              {==}
            case R.KVc{}:
              {==}
            case R.KCt{}:
              {==}

def lv.stop.eq(+e: R.Ask, +k: R.Cls, +x: U32, +w: Bytes()) ->
  {Http.lv.stop(e, k, x, w) == RS.len.view(e, RS.Span{Nil{}, RS.SAt{k, x, Bytes.to_list(w)}}) : RS.FLine}:
  match k:
    case R.KDg{}:
      +sp = RS.span(RS.TDig{}, Bytes.to_list(w))
      Equal.trans(RS.FLine, Http.lv.dig(e, w, Http.lv.num(e, 0, x)), lv.g(e, sp, Http.lv.num(e, 0, x)),
        RS.len.run(e, RS.span.push(x, sp)), lv.dig.eq(e, w, Http.lv.num(e, 0, x)),
        Equal.trans(RS.FLine, lv.g(e, sp, Http.lv.num(e, 0, x)), lv.g(e, RS.span.push(x, sp), 0),
          RS.len.run(e, RS.span.push(x, sp)),
          Equal.sym(RS.FLine, lv.g(e, RS.span.push(x, sp), 0), lv.g(e, sp, Http.lv.num(e, 0, x)), lv.push(e, x, sp, 0)),
          Equal.sym(RS.FLine, RS.len.run(e, RS.span.push(x, sp)), lv.g(e, RS.span.push(x, sp), 0),
            lv.run(e, RS.span.push(x, sp)))))
    case R.KSp{}:
      {==}
    case R.KHt{}:
      {==}
    case R.KCr{}:
      {==}
    case R.KLf{}:
      {==}
    case R.KCo{}:
      {==}
    case R.KCm{}:
      {==}
    case R.KTk{}:
      {==}
    case R.KVc{}:
      {==}
    case R.KCt{}:
      {==}

def lv.ows.step(+b: Bool, +e: R.Ask, +x: U32, +w: Bytes(),
  ih: {Http.lv.ows(e, w) == RS.len.view(e, RS.span(RS.TOws{}, Bytes.to_list(w))) : RS.FLine}) ->
  {Http.lv.ows.at(b, e, R.cls(x), x, w, Http.lv.ows(e, w)) ==
    RS.len.view(e, RS.span.pick(b, R.cls(x), x, Bytes.to_list(w), RS.span(RS.TOws{}, Bytes.to_list(w)))) : RS.FLine}:
  match b:
    case True{}:
      Equal.trans(RS.FLine, Http.lv.ows(e, w), RS.len.view(e, RS.span(RS.TOws{}, Bytes.to_list(w))),
        RS.len.view(e, RS.span.push(x, RS.span(RS.TOws{}, Bytes.to_list(w)))), ih,
        Equal.sym(RS.FLine, RS.len.view(e, RS.span.push(x, RS.span(RS.TOws{}, Bytes.to_list(w)))),
          RS.len.view(e, RS.span(RS.TOws{}, Bytes.to_list(w))), lv.vpush(e, x, RS.span(RS.TOws{}, Bytes.to_list(w)))))
    case False{}:
      lv.stop.eq(e, R.cls(x), x, w)

def lv.ows.eq(+e: R.Ask, +v: Bytes()) ->
  {Http.lv.ows(e, v) == RS.len.view(e, RS.span(RS.TOws{}, Bytes.to_list(v))) : RS.FLine}:
  match v:
    case SNil{}:
      {==}
    case SCon{+h, +w}:
      match h:
        case Chr{+x}:
          lv.ows.step(RS.allows(RS.TOws{}, R.cls(x)), e, x, w, lv.ows.eq(e, w))

# the length's walk is rok.len, for every value
def len.fast.eq(+head: Bool, +bl: Bool, +clen: Bytes(), +body: Bytes()) ->
  {Http.len.fast(head, bl, clen, body) == X.rok.len(head, bl, clen, body) : Bool}:
  match clen:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      match c:
        case Chr{+x}:
          +d : Bytes() = SCon{Chr{x}, t}
          +sp = RS.span(RS.TOws{}, Bytes.to_list(d))
          %Equal.sym(RS.FLine, RS.len.view(X.rask(head), RS.span.push(32, sp)), RS.len.view(X.rask(head), sp),
              lv.vpush(X.rask(head), 32, sp)) :
            {Bool.and(X.rok.all(RS.TVal{}, d), X.rok.len.at(Http.lv.ows(X.rask(head), d), bl, body)) ==
              Bool.and(X.rok.all(RS.TVal{}, d), X.rok.len.at(_, bl, body)) : Bool}
          %lv.ows.eq(X.rask(head), d) :
            {Bool.and(X.rok.all(RS.TVal{}, d), X.rok.len.at(Http.lv.ows(X.rask(head), d), bl, body)) ==
              Bool.and(X.rok.all(RS.TVal{}, d), X.rok.len.at(_, bl, body)) : Bool}
          {==}

def len.sound(+head: Bool, +bl: Bool, +cl: Bytes(), +body: Bytes(),
  h: {Http.len.fast(head, bl, cl, body) == True{} : Bool}) -> {X.rok.len(head, bl, cl, body) == True{} : Bool}:
  %len.fast.eq(head, bl, cl, body) : {_ == True{} : Bool}
  h

# fast.sound: the fast check passes only where rvalid does
def fast.sound(+head: Bool, +code: U32, h: X.RHead, +body: Bytes(), +f: {Http.enc.fast(head, code, h, body) == True{} : Bool}) ->
  {X.rvalid(head, code, X.rsp.fin(head, code, h, body)) == True{} : Bool}:
  match h:
    case X.RHead{+cd, +why, +fs, +hl}:
      +bl = X.rbodyless(head, code)
      +cl = X.rclen(head, bl, hl, body)
      +a = Http.st.in(Http.statuses(), code, cd, why)
      +b = Http.fields.fast(fs)
      +c = Http.len.fast(head, bl, cl, body)
      +ab = Bool.and_l(Bool.and(a, b), c, f)
      tt(Bool.and(Bool.and(X.rok.code(cd, code), X.rok.all(RS.TVal{}, why)), X.rok.fields(fs)),
        X.rok.len(head, bl, cl, body),
        tt(Bool.and(X.rok.code(cd, code), X.rok.all(RS.TVal{}, why)), X.rok.fields(fs),
          st.sound(Http.statuses(), code, cd, why, st.known(), Bool.and_l(a, b, ab)),
          fields.sound(fs, Bool.and_r(a, b, ab))),
        len.sound(head, bl, cl, body, Bool.and_r(Bool.and(a, b), c, f)))

def check.at(fv: Bool, +head: Bool, +code: U32, +h: X.RHead, +body: Bytes(),
  ef: {Http.enc.fast(head, code, h, body) == fv : Bool},
  e: {Http.enc.check.at(fv, head, code, h, body) == True{} : Bool}) ->
  {X.rvalid(head, code, X.rsp.fin(head, code, h, body)) == True{} : Bool}:
  match fv:
    case True{}:
      fast.sound(head, code, h, body, ef)
    case False{}:
      e

# the check passes only where rvalid does
def check.sound(+head: Bool, +code: U32, +h: X.RHead, +body: Bytes(),
  e: {Http.enc.check(head, code, h, body) == True{} : Bool}) ->
  {X.rvalid(head, code, X.rsp.fin(head, code, h, body)) == True{} : Bool}:
  check.at(Http.enc.fast(head, code, h, body), head, code, h, body, {==}, e)

# the 500 passes rvalid, to HEAD and to anything else
def e500.ok(head: Bool) -> {X.rvalid(head, 500, X.rsp.fin(head, 500, Http.e500.head(), Http.e500.body())) == True{} : Bool}:
  match head:
    case True{}:
      {==}
    case False{}:
      {==}

def resp.pick(ok: Bool, +head: Bool, +closing: Bool, +v10: Bool, +code: U32, +h: X.RHead, +body: Bytes(),
  e: {Http.enc.check(head, code, h, body) == ok : Bool}) ->
  {RS.response(X.rask(head), Bytes.to_list(Http.enc.pick(ok, head, code, h, body, closing, v10))) ==
    Laws.sent(head, closing, code, ok, body) : R.Look}:
  match ok:
    case True{}:
      PP.rr.h(h, head, code, body, closing, v10, check.sound(head, code, h, body, e))
    case False{}:
      PP.rr.h(Http.e500.head(), head, 500, Http.e500.body(), closing, v10, e500.ok(head))

def Laws.respond_framed(head, closing, v10, code, hs, body):
  resp.pick(Http.enc.check(head, code, Http.rhead(code, hs, body), body), head, closing, v10, code,
    Http.rhead(code, hs, body), body, {==})

# The router
# ==========

def mem.eq(+m: Bytes(), ms: List<&2, Bytes()>) -> {Server.mem(m, ms) == Laws.spec.mem(m, ms) : Bool}:
  match ms:
    case Nil{}:
      {==}
    case Con{+x, t}:
      Equal.cong(Bool, Bool, b => Bool.or(String.eq(m, x), b), Server.mem(m, t), Laws.spec.mem(m, t), mem.eq(m, t))

# union over a concatenation is one union after the other
def union.app(xs: List<&2, Bytes()>, -ys: List<&2, Bytes()>, +acc: List<&2, Bytes()>) ->
  {Server.union(List.append(&2, Bytes(), xs, ys), acc) == Server.union(ys, Server.union(xs, acc)) : List<&2, Bytes()>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, t}:
      union.app(t, ys, Server.union.put(Server.mem(x, acc), x, acc))

def un.at(b: Bool, +x: Bytes(), +acc: List<&2, Bytes()>, -t: List<&2, Bytes()>,
  ih: @+a2: List<&2, Bytes()> -> {Server.union(t, a2) == List.append(&2, Bytes(), a2, Laws.spec.nub.go(t, a2)) : List<&2, Bytes()>}) ->
  {Server.union(t, Server.union.put(b, x, acc)) ==
    List.append(&2, Bytes(), acc, Laws.spec.nub.at(b, x, acc, sn => Laws.spec.nub.go(t, sn))) : List<&2, Bytes()>}:
  match b:
    case True{}:
      ih(acc)
    case False{}:
      +a2 = List.append(&2, Bytes(), acc, [x])
      Equal.trans(List<&2, Bytes()>, Server.union(t, a2), List.append(&2, Bytes(), a2, Laws.spec.nub.go(t, a2)),
        List.append(&2, Bytes(), acc, Con{x, Laws.spec.nub.go(t, a2)}), ih(a2),
        PP.app.assoc(Bytes(), acc, [x], Laws.spec.nub.go(t, a2)))

# union, started from acc, is acc and then the methods acc has not, each
# once, as nub has them
def union.nub(xs: List<&2, Bytes()>, +acc: List<&2, Bytes()>) ->
  {Server.union(xs, acc) == List.append(&2, Bytes(), acc, Laws.spec.nub.go(xs, acc)) : List<&2, Bytes()>}:
  match xs:
    case Nil{}:
      Equal.sym(List<&2, Bytes()>, List.append(&2, Bytes(), acc, Nil{}), acc, PP.app.nil(Bytes(), acc))
    case Con{+x, t}:
      %mem.eq(x, acc) :
        {Server.union(t, Server.union.put(Server.mem(x, acc), x, acc)) ==
          List.append(&2, Bytes(), acc, Laws.spec.nub.at(_, x, acc, sn => Laws.spec.nub.go(t, sn))) : List<&2, Bytes()>}
      un.at(Server.mem(x, acc), x, acc, t, a2 => union.nub(t, a2))

def pk.at(mm: Maybe<&2, List<&2, Http.Header>>, hb: Bool, +i: Nat, +ms: List<&2, Bytes()>, +acc: List<&2, Bytes()>,
  -go: List<&2, Bytes()> -> Server.Pick, -h: Maybe<&2, Server.Pick>, -a: List<&2, Bytes()>,
  ih: @+al: List<&2, Bytes()> -> {go(al) == Laws.spec.pick.end(h, Server.union(a, al)) : Server.Pick}) ->
  {Server.pick.at(mm, hb, i, ms, acc, go) ==
    Laws.spec.pick.end(Laws.spec.hit.at(mm, hb, i, h), Server.union(Laws.spec.allow.at(mm, ms, a), acc)) : Server.Pick}:
  match mm:
    case None{}:
      ih(acc)
    case Some{ps}:
      match hb:
        case True{}:
          {==}
        case False{}:
          Equal.trans(Server.Pick, go(Server.union(ms, acc)), Laws.spec.pick.end(h, Server.union(a, Server.union(ms, acc))),
            Laws.spec.pick.end(h, Server.union(List.append(&2, Bytes(), ms, a), acc)), ih(Server.union(ms, acc)),
            Equal.cong(List<&2, Bytes()>, Server.Pick, u => Laws.spec.pick.end(h, u), Server.union(a, Server.union(ms, acc)),
              Server.union(List.append(&2, Bytes(), ms, a), acc),
              Equal.sym(List<&2, Bytes()>, Server.union(List.append(&2, Bytes(), ms, a), acc),
                Server.union(a, Server.union(ms, acc)), union.app(ms, a, acc))))

# the router's one walk is the reference, from any route i and any
# methods gathered so far
def pick.eq(pats: List<&2, Server.Pat>, +m: Bytes(), +xs: List<&2, Bytes()>, +i: Nat, +acc: List<&2, Bytes()>) ->
  {Server.pick.go(pats, m, xs, i, acc) ==
    Laws.spec.pick.end(Laws.spec.hit(pats, m, xs, i), Server.union(Laws.spec.allow(pats, xs), acc)) : Server.Pick}:
  match pats:
    case Nil{}:
      match acc:
        case Nil{}:
          {==}
        case Con{a, t}:
          {==}
    case Con{p, t}:
      match p:
        case Server.Pat{+ms, +pat}:
          %mem.eq(m, ms) :
            {Server.pick.go(Con{Server.Pat{ms, pat}, t}, m, xs, i, acc) ==
              Laws.spec.pick.end(Laws.spec.hit.at(Server.matches(pat, xs), _, i, Laws.spec.hit(t, m, xs, 1n+i)),
                Server.union(Laws.spec.allow.at(Server.matches(pat, xs), ms, Laws.spec.allow(t, xs)), acc)) : Server.Pick}
          pk.at(Server.matches(pat, xs), Server.mem(m, ms), i, ms, acc, al => Server.pick.go(t, m, xs, 1n+i, al),
            Laws.spec.hit(t, m, xs, 1n+i), Laws.spec.allow(t, xs), al => pick.eq(t, m, xs, 1n+i, al))

def Laws.route_first(pats, m, path):
  +xs = Server.segs(path)
  +a = Laws.spec.allow(pats, xs)
  +h = Laws.spec.hit(pats, m, xs, 0n)
  Equal.trans(Server.Pick, Server.pick.go(pats, m, xs, 0n, Nil{}), Laws.spec.pick.end(h, Server.union(a, Nil{})),
    Laws.spec.pick.end(h, Laws.spec.nub(a)), pick.eq(pats, m, xs, 0n, Nil{}),
    Equal.cong(List<&2, Bytes()>, Server.Pick, u => Laws.spec.pick.end(h, u), Server.union(a, Nil{}), Laws.spec.nub(a),
      union.nub(a, Nil{})))

# Redirects
# =========

# what follow hands on is clean, or nothing
def f.ok(+orig: Bytes(), m: Maybe<&2, Client.IReq>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{r}:
      Laws.clean(orig, r)

# a field kept or dropped by keep with strip on: no credential comes out
def sk(+n: Bytes(), +v: Bytes(), c: Bool, e: {Laws.spec.cred(n) == c : Bool}, d2: Bool, rest: List<&2, Http.Header>,
  ih: {Laws.spec.no.creds(rest) == True{} : Bool}) ->
  {Laws.spec.no.creds(Client.keep.put(Bool.and(Bool.not(c), d2), Http.Header{n, v}, rest)) == True{} : Bool}:
  match c:
    case True{}:
      ih
    case False{}:
      match d2:
        case False{}:
          ih
        case True{}:
          %Equal.sym(Bool, Laws.spec.cred(n), False{}, e) :
            {Bool.and(Bool.not(_), Laws.spec.no.creds(rest)) == True{} : Bool}
          ih

def strip.ok(+d: Bool, hs: List<&2, Http.Header>) -> {Laws.spec.no.creds(Client.keep(True{}, d, hs)) == True{} : Bool}:
  match hs:
    case Nil{}:
      {==}
    case Con{h, +t}:
      match h:
        case Http.Header{+n, +v}:
          sk(n, v, Client.cred(n), {==}, Bool.not(Bool.and(d, Bool.or(String.eq(n, "content-type"), String.eq(n, "content-length")))),
            Client.keep(True{}, d, t), strip.ok(d, t))

def to.at(b: Bool, +d: Bool, hs: List<&2, Http.Header>) ->
  {Bool.or(b, Laws.spec.no.creds(Client.keep(Bool.not(b), d, hs))) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      strip.ok(d, hs)

def to.ok(+orig: Bytes(), +m: Bytes(), +m2: Bytes(), hs: List<&2, Http.Header>, body: Bytes(), +u2: U.Url) ->
  {Laws.clean(orig, Client.follow.to(orig, m, m2, hs, body, u2)) == True{} : Bool}:
  to.at(String.eq(U.origin(u2), orig), Bool.not(String.eq(m, m2)), hs)

def fat.ok(+orig: Bytes(), +s: U32, r: Result<&2, &2, Bytes(), U.Url>, rq: Client.IReq) ->
  {f.ok(orig, Client.follow.at(orig, s, r, rq)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{u2}:
      match rq:
        case Client.IReq{+m, u, hs, body}:
          to.ok(orig, m, Client.method.next(s, m), hs, body, u2)

def floc.ok(+orig: Bytes(), +s: U32, loc: Maybe<&2, Bytes()>, rq: Client.IReq) ->
  {f.ok(orig, Client.follow.loc(orig, s, loc, rq)) == True{} : Bool}:
  match loc:
    case None{}:
      {==}
    case Some{l}:
      match rq:
        case Client.IReq{m, +u, hs, body}:
          fat.ok(orig, s, U.resolve(u, l), Client.IReq{m, u, hs, body})

def fgo.ok(+orig: Bytes(), rq: Client.IReq, redir: Bool, +s: U32, loc: Maybe<&2, Bytes()>) ->
  {f.ok(orig, Client.follow.go(orig, rq, redir, s, loc)) == True{} : Bool}:
  match redir:
    case True{}:
      floc.ok(orig, s, loc, rq)
    case False{}:
      {==}

# every request a redirect sends the client on to is clean for the
# first origin: it goes there, or it carries no credential
def fclean(+orig: Bytes(), rq: Client.IReq, resp: Http.Response) -> {f.ok(orig, Client.follow(orig, rq, resp)) == True{} : Bool}:
  match resp:
    case Http.Response{+s, hs, b}:
      fgo.ok(orig, rq, Client.redirecting(s), s, Http.get(hs, "location"))

# the scripted peer after a chain: never asked for one more, never sent
# a request that was not clean
def Ok2(s: Laws.Script) -> Type:
  {Laws.sc.over(s) == False{} : Bool} & {Laws.sc.leak(s) == False{} : Bool}

def Cont(+orig: Bytes(), +n: Nat, -again: Laws.Script -> Client.IReq -> W.Id(Laws.Script & Client.Res())) -> Type:
  @+t2: List<&2, Client.Res()> -> @+rq2: Client.IReq -> @c2: {Laws.clean(orig, rq2) == True{} : Bool} ->
    Ok2(Pair.fst(Laws.Script, Client.Res(), again(Laws.Script{t2, n, False{}, orig, False{}}, rq2)))

def next.ok(+orig: Bytes(), m: Maybe<&2, Client.IReq>, fm: {f.ok(orig, m) == True{} : Bool}, resp: Http.Response,
  t: List<&2, Client.Res()>, +n: Nat, -again: Laws.Script -> Client.IReq -> W.Id(Laws.Script & Client.Res()),
  ag: Cont(orig, n, again)) ->
  Ok2(Pair.fst(Laws.Script, Client.Res(),
    Client.chain.next(~W.Id, ~W.Id.pure, ~Laws.Script, m, resp, Laws.Script{t, n, False{}, orig, False{}}, again))):
  match m:
    case None{}:
      ({==}, {==})
    case Some{rq2}:
      ag(t, rq2, fm)

def on.ok(+orig: Bytes(), +rq: Client.IReq, t: List<&2, Client.Res()>, +n: Nat, r: Client.Res(),
  -again: Laws.Script -> Client.IReq -> W.Id(Laws.Script & Client.Res()), ag: Cont(orig, n, again)) ->
  Ok2(Pair.fst(Laws.Script, Client.Res(),
    Client.chain.on(~W.Id, ~W.Id.pure, ~Laws.Script, orig, rq, (Laws.Script{t, n, False{}, orig, False{}}, r), again))):
  match r:
    case Fail{e}:
      ({==}, {==})
    case Done{+resp}:
      next.ok(orig, Client.follow(orig, rq, resp), fclean(orig, rq, resp), resp, t, n, again, ag)

def pop.ok(+orig: Bytes(), +rq: Client.IReq, ans: List<&2, Client.Res()>, +n: Nat,
  -again: Laws.Script -> Client.IReq -> W.Id(Laws.Script & Client.Res()), ag: Cont(orig, n, again)) ->
  Ok2(Pair.fst(Laws.Script, Client.Res(),
    Client.chain.on(~W.Id, ~W.Id.pure, ~Laws.Script, orig, rq, Laws.sc.pop(ans, (n, False{}), orig, False{}), again))):
  match ans:
    case Nil{}:
      ({==}, {==})
    case Con{r, t}:
      on.ok(orig, rq, t, n, r, again, ag)

# the peer after a send: one fewer request left, and no leak, the
# request being clean
def send.ok(ans: List<&2, Client.Res()>, +n: Nat, +orig: Bytes(), +rq: Client.IReq, c: {Laws.clean(orig, rq) == True{} : Bool}) ->
  {Laws.sc.pop(ans, (n, False{}), orig, False{}) == Laws.sc.send(Laws.Script{ans, 1n+n, False{}, orig, False{}}, rq) :
    Laws.Script & Client.Res()}:
  %Equal.sym(Bool, Laws.clean(orig, rq), True{}, c) :
    {Laws.sc.pop(ans, (n, False{}), orig, False{}) == Laws.sc.pop(ans, (n, False{}), orig, Bool.or(False{}, Bool.not(_))) :
      Laws.Script & Client.Res()}
  {==}

def at.ok(+orig: Bytes(), +rq: Client.IReq, ans: List<&2, Client.Res()>, +n: Nat, -sr: Laws.Script & Client.Res(),
  e: {Laws.sc.pop(ans, (n, False{}), orig, False{}) == sr : Laws.Script & Client.Res()},
  -again: Laws.Script -> Client.IReq -> W.Id(Laws.Script & Client.Res()), ag: Cont(orig, n, again)) ->
  Ok2(Pair.fst(Laws.Script, Client.Res(), Client.chain.on(~W.Id, ~W.Id.pure, ~Laws.Script, orig, rq, sr, again))):
  %e : Ok2(Pair.fst(Laws.Script, Client.Res(), Client.chain.on(~W.Id, ~W.Id.pure, ~Laws.Script, orig, rq, _, again)))
  pop.ok(orig, rq, ans, n, again, ag)

# the chain from a peer that may take k + 1 more requests, and a clean
# request: the peer is never asked for one more, and nothing leaks
def chain.ok(k: Nat) -> @+orig: Bytes() -> @+rq: Client.IReq -> @+ans: List<&2, Client.Res()> ->
  @c: {Laws.clean(orig, rq) == True{} : Bool} ->
  Ok2(Pair.fst(Laws.Script, Client.Res(), Laws.sim.chain(k, orig, rq, Laws.Script{ans, 1n+k, False{}, orig, False{}}))):
  match k:
    case 0n:
      +orig => +rq => +ans => c =>
        at.ok(orig, rq, ans, 0n, Laws.sc.send(Laws.Script{ans, 1n+0n, False{}, orig, False{}}, rq),
          send.ok(ans, 0n, orig, rq, c), s2 => rq2 => W.Id.pure(Laws.Script & Client.Res(), (s2, Fail{Client.TooManyRedirects{}})),
          t2 => rq2 => c2 => ({==}, {==}))
    case 1n+(+j):
      +orig => +rq => +ans => c =>
        at.ok(orig, rq, ans, 1n+j, Laws.sc.send(Laws.Script{ans, 1n+(1n+j), False{}, orig, False{}}, rq),
          send.ok(ans, 1n+j, orig, rq, c),
          s2 => rq2 => Client.chain(~W.Id, ~W.Id.pure, ~W.Id.bind, ~Laws.Script, ~Laws.sc.send, j, orig, rq2, s2),
          t2 => rq2 => c2 => chain.ok(j)(orig, rq2, t2, c2))

# the cap alone, for any request: a peer allowed k + 1 more is never
# asked for one more, whatever it has seen leak
def Cont1(+orig: Bytes(), +n: Nat, -again: Laws.Script -> Client.IReq -> W.Id(Laws.Script & Client.Res())) -> Type:
  @+t2: List<&2, Client.Res()> -> @+rq2: Client.IReq -> @+lk2: Bool ->
    {Laws.sc.over(Pair.fst(Laws.Script, Client.Res(), again(Laws.Script{t2, n, False{}, orig, lk2}, rq2))) == False{} : Bool}

def next1(+orig: Bytes(), m: Maybe<&2, Client.IReq>, resp: Http.Response, t: List<&2, Client.Res()>, +n: Nat, +lk: Bool,
  -again: Laws.Script -> Client.IReq -> W.Id(Laws.Script & Client.Res()), ag: Cont1(orig, n, again)) ->
  {Laws.sc.over(Pair.fst(Laws.Script, Client.Res(),
    Client.chain.next(~W.Id, ~W.Id.pure, ~Laws.Script, m, resp, Laws.Script{t, n, False{}, orig, lk}, again))) == False{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{rq2}:
      ag(t, rq2, lk)

def on1(+orig: Bytes(), +rq: Client.IReq, t: List<&2, Client.Res()>, +n: Nat, +lk: Bool, r: Client.Res(),
  -again: Laws.Script -> Client.IReq -> W.Id(Laws.Script & Client.Res()), ag: Cont1(orig, n, again)) ->
  {Laws.sc.over(Pair.fst(Laws.Script, Client.Res(),
    Client.chain.on(~W.Id, ~W.Id.pure, ~Laws.Script, orig, rq, (Laws.Script{t, n, False{}, orig, lk}, r), again))) == False{} :
    Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{+resp}:
      next1(orig, Client.follow(orig, rq, resp), resp, t, n, lk, again, ag)

def pop1(+orig: Bytes(), +rq: Client.IReq, ans: List<&2, Client.Res()>, +n: Nat, +lk: Bool,
  -again: Laws.Script -> Client.IReq -> W.Id(Laws.Script & Client.Res()), ag: Cont1(orig, n, again)) ->
  {Laws.sc.over(Pair.fst(Laws.Script, Client.Res(),
    Client.chain.on(~W.Id, ~W.Id.pure, ~Laws.Script, orig, rq, Laws.sc.pop(ans, (n, False{}), orig, lk), again))) == False{} :
    Bool}:
  match ans:
    case Nil{}:
      {==}
    case Con{r, t}:
      on1(orig, rq, t, n, lk, r, again, ag)

def cap.ok(k: Nat) -> @+orig: Bytes() -> @+rq: Client.IReq -> @+ans: List<&2, Client.Res()> -> @+lk: Bool ->
  {Laws.sc.over(Pair.fst(Laws.Script, Client.Res(), Laws.sim.chain(k, orig, rq, Laws.Script{ans, 1n+k, False{}, orig, lk}))) ==
    False{} : Bool}:
  match k:
    case 0n:
      +orig => +rq => +ans => +lk =>
        pop1(orig, rq, ans, 0n, Bool.or(lk, Bool.not(Laws.clean(orig, rq))),
          s2 => rq2 => W.Id.pure(Laws.Script & Client.Res(), (s2, Fail{Client.TooManyRedirects{}})), t2 => rq2 => lk2 => {==})
    case 1n+(+j):
      +orig => +rq => +ans => +lk =>
        pop1(orig, rq, ans, 1n+j, Bool.or(lk, Bool.not(Laws.clean(orig, rq))),
          s2 => rq2 => Client.chain(~W.Id, ~W.Id.pure, ~W.Id.bind, ~Laws.Script, ~Laws.sc.send, j, orig, rq2, s2),
          t2 => rq2 => lk2 => cap.ok(j)(orig, rq2, t2, lk2))

def Laws.redirect_cap(k, orig, rq, ans):
  cap.ok(k)(orig, rq, ans, False{})

def Laws.redirect_creds(k, orig, rq, ans, c):
  Pair.snd({Laws.sc.over(Pair.fst(Laws.Script, Client.Res(),
    Laws.sim.chain(k, orig, rq, Laws.Script{ans, 1n+k, False{}, orig, False{}}))) == False{} : Bool},
    {Laws.sc.leak(Pair.fst(Laws.Script, Client.Res(),
    Laws.sim.chain(k, orig, rq, Laws.Script{ans, 1n+k, False{}, orig, False{}}))) == False{} : Bool},
    chain.ok(k)(orig, rq, ans, c))

# Streamed bodies
# ===============
#
# stream_body is four known steps: Stream.drain is the kit's drain at
# the reader's hooks (sd, by induction on the reads), whose chunks put
# back are the reader fed the reads in turn (wire/http1's drain_reads),
# which is the reader fed them joined (reads_split) a byte at a time
# (feed_buf_is_feed), which from the body's entry is the spec's walk
# from the same place (wire/http1/PROOF.bend's walk.lem, the simulation
# resp_sim is made of: Stream.entry is the reader where emb puts the
# walk entered at the body). stream_next follows: what follows the body
# is the same with the chunks put back or not (ng). stream_bounded: a
# take leaves the reader holding no body byte (take2), and the rest is
# what fits checked.

def sd.on(q: R.P & Bytes(), +acc: Bytes(), +e: R.Ask, -t: List<&2, Bytes()>,
  ih: @p: R.P -> @+a: Bytes() ->
    {Stream.drain(e, t, p, a) == Wr.drain(~R.Ask, ~R.P, ~R.wstep, ~R.wadv, ~R.take, e, t, p, a) : R.P & Bytes()}) ->
  {Wr.drain.on(R.P, q, acc, p => a => Stream.drain(e, t, p, a)) ==
    Wr.drain.on(R.P, q, acc, p => a => Wr.drain(~R.Ask, ~R.P, ~R.wstep, ~R.wadv, ~R.take, e, t, p, a)) :
    R.P & Bytes()}:
  match q:
    case (p, +x):
      ih(p, Bytes.append(acc, x))

# a body's reads, as Stream.read steps them, are the kit's drain
def sd(+e: R.Ask, rs: List<&2, Bytes()>, p: R.P, +acc: Bytes()) ->
  {Stream.drain(e, rs, p, acc) == Wr.drain(~R.Ask, ~R.P, ~R.wstep, ~R.wadv, ~R.take, e, rs, p, acc) : R.P & Bytes()}:
  match rs:
    case Nil{}:
      {==}
    case Con{+r, t}:
      sd.on(Stream.step(e, r, p), acc, e, t, p2 => a2 => sd(e, t, p2, a2))

# the reader entered at the body is the spec's walk entered there
def entry.spec(+e: R.Ask, f: Stream.Frame, +bs: List<&2, U32>) ->
  {R.look(R.feed(e, bs, Stream.entry(e, f))) == Laws.spec.body(e, f, bs) : R.Look}:
  match f:
    case Stream.FLen{n}:
      match n:
        case 0n:
          HP.walk.lem(e, bs, RS.W{RS.MDone{RS.resp(R.body.head(), Nil{}, False{}), Nil{}}, Nil{}})(Unit{})
        case 1n+q:
          HP.walk.lem(e, bs, RS.W{RS.MBody{R.body.head(), q, Nil{}}, Nil{}})(Unit{})
    case Stream.FChunked{}:
      HP.walk.lem(e, bs, RS.W{RS.MChunk{R.body.head(), R.ASize0{}, 0, Nil{}, R.ask.cap(e)}, Nil{}})(Unit{})

def Laws.stream_body(e, f, rs):
  +p0 = Stream.entry(e, f)
  +bs = Bytes.concat(rs)
  -sq = Stream.drain(e, rs, p0, "")
  -wq = Wr.drain(~R.Ask, ~R.P, ~R.wstep, ~R.wadv, ~R.take, e, rs, p0, "")
  %Equal.sym(R.P & Bytes(), sq, wq, sd(e, rs, p0, "")) :
    {R.look(R.give(Wr.drain.b(R.P, _), Wr.drain.s(R.P, _))) == Laws.spec.body(e, f, Bytes.to_list(bs)) : R.Look}
  %Equal.sym(R.P, R.give(Wr.drain.b(R.P, wq), Wr.drain.s(R.P, wq)), R.reads(e, rs, p0), HL.drain_reads(e, rs, p0)) :
    {R.look(_) == Laws.spec.body(e, f, Bytes.to_list(bs)) : R.Look}
  %Equal.sym(R.P, R.reads(e, rs, p0), R.feed_buf(e, bs, p0), HL.reads_split(e, rs, p0)) :
    {R.look(_) == Laws.spec.body(e, f, Bytes.to_list(bs)) : R.Look}
  %Equal.sym(R.P, R.feed_buf(e, bs, p0), R.feed(e, Bytes.to_list(bs), p0), HL.feed_buf_is_feed(e, bs, p0)) :
    {R.look(_) == Laws.spec.body(e, f, Bytes.to_list(bs)) : R.Look}
  entry.spec(e, f, Bytes.to_list(bs))

# what follows the body is the same with bytes put back in front
def ng(+g: Bytes(), p: R.P) -> {Stream.next(R.give(g, p)) == Stream.next(p) : Maybe<&2, Bytes()>}:
  match p:
    case R.P{st, out}:
      match st:
        case R.Fin{r, x}:
          {==}
        case R.SVer{a, b}:
          {==}
        case R.SCode{v10, n, k}:
          {==}
        case R.SWhy{v10, code}:
          {==}
        case R.Eol{h}:
          {==}
        case R.Lin{h}:
          {==}
        case R.Nam{h, cl, te, co}:
          {==}
        case R.Oth{h}:
          {==}
        case R.Len0{h}:
          {==}
        case R.Len{h, n}:
          {==}
        case R.LenW{h, n}:
          {==}
        case R.Te0{h}:
          {==}
        case R.Te{h, m}:
          {==}
        case R.Conn{h, cl, ka, mc, mk}:
          {==}
        case R.Eoh{h}:
          {==}
        case R.Bod{h, more, got}:
          {==}
        case R.Chk{h, at, n, got, left}:
          {==}
        case R.Dat{h, more, got, left}:
          {==}
        case R.Clo{h, got, left}:
          {==}
        case R.Bad{}:
          {==}

def nx.spec(l: R.Look) -> {Stream.next.of(l) == Laws.spec.next(l) : Maybe<&2, Bytes()>}:
  match l:
    case R.Look{i, end}:
      match end:
        case R.Final{r, x}:
          {==}
        case R.Open{}:
          {==}
        case R.Refused{}:
          {==}
        case R.Closing{r}:
          {==}

def nx.at(+g: Bytes(), p: R.P, +l: R.Look, e: {R.look(R.give(g, p)) == l : R.Look}) ->
  {Stream.next(p) == Laws.spec.next(l) : Maybe<&2, Bytes()>}:
  Equal.trans(Maybe<&2, Bytes()>, Stream.next(p), Stream.next(R.give(g, p)), Laws.spec.next(l),
    Equal.sym(Maybe<&2, Bytes()>, Stream.next(R.give(g, p)), Stream.next(p), ng(g, p)),
    Equal.trans(Maybe<&2, Bytes()>, Stream.next(R.give(g, p)), Stream.next.of(l), Laws.spec.next(l),
      Equal.cong(R.Look, Maybe<&2, Bytes()>, x => Stream.next.of(x), R.look(R.give(g, p)), l, e),
      nx.spec(l)))

def Laws.stream_next(e, f, rs):
  nx.at(Wr.drain.b(R.P, Laws.streamed(e, f, rs)), Wr.drain.s(R.P, Laws.streamed(e, f, rs)),
    Laws.spec.body(e, f, Bytes.to_list(Bytes.concat(rs))), Laws.stream_body(e, f, rs))

# a take leaves the reader holding no byte of the body
def take2(z: R.P) -> {Wr.drain.b(R.P, R.take(Wr.drain.s(R.P, R.take(z)))) == "" : Bytes()}:
  match z:
    case R.P{st, out}:
      match st:
        case R.Fin{r, x}:
          match r:
            case R.Resp{c, v, cl, b}:
              {==}
        case R.SVer{a, b}:
          {==}
        case R.SCode{v10, n, k}:
          {==}
        case R.SWhy{v10, code}:
          {==}
        case R.Eol{h}:
          {==}
        case R.Lin{h}:
          {==}
        case R.Nam{h, cl, te, co}:
          {==}
        case R.Oth{h}:
          {==}
        case R.Len0{h}:
          {==}
        case R.Len{h, n}:
          {==}
        case R.LenW{h, n}:
          {==}
        case R.Te0{h}:
          {==}
        case R.Te{h, m}:
          {==}
        case R.Conn{h, cl, ka, mc, mk}:
          {==}
        case R.Eoh{h}:
          {==}
        case R.Bod{h, more, got}:
          {==}
        case R.Chk{h, at, n, got, left}:
          {==}
        case R.Dat{h, more, got, left}:
          {==}
        case R.Clo{h, got, left}:
          {==}
        case R.Bad{}:
          {==}

# what follows the body, as Stream.rest reads it and as the law spells it
def after.eq(p: R.P) -> {Laws.spec.after(p) == Stream.rest(p) : Bytes()}:
  match p:
    case R.P{st, out}:
      match st:
        case R.Fin{r, x}:
          {==}
        case R.SVer{a, b}:
          {==}
        case R.SCode{v10, n, k}:
          {==}
        case R.SWhy{v10, code}:
          {==}
        case R.Eol{h}:
          {==}
        case R.Lin{h}:
          {==}
        case R.Nam{h, cl, te, co}:
          {==}
        case R.Oth{h}:
          {==}
        case R.Len0{h}:
          {==}
        case R.Len{h, n}:
          {==}
        case R.LenW{h, n}:
          {==}
        case R.Te0{h}:
          {==}
        case R.Te{h, m}:
          {==}
        case R.Conn{h, cl, ka, mc, mk}:
          {==}
        case R.Eoh{h}:
          {==}
        case R.Bod{h, more, got}:
          {==}
        case R.Chk{h, at, n, got, left}:
          {==}
        case R.Dat{h, more, got, left}:
          {==}
        case R.Clo{h, got, left}:
          {==}
        case R.Bad{}:
          {==}

def bd.at(q: R.P & Bytes(), +n: Nat, h: {Wr.drain.b(R.P, R.take(Wr.drain.s(R.P, q))) == "" : Bytes()},
  ok: {Stream.fits(Wr.drain.s(R.P, q), Wr.drain.b(R.P, q), n) == True{} : Bool}) ->
  {Nat.is_le(Laws.spec.hold(Wr.drain.s(R.P, q), Wr.drain.b(R.P, q)), n) == True{} : Bool}:
  match q:
    case (+p, +x):
      %Equal.sym(Bytes(), Wr.drain.b(R.P, R.take(p)), "", h) :
        {Nat.is_le(Nat.add(Bytes.len(x), Nat.add(Bytes.len(_), Bytes.len(Laws.spec.after(p)))), n) == True{} : Bool}
      %Equal.sym(Bytes(), Laws.spec.after(p), Stream.rest(p), after.eq(p)) :
        {Nat.is_le(Nat.add(Bytes.len(x), Bytes.len(_)), n) == True{} : Bool}
      ok

def Laws.stream_bounded(e, bs, p, ok):
  bd.at(Stream.step(e, bs, p), Bytes.len(bs), take2(R.feed_buf(e, bs, p)), ok)

# A stream route's head
# =====================
#
# stream_head leans on the engine's own simulation (EP): the relation
# REL its frame_sim is made of holds after every byte (STEP), and says,
# for each place the walk can be, where the reader is. At a head's blank
# line (MEoh) the reader is at CrL with a pending head that looks like
# the walk's (PR); the request it makes is the walk's (REQ), and its
# Hosts and framing are (hok, bok). Everywhere else the relation names a
# state that is not CrL -- through the line lemmas for a request line or
# a field line in progress, and Dead for a refusal -- so neither side has
# a head.

# the relation, after every byte of an input
def sr.walk(bs: List<&2, U32>, +w: Spec.W, +p: Eng.P, s: EP.SR(p, w)) -> EP.SR(Eng.feed(bs, p), Spec.walk(bs, w)):
  match bs:
    case Nil{}:
      s
    case Con{+c, t}:
      (pd, r) = s
      sr.walk(t, Spec.next(w, c), Eng.step(p, c), EP.STEP(w, c, p, pd, r))

# a reader equal to one with no head has none
def by.p(+ip: Bytes(), -p: Eng.P, -x: Eng.P, -m: Maybe<&2, Stream.Head>, e: {p == x : Eng.P},
  g: {Stream.at.head(ip, x) == m : Maybe<&2, Stream.Head>}) -> {Stream.at.head(ip, p) == m : Maybe<&2, Stream.Head>}:
  Equal.trans(Maybe<&2, Stream.Head>, Stream.at.head(ip, p), Stream.at.head(ip, x), m,
    Equal.cong(Eng.P, Maybe<&2, Stream.Head>, y => Stream.at.head(ip, y), p, x, e), g)

def st.bad(-st: Eng.St, -pd: Eng.Pend, -o: List<&2, Eng.Req>, -out: List<&2, Eng.Req>,
  d: {Eng.P{st, Eng.pend.new(), o} == Eng.P{Eng.Bad{}, Eng.pend.new(), out} : Eng.P}) -> {st == Eng.Bad{} : Eng.St}:
  Equal.cong(Eng.P, Eng.St, y => EP.st.of(y), Eng.P{st, Eng.pend.new(), o}, Eng.P{Eng.Bad{}, Eng.pend.new(), out}, d)

def dead.st(+ip: Bytes(), st: Eng.St, +pd: Eng.Pend, e: {st == Eng.Bad{} : Eng.St}) ->
  {Stream.at.head.st(ip, st, pd) == None{} : Maybe<&2, Stream.Head>}:
  %Equal.sym(Eng.St, st, Eng.Bad{}, e) : {Stream.at.head.st(ip, _, pd) == None{} : Maybe<&2, Stream.Head>}
  {==}

# a refused reader has no head
def dead.none(+ip: Bytes(), q: Eng.P, -out: List<&2, Eng.Req>) -> EP.Dead(q, out) -> {Stream.at.head(ip, q) == None{} : Maybe<&2, Stream.Head>}:
  match q:
    case Eng.P{st, +pd, o}:
      d => dead.st(ip, st, pd, st.bad(st, pd, o, out, d))

# a request line in progress
def none.req(+ip: Bytes(), v: Spec.RLine, +q: Eng.P, -out: List<&2, Eng.Req>) -> EP.LR.req(q, v, out) -> {Stream.at.head(ip, q) == None{} : Maybe<&2, Stream.Head>}:
  match v:
    case Spec.RNone{}:
      lr => by.p(ip, q, Eng.P{Eng.Pre{}, Eng.pend.new(), out}, None{}, lr, {==})
    case Spec.RMeth{m}:
      lr => by.p(ip, q, Eng.P{Eng.InM{Bytes.from_list(m)}, Eng.pend.new(), out}, None{}, lr, {==})
    case Spec.RTarget{m, t}:
      lr => by.p(ip, q, Eng.P{Eng.InT{Bytes.from_list(t)}, EP.pd1(m), out}, None{}, lr, {==})
    case Spec.RVer{m, t, v}:
      lr => by.p(ip, q, Eng.P{Eng.InV{Bytes.from_list(v)}, EP.pd2(m, t), out}, None{}, lr, {==})
    case Spec.RBad{}:
      lr => dead.none(ip, q, out)(lr)

def none.len(+ip: Bytes(), ws: Bool, +q: Eng.P, -n: U32, -pd: Eng.Pend, -out: List<&2, Eng.Req>) ->
  EP.LR.len(q, n, ws, pd, out) -> {Stream.at.head(ip, q) == None{} : Maybe<&2, Stream.Head>}:
  match ws:
    case True{}:
      lr => by.p(ip, q, Eng.P{Eng.InLt{n}, pd, out}, None{}, lr, {==})
    case False{}:
      lr => by.p(ip, q, Eng.P{Eng.InL{n}, pd, out}, None{}, lr, {==})

# a field line's value in progress
def none.val(+ip: Bytes(), val: Spec.Val, +q: Eng.P, -pd: Eng.Pend, -out: List<&2, Eng.Req>) ->
  EP.LR.val(q, val, pd, out) -> {Stream.at.head(ip, q) == None{} : Maybe<&2, Stream.Head>}:
  match val:
    case Spec.VLen0{}:
      lr => by.p(ip, q, Eng.P{Eng.InL0{}, pd, out}, None{}, lr, {==})
    case Spec.VLen{n, ws}:
      lr => none.len(ip, ws, q, n, pd, out)(lr)
    case Spec.VConn{d, c}:
      lr => by.p(ip, q, Eng.P{Eng.InLc{EP.lowb(c), Spec.named("close", d), Spec.named("upgrade", d),
        Spec.named("keep-alive", d), Spec.lowall(d)}, pd, out}, None{}, lr, {==})
    case Spec.VUp{d, c}:
      lr => by.p(ip, q, Eng.P{Eng.InLu{EP.lowb(c), Spec.named("websocket", d)}, pd, out}, None{}, lr, {==})
    case Spec.VKey0{}:
      lr => by.p(ip, q, Eng.P{Eng.InLk0{}, pd, out}, None{}, lr, {==})
    case Spec.VKey{k}:
      lr => by.p(ip, q, Eng.P{Eng.InLk{Bytes.from_list(k)}, pd, out}, None{}, lr, {==})
    case Spec.VVer{v}:
      lr => by.p(ip, q, Eng.P{Eng.InLv{Bytes.from_list(v)}, pd, out}, None{}, lr, {==})
    case Spec.VTe0{}:
      lr => by.p(ip, q, Eng.P{Eng.InLe0{}, pd, out}, None{}, lr, {==})
    case Spec.VTe{t}:
      lr => by.p(ip, q, Eng.P{Eng.InLe{Bytes.from_list(t)}, pd, out}, None{}, lr, {==})
    case Spec.VHost{n, v}:
      lr => by.p(ip, q, Eng.P{Eng.InLx{Bytes.from_list(v)}, Eng.pend.nm(Eng.pend.host(pd), n), out}, None{}, lr, {==})
    case Spec.VSkip{n, v}:
      lr => by.p(ip, q, Eng.P{Eng.InLx{Bytes.from_list(v)}, Eng.pend.nm(pd, n), out}, None{}, lr, {==})

# a field line in progress
def none.field(+ip: Bytes(), v: Spec.FLine, +q: Eng.P, -pd: Eng.Pend, -out: List<&2, Eng.Req>) ->
  EP.LR.field(q, v, pd, out) -> {Stream.at.head(ip, q) == None{} : Maybe<&2, Stream.Head>}:
  match v:
    case Spec.FEmpty{}:
      lr => by.p(ip, q, Eng.P{Eng.Lin{}, pd, out}, None{}, lr, {==})
    case Spec.FName{n}:
      lr => by.p(ip, q, Eng.P{Eng.InN{Bytes.from_list(n)}, pd, out}, None{}, lr, {==})
    case Spec.FVal{val}:
      lr => none.val(ip, val, q, pd, out)(lr)
    case Spec.FBad{}:
      lr => dead.none(ip, q, out)(lr)

# The head at the blank line
# --------------------------

# the engine's framing decision, read off what the pending head holds
def hf.pv(x: EP.PV) -> Bool & Eng.Bd:
  match x:
    case EP.PV{m, p, cl, close, host, u, fx, hx}:
      match fx:
        case Eng.Fx{+v10, ka, te}:
          (Eng.hosts.ok(v10, host), Eng.body.kind(te, v10, cl))

def e.hf(pd: Eng.Pend) -> {Eng.head.frame(pd) == hf.pv(EP.pv(pd)) : Bool & Eng.Bd}:
  match pd:
    case Eng.Pend{m, p, cl, close, host, ws, fx, hx, nx}:
      match fx:
        case Eng.Fx{a, b, c}:
          {==}

# the engine's framing is the spec's, mapped
def fr.eq(ok: Bool, b: Spec.Body) -> {Stream.head.frame(ok, EP.bdv(b)) == Laws.spec.frame(ok, b) : Maybe<&2, Stream.Frame>}:
  match ok b:
    case False{} x:
      {==}
    case True{} Spec.BNone{}:
      {==}
    case True{} Spec.BLen{n}:
      {==}
    case True{} Spec.BChunked{}:
      {==}
    case True{} Spec.BBad{}:
      {==}

# a head made from a request and a framing is the one the law spells out
def mk.hd(+ip: Bytes(), +m: Eng.Meth, +t: Bytes(), +b: Bytes(), +cl: Bool, +ws: Bool, +k: Bytes(), +f: Stream.Frame,
  hd: Eng.Hd) ->
  {Stream.head.ok(ip, Eng.Req{m, t, b, cl, ws, k, hd}, f) == Laws.spec.head.req(ip, Eng.Req{m, t, b, cl, ws, k, hd}, f) :
    Stream.Head}:
  match hd:
    case Eng.Hd{+mb, +v10, +fs, +cn}:
      %req.eq(ip, Eng.Req{m, t, b, cl, ws, k, Eng.Hd{mb, v10, fs, cn}}) :
        {Stream.HOk{Http.req.of(ip, Eng.Req{m, t, b, cl, ws, k, Eng.Hd{mb, v10, fs, cn}}), f, v10, cl || ws,
          String.eq(mb, "HEAD")} ==
          Stream.HOk{_, f, v10, cl || ws, String.eq(mb, "HEAD")} : Stream.Head}
      {==}

def mk.some(+ip: Bytes(), r: Eng.Req, f: Stream.Frame) ->
  {Stream.head.ok(ip, r, f) == Laws.spec.head.req(ip, r, f) : Stream.Head}:
  match r:
    case Eng.Req{m, t, b, cl, ws, k, hd}:
      mk.hd(ip, m, t, b, cl, ws, k, f, hd)

def mk.eq(+ip: Bytes(), r: Eng.Req, mf: Maybe<&2, Stream.Frame>) ->
  {Stream.head.mk(ip, r, mf) == Laws.spec.head.mk(ip, r, mf) : Stream.Head}:
  match mf:
    case None{}:
      {==}
    case Some{f}:
      mk.some(ip, r, f)

def HV(+ip: Bytes(), -pd: Eng.Pend, -h: Spec.Head) -> Type:
  {Stream.head.of(ip, pd) == Laws.spec.head(ip, h) : Stream.Head}

def pair.eq(+v10: Bool, +te: Bool, +hs: Nat, +l: Maybe<&2, U32>) ->
  {(Eng.hosts.ok(v10, EP.hsat(hs)), Eng.body.kind(te, v10, EP.clv(l))) ==
    (Spec.hosts.ok(v10, hs), EP.bdv(Spec.body.of(te, v10, l))) : Bool & Eng.Bd}:
  %EP.hok(v10, hs) :
    {(Eng.hosts.ok(v10, EP.hsat(hs)), Eng.body.kind(te, v10, EP.clv(l))) == (_, EP.bdv(Spec.body.of(te, v10, l))) :
      Bool & Eng.Bd}
  %EP.bok(te, v10, l) :
    {(Eng.hosts.ok(v10, EP.hsat(hs)), Eng.body.kind(te, v10, EP.clv(l))) == (Eng.hosts.ok(v10, EP.hsat(hs)), _) :
      Bool & Eng.Bd}
  {==}

def head.at.fx(+ip: Bytes(), +pd: Eng.Pend, +h: Spec.Head, +v10: Bool, +te: Bool, +hs: Nat, +l: Maybe<&2, U32>,
  +pr: EP.PR(pd, h),
  eh: {hf.pv(EP.hv(h)) == (Eng.hosts.ok(v10, EP.hsat(hs)), Eng.body.kind(te, v10, EP.clv(l))) : Bool & Eng.Bd}) ->
  {Stream.head.pair(ip, Eng.pend.req(pd, ""), Eng.head.frame(pd)) ==
    Stream.head.mk(ip, Spec.req(h, Nil{}), Laws.spec.frame(Spec.hosts.ok(v10, hs), Spec.body.of(te, v10, l))) :
    Stream.Head}:
  +fe = Equal.trans(Bool & Eng.Bd, Eng.head.frame(pd), hf.pv(EP.pv(pd)),
    (Spec.hosts.ok(v10, hs), EP.bdv(Spec.body.of(te, v10, l))), e.hf(pd),
    Equal.trans(Bool & Eng.Bd, hf.pv(EP.pv(pd)), hf.pv(EP.hv(h)), (Spec.hosts.ok(v10, hs), EP.bdv(Spec.body.of(te, v10, l))),
      Equal.cong(EP.PV, Bool & Eng.Bd, x => hf.pv(x), EP.pv(pd), EP.hv(h), pr),
      Equal.trans(Bool & Eng.Bd, hf.pv(EP.hv(h)), (Eng.hosts.ok(v10, EP.hsat(hs)), Eng.body.kind(te, v10, EP.clv(l))),
        (Spec.hosts.ok(v10, hs), EP.bdv(Spec.body.of(te, v10, l))), eh, pair.eq(v10, te, hs, l))))
  %EP.REQ(pd, h, Nil{}, pr) :
    {Stream.head.pair(ip, _, Eng.head.frame(pd)) ==
      Stream.head.mk(ip, Spec.req(h, Nil{}), Laws.spec.frame(Spec.hosts.ok(v10, hs), Spec.body.of(te, v10, l))) :
      Stream.Head}
  %Equal.sym(Bool & Eng.Bd, Eng.head.frame(pd), (Spec.hosts.ok(v10, hs), EP.bdv(Spec.body.of(te, v10, l))), fe) :
    {Stream.head.pair(ip, Spec.req(h, Nil{}), _) ==
      Stream.head.mk(ip, Spec.req(h, Nil{}), Laws.spec.frame(Spec.hosts.ok(v10, hs), Spec.body.of(te, v10, l))) :
      Stream.Head}
  %Equal.sym(Maybe<&2, Stream.Frame>, Stream.head.frame(Spec.hosts.ok(v10, hs), EP.bdv(Spec.body.of(te, v10, l))),
    Laws.spec.frame(Spec.hosts.ok(v10, hs), Spec.body.of(te, v10, l)),
    fr.eq(Spec.hosts.ok(v10, hs), Spec.body.of(te, v10, l))) :
    {Stream.head.mk(ip, Spec.req(h, Nil{}), _) ==
      Stream.head.mk(ip, Spec.req(h, Nil{}), Laws.spec.frame(Spec.hosts.ok(v10, hs), Spec.body.of(te, v10, l))) :
      Stream.Head}
  {==}

# LEMMA: at the blank line, the reader's head is the walk's
def head.at(+ip: Bytes(), +pd: Eng.Pend, h: Spec.Head) -> EP.PR(pd, h) -> HV(ip, pd, h):
  match h:
    case Spec.Head{+hm, +ht, +l, +hc, +hs, +hk, +hu, +hcu, +hvb, +hf, +hxx}:
      match hf:
        case Eng.Fx{+v10, +ka, +te}:
          pr => Equal.trans(Stream.Head, Stream.head.of(ip, pd),
            Stream.head.mk(ip, Spec.req(Spec.Head{hm, ht, l, hc, hs, hk, hu, hcu, hvb, Eng.Fx{v10, ka, te}, hxx}, Nil{}),
              Laws.spec.frame(Spec.hosts.ok(v10, hs), Spec.body.of(te, v10, l))),
            Laws.spec.head(ip, Spec.Head{hm, ht, l, hc, hs, hk, hu, hcu, hvb, Eng.Fx{v10, ka, te}, hxx}),
            head.at.fx(ip, pd, Spec.Head{hm, ht, l, hc, hs, hk, hu, hcu, hvb, Eng.Fx{v10, ka, te}, hxx}, v10, te, hs, l,
              pr, {==}),
            mk.eq(ip, Spec.req(Spec.Head{hm, ht, l, hc, hs, hk, hu, hcu, hvb, Eng.Fx{v10, ka, te}, hxx}, Nil{}),
              Laws.spec.frame(Spec.hosts.ok(v10, hs), Spec.body.of(te, v10, l))))

# LEMMA: wherever the walk is, the reader has the head it has
def view.m(+ip: Bytes(), mode: Spec.Mode, +p: Eng.P, +pd: Eng.Pend, +out: List<&2, Eng.Req>, +since: List<&2, U32>,
  r: EP.REL.m(p, mode, out, since, pd)) ->
  {Stream.at.head(ip, p) == Laws.spec.at.head.m(ip, mode) : Maybe<&2, Stream.Head>}:
  match mode:
    case Spec.MReq{+cur}:
      (e1, r2) = r
      (pl, bnd) = r2
      by.p(ip, p, Eng.feed(cur, Eng.P{Eng.Pre{}, Eng.pend.new(), out}), None{}, e1,
        none.req(ip, Spec.req.view(cur), Eng.feed(cur, Eng.P{Eng.Pre{}, Eng.pend.new(), out}), out)(EP.line.req(cur, out)(pl)))
    case Spec.MBlank{}:
      (e1, bnd) = r
      by.p(ip, p, Eng.P{Eng.PreLf{}, Eng.pend.new(), out}, None{}, e1, {==})
    case Spec.MField{h, +cur}:
      (pr, r2) = r
      (e1, r3) = r2
      (pl, bnd) = r3
      by.p(ip, p, Eng.feed(cur, Eng.P{Eng.Lin{}, pd, out}), None{}, e1,
        none.field(ip, Spec.field.view(cur), Eng.feed(cur, Eng.P{Eng.Lin{}, pd, out}), pd, out)(EP.line.field(cur, pd, out)(pl)))
    case Spec.MEol{h}:
      (pr, r2) = r
      (e1, bnd) = r2
      by.p(ip, p, Eng.P{Eng.CrM{}, pd, out}, None{}, e1, {==})
    case Spec.MEoh{+h}:
      (pr, r2) = r
      (e1, bnd) = r2
      by.p(ip, p, Eng.P{Eng.CrL{}, pd, out}, Some{Laws.spec.head(ip, h)}, e1,
        Equal.cong(Stream.Head, Maybe<&2, Stream.Head>, y => Some{y}, Stream.head.of(ip, pd), Laws.spec.head(ip, h),
          head.at(ip, pd, h)(pr)))
    case Spec.MBody{h, more, got}:
      (pr, r2) = r
      (e1, bnd) = r2
      by.p(ip, p, Eng.P{Eng.Bod{more, Bytes.from_list(got)}, pd, out}, None{}, e1, {==})
    case Spec.MChunk{h, at, n, got, left}:
      (pr, r2) = r
      (e1, bnd) = r2
      by.p(ip, p, Eng.P{Eng.Chk{EP.at.eng(at), n, Bytes.from_list(got), left}, pd, out}, None{}, e1, {==})
    case Spec.MData{h, more, got, left}:
      (pr, r2) = r
      (e1, bnd) = r2
      by.p(ip, p, Eng.P{Eng.Chd{more, Bytes.from_list(got), left}, pd, out}, None{}, e1, {==})
    case Spec.MUp{got}:
      by.p(ip, p, Eng.P{Eng.Rest{Bytes.from_list(got)}, Eng.pend.new(), out}, None{}, r, {==})
    case Spec.MBad{}:
      dead.none(ip, p, out)(r)

def view.sr(+ip: Bytes(), +p: Eng.P, w: Spec.W, s: EP.SR(p, w)) ->
  {Stream.at.head(ip, p) == Laws.spec.at.head(ip, w) : Maybe<&2, Stream.Head>}:
  match w:
    case Spec.W{mode, +out, +since}:
      (pd, r) = s
      view.m(ip, mode, p, pd, out, since, r)

def Laws.stream_head(ip, rs):
  +l = Bytes.to_list(Bytes.concat(rs))
  Equal.trans(Maybe<&2, Stream.Head>, Stream.at.head(ip, EL.reads(rs, Eng.p.new())), Stream.at.head(ip, Eng.feed(l, Eng.p.new())),
    Laws.spec.at.head(ip, Spec.walk(l, Laws.spec.start())),
    Equal.cong(Eng.P, Maybe<&2, Stream.Head>, y => Stream.at.head(ip, y), EL.reads(rs, Eng.p.new()), Eng.feed(l, Eng.p.new()),
      EP.reads.is(rs, Eng.p.new())),
    view.sr(ip, Eng.feed(l, Eng.p.new()), Spec.walk(l, Laws.spec.start()),
      sr.walk(l, Laws.spec.start(), Eng.p.new(), (Eng.pend.new(), ({==}, (Unit{}, {==}))))))
