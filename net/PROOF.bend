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
# The laws of response bodies written as they are made lean on
# bend-proxy's head lemmas and walk the spec over the chunks themselves.
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
import ./ws_hs.bend as H
import ../wire/loop.bend as L

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

# Middleware over a table, the command line, JSON's typed fields: by
# computation

def Laws.wrap_vectors():
  {==}

def Laws.wrap_pats():
  {==}

def Laws.argv_vectors():
  {==}

def Laws.flag_vectors():
  {==}

def Laws.flag_num_vectors():
  {==}

def Laws.flag_on_vectors():
  {==}

def Laws.json_str_vectors():
  {==}

def Laws.json_u32_vectors():
  {==}

def Laws.json_nat_vectors():
  {==}

def Laws.json_i64_vectors():
  {==}

def Laws.json_bool_vectors():
  {==}

def Laws.json_arr_vectors():
  {==}

def Laws.json_obj_vectors():
  {==}

def Laws.json_fails_vectors():
  {==}

def Laws.json_num_text_vectors():
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

# The handler's time
# ==================

def Laws.handler_late(ms, t, h, head, closing, v10, resp, acc):
  %Equal.sym(Bool, Nat.is_lt(t, U32.to_nat(ms)), False{}, h) : {Server.plan(head, closing, v10, Laws.within.at(_, resp), acc) ==
    Server.End{Con{L.Raw{Server.own(head, v10, 503)}, acc}} : Server.Plan}
  {==}

def Laws.handler_in_time(ms, t, h, head, closing, v10, resp, acc):
  %Equal.sym(Bool, Nat.is_lt(t, U32.to_nat(ms)), True{}, h) : {Server.plan(head, closing, v10, Laws.within.at(_, resp), acc) ==
    Server.plan.of(closing, Server.rev.onto(Server.segs.of(head, closing, v10, resp), acc)) : Server.Plan}
  {==}

def Laws.late_framed(head, v10):
  match head v10:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# WebSockets
# ==========

def ws.426(+get: Bool, +key: Bytes(), +offered: List<&2, Bytes()>, +proto: Bytes()) ->
  {H.s.answer(get, False{}, key, offered, proto) == H.SNo{426} : H.Sv}:
  match get:
    case True{}:
      {==}
    case False{}:
      {==}

# Response bodies, written as they are made
# =========================================
#
# pour_chunked walks wire/http1's spec over what Stream.poured writes. The
# head is bend-proxy's (rser.list, rline.st, rfields.walk, rconn: the
# handler's fields change nothing) with one field more, the
# Transfer-Encoding, read here (te.line), and the blank line then frames
# the body chunked (te.end). The body is the writes in turn (bw), each
# cut by Stream.chunks.go from 2^14 down (cg, by induction on the bit:
# a chunk that fits is read as its data by pw -- its size line's digits
# by dw, each paid for, what the line says by the table tab, its data by
# dd -- and what is left is under the next bit, rest.lt), and the last
# chunk ends it (last). The budget is the one the law takes (Laws.fits),
# spent as the spec spends it. pour_length is bend-proxy's rmain over the
# head with the length, once rvalid's length is seen to read the body
# only by its length (len.ok) and the writes to go out as they are
# (emits.len). The 204, the 304 and the 500 are rmain and rr.h over a
# body the writer never sends (emits.none, pour_quiet). pour_capped and
# pour_bounded are arithmetic on the writer's counts: a length never
# passed (cap), and a chunk's framing at most eight bytes (hl, bnd).

def Laws.pour_vectors():
  {==}

def Laws.fits_vectors():
  {==}

# pour_quiet: a failed writer emits nothing, and its end is nothing
def quiet.end(m: Stream.Mode, e: Stream.Err) -> {Pair.fst(Bytes(), Bool, Stream.close(Stream.Sent{m, Some{e}})) == "" : Bytes()}:
  match m:
    case Stream.MChunked{}:
      {==}
    case Stream.MLen{l}:
      {==}
    case Stream.MRaw{}:
      {==}
    case Stream.MNone{}:
      {==}

def Laws.pour_quiet(m, e, ws):
  match ws:
    case Nil{}:
      quiet.end(m, e)
    case Con{x, t}:
      Laws.pour_quiet(m, e, t)

# Lists, bytes, numbers
# ---------------------

# the walk over two parts: the second from where the first left it
def po.wapp(+e: R.Ask, xs: List<&2, U32>, -ys: List<&2, U32>, w: RS.W) ->
  {RS.walk(e, List.append(&2, U32, xs, ys), w) == RS.walk(e, ys, RS.walk(e, xs, w)) : RS.W}:
  match xs:
    case Nil{}:
      {==}
    case Con{+c, t}:
      po.wapp(e, t, ys, RS.next(e, w, c))

def po.wb(+e: R.Ask, +a: Bytes(), +b: Bytes(), +w: RS.W) ->
  {RS.walk(e, Bytes.to_list(Bytes.append(a, b)), w) == RS.walk(e, Bytes.to_list(b), RS.walk(e, Bytes.to_list(a), w)) : RS.W}:
  %Equal.sym(List<&2, U32>, Bytes.to_list(Bytes.append(a, b)), List.append(&2, U32, Bytes.to_list(a), Bytes.to_list(b)),
    Bytes.to_list_append(a, b)) : {RS.walk(e, _, w) == RS.walk(e, Bytes.to_list(b), RS.walk(e, Bytes.to_list(a), w)) : RS.W}
  po.wapp(e, Bytes.to_list(a), Bytes.to_list(b), w)

def po.blen(+c: Char, +t: Bytes()) -> {Bytes.len(SCon{c, t}) == 1n+Bytes.len(t) : Nat}:
  Bytes.len.shift(t, 0n)

def po.sub0(+a: Nat) -> {Nat.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

# a take of no more than there is has what it asked for
def po.take.len(x: Bytes(), s: Nat, h: {Nat.is_le(s, Bytes.len(x)) == True{} : Bool}) ->
  {Bytes.len(String.take(x, s)) == s : Nat}:
  match x s:
    case SNil{} 0n:
      {==}
    case SNil{} 1n+q:
      Bool.no({Bytes.len(String.take(SNil{}, 1n+q)) == 1n+q : Nat}, h)
    case SCon{c, t} 0n:
      {==}
    case SCon{+c, +t} 1n+(+q):
      +hq = Equal.trans(Bool, Nat.is_le(q, Bytes.len(t)), Nat.is_le(1n+q, Bytes.len(SCon{c, t})), True{},
        Equal.cong(Nat, Bool, y => Nat.is_le(1n+q, y), 1n+Bytes.len(t), Bytes.len(SCon{c, t}),
          Equal.sym(Nat, Bytes.len(SCon{c, t}), 1n+Bytes.len(t), po.blen(c, t))), h)
      %Equal.sym(Nat, Bytes.len(SCon{c, String.take(t, q)}), 1n+Bytes.len(String.take(t, q)), po.blen(c, String.take(t, q))) :
        {_ == 1n+q : Nat}
      Equal.cong(Nat, Nat, y => 1n+y, Bytes.len(String.take(t, q)), q, po.take.len(t, q, hq))

def po.drop.len(x: Bytes(), s: Nat) -> {Bytes.len(String.drop(x, s)) == Nat.sub(Bytes.len(x), s) : Nat}:
  match x s:
    case SNil{} 0n:
      {==}
    case SNil{} 1n+q:
      {==}
    case SCon{+c, +t} 0n:
      Equal.sym(Nat, Nat.sub(Bytes.len(SCon{c, t}), 0n), Bytes.len(SCon{c, t}), po.sub0(Bytes.len(SCon{c, t})))
    case SCon{+c, +t} 1n+(+q):
      %Equal.sym(Nat, Bytes.len(SCon{c, t}), 1n+Bytes.len(t), po.blen(c, t)) :
        {Bytes.len(String.drop(t, q)) == Nat.sub(_, 1n+q) : Nat}
      po.drop.len(t, q)

# a take and the drop after it are the whole
def po.split(x: Bytes(), s: Nat) ->
  {Bytes.to_list(x) == List.append(&2, U32, Bytes.to_list(String.take(x, s)), Bytes.to_list(String.drop(x, s))) :
    List<&2, U32>}:
  match x s:
    case SNil{} 0n:
      {==}
    case SNil{} 1n+q:
      {==}
    case SCon{c, t} 0n:
      {==}
    case SCon{Chr{+c}, +t} 1n+(+q):
      Equal.cong(List<&2, U32>, List<&2, U32>, ys => Con{c, ys}, Bytes.to_list(t),
        List.append(&2, U32, Bytes.to_list(String.take(t, q)), Bytes.to_list(String.drop(t, q))), po.split(t, q))

def po.add.succ(a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, y => 1n+y, Nat.add(p, 1n+b), 1n+Nat.add(p, b), po.add.succ(p, b))

def po.double.add(s: Nat) -> {Nat.double(s) == Nat.add(s, s) : Nat}:
  match s:
    case 0n:
      {==}
    case 1n+(+p):
      %Equal.sym(Nat, Nat.add(p, 1n+p), 1n+Nat.add(p, p), po.add.succ(p, p)) : {2n+Nat.double(p) == 1n+_ : Nat}
      Equal.cong(Nat, Nat, y => 2n+y, Nat.double(p), Nat.add(p, p), po.double.add(p))

def po.sub.add(s: Nat, n: Nat, h: {Nat.is_le(s, n) == True{} : Bool}) -> {Nat.add(s, Nat.sub(n, s)) == n : Nat}:
  match s n:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Bool.no({Nat.add(1n+p, Nat.sub(0n, 1n+p)) == 0n : Nat}, h)
    case 1n+(+p) 1n+(+q):
      Equal.cong(Nat, Nat, y => 1n+y, Nat.add(p, Nat.sub(q, p)), q, po.sub.add(p, q, h))

def po.lt.cancel(s: Nat, +r: Nat, +t: Nat) -> {Nat.is_lt(Nat.add(s, r), Nat.add(s, t)) == Nat.is_lt(r, t) : Bool}:
  match s:
    case 0n:
      {==}
    case 1n+p:
      po.lt.cancel(p, r, t)

# what is left after a chunk of s, of fewer than 2s bytes, is fewer than s
def po.rest.lt(+s: Nat, +n: Nat, le: {Nat.is_le(s, n) == True{} : Bool},
  lt: {Nat.is_lt(n, Nat.add(s, s)) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(n, s), s) == True{} : Bool}:
  %po.lt.cancel(s, Nat.sub(n, s), s) : {_ == True{} : Bool}
  %Equal.sym(Nat, Nat.add(s, Nat.sub(n, s)), n, po.sub.add(s, n, le)) : {Nat.is_lt(_, Nat.add(s, s)) == True{} : Bool}
  lt

# The chunks, read back
# ---------------------

# where a size line's digits leave the grammar: in the size, once one came
def po.dig.at(ds: List<&2, U32>, at: R.At) -> R.At:
  match ds:
    case Nil{}:
      at
    case Con{c, t}:
      po.dig.at(t, R.ASize{})

def po.dw.go(g: R.Go, +t: List<&2, U32>, +n: U32, +left: U32, +e: R.Ask, +h: R.Head, +got: List<&2, U32>,
  +o: List<&2, U32>, +ok: {Laws.dig.step(g, n, left, n2 => l2 => Laws.dig.ok(t, R.ASize{}, n2, l2)) == True{} : Bool},
  ih: @+n2: U32 -> @+l2: U32 -> {Laws.dig.ok(t, R.ASize{}, n2, l2) == True{} : Bool} ->
    {RS.walk(e, t, RS.W{RS.MChunk{h, R.ASize{}, n2, got, l2}, o}) ==
      RS.W{RS.MChunk{h, po.dig.at(t, R.ASize{}), Laws.dig.val(t, R.ASize{}, n2), got, Laws.dig.left(t, l2)}, o} : RS.W}) ->
  {RS.walk(e, t, RS.W{RS.chunk.go(g, h, n, got, left), o}) ==
    RS.W{RS.MChunk{h, po.dig.at(t, R.ASize{}), Laws.dig.val.step(g, n, n2 => Laws.dig.val(t, R.ASize{}, n2)), got,
      Laws.dig.left(t, (left - 1 : U32))}, o} : RS.W}:
  match g:
    case R.GDigit{+d}:
      +n2 : U32 = (n * 16 + d : U32)
      +a = Bool.not(U32.is_le(left, n2))
      +b = Laws.dig.ok(t, R.ASize{}, n2, (left - 1 : U32))
      +hle = Bool.not_true(U32.is_le(left, n2), Bool.and_l(a, b, ok))
      %Equal.sym(Bool, U32.is_le(left, n2), False{}, hle) :
        {RS.walk(e, t, RS.W{RS.chunk.paid(_, h, R.ASize{}, n2, got, left), o}) ==
          RS.W{RS.MChunk{h, po.dig.at(t, R.ASize{}), Laws.dig.val(t, R.ASize{}, n2), got, Laws.dig.left(t, (left - 1 : U32))}, o} :
          RS.W}
      ih(n2, (left - 1 : U32), Bool.and_r(a, b, ok))
    case R.GBad{}:
      Bool.no({RS.walk(e, t, RS.W{RS.chunk.go(R.GBad{}, h, n, got, left), o}) ==
        RS.W{RS.MChunk{h, po.dig.at(t, R.ASize{}), n, got, Laws.dig.left(t, (left - 1 : U32))}, o} : RS.W}, ok)
    case R.GTo{at, paid}:
      Bool.no({RS.walk(e, t, RS.W{RS.chunk.go(R.GTo{at, paid}, h, n, got, left), o}) ==
        RS.W{RS.MChunk{h, po.dig.at(t, R.ASize{}), n, got, Laws.dig.left(t, (left - 1 : U32))}, o} : RS.W}, ok)
    case R.GLine{}:
      Bool.no({RS.walk(e, t, RS.W{RS.chunk.go(R.GLine{}, h, n, got, left), o}) ==
        RS.W{RS.MChunk{h, po.dig.at(t, R.ASize{}), n, got, Laws.dig.left(t, (left - 1 : U32))}, o} : RS.W}, ok)
    case R.GDone{}:
      Bool.no({RS.walk(e, t, RS.W{RS.chunk.go(R.GDone{}, h, n, got, left), o}) ==
        RS.W{RS.MChunk{h, po.dig.at(t, R.ASize{}), n, got, Laws.dig.left(t, (left - 1 : U32))}, o} : RS.W}, ok)

# LEMMA: a size line's digits, each paid for, are read as their size, the
# budget spent a digit each
def po.dw(ds: List<&2, U32>, at: R.At, +n: U32, +left: U32, +e: R.Ask, +h: R.Head, +got: List<&2, U32>,
  +o: List<&2, U32>, ok: {Laws.dig.ok(ds, at, n, left) == True{} : Bool}) ->
  {RS.walk(e, ds, RS.W{RS.MChunk{h, at, n, got, left}, o}) ==
    RS.W{RS.MChunk{h, po.dig.at(ds, at), Laws.dig.val(ds, at, n), got, Laws.dig.left(ds, left)}, o} : RS.W}:
  match ds:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      po.dw.go(R.chunk.step(at, R.xk.of(R.cls(c), c)), t, n, left, e, h, got, o, ok,
        n2 => l2 => k => po.dw(t, R.ASize{}, n2, l2, e, h, got, o, k))

# LEMMA: a chunk's data is counted off to its last byte, and its CR LF is
# next
def po.dd(t: Bytes(), +c: U32, +e: R.Ask, +h: R.Head, +got: List<&2, U32>, +left: U32, +o: List<&2, U32>) ->
  {RS.walk(e, Con{c, Bytes.to_list(t)}, RS.W{RS.MData{h, Bytes.len(t), got, left}, o}) ==
    RS.W{RS.MChunk{h, R.ADataCr{}, 0, List.append(&2, U32, got, Con{c, Bytes.to_list(t)}), left}, o} : RS.W}:
  match t:
    case SNil{}:
      {==}
    case SCon{Chr{+c2}, +t2}:
      %Equal.sym(Nat, Bytes.len(SCon{Chr{c2}, t2}), 1n+Bytes.len(t2), po.blen(Chr{c2}, t2)) :
        {RS.walk(e, Con{c, Con{c2, Bytes.to_list(t2)}}, RS.W{RS.MData{h, _, got, left}, o}) ==
          RS.W{RS.MChunk{h, R.ADataCr{}, 0, List.append(&2, U32, got, Con{c, Con{c2, Bytes.to_list(t2)}}), left}, o} : RS.W}
      %PP.app.assoc(U32, got, Con{c, Nil{}}, Con{c2, Bytes.to_list(t2)}) :
        {RS.walk(e, Con{c2, Bytes.to_list(t2)}, RS.W{RS.MData{h, Bytes.len(t2), RS.snoc(got, c), left}, o}) ==
          RS.W{RS.MChunk{h, R.ADataCr{}, 0, _, left}, o} : RS.W}
      po.dd(t2, c2, e, h, RS.snoc(got, c), left, o)


# the bound a write cut from 2^j down is under: 2^(j+1)
def po.lim(j: Nat) -> Nat:
  Stream.nth.size(j, [2n, 4n, 8n, 16n, 32n, 64n, 128n, 256n, 512n, 1024n, 2048n, 4096n, 8192n, 16384n, 32768n])

def po.lim.pred(j: Nat) -> Nat:
  match j:
    case 0n:
      1n
    case 1n+i:
      po.lim(i)

# what the fifteen size lines say, each: read to the size, not zero, the
# chunk's size
def po.Tab(+j: Nat) -> Type:
  {po.dig.at(Laws.chunk.ds(j), R.ASize0{}) == R.ASize{} : R.At} &
    {U32.is_zero(Laws.dig.val(Laws.chunk.ds(j), R.ASize0{}, 0)) == False{} : Bool} &
    {Nat.is_eq(U32.to_nat(Laws.dig.val(Laws.chunk.ds(j), R.ASize0{}, 0)), Stream.chunk.size(j)) == True{} : Bool} &
    {Nat.is_eq(Stream.chunk.size(j), 0n) == False{} : Bool} &
    {Nat.is_eq(po.lim(j), Nat.add(Stream.chunk.size(j), Stream.chunk.size(j))) == True{} : Bool} &
    {Nat.is_eq(po.lim.pred(j), Stream.chunk.size(j)) == True{} : Bool}

def po.tab(j: Nat, hj: {Nat.is_le(j, 14n) == True{} : Bool}) -> po.Tab(j):
  match j:
    case 0n:
      ({==}, ({==}, ({==}, ({==}, ({==}, {==})))))
    case 1n+j1:
      match j1:
        case 0n:
          ({==}, ({==}, ({==}, ({==}, ({==}, {==})))))
        case 1n+j2:
          match j2:
            case 0n:
              ({==}, ({==}, ({==}, ({==}, ({==}, {==})))))
            case 1n+j3:
              match j3:
                case 0n:
                  ({==}, ({==}, ({==}, ({==}, ({==}, {==})))))
                case 1n+j4:
                  match j4:
                    case 0n:
                      ({==}, ({==}, ({==}, ({==}, ({==}, {==})))))
                    case 1n+j5:
                      match j5:
                        case 0n:
                          ({==}, ({==}, ({==}, ({==}, ({==}, {==})))))
                        case 1n+j6:
                          match j6:
                            case 0n:
                              ({==}, ({==}, ({==}, ({==}, ({==}, {==})))))
                            case 1n+j7:
                              match j7:
                                case 0n:
                                  ({==}, ({==}, ({==}, ({==}, ({==}, {==})))))
                                case 1n+j8:
                                  match j8:
                                    case 0n:
                                      ({==}, ({==}, ({==}, ({==}, ({==}, {==})))))
                                    case 1n+j9:
                                      match j9:
                                        case 0n:
                                          ({==}, ({==}, ({==}, ({==}, ({==}, {==})))))
                                        case 1n+j10:
                                          match j10:
                                            case 0n:
                                              ({==}, ({==}, ({==}, ({==}, ({==}, {==})))))
                                            case 1n+j11:
                                              match j11:
                                                case 0n:
                                                  ({==}, ({==}, ({==}, ({==}, ({==}, {==})))))
                                                case 1n+j12:
                                                  match j12:
                                                    case 0n:
                                                      ({==}, ({==}, ({==}, ({==}, ({==}, {==})))))
                                                    case 1n+j13:
                                                      match j13:
                                                        case 0n:
                                                          ({==}, ({==}, ({==}, ({==}, ({==}, {==})))))
                                                        case 1n+j14:
                                                          match j14:
                                                            case 0n:
                                                              ({==}, ({==}, ({==}, ({==}, ({==}, {==})))))
                                                            case 1n+j15:
                                                              Bool.no(po.Tab(1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+j15), hj)

def po.nat.eq(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Bool.no({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      Bool.no({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, x => 1n+x, p, q, po.nat.eq(p, q, h))

def po.t5(+j: Nat, tab: po.Tab(j)) -> {Nat.is_eq(po.lim(j), Nat.add(Stream.chunk.size(j), Stream.chunk.size(j))) == True{} : Bool}:
  (a, r) = tab
  (b, r2) = r
  (c, r3) = r2
  (d, r4) = r3
  (f, g) = r4
  f

def po.t6(+j: Nat, tab: po.Tab(j)) -> {Nat.is_eq(po.lim.pred(j), Stream.chunk.size(j)) == True{} : Bool}:
  (a, r) = tab
  (b, r2) = r
  (c, r3) = r2
  (d, r4) = r3
  (f, g) = r4
  g

# LEMMA: a chunk -- its size line, CR LF, its data, CR LF -- is read as
# its data, the budget spent on its line and its data
def po.pw(+j: Nat, +c: U32, +t: Bytes(), +r: Bytes(), +e: R.Ask, +h: R.Head, +got: List<&2, U32>, +left: U32,
  +o: List<&2, U32>, tab: po.Tab(j), hp: {Bytes.len(SCon{Chr{c}, t}) == Stream.chunk.size(j) : Nat},
  ok: {Laws.chunk.ok(j, left) == True{} : Bool}) ->
  {RS.walk(e, Bytes.to_list(Bytes.append(Stream.chunk.hex(j), Bytes.append("\r\n", Bytes.append(SCon{Chr{c}, t},
    Bytes.append("\r\n", r))))), RS.W{RS.MChunk{h, R.ASize0{}, 0, got, left}, o}) ==
    RS.walk(e, Bytes.to_list(r), RS.W{RS.MChunk{h, R.ASize0{}, 0, List.append(&2, U32, got, Bytes.to_list(SCon{Chr{c}, t})),
      Laws.chunk.left(j, left)}, o}) : RS.W}:
  (t1, tr) = tab
  (t2, tr2) = tr
  (t3, tr3) = tr2
  (t4, tr4) = tr3
  (t5, t6) = tr4
  +ds = Laws.chunk.ds(j)
  +v = Laws.dig.val(ds, R.ASize0{}, 0)
  +l1 = Laws.dig.left(ds, left)
  +w0 : RS.W = RS.W{RS.MChunk{h, R.ASize0{}, 0, got, left}, o}
  +p : Bytes() = SCon{Chr{c}, t}
  +b3 = Bytes.append("\r\n", r)
  +b2 = Bytes.append(p, b3)
  +b1 = Bytes.append("\r\n", b2)
  +rhs = RS.walk(e, Bytes.to_list(r), RS.W{RS.MChunk{h, R.ASize0{}, 0, List.append(&2, U32, got, Bytes.to_list(p)),
    Laws.chunk.left(j, left)}, o})
  %Equal.sym(RS.W, RS.walk(e, Bytes.to_list(Bytes.append(Stream.chunk.hex(j), b1)), w0),
    RS.walk(e, Bytes.to_list(b1), RS.walk(e, Bytes.to_list(Stream.chunk.hex(j)), w0)), po.wb(e, Stream.chunk.hex(j), b1, w0)) :
    {_ == rhs : RS.W}
  %Equal.sym(RS.W, RS.walk(e, ds, w0), RS.W{RS.MChunk{h, po.dig.at(ds, R.ASize0{}), v, got, l1}, o},
    po.dw(ds, R.ASize0{}, 0, left, e, h, got, o, ok)) :
    {RS.walk(e, Bytes.to_list(b1), _) == rhs : RS.W}
  %Equal.sym(R.At, po.dig.at(ds, R.ASize0{}), R.ASize{}, t1) :
    {RS.walk(e, Bytes.to_list(b1), RS.W{RS.MChunk{h, _, v, got, l1}, o}) == rhs : RS.W}
  +w1 : RS.W = RS.W{RS.MChunk{h, R.ASize{}, v, got, l1}, o}
  %Equal.sym(RS.W, RS.walk(e, Bytes.to_list(b1), w1), RS.walk(e, Bytes.to_list(b2), RS.walk(e, Bytes.to_list("\r\n"), w1)),
    po.wb(e, "\r\n", b2, w1)) :
    {_ == rhs : RS.W}
  %Equal.sym(Bool, U32.is_zero(v), False{}, t2) :
    {RS.walk(e, Bytes.to_list(b2), RS.W{RS.chunk.line(_, h, v, got, l1), o}) == rhs : RS.W}
  %Equal.sym(Nat, U32.to_nat(v), Stream.chunk.size(j), po.nat.eq(U32.to_nat(v), Stream.chunk.size(j), t3)) :
    {RS.walk(e, Bytes.to_list(b2), RS.W{RS.MData{h, Nat.sub(_, 1n), got, (l1 - v : U32)}, o}) == rhs : RS.W}
  %hp :
    {RS.walk(e, Bytes.to_list(b2), RS.W{RS.MData{h, Nat.sub(_, 1n), got, (l1 - v : U32)}, o}) == rhs : RS.W}
  +w2 : RS.W = RS.W{RS.MData{h, Nat.sub(Bytes.len(p), 1n), got, (l1 - v : U32)}, o}
  %Equal.sym(RS.W, RS.walk(e, Bytes.to_list(b2), w2), RS.walk(e, Bytes.to_list(b3), RS.walk(e, Bytes.to_list(p), w2)),
    po.wb(e, p, b3, w2)) :
    {_ == rhs : RS.W}
  %Equal.sym(Nat, Bytes.len(p), 1n+Bytes.len(t), po.blen(Chr{c}, t)) :
    {RS.walk(e, Bytes.to_list(b3), RS.walk(e, Bytes.to_list(p), RS.W{RS.MData{h, Nat.sub(_, 1n), got, (l1 - v : U32)}, o})) == rhs :
      RS.W}
  %Equal.sym(Nat, Nat.sub(Bytes.len(t), 0n), Bytes.len(t), po.sub0(Bytes.len(t))) :
    {RS.walk(e, Bytes.to_list(b3), RS.walk(e, Bytes.to_list(p), RS.W{RS.MData{h, _, got, (l1 - v : U32)}, o})) == rhs : RS.W}
  %Equal.sym(RS.W, RS.walk(e, Con{c, Bytes.to_list(t)}, RS.W{RS.MData{h, Bytes.len(t), got, (l1 - v : U32)}, o}),
    RS.W{RS.MChunk{h, R.ADataCr{}, 0, List.append(&2, U32, got, Con{c, Bytes.to_list(t)}), (l1 - v : U32)}, o},
    po.dd(t, c, e, h, got, (l1 - v : U32), o)) :
    {RS.walk(e, Bytes.to_list(b3), _) == rhs : RS.W}
  +w3 : RS.W = RS.W{RS.MChunk{h, R.ADataCr{}, 0, List.append(&2, U32, got, Con{c, Bytes.to_list(t)}), (l1 - v : U32)}, o}
  %Equal.sym(RS.W, RS.walk(e, Bytes.to_list(b3), w3), RS.walk(e, Bytes.to_list(r), RS.walk(e, Bytes.to_list("\r\n"), w3)),
    po.wb(e, "\r\n", r, w3)) :
    {_ == rhs : RS.W}
  {==}

def po.ge.le(a: Nat, b: Nat) -> {Nat.is_ge(a, b) == Nat.is_le(b, a) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      po.ge.le(p, q)

def po.ge.not(a: Nat, b: Nat) -> {Bool.not(Nat.is_ge(a, b)) == Nat.is_lt(a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      po.ge.not(p, q)

def po.lt0(n: Nat) -> {Nat.is_lt(n, 0n) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}


def po.W5(+h: R.Head, +g: List<&2, U32>, +l: U32, +o: List<&2, U32>) -> RS.W:
  RS.W{RS.MChunk{h, R.ASize0{}, 0, g, l}, o}

def po.and.r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      Bool.no({b == True{} : Bool}, e)

# what the chunks of a write hand on, and what they leave
def po.IH(-j: Nat, +e: R.Ask, +h: R.Head, +o: List<&2, U32>, -go: Bytes() -> Bytes(), -okgo: Nat -> U32 -> Bool,
  -lgo: Nat -> U32 -> U32) -> Type:
  @+y: Bytes() -> @+l: U32 -> @+g: List<&2, U32> -> {okgo(Bytes.len(y), l) == True{} : Bool} ->
    {Nat.is_lt(Bytes.len(y), Stream.chunk.size(j)) == True{} : Bool} ->
    {RS.walk(e, Bytes.to_list(go(y)), RS.W{RS.MChunk{h, R.ASize0{}, 0, g, l}, o}) ==
      RS.W{RS.MChunk{h, R.ASize0{}, 0, List.append(&2, U32, g, Bytes.to_list(y)), lgo(Bytes.len(y), l)}, o} : RS.W}

# a chunk that fits: its bytes (p, the take), read, then the rest's
def po.ca.p(p: Bytes(), +j: Nat, +x: Bytes(), +e: R.Ask, +h: R.Head, +got: List<&2, U32>, +left: U32, +o: List<&2, U32>,
  go: Bytes() -> Bytes(), -okgo: Nat -> U32 -> Bool, -lgo: Nat -> U32 -> U32, +hj: {Nat.is_le(j, 14n) == True{} : Bool},
  +ep: {String.take(x, Stream.chunk.size(j)) == p : Bytes()},
  +fit0: {Nat.is_ge(Bytes.len(x), Stream.chunk.size(j)) == True{} : Bool},
  +inv: {Nat.is_lt(Bytes.len(x), po.lim(j)) == True{} : Bool},
  +ok: {Laws.ok.at(True{}, j, Bytes.len(x), left, okgo) == True{} : Bool}, ih: po.IH(j, e, h, o, go, okgo, lgo),
  tab: po.Tab(j), +h5: {Nat.is_eq(po.lim(j), Nat.add(Stream.chunk.size(j), Stream.chunk.size(j))) == True{} : Bool}) ->
  {RS.walk(e, Bytes.to_list(Stream.chunks.at(True{}, j, x, go)), RS.W{RS.MChunk{h, R.ASize0{}, 0, got, left}, o}) ==
    RS.W{RS.MChunk{h, R.ASize0{}, 0, List.append(&2, U32, got, Bytes.to_list(x)), Laws.left.at(True{}, j, Bytes.len(x), left, lgo)},
      o} : RS.W}:
  match p:
    case SNil{}:
      (t1, tr) = tab
      (t2, tr2) = tr
      (t3, tr3) = tr2
      (t4, tr4) = tr3
      (t5, t6) = tr4
      +s = Stream.chunk.size(j)
      +fit = Equal.trans(Bool, Nat.is_le(Stream.chunk.size(j), Bytes.len(x)), Nat.is_ge(Bytes.len(x), Stream.chunk.size(j)), True{}, Equal.sym(Bool, Nat.is_ge(Bytes.len(x), Stream.chunk.size(j)), Nat.is_le(Stream.chunk.size(j), Bytes.len(x)), po.ge.le(Bytes.len(x), Stream.chunk.size(j))), fit0)
      +lp = po.take.len(x, s, fit)
      +z = Equal.trans(Nat, 0n, Bytes.len(String.take(x, s)), s,
        Equal.cong(Bytes(), Nat, b => Bytes.len(b), SNil{}, String.take(x, s), Equal.sym(Bytes(), String.take(x, s), SNil{}, ep)), lp)
      Bool.no({RS.walk(e, Bytes.to_list(Stream.chunks.at(True{}, j, x, go)), RS.W{RS.MChunk{h, R.ASize0{}, 0, got, left}, o}) ==
        RS.W{RS.MChunk{h, R.ASize0{}, 0, List.append(&2, U32, got, Bytes.to_list(x)), Laws.left.at(True{}, j, Bytes.len(x), left, lgo)},
          o} : RS.W},
        Equal.sym(Bool, True{}, False{}, Equal.trans(Bool, True{}, Nat.is_eq(s, 0n), False{},
          Equal.cong(Nat, Bool, y => Nat.is_eq(y, 0n), 0n, s, z), t4)))
    case SCon{Chr{+c}, +t}:
      +s = Stream.chunk.size(j)
      +fit = Equal.trans(Bool, Nat.is_le(Stream.chunk.size(j), Bytes.len(x)), Nat.is_ge(Bytes.len(x), Stream.chunk.size(j)), True{}, Equal.sym(Bool, Nat.is_ge(Bytes.len(x), Stream.chunk.size(j)), Nat.is_le(Stream.chunk.size(j), Bytes.len(x)), po.ge.le(Bytes.len(x), Stream.chunk.size(j))), fit0)
      +lp = po.take.len(x, s, fit)
      +pc : Bytes() = SCon{Chr{c}, t}
      +d = String.drop(x, s)
      +cl = Laws.chunk.left(j, left)
      +a = Laws.chunk.ok(j, left)
      +hp = Equal.trans(Nat, Bytes.len(pc), Bytes.len(String.take(x, s)), s,
        Equal.cong(Bytes(), Nat, q => Bytes.len(q), pc, String.take(x, s), Equal.sym(Bytes(), String.take(x, s), pc, ep)), lp)
      +okr = Equal.trans(Bool, okgo(Bytes.len(d), cl), okgo(Nat.sub(Bytes.len(x), s), cl), True{},
        Equal.cong(Nat, Bool, n => okgo(n, cl), Bytes.len(d), Nat.sub(Bytes.len(x), s), po.drop.len(x, s)),
        po.and.r(a, okgo(Nat.sub(Bytes.len(x), s), cl), ok))
      +invr = Equal.trans(Bool, Nat.is_lt(Bytes.len(d), s), Nat.is_lt(Nat.sub(Bytes.len(x), s), s), True{},
        Equal.cong(Nat, Bool, n => Nat.is_lt(n, s), Bytes.len(d), Nat.sub(Bytes.len(x), s), po.drop.len(x, s)),
        po.rest.lt(s, Bytes.len(x), fit, Equal.trans(Bool, Nat.is_lt(Bytes.len(x), Nat.add(s, s)), Nat.is_lt(Bytes.len(x), po.lim(j)),
          True{}, Equal.cong(Nat, Bool, m => Nat.is_lt(Bytes.len(x), m), Nat.add(s, s), po.lim(j),
            Equal.sym(Nat, po.lim(j), Nat.add(s, s), po.nat.eq(po.lim(j), Nat.add(s, s), h5))), inv)))
      +g1 = List.append(&2, U32, got, Bytes.to_list(pc))
      %Equal.sym(Bytes(), String.take(x, s), pc, ep) :
        {RS.walk(e, Bytes.to_list(Bytes.append(Stream.chunk.hex(j), Bytes.append("\r\n", Bytes.append(_, Bytes.append("\r\n",
          go(d)))))), po.W5(h, got, left, o)) ==
          po.W5(h, List.append(&2, U32, got, Bytes.to_list(x)), lgo(Nat.sub(Bytes.len(x), s), cl), o) : RS.W}
      %Equal.sym(RS.W, RS.walk(e, Bytes.to_list(Bytes.append(Stream.chunk.hex(j), Bytes.append("\r\n", Bytes.append(pc,
          Bytes.append("\r\n", go(d)))))), po.W5(h, got, left, o)),
        RS.walk(e, Bytes.to_list(go(d)), po.W5(h, g1, cl, o)),
        po.pw(j, c, t, go(d), e, h, got, left, o, tab, hp, Bool.and_l(a, okgo(Nat.sub(Bytes.len(x), s), cl), ok))) :
        {_ == po.W5(h, List.append(&2, U32, got, Bytes.to_list(x)), lgo(Nat.sub(Bytes.len(x), s), cl), o) : RS.W}
      %Equal.sym(RS.W, RS.walk(e, Bytes.to_list(go(d)), po.W5(h, g1, cl, o)),
        po.W5(h, List.append(&2, U32, g1, Bytes.to_list(d)), lgo(Bytes.len(d), cl), o),
        ih(d, cl, g1, okr, invr)) :
        {_ == po.W5(h, List.append(&2, U32, got, Bytes.to_list(x)), lgo(Nat.sub(Bytes.len(x), s), cl), o) : RS.W}
      %Equal.sym(List<&2, U32>, List.append(&2, U32, g1, Bytes.to_list(d)),
        List.append(&2, U32, got, List.append(&2, U32, Bytes.to_list(pc), Bytes.to_list(d))),
        PP.app.assoc(U32, got, Bytes.to_list(pc), Bytes.to_list(d))) :
        {po.W5(h, _, lgo(Bytes.len(d), cl), o) ==
          po.W5(h, List.append(&2, U32, got, Bytes.to_list(x)), lgo(Nat.sub(Bytes.len(x), s), cl), o) : RS.W}
      %Equal.trans(List<&2, U32>, Bytes.to_list(x), List.append(&2, U32, Bytes.to_list(String.take(x, s)), Bytes.to_list(d)),
        List.append(&2, U32, Bytes.to_list(pc), Bytes.to_list(d)), po.split(x, s),
        Equal.cong(Bytes(), List<&2, U32>, q => List.append(&2, U32, Bytes.to_list(q), Bytes.to_list(d)), String.take(x, s), pc,
          ep)) :
        {po.W5(h, List.append(&2, U32, got, _), lgo(Bytes.len(d), cl), o) ==
          po.W5(h, List.append(&2, U32, got, Bytes.to_list(x)), lgo(Nat.sub(Bytes.len(x), s), cl), o) : RS.W}
      %Equal.sym(Nat, Bytes.len(d), Nat.sub(Bytes.len(x), s), po.drop.len(x, s)) :
        {po.W5(h, List.append(&2, U32, got, Bytes.to_list(x)), lgo(_, cl), o) ==
          po.W5(h, List.append(&2, U32, got, Bytes.to_list(x)), lgo(Nat.sub(Bytes.len(x), s), cl), o) : RS.W}
      {==}

# a chunk of 2^j at the front of x, if one fits, then the rest
def po.ca(fit: Bool, +j: Nat, +x: Bytes(), +e: R.Ask, +h: R.Head, +got: List<&2, U32>, +left: U32, +o: List<&2, U32>,
  go: Bytes() -> Bytes(), -okgo: Nat -> U32 -> Bool, -lgo: Nat -> U32 -> U32, +hj: {Nat.is_le(j, 14n) == True{} : Bool},
  +ef: {Nat.is_ge(Bytes.len(x), Stream.chunk.size(j)) == fit : Bool},
  +inv: {Nat.is_lt(Bytes.len(x), po.lim(j)) == True{} : Bool},
  +ok: {Laws.ok.at(fit, j, Bytes.len(x), left, okgo) == True{} : Bool}, ih: po.IH(j, e, h, o, go, okgo, lgo)) ->
  {RS.walk(e, Bytes.to_list(Stream.chunks.at(fit, j, x, go)), RS.W{RS.MChunk{h, R.ASize0{}, 0, got, left}, o}) ==
    RS.W{RS.MChunk{h, R.ASize0{}, 0, List.append(&2, U32, got, Bytes.to_list(x)), Laws.left.at(fit, j, Bytes.len(x), left, lgo)},
      o} : RS.W}:
  match fit:
    case True{}:
      po.ca.p(String.take(x, Stream.chunk.size(j)), j, x, e, h, got, left, o, go, okgo, lgo, hj, {==}, ef, inv, ok, ih,
        po.tab(j, hj), po.t5(j, po.tab(j, hj)))
    case False{}:
      +s = Stream.chunk.size(j)
      ih(x, left, got, ok, Equal.trans(Bool, Nat.is_lt(Bytes.len(x), s), Bool.not(Nat.is_ge(Bytes.len(x), s)), True{},
        Equal.sym(Bool, Bool.not(Nat.is_ge(Bytes.len(x), s)), Nat.is_lt(Bytes.len(x), s), po.ge.not(Bytes.len(x), s)),
        Equal.cong(Bool, Bool, q => Bool.not(q), Nat.is_ge(Bytes.len(x), s), False{}, ef)))

# the last bit: what is left of a write under one byte is nothing
def po.cg0(y: Bytes(), +e: R.Ask, +h: R.Head, +g: List<&2, U32>, +l: U32, +o: List<&2, U32>,
  iv: {Nat.is_lt(Bytes.len(y), Stream.chunk.size(0n)) == True{} : Bool}) ->
  {RS.walk(e, Bytes.to_list(""), RS.W{RS.MChunk{h, R.ASize0{}, 0, g, l}, o}) ==
    RS.W{RS.MChunk{h, R.ASize0{}, 0, List.append(&2, U32, g, Bytes.to_list(y)), l}, o} : RS.W}:
  match y:
    case SNil{}:
      Equal.cong(List<&2, U32>, RS.W, q => RS.W{RS.MChunk{h, R.ASize0{}, 0, q, l}, o}, g, List.append(&2, U32, g, Nil{}),
        Equal.sym(List<&2, U32>, List.append(&2, U32, g, Nil{}), g, PP.app.nil(U32, g)))
    case SCon{+c, +t}:
      Bool.no({RS.walk(e, Bytes.to_list(""), RS.W{RS.MChunk{h, R.ASize0{}, 0, g, l}, o}) ==
        RS.W{RS.MChunk{h, R.ASize0{}, 0, List.append(&2, U32, g, Bytes.to_list(SCon{c, t})), l}, o} : RS.W},
        Equal.trans(Bool, False{}, Nat.is_lt(Bytes.len(t), 0n), True{}, Equal.sym(Bool, Nat.is_lt(Bytes.len(t), 0n), False{},
          po.lt0(Bytes.len(t))),
          Equal.trans(Bool, Nat.is_lt(1n+Bytes.len(t), 1n), Nat.is_lt(Bytes.len(SCon{c, t}), 1n), True{},
            Equal.cong(Nat, Bool, n => Nat.is_lt(n, 1n), 1n+Bytes.len(t), Bytes.len(SCon{c, t}),
              Equal.sym(Nat, Bytes.len(SCon{c, t}), 1n+Bytes.len(t), po.blen(c, t))), iv)))

# LEMMA: a write of fewer than 2^(j+1) bytes, cut into chunks from 2^j
# down, each paid for, is read back as itself
def po.cg(j: Nat, +x: Bytes(), +e: R.Ask, +h: R.Head, +got: List<&2, U32>, +left: U32, +o: List<&2, U32>,
  +hj: {Nat.is_le(j, 14n) == True{} : Bool},
  +inv: {Nat.is_lt(Bytes.len(x), po.lim(j)) == True{} : Bool},
  +ok: {Laws.ok.go(j, Bytes.len(x), left) == True{} : Bool}) ->
  {RS.walk(e, Bytes.to_list(Stream.chunks.go(j, x)), RS.W{RS.MChunk{h, R.ASize0{}, 0, got, left}, o}) ==
    RS.W{RS.MChunk{h, R.ASize0{}, 0, List.append(&2, U32, got, Bytes.to_list(x)), Laws.left.go(j, Bytes.len(x), left)}, o} :
    RS.W}:
  match j:
    case 0n:
      po.ca(Nat.is_ge(Bytes.len(x), Stream.chunk.size(0n)), 0n, x, e, h, got, left, o, t => "", n2 => l => True{},
        n2 => l => l, hj, {==}, inv, ok, y => l => g => k => iv => po.cg0(y, e, h, g, l, o, iv))
    case 1n+(+i):
      po.ca(Nat.is_ge(Bytes.len(x), Stream.chunk.size(1n+i)), 1n+i, x, e, h, got, left, o, t => Stream.chunks.go(i, t),
        n2 => l => Laws.ok.go(i, n2, l), n2 => l => Laws.left.go(i, n2, l), hj, {==}, inv, ok,
        y => l => g => k => iv => po.cg(i, y, e, h, g, l, o, Nat.is_le_trans(i, 13n, 14n, hj, {==}),
          Equal.trans(Bool, Nat.is_lt(Bytes.len(y), po.lim(i)), Nat.is_lt(Bytes.len(y), Stream.chunk.size(1n+i)), True{},
            Equal.cong(Nat, Bool, m => Nat.is_lt(Bytes.len(y), m), po.lim(i), Stream.chunk.size(1n+i),
              po.nat.eq(po.lim(i), Stream.chunk.size(1n+i), po.t6(1n+i, po.tab(1n+i, hj)))), iv), k))

def po.le.up(r: Nat, +y: Nat, h: {Nat.is_le(r, y) == True{} : Bool}) -> {Nat.is_le(r, 1n+y) == True{} : Bool}:
  match r y:
    case 0n _:
      {==}
    case 1n+p 0n:
      Bool.no({Nat.is_le(1n+p, 1n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      po.le.up(p, q, h)

def po.le.dbl(q: Nat) -> {Nat.is_le(q, Nat.double(q)) == True{} : Bool}:
  match q:
    case 0n:
      {==}
    case 1n+(+r):
      po.le.up(r, Nat.double(r), po.le.dbl(r))

# n at most s, s not zero: n under twice s
def po.lt.dbl(n: Nat, s: Nat, h: {Nat.is_le(n, s) == True{} : Bool}, hs: {Nat.is_eq(s, 0n) == False{} : Bool}) ->
  {Nat.is_lt(n, Nat.double(s)) == True{} : Bool}:
  match n s:
    case 0n 0n:
      Bool.no({Nat.is_lt(0n, Nat.double(0n)) == True{} : Bool}, Equal.sym(Bool, True{}, False{}, hs))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Bool.no({Nat.is_lt(1n+p, Nat.double(0n)) == True{} : Bool}, h)
    case 1n+(+p) 1n+(+q):
      Equal.trans(Bool, Nat.is_lt(p, 1n+Nat.double(q)), Nat.is_le(p, Nat.double(q)), True{}, Nat.lt_succ(p, Nat.double(q)),
        Nat.is_le_trans(p, q, Nat.double(q), h, po.le.dbl(q)))

def po.nz14() -> {Nat.is_eq(Stream.chunk.size(14n), 0n) == False{} : Bool}:
  {==}

# a write Stream.emit takes whole is under the bound its cutting needs
def po.lim14(+n: Nat, h: {Nat.is_le(n, 16384n) == True{} : Bool}) -> {Nat.is_lt(n, po.lim(14n)) == True{} : Bool}:
  Nat.is_lt_le_trans(n, 16385n, po.lim(14n), Equal.trans(Bool, Nat.is_lt(n, 16385n), Nat.is_le(n, 16384n), True{},
    Nat.lt_succ(n, 16384n), h), {==})

# LEMMA: the last chunk, its digit paid for, ends the body
def po.last(+e: R.Ask, +h: R.Head, +got: List<&2, U32>, +left: U32, +o: List<&2, U32>,
  ok: {Laws.dig.ok([48], R.ASize0{}, 0, left) == True{} : Bool}) ->
  {RS.walk(e, Bytes.to_list(Stream.chunk.last()), po.W5(h, got, left, o)) ==
    RS.W{RS.MDone{RS.resp(h, got, False{}), Nil{}}, o} : RS.W}:
  %Equal.sym(RS.W, RS.walk(e, List.append(&2, U32, [48], Bytes.to_list("\r\n\r\n")), po.W5(h, got, left, o)),
    RS.walk(e, Bytes.to_list("\r\n\r\n"), RS.walk(e, [48], po.W5(h, got, left, o))),
    po.wapp(e, [48], Bytes.to_list("\r\n\r\n"), po.W5(h, got, left, o))) :
    {_ == RS.W{RS.MDone{RS.resp(h, got, False{}), Nil{}}, o} : RS.W}
  %Equal.sym(RS.W, RS.walk(e, [48], po.W5(h, got, left, o)),
    RS.W{RS.MChunk{h, po.dig.at([48], R.ASize0{}), Laws.dig.val([48], R.ASize0{}, 0), got, Laws.dig.left([48], left)}, o},
    po.dw([48], R.ASize0{}, 0, left, e, h, got, o, ok)) :
    {RS.walk(e, Bytes.to_list("\r\n\r\n"), _) == RS.W{RS.MDone{RS.resp(h, got, False{}), Nil{}}, o} : RS.W}
  {==}

# LEMMA: a chunked body of small writes, each paid for, is read back as
# the writes joined, and it ends
def po.bw(ws: List<&2, Bytes()>, +e: R.Ask, +h: R.Head, +got: List<&2, U32>, +left: U32, +o: List<&2, U32>,
  +sm: {Laws.small(ws) == True{} : Bool}, +fit: {Laws.fits(ws, left) == True{} : Bool}) ->
  {RS.walk(e, Bytes.to_list(Stream.emits(ws, Stream.Sent{Stream.MChunked{}, None{}})), po.W5(h, got, left, o)) ==
    RS.W{RS.MDone{RS.resp(h, List.append(&2, U32, got, Bytes.to_list(Bytes.concat(ws))), False{}), Nil{}}, o} : RS.W}:
  match ws:
    case Nil{}:
      %Equal.sym(List<&2, U32>, List.append(&2, U32, got, Nil{}), got, PP.app.nil(U32, got)) :
        {RS.walk(e, Bytes.to_list(Stream.chunk.last()), po.W5(h, got, left, o)) ==
          RS.W{RS.MDone{RS.resp(h, _, False{}), Nil{}}, o} : RS.W}
      po.last(e, h, got, left, o, fit)
    case Con{+x, +t}:
      +rest = Stream.emits(t, Stream.Sent{Stream.MChunked{}, None{}})
      +g2 = List.append(&2, U32, got, Bytes.to_list(x))
      +tgt : RS.W = RS.W{RS.MDone{RS.resp(h, List.append(&2, U32, got, Bytes.to_list(Bytes.concat(Con{x, t}))), False{}), Nil{}}, o}
      %Equal.sym(Bool, Nat.is_le(Bytes.len(x), Stream.emit.max()), True{}, Bool.and_l(Nat.is_le(Bytes.len(x), Stream.emit.max()), Laws.small(t), sm)) :
        {RS.walk(e, Bytes.to_list(Stream.emits.on(Stream.emit.chunked(_, x), s2 => Stream.emits(t, s2))), po.W5(h, got, left, o)) ==
          tgt : RS.W}
      %Equal.sym(RS.W, RS.walk(e, Bytes.to_list(Bytes.append(Stream.chunks(x), rest)), po.W5(h, got, left, o)),
        RS.walk(e, Bytes.to_list(rest), RS.walk(e, Bytes.to_list(Stream.chunks(x)), po.W5(h, got, left, o))),
        po.wb(e, Stream.chunks(x), rest, po.W5(h, got, left, o))) :
        {_ == tgt : RS.W}
      %Equal.sym(RS.W, RS.walk(e, Bytes.to_list(Stream.chunks(x)), po.W5(h, got, left, o)), po.W5(h, g2, Laws.left.go(14n, Bytes.len(x), left), o),
        po.cg(14n, x, e, h, got, left, o, {==}, po.lim14(Bytes.len(x), Bool.and_l(Nat.is_le(Bytes.len(x), Stream.emit.max()),
          Laws.small(t), sm)), Bool.and_l(Laws.ok.go(14n, Bytes.len(x), left), Laws.fits(t, Laws.left.go(14n, Bytes.len(x), left)), fit))) :
        {RS.walk(e, Bytes.to_list(rest), _) == tgt : RS.W}
      %Equal.sym(RS.W, RS.walk(e, Bytes.to_list(rest), po.W5(h, g2, Laws.left.go(14n, Bytes.len(x), left), o)),
        RS.W{RS.MDone{RS.resp(h, List.append(&2, U32, g2, Bytes.to_list(Bytes.concat(t))), False{}), Nil{}}, o},
        po.bw(t, e, h, g2, Laws.left.go(14n, Bytes.len(x), left), o, po.and.r(Nat.is_le(Bytes.len(x), Stream.emit.max()), Laws.small(t), sm), po.and.r(Laws.ok.go(14n, Bytes.len(x), left), Laws.fits(t, Laws.left.go(14n, Bytes.len(x), left)), fit))) :
        {_ == tgt : RS.W}
      %Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, got, Bytes.to_list(x)), Bytes.to_list(Bytes.concat(t))),
        List.append(&2, U32, got, List.append(&2, U32, Bytes.to_list(x), Bytes.to_list(Bytes.concat(t)))),
        PP.app.assoc(U32, got, Bytes.to_list(x), Bytes.to_list(Bytes.concat(t)))) :
        {RS.W{RS.MDone{RS.resp(h, _, False{}), Nil{}}, o} == tgt : RS.W}
      %Bytes.to_list_append(x, Bytes.concat(t)) :
        {RS.W{RS.MDone{RS.resp(h, List.append(&2, U32, got, _), False{}), Nil{}}, o} == tgt : RS.W}
      {==}

# The head of a chunked response
# ------------------------------

def po.split3(a: Bool, b: Bool, -c: Bool, h: {(a && b && c) == True{} : Bool}) ->
  {a == True{} : Bool} & {b == True{} : Bool} & {c == True{} : Bool}:
  match a b:
    case True{} True{}:
      ({==}, ({==}, h))
    case False{} _:
      Bool.no({False{} == True{} : Bool} & {b == True{} : Bool} & {c == True{} : Bool}, h)
    case True{} False{}:
      Bool.no({True{} == True{} : Bool} & {False{} == True{} : Bool} & {c == True{} : Bool}, h)

def po.split5(a: Bool, b: Bool, c: Bool, d: Bool, -f: Bool, h: {(a && b && c && d && f) == True{} : Bool}) ->
  {a == True{} : Bool} & {b == True{} : Bool} & {c == True{} : Bool} & {d == True{} : Bool} & {f == True{} : Bool}:
  match a b c d:
    case True{} True{} True{} True{}:
      ({==}, ({==}, ({==}, ({==}, h))))
    case False{} _ _ _:
      Bool.no({False{} == True{} : Bool} & {b == True{} : Bool} & {c == True{} : Bool} & {d == True{} : Bool} &
        {f == True{} : Bool}, h)
    case True{} False{} _ _:
      Bool.no({True{} == True{} : Bool} & {False{} == True{} : Bool} & {c == True{} : Bool} & {d == True{} : Bool} &
        {f == True{} : Bool}, h)
    case True{} True{} False{} _:
      Bool.no({True{} == True{} : Bool} & {True{} == True{} : Bool} & {False{} == True{} : Bool} & {d == True{} : Bool} &
        {f == True{} : Bool}, h)
    case True{} True{} True{} False{}:
      Bool.no({True{} == True{} : Bool} & {True{} == True{} : Bool} & {True{} == True{} : Bool} & {False{} == True{} : Bool} &
        {f == True{} : Bool}, h)

def po.and4(a: Bool, b: Bool, c: Bool, -d: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool},
  hc: {c == True{} : Bool}, hd: {d == True{} : Bool}) -> {(a && b && c && d) == True{} : Bool}:
  match a b c:
    case True{} True{} True{}:
      hd
    case False{} _ _:
      Bool.no({(False{} && b && c && d) == True{} : Bool}, ha)
    case True{} False{} _:
      Bool.no({(True{} && False{} && c && d) == True{} : Bool}, hb)
    case True{} True{} False{}:
      Bool.no({(True{} && True{} && False{} && d) == True{} : Bool}, hc)

def po.not.true(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Bool.no({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def po.bapp.nil(a: Bytes()) -> {Bytes.append(a, "") == a : Bytes()}:
  match a:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      Equal.cong(Bytes(), Bytes(), y => SCon{c, y}, Bytes.append(t, ""), t, po.bapp.nil(t))

# the 500 passes rvalid, to HEAD and to anything else
def po.e500.ok(head: Bool) -> {X.rvalid(head, 500, X.rsp.fin(head, 500, Http.e500.head(), Http.e500.body())) == True{} : Bool}:
  match head:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.ws_version(key, up, cu, ver, h, get, offered, proto):
  %Equal.sym(Bool, Pair.fst(Bool, Bytes(), Eng.up.asked(Eng.Asks{key, up, cu, ver})), False{}, EP.no13(key, up, cu, ver, h)) :
    {H.s.answer(get, _, key, offered, proto) == H.SNo{426} : H.Sv}
  ws.426(get, key, offered, proto)

def Laws.ws_route_methods(up, m, pat, h):
  {==}

def Laws.ws_route_vectors():
  {==}

# a writer with no body sends nothing, whatever is written
def po.emits.none(ws: List<&2, Bytes()>) -> {Stream.emits(ws, Stream.Sent{Stream.MNone{}, None{}}) == "" : Bytes()}:
  match ws:
    case Nil{}:
      {==}
    case Con{x, t}:
      Laws.pour_quiet(Stream.MNone{}, Stream.ENone{}, t)

# the head a chunked response's fields leave: HTTP/1.1, the code, no
# length, chunked
def po.H1(+code: U32) -> R.Head:
  R.Head{False{}, code, None{}, True{}, False{}, False{}}

# the Transfer-Encoding line is read as chunked
def po.te.line(+code: U32, +rest: List<&2, U32>) ->
  {RS.walk(X.rask(False{}), List.append(&2, U32, PP.FLl(Wr.Field{"transfer-encoding", "chunked"}), Con{13, Con{10, rest}}),
    RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}) ==
    RS.walk(X.rask(False{}), rest, RS.W{RS.MField{po.H1(code), Nil{}}, Nil{}}) : RS.W}:
  {==}

# with a code of 200 or more, not 204 or 304, and chunked: the framing is
# chunked
def po.rfr.te(+code: U32, +cl: Bool, +ka: Bool, hlt: {U32.is_lt(code, 200) == False{} : Bool},
  hnb: {(U32.is_eq(code, 204) || U32.is_eq(code, 304)) == False{} : Bool}) ->
  {RS.framing(X.rask(False{}), R.Head{False{}, code, None{}, True{}, cl, ka}) == R.FChunked{} : R.Frame}:
  Equal.trans(R.Frame, RS.framing(X.rask(False{}), R.Head{False{}, code, None{}, True{}, cl, ka}),
    RS.frame.pick(U32.is_eq(code, 204) || U32.is_eq(code, 304), R.FNone{}, R.FChunked{}), R.FChunked{},
    Equal.cong(Bool, R.Frame, b => RS.frame.pick(b && Bool.not(U32.is_eq(code, 101)), R.FNext{},
      RS.frame.pick(False{} || b || U32.is_eq(code, 204) || U32.is_eq(code, 304), R.FNone{}, R.FChunked{})),
      U32.is_lt(code, 200), False{}, hlt),
    Equal.cong(Bool, R.Frame, b => RS.frame.pick(b, R.FNone{}, R.FChunked{}), U32.is_eq(code, 204) || U32.is_eq(code, 304),
      False{}, hnb))

def po.te.end.at(+code: U32, +cl: Bool, +ka: Bool, +rest: List<&2, U32>, hlt: {U32.is_lt(code, 200) == False{} : Bool},
  hnb: {(U32.is_eq(code, 204) || U32.is_eq(code, 304)) == False{} : Bool}) ->
  {RS.walk(X.rask(False{}), Con{13, Con{10, rest}}, RS.W{RS.MField{R.Head{False{}, code, None{}, True{}, cl, ka}, Nil{}}, Nil{}}) ==
    RS.walk(X.rask(False{}), rest, po.W5(R.Head{False{}, code, None{}, True{}, cl, ka}, Nil{}, 268435455, Nil{})) : RS.W}:
  Equal.cong(R.Frame, RS.W, f => RS.walk(X.rask(False{}), rest, RS.head.at(X.rask(False{}), f,
    R.Head{False{}, code, None{}, True{}, cl, ka}, Nil{})), RS.framing(X.rask(False{}), R.Head{False{}, code, None{}, True{}, cl, ka}),
    R.FChunked{}, po.rfr.te(code, cl, ka, hlt, hnb))

# the blank line: the body is chunked, from its first byte
def po.te.end(closing: Bool, +code: U32, +rest: List<&2, U32>, hlt: {U32.is_lt(code, 200) == False{} : Bool},
  hnb: {(U32.is_eq(code, 204) || U32.is_eq(code, 304)) == False{} : Bool}) ->
  {RS.walk(X.rask(False{}), Con{13, Con{10, rest}}, RS.W{RS.MField{PP.rhc(po.H1(code), closing, False{}), Nil{}}, Nil{}}) ==
    RS.walk(X.rask(False{}), rest, po.W5(PP.rhc(po.H1(code), closing, False{}), Nil{}, 268435455, Nil{})) : RS.W}:
  match closing:
    case True{}:
      po.te.end.at(code, True{}, False{}, rest, hlt, hnb)
    case False{}:
      po.te.end.at(code, False{}, False{}, rest, hlt, hnb)

# the response read: the code, HTTP/1.1, closing as the server closes
def po.resp.te(closing: Bool, +code: U32, +got: List<&2, U32>, h101: {U32.is_eq(code, 101) == False{} : Bool}) ->
  {RS.resp(PP.rhc(po.H1(code), closing, False{}), got, False{}) == R.Resp{code, False{}, closing, Bytes.from_list(got)} : R.Resp}:
  match closing:
    case True{}:
      {==}
    case False{}:
      Equal.cong(Bool, R.Resp, b => R.Resp{code, False{}, False{} || (False{} && Bool.not(False{})) || b || False{},
        Bytes.from_list(got)}, U32.is_eq(code, 101), False{}, h101)

# what rok.code says, taken apart
def po.C5(+cd: Bytes(), +code: U32) -> Type:
  {X.rok.all(RS.TDig{}, cd) == True{} : Bool} & {RS.code.whole(Bytes.to_list(cd)) == True{} : Bool} &
    {U32.is_eq(RS.num(Bytes.to_list(cd)), code) == True{} : Bool} & {Bool.not(U32.is_lt(code, 200)) == True{} : Bool} &
    {Bool.not(U32.is_eq(code, 101)) == True{} : Bool}

def po.c5(+cd: Bytes(), +code: U32, h: {X.rok.code(cd, code) == True{} : Bool}) -> po.C5(cd, code):
  po.split5(X.rok.all(RS.TDig{}, cd), RS.code.whole(Bytes.to_list(cd)), U32.is_eq(RS.num(Bytes.to_list(cd)), code),
    Bool.not(U32.is_lt(code, 200)), Bool.not(U32.is_eq(code, 101)), h)

# LEMMA: a chunked response whose head passed the check, sent, is read
# back to its end: the handler's status, the writes joined
def po.walk.te(+cd: Bytes(), +why: Bytes(), +fs: List<&2, Wr.Field>, +closing: Bool, +code: U32, +ws: List<&2, Bytes()>,
  sm: {Laws.small(ws) == True{} : Bool}, fit: {Laws.fits(ws, R.ask.cap(X.rask(False{}))) == True{} : Bool},
  sp: po.C5(cd, code), +s2: {X.rok.all(RS.TVal{}, why) == True{} : Bool},
  s3: {X.rok.fields(fs) == True{} : Bool}, +enb: {(U32.is_eq(code, 204) || U32.is_eq(code, 304)) == False{} : Bool}) ->
  {RS.walk(X.rask(False{}), Bytes.to_list(X.rser(X.Rsp{cd, why, List.append(&2, Wr.Field, fs, Stream.te()), "",
    Stream.emits(ws, Stream.Sent{Stream.MChunked{}, None{}}), False{}}, X.conn.val(closing, False{}))), RS.w.new()) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bytes.concat(ws)}, Nil{}}, Nil{}} : RS.W}:
  (ad, k1) = sp
  (cw, k2) = k1
  (heq, k3) = k2
  (nlt, n101) = k3
  +e = X.rask(False{})
  +conn = X.conn.val(closing, False{})
  +b = Stream.emits(ws, Stream.Sent{Stream.MChunked{}, None{}})
  +fs2 = List.append(&2, Wr.Field, fs, Stream.te())
  +t2 : List<&2, U32> = Con{13, Con{10, Bytes.to_list(b)}}
  +rest1 = List.append(&2, U32, PP.FLSl(X.rall(fs2, "", conn)), t2)
  +rc = X.rconf(conn)
  +tef : Wr.Field = Wr.Field{"transfer-encoding", "chunked"}
  +r5 = List.append(&2, U32, PP.FLSl(Con{tef, rc}), t2)
  +r7 = List.append(&2, U32, PP.FLSl(rc), t2)
  +hn = R.head.new(False{}, code)
  +h2 = PP.rhc(po.H1(code), closing, False{})
  +tgt : RS.W = RS.W{RS.MDone{R.Resp{code, False{}, closing, Bytes.concat(ws)}, Nil{}}, Nil{}}
  %Equal.sym(List<&2, U32>, Bytes.to_list(X.rser(X.Rsp{cd, why, fs2, "", b, False{}}, conn)),
    PP.RSERl(cd, why, fs2, "", conn, Bool.pick(Bytes(), False{}, "", b)), PP.rser.list(cd, why, fs2, "", conn, b, False{})) :
    {RS.walk(e, _, RS.w.new()) == tgt : RS.W}
  %Equal.sym(RS.W, RS.walk(e, List.append(&2, U32, PP.SLl(cd, why), Con{13, Con{10, rest1}}), RS.W{RS.MStatus{Nil{}}, Nil{}}),
    RS.walk(e, rest1, RS.W{RS.MField{R.head.new(False{}, RS.num(Bytes.to_list(cd))), Nil{}}, Nil{}}),
    PP.rline.st(cd, why, rest1, e, Nil{}, ad, cw, s2)) :
    {_ == tgt : RS.W}
  %Equal.sym(U32, RS.num(Bytes.to_list(cd)), code, PP.u32.eq(RS.num(Bytes.to_list(cd)), code, heq)) :
    {RS.walk(e, rest1, RS.W{RS.MField{R.head.new(False{}, _), Nil{}}, Nil{}}) == tgt : RS.W}
  %Equal.sym(List<&2, U32>, rest1, List.append(&2, U32, PP.FLSl(fs), r5),
    Equal.trans(List<&2, U32>, rest1, List.append(&2, U32, List.append(&2, U32, PP.FLSl(fs), PP.FLSl(Con{tef, rc})), t2),
      List.append(&2, U32, PP.FLSl(fs), r5),
      Equal.trans(List<&2, U32>, rest1, List.append(&2, U32, PP.FLSl(List.append(&2, Wr.Field, fs, Con{tef, rc})), t2),
        List.append(&2, U32, List.append(&2, U32, PP.FLSl(fs), PP.FLSl(Con{tef, rc})), t2),
        Equal.cong(List<&2, Wr.Field>, List<&2, U32>, q => List.append(&2, U32, PP.FLSl(q), t2), List.append(&2, Wr.Field, fs2, rc),
          List.append(&2, Wr.Field, fs, Con{tef, rc}), PP.app.assoc(Wr.Field, fs, Stream.te(), rc)),
        Equal.cong(List<&2, U32>, List<&2, U32>, q => List.append(&2, U32, q, t2),
          PP.FLSl(List.append(&2, Wr.Field, fs, Con{tef, rc})), List.append(&2, U32, PP.FLSl(fs), PP.FLSl(Con{tef, rc})),
          PP.fls.app(fs, Con{tef, rc}))),
      PP.app.assoc(U32, PP.FLSl(fs), PP.FLSl(Con{tef, rc}), t2))) :
    {RS.walk(e, _, RS.W{RS.MField{hn, Nil{}}, Nil{}}) == tgt : RS.W}
  %Equal.sym(RS.W, RS.walk(e, List.append(&2, U32, PP.FLSl(fs), r5), RS.W{RS.MField{hn, Nil{}}, Nil{}}),
    RS.walk(e, r5, RS.W{RS.MField{hn, Nil{}}, Nil{}}), PP.rfields.walk(fs, r5, hn, e, Nil{}, s3)) :
    {_ == tgt : RS.W}
  %Equal.sym(List<&2, U32>, r5, List.append(&2, U32, PP.FLl(tef), Con{13, Con{10, r7}}),
    PP.app.assoc(U32, PP.FLl(tef), Con{13, Con{10, PP.FLSl(rc)}}, t2)) :
    {RS.walk(e, _, RS.W{RS.MField{hn, Nil{}}, Nil{}}) == tgt : RS.W}
  %Equal.sym(RS.W, RS.walk(e, List.append(&2, U32, PP.FLl(tef), Con{13, Con{10, r7}}), RS.W{RS.MField{hn, Nil{}}, Nil{}}),
    RS.walk(e, r7, RS.W{RS.MField{po.H1(code), Nil{}}, Nil{}}), po.te.line(code, r7)) :
    {_ == tgt : RS.W}
  %Equal.sym(RS.W, RS.walk(e, r7, RS.W{RS.MField{po.H1(code), Nil{}}, Nil{}}),
    RS.walk(e, t2, RS.W{RS.MField{h2, Nil{}}, Nil{}}), PP.rconn(closing, False{}, po.H1(code), t2, e, Nil{})) :
    {_ == tgt : RS.W}
  %Equal.sym(RS.W, RS.walk(e, t2, RS.W{RS.MField{h2, Nil{}}, Nil{}}),
    RS.walk(e, Bytes.to_list(b), po.W5(h2, Nil{}, 268435455, Nil{})),
    po.te.end(closing, code, Bytes.to_list(b), po.not.true(U32.is_lt(code, 200), nlt), enb)) :
    {_ == tgt : RS.W}
  %Equal.sym(RS.W, RS.walk(e, Bytes.to_list(b), po.W5(h2, Nil{}, 268435455, Nil{})),
    RS.W{RS.MDone{RS.resp(h2, List.append(&2, U32, Nil{}, Bytes.to_list(Bytes.concat(ws))), False{}), Nil{}}, Nil{}},
    po.bw(ws, e, h2, Nil{}, 268435455, Nil{}, sm, fit)) :
    {_ == tgt : RS.W}
  %Equal.sym(R.Resp, RS.resp(h2, Bytes.to_list(Bytes.concat(ws)), False{}),
    R.Resp{code, False{}, closing, Bytes.from_list(Bytes.to_list(Bytes.concat(ws)))},
    po.resp.te(closing, code, Bytes.to_list(Bytes.concat(ws)), po.not.true(U32.is_eq(code, 101), n101))) :
    {RS.W{RS.MDone{_, Nil{}}, Nil{}} == tgt : RS.W}
  %Equal.sym(Bytes(), Bytes.from_list(Bytes.to_list(Bytes.concat(ws))), Bytes.concat(ws), PP.bytes.rt(Bytes.concat(ws))) :
    {RS.W{RS.MDone{R.Resp{code, False{}, closing, _}, Nil{}}, Nil{}} == tgt : RS.W}
  {==}

# pour_chunked
# ------------

def po.R500(+closing: Bool) -> Bytes():
  X.reply(Some{X.rsp.fin(False{}, 500, Http.e500.head(), Http.e500.body())}, False{}, closing, False{})

# a head that failed the check: the 500, and nothing after it
def po.pc500(+closing: Bool, +code: U32, +ws: List<&2, Bytes()>) ->
  {RS.response(X.rask(False{}), Bytes.to_list(Bytes.append(po.R500(closing),
    Stream.emits(ws, Stream.Sent{Stream.MNone{}, Some{Stream.EBad{}}})))) ==
    Laws.sent(False{}, closing, code, False{}, Bytes.concat(ws)) : R.Look}:
  %Equal.sym(Bytes(), Stream.emits(ws, Stream.Sent{Stream.MNone{}, Some{Stream.EBad{}}}), "",
    Laws.pour_quiet(Stream.MNone{}, Stream.EBad{}, ws)) :
    {RS.response(X.rask(False{}), Bytes.to_list(Bytes.append(po.R500(closing), _))) ==
      Laws.sent(False{}, closing, code, False{}, Bytes.concat(ws)) : R.Look}
  %Equal.sym(Bytes(), Bytes.append(po.R500(closing), ""), po.R500(closing), po.bapp.nil(po.R500(closing))) :
    {RS.response(X.rask(False{}), Bytes.to_list(_)) == Laws.sent(False{}, closing, code, False{}, Bytes.concat(ws)) : R.Look}
  PP.rr.h(Http.e500.head(), False{}, 500, Http.e500.body(), closing, False{}, po.e500.ok(False{}))

def po.C3(+cd: Bytes(), +code: U32, +why: Bytes(), fs: List<&2, Wr.Field>) -> Type:
  {X.rok.code(cd, code) == True{} : Bool} & {X.rok.all(RS.TVal{}, why) == True{} : Bool} & {X.rok.fields(fs) == True{} : Bool}

# a 204 or 304: the head alone
def po.pc.nb(+cd: Bytes(), +why: Bytes(), +fs: List<&2, Wr.Field>, +closing: Bool, +code: U32, +ws: List<&2, Bytes()>,
  sp: po.C3(cd, code, why, fs), +enb: {(U32.is_eq(code, 204) || U32.is_eq(code, 304)) == True{} : Bool}) ->
  {RS.response(X.rask(False{}), Bytes.to_list(Bytes.append(Stream.rhd.bytes(cd, why, fs, "", X.conn.val(closing, False{})),
    Stream.emits(ws, Stream.Sent{Stream.MNone{}, None{}})))) ==
    Laws.sent(False{}, closing, code, True{}, Bytes.concat(ws)) : R.Look}:
  (s1, k) = sp
  (s2, s3) = k
  +hb = Stream.rhd.bytes(cd, why, fs, "", X.conn.val(closing, False{}))
  +rbl = X.rbodyless(False{}, code)
  %Equal.sym(Bytes(), Stream.emits(ws, Stream.Sent{Stream.MNone{}, None{}}), "", po.emits.none(ws)) :
    {RS.response(X.rask(False{}), Bytes.to_list(Bytes.append(hb, _))) ==
      Laws.sent(False{}, closing, code, True{}, Bytes.concat(ws)) : R.Look}
  %Equal.cong(Bool, Bytes(), b => Bytes.append(hb, Bool.pick(Bytes(), b, "", "")), rbl, True{}, enb) :
    {RS.response(X.rask(False{}), Bytes.to_list(_)) == Laws.sent(False{}, closing, code, True{}, Bytes.concat(ws)) : R.Look}
  Equal.trans(R.Look, RS.response(X.rask(False{}), Bytes.to_list(X.rser(X.Rsp{cd, why, fs, "", "", rbl}, X.conn.val(closing, False{})))),
    R.Look{Nil{}, R.Final{R.Resp{code, False{}, closing, ""}, ""}}, Laws.sent(False{}, closing, code, True{}, Bytes.concat(ws)),
    Equal.trans(R.Look, RS.response(X.rask(False{}), Bytes.to_list(X.rser(X.Rsp{cd, why, fs, "", "", rbl}, X.conn.val(closing, False{})))),
      RS.finish(X.rask(False{}), RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), rbl, "", "")}, Nil{}}, Nil{}}),
      R.Look{Nil{}, R.Final{R.Resp{code, False{}, closing, ""}, ""}},
      Equal.cong(RS.W, R.Look, w => RS.finish(X.rask(False{}), w),
        RS.walk(X.rask(False{}), Bytes.to_list(X.rser(X.Rsp{cd, why, fs, "", "", rbl}, X.conn.val(closing, False{}))), RS.w.new()),
        RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), rbl, "", "")}, Nil{}}, Nil{}},
        PP.rmain(cd, why, fs, "", False{}, code, "", closing, False{},
          po.and4(X.rok.code(cd, code), X.rok.all(RS.TVal{}, why), X.rok.fields(fs), X.rok.len(False{}, rbl, "", ""), s1, s2, s3, enb))),
      Equal.cong(Bool, R.Look, b => R.Look{Nil{}, R.Final{R.Resp{code, False{}, closing, Bool.pick(Bytes(), b, "", "")}, ""}}, rbl,
        True{}, enb)),
    Equal.sym(R.Look, Laws.sent(False{}, closing, code, True{}, Bytes.concat(ws)), R.Look{Nil{}, R.Final{R.Resp{code, False{}, closing, ""}, ""}},
      Equal.cong(Bool, R.Look, b => R.Look{Nil{}, R.Final{R.Resp{code, False{}, closing, Bool.pick(Bytes(), b, "", Bytes.concat(ws))}, ""}},
        rbl, True{}, enb)))

# chunked: the head, the writes, the last chunk
def po.pc.te(+cd: Bytes(), +why: Bytes(), +fs: List<&2, Wr.Field>, +closing: Bool, +code: U32, +ws: List<&2, Bytes()>,
  sm: {Laws.small(ws) == True{} : Bool}, fit: {Laws.fits(ws, R.ask.cap(X.rask(False{}))) == True{} : Bool},
  sp: po.C3(cd, code, why, fs), +enb: {(U32.is_eq(code, 204) || U32.is_eq(code, 304)) == False{} : Bool}) ->
  {RS.response(X.rask(False{}), Bytes.to_list(Bytes.append(Stream.rhd.bytes(cd, why, List.append(&2, Wr.Field, fs, Stream.te()), "",
    X.conn.val(closing, False{})), Stream.emits(ws, Stream.Sent{Stream.MChunked{}, None{}})))) ==
    Laws.sent(False{}, closing, code, True{}, Bytes.concat(ws)) : R.Look}:
  (s1, k) = sp
  (s2, s3) = k
  +fs2 = List.append(&2, Wr.Field, fs, Stream.te())
  +b = Stream.emits(ws, Stream.Sent{Stream.MChunked{}, None{}})
  Equal.trans(R.Look, RS.finish(X.rask(False{}), RS.walk(X.rask(False{}), Bytes.to_list(X.rser(X.Rsp{cd, why, fs2, "", b, False{}},
      X.conn.val(closing, False{}))), RS.w.new())),
    R.Look{Nil{}, R.Final{R.Resp{code, False{}, closing, Bytes.concat(ws)}, ""}}, Laws.sent(False{}, closing, code, True{}, Bytes.concat(ws)),
    Equal.cong(RS.W, R.Look, w => RS.finish(X.rask(False{}), w),
      RS.walk(X.rask(False{}), Bytes.to_list(X.rser(X.Rsp{cd, why, fs2, "", b, False{}}, X.conn.val(closing, False{}))), RS.w.new()),
      RS.W{RS.MDone{R.Resp{code, False{}, closing, Bytes.concat(ws)}, Nil{}}, Nil{}},
      po.walk.te(cd, why, fs, closing, code, ws, sm, fit, po.c5(cd, code, s1), s2, s3, enb)),
    Equal.sym(R.Look, Laws.sent(False{}, closing, code, True{}, Bytes.concat(ws)),
      R.Look{Nil{}, R.Final{R.Resp{code, False{}, closing, Bytes.concat(ws)}, ""}},
      Equal.cong(Bool, R.Look, b2 => R.Look{Nil{}, R.Final{R.Resp{code, False{}, closing, Bool.pick(Bytes(), b2, "", Bytes.concat(ws))},
        ""}}, U32.is_eq(code, 204) || U32.is_eq(code, 304), False{}, enb)))

def po.pc(ok: Bool, nb: Bool, +cd: Bytes(), +why: Bytes(), +fs: List<&2, Wr.Field>, +closing: Bool, +code: U32,
  +ws: List<&2, Bytes()>, sm: {Laws.small(ws) == True{} : Bool},
  fit: {Laws.fits(ws, R.ask.cap(X.rask(False{}))) == True{} : Bool},
  +eok: {Stream.rhd.ok(cd, code, why, fs) == ok : Bool},
  +enb: {(U32.is_eq(code, 204) || U32.is_eq(code, 304)) == nb : Bool}) ->
  {RS.response(X.rask(False{}), Bytes.to_list(Stream.poured.at(Stream.opening.none.at(nb, False{}, False{}, False{}, closing, False{},
    code, cd, why, fs), ws))) == Laws.sent(False{}, closing, code, ok, Bytes.concat(ws)) : R.Look}:
  match ok nb:
    case False{} True{}:
      %Equal.sym(Bool, Stream.rhd.ok(cd, code, why, fs), False{}, eok) :
        {RS.response(X.rask(False{}), Bytes.to_list(Stream.poured.at(Stream.opening.ok(_, False{}, closing, False{},
          Stream.rhd.bytes(cd, why, fs, "", X.conn.val(closing, False{})), Stream.MNone{}), ws))) ==
          Laws.sent(False{}, closing, code, False{}, Bytes.concat(ws)) : R.Look}
      po.pc500(closing, code, ws)
    case False{} False{}:
      %Equal.sym(Bool, Stream.rhd.ok(cd, code, why, fs), False{}, eok) :
        {RS.response(X.rask(False{}), Bytes.to_list(Stream.poured.at(Stream.opening.ok(_, False{}, closing, False{},
          Stream.rhd.bytes(cd, why, List.append(&2, Wr.Field, fs, Stream.te()), "", X.conn.val(closing, False{})),
          Stream.mode.body(False{}, Stream.MChunked{})), ws))) ==
          Laws.sent(False{}, closing, code, False{}, Bytes.concat(ws)) : R.Look}
      po.pc500(closing, code, ws)
    case True{} True{}:
      %Equal.sym(Bool, Stream.rhd.ok(cd, code, why, fs), True{}, eok) :
        {RS.response(X.rask(False{}), Bytes.to_list(Stream.poured.at(Stream.opening.ok(_, False{}, closing, False{},
          Stream.rhd.bytes(cd, why, fs, "", X.conn.val(closing, False{})), Stream.MNone{}), ws))) ==
          Laws.sent(False{}, closing, code, True{}, Bytes.concat(ws)) : R.Look}
      po.pc.nb(cd, why, fs, closing, code, ws, po.split3(X.rok.code(cd, code), X.rok.all(RS.TVal{}, why), X.rok.fields(fs), eok),
        enb)
    case True{} False{}:
      %Equal.sym(Bool, Stream.rhd.ok(cd, code, why, fs), True{}, eok) :
        {RS.response(X.rask(False{}), Bytes.to_list(Stream.poured.at(Stream.opening.ok(_, False{}, closing, False{},
          Stream.rhd.bytes(cd, why, List.append(&2, Wr.Field, fs, Stream.te()), "", X.conn.val(closing, False{})),
          Stream.mode.body(False{}, Stream.MChunked{})), ws))) ==
          Laws.sent(False{}, closing, code, True{}, Bytes.concat(ws)) : R.Look}
      po.pc.te(cd, why, fs, closing, code, ws, sm, fit, po.split3(X.rok.code(cd, code), X.rok.all(RS.TVal{}, why),
        X.rok.fields(fs), eok), enb)

def po.pc.h(h: X.RHead, +closing: Bool, +code: U32, +ws: List<&2, Bytes()>, sm: {Laws.small(ws) == True{} : Bool},
  fit: {Laws.fits(ws, R.ask.cap(X.rask(False{}))) == True{} : Bool}) ->
  {RS.response(X.rask(False{}), Bytes.to_list(Stream.poured.at(Stream.opening.none(False{}, closing, False{}, code,
    U32.is_eq(code, 204) || U32.is_eq(code, 304), h), ws))) ==
    Laws.sent(False{}, closing, code, Laws.pour.ok(code, h), Bytes.concat(ws)) : R.Look}:
  match h:
    case X.RHead{+cd, +why, +fs, hl}:
      po.pc(Stream.rhd.ok(cd, code, why, fs), U32.is_eq(code, 204) || U32.is_eq(code, 304), cd, why, fs, closing, code, ws, sm, fit,
        {==}, {==})

def Laws.pour_chunked(closing, code, hs, ws, sm, fit):
  po.pc.h(Http.rhead(code, hs, ""), closing, code, ws, sm, fit)

# pour_length, pour_capped
# ------------------------

def po.le0(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def po.eq.refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      po.eq.refl(p)

def po.le.add(a: Nat, +b: Nat) -> {Nat.is_le(a, Nat.add(a, b)) == True{} : Bool}:
  match a:
    case 0n:
      po.le0(b)
    case 1n+p:
      po.le.add(p, b)

def po.sub.add.l(a: Nat, +b: Nat) -> {Nat.sub(Nat.add(a, b), a) == b : Nat}:
  match a:
    case 0n:
      po.sub0(b)
    case 1n+p:
      po.sub.add.l(p, b)

# a over n, b over what is left: the two over n
def po.le.add.sub(a: Nat, +b: Nat, n: Nat, h1: {Nat.is_le(a, n) == True{} : Bool},
  h2: {Nat.is_le(b, Nat.sub(n, a)) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, b), n) == True{} : Bool}:
  match a n:
    case 0n 0n:
      h2
    case 0n 1n+q:
      h2
    case 1n+p 0n:
      Bool.no({Nat.is_le(Nat.add(1n+p, b), 0n) == True{} : Bool}, h1)
    case 1n+p 1n+q:
      po.le.add.sub(p, b, q, h1, h2)

def po.empty.len(b: Bytes()) -> {String.is_empty(b) == Nat.is_eq(Bytes.len(b), 0n) : Bool}:
  match b:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      Equal.cong(Nat, Bool, n => Nat.is_eq(n, 0n), 1n+Bytes.len(t), Bytes.len(SCon{c, t}),
        Equal.sym(Nat, Bytes.len(SCon{c, t}), 1n+Bytes.len(t), po.blen(c, t)))

# rvalid's length, read against a body, is len.ok's against its length
def po.len.at(v: RS.FLine, +bl: Bool, +body: Bytes()) ->
  {X.rok.len.at(v, bl, body) == Stream.len.at.n(v, bl, Bytes.len(body)) : Bool}:
  match v:
    case RS.FVal{val}:
      match val:
        case RS.VLen{+m, ws}:
          Equal.cong(Bool, Bool, q => (Bool.not(U32.is_lt(268435455, m)) && (bl ||
            (X.same(U32.is_zero(m), q) && Nat.is_eq(U32.to_nat(m), Bytes.len(body))))), String.is_empty(body),
            Nat.is_eq(Bytes.len(body), 0n), po.empty.len(body))
        case RS.VLen0{}:
          {==}
        case RS.VTe0{}:
          {==}
        case RS.VTe{t}:
          {==}
        case RS.VConn{d, c}:
          {==}
        case RS.VSkip{}:
          {==}
    case RS.FEmpty{}:
      {==}
    case RS.FName{nm}:
      {==}
    case RS.FBad{}:
      {==}

def po.len.ok(+head: Bool, +bl: Bool, clen: Bytes(), +body: Bytes()) ->
  {X.rok.len(head, bl, clen, body) == Stream.len.ok(head, bl, clen, Bytes.len(body)) : Bool}:
  match clen:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      Equal.cong(Bool, Bool, q => (X.rok.all(RS.TVal{}, SCon{c, t}) && q),
        X.rok.len.at(RS.len.view(X.rask(head), RS.span(RS.TOws{}, Con{32, Bytes.to_list(SCon{c, t})})), bl, body),
        Stream.len.at.n(RS.len.view(X.rask(head), RS.span(RS.TOws{}, Con{32, Bytes.to_list(SCon{c, t})})), bl, Bytes.len(body)),
        po.len.at(RS.len.view(X.rask(head), RS.span(RS.TOws{}, Con{32, Bytes.to_list(SCon{c, t})})), bl, body))

# a length's writes that come to it go out as they are
def po.emits.len(ws: List<&2, Bytes()>, +n: Nat, h: {Nat.is_eq(Bytes.len(Bytes.concat(ws)), n) == True{} : Bool}) ->
  {Stream.emits(ws, Stream.Sent{Stream.MLen{n}, None{}}) == Bytes.concat(ws) : Bytes()}:
  match ws:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +lc = Bytes.len(Bytes.concat(t))
      +en = Equal.trans(Nat, n, Bytes.len(Bytes.append(x, Bytes.concat(t))), Nat.add(Bytes.len(x), lc),
        Equal.sym(Nat, Bytes.len(Bytes.append(x, Bytes.concat(t))), n, po.nat.eq(Bytes.len(Bytes.append(x, Bytes.concat(t))), n, h)),
        Bytes.len_append(x, Bytes.concat(t)))
      +hl = Equal.trans(Bool, Nat.is_le(Bytes.len(x), n), Nat.is_le(Bytes.len(x), Nat.add(Bytes.len(x), lc)), True{},
        Equal.cong(Nat, Bool, m => Nat.is_le(Bytes.len(x), m), n, Nat.add(Bytes.len(x), lc), en), po.le.add(Bytes.len(x), lc))
      +hr = Equal.trans(Bool, Nat.is_eq(lc, Nat.sub(n, Bytes.len(x))), Nat.is_eq(lc, lc), True{},
        Equal.cong(Nat, Bool, m => Nat.is_eq(lc, m), Nat.sub(n, Bytes.len(x)), lc,
          Equal.trans(Nat, Nat.sub(n, Bytes.len(x)), Nat.sub(Nat.add(Bytes.len(x), lc), Bytes.len(x)), lc,
            Equal.cong(Nat, Nat, m => Nat.sub(m, Bytes.len(x)), n, Nat.add(Bytes.len(x), lc), en), po.sub.add.l(Bytes.len(x), lc))),
        po.eq.refl(lc))
      %Equal.sym(Bool, Nat.is_le(Bytes.len(x), n), True{}, hl) :
        {Stream.emits.on(Stream.emit.len(_, n, x), s2 => Stream.emits(t, s2)) == Bytes.concat(Con{x, t}) : Bytes()}
      Equal.cong(Bytes(), Bytes(), y => Bytes.append(x, y), Stream.emits(t, Stream.Sent{Stream.MLen{Nat.sub(n, Bytes.len(x))}, None{}}),
        Bytes.concat(t), po.emits.len(t, Nat.sub(n, Bytes.len(x)), hr))

def po.R500v(+closing: Bool, +v10: Bool) -> Bytes():
  X.reply(Some{X.rsp.fin(False{}, 500, Http.e500.head(), Http.e500.body())}, False{}, closing, v10)

def po.pl500(+closing: Bool, +v10: Bool, +code: U32, +ws: List<&2, Bytes()>) ->
  {RS.response(X.rask(False{}), Bytes.to_list(Bytes.append(po.R500v(closing, v10),
    Stream.emits(ws, Stream.Sent{Stream.MNone{}, Some{Stream.EBad{}}})))) ==
    Laws.sent(False{}, closing, code, False{}, Bytes.concat(ws)) : R.Look}:
  %Equal.sym(Bytes(), Stream.emits(ws, Stream.Sent{Stream.MNone{}, Some{Stream.EBad{}}}), "",
    Laws.pour_quiet(Stream.MNone{}, Stream.EBad{}, ws)) :
    {RS.response(X.rask(False{}), Bytes.to_list(Bytes.append(po.R500v(closing, v10), _))) ==
      Laws.sent(False{}, closing, code, False{}, Bytes.concat(ws)) : R.Look}
  %Equal.sym(Bytes(), Bytes.append(po.R500v(closing, v10), ""), po.R500v(closing, v10), po.bapp.nil(po.R500v(closing, v10))) :
    {RS.response(X.rask(False{}), Bytes.to_list(_)) == Laws.sent(False{}, closing, code, False{}, Bytes.concat(ws)) : R.Look}
  PP.rr.h(Http.e500.head(), False{}, 500, Http.e500.body(), closing, v10, po.e500.ok(False{}))

# a declared length, the check passed: rmain, the body the writes
def po.pl.body(+cd: Bytes(), +why: Bytes(), +fs: List<&2, Wr.Field>, +clen: Bytes(), +closing: Bool, +v10: Bool, +code: U32,
  +ws: List<&2, Bytes()>, +n: Nat, sp: po.C3(cd, code, why, fs),
  +lk: {Stream.len.ok(False{}, X.rbodyless(False{}, code), clen, n) == True{} : Bool},
  hn: {Nat.is_eq(Bytes.len(Bytes.concat(ws)), n) == True{} : Bool}) ->
  {RS.response(X.rask(False{}), Bytes.to_list(X.rser(X.Rsp{cd, why, fs, clen, Bytes.concat(ws), X.rbodyless(False{}, code)},
    X.conn.val(closing, v10)))) ==
    R.Look{Nil{}, R.Final{R.Resp{code, False{}, closing, Bool.pick(Bytes(), X.rbodyless(False{}, code), "", Bytes.concat(ws))}, ""}} :
    R.Look}:
  (s1, k) = sp
  (s2, s3) = k
  +rbl = X.rbodyless(False{}, code)
  +body = Bytes.concat(ws)
  +lv = Equal.trans(Bool, X.rok.len(False{}, rbl, clen, body), Stream.len.ok(False{}, rbl, clen, Bytes.len(body)), True{},
    po.len.ok(False{}, rbl, clen, body),
    Equal.trans(Bool, Stream.len.ok(False{}, rbl, clen, Bytes.len(body)), Stream.len.ok(False{}, rbl, clen, n), True{},
      Equal.cong(Nat, Bool, m => Stream.len.ok(False{}, rbl, clen, m), Bytes.len(body), n, po.nat.eq(Bytes.len(body), n, hn)), lk))
  Equal.cong(RS.W, R.Look, w => RS.finish(X.rask(False{}), w),
    RS.walk(X.rask(False{}), Bytes.to_list(X.rser(X.Rsp{cd, why, fs, clen, body, rbl}, X.conn.val(closing, v10))), RS.w.new()),
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), rbl, "", body)}, Nil{}}, Nil{}},
    PP.rmain(cd, why, fs, clen, False{}, code, body, closing, v10,
      po.and4(X.rok.code(cd, code), X.rok.all(RS.TVal{}, why), X.rok.fields(fs), X.rok.len(False{}, rbl, clen, body), s1, s2, s3, lv)))

# the check passed: a 204 or 304 has its head alone, any other the
# writes, which come to the length
def po.pl.nb(nb: Bool, +cd: Bytes(), +why: Bytes(), +fs: List<&2, Wr.Field>, +closing: Bool, +v10: Bool, +code: U32, +n: Nat,
  +ws: List<&2, Bytes()>, +hn: {Nat.is_eq(Bytes.len(Bytes.concat(ws)), n) == True{} : Bool}, sp: po.C3(cd, code, why, fs),
  +lk: {Stream.len.ok(False{}, X.rbodyless(False{}, code), Bool.pick(Bytes(), nb, "", Nat.show(n)), n) == True{} : Bool},
  +enb: {(U32.is_eq(code, 204) || U32.is_eq(code, 304)) == nb : Bool}) ->
  {RS.response(X.rask(False{}), Bytes.to_list(Bytes.append(Stream.rhd.bytes(cd, why, fs, Bool.pick(Bytes(), nb, "", Nat.show(n)),
    X.conn.val(closing, v10)), Stream.emits(ws, Stream.Sent{Stream.mode.body(X.rbodyless(False{}, code), Stream.MLen{n}), None{}})))) ==
    Laws.sent(False{}, closing, code, True{}, Bytes.concat(ws)) : R.Look}:
  match nb:
    case True{}:
      +rbl = X.rbodyless(False{}, code)
      +hb = Stream.rhd.bytes(cd, why, fs, "", X.conn.val(closing, v10))
      %Equal.sym(Bool, rbl, True{}, enb) :
        {RS.response(X.rask(False{}), Bytes.to_list(Bytes.append(hb, Stream.emits(ws, Stream.Sent{Stream.mode.body(_, Stream.MLen{n}),
          None{}})))) == Laws.sent(False{}, closing, code, True{}, Bytes.concat(ws)) : R.Look}
      %Equal.sym(Bytes(), Stream.emits(ws, Stream.Sent{Stream.MNone{}, None{}}), "", po.emits.none(ws)) :
        {RS.response(X.rask(False{}), Bytes.to_list(Bytes.append(hb, _))) ==
          Laws.sent(False{}, closing, code, True{}, Bytes.concat(ws)) : R.Look}
      %Equal.cong(Bool, Bytes(), b => Bytes.append(hb, Bool.pick(Bytes(), b, "", Bytes.concat(ws))), rbl, True{}, enb) :
        {RS.response(X.rask(False{}), Bytes.to_list(_)) == Laws.sent(False{}, closing, code, True{}, Bytes.concat(ws)) : R.Look}
      po.pl.body(cd, why, fs, "", closing, v10, code, ws, n, sp, lk, hn)
    case False{}:
      +rbl = X.rbodyless(False{}, code)
      +hb = Stream.rhd.bytes(cd, why, fs, Nat.show(n), X.conn.val(closing, v10))
      %Equal.sym(Bool, rbl, False{}, enb) :
        {RS.response(X.rask(False{}), Bytes.to_list(Bytes.append(hb, Stream.emits(ws, Stream.Sent{Stream.mode.body(_, Stream.MLen{n}),
          None{}})))) == Laws.sent(False{}, closing, code, True{}, Bytes.concat(ws)) : R.Look}
      %Equal.sym(Bytes(), Stream.emits(ws, Stream.Sent{Stream.MLen{n}, None{}}), Bytes.concat(ws), po.emits.len(ws, n, hn)) :
        {RS.response(X.rask(False{}), Bytes.to_list(Bytes.append(hb, _))) ==
          Laws.sent(False{}, closing, code, True{}, Bytes.concat(ws)) : R.Look}
      %Equal.cong(Bool, Bytes(), b => Bytes.append(hb, Bool.pick(Bytes(), b, "", Bytes.concat(ws))), rbl, False{}, enb) :
        {RS.response(X.rask(False{}), Bytes.to_list(_)) == Laws.sent(False{}, closing, code, True{}, Bytes.concat(ws)) : R.Look}
      po.pl.body(cd, why, fs, Nat.show(n), closing, v10, code, ws, n, sp, lk, hn)

def po.pl(ok: Bool, +nb: Bool, +cd: Bytes(), +why: Bytes(), +fs: List<&2, Wr.Field>, +closing: Bool, +v10: Bool, +code: U32,
  +n: Nat, +ws: List<&2, Bytes()>, +hn: {Nat.is_eq(Bytes.len(Bytes.concat(ws)), n) == True{} : Bool},
  +eok: {Stream.len.check(False{}, code, cd, why, fs, Bool.pick(Bytes(), nb, "", Nat.show(n)), n) == ok : Bool},
  +enb: {(U32.is_eq(code, 204) || U32.is_eq(code, 304)) == nb : Bool}) ->
  {RS.response(X.rask(False{}), Bytes.to_list(Stream.poured.at(Stream.opening.ok(Stream.len.check(False{}, code, cd, why, fs,
    Bool.pick(Bytes(), nb, "", Nat.show(n)), n), False{}, closing, v10, Stream.rhd.bytes(cd, why, fs, Bool.pick(Bytes(), nb, "",
    Nat.show(n)), X.conn.val(closing, v10)), Stream.mode.body(X.rbodyless(False{}, code), Stream.MLen{n})), ws))) ==
    Laws.sent(False{}, closing, code, ok, Bytes.concat(ws)) : R.Look}:
  match ok:
    case False{}:
      %Equal.sym(Bool, Stream.len.check(False{}, code, cd, why, fs, Bool.pick(Bytes(), nb, "", Nat.show(n)), n), False{}, eok) :
        {RS.response(X.rask(False{}), Bytes.to_list(Stream.poured.at(Stream.opening.ok(_, False{}, closing, v10,
          Stream.rhd.bytes(cd, why, fs, Bool.pick(Bytes(), nb, "", Nat.show(n)), X.conn.val(closing, v10)),
          Stream.mode.body(X.rbodyless(False{}, code), Stream.MLen{n})), ws))) ==
          Laws.sent(False{}, closing, code, False{}, Bytes.concat(ws)) : R.Look}
      po.pl500(closing, v10, code, ws)
    case True{}:
      +clen = Bool.pick(Bytes(), nb, "", Nat.show(n))
      +rbl = X.rbodyless(False{}, code)
      +hb = Stream.rhd.bytes(cd, why, fs, clen, X.conn.val(closing, v10))
      +lk = po.and.r(Stream.rhd.ok(cd, code, why, fs), Stream.len.ok(False{}, rbl, clen, n), eok)
      %Equal.sym(Bool, Stream.len.check(False{}, code, cd, why, fs, clen, n), True{}, eok) :
        {RS.response(X.rask(False{}), Bytes.to_list(Stream.poured.at(Stream.opening.ok(_, False{}, closing, v10, hb,
          Stream.mode.body(rbl, Stream.MLen{n})), ws))) == Laws.sent(False{}, closing, code, True{}, Bytes.concat(ws)) : R.Look}
      po.pl.nb(nb, cd, why, fs, closing, v10, code, n, ws, hn, po.split3(X.rok.code(cd, code), X.rok.all(RS.TVal{}, why),
        X.rok.fields(fs), Bool.and_l(Stream.rhd.ok(cd, code, why, fs), Stream.len.ok(False{}, rbl, clen, n), eok)), lk, enb)

def po.pl.h(h: X.RHead, +closing: Bool, +v10: Bool, +code: U32, +n: Nat, +ws: List<&2, Bytes()>,
  +hn: {Nat.is_eq(Bytes.len(Bytes.concat(ws)), n) == True{} : Bool}) ->
  {RS.response(X.rask(False{}), Bytes.to_list(Stream.poured.at(Stream.opening.len(False{}, closing, v10, code,
    U32.is_eq(code, 204) || U32.is_eq(code, 304), n, h), ws))) ==
    Laws.sent(False{}, closing, code, Laws.pour.ok.len(code, h, n), Bytes.concat(ws)) : R.Look}:
  match h:
    case X.RHead{+cd, +why, +fs, hl}:
      po.pl(Stream.len.check(False{}, code, cd, why, fs, Bool.pick(Bytes(), U32.is_eq(code, 204) || U32.is_eq(code, 304), "",
        Nat.show(n)), n), U32.is_eq(code, 204) || U32.is_eq(code, 304), cd, why, fs, closing, v10, code, n, ws, hn, {==}, {==})

def Laws.pour_length(closing, v10, code, hs, n, ws, hn):
  po.pl.h(Http.rhead(code, hs, ""), closing, v10, code, n, ws, hn)

# pour_capped
# -----------

def po.cap.at(fit: Bool, +x: Bytes(), +t: List<&2, Bytes()>, +n: Nat, +ef: {Nat.is_le(Bytes.len(x), n) == fit : Bool},
  ih: @+n2: Nat -> {Nat.is_le(Bytes.len(Stream.emits(t, Stream.Sent{Stream.MLen{n2}, None{}})), n2) == True{} : Bool}) ->
  {Nat.is_le(Bytes.len(Stream.emits.on(Stream.emit.len(fit, n, x), s2 => Stream.emits(t, s2))), n) == True{} : Bool}:
  match fit:
    case True{}:
      +r = Stream.emits(t, Stream.Sent{Stream.MLen{Nat.sub(n, Bytes.len(x))}, None{}})
      %Equal.sym(Nat, Bytes.len(Bytes.append(x, r)), Nat.add(Bytes.len(x), Bytes.len(r)), Bytes.len_append(x, r)) :
        {Nat.is_le(_, n) == True{} : Bool}
      po.le.add.sub(Bytes.len(x), Bytes.len(r), n, ef, ih(Nat.sub(n, Bytes.len(x))))
    case False{}:
      %Equal.sym(Bytes(), Stream.emits(t, Stream.Sent{Stream.MLen{n}, Some{Stream.ELarge{}}}), "",
        Laws.pour_quiet(Stream.MLen{n}, Stream.ELarge{}, t)) :
        {Nat.is_le(Bytes.len(Bytes.append("", _)), n) == True{} : Bool}
      po.le0(n)

def po.cap(ws: List<&2, Bytes()>, +n: Nat) ->
  {Nat.is_le(Bytes.len(Stream.emits(ws, Stream.Sent{Stream.MLen{n}, None{}})), n) == True{} : Bool}:
  match ws:
    case Nil{}:
      po.le0(n)
    case Con{+x, +t}:
      po.cap.at(Nat.is_le(Bytes.len(x), n), x, t, n, {==}, n2 => po.cap(t, n2))

def Laws.pour_capped(n, ws):
  po.cap(ws, n)


# every size line is at most four digits
def po.hl(j: Nat, hj: {Nat.is_le(j, 14n) == True{} : Bool}) -> {Nat.is_le(Bytes.len(Stream.chunk.hex(j)), 4n) == True{} : Bool}:
  match j:
    case 0n:
      {==}
    case 1n+j1:
      match j1:
        case 0n:
          {==}
        case 1n+j2:
          match j2:
            case 0n:
              {==}
            case 1n+j3:
              match j3:
                case 0n:
                  {==}
                case 1n+j4:
                  match j4:
                    case 0n:
                      {==}
                    case 1n+j5:
                      match j5:
                        case 0n:
                          {==}
                        case 1n+j6:
                          match j6:
                            case 0n:
                              {==}
                            case 1n+j7:
                              match j7:
                                case 0n:
                                  {==}
                                case 1n+j8:
                                  match j8:
                                    case 0n:
                                      {==}
                                    case 1n+j9:
                                      match j9:
                                        case 0n:
                                          {==}
                                        case 1n+j10:
                                          match j10:
                                            case 0n:
                                              {==}
                                            case 1n+j11:
                                              match j11:
                                                case 0n:
                                                  {==}
                                                case 1n+j12:
                                                  match j12:
                                                    case 0n:
                                                      {==}
                                                    case 1n+j13:
                                                      match j13:
                                                        case 0n:
                                                          {==}
                                                        case 1n+j14:
                                                          match j14:
                                                            case 0n:
                                                              {==}
                                                            case 1n+j15:
                                                              Bool.no({Nat.is_le(Bytes.len(Stream.chunk.hex(1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+j15)), 4n) == True{} : Bool}, hj)

# pour_bounded
# ------------

def po.le.refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      po.le.refl(p)

def po.le.add.k(k: Nat, +c: Nat) -> {Nat.is_le(c, Nat.add(k, c)) == True{} : Bool}:
  match k:
    case 0n:
      po.le.refl(c)
    case 1n+(+q):
      po.le.up(c, Nat.add(q, c), po.le.add.k(q, c))

# adding on the left keeps the order
def po.le.add.l(s: Nat, +r: Nat, +t: Nat, h: {Nat.is_le(r, t) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(s, r), Nat.add(s, t)) == True{} : Bool}:
  match s:
    case 0n:
      h
    case 1n+p:
      po.le.add.l(p, r, t, h)

# and on the right
def po.le.add.r(a: Nat, b: Nat, +t: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(a, t), Nat.add(b, t)) == True{} : Bool}:
  match a b:
    case 0n 0n:
      po.le.refl(t)
    case 0n 1n+(+q):
      po.le.up(t, Nat.add(q, t), po.le.add.k(q, t))
    case 1n+p 0n:
      Bool.no({Nat.is_le(Nat.add(1n+p, t), Nat.add(0n, t)) == True{} : Bool}, h)
    case 1n+p 1n+q:
      po.le.add.r(p, q, t, h)

def po.add.assoc(a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+(+p):
      Equal.cong(Nat, Nat, y => 1n+y, Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), po.add.assoc(p, b, c))

def po.add.shift(+a: Nat, k: Nat, +b: Nat) -> {Nat.add(a, Nat.add(k, b)) == Nat.add(k, Nat.add(a, b)) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+(+q):
      Equal.trans(Nat, Nat.add(a, 1n+Nat.add(q, b)), 1n+Nat.add(a, Nat.add(q, b)), 1n+Nat.add(q, Nat.add(a, b)),
        po.add.succ(a, Nat.add(q, b)),
        Equal.cong(Nat, Nat, y => 1n+y, Nat.add(a, Nat.add(q, b)), Nat.add(q, Nat.add(a, b)), po.add.shift(a, q, b)))

# the framing a write may take, from 2^j down: eight bytes a chunk
def po.capj(j: Nat) -> Nat:
  match j:
    case 0n:
      Nat.add(8n, 0n)
    case 1n+i:
      Nat.add(8n, po.capj(i))

# a chunk's length: its line, CR LF, its data, CR LF, then the rest's
def po.len4(+hx: Bytes(), +tk: Bytes(), +rr: Bytes()) ->
  {Bytes.len(Bytes.append(hx, Bytes.append("\r\n", Bytes.append(tk, Bytes.append("\r\n", rr))))) ==
    Nat.add(Bytes.len(hx), 2n+Nat.add(Bytes.len(tk), 2n+Bytes.len(rr))) : Nat}:
  +w = Bytes.append("\r\n", rr)
  +z = Bytes.append(tk, w)
  +y = Bytes.append("\r\n", z)
  Equal.trans(Nat, Bytes.len(Bytes.append(hx, y)), Nat.add(Bytes.len(hx), Bytes.len(y)),
    Nat.add(Bytes.len(hx), 2n+Nat.add(Bytes.len(tk), 2n+Bytes.len(rr))), Bytes.len_append(hx, y),
    Equal.cong(Nat, Nat, q => Nat.add(Bytes.len(hx), q), Bytes.len(y), 2n+Nat.add(Bytes.len(tk), 2n+Bytes.len(rr)),
      Equal.trans(Nat, Bytes.len(y), Nat.add(2n, Bytes.len(z)), 2n+Nat.add(Bytes.len(tk), 2n+Bytes.len(rr)),
        Bytes.len_append("\r\n", z),
        Equal.cong(Nat, Nat, q => 2n+q, Bytes.len(z), Nat.add(Bytes.len(tk), 2n+Bytes.len(rr)),
          Equal.trans(Nat, Bytes.len(z), Nat.add(Bytes.len(tk), Bytes.len(w)), Nat.add(Bytes.len(tk), 2n+Bytes.len(rr)),
            Bytes.len_append(tk, w),
            Equal.cong(Nat, Nat, q => Nat.add(Bytes.len(tk), q), Bytes.len(w), 2n+Bytes.len(rr), Bytes.len_append("\r\n", rr)))))))

def po.bnd.fit(+j: Nat, +x: Bytes(), go: Bytes() -> Bytes(), +cg: Nat, +hj: {Nat.is_le(j, 14n) == True{} : Bool},
  +fit: {Nat.is_le(Stream.chunk.size(j), Bytes.len(x)) == True{} : Bool},
  +ih: {Nat.is_le(Bytes.len(go(String.drop(x, Stream.chunk.size(j)))),
    Nat.add(Bytes.len(String.drop(x, Stream.chunk.size(j))), cg)) == True{} : Bool}) ->
  {Nat.is_le(Bytes.len(Stream.chunks.at(True{}, j, x, go)), Nat.add(Bytes.len(x), Nat.add(8n, cg))) == True{} : Bool}:
  +s = Stream.chunk.size(j)
  +hx = Stream.chunk.hex(j)
  +tk = String.take(x, s)
  +d = String.drop(x, s)
  +rr = go(d)
  +lh = Bytes.len(hx)
  +lt = Bytes.len(tk)
  +lr = Bytes.len(rr)
  +ld = Bytes.len(d)
  +lx = Bytes.len(x)
  %Equal.sym(Nat, Bytes.len(Bytes.append(hx, Bytes.append("\r\n", Bytes.append(tk, Bytes.append("\r\n", rr))))),
    Nat.add(lh, 2n+Nat.add(lt, 2n+lr)), po.len4(hx, tk, rr)) :
    {Nat.is_le(_, Nat.add(lx, Nat.add(8n, cg))) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(lt, 2n+lr), 2n+Nat.add(lt, lr), Equal.trans(Nat, Nat.add(lt, 2n+lr), 1n+Nat.add(lt, 1n+lr),
    2n+Nat.add(lt, lr), po.add.succ(lt, 1n+lr), Equal.cong(Nat, Nat, y => 1n+y, Nat.add(lt, 1n+lr), 1n+Nat.add(lt, lr),
      po.add.succ(lt, lr)))) :
    {Nat.is_le(Nat.add(lh, 2n+_), Nat.add(lx, Nat.add(8n, cg))) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(lx, Nat.add(8n, cg)), Nat.add(8n, Nat.add(lx, cg)), po.add.shift(lx, 8n, cg)) :
    {Nat.is_le(Nat.add(lh, 4n+Nat.add(lt, lr)), _) == True{} : Bool}
  +lxe = Equal.trans(Nat, Nat.add(lt, ld), Nat.add(s, Nat.sub(lx, s)), lx,
    Equal.trans(Nat, Nat.add(lt, ld), Nat.add(s, ld), Nat.add(s, Nat.sub(lx, s)),
      Equal.cong(Nat, Nat, y => Nat.add(y, ld), lt, s, po.take.len(x, s, fit)),
      Equal.cong(Nat, Nat, y => Nat.add(s, y), ld, Nat.sub(lx, s), po.drop.len(x, s))),
    po.sub.add(s, lx, fit))
  Nat.is_le_trans(Nat.add(lh, 4n+Nat.add(lt, lr)), Nat.add(4n, 4n+Nat.add(lt, lr)), 8n+Nat.add(lx, cg),
    po.le.add.r(lh, 4n, 4n+Nat.add(lt, lr), po.hl(j, hj)),
    Nat.is_le_trans(Nat.add(lt, lr), Nat.add(lt, Nat.add(ld, cg)), Nat.add(lx, cg),
      po.le.add.l(lt, lr, Nat.add(ld, cg), ih),
      Equal.trans(Bool, Nat.is_le(Nat.add(lt, Nat.add(ld, cg)), Nat.add(lx, cg)), Nat.is_le(Nat.add(lx, cg), Nat.add(lx, cg)), True{},
        Equal.cong(Nat, Bool, y => Nat.is_le(y, Nat.add(lx, cg)), Nat.add(lt, Nat.add(ld, cg)), Nat.add(lx, cg),
          Equal.trans(Nat, Nat.add(lt, Nat.add(ld, cg)), Nat.add(Nat.add(lt, ld), cg), Nat.add(lx, cg),
            Equal.sym(Nat, Nat.add(Nat.add(lt, ld), cg), Nat.add(lt, Nat.add(ld, cg)), po.add.assoc(lt, ld, cg)),
            Equal.cong(Nat, Nat, y => Nat.add(y, cg), Nat.add(lt, ld), lx, lxe))),
        po.le.refl(Nat.add(lx, cg)))))

def po.bnd.at(fit: Bool, +j: Nat, +x: Bytes(), go: Bytes() -> Bytes(), +cg: Nat, +hj: {Nat.is_le(j, 14n) == True{} : Bool},
  +ef: {Nat.is_ge(Bytes.len(x), Stream.chunk.size(j)) == fit : Bool},
  ih: @+y: Bytes() -> {Nat.is_le(Bytes.len(go(y)), Nat.add(Bytes.len(y), cg)) == True{} : Bool}) ->
  {Nat.is_le(Bytes.len(Stream.chunks.at(fit, j, x, go)), Nat.add(Bytes.len(x), Nat.add(8n, cg))) == True{} : Bool}:
  match fit:
    case True{}:
      po.bnd.fit(j, x, go, cg, hj, Equal.trans(Bool, Nat.is_le(Stream.chunk.size(j), Bytes.len(x)),
        Nat.is_ge(Bytes.len(x), Stream.chunk.size(j)), True{},
        Equal.sym(Bool, Nat.is_ge(Bytes.len(x), Stream.chunk.size(j)), Nat.is_le(Stream.chunk.size(j), Bytes.len(x)),
          po.ge.le(Bytes.len(x), Stream.chunk.size(j))), ef), ih(String.drop(x, Stream.chunk.size(j))))
    case False{}:
      Nat.is_le_trans(Bytes.len(go(x)), Nat.add(Bytes.len(x), cg), Nat.add(Bytes.len(x), Nat.add(8n, cg)), ih(x),
        po.le.add.l(Bytes.len(x), cg, Nat.add(8n, cg), po.le.add.k(8n, cg)))

def po.bnd(j: Nat, +x: Bytes(), +hj: {Nat.is_le(j, 14n) == True{} : Bool}) ->
  {Nat.is_le(Bytes.len(Stream.chunks.go(j, x)), Nat.add(Bytes.len(x), po.capj(j))) == True{} : Bool}:
  match j:
    case 0n:
      po.bnd.at(Nat.is_ge(Bytes.len(x), Stream.chunk.size(0n)), 0n, x, t => "", 0n, hj, {==}, y => po.le0(Nat.add(Bytes.len(y), 0n)))
    case 1n+(+i):
      po.bnd.at(Nat.is_ge(Bytes.len(x), Stream.chunk.size(1n+i)), 1n+i, x, t => Stream.chunks.go(i, t), po.capj(i), hj, {==},
        y => po.bnd(i, y, Nat.is_le_trans(i, 13n, 14n, hj, {==})))

def po.bd.ch(ok: Bool, +x: Bytes(), ef: {Nat.is_le(Bytes.len(x), Stream.emit.max()) == ok : Bool}) ->
  {Nat.is_le(Bytes.len(Pair.snd(Stream.Sent, Bytes(), Stream.emit.chunked(ok, x))), Nat.add(Bytes.len(x), 120n)) == True{} : Bool}:
  match ok:
    case True{}:
      po.bnd(14n, x, {==})
    case False{}:
      po.le0(Nat.add(Bytes.len(x), 120n))

def po.bd.len(ok: Bool, +left: Nat, +x: Bytes()) ->
  {Nat.is_le(Bytes.len(Pair.snd(Stream.Sent, Bytes(), Stream.emit.len(ok, left, x))), Nat.add(Bytes.len(x), 120n)) == True{} : Bool}:
  match ok:
    case True{}:
      po.le.add(Bytes.len(x), 120n)
    case False{}:
      po.le0(Nat.add(Bytes.len(x), 120n))

def po.bd.mode(m: Stream.Mode, +x: Bytes()) ->
  {Nat.is_le(Bytes.len(Pair.snd(Stream.Sent, Bytes(), Stream.emit.mode(m, x))), Nat.add(Bytes.len(x), 120n)) == True{} : Bool}:
  match m:
    case Stream.MChunked{}:
      po.bd.ch(Nat.is_le(Bytes.len(x), Stream.emit.max()), x, {==})
    case Stream.MLen{+left}:
      po.bd.len(Nat.is_le(Bytes.len(x), left), left, x)
    case Stream.MRaw{}:
      po.le.add(Bytes.len(x), 120n)
    case Stream.MNone{}:
      po.le0(Nat.add(Bytes.len(x), 120n))

def Laws.pour_bounded(st, x):
  match st:
    case Stream.Sent{m, f}:
      match f:
        case Some{e}:
          po.le0(Nat.add(Bytes.len(x), 120n))
        case None{}:
          po.bd.mode(m, x)

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
