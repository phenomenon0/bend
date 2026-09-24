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
# because it keeps the credentials only for the first origin.
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
import ./http.bend as Http
import ./url.bend as U
import ./server.bend as Server
import ./client.bend as Client
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

def fields.eq(fs: List<&2, Wr.Field>) -> {Http.fields.of(fs) == Laws.spec.fields(fs) : List<&2, Http.Header>}:
  match fs:
    case Nil{}:
      {==}
    case Con{f, t}:
      match f:
        case Wr.Field{+n, +v}:
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

# fast.sound: the fast check passes only where rvalid does
def fast.sound(+head: Bool, +code: U32, h: X.RHead, +body: Bytes(), +f: {Http.enc.fast(head, code, h, body) == True{} : Bool}) ->
  {X.rvalid(head, code, X.rsp.fin(head, code, h, body)) == True{} : Bool}:
  match h:
    case X.RHead{+cd, +why, +fs, +hl}:
      +bl = X.rbodyless(head, code)
      +cl = X.rclen(head, bl, hl, body)
      +a = Http.st.in(Http.statuses(), code, cd, why)
      +b = Http.fields.fast(fs)
      +c = X.rok.len(head, bl, cl, body)
      +ab = Bool.and_l(Bool.and(a, b), c, f)
      tt(Bool.and(Bool.and(X.rok.code(cd, code), X.rok.all(RS.TVal{}, why)), X.rok.fields(fs)), c,
        tt(Bool.and(X.rok.code(cd, code), X.rok.all(RS.TVal{}, why)), X.rok.fields(fs),
          st.sound(Http.statuses(), code, cd, why, st.known(), Bool.and_l(a, b, ab)),
          fields.sound(fs, Bool.and_r(a, b, ab))),
        Bool.and_r(Bool.and(a, b), c, f))

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
