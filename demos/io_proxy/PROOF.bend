# The proofs of bend-proxy's laws.
#
# scan_is_spec is a simulation between two walks that never meet
# directly: the proxy feeds each read whole to the engine's reader (its
# block walk, which is the byte walk by feed_buf_is_feed) and takes the
# requests it completed after; the reference steps spec.bend's walk a
# byte at a time and restarts after each request. What joins them is
# frame_sim, the engine's law that its reader agrees with frame() on
# every input: after each byte, the reader fed from fresh and the walk
# are compared through frame_sim of the bytes since the last request --
# the same request, and a refusal on one exactly when the other refuses.
# The reader never restarts: that it need not is out-independence (a
# step never looks at the requests done) and that a step completing a
# request leaves a fresh reader, both proved here over every row of the
# engine's step. The rest is bookkeeping: the requests taken in order
# (reversed accumulators, reversed back), and a stream cut into reads
# is the stream whole.
import Base
import ../../wire/reader.bend as Wr
import ../io_http_engine/main.bend as Eng
import ../io_http_engine/spec.bend as Spec
import ../io_http_engine/LAWS.bend as EL
import ../io_http_engine/PROOF.bend as EP
import ../../wire/http1/resp.bend as R
import ../../wire/http1/spec.bend as RS
import ./core.bend as X
import ./LAWS.bend as Laws


# Lists
# =====

def app.nil(-A: Data, xs: List<&2, A>) -> {List.append(&2, A, xs, Nil{}) == xs : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(List<&2, A>, List<&2, A>, ys => Con{h, ys}, List.append(&2, A, t, Nil{}), t, app.nil(A, t))

def app.assoc(-A: Data, xs: List<&2, A>, -ys: List<&2, A>, -zs: List<&2, A>) ->
  {List.append(&2, A, List.append(&2, A, xs, ys), zs) == List.append(&2, A, xs, List.append(&2, A, ys, zs)) :
    List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(List<&2, A>, List<&2, A>, us => Con{h, us}, List.append(&2, A, List.append(&2, A, t, ys), zs),
        List.append(&2, A, t, List.append(&2, A, ys, zs)), app.assoc(A, t, ys, zs))

# reversing onto a list is reversing, then appending it
def rev.go(-A: Data, xs: List<&2, A>, +acc: List<&2, A>) ->
  {List.reverse.go(&2, A, xs, acc) == List.append(&2, A, List.reverse(&2, A, xs), acc) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.trans(List<&2, A>, List.reverse.go(&2, A, t, Con{h, acc}),
        List.append(&2, A, List.reverse(&2, A, t), Con{h, acc}),
        List.append(&2, A, List.reverse.go(&2, A, t, Con{h, Nil{}}), acc),
        rev.go(A, t, Con{h, acc}),
        Equal.trans(List<&2, A>, List.append(&2, A, List.reverse(&2, A, t), Con{h, acc}),
          List.append(&2, A, List.append(&2, A, List.reverse(&2, A, t), Con{h, Nil{}}), acc),
          List.append(&2, A, List.reverse.go(&2, A, t, Con{h, Nil{}}), acc),
          Equal.sym(List<&2, A>, List.append(&2, A, List.append(&2, A, List.reverse(&2, A, t), Con{h, Nil{}}), acc),
            List.append(&2, A, List.reverse(&2, A, t), Con{h, acc}),
            app.assoc(A, List.reverse(&2, A, t), Con{h, Nil{}}, acc)),
          Equal.cong(List<&2, A>, List<&2, A>, us => List.append(&2, A, us, acc),
            List.append(&2, A, List.reverse(&2, A, t), Con{h, Nil{}}), List.reverse.go(&2, A, t, Con{h, Nil{}}),
            Equal.sym(List<&2, A>, List.reverse.go(&2, A, t, Con{h, Nil{}}),
              List.append(&2, A, List.reverse(&2, A, t), Con{h, Nil{}}), rev.go(A, t, Con{h, Nil{}})))))

def rev.twice.go(-A: Data, xs: List<&2, A>, a: List<&2, A>, -b: List<&2, A>) ->
  {List.reverse.go(&2, A, List.reverse.go(&2, A, xs, a), b) == List.reverse.go(&2, A, a, List.append(&2, A, xs, b)) :
    List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      rev.twice.go(A, t, Con{h, a}, b)

def rev.rev(-A: Data, +xs: List<&2, A>) -> {List.reverse(&2, A, List.reverse(&2, A, xs)) == xs : List<&2, A>}:
  Equal.trans(List<&2, A>, List.reverse(&2, A, List.reverse(&2, A, xs)), List.append(&2, A, xs, Nil{}), xs,
    rev.twice.go(A, xs, Nil{}, Nil{}), app.nil(A, xs))

def rev.inj(-A: Data, +a: List<&2, A>, +b: List<&2, A>,
  e: {List.reverse(&2, A, a) == List.reverse(&2, A, b) : List<&2, A>}) -> {a == b : List<&2, A>}:
  Equal.trans(List<&2, A>, a, List.reverse(&2, A, List.reverse(&2, A, a)), b,
    Equal.sym(List<&2, A>, List.reverse(&2, A, List.reverse(&2, A, a)), a, rev.rev(A, a)),
    Equal.trans(List<&2, A>, List.reverse(&2, A, List.reverse(&2, A, a)), List.reverse(&2, A, List.reverse(&2, A, b)), b,
      Equal.cong(List<&2, A>, List<&2, A>, xs => List.reverse(&2, A, xs), List.reverse(&2, A, a),
        List.reverse(&2, A, b), e),
      rev.rev(A, b)))

# reversing a list with one more at its head puts it at the end
def rev.con(-A: Data, +h: A, +t: List<&2, A>) ->
  {List.reverse(&2, A, Con{h, t}) == List.append(&2, A, List.reverse(&2, A, t), Con{h, Nil{}}) : List<&2, A>}:
  rev.go(A, t, Con{h, Nil{}})

def treqs.rev.go(ts: List<&2, Laws.PTook>, acc: List<&2, Laws.PTook>) ->
  {Laws.took.reqs(List.reverse.go(&2, Laws.PTook, ts, acc)) ==
    List.reverse.go(&2, Eng.Req, Laws.took.reqs(ts), Laws.took.reqs(acc)) : List<&2, Eng.Req>}:
  match ts:
    case Nil{}:
      {==}
    case Con{h, t}:
      match h:
        case Laws.PTook{raw, q}:
          treqs.rev.go(t, Con{Laws.PTook{raw, q}, acc})

def treqs.rev(ts: List<&2, Laws.PTook>) ->
  {Laws.took.reqs(List.reverse(&2, Laws.PTook, ts)) == List.reverse(&2, Eng.Req, Laws.took.reqs(ts)) :
    List<&2, Eng.Req>}:
  treqs.rev.go(ts, Nil{})


# The engine's reader and the requests it has done
# =================================================
#
# The proxy feeds a read whole and takes the requests it completed from
# the reader's out after; the reference restarts after each. The two are
# one walk because the reader never looks at the requests it has done
# (out-independence: a step with done requests o behind its own is the
# step with none, o put behind), and a step that completes a request
# completes exactly one and leaves a fresh reader (or what follows an
# upgrade) -- and a step that completes none never hands over.

# a reader with done requests o put behind its own
def AO(p: Eng.P, o: List<&2, Eng.Req>) -> Eng.P:
  match p:
    case Eng.P{st, pd, x}:
      Eng.P{st, pd, List.append(&2, Eng.Req, x, o)}

def nh(st: Eng.St) -> Bool:
  match st:
    case Eng.Rest{bs}:
      False{}
    case _:
      True{}

# what a step from no done requests leaves: none and not handed over,
# or one, and a fresh reader
def ES.out(st: Eng.St, pd: Eng.Pend, out: List<&2, Eng.Req>) -> Type:
  match out:
    case Nil{}:
      {nh(st) == True{} : Bool}
    case Con{q, t}:
      {t == Nil{} : List<&2, Eng.Req>} & {st == Eng.emit.next(Eng.req.ws(q)) : Eng.St} &
        {pd == Eng.pend.new() : Eng.Pend}

def ES(p: Eng.P) -> Type:
  match p:
    case Eng.P{st, pd, out}:
      ES.out(st, pd, out)

def BD(b: Bool, tc: Type, fc: Type) -> Type:
  match b:
    case True{}:
      tc
    case False{}:
      fc

def no(-g: Type, e: {False{} == True{} : Bool}) -> g:
  %e : BD(_, g, Unit)
  Unit{}

def yes.no(-g: Type, e: {True{} == False{} : Bool}) -> g:
  %e : BD(_, Unit, g)
  Unit{}

def oi.emit.go(r: Eng.Req, -xo: List<&2, Eng.Req>, -oo: List<&2, Eng.Req>) ->
  {Eng.emit.go(r, List.append(&2, Eng.Req, xo, oo)) == AO(Eng.emit.go(r, xo), oo) : Eng.P}:
  match r:
    case Eng.Req{m0, p0, b0, cl0, ws0, k0, hd0}:
      {==}

def es.emit.go(r: Eng.Req) -> ES(Eng.emit.go(r, Nil{})):
  match r:
    case Eng.Req{m0, p0, b0, cl0, ws0, k0, hd0}:
      ({==}, ({==}, {==}))

def oi.emit(+pd: Eng.Pend, +b: Bytes(), -xo: List<&2, Eng.Req>, -oo: List<&2, Eng.Req>) ->
  {Eng.emit(pd, b, List.append(&2, Eng.Req, xo, oo)) == AO(Eng.emit(pd, b, xo), oo) : Eng.P}:
  oi.emit.go(Eng.pend.req(pd, b), xo, oo)

def es.emit(+pd: Eng.Pend, +b: Bytes()) -> ES(Eng.emit(pd, b, Nil{})):
  es.emit.go(Eng.pend.req(pd, b))

def oi.target(p: Bytes(), -pd: Eng.Pend, -xo: List<&2, Eng.Req>, -oo: List<&2, Eng.Req>) ->
  {Eng.step.target(p, pd, List.append(&2, Eng.Req, xo, oo)) == AO(Eng.step.target(p, pd, xo), oo) : Eng.P}:
  match p:
    case SNil{}:
      {==}
    case SCon{c, t}:
      {==}

def es.target(p: Bytes(), -pd: Eng.Pend) ->
  ES(Eng.step.target(p, pd, Nil{})):
  match p:
    case SNil{}:
      {==}
    case SCon{c, t}:
      {==}

def oi.ver(v11: Bool, v10: Bool, -pd: Eng.Pend, -xo: List<&2, Eng.Req>, -oo: List<&2, Eng.Req>) ->
  {Eng.step.ver(v11, v10, pd, List.append(&2, Eng.Req, xo, oo)) == AO(Eng.step.ver(v11, v10, pd, xo), oo) : Eng.P}:
  match v11 v10:
    case True{} _:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def es.ver(v11: Bool, v10: Bool, -pd: Eng.Pend) ->
  ES(Eng.step.ver(v11, v10, pd, Nil{})):
  match v11 v10:
    case True{} _:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def oi.name(f: Eng.Fld, -n: Bytes(), -pd: Eng.Pend, -xo: List<&2, Eng.Req>, -oo: List<&2, Eng.Req>) ->
  {Eng.step.name(f, n, pd, List.append(&2, Eng.Req, xo, oo)) == AO(Eng.step.name(f, n, pd, xo), oo) : Eng.P}:
  match f:
    case Eng.FTe{}:
      {==}
    case Eng.FCl{}:
      {==}
    case Eng.FConn{}:
      {==}
    case Eng.FUp{}:
      {==}
    case Eng.FKey{}:
      {==}
    case Eng.FHost{}:
      {==}
    case Eng.FVer{}:
      {==}
    case Eng.FOther{}:
      {==}

def es.name(f: Eng.Fld, -n: Bytes(), -pd: Eng.Pend) ->
  ES(Eng.step.name(f, n, pd, Nil{})):
  match f:
    case Eng.FTe{}:
      {==}
    case Eng.FCl{}:
      {==}
    case Eng.FConn{}:
      {==}
    case Eng.FUp{}:
      {==}
    case Eng.FKey{}:
      {==}
    case Eng.FHost{}:
      {==}
    case Eng.FVer{}:
      {==}
    case Eng.FOther{}:
      {==}

def oi.dgo(-n: U32, -pd: Eng.Pend, big: Bool, -xo: List<&2, Eng.Req>, -oo: List<&2, Eng.Req>) ->
  {Eng.step.digit.go(n, pd, List.append(&2, Eng.Req, xo, oo), big) == AO(Eng.step.digit.go(n, pd, xo, big), oo) : Eng.P}:
  match big:
    case True{}:
      {==}
    case False{}:
      {==}

def es.dgo(-n: U32, -pd: Eng.Pend, big: Bool) -> ES(Eng.step.digit.go(n, pd, Nil{}, big)):
  match big:
    case True{}:
      {==}
    case False{}:
      {==}

def oi.digit(+v: U32, +c: U32, -pd: Eng.Pend, -xo: List<&2, Eng.Req>, -oo: List<&2, Eng.Req>) ->
  {Eng.step.digit(v, c, pd, List.append(&2, Eng.Req, xo, oo)) == AO(Eng.step.digit(v, c, pd, xo), oo) : Eng.P}:
  oi.dgo((v * 10 + (c - 48) : U32), pd, U32.is_lt(Eng.body.cap(), (v * 10 + (c - 48) : U32)), xo, oo)

def es.digit(+v: U32, +c: U32, -pd: Eng.Pend) -> ES(Eng.step.digit(v, c, pd, Nil{})):
  es.dgo((v * 10 + (c - 48) : U32), pd, U32.is_lt(Eng.body.cap(), (v * 10 + (c - 48) : U32)))

def oi.clen.dup(-pd: Eng.Pend, agree: Bool, -xo: List<&2, Eng.Req>, -oo: List<&2, Eng.Req>) ->
  {Eng.step.clen.dup(pd, List.append(&2, Eng.Req, xo, oo), agree) == AO(Eng.step.clen.dup(pd, xo, agree), oo) : Eng.P}:
  match agree:
    case True{}:
      {==}
    case False{}:
      {==}

def es.clen.dup(-pd: Eng.Pend, agree: Bool) -> ES(Eng.step.clen.dup(pd, Nil{}, agree)):
  match agree:
    case True{}:
      {==}
    case False{}:
      {==}

def oi.clen.go(-meth: Eng.Meth, -path: Bytes(), cl: Eng.Cl, -close: Bool, -host: Eng.Hosts, -ws: Eng.Up, -fx: Eng.Fx, -hx: Eng.Hx, -nx: Maybe<&2, Eng.Pend>, +v: U32, -xo: List<&2, Eng.Req>, -oo: List<&2, Eng.Req>) ->
  {Eng.step.clen.go(meth, path, cl, close, host, ws, fx, hx, nx, v, List.append(&2, Eng.Req, xo, oo)) ==
    AO(Eng.step.clen.go(meth, path, cl, close, host, ws, fx, hx, nx, v, xo), oo) : Eng.P}:
  match cl:
    case Eng.NoCl{}:
      {==}
    case Eng.Has{+w}:
      oi.clen.dup(Eng.Pend{meth, path, Eng.Has{w}, close, host, ws, fx, hx, nx}, U32.is_eq(v, w), xo, oo)

def es.clen.go(-meth: Eng.Meth, -path: Bytes(), cl: Eng.Cl, -close: Bool, -host: Eng.Hosts, -ws: Eng.Up, -fx: Eng.Fx, -hx: Eng.Hx, -nx: Maybe<&2, Eng.Pend>, +v: U32) ->
  ES(Eng.step.clen.go(meth, path, cl, close, host, ws, fx, hx, nx, v, Nil{})):
  match cl:
    case Eng.NoCl{}:
      {==}
    case Eng.Has{+w}:
      es.clen.dup(Eng.Pend{meth, path, Eng.Has{w}, close, host, ws, fx, hx, nx}, U32.is_eq(v, w))

def oi.clen(+v: U32, pd: Eng.Pend, -xo: List<&2, Eng.Req>, -oo: List<&2, Eng.Req>) ->
  {Eng.step.clen(v, pd, List.append(&2, Eng.Req, xo, oo)) == AO(Eng.step.clen(v, pd, xo), oo) : Eng.P}:
  match pd:
    case Eng.Pend{meth, path, cl, close, host, ws, fx, hx, nx}:
      oi.clen.go(meth, path, cl, close, host, ws, fx, hx, nx, v, xo, oo)

def es.clen(+v: U32, pd: Eng.Pend) -> ES(Eng.step.clen(v, pd, Nil{})):
  match pd:
    case Eng.Pend{meth, path, cl, close, host, ws, fx, hx, nx}:
      es.clen.go(meth, path, cl, close, host, ws, fx, hx, nx, v)

def oi.te.go(ok: Bool, -meth: Eng.Meth, -path: Bytes(), -cl: Eng.Cl, -close: Bool, -host: Eng.Hosts, -ws: Eng.Up, -v10: Bool, -ka: Bool, -hx: Eng.Hx, -nx: Maybe<&2, Eng.Pend>, -te: Bool, -xo: List<&2, Eng.Req>, -oo: List<&2, Eng.Req>) ->
  {Eng.step.te.go(ok, meth, path, cl, close, host, ws, v10, ka, hx, nx, List.append(&2, Eng.Req, xo, oo), te) ==
    AO(Eng.step.te.go(ok, meth, path, cl, close, host, ws, v10, ka, hx, nx, xo, te), oo) : Eng.P}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def es.te.go(ok: Bool, -meth: Eng.Meth, -path: Bytes(), -cl: Eng.Cl, -close: Bool, -host: Eng.Hosts, -ws: Eng.Up, -v10: Bool, -ka: Bool, -hx: Eng.Hx, -nx: Maybe<&2, Eng.Pend>, -te: Bool) ->
  ES(Eng.step.te.go(ok, meth, path, cl, close, host, ws, v10, ka, hx, nx, Nil{}, te)):
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def oi.te.at(+ok: Bool, pd: Eng.Pend, -xo: List<&2, Eng.Req>, -oo: List<&2, Eng.Req>) ->
  {Eng.step.te.at(ok, pd, List.append(&2, Eng.Req, xo, oo)) == AO(Eng.step.te.at(ok, pd, xo), oo) : Eng.P}:
  match pd:
    case Eng.Pend{meth, path, cl, close, host, ws, fx, hx, nx}:
      match fx:
        case Eng.Fx{v10, ka, +te}:
          oi.te.go(ok && Bool.not(te), meth, path, cl, close, host, ws, v10, ka, hx, nx, te, xo, oo)

def es.te.at(+ok: Bool, pd: Eng.Pend) -> ES(Eng.step.te.at(ok, pd, Nil{})):
  match pd:
    case Eng.Pend{meth, path, cl, close, host, ws, fx, hx, nx}:
      match fx:
        case Eng.Fx{v10, ka, +te}:
          es.te.go(ok && Bool.not(te), meth, path, cl, close, host, ws, v10, ka, hx, nx, te)

def oi.te(+v: Bytes(), +pd: Eng.Pend, -xo: List<&2, Eng.Req>, -oo: List<&2, Eng.Req>) ->
  {Eng.step.te(v, pd, List.append(&2, Eng.Req, xo, oo)) == AO(Eng.step.te(v, pd, xo), oo) : Eng.P}:
  oi.te.at(Eng.bytes.eq(Eng.lows(v), Eng.te.lit()), pd, xo, oo)

def es.te(+v: Bytes(), +pd: Eng.Pend) -> ES(Eng.step.te(v, pd, Nil{})):
  es.te.at(Eng.bytes.eq(Eng.lows(v), Eng.te.lit()), pd)

def oi.head.len(+pd: Eng.Pend, -v: U32, z: Bool, -xo: List<&2, Eng.Req>, -oo: List<&2, Eng.Req>) ->
  {Eng.step.head.len(pd, v, List.append(&2, Eng.Req, xo, oo), z) == AO(Eng.step.head.len(pd, v, xo, z), oo) : Eng.P}:
  match z:
    case True{}:
      oi.emit(pd, "", xo, oo)
    case False{}:
      {==}

def es.head.len(+pd: Eng.Pend, -v: U32, z: Bool) -> ES(Eng.step.head.len(pd, v, Nil{}, z)):
  match z:
    case True{}:
      es.emit(pd, "")
    case False{}:
      {==}

def oi.head.at(+pd: Eng.Pend, ok: Bool, bd: Eng.Bd, -xo: List<&2, Eng.Req>, -oo: List<&2, Eng.Req>) ->
  {Eng.step.head.at(pd, ok, bd, List.append(&2, Eng.Req, xo, oo)) == AO(Eng.step.head.at(pd, ok, bd, xo), oo) : Eng.P}:
  match ok bd:
    case False{} _:
      {==}
    case True{} Eng.BdBad{}:
      {==}
    case True{} Eng.BdNone{}:
      oi.emit(pd, "", xo, oo)
    case True{} Eng.BdLen{+v}:
      oi.head.len(pd, v, U32.is_zero(v), xo, oo)
    case True{} Eng.BdChunked{}:
      {==}

def es.head.at(+pd: Eng.Pend, ok: Bool, bd: Eng.Bd) -> ES(Eng.step.head.at(pd, ok, bd, Nil{})):
  match ok bd:
    case False{} _:
      {==}
    case True{} Eng.BdBad{}:
      {==}
    case True{} Eng.BdNone{}:
      es.emit(pd, "")
    case True{} Eng.BdLen{+v}:
      es.head.len(pd, v, U32.is_zero(v))
    case True{} Eng.BdChunked{}:
      {==}

def oi.head.fx(+pd: Eng.Pend, +host: Eng.Hosts, +cl: Eng.Cl, fx: Eng.Fx, -xo: List<&2, Eng.Req>, -oo: List<&2, Eng.Req>) ->
  {Eng.step.head.fx(pd, host, cl, fx, List.append(&2, Eng.Req, xo, oo)) == AO(Eng.step.head.fx(pd, host, cl, fx, xo), oo) : Eng.P}:
  match fx:
    case Eng.Fx{+v10, ka, te}:
      oi.head.at(pd, Eng.hosts.ok(v10, host), Eng.body.kind(te, v10, cl), xo, oo)

def es.head.fx(+pd: Eng.Pend, +host: Eng.Hosts, +cl: Eng.Cl, fx: Eng.Fx) ->
  ES(Eng.step.head.fx(pd, host, cl, fx, Nil{})):
  match fx:
    case Eng.Fx{+v10, ka, te}:
      es.head.at(pd, Eng.hosts.ok(v10, host), Eng.body.kind(te, v10, cl))

def oi.head(pd: Eng.Pend, -xo: List<&2, Eng.Req>, -oo: List<&2, Eng.Req>) ->
  {Eng.step.head(pd, List.append(&2, Eng.Req, xo, oo)) == AO(Eng.step.head(pd, xo), oo) : Eng.P}:
  match pd:
    case Eng.Pend{meth, path, +cl, close, +host, ws, +fx, hx, nx}:
      oi.head.fx(Eng.Pend{meth, path, cl, close, host, ws, fx, hx, nx}, host, cl, fx, xo, oo)

def es.head(pd: Eng.Pend) -> ES(Eng.step.head(pd, Nil{})):
  match pd:
    case Eng.Pend{meth, path, +cl, close, +host, ws, +fx, hx, nx}:
      es.head.fx(Eng.Pend{meth, path, cl, close, host, ws, fx, hx, nx}, host, cl, fx)

def oi.body(r: Nat, +b: Bytes(), +c: U32, +pd: Eng.Pend, -xo: List<&2, Eng.Req>, -oo: List<&2, Eng.Req>) ->
  {Eng.step.body(r, b, c, pd, List.append(&2, Eng.Req, xo, oo)) == AO(Eng.step.body(r, b, c, pd, xo), oo) : Eng.P}:
  match r:
    case 0n:
      oi.emit(pd, Eng.push(b, c), xo, oo)
    case 1n+q:
      {==}

def es.body(r: Nat, +b: Bytes(), +c: U32, +pd: Eng.Pend) -> ES(Eng.step.body(r, b, c, pd, Nil{})):
  match r:
    case 0n:
      es.emit(pd, Eng.push(b, c))
    case 1n+q:
      {==}

def oi.chd(r: Nat, -b: Bytes(), -c: U32, -left: U32, -pd: Eng.Pend, -xo: List<&2, Eng.Req>, -oo: List<&2, Eng.Req>) ->
  {Eng.step.chd(r, b, c, left, pd, List.append(&2, Eng.Req, xo, oo)) == AO(Eng.step.chd(r, b, c, left, pd, xo), oo) : Eng.P}:
  match r:
    case 0n:
      {==}
    case 1n+q:
      {==}

def es.chd(r: Nat, -b: Bytes(), -c: U32, -left: U32, -pd: Eng.Pend) -> ES(Eng.step.chd(r, b, c, left, pd, Nil{})):
  match r:
    case 0n:
      {==}
    case 1n+q:
      {==}

def oi.chk.paid(over: Bool, -pos: Eng.ChPos, -n: U32, -b: Bytes(), -left: U32, -pd: Eng.Pend, -xo: List<&2, Eng.Req>, -oo: List<&2, Eng.Req>) ->
  {Eng.chk.paid(over, pos, n, b, left, pd, List.append(&2, Eng.Req, xo, oo)) == AO(Eng.chk.paid(over, pos, n, b, left, pd, xo), oo) : Eng.P}:
  match over:
    case True{}:
      {==}
    case False{}:
      {==}

def es.chk.paid(over: Bool, -pos: Eng.ChPos, -n: U32, -b: Bytes(), -left: U32, -pd: Eng.Pend) -> ES(Eng.chk.paid(over, pos, n, b, left, pd, Nil{})):
  match over:
    case True{}:
      {==}
    case False{}:
      {==}

def oi.chk.to(paid: Bool, -pos: Eng.ChPos, +n: U32, -b: Bytes(), +left: U32, -pd: Eng.Pend, -xo: List<&2, Eng.Req>, -oo: List<&2, Eng.Req>) ->
  {Eng.chk.to(paid, pos, n, b, left, pd, List.append(&2, Eng.Req, xo, oo)) == AO(Eng.chk.to(paid, pos, n, b, left, pd, xo), oo) : Eng.P}:
  match paid:
    case True{}:
      oi.chk.paid(U32.is_le(left, n), pos, n, b, left, pd, xo, oo)
    case False{}:
      {==}

def es.chk.to(paid: Bool, -pos: Eng.ChPos, +n: U32, -b: Bytes(), +left: U32, -pd: Eng.Pend) -> ES(Eng.chk.to(paid, pos, n, b, left, pd, Nil{})):
  match paid:
    case True{}:
      es.chk.paid(U32.is_le(left, n), pos, n, b, left, pd)
    case False{}:
      {==}

def oi.chk.line(z: Bool, -n: U32, -b: Bytes(), -left: U32, -pd: Eng.Pend, -xo: List<&2, Eng.Req>, -oo: List<&2, Eng.Req>) ->
  {Eng.chk.line(z, n, b, left, pd, List.append(&2, Eng.Req, xo, oo)) == AO(Eng.chk.line(z, n, b, left, pd, xo), oo) : Eng.P}:
  match z:
    case True{}:
      {==}
    case False{}:
      {==}

def es.chk.line(z: Bool, -n: U32, -b: Bytes(), -left: U32, -pd: Eng.Pend) -> ES(Eng.chk.line(z, n, b, left, pd, Nil{})):
  match z:
    case True{}:
      {==}
    case False{}:
      {==}

def oi.chk(mv: Eng.Mv, +n: U32, +b: Bytes(), +left: U32, +pd: Eng.Pend, -xo: List<&2, Eng.Req>, -oo: List<&2, Eng.Req>) ->
  {Eng.step.chk(mv, n, b, left, pd, List.append(&2, Eng.Req, xo, oo)) == AO(Eng.step.chk(mv, n, b, left, pd, xo), oo) : Eng.P}:
  match mv:
    case Eng.MvBad{}:
      {==}
    case Eng.MvTo{pos, paid}:
      oi.chk.to(paid, pos, n, b, left, pd, xo, oo)
    case Eng.MvDigit{+d}:
      oi.chk.paid(U32.is_le(left, (n * 16 + d : U32)), Eng.CSize{}, (n * 16 + d : U32), b, left, pd, xo, oo)
    case Eng.MvLine{}:
      oi.chk.line(U32.is_zero(n), n, b, left, pd, xo, oo)
    case Eng.MvDone{}:
      oi.emit(pd, b, xo, oo)

def es.chk(mv: Eng.Mv, +n: U32, +b: Bytes(), +left: U32, +pd: Eng.Pend) -> ES(Eng.step.chk(mv, n, b, left, pd, Nil{})):
  match mv:
    case Eng.MvBad{}:
      {==}
    case Eng.MvTo{pos, paid}:
      es.chk.to(paid, pos, n, b, left, pd)
    case Eng.MvDigit{+d}:
      es.chk.paid(U32.is_le(left, (n * 16 + d : U32)), Eng.CSize{}, (n * 16 + d : U32), b, left, pd)
    case Eng.MvLine{}:
      es.chk.line(U32.is_zero(n), n, b, left, pd)
    case Eng.MvDone{}:
      es.emit(pd, b)

# LEMMA: a step does not look at the requests done ...
def oi.at(+st: Eng.St, +k: Eng.Cls, +c: U32, +pd: Eng.Pend, -xo: List<&2, Eng.Req>, -oo: List<&2, Eng.Req>) ->
  {Eng.step.at(st, k, c, pd, List.append(&2, Eng.Req, xo, oo)) == AO(Eng.step.at(st, k, c, pd, xo), oo) : Eng.P}:
  match st k:
    case Eng.Pre{} Eng.KCr{}:
      {==}
    case Eng.Pre{} Eng.KTk{}:
      {==}
    case Eng.Pre{} Eng.KDg{}:
      {==}
    case Eng.Pre{} Eng.KSp{}:
      {==}
    case Eng.Pre{} Eng.KHt{}:
      {==}
    case Eng.Pre{} Eng.KLf{}:
      {==}
    case Eng.Pre{} Eng.KCo{}:
      {==}
    case Eng.Pre{} Eng.KCm{}:
      {==}
    case Eng.Pre{} Eng.KVc{}:
      {==}
    case Eng.Pre{} Eng.KCt{}:
      {==}
    case Eng.PreLf{} Eng.KLf{}:
      {==}
    case Eng.PreLf{} Eng.KSp{}:
      {==}
    case Eng.PreLf{} Eng.KHt{}:
      {==}
    case Eng.PreLf{} Eng.KCr{}:
      {==}
    case Eng.PreLf{} Eng.KCo{}:
      {==}
    case Eng.PreLf{} Eng.KCm{}:
      {==}
    case Eng.PreLf{} Eng.KDg{}:
      {==}
    case Eng.PreLf{} Eng.KTk{}:
      {==}
    case Eng.PreLf{} Eng.KVc{}:
      {==}
    case Eng.PreLf{} Eng.KCt{}:
      {==}
    case Eng.InM{m} Eng.KSp{}:
      {==}
    case Eng.InM{m} Eng.KTk{}:
      {==}
    case Eng.InM{m} Eng.KDg{}:
      {==}
    case Eng.InM{m} Eng.KHt{}:
      {==}
    case Eng.InM{m} Eng.KCr{}:
      {==}
    case Eng.InM{m} Eng.KLf{}:
      {==}
    case Eng.InM{m} Eng.KCo{}:
      {==}
    case Eng.InM{m} Eng.KCm{}:
      {==}
    case Eng.InM{m} Eng.KVc{}:
      {==}
    case Eng.InM{m} Eng.KCt{}:
      {==}
    case Eng.InT{p} Eng.KSp{}:
      oi.target(p, pd, xo, oo)
    case Eng.InT{p} Eng.KHt{}:
      {==}
    case Eng.InT{p} Eng.KCr{}:
      {==}
    case Eng.InT{p} Eng.KLf{}:
      {==}
    case Eng.InT{p} Eng.KCt{}:
      {==}
    case Eng.InT{p} Eng.KCo{}:
      {==}
    case Eng.InT{p} Eng.KCm{}:
      {==}
    case Eng.InT{p} Eng.KDg{}:
      {==}
    case Eng.InT{p} Eng.KTk{}:
      {==}
    case Eng.InT{p} Eng.KVc{}:
      {==}
    case Eng.InV{+v} Eng.KCr{}:
      oi.ver(Eng.bytes.eq(v, Eng.ver.lit()), Eng.bytes.eq(v, Eng.ver10.lit()), pd, xo, oo)
    case Eng.InV{v} Eng.KTk{}:
      {==}
    case Eng.InV{v} Eng.KDg{}:
      {==}
    case Eng.InV{v} Eng.KVc{}:
      {==}
    case Eng.InV{v} Eng.KSp{}:
      {==}
    case Eng.InV{v} Eng.KHt{}:
      {==}
    case Eng.InV{v} Eng.KLf{}:
      {==}
    case Eng.InV{v} Eng.KCo{}:
      {==}
    case Eng.InV{v} Eng.KCm{}:
      {==}
    case Eng.InV{v} Eng.KCt{}:
      {==}
    case Eng.CrM{} Eng.KLf{}:
      {==}
    case Eng.CrM{} Eng.KSp{}:
      {==}
    case Eng.CrM{} Eng.KHt{}:
      {==}
    case Eng.CrM{} Eng.KCr{}:
      {==}
    case Eng.CrM{} Eng.KCo{}:
      {==}
    case Eng.CrM{} Eng.KCm{}:
      {==}
    case Eng.CrM{} Eng.KDg{}:
      {==}
    case Eng.CrM{} Eng.KTk{}:
      {==}
    case Eng.CrM{} Eng.KVc{}:
      {==}
    case Eng.CrM{} Eng.KCt{}:
      {==}
    case Eng.Lin{} Eng.KCr{}:
      {==}
    case Eng.Lin{} Eng.KTk{}:
      {==}
    case Eng.Lin{} Eng.KDg{}:
      {==}
    case Eng.Lin{} Eng.KSp{}:
      {==}
    case Eng.Lin{} Eng.KHt{}:
      {==}
    case Eng.Lin{} Eng.KLf{}:
      {==}
    case Eng.Lin{} Eng.KCo{}:
      {==}
    case Eng.Lin{} Eng.KCm{}:
      {==}
    case Eng.Lin{} Eng.KVc{}:
      {==}
    case Eng.Lin{} Eng.KCt{}:
      {==}
    case Eng.InN{+n} Eng.KCo{}:
      oi.name(Eng.fld.name(n), n, pd, xo, oo)
    case Eng.InN{n} Eng.KTk{}:
      {==}
    case Eng.InN{n} Eng.KDg{}:
      {==}
    case Eng.InN{n} Eng.KSp{}:
      {==}
    case Eng.InN{n} Eng.KHt{}:
      {==}
    case Eng.InN{n} Eng.KCr{}:
      {==}
    case Eng.InN{n} Eng.KLf{}:
      {==}
    case Eng.InN{n} Eng.KCm{}:
      {==}
    case Eng.InN{n} Eng.KVc{}:
      {==}
    case Eng.InN{n} Eng.KCt{}:
      {==}
    case Eng.InL0{} Eng.KSp{}:
      {==}
    case Eng.InL0{} Eng.KHt{}:
      {==}
    case Eng.InL0{} Eng.KDg{}:
      oi.digit(0, c, pd, xo, oo)
    case Eng.InL0{} Eng.KCr{}:
      {==}
    case Eng.InL0{} Eng.KLf{}:
      {==}
    case Eng.InL0{} Eng.KCo{}:
      {==}
    case Eng.InL0{} Eng.KCm{}:
      {==}
    case Eng.InL0{} Eng.KTk{}:
      {==}
    case Eng.InL0{} Eng.KVc{}:
      {==}
    case Eng.InL0{} Eng.KCt{}:
      {==}
    case Eng.InL{v} Eng.KDg{}:
      oi.digit(v, c, pd, xo, oo)
    case Eng.InL{v} Eng.KSp{}:
      {==}
    case Eng.InL{v} Eng.KHt{}:
      {==}
    case Eng.InL{v} Eng.KCr{}:
      oi.clen(v, pd, xo, oo)
    case Eng.InL{v} Eng.KLf{}:
      {==}
    case Eng.InL{v} Eng.KCo{}:
      {==}
    case Eng.InL{v} Eng.KCm{}:
      {==}
    case Eng.InL{v} Eng.KTk{}:
      {==}
    case Eng.InL{v} Eng.KVc{}:
      {==}
    case Eng.InL{v} Eng.KCt{}:
      {==}
    case Eng.InLt{v} Eng.KSp{}:
      {==}
    case Eng.InLt{v} Eng.KHt{}:
      {==}
    case Eng.InLt{v} Eng.KCr{}:
      oi.clen(v, pd, xo, oo)
    case Eng.InLt{v} Eng.KLf{}:
      {==}
    case Eng.InLt{v} Eng.KCo{}:
      {==}
    case Eng.InLt{v} Eng.KCm{}:
      {==}
    case Eng.InLt{v} Eng.KDg{}:
      {==}
    case Eng.InLt{v} Eng.KTk{}:
      {==}
    case Eng.InLt{v} Eng.KVc{}:
      {==}
    case Eng.InLt{v} Eng.KCt{}:
      {==}
    case Eng.InLc{t, a, b, e, ms} Eng.KCr{}:
      {==}
    case Eng.InLc{t, a, b, e, ms} Eng.KSp{}:
      {==}
    case Eng.InLc{t, a, b, e, ms} Eng.KHt{}:
      {==}
    case Eng.InLc{t, a, b, e, ms} Eng.KCm{}:
      {==}
    case Eng.InLc{t, a, b, e, ms} Eng.KLf{}:
      {==}
    case Eng.InLc{t, a, b, e, ms} Eng.KCt{}:
      {==}
    case Eng.InLc{t, a, b, e, ms} Eng.KCo{}:
      {==}
    case Eng.InLc{t, a, b, e, ms} Eng.KDg{}:
      {==}
    case Eng.InLc{t, a, b, e, ms} Eng.KTk{}:
      {==}
    case Eng.InLc{t, a, b, e, ms} Eng.KVc{}:
      {==}
    case Eng.InLu{t, w} Eng.KCr{}:
      {==}
    case Eng.InLu{t, w} Eng.KSp{}:
      {==}
    case Eng.InLu{t, w} Eng.KHt{}:
      {==}
    case Eng.InLu{t, w} Eng.KCm{}:
      {==}
    case Eng.InLu{t, w} Eng.KLf{}:
      {==}
    case Eng.InLu{t, w} Eng.KCt{}:
      {==}
    case Eng.InLu{t, w} Eng.KCo{}:
      {==}
    case Eng.InLu{t, w} Eng.KDg{}:
      {==}
    case Eng.InLu{t, w} Eng.KTk{}:
      {==}
    case Eng.InLu{t, w} Eng.KVc{}:
      {==}
    case Eng.InLk0{} Eng.KSp{}:
      {==}
    case Eng.InLk0{} Eng.KHt{}:
      {==}
    case Eng.InLk0{} Eng.KCr{}:
      {==}
    case Eng.InLk0{} Eng.KLf{}:
      {==}
    case Eng.InLk0{} Eng.KCt{}:
      {==}
    case Eng.InLk0{} Eng.KCo{}:
      {==}
    case Eng.InLk0{} Eng.KCm{}:
      {==}
    case Eng.InLk0{} Eng.KDg{}:
      {==}
    case Eng.InLk0{} Eng.KTk{}:
      {==}
    case Eng.InLk0{} Eng.KVc{}:
      {==}
    case Eng.InLk{k} Eng.KCr{}:
      {==}
    case Eng.InLk{k} Eng.KLf{}:
      {==}
    case Eng.InLk{k} Eng.KCt{}:
      {==}
    case Eng.InLk{k} Eng.KSp{}:
      {==}
    case Eng.InLk{k} Eng.KHt{}:
      {==}
    case Eng.InLk{k} Eng.KCo{}:
      {==}
    case Eng.InLk{k} Eng.KCm{}:
      {==}
    case Eng.InLk{k} Eng.KDg{}:
      {==}
    case Eng.InLk{k} Eng.KTk{}:
      {==}
    case Eng.InLk{k} Eng.KVc{}:
      {==}
    case Eng.InLv{v} Eng.KCr{}:
      {==}
    case Eng.InLv{v} Eng.KLf{}:
      {==}
    case Eng.InLv{v} Eng.KCt{}:
      {==}
    case Eng.InLv{v} Eng.KSp{}:
      {==}
    case Eng.InLv{v} Eng.KHt{}:
      {==}
    case Eng.InLv{v} Eng.KCo{}:
      {==}
    case Eng.InLv{v} Eng.KCm{}:
      {==}
    case Eng.InLv{v} Eng.KDg{}:
      {==}
    case Eng.InLv{v} Eng.KTk{}:
      {==}
    case Eng.InLv{v} Eng.KVc{}:
      {==}
    case Eng.InLx{v} Eng.KCr{}:
      {==}
    case Eng.InLx{v} Eng.KLf{}:
      {==}
    case Eng.InLx{v} Eng.KCt{}:
      {==}
    case Eng.InLx{v} Eng.KSp{}:
      {==}
    case Eng.InLx{v} Eng.KHt{}:
      {==}
    case Eng.InLx{v} Eng.KCo{}:
      {==}
    case Eng.InLx{v} Eng.KCm{}:
      {==}
    case Eng.InLx{v} Eng.KDg{}:
      {==}
    case Eng.InLx{v} Eng.KTk{}:
      {==}
    case Eng.InLx{v} Eng.KVc{}:
      {==}
    case Eng.InLe0{} Eng.KSp{}:
      {==}
    case Eng.InLe0{} Eng.KHt{}:
      {==}
    case Eng.InLe0{} Eng.KCr{}:
      {==}
    case Eng.InLe0{} Eng.KLf{}:
      {==}
    case Eng.InLe0{} Eng.KCt{}:
      {==}
    case Eng.InLe0{} Eng.KCo{}:
      {==}
    case Eng.InLe0{} Eng.KCm{}:
      {==}
    case Eng.InLe0{} Eng.KDg{}:
      {==}
    case Eng.InLe0{} Eng.KTk{}:
      {==}
    case Eng.InLe0{} Eng.KVc{}:
      {==}
    case Eng.InLe{v} Eng.KCr{}:
      oi.te(v, pd, xo, oo)
    case Eng.InLe{v} Eng.KLf{}:
      {==}
    case Eng.InLe{v} Eng.KCt{}:
      {==}
    case Eng.InLe{v} Eng.KSp{}:
      {==}
    case Eng.InLe{v} Eng.KHt{}:
      {==}
    case Eng.InLe{v} Eng.KCo{}:
      {==}
    case Eng.InLe{v} Eng.KCm{}:
      {==}
    case Eng.InLe{v} Eng.KDg{}:
      {==}
    case Eng.InLe{v} Eng.KTk{}:
      {==}
    case Eng.InLe{v} Eng.KVc{}:
      {==}
    case Eng.CrL{} Eng.KLf{}:
      oi.head(pd, xo, oo)
    case Eng.CrL{} Eng.KSp{}:
      {==}
    case Eng.CrL{} Eng.KHt{}:
      {==}
    case Eng.CrL{} Eng.KCr{}:
      {==}
    case Eng.CrL{} Eng.KCo{}:
      {==}
    case Eng.CrL{} Eng.KCm{}:
      {==}
    case Eng.CrL{} Eng.KDg{}:
      {==}
    case Eng.CrL{} Eng.KTk{}:
      {==}
    case Eng.CrL{} Eng.KVc{}:
      {==}
    case Eng.CrL{} Eng.KCt{}:
      {==}
    case Eng.Bod{r, b} _:
      oi.body(r, b, c, pd, xo, oo)
    case Eng.Chk{pos, n, b, left} x:
      oi.chk(Eng.chk.next(pos, Eng.xk.of(x, c)), n, b, left, pd, xo, oo)
    case Eng.Chd{r, b, left} _:
      oi.chd(r, b, c, left, pd, xo, oo)
    case Eng.Rest{bs} _:
      {==}
    case Eng.Bad{} _:
      {==}

# ... and a step from none does at most one, then starts again
def es.at(+st: Eng.St, +k: Eng.Cls, +c: U32, +pd: Eng.Pend, hn: {nh(st) == True{} : Bool}) ->
  ES(Eng.step.at(st, k, c, pd, Nil{})):
  match st k:
    case Eng.Pre{} Eng.KCr{}:
      {==}
    case Eng.Pre{} Eng.KTk{}:
      {==}
    case Eng.Pre{} Eng.KDg{}:
      {==}
    case Eng.Pre{} Eng.KSp{}:
      {==}
    case Eng.Pre{} Eng.KHt{}:
      {==}
    case Eng.Pre{} Eng.KLf{}:
      {==}
    case Eng.Pre{} Eng.KCo{}:
      {==}
    case Eng.Pre{} Eng.KCm{}:
      {==}
    case Eng.Pre{} Eng.KVc{}:
      {==}
    case Eng.Pre{} Eng.KCt{}:
      {==}
    case Eng.PreLf{} Eng.KLf{}:
      {==}
    case Eng.PreLf{} Eng.KSp{}:
      {==}
    case Eng.PreLf{} Eng.KHt{}:
      {==}
    case Eng.PreLf{} Eng.KCr{}:
      {==}
    case Eng.PreLf{} Eng.KCo{}:
      {==}
    case Eng.PreLf{} Eng.KCm{}:
      {==}
    case Eng.PreLf{} Eng.KDg{}:
      {==}
    case Eng.PreLf{} Eng.KTk{}:
      {==}
    case Eng.PreLf{} Eng.KVc{}:
      {==}
    case Eng.PreLf{} Eng.KCt{}:
      {==}
    case Eng.InM{m} Eng.KSp{}:
      {==}
    case Eng.InM{m} Eng.KTk{}:
      {==}
    case Eng.InM{m} Eng.KDg{}:
      {==}
    case Eng.InM{m} Eng.KHt{}:
      {==}
    case Eng.InM{m} Eng.KCr{}:
      {==}
    case Eng.InM{m} Eng.KLf{}:
      {==}
    case Eng.InM{m} Eng.KCo{}:
      {==}
    case Eng.InM{m} Eng.KCm{}:
      {==}
    case Eng.InM{m} Eng.KVc{}:
      {==}
    case Eng.InM{m} Eng.KCt{}:
      {==}
    case Eng.InT{p} Eng.KSp{}:
      es.target(p, pd)
    case Eng.InT{p} Eng.KHt{}:
      {==}
    case Eng.InT{p} Eng.KCr{}:
      {==}
    case Eng.InT{p} Eng.KLf{}:
      {==}
    case Eng.InT{p} Eng.KCt{}:
      {==}
    case Eng.InT{p} Eng.KCo{}:
      {==}
    case Eng.InT{p} Eng.KCm{}:
      {==}
    case Eng.InT{p} Eng.KDg{}:
      {==}
    case Eng.InT{p} Eng.KTk{}:
      {==}
    case Eng.InT{p} Eng.KVc{}:
      {==}
    case Eng.InV{+v} Eng.KCr{}:
      es.ver(Eng.bytes.eq(v, Eng.ver.lit()), Eng.bytes.eq(v, Eng.ver10.lit()), pd)
    case Eng.InV{v} Eng.KTk{}:
      {==}
    case Eng.InV{v} Eng.KDg{}:
      {==}
    case Eng.InV{v} Eng.KVc{}:
      {==}
    case Eng.InV{v} Eng.KSp{}:
      {==}
    case Eng.InV{v} Eng.KHt{}:
      {==}
    case Eng.InV{v} Eng.KLf{}:
      {==}
    case Eng.InV{v} Eng.KCo{}:
      {==}
    case Eng.InV{v} Eng.KCm{}:
      {==}
    case Eng.InV{v} Eng.KCt{}:
      {==}
    case Eng.CrM{} Eng.KLf{}:
      {==}
    case Eng.CrM{} Eng.KSp{}:
      {==}
    case Eng.CrM{} Eng.KHt{}:
      {==}
    case Eng.CrM{} Eng.KCr{}:
      {==}
    case Eng.CrM{} Eng.KCo{}:
      {==}
    case Eng.CrM{} Eng.KCm{}:
      {==}
    case Eng.CrM{} Eng.KDg{}:
      {==}
    case Eng.CrM{} Eng.KTk{}:
      {==}
    case Eng.CrM{} Eng.KVc{}:
      {==}
    case Eng.CrM{} Eng.KCt{}:
      {==}
    case Eng.Lin{} Eng.KCr{}:
      {==}
    case Eng.Lin{} Eng.KTk{}:
      {==}
    case Eng.Lin{} Eng.KDg{}:
      {==}
    case Eng.Lin{} Eng.KSp{}:
      {==}
    case Eng.Lin{} Eng.KHt{}:
      {==}
    case Eng.Lin{} Eng.KLf{}:
      {==}
    case Eng.Lin{} Eng.KCo{}:
      {==}
    case Eng.Lin{} Eng.KCm{}:
      {==}
    case Eng.Lin{} Eng.KVc{}:
      {==}
    case Eng.Lin{} Eng.KCt{}:
      {==}
    case Eng.InN{+n} Eng.KCo{}:
      es.name(Eng.fld.name(n), n, pd)
    case Eng.InN{n} Eng.KTk{}:
      {==}
    case Eng.InN{n} Eng.KDg{}:
      {==}
    case Eng.InN{n} Eng.KSp{}:
      {==}
    case Eng.InN{n} Eng.KHt{}:
      {==}
    case Eng.InN{n} Eng.KCr{}:
      {==}
    case Eng.InN{n} Eng.KLf{}:
      {==}
    case Eng.InN{n} Eng.KCm{}:
      {==}
    case Eng.InN{n} Eng.KVc{}:
      {==}
    case Eng.InN{n} Eng.KCt{}:
      {==}
    case Eng.InL0{} Eng.KSp{}:
      {==}
    case Eng.InL0{} Eng.KHt{}:
      {==}
    case Eng.InL0{} Eng.KDg{}:
      es.digit(0, c, pd)
    case Eng.InL0{} Eng.KCr{}:
      {==}
    case Eng.InL0{} Eng.KLf{}:
      {==}
    case Eng.InL0{} Eng.KCo{}:
      {==}
    case Eng.InL0{} Eng.KCm{}:
      {==}
    case Eng.InL0{} Eng.KTk{}:
      {==}
    case Eng.InL0{} Eng.KVc{}:
      {==}
    case Eng.InL0{} Eng.KCt{}:
      {==}
    case Eng.InL{v} Eng.KDg{}:
      es.digit(v, c, pd)
    case Eng.InL{v} Eng.KSp{}:
      {==}
    case Eng.InL{v} Eng.KHt{}:
      {==}
    case Eng.InL{v} Eng.KCr{}:
      es.clen(v, pd)
    case Eng.InL{v} Eng.KLf{}:
      {==}
    case Eng.InL{v} Eng.KCo{}:
      {==}
    case Eng.InL{v} Eng.KCm{}:
      {==}
    case Eng.InL{v} Eng.KTk{}:
      {==}
    case Eng.InL{v} Eng.KVc{}:
      {==}
    case Eng.InL{v} Eng.KCt{}:
      {==}
    case Eng.InLt{v} Eng.KSp{}:
      {==}
    case Eng.InLt{v} Eng.KHt{}:
      {==}
    case Eng.InLt{v} Eng.KCr{}:
      es.clen(v, pd)
    case Eng.InLt{v} Eng.KLf{}:
      {==}
    case Eng.InLt{v} Eng.KCo{}:
      {==}
    case Eng.InLt{v} Eng.KCm{}:
      {==}
    case Eng.InLt{v} Eng.KDg{}:
      {==}
    case Eng.InLt{v} Eng.KTk{}:
      {==}
    case Eng.InLt{v} Eng.KVc{}:
      {==}
    case Eng.InLt{v} Eng.KCt{}:
      {==}
    case Eng.InLc{t, a, b, e, ms} Eng.KCr{}:
      {==}
    case Eng.InLc{t, a, b, e, ms} Eng.KSp{}:
      {==}
    case Eng.InLc{t, a, b, e, ms} Eng.KHt{}:
      {==}
    case Eng.InLc{t, a, b, e, ms} Eng.KCm{}:
      {==}
    case Eng.InLc{t, a, b, e, ms} Eng.KLf{}:
      {==}
    case Eng.InLc{t, a, b, e, ms} Eng.KCt{}:
      {==}
    case Eng.InLc{t, a, b, e, ms} Eng.KCo{}:
      {==}
    case Eng.InLc{t, a, b, e, ms} Eng.KDg{}:
      {==}
    case Eng.InLc{t, a, b, e, ms} Eng.KTk{}:
      {==}
    case Eng.InLc{t, a, b, e, ms} Eng.KVc{}:
      {==}
    case Eng.InLu{t, w} Eng.KCr{}:
      {==}
    case Eng.InLu{t, w} Eng.KSp{}:
      {==}
    case Eng.InLu{t, w} Eng.KHt{}:
      {==}
    case Eng.InLu{t, w} Eng.KCm{}:
      {==}
    case Eng.InLu{t, w} Eng.KLf{}:
      {==}
    case Eng.InLu{t, w} Eng.KCt{}:
      {==}
    case Eng.InLu{t, w} Eng.KCo{}:
      {==}
    case Eng.InLu{t, w} Eng.KDg{}:
      {==}
    case Eng.InLu{t, w} Eng.KTk{}:
      {==}
    case Eng.InLu{t, w} Eng.KVc{}:
      {==}
    case Eng.InLk0{} Eng.KSp{}:
      {==}
    case Eng.InLk0{} Eng.KHt{}:
      {==}
    case Eng.InLk0{} Eng.KCr{}:
      {==}
    case Eng.InLk0{} Eng.KLf{}:
      {==}
    case Eng.InLk0{} Eng.KCt{}:
      {==}
    case Eng.InLk0{} Eng.KCo{}:
      {==}
    case Eng.InLk0{} Eng.KCm{}:
      {==}
    case Eng.InLk0{} Eng.KDg{}:
      {==}
    case Eng.InLk0{} Eng.KTk{}:
      {==}
    case Eng.InLk0{} Eng.KVc{}:
      {==}
    case Eng.InLk{k} Eng.KCr{}:
      {==}
    case Eng.InLk{k} Eng.KLf{}:
      {==}
    case Eng.InLk{k} Eng.KCt{}:
      {==}
    case Eng.InLk{k} Eng.KSp{}:
      {==}
    case Eng.InLk{k} Eng.KHt{}:
      {==}
    case Eng.InLk{k} Eng.KCo{}:
      {==}
    case Eng.InLk{k} Eng.KCm{}:
      {==}
    case Eng.InLk{k} Eng.KDg{}:
      {==}
    case Eng.InLk{k} Eng.KTk{}:
      {==}
    case Eng.InLk{k} Eng.KVc{}:
      {==}
    case Eng.InLv{v} Eng.KCr{}:
      {==}
    case Eng.InLv{v} Eng.KLf{}:
      {==}
    case Eng.InLv{v} Eng.KCt{}:
      {==}
    case Eng.InLv{v} Eng.KSp{}:
      {==}
    case Eng.InLv{v} Eng.KHt{}:
      {==}
    case Eng.InLv{v} Eng.KCo{}:
      {==}
    case Eng.InLv{v} Eng.KCm{}:
      {==}
    case Eng.InLv{v} Eng.KDg{}:
      {==}
    case Eng.InLv{v} Eng.KTk{}:
      {==}
    case Eng.InLv{v} Eng.KVc{}:
      {==}
    case Eng.InLx{v} Eng.KCr{}:
      {==}
    case Eng.InLx{v} Eng.KLf{}:
      {==}
    case Eng.InLx{v} Eng.KCt{}:
      {==}
    case Eng.InLx{v} Eng.KSp{}:
      {==}
    case Eng.InLx{v} Eng.KHt{}:
      {==}
    case Eng.InLx{v} Eng.KCo{}:
      {==}
    case Eng.InLx{v} Eng.KCm{}:
      {==}
    case Eng.InLx{v} Eng.KDg{}:
      {==}
    case Eng.InLx{v} Eng.KTk{}:
      {==}
    case Eng.InLx{v} Eng.KVc{}:
      {==}
    case Eng.InLe0{} Eng.KSp{}:
      {==}
    case Eng.InLe0{} Eng.KHt{}:
      {==}
    case Eng.InLe0{} Eng.KCr{}:
      {==}
    case Eng.InLe0{} Eng.KLf{}:
      {==}
    case Eng.InLe0{} Eng.KCt{}:
      {==}
    case Eng.InLe0{} Eng.KCo{}:
      {==}
    case Eng.InLe0{} Eng.KCm{}:
      {==}
    case Eng.InLe0{} Eng.KDg{}:
      {==}
    case Eng.InLe0{} Eng.KTk{}:
      {==}
    case Eng.InLe0{} Eng.KVc{}:
      {==}
    case Eng.InLe{v} Eng.KCr{}:
      es.te(v, pd)
    case Eng.InLe{v} Eng.KLf{}:
      {==}
    case Eng.InLe{v} Eng.KCt{}:
      {==}
    case Eng.InLe{v} Eng.KSp{}:
      {==}
    case Eng.InLe{v} Eng.KHt{}:
      {==}
    case Eng.InLe{v} Eng.KCo{}:
      {==}
    case Eng.InLe{v} Eng.KCm{}:
      {==}
    case Eng.InLe{v} Eng.KDg{}:
      {==}
    case Eng.InLe{v} Eng.KTk{}:
      {==}
    case Eng.InLe{v} Eng.KVc{}:
      {==}
    case Eng.CrL{} Eng.KLf{}:
      es.head(pd)
    case Eng.CrL{} Eng.KSp{}:
      {==}
    case Eng.CrL{} Eng.KHt{}:
      {==}
    case Eng.CrL{} Eng.KCr{}:
      {==}
    case Eng.CrL{} Eng.KCo{}:
      {==}
    case Eng.CrL{} Eng.KCm{}:
      {==}
    case Eng.CrL{} Eng.KDg{}:
      {==}
    case Eng.CrL{} Eng.KTk{}:
      {==}
    case Eng.CrL{} Eng.KVc{}:
      {==}
    case Eng.CrL{} Eng.KCt{}:
      {==}
    case Eng.Bod{r, b} _:
      es.body(r, b, c, pd)
    case Eng.Chk{pos, n, b, left} x:
      es.chk(Eng.chk.next(pos, Eng.xk.of(x, c)), n, b, left, pd)
    case Eng.Chd{r, b, left} _:
      es.chd(r, b, c, left, pd)
    case Eng.Rest{bs} _:
      hn
    case Eng.Bad{} _:
      {==}

def oi.step(+st: Eng.St, +pd: Eng.Pend, +c: U32, -o: List<&2, Eng.Req>) ->
  {Eng.step(Eng.P{st, pd, o}, c) == AO(Eng.step(Eng.P{st, pd, Nil{}}, c), o) : Eng.P}:
  oi.at(st, Eng.cls(c), c, pd, Nil{}, o)

def es.step(+st: Eng.St, +pd: Eng.Pend, +c: U32, hn: {nh(st) == True{} : Bool}) ->
  ES(Eng.step(Eng.P{st, pd, Nil{}}, c)):
  es.at(st, Eng.cls(c), c, pd, hn)

# One byte
# ========

# the walk over one more byte is one more step
def walk.snoc(xs: List<&2, U32>, -c: U32, +w: Spec.W) ->
  {Spec.walk(Spec.snoc(xs, c), w) == Spec.next(Spec.walk(xs, w), c) : Spec.W}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      walk.snoc(t, c, Spec.next(w, x))

# and so is the reader's, by the kit's feed_split
def feed.snoc(+xs: List<&2, U32>, +c: U32, +p: Eng.P) ->
  {Eng.feed(Spec.snoc(xs, c), p) == Eng.step(Eng.feed(xs, p), c) : Eng.P}:
  EL.feed_split(xs, Con{c, Nil{}}, p)

# what a byte leaves the reader fed from fresh: still reading, a
# request completed (or one that asked to upgrade), or refused
type OStp is Data:
  SGo{st: Eng.St, pd: Eng.Pend}
  SMsg{r: Eng.Req}
  SUp{r: Eng.Req}
  SBad{}

def ostp.req(ws: Bool, r: Eng.Req) -> OStp:
  match ws:
    case True{}:
      SUp{r}
    case False{}:
      SMsg{r}

def ostp.st(st: Eng.St, pd: Eng.Pend) -> OStp:
  match st:
    case Eng.Bad{}:
      SBad{}
    case _:
      SGo{st, pd}

def ostp.out(st: Eng.St, pd: Eng.Pend, out: List<&2, Eng.Req>) -> OStp:
  match out:
    case Con{+r, t}:
      ostp.req(Eng.req.ws(r), r)
    case Nil{}:
      ostp.st(st, pd)

def ostp.of(p: Eng.P) -> OStp:
  match p:
    case Eng.P{st, pd, out}:
      ostp.out(st, pd, out)

# what the reader's step and the reference's left, related: still
# reading on the same bytes, the same request, or both refused
def StpRel(a: OStp, b: Laws.PStp) -> Type:
  match a b:
    case SGo{st, pd} Laws.PGo{w, r}:
      {Eng.P{st, pd, Nil{}} == Eng.feed(r, Eng.p.new()) : Eng.P} & {w == Spec.walk(r, Laws.w0()) : Spec.W}
    case SMsg{q} Laws.PMsg{r, q2}:
      {q == q2 : Eng.Req}
    case SUp{q} Laws.PUp{r, q2}:
      {q == q2 : Eng.Req}
    case SBad{} Laws.PBad{}:
      Unit
    case _ _:
      Empty

def look.eq(l: EL.Look, m: EL.Look) -> Bool:
  match l m:
    case EL.Reading{} EL.Reading{}:
      True{}
    case EL.Refusing{} EL.Refusing{}:
      True{}
    case EL.Handing{} EL.Handing{}:
      True{}
    case _ _:
      False{}

# two different looks are never equal
def look.no(-g: Type, x: EL.Look, -y: EL.Look, e: {x == y : EL.Look}) -> BD(look.eq(x, y), Unit, g):
  match x:
    case EL.Reading{}:
      %e : BD(look.eq(EL.Reading{}, _), Unit, g)
      Unit{}
    case EL.Refusing{}:
      %e : BD(look.eq(EL.Refusing{}, _), Unit, g)
      Unit{}
    case EL.Handing{}:
      %e : BD(look.eq(EL.Handing{}, _), Unit, g)
      Unit{}

def st.of(p: Eng.P) -> Eng.St:
  match p:
    case Eng.P{st, pd, out}:
      st

def out.of(p: Eng.P) -> List<&2, Eng.Req>:
  match p:
    case Eng.P{st, pd, out}:
      out

def st.bad(st: Eng.St) -> Bool:
  match st:
    case Eng.Bad{}:
      True{}
    case _:
      False{}

def lk.fst(l: List<&2, Eng.Req> & EL.Look) -> List<&2, Eng.Req>:
  Pair.fst(List<&2, Eng.Req>, EL.Look, l)

def lk.snd(l: List<&2, Eng.Req> & EL.Look) -> EL.Look:
  Pair.snd(List<&2, Eng.Req>, EL.Look, l)

# a request completed on the byte: both sides take it
def req.rel(b: Bool, -r: List<&2, U32>, -q: Eng.Req) -> StpRel(ostp.req(b, q), Laws.px.req(b, r, q)):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# none completed, the walk's framing still open: the reader is not
# refused (it reads), and both go on reading the same bytes
def nil.open(st: Eng.St, -pd: Eng.Pend, -r: List<&2, U32>, -mode: Spec.Mode, -since: List<&2, U32>,
  hl: {EL.look.st(st) == EL.Reading{} : EL.Look},
  hp: {Eng.P{st, pd, Nil{}} == Eng.feed(r, Eng.p.new()) : Eng.P},
  hw: {Spec.W{mode, Nil{}, since} == Spec.walk(r, Laws.w0()) : Spec.W}) ->
  StpRel(ostp.st(st, pd), Laws.PGo{Spec.W{mode, Nil{}, since}, r}):
  match st:
    case Eng.Pre{}:
      (hp, hw)
    case Eng.PreLf{}:
      (hp, hw)
    case Eng.InM{m0}:
      (hp, hw)
    case Eng.InT{p0}:
      (hp, hw)
    case Eng.InV{v0}:
      (hp, hw)
    case Eng.CrM{}:
      (hp, hw)
    case Eng.Lin{}:
      (hp, hw)
    case Eng.InN{n0}:
      (hp, hw)
    case Eng.InL0{}:
      (hp, hw)
    case Eng.InL{v0}:
      (hp, hw)
    case Eng.InLt{v0}:
      (hp, hw)
    case Eng.InLc{t0, cl0, up0, ka0, ms0}:
      (hp, hw)
    case Eng.InLu{t0, ws0}:
      (hp, hw)
    case Eng.InLk0{}:
      (hp, hw)
    case Eng.InLk{k0}:
      (hp, hw)
    case Eng.InLv{v0}:
      (hp, hw)
    case Eng.InLx{v0}:
      (hp, hw)
    case Eng.InLe0{}:
      (hp, hw)
    case Eng.InLe{v0}:
      (hp, hw)
    case Eng.CrL{}:
      (hp, hw)
    case Eng.Bod{r0, b0}:
      (hp, hw)
    case Eng.Chk{pos0, n0, b0, left0}:
      (hp, hw)
    case Eng.Chd{r0, b0, left0}:
      (hp, hw)
    case Eng.Rest{bs0}:
      (hp, hw)
    case Eng.Bad{}:
      look.no(Empty, EL.Refusing{}, EL.Reading{}, hl)

# none completed, the framing refused: the reader has refused too
def nil.refused(st: Eng.St, -pd: Eng.Pend, hl: {EL.look.st(st) == EL.Refusing{} : EL.Look}) ->
  StpRel(ostp.st(st, pd), Laws.PBad{}):
  match st:
    case Eng.Pre{}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.PreLf{}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.InM{m0}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.InT{p0}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.InV{v0}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.CrM{}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.Lin{}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.InN{n0}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.InL0{}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.InL{v0}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.InLt{v0}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.InLc{t0, cl0, up0, ka0, ms0}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.InLu{t0, ws0}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.InLk0{}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.InLk{k0}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.InLv{v0}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.InLx{v0}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.InLe0{}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.InLe{v0}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.CrL{}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.Bod{r0, b0}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.Chk{pos0, n0, b0, left0}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.Chd{r0, b0, left0}:
      look.no(Empty, EL.Reading{}, EL.Refusing{}, hl)
    case Eng.Rest{bs0}:
      look.no(Empty, EL.Handing{}, EL.Refusing{}, hl)
    case Eng.Bad{}:
      Unit{}

# none completed after an upgrade (never, but it would read on)
def nil.up(st: Eng.St, -pd: Eng.Pend, -r: List<&2, U32>, -mode: Spec.Mode, -since: List<&2, U32>,
  -b: Bytes(), hs: {st == Eng.Rest{b} : Eng.St},
  hp: {Eng.P{st, pd, Nil{}} == Eng.feed(r, Eng.p.new()) : Eng.P},
  hw: {Spec.W{mode, Nil{}, since} == Spec.walk(r, Laws.w0()) : Spec.W}) ->
  StpRel(ostp.st(st, pd), Laws.PGo{Spec.W{mode, Nil{}, since}, r}):
  match st:
    case Eng.Pre{}:
      (hp, hw)
    case Eng.PreLf{}:
      (hp, hw)
    case Eng.InM{m0}:
      (hp, hw)
    case Eng.InT{p0}:
      (hp, hw)
    case Eng.InV{v0}:
      (hp, hw)
    case Eng.CrM{}:
      (hp, hw)
    case Eng.Lin{}:
      (hp, hw)
    case Eng.InN{n0}:
      (hp, hw)
    case Eng.InL0{}:
      (hp, hw)
    case Eng.InL{v0}:
      (hp, hw)
    case Eng.InLt{v0}:
      (hp, hw)
    case Eng.InLc{t0, cl0, up0, ka0, ms0}:
      (hp, hw)
    case Eng.InLu{t0, ws0}:
      (hp, hw)
    case Eng.InLk0{}:
      (hp, hw)
    case Eng.InLk{k0}:
      (hp, hw)
    case Eng.InLv{v0}:
      (hp, hw)
    case Eng.InLx{v0}:
      (hp, hw)
    case Eng.InLe0{}:
      (hp, hw)
    case Eng.InLe{v0}:
      (hp, hw)
    case Eng.CrL{}:
      (hp, hw)
    case Eng.Bod{r0, b0}:
      (hp, hw)
    case Eng.Chk{pos0, n0, b0, left0}:
      (hp, hw)
    case Eng.Chd{r0, b0, left0}:
      (hp, hw)
    case Eng.Rest{bs0}:
      (hp, hw)
    case Eng.Bad{}:
      no(Empty, Equal.cong(Eng.St, Bool, st.bad, Eng.Rest{b}, Eng.Bad{}, Equal.sym(Eng.St, Eng.Bad{}, Eng.Rest{b}, hs)))

def fin.open(out: List<&2, Eng.Req>, st: Eng.St, +pd: Eng.Pend, -r: List<&2, U32>, +mode: Spec.Mode,
  +since: List<&2, U32>, -rest: List<&2, U32>, he: {Spec.finish.end(mode, since) == Spec.Open{rest} : Spec.End},
  hl: {EL.look.st(st) == EL.Reading{} : EL.Look},
  hp: {Eng.P{st, pd, out} == Eng.feed(r, Eng.p.new()) : Eng.P},
  hw: {Spec.W{mode, out, since} == Spec.walk(r, Laws.w0()) : Spec.W}) ->
  StpRel(ostp.out(st, pd, out), Laws.px.out(mode, out, since, r)):
  match out:
    case Con{+q, t}:
      req.rel(Eng.req.ws(q), r, q)
    case Nil{}:
      %Equal.sym(Spec.End, Spec.finish.end(mode, since), Spec.Open{rest}, he) :
        StpRel(ostp.st(st, pd), Laws.px.end(_, Spec.W{mode, Nil{}, since}, r))
      nil.open(st, pd, r, mode, since, hl, hp, hw)

def fin.refused(out: List<&2, Eng.Req>, st: Eng.St, +pd: Eng.Pend, -r: List<&2, U32>, +mode: Spec.Mode,
  +since: List<&2, U32>, he: {Spec.finish.end(mode, since) == Spec.Refused{} : Spec.End},
  hl: {EL.look.st(st) == EL.Refusing{} : EL.Look}) ->
  StpRel(ostp.out(st, pd, out), Laws.px.out(mode, out, since, r)):
  match out:
    case Con{+q, t}:
      req.rel(Eng.req.ws(q), r, q)
    case Nil{}:
      %Equal.sym(Spec.End, Spec.finish.end(mode, since), Spec.Refused{}, he) :
        StpRel(ostp.st(st, pd), Laws.px.end(_, Spec.W{mode, Nil{}, since}, r))
      nil.refused(st, pd, hl)

def fin.up(out: List<&2, Eng.Req>, st: Eng.St, +pd: Eng.Pend, -r: List<&2, U32>, +mode: Spec.Mode,
  +since: List<&2, U32>, -b: Bytes(), he: {Spec.finish.end(mode, since) == Spec.Upgraded{b} : Spec.End},
  hs: {st == Eng.Rest{b} : Eng.St},
  hp: {Eng.P{st, pd, out} == Eng.feed(r, Eng.p.new()) : Eng.P},
  hw: {Spec.W{mode, out, since} == Spec.walk(r, Laws.w0()) : Spec.W}) ->
  StpRel(ostp.out(st, pd, out), Laws.px.out(mode, out, since, r)):
  match out:
    case Con{+q, t}:
      req.rel(Eng.req.ws(q), r, q)
    case Nil{}:
      %Equal.sym(Spec.End, Spec.finish.end(mode, since), Spec.Upgraded{b}, he) :
        StpRel(ostp.st(st, pd), Laws.px.end(_, Spec.W{mode, Nil{}, since}, r))
      nil.up(st, pd, r, mode, since, b, hs, hp, hw)

# one equality between pairs is two, and one between readers two more
def pair.eqs(-a: List<&2, Eng.Req>, -b: EL.Look, -c: List<&2, Eng.Req>, -d: EL.Look,
  e: {(a, b) == (c, d) : List<&2, Eng.Req> & EL.Look}) -> {a == c : List<&2, Eng.Req>} & {b == d : EL.Look}:
  %Equal.sym(List<&2, Eng.Req> & EL.Look, (a, b), (c, d), e) : {lk.fst(_) == c : List<&2, Eng.Req>} & {lk.snd(_) == d : EL.Look}
  ({==}, {==})

def p.eqs(-st: Eng.St, -pd: Eng.Pend, -out: List<&2, Eng.Req>, -st2: Eng.St, -pd2: Eng.Pend,
  -out2: List<&2, Eng.Req>, e: {Eng.P{st, pd, out} == Eng.P{st2, pd2, out2} : Eng.P}) ->
  {st == st2 : Eng.St} & {out == out2 : List<&2, Eng.Req>}:
  %Equal.sym(Eng.P, Eng.P{st, pd, out}, Eng.P{st2, pd2, out2}, e) : {st.of(_) == st2 : Eng.St} & {out.of(_) == out2 : List<&2, Eng.Req>}
  ({==}, {==})

def e.open(+st: Eng.St, +pd: Eng.Pend, +out: List<&2, Eng.Req>, +mode: Spec.Mode, +o2: List<&2, Eng.Req>,
  +since: List<&2, U32>, -rest: List<&2, U32>, he: {Spec.finish.end(mode, since) == Spec.Open{rest} : Spec.End},
  -r: List<&2, U32>,
  l2: {List.reverse(&2, Eng.Req, out) == List.reverse(&2, Eng.Req, o2) : List<&2, Eng.Req>} &
    {EL.look.st(st) == EL.Reading{} : EL.Look},
  hp: {Eng.P{st, pd, out} == Eng.feed(r, Eng.p.new()) : Eng.P},
  hw: {Spec.W{mode, o2, since} == Spec.walk(r, Laws.w0()) : Spec.W}) ->
  StpRel(ostp.out(st, pd, out), Laws.px.out(mode, o2, since, r)):
  (lr, ls) = l2
  +eq = rev.inj(Eng.Req, out, o2, lr)
  %eq : StpRel(ostp.out(st, pd, out), Laws.px.out(mode, _, since, r))
  fin.open(out, st, pd, r, mode, since, rest, he, ls, hp,
    Equal.trans(Spec.W, Spec.W{mode, out, since}, Spec.W{mode, o2, since}, Spec.walk(r, Laws.w0()),
      Equal.cong(List<&2, Eng.Req>, Spec.W, x => Spec.W{mode, x, since}, out, o2, eq), hw))

def e.refused(+st: Eng.St, +pd: Eng.Pend, +out: List<&2, Eng.Req>, +mode: Spec.Mode, +o2: List<&2, Eng.Req>,
  +since: List<&2, U32>, he: {Spec.finish.end(mode, since) == Spec.Refused{} : Spec.End},
  -r: List<&2, U32>,
  l2: {List.reverse(&2, Eng.Req, out) == List.reverse(&2, Eng.Req, o2) : List<&2, Eng.Req>} &
    {EL.look.st(st) == EL.Refusing{} : EL.Look}) ->
  StpRel(ostp.out(st, pd, out), Laws.px.out(mode, o2, since, r)):
  (lr, ls) = l2
  +eq = rev.inj(Eng.Req, out, o2, lr)
  %eq : StpRel(ostp.out(st, pd, out), Laws.px.out(mode, _, since, r))
  fin.refused(out, st, pd, r, mode, since, he, ls)

def e.up(+st: Eng.St, +pd: Eng.Pend, +out: List<&2, Eng.Req>, +mode: Spec.Mode, +o2: List<&2, Eng.Req>,
  +since: List<&2, U32>, -b: Bytes(), he: {Spec.finish.end(mode, since) == Spec.Upgraded{b} : Spec.End},
  -r: List<&2, U32>,
  p2: {st == Eng.Rest{b} : Eng.St} &
    {out == List.reverse(&2, Eng.Req, List.reverse(&2, Eng.Req, o2)) : List<&2, Eng.Req>},
  hp: {Eng.P{st, pd, out} == Eng.feed(r, Eng.p.new()) : Eng.P},
  hw: {Spec.W{mode, o2, since} == Spec.walk(r, Laws.w0()) : Spec.W}) ->
  StpRel(ostp.out(st, pd, out), Laws.px.out(mode, o2, since, r)):
  (es, eo) = p2
  +eq = Equal.trans(List<&2, Eng.Req>, out, List.reverse(&2, Eng.Req, List.reverse(&2, Eng.Req, o2)), o2, eo,
    rev.rev(Eng.Req, o2))
  %eq : StpRel(ostp.out(st, pd, out), Laws.px.out(mode, _, since, r))
  fin.up(out, st, pd, r, mode, since, b, he, es, hp,
    Equal.trans(Spec.W, Spec.W{mode, out, since}, Spec.W{mode, o2, since}, Spec.walk(r, Laws.w0()),
      Equal.cong(List<&2, Eng.Req>, Spec.W, x => Spec.W{mode, x, since}, out, o2, eq), hw))

# the walk's step and the reader's, compared through frame_sim's
# agreement at the byte, whichever way the framing ends there
def stp.end(+st: Eng.St, +pd: Eng.Pend, +out: List<&2, Eng.Req>, +mode: Spec.Mode, +o2: List<&2, Eng.Req>,
  +since: List<&2, U32>, e: Spec.End, he: {Spec.finish.end(mode, since) == e : Spec.End},
  -r: List<&2, U32>,
  ag: EL.agree.end(Eng.P{st, pd, out}, List.reverse(&2, Eng.Req, o2), e),
  hp: {Eng.P{st, pd, out} == Eng.feed(r, Eng.p.new()) : Eng.P},
  hw: {Spec.W{mode, o2, since} == Spec.walk(r, Laws.w0()) : Spec.W}) ->
  StpRel(ostp.out(st, pd, out), Laws.px.out(mode, o2, since, r)):
  match e:
    case Spec.Open{rest}:
      (l, q) = ag
      e.open(st, pd, out, mode, o2, since, rest, he, r,
        pair.eqs(List.reverse(&2, Eng.Req, out), EL.look.st(st), List.reverse(&2, Eng.Req, o2), EL.Reading{}, l), hp, hw)
    case Spec.Refused{}:
      e.refused(st, pd, out, mode, o2, since, he, r,
        pair.eqs(List.reverse(&2, Eng.Req, out), EL.look.st(st), List.reverse(&2, Eng.Req, o2), EL.Refusing{}, ag))
    case Spec.Upgraded{b}:
      e.up(st, pd, out, mode, o2, since, b, he, r,
        p.eqs(st, pd, out, Eng.Rest{b}, Eng.pend.new(), List.reverse(&2, Eng.Req, List.reverse(&2, Eng.Req, o2)), ag),
        hp, hw)

def stp.at(+pp: Eng.P, +ww: Spec.W, -r: List<&2, U32>,
  ag: EL.agree(pp, Spec.finish(ww)), hp: {pp == Eng.feed(r, Eng.p.new()) : Eng.P},
  hw: {ww == Spec.walk(r, Laws.w0()) : Spec.W}) ->
  StpRel(ostp.of(pp), Laws.px.of(ww, r)):
  match pp ww:
    case Eng.P{+st, +pd, +out} Spec.W{+mode, +o2, +since}:
      stp.end(st, pd, out, mode, o2, since, Spec.finish.end(mode, since), {==}, r, ag, hp, hw)


# frame_sim at the bytes so far, one more byte in
def ag.at(-p: Eng.P, -w: Spec.W, +r: List<&2, U32>, +c: U32,
  hp: {Eng.step(p, c) == Eng.feed(Spec.snoc(r, c), Eng.p.new()) : Eng.P},
  hw: {Spec.next(w, c) == Spec.walk(Spec.snoc(r, c), Laws.w0()) : Spec.W}) ->
  EL.agree(Eng.step(p, c), Spec.finish(Spec.next(w, c))):
  %Equal.sym(Eng.P, Eng.step(p, c), Eng.feed(Spec.snoc(r, c), Eng.p.new()), hp) :
    EL.agree(_, Spec.finish(Spec.next(w, c)))
  %Equal.sym(Spec.W, Spec.next(w, c), Spec.walk(Spec.snoc(r, c), Laws.w0()), hw) :
    EL.agree(Eng.feed(Spec.snoc(r, c), Eng.p.new()), Spec.finish(_))
  EL.frame_sim(Spec.snoc(r, c))

# LEMMA: one byte. The reader's step and the reference's, from a reader
# fed the bytes the walk walked, leave results that agree.
def stp.is(+p: Eng.P, +w: Spec.W, +r: List<&2, U32>, +c: U32,
  rel: {p == Eng.feed(r, Eng.p.new()) : Eng.P} & {w == Spec.walk(r, Laws.w0()) : Spec.W}) ->
  StpRel(ostp.of(Eng.step(p, c)), Laws.px.stp(w, c, r)):
  (e2, e3) = rel
  +hp = Equal.trans(Eng.P, Eng.step(p, c), Eng.step(Eng.feed(r, Eng.p.new()), c),
    Eng.feed(Spec.snoc(r, c), Eng.p.new()),
    Equal.cong(Eng.P, Eng.P, x => Eng.step(x, c), p, Eng.feed(r, Eng.p.new()), e2),
    Equal.sym(Eng.P, Eng.feed(Spec.snoc(r, c), Eng.p.new()), Eng.step(Eng.feed(r, Eng.p.new()), c),
      feed.snoc(r, c, Eng.p.new())))
  +hw = Equal.trans(Spec.W, Spec.next(w, c), Spec.next(Spec.walk(r, Laws.w0()), c),
    Spec.walk(Spec.snoc(r, c), Laws.w0()),
    Equal.cong(Spec.W, Spec.W, x => Spec.next(x, c), w, Spec.walk(r, Laws.w0()), e3),
    Equal.sym(Spec.W, Spec.walk(Spec.snoc(r, c), Laws.w0()), Spec.next(Spec.walk(r, Laws.w0()), c),
      walk.snoc(r, c, Laws.w0())))
  stp.at(Eng.step(p, c), Spec.next(w, c), Spec.snoc(r, c), ag.at(p, w, r, c, hp, hw), hp, hw)

# A read
# ======
#
# The proxy feeds a read whole (feed_buf, which is feed) and takes the
# requests out after; the reference walks the read a byte at a time,
# restarting after each request. GRel relates the reader fed so far,
# with every request it completed in this read behind it, to the
# reference's step and the requests it took, newest first.

# reading: neither refused nor handed over
def rd(st: Eng.St) -> Bool:
  match st:
    case Eng.Bad{}:
      False{}
    case Eng.Rest{bs}:
      False{}
    case _:
      True{}

def GRel.go(q: Eng.P, w: Spec.W, r: List<&2, U32>, acc: List<&2, Laws.PTook>) -> Type:
  match q:
    case Eng.P{st, pd, o}:
      {Eng.P{st, pd, Nil{}} == Eng.feed(r, Eng.p.new()) : Eng.P} & {w == Spec.walk(r, Laws.w0()) : Spec.W} &
        {rd(st) == True{} : Bool} & {o == Laws.took.reqs(acc) : List<&2, Eng.Req>}

def GRel.up(q: Eng.P, r: Eng.Req, acc: List<&2, Laws.PTook>) -> Type:
  match q:
    case Eng.P{st, pd, o}:
      {nh(st) == False{} : Bool} & {o == Con{r, Laws.took.reqs(acc)} : List<&2, Eng.Req>}

def GRel.bad(q: Eng.P, acc: List<&2, Laws.PTook>) -> Type:
  match q:
    case Eng.P{st, pd, o}:
      {st == Eng.Bad{} : Eng.St} & {o == Laws.took.reqs(acc) : List<&2, Eng.Req>}

def GRel(q: Eng.P, b: Laws.PStp, acc: List<&2, Laws.PTook>) -> Type:
  match b:
    case Laws.PGo{w, r}:
      GRel.go(q, w, r, acc)
    case Laws.PMsg{raw, r}:
      {q == Eng.P{Eng.Pre{}, Eng.pend.new(), Con{r, Laws.took.reqs(acc)}} : Eng.P}
    case Laws.PUp{raw, r}:
      GRel.up(q, r, acc)
    case Laws.PBad{}:
      GRel.bad(q, acc)

# the scan waiting after a read, against the walk waiting
def Waits2(sc: X.Scan, w: Spec.W, raw: List<&2, U32>) -> Type:
  match sc:
    case X.Scan{p, n}:
      GRel(p, Laws.PGo{w, raw}, Nil{})

def Tails2(t: X.Tail, u: Laws.PTail) -> Type:
  match t u:
    case X.TWait{sc} Laws.PWait{w, raw}:
      Waits2(sc, w, raw)
    case X.TBad{} Laws.PRefused{}:
      Unit
    case X.TUp{} Laws.PUpgraded{}:
      Unit
    case _ _:
      Empty

def Scans2(s: X.Scanned, f: Laws.PScanned) -> Type:
  match s f:
    case X.Scanned{ts, t} Laws.PScanned{us, u}:
      {ts == Laws.took.reqs(us) : List<&2, Eng.Req>} & Tails2(t, u)

def rd.nh(st: Eng.St, h: {rd(st) == True{} : Bool}) -> {nh(st) == True{} : Bool}:
  match st:
    case Eng.Pre{}:
      {==}
    case Eng.PreLf{}:
      {==}
    case Eng.InM{m0}:
      {==}
    case Eng.InT{p0}:
      {==}
    case Eng.InV{v0}:
      {==}
    case Eng.CrM{}:
      {==}
    case Eng.Lin{}:
      {==}
    case Eng.InN{n0}:
      {==}
    case Eng.InL0{}:
      {==}
    case Eng.InL{v0}:
      {==}
    case Eng.InLt{v0}:
      {==}
    case Eng.InLc{t0, cl0, up0, ka0, ms0}:
      {==}
    case Eng.InLu{t0, ws0}:
      {==}
    case Eng.InLk0{}:
      {==}
    case Eng.InLk{k0}:
      {==}
    case Eng.InLv{v0}:
      {==}
    case Eng.InLx{v0}:
      {==}
    case Eng.InLe0{}:
      {==}
    case Eng.InLe{v0}:
      {==}
    case Eng.CrL{}:
      {==}
    case Eng.Bod{r0, b0}:
      {==}
    case Eng.Chk{pos0, n0, b0, left0}:
      {==}
    case Eng.Chd{r0, b0, left0}:
      {==}
    case Eng.Rest{bs0}:
      no({nh(Eng.Rest{bs0}) == True{} : Bool}, h)
    case Eng.Bad{}:
      {==}

def rest.of(st: Eng.St) -> Bytes():
  match st:
    case Eng.Rest{b}:
      b
    case _:
      ""

def up.st(st: Eng.St, h: {nh(st) == False{} : Bool}) -> {st == Eng.Rest{rest.of(st)} : Eng.St}:
  match st:
    case Eng.Pre{}:
      yes.no({Eng.Pre{} == Eng.Rest{rest.of(Eng.Pre{})} : Eng.St}, h)
    case Eng.PreLf{}:
      yes.no({Eng.PreLf{} == Eng.Rest{rest.of(Eng.PreLf{})} : Eng.St}, h)
    case Eng.InM{m0}:
      yes.no({Eng.InM{m0} == Eng.Rest{rest.of(Eng.InM{m0})} : Eng.St}, h)
    case Eng.InT{p0}:
      yes.no({Eng.InT{p0} == Eng.Rest{rest.of(Eng.InT{p0})} : Eng.St}, h)
    case Eng.InV{v0}:
      yes.no({Eng.InV{v0} == Eng.Rest{rest.of(Eng.InV{v0})} : Eng.St}, h)
    case Eng.CrM{}:
      yes.no({Eng.CrM{} == Eng.Rest{rest.of(Eng.CrM{})} : Eng.St}, h)
    case Eng.Lin{}:
      yes.no({Eng.Lin{} == Eng.Rest{rest.of(Eng.Lin{})} : Eng.St}, h)
    case Eng.InN{n0}:
      yes.no({Eng.InN{n0} == Eng.Rest{rest.of(Eng.InN{n0})} : Eng.St}, h)
    case Eng.InL0{}:
      yes.no({Eng.InL0{} == Eng.Rest{rest.of(Eng.InL0{})} : Eng.St}, h)
    case Eng.InL{v0}:
      yes.no({Eng.InL{v0} == Eng.Rest{rest.of(Eng.InL{v0})} : Eng.St}, h)
    case Eng.InLt{v0}:
      yes.no({Eng.InLt{v0} == Eng.Rest{rest.of(Eng.InLt{v0})} : Eng.St}, h)
    case Eng.InLc{t0, cl0, up0, ka0, ms0}:
      yes.no({Eng.InLc{t0, cl0, up0, ka0, ms0} == Eng.Rest{rest.of(Eng.InLc{t0, cl0, up0, ka0, ms0})} : Eng.St}, h)
    case Eng.InLu{t0, ws0}:
      yes.no({Eng.InLu{t0, ws0} == Eng.Rest{rest.of(Eng.InLu{t0, ws0})} : Eng.St}, h)
    case Eng.InLk0{}:
      yes.no({Eng.InLk0{} == Eng.Rest{rest.of(Eng.InLk0{})} : Eng.St}, h)
    case Eng.InLk{k0}:
      yes.no({Eng.InLk{k0} == Eng.Rest{rest.of(Eng.InLk{k0})} : Eng.St}, h)
    case Eng.InLv{v0}:
      yes.no({Eng.InLv{v0} == Eng.Rest{rest.of(Eng.InLv{v0})} : Eng.St}, h)
    case Eng.InLx{v0}:
      yes.no({Eng.InLx{v0} == Eng.Rest{rest.of(Eng.InLx{v0})} : Eng.St}, h)
    case Eng.InLe0{}:
      yes.no({Eng.InLe0{} == Eng.Rest{rest.of(Eng.InLe0{})} : Eng.St}, h)
    case Eng.InLe{v0}:
      yes.no({Eng.InLe{v0} == Eng.Rest{rest.of(Eng.InLe{v0})} : Eng.St}, h)
    case Eng.CrL{}:
      yes.no({Eng.CrL{} == Eng.Rest{rest.of(Eng.CrL{})} : Eng.St}, h)
    case Eng.Bod{r0, b0}:
      yes.no({Eng.Bod{r0, b0} == Eng.Rest{rest.of(Eng.Bod{r0, b0})} : Eng.St}, h)
    case Eng.Chk{pos0, n0, b0, left0}:
      yes.no({Eng.Chk{pos0, n0, b0, left0} == Eng.Rest{rest.of(Eng.Chk{pos0, n0, b0, left0})} : Eng.St}, h)
    case Eng.Chd{r0, b0, left0}:
      yes.no({Eng.Chd{r0, b0, left0} == Eng.Rest{rest.of(Eng.Chd{r0, b0, left0})} : Eng.St}, h)
    case Eng.Rest{bs0}:
      {==}
    case Eng.Bad{}:
      yes.no({Eng.Bad{} == Eng.Rest{rest.of(Eng.Bad{})} : Eng.St}, h)

# a reader reading waits, on the bytes it was fed
def tail.wait2(st: Eng.St, -pd: Eng.Pend, -m: Nat, -w: Spec.W, -r: List<&2, U32>, hr: {rd(st) == True{} : Bool},
  hp: {Eng.P{st, pd, Nil{}} == Eng.feed(r, Eng.p.new()) : Eng.P}, hw: {w == Spec.walk(r, Laws.w0()) : Spec.W}) ->
  Tails2(X.tail.of(st, pd, m), Laws.PWait{w, r}):
  match st:
    case Eng.Pre{}:
      (hp, (hw, (hr, {==})))
    case Eng.PreLf{}:
      (hp, (hw, (hr, {==})))
    case Eng.InM{m0}:
      (hp, (hw, (hr, {==})))
    case Eng.InT{p0}:
      (hp, (hw, (hr, {==})))
    case Eng.InV{v0}:
      (hp, (hw, (hr, {==})))
    case Eng.CrM{}:
      (hp, (hw, (hr, {==})))
    case Eng.Lin{}:
      (hp, (hw, (hr, {==})))
    case Eng.InN{n0}:
      (hp, (hw, (hr, {==})))
    case Eng.InL0{}:
      (hp, (hw, (hr, {==})))
    case Eng.InL{v0}:
      (hp, (hw, (hr, {==})))
    case Eng.InLt{v0}:
      (hp, (hw, (hr, {==})))
    case Eng.InLc{t0, cl0, up0, ka0, ms0}:
      (hp, (hw, (hr, {==})))
    case Eng.InLu{t0, ws0}:
      (hp, (hw, (hr, {==})))
    case Eng.InLk0{}:
      (hp, (hw, (hr, {==})))
    case Eng.InLk{k0}:
      (hp, (hw, (hr, {==})))
    case Eng.InLv{v0}:
      (hp, (hw, (hr, {==})))
    case Eng.InLx{v0}:
      (hp, (hw, (hr, {==})))
    case Eng.InLe0{}:
      (hp, (hw, (hr, {==})))
    case Eng.InLe{v0}:
      (hp, (hw, (hr, {==})))
    case Eng.CrL{}:
      (hp, (hw, (hr, {==})))
    case Eng.Bod{r0, b0}:
      (hp, (hw, (hr, {==})))
    case Eng.Chk{pos0, n0, b0, left0}:
      (hp, (hw, (hr, {==})))
    case Eng.Chd{r0, b0, left0}:
      (hp, (hw, (hr, {==})))
    case Eng.Rest{bs0}:
      no(Tails2(X.tail.of(Eng.Rest{bs0}, pd, m), Laws.PWait{w, r}), hr)
    case Eng.Bad{}:
      no(Tails2(X.tail.of(Eng.Bad{}, pd, m), Laws.PWait{w, r}), hr)

# the requests the reader completed, oldest first, are the reference's
def rv(o: List<&2, Eng.Req>, +acc: List<&2, Laws.PTook>, ho: {o == Laws.took.reqs(acc) : List<&2, Eng.Req>}) ->
  {List.reverse(&2, Eng.Req, o) == Laws.took.reqs(List.reverse(&2, Laws.PTook, acc)) : List<&2, Eng.Req>}:
  Equal.trans(List<&2, Eng.Req>, List.reverse(&2, Eng.Req, o), List.reverse(&2, Eng.Req, Laws.took.reqs(acc)),
    Laws.took.reqs(List.reverse(&2, Laws.PTook, acc)),
    Equal.cong(List<&2, Eng.Req>, List<&2, Eng.Req>, xs => List.reverse(&2, Eng.Req, xs), o, Laws.took.reqs(acc), ho),
    Equal.sym(List<&2, Eng.Req>, Laws.took.reqs(List.reverse(&2, Laws.PTook, acc)),
      List.reverse(&2, Eng.Req, Laws.took.reqs(acc)), treqs.rev(acc)))

# after an upgrade, the reader holds what follows
def restb(bs: List<&2, U32>, b: Bytes()) -> Bytes():
  match bs:
    case Nil{}:
      b
    case Con{c, t}:
      restb(t, Eng.push(b, c))

def rest.feed(bs: List<&2, U32>, +b: Bytes(), -pd: Eng.Pend, -o: List<&2, Eng.Req>) ->
  {Eng.feed(bs, Eng.P{Eng.Rest{b}, pd, o}) == Eng.P{Eng.Rest{restb(bs, b)}, pd, o} : Eng.P}:
  match bs:
    case Nil{}:
      {==}
    case Con{+c, t}:
      rest.feed(t, Eng.push(b, c), pd, o)

# The end of a read
# -----------------

def fed.bad(o: List<&2, Eng.Req>, -pd: Eng.Pend, -n: Nat, -k: Nat, +acc: List<&2, Laws.PTook>,
  ho: {o == Laws.took.reqs(acc) : List<&2, Eng.Req>}) ->
  Scans2(X.scan.took(Eng.Bad{}, pd, X.head.n(o, n, k)), Laws.PScanned{List.reverse(&2, Laws.PTook, acc), Laws.PRefused{}}):
  match o:
    case Nil{}:
      (rv(Nil{}, acc, ho), Unit{})
    case Con{h, t}:
      (rv(Con{h, t}, acc, ho), Unit{})

def end.bad(bs: List<&2, U32>, q: Eng.P, +acc: List<&2, Laws.PTook>, -n: Nat, -k: Nat, g: GRel(q, Laws.PBad{}, acc)) ->
  Scans2(X.scan.fed(Eng.feed(bs, q), n, k), Laws.px.done(acc, Laws.PRefused{})):
  match q:
    case Eng.P{st, +pd, +o}:
      (hs, ho) = g
      %Equal.sym(Eng.St, st, Eng.Bad{}, hs) :
        Scans2(X.scan.fed(Eng.feed(bs, Eng.P{_, pd, o}), n, k), Laws.px.done(acc, Laws.PRefused{}))
      %Equal.sym(Eng.P, Eng.feed(bs, Eng.P{Eng.Bad{}, pd, o}), Eng.P{Eng.Bad{}, pd, o}, EL.bad_feeds(bs, pd, o)) :
        Scans2(X.scan.fed(_, n, k), Laws.px.done(acc, Laws.PRefused{}))
      fed.bad(o, pd, n, k, acc, ho)

def end.up(bs: List<&2, U32>, q: Eng.P, +acc: List<&2, Laws.PTook>, +raw: List<&2, U32>, +r: Eng.Req, -n: Nat, -k: Nat,
  g: GRel(q, Laws.PUp{raw, r}, acc)) ->
  Scans2(X.scan.fed(Eng.feed(bs, q), n, k), Laws.px.done(Con{Laws.PTook{raw, r}, acc}, Laws.PUpgraded{})):
  match q:
    case Eng.P{+st, +pd, +o}:
      (hn, ho) = g
      %Equal.sym(Eng.St, st, Eng.Rest{rest.of(st)}, up.st(st, hn)) :
        Scans2(X.scan.fed(Eng.feed(bs, Eng.P{_, pd, o}), n, k),
          Laws.px.done(Con{Laws.PTook{raw, r}, acc}, Laws.PUpgraded{}))
      %Equal.sym(Eng.P, Eng.feed(bs, Eng.P{Eng.Rest{rest.of(st)}, pd, o}),
        Eng.P{Eng.Rest{restb(bs, rest.of(st))}, pd, o}, rest.feed(bs, rest.of(st), pd, o)) :
        Scans2(X.scan.fed(_, n, k), Laws.px.done(Con{Laws.PTook{raw, r}, acc}, Laws.PUpgraded{}))
      %Equal.sym(List<&2, Eng.Req>, o, Con{r, Laws.took.reqs(acc)}, ho) :
        Scans2(X.scan.fed(Eng.P{Eng.Rest{restb(bs, rest.of(st))}, pd, _}, n, k),
          Laws.px.done(Con{Laws.PTook{raw, r}, acc}, Laws.PUpgraded{}))
      (Equal.sym(List<&2, Eng.Req>, Laws.took.reqs(List.reverse(&2, Laws.PTook, Con{Laws.PTook{raw, r}, acc})),
        List.reverse(&2, Eng.Req, Con{r, Laws.took.reqs(acc)}), treqs.rev(Con{Laws.PTook{raw, r}, acc})), Unit{})

def fed.wait(o: List<&2, Eng.Req>, +st: Eng.St, +pd: Eng.Pend, -n: Nat, -k: Nat, +acc: List<&2, Laws.PTook>,
  -w: Spec.W, -r: List<&2, U32>, ho: {o == Laws.took.reqs(acc) : List<&2, Eng.Req>}, hr: {rd(st) == True{} : Bool},
  hp: {Eng.P{st, pd, Nil{}} == Eng.feed(r, Eng.p.new()) : Eng.P}, hw: {w == Spec.walk(r, Laws.w0()) : Spec.W}) ->
  Scans2(X.scan.took(st, pd, X.head.n(o, n, k)), Laws.PScanned{List.reverse(&2, Laws.PTook, acc), Laws.PWait{w, r}}):
  match o:
    case Nil{}:
      (rv(Nil{}, acc, ho), tail.wait2(st, pd, Nat.add(n, k), w, r, hr, hp, hw))
    case Con{h, t}:
      (rv(Con{h, t}, acc, ho), tail.wait2(st, pd, k, w, r, hr, hp, hw))

def end.wait(q: Eng.P, -w: Spec.W, -r: List<&2, U32>, +acc: List<&2, Laws.PTook>, -n: Nat, -k: Nat,
  g: GRel(q, Laws.PGo{w, r}, acc)) ->
  Scans2(X.scan.fed(Eng.feed(Nil{}, q), n, k), Laws.px.done(acc, Laws.PWait{w, r})):
  match q:
    case Eng.P{+st, +pd, o}:
      (hp, g2) = g
      (hw, g3) = g2
      (hr, ho) = g3
      fed.wait(o, st, pd, n, k, acc, w, r, ho, hr, hp, hw)

def end.msg(-q: Eng.P, +raw: List<&2, U32>, +r: Eng.Req, +acc: List<&2, Laws.PTook>, -n: Nat, -k: Nat,
  g: GRel(q, Laws.PMsg{raw, r}, acc)) ->
  Scans2(X.scan.fed(Eng.feed(Nil{}, q), n, k), Laws.px.done(Con{Laws.PTook{raw, r}, acc}, Laws.PWait{Laws.w0(), Nil{}})):
  %Equal.sym(Eng.P, q, Eng.P{Eng.Pre{}, Eng.pend.new(), Con{r, Laws.took.reqs(acc)}}, g) :
    Scans2(X.scan.fed(Eng.feed(Nil{}, _), n, k), Laws.px.done(Con{Laws.PTook{raw, r}, acc}, Laws.PWait{Laws.w0(), Nil{}}))
  (Equal.sym(List<&2, Eng.Req>, Laws.took.reqs(List.reverse(&2, Laws.PTook, Con{Laws.PTook{raw, r}, acc})),
    List.reverse(&2, Eng.Req, Con{r, Laws.took.reqs(acc)}), treqs.rev(Con{Laws.PTook{raw, r}, acc})),
    ({==}, ({==}, ({==}, {==}))))

# One byte, on both
# -----------------

def go.sgo(-st: Eng.St, -pd: Eng.Pend, b: Laws.PStp, -o: List<&2, Eng.Req>, -acc: List<&2, Laws.PTook>,
  hr: {rd(st) == True{} : Bool}, ho: {o == Laws.took.reqs(acc) : List<&2, Eng.Req>}, rel: StpRel(SGo{st, pd}, b)) ->
  GRel(Eng.P{st, pd, o}, b, acc):
  match b:
    case Laws.PGo{w, r}:
      (hp, hw) = rel
      (hp, (hw, (hr, ho)))
    case Laws.PMsg{raw, r}:
      match rel:
    case Laws.PUp{raw, r}:
      match rel:
    case Laws.PBad{}:
      match rel:

def go.bad(-pd: Eng.Pend, b: Laws.PStp, -o: List<&2, Eng.Req>, -acc: List<&2, Laws.PTook>,
  ho: {o == Laws.took.reqs(acc) : List<&2, Eng.Req>}, rel: StpRel(SBad{}, b)) ->
  GRel(Eng.P{Eng.Bad{}, pd, o}, b, acc):
  match b:
    case Laws.PBad{}:
      ({==}, ho)
    case Laws.PGo{w, r}:
      match rel:
    case Laws.PMsg{raw, r}:
      match rel:
    case Laws.PUp{raw, r}:
      match rel:

# none completed on the byte
def go.nil(st: Eng.St, -pd: Eng.Pend, b: Laws.PStp, -o: List<&2, Eng.Req>, -acc: List<&2, Laws.PTook>,
  ho: {o == Laws.took.reqs(acc) : List<&2, Eng.Req>}, rel: StpRel(ostp.st(st, pd), b),
  sh: {nh(st) == True{} : Bool}) ->
  GRel(Eng.P{st, pd, o}, b, acc):
  match st:
    case Eng.Pre{}:
      go.sgo(Eng.Pre{}, pd, b, o, acc, {==}, ho, rel)
    case Eng.PreLf{}:
      go.sgo(Eng.PreLf{}, pd, b, o, acc, {==}, ho, rel)
    case Eng.InM{m0}:
      go.sgo(Eng.InM{m0}, pd, b, o, acc, {==}, ho, rel)
    case Eng.InT{p0}:
      go.sgo(Eng.InT{p0}, pd, b, o, acc, {==}, ho, rel)
    case Eng.InV{v0}:
      go.sgo(Eng.InV{v0}, pd, b, o, acc, {==}, ho, rel)
    case Eng.CrM{}:
      go.sgo(Eng.CrM{}, pd, b, o, acc, {==}, ho, rel)
    case Eng.Lin{}:
      go.sgo(Eng.Lin{}, pd, b, o, acc, {==}, ho, rel)
    case Eng.InN{n0}:
      go.sgo(Eng.InN{n0}, pd, b, o, acc, {==}, ho, rel)
    case Eng.InL0{}:
      go.sgo(Eng.InL0{}, pd, b, o, acc, {==}, ho, rel)
    case Eng.InL{v0}:
      go.sgo(Eng.InL{v0}, pd, b, o, acc, {==}, ho, rel)
    case Eng.InLt{v0}:
      go.sgo(Eng.InLt{v0}, pd, b, o, acc, {==}, ho, rel)
    case Eng.InLc{t0, cl0, up0, ka0, ms0}:
      go.sgo(Eng.InLc{t0, cl0, up0, ka0, ms0}, pd, b, o, acc, {==}, ho, rel)
    case Eng.InLu{t0, ws0}:
      go.sgo(Eng.InLu{t0, ws0}, pd, b, o, acc, {==}, ho, rel)
    case Eng.InLk0{}:
      go.sgo(Eng.InLk0{}, pd, b, o, acc, {==}, ho, rel)
    case Eng.InLk{k0}:
      go.sgo(Eng.InLk{k0}, pd, b, o, acc, {==}, ho, rel)
    case Eng.InLv{v0}:
      go.sgo(Eng.InLv{v0}, pd, b, o, acc, {==}, ho, rel)
    case Eng.InLx{v0}:
      go.sgo(Eng.InLx{v0}, pd, b, o, acc, {==}, ho, rel)
    case Eng.InLe0{}:
      go.sgo(Eng.InLe0{}, pd, b, o, acc, {==}, ho, rel)
    case Eng.InLe{v0}:
      go.sgo(Eng.InLe{v0}, pd, b, o, acc, {==}, ho, rel)
    case Eng.CrL{}:
      go.sgo(Eng.CrL{}, pd, b, o, acc, {==}, ho, rel)
    case Eng.Bod{r0, b0}:
      go.sgo(Eng.Bod{r0, b0}, pd, b, o, acc, {==}, ho, rel)
    case Eng.Chk{pos0, n0, b0, left0}:
      go.sgo(Eng.Chk{pos0, n0, b0, left0}, pd, b, o, acc, {==}, ho, rel)
    case Eng.Chd{r0, b0, left0}:
      go.sgo(Eng.Chd{r0, b0, left0}, pd, b, o, acc, {==}, ho, rel)
    case Eng.Rest{bs0}:
      no(GRel(Eng.P{Eng.Rest{bs0}, pd, o}, b, acc), sh)
    case Eng.Bad{}:
      go.bad(pd, b, o, acc, ho, rel)

# one completed on the byte: the reference took it too
def go.req(ws: Bool, -q: Eng.Req, b: Laws.PStp, -o: List<&2, Eng.Req>, -acc: List<&2, Laws.PTook>,
  ho: {o == Laws.took.reqs(acc) : List<&2, Eng.Req>}, rel: StpRel(ostp.req(ws, q), b)) ->
  GRel(Eng.P{Eng.emit.next(ws), Eng.pend.new(), Con{q, o}}, b, acc):
  match ws b:
    case True{} Laws.PUp{raw, q2}:
      %Equal.sym(Eng.Req, q, q2, rel) : GRel(Eng.P{Eng.Rest{""}, Eng.pend.new(), Con{_, o}}, Laws.PUp{raw, q2}, acc)
      ({==}, Equal.cong(List<&2, Eng.Req>, List<&2, Eng.Req>, xs => Con{q2, xs}, o, Laws.took.reqs(acc), ho))
    case True{} Laws.PGo{w, r}:
      match rel:
    case True{} Laws.PMsg{raw, q2}:
      match rel:
    case True{} Laws.PBad{}:
      match rel:
    case False{} Laws.PMsg{raw, q2}:
      %Equal.sym(Eng.Req, q, q2, rel) : GRel(Eng.P{Eng.Pre{}, Eng.pend.new(), Con{_, o}}, Laws.PMsg{raw, q2}, acc)
      Equal.cong(List<&2, Eng.Req>, Eng.P, xs => Eng.P{Eng.Pre{}, Eng.pend.new(), Con{q2, xs}}, o, Laws.took.reqs(acc), ho)
    case False{} Laws.PGo{w, r}:
      match rel:
    case False{} Laws.PUp{raw, q2}:
      match rel:
    case False{} Laws.PBad{}:
      match rel:

def go.con(-st: Eng.St, -pd: Eng.Pend, +q: Eng.Req, -t: List<&2, Eng.Req>, b: Laws.PStp, -o: List<&2, Eng.Req>,
  -acc: List<&2, Laws.PTook>, ho: {o == Laws.took.reqs(acc) : List<&2, Eng.Req>},
  rel: StpRel(ostp.req(Eng.req.ws(q), q), b), sh: ES.out(st, pd, Con{q, t})) ->
  GRel(Eng.P{st, pd, Con{q, List.append(&2, Eng.Req, t, o)}}, b, acc):
  (ht, sh2) = sh
  (hs, hpd) = sh2
  %Equal.sym(List<&2, Eng.Req>, t, Nil{}, ht) :
    GRel(Eng.P{st, pd, Con{q, List.append(&2, Eng.Req, _, o)}}, b, acc)
  %Equal.sym(Eng.St, st, Eng.emit.next(Eng.req.ws(q)), hs) :
    GRel(Eng.P{_, pd, Con{q, o}}, b, acc)
  %Equal.sym(Eng.Pend, pd, Eng.pend.new(), hpd) :
    GRel(Eng.P{Eng.emit.next(Eng.req.ws(q)), _, Con{q, o}}, b, acc)
  go.req(Eng.req.ws(q), q, b, o, acc, ho, rel)

def go.at2(q0: Eng.P, b: Laws.PStp, -o: List<&2, Eng.Req>, -acc: List<&2, Laws.PTook>,
  ho: {o == Laws.took.reqs(acc) : List<&2, Eng.Req>}, rel: StpRel(ostp.of(q0), b), sh: ES(q0)) ->
  GRel(AO(q0, o), b, acc):
  match q0:
    case Eng.P{st, pd, x}:
      match x:
        case Nil{}:
          go.nil(st, pd, b, o, acc, ho, rel, sh)
        case Con{q, t}:
          go.con(st, pd, q, t, b, o, acc, ho, rel, sh)

# LEMMA: one byte. The reader's step with the requests of this read
# behind it, and the reference's, from states related, leave states
# related.
def go.at(q: Eng.P, +w: Spec.W, +r: List<&2, U32>, +c: U32, -acc: List<&2, Laws.PTook>,
  g: GRel(q, Laws.PGo{w, r}, acc)) ->
  GRel(Eng.step(q, c), Laws.px.stp(w, c, r), acc):
  match q:
    case Eng.P{+st, +pd, o}:
      (hp, g2) = g
      (hw, g3) = g2
      (hr, ho) = g3
      %Equal.sym(Eng.P, Eng.step(Eng.P{st, pd, o}, c), AO(Eng.step(Eng.P{st, pd, Nil{}}, c), o), oi.step(st, pd, c, o)) :
        GRel(_, Laws.px.stp(w, c, r), acc)
      go.at2(Eng.step(Eng.P{st, pd, Nil{}}, c), Laws.px.stp(w, c, r), o, acc, ho,
        stp.is(Eng.P{st, pd, Nil{}}, w, r, c, (hp, hw)), es.step(st, pd, c, rd.nh(st, hr)))

# just after a request, a fresh reader: the reference's fresh walk
def go.msg(-q: Eng.P, -raw: List<&2, U32>, +r: Eng.Req, +c: U32, +acc: List<&2, Laws.PTook>,
  g: GRel(q, Laws.PMsg{raw, r}, acc)) ->
  GRel(Eng.step(q, c), Laws.px.stp(Laws.w0(), c, Nil{}), Con{Laws.PTook{raw, r}, acc}):
  %Equal.sym(Eng.P, q, Eng.P{Eng.Pre{}, Eng.pend.new(), Con{r, Laws.took.reqs(acc)}}, g) :
    GRel(Eng.step(_, c), Laws.px.stp(Laws.w0(), c, Nil{}), Con{Laws.PTook{raw, r}, acc})
  go.at(Eng.P{Eng.Pre{}, Eng.pend.new(), Con{r, Laws.took.reqs(acc)}}, Laws.w0(), Nil{}, c,
    Con{Laws.PTook{raw, r}, acc}, ({==}, ({==}, ({==}, {==}))))

# LEMMA: a read, a byte at a time on both sides
def go.is(bs: List<&2, U32>, +q: Eng.P, b: Laws.PStp, +acc: List<&2, Laws.PTook>, -n: Nat, -k: Nat,
  g: GRel(q, b, acc)) ->
  Scans2(X.scan.fed(Eng.feed(bs, q), n, k), Laws.px.go(bs, b, acc)):
  match bs b:
    case Nil{} Laws.PBad{}:
      end.bad(Nil{}, q, acc, n, k, g)
    case Con{c, t} Laws.PBad{}:
      end.bad(Con{c, t}, q, acc, n, k, g)
    case Nil{} Laws.PUp{raw, r}:
      end.up(Nil{}, q, acc, raw, r, n, k, g)
    case Con{c, t} Laws.PUp{raw, r}:
      end.up(Con{c, t}, q, acc, raw, r, n, k, g)
    case Nil{} Laws.PGo{w, r}:
      end.wait(q, w, r, acc, n, k, g)
    case Nil{} Laws.PMsg{raw, r}:
      end.msg(q, raw, r, acc, n, k, g)
    case Con{+c, t} Laws.PGo{+w, +r}:
      go.is(t, Eng.step(q, c), Laws.px.stp(w, c, r), acc, n, k, go.at(q, w, r, c, acc, g))
    case Con{+c, t} Laws.PMsg{raw, +r}:
      go.is(t, Eng.step(q, c), Laws.px.stp(Laws.w0(), c, Nil{}), Con{Laws.PTook{raw, r}, acc}, n, k,
        go.msg(q, raw, r, c, acc, g))

# LEMMA: a read. The proxy's scan of a read and the reference's walk of
# its bytes, from a scan that waits as the walk does, take the same
# requests and end the same way.
def read.is(+s: Bytes(), sc: X.Scan, +w: Spec.W, +raw: List<&2, U32>, wt: Waits2(sc, w, raw)) ->
  Scans2(X.scan(s, sc), Laws.px.go(Bytes.to_list(s), Laws.PGo{w, raw}, Nil{})):
  match sc:
    case X.Scan{+p, n}:
      %Equal.sym(Eng.P, Eng.feed_buf(s, p), Eng.feed(Bytes.to_list(s), p), EL.feed_buf_is_feed(s, p)) :
        Scans2(X.scan.fed(_, n, Bytes.len(s)), Laws.px.go(Bytes.to_list(s), Laws.PGo{w, raw}, Nil{}))
      go.is(Bytes.to_list(s), p, Laws.PGo{w, raw}, Nil{}, n, Bytes.len(s), wt)

# A stream cut in two
# ===================

# requests taken before, put in front
def pre(xs: List<&2, Laws.PTook>, f: Laws.PScanned) -> Laws.PScanned:
  match f:
    case Laws.PScanned{us, u}:
      Laws.PScanned{List.append(&2, Laws.PTook, xs, us), u}

# the rest of a stream, walked on from where the first part ended
def then(f: Laws.PScanned, ys: List<&2, U32>) -> Laws.PScanned:
  match f:
    case Laws.PScanned{us, u}:
      match u:
        case Laws.PWait{w, raw}:
          Laws.px.go(ys, Laws.PGo{w, raw}, List.reverse(&2, Laws.PTook, us))
        case Laws.PRefused{}:
          Laws.PScanned{us, Laws.PRefused{}}
        case Laws.PUpgraded{}:
          Laws.PScanned{us, Laws.PUpgraded{}}

def pre.pre(+a: List<&2, Laws.PTook>, +b: List<&2, Laws.PTook>, f: Laws.PScanned) ->
  {pre(List.append(&2, Laws.PTook, a, b), f) == pre(a, pre(b, f)) : Laws.PScanned}:
  match f:
    case Laws.PScanned{us, u}:
      Equal.cong(List<&2, Laws.PTook>, Laws.PScanned, x => Laws.PScanned{x, u},
        List.append(&2, Laws.PTook, List.append(&2, Laws.PTook, a, b), us),
        List.append(&2, Laws.PTook, a, List.append(&2, Laws.PTook, b, us)), app.assoc(Laws.PTook, a, b, us))

def done.nil(+acc: List<&2, Laws.PTook>, u: Laws.PTail) ->
  {Laws.px.done(acc, u) == pre(List.reverse(&2, Laws.PTook, acc), Laws.px.done(Nil{}, u)) : Laws.PScanned}:
  Equal.cong(List<&2, Laws.PTook>, Laws.PScanned, x => Laws.PScanned{x, u}, List.reverse(&2, Laws.PTook, acc),
    List.append(&2, Laws.PTook, List.reverse(&2, Laws.PTook, acc), Nil{}),
    Equal.sym(List<&2, Laws.PTook>, List.append(&2, Laws.PTook, List.reverse(&2, Laws.PTook, acc), Nil{}),
      List.reverse(&2, Laws.PTook, acc), app.nil(Laws.PTook, List.reverse(&2, Laws.PTook, acc))))

def done.one(+x: Laws.PTook, +acc: List<&2, Laws.PTook>, u: Laws.PTail) ->
  {Laws.px.done(Con{x, acc}, u) == pre(List.reverse(&2, Laws.PTook, acc), Laws.px.done(Con{x, Nil{}}, u)) :
    Laws.PScanned}:
  Equal.cong(List<&2, Laws.PTook>, Laws.PScanned, y => Laws.PScanned{y, u}, List.reverse(&2, Laws.PTook, Con{x, acc}),
    List.append(&2, Laws.PTook, List.reverse(&2, Laws.PTook, acc), Con{x, Nil{}}), rev.con(Laws.PTook, x, acc))

# the requests taken before a walk are in front of what it takes
def go.acc(+bs: List<&2, U32>, st: Laws.PStp, +acc: List<&2, Laws.PTook>) ->
  {Laws.px.go(bs, st, acc) == pre(List.reverse(&2, Laws.PTook, acc), Laws.px.go(bs, st, Nil{})) : Laws.PScanned}:
  match bs st:
    case Nil{} Laws.PBad{}:
      done.nil(acc, Laws.PRefused{})
    case Nil{} Laws.PUp{raw, r}:
      done.one(Laws.PTook{raw, r}, acc, Laws.PUpgraded{})
    case Nil{} Laws.PGo{w, raw}:
      done.nil(acc, Laws.PWait{w, raw})
    case Nil{} Laws.PMsg{raw, r}:
      done.one(Laws.PTook{raw, r}, acc, Laws.PWait{Laws.w0(), Nil{}})
    case Con{c, t} Laws.PBad{}:
      done.nil(acc, Laws.PRefused{})
    case Con{c, t} Laws.PUp{raw, r}:
      done.one(Laws.PTook{raw, r}, acc, Laws.PUpgraded{})
    case Con{+c, +t} Laws.PGo{w, raw}:
      go.acc(t, Laws.px.stp(w, c, raw), acc)
    case Con{+c, +t} Laws.PMsg{+raw, +r}:
      Equal.trans(Laws.PScanned, Laws.px.go(t, Laws.px.stp(Laws.w0(), c, Nil{}), Con{Laws.PTook{raw, r}, acc}),
        pre(List.reverse(&2, Laws.PTook, Con{Laws.PTook{raw, r}, acc}), Laws.px.go(t, Laws.px.stp(Laws.w0(), c, Nil{}), Nil{})),
        pre(List.reverse(&2, Laws.PTook, acc), Laws.px.go(t, Laws.px.stp(Laws.w0(), c, Nil{}), Con{Laws.PTook{raw, r}, Nil{}})),
        go.acc(t, Laws.px.stp(Laws.w0(), c, Nil{}), Con{Laws.PTook{raw, r}, acc}),
        Equal.trans(Laws.PScanned,
          pre(List.reverse(&2, Laws.PTook, Con{Laws.PTook{raw, r}, acc}), Laws.px.go(t, Laws.px.stp(Laws.w0(), c, Nil{}), Nil{})),
          pre(List.reverse(&2, Laws.PTook, acc), pre(Con{Laws.PTook{raw, r}, Nil{}}, Laws.px.go(t, Laws.px.stp(Laws.w0(), c, Nil{}), Nil{}))),
          pre(List.reverse(&2, Laws.PTook, acc), Laws.px.go(t, Laws.px.stp(Laws.w0(), c, Nil{}), Con{Laws.PTook{raw, r}, Nil{}})),
          %Equal.sym(List<&2, Laws.PTook>, List.reverse(&2, Laws.PTook, Con{Laws.PTook{raw, r}, acc}),
            List.append(&2, Laws.PTook, List.reverse(&2, Laws.PTook, acc), Con{Laws.PTook{raw, r}, Nil{}}),
            rev.con(Laws.PTook, Laws.PTook{raw, r}, acc)) :
            {pre(_, Laws.px.go(t, Laws.px.stp(Laws.w0(), c, Nil{}), Nil{})) ==
              pre(List.reverse(&2, Laws.PTook, acc), pre(Con{Laws.PTook{raw, r}, Nil{}}, Laws.px.go(t, Laws.px.stp(Laws.w0(), c, Nil{}), Nil{}))) :
              Laws.PScanned}
          pre.pre(List.reverse(&2, Laws.PTook, acc), Con{Laws.PTook{raw, r}, Nil{}},
            Laws.px.go(t, Laws.px.stp(Laws.w0(), c, Nil{}), Nil{})),
          Equal.cong(Laws.PScanned, Laws.PScanned, f => pre(List.reverse(&2, Laws.PTook, acc), f),
            pre(Con{Laws.PTook{raw, r}, Nil{}}, Laws.px.go(t, Laws.px.stp(Laws.w0(), c, Nil{}), Nil{})),
            Laws.px.go(t, Laws.px.stp(Laws.w0(), c, Nil{}), Con{Laws.PTook{raw, r}, Nil{}}),
            Equal.sym(Laws.PScanned, Laws.px.go(t, Laws.px.stp(Laws.w0(), c, Nil{}), Con{Laws.PTook{raw, r}, Nil{}}),
              pre(Con{Laws.PTook{raw, r}, Nil{}}, Laws.px.go(t, Laws.px.stp(Laws.w0(), c, Nil{}), Nil{})),
              go.acc(t, Laws.px.stp(Laws.w0(), c, Nil{}), Con{Laws.PTook{raw, r}, Nil{}})))))

# a walk over a stream is a walk over its first part, then its rest
def go.app0(ys: List<&2, U32>, st: Laws.PStp, +acc: List<&2, Laws.PTook>) ->
  {Laws.px.go(ys, st, acc) == then(Laws.px.go(Nil{}, st, acc), ys) : Laws.PScanned}:
  match ys st:
    case Nil{} Laws.PBad{}:
      {==}
    case Con{c, t} Laws.PBad{}:
      {==}
    case Nil{} Laws.PUp{raw, r}:
      {==}
    case Con{c, t} Laws.PUp{raw, r}:
      {==}
    case Nil{} Laws.PGo{w, raw}:
      %rev.rev(Laws.PTook, acc) : {Laws.px.go(Nil{}, Laws.PGo{w, raw}, _) ==
        Laws.px.go(Nil{}, Laws.PGo{w, raw}, List.reverse(&2, Laws.PTook, List.reverse(&2, Laws.PTook, acc))) :
        Laws.PScanned}
      {==}
    case Con{c, t} Laws.PGo{w, raw}:
      %rev.rev(Laws.PTook, acc) : {Laws.px.go(Con{c, t}, Laws.PGo{w, raw}, _) ==
        Laws.px.go(Con{c, t}, Laws.PGo{w, raw}, List.reverse(&2, Laws.PTook, List.reverse(&2, Laws.PTook, acc))) :
        Laws.PScanned}
      {==}
    case Nil{} Laws.PMsg{raw, r}:
      %rev.rev(Laws.PTook, Con{Laws.PTook{raw, r}, acc}) : {Laws.px.go(Nil{}, Laws.PGo{Laws.w0(), Nil{}}, _) ==
        Laws.px.go(Nil{}, Laws.PGo{Laws.w0(), Nil{}},
          List.reverse(&2, Laws.PTook, List.reverse(&2, Laws.PTook, Con{Laws.PTook{raw, r}, acc}))) : Laws.PScanned}
      {==}
    case Con{c, t} Laws.PMsg{raw, r}:
      %rev.rev(Laws.PTook, Con{Laws.PTook{raw, r}, acc}) : {Laws.px.go(Con{c, t}, Laws.PGo{Laws.w0(), Nil{}}, _) ==
        Laws.px.go(Con{c, t}, Laws.PGo{Laws.w0(), Nil{}},
          List.reverse(&2, Laws.PTook, List.reverse(&2, Laws.PTook, Con{Laws.PTook{raw, r}, acc}))) : Laws.PScanned}
      {==}

def go.app(xs: List<&2, U32>, +ys: List<&2, U32>, st: Laws.PStp, +acc: List<&2, Laws.PTook>) ->
  {Laws.px.go(List.append(&2, U32, xs, ys), st, acc) == then(Laws.px.go(xs, st, acc), ys) : Laws.PScanned}:
  match xs st:
    case Nil{} _:
      go.app0(ys, st, acc)
    case Con{c, t} Laws.PBad{}:
      {==}
    case Con{c, t} Laws.PUp{raw, r}:
      {==}
    case Con{+c, t} Laws.PGo{w, raw}:
      go.app(t, ys, Laws.px.stp(w, c, raw), acc)
    case Con{+c, t} Laws.PMsg{raw, r}:
      go.app(t, ys, Laws.px.stp(Laws.w0(), c, Nil{}), Con{Laws.PTook{raw, r}, acc})

# The reads of a connection
# =========================

def treqs.app(xs: List<&2, Laws.PTook>, -ys: List<&2, Laws.PTook>) ->
  {Laws.took.reqs(List.append(&2, Laws.PTook, xs, ys)) == List.append(&2, Eng.Req, Laws.took.reqs(xs), Laws.took.reqs(ys)) : List<&2, Eng.Req>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      match h:
        case Laws.PTook{raw, +q}:
          Equal.cong(List<&2, Eng.Req>, List<&2, Eng.Req>, zs => Con{q, zs}, Laws.took.reqs(List.append(&2, Laws.PTook, t, ys)), List.append(&2, Eng.Req, Laws.took.reqs(t), Laws.took.reqs(ys)), treqs.app(t, ys))

# the proxy's connection so far against the reference's walk: the
# requests the reference took before (pre) and then the connection's
def RA(pre: List<&2, Laws.PTook>, c: Laws.Conn, f: Laws.PScanned) -> Type:
  match c f:
    case Laws.Conn{ts, t} Laws.PScanned{us, u}:
      {List.append(&2, Eng.Req, Laws.took.reqs(pre), ts) == Laws.took.reqs(us) : List<&2, Eng.Req>} & Tails2(t, u)

def ra.rw(-ra1: List<&2, Laws.PTook>, -ra2: List<&2, Laws.PTook>, -c: Laws.Conn, -f: Laws.PScanned,
  e: {ra1 == ra2 : List<&2, Laws.PTook>}, h: RA(ra1, c, f)) -> RA(ra2, c, f):
  %e : RA(_, c, f)
  h

def more.ra(+ts: List<&2, Eng.Req>, c: Laws.Conn, f: Laws.PScanned, +ra: List<&2, Laws.PTook>,
  +us: List<&2, Laws.PTook>, hts: {ts == Laws.took.reqs(us) : List<&2, Eng.Req>},
  h: RA(List.append(&2, Laws.PTook, ra, us), c, f)) -> RA(ra, Laws.conn.more(ts, c), f):
  match c f:
    case Laws.Conn{+ts2, t2} Laws.PScanned{us2, u2}:
      (h1, h2) = h
      (Equal.trans(List<&2, Eng.Req>, List.append(&2, Eng.Req, Laws.took.reqs(ra), List.append(&2, Eng.Req, ts, ts2)), List.append(&2, Eng.Req, Laws.took.reqs(List.append(&2, Laws.PTook, ra, us)), ts2), Laws.took.reqs(us2),
        Equal.trans(List<&2, Eng.Req>, List.append(&2, Eng.Req, Laws.took.reqs(ra), List.append(&2, Eng.Req, ts, ts2)), List.append(&2, Eng.Req, Laws.took.reqs(ra), List.append(&2, Eng.Req, Laws.took.reqs(us), ts2)), List.append(&2, Eng.Req, Laws.took.reqs(List.append(&2, Laws.PTook, ra, us)), ts2),
          Equal.cong(List<&2, Eng.Req>, List<&2, Eng.Req>, x => List.append(&2, Eng.Req, Laws.took.reqs(ra), List.append(&2, Eng.Req, x, ts2)), ts, Laws.took.reqs(us), hts),
          Equal.trans(List<&2, Eng.Req>, List.append(&2, Eng.Req, Laws.took.reqs(ra), List.append(&2, Eng.Req, Laws.took.reqs(us), ts2)), List.append(&2, Eng.Req, List.append(&2, Eng.Req, Laws.took.reqs(ra), Laws.took.reqs(us)), ts2), List.append(&2, Eng.Req, Laws.took.reqs(List.append(&2, Laws.PTook, ra, us)), ts2),
            Equal.sym(List<&2, Eng.Req>, List.append(&2, Eng.Req, List.append(&2, Eng.Req, Laws.took.reqs(ra), Laws.took.reqs(us)), ts2), List.append(&2, Eng.Req, Laws.took.reqs(ra), List.append(&2, Eng.Req, Laws.took.reqs(us), ts2)),
              app.assoc(Eng.Req, Laws.took.reqs(ra), Laws.took.reqs(us), ts2)),
            Equal.cong(List<&2, Eng.Req>, List<&2, Eng.Req>, x => List.append(&2, Eng.Req, x, ts2),
              List.append(&2, Eng.Req, Laws.took.reqs(ra), Laws.took.reqs(us)), Laws.took.reqs(List.append(&2, Laws.PTook, ra, us)),
              Equal.sym(List<&2, Eng.Req>, Laws.took.reqs(List.append(&2, Laws.PTook, ra, us)), List.append(&2, Eng.Req, Laws.took.reqs(ra), Laws.took.reqs(us)), treqs.app(ra, us))))),
        h1), h2)

def tail.wait(+ts: List<&2, Eng.Req>, +sc2: X.Scan, +w2: Spec.W, +raw2: List<&2, U32>, +us: List<&2, Laws.PTook>,
  hts: {ts == Laws.took.reqs(us) : List<&2, Eng.Req>}, wt: Waits2(sc2, w2, raw2), +t: List<&2, Bytes()>,
  +ra: List<&2, Laws.PTook>,
  ih: @+sc: X.Scan -> @+w: Spec.W -> @+raw: List<&2, U32> -> @+pr: List<&2, Laws.PTook> -> Waits2(sc, w, raw) ->
    RA(List.reverse(&2, Laws.PTook, pr), Laws.reads.go(t, sc), Laws.px.go(Bytes.to_list(Bytes.concat(t)), Laws.PGo{w, raw}, pr))) ->
  RA(ra, Laws.conn.more(ts, Laws.reads.go(t, sc2)), Laws.px.go(Bytes.to_list(Bytes.concat(t)), Laws.PGo{w2, raw2},
    List.reverse(&2, Laws.PTook, List.append(&2, Laws.PTook, ra, us)))):
  more.ra(ts, Laws.reads.go(t, sc2), Laws.px.go(Bytes.to_list(Bytes.concat(t)), Laws.PGo{w2, raw2},
      List.reverse(&2, Laws.PTook, List.append(&2, Laws.PTook, ra, us))), ra, us, hts,
    ra.rw(List.reverse(&2, Laws.PTook, List.reverse(&2, Laws.PTook, List.append(&2, Laws.PTook, ra, us))),
      List.append(&2, Laws.PTook, ra, us), Laws.reads.go(t, sc2),
      Laws.px.go(Bytes.to_list(Bytes.concat(t)), Laws.PGo{w2, raw2},
        List.reverse(&2, Laws.PTook, List.append(&2, Laws.PTook, ra, us))),
      rev.rev(Laws.PTook, List.append(&2, Laws.PTook, ra, us)),
      ih(sc2, w2, raw2, List.reverse(&2, Laws.PTook, List.append(&2, Laws.PTook, ra, us)), wt)))

# a read that ends refused or upgraded ends the connection on both
def ra.end(+ts: List<&2, Eng.Req>, +ra: List<&2, Laws.PTook>, +us: List<&2, Laws.PTook>,
  hts: {ts == Laws.took.reqs(us) : List<&2, Eng.Req>}) ->
  {List.append(&2, Eng.Req, Laws.took.reqs(ra), ts) == Laws.took.reqs(List.append(&2, Laws.PTook, ra, us)) :
    List<&2, Eng.Req>}:
  Equal.trans(List<&2, Eng.Req>, List.append(&2, Eng.Req, Laws.took.reqs(ra), ts), List.append(&2, Eng.Req, Laws.took.reqs(ra), Laws.took.reqs(us)), Laws.took.reqs(List.append(&2, Laws.PTook, ra, us)),
    Equal.cong(List<&2, Eng.Req>, List<&2, Eng.Req>, x => List.append(&2, Eng.Req, Laws.took.reqs(ra), x), ts,
      Laws.took.reqs(us), hts),
    Equal.sym(List<&2, Eng.Req>, Laws.took.reqs(List.append(&2, Laws.PTook, ra, us)), List.append(&2, Eng.Req, Laws.took.reqs(ra), Laws.took.reqs(us)), treqs.app(ra, us)))

def reads.tail(+ts: List<&2, Eng.Req>, tl: X.Tail, +us: List<&2, Laws.PTook>, u: Laws.PTail,
  hts: {ts == Laws.took.reqs(us) : List<&2, Eng.Req>}, ht: Tails2(tl, u), +t: List<&2, Bytes()>,
  +ra: List<&2, Laws.PTook>,
  ih: @+sc: X.Scan -> @+w: Spec.W -> @+raw: List<&2, U32> -> @+pr: List<&2, Laws.PTook> -> Waits2(sc, w, raw) ->
    RA(List.reverse(&2, Laws.PTook, pr), Laws.reads.go(t, sc), Laws.px.go(Bytes.to_list(Bytes.concat(t)), Laws.PGo{w, raw}, pr))) ->
  RA(ra, Laws.reads.at(X.Scanned{ts, tl}, s2 => Laws.reads.go(t, s2)),
    then(pre(ra, Laws.PScanned{us, u}), Bytes.to_list(Bytes.concat(t)))):
  match tl u:
    case X.TWait{sc2} Laws.PWait{w2, raw2}:
      tail.wait(ts, sc2, w2, raw2, us, hts, ht, t, ra, ih)
    case X.TWait{sc2} Laws.PRefused{}:
      match ht:
    case X.TWait{sc2} Laws.PUpgraded{}:
      match ht:
    case X.TBad{} Laws.PWait{w2, raw2}:
      match ht:
    case X.TBad{} Laws.PRefused{}:
      (ra.end(ts, ra, us, hts), Unit{})
    case X.TBad{} Laws.PUpgraded{}:
      match ht:
    case X.TUp{} Laws.PWait{w2, raw2}:
      match ht:
    case X.TUp{} Laws.PRefused{}:
      match ht:
    case X.TUp{} Laws.PUpgraded{}:
      (ra.end(ts, ra, us, hts), Unit{})

def reads.step(sd: X.Scanned, f: Laws.PScanned, hs: Scans2(sd, f), +t: List<&2, Bytes()>,
  +ra: List<&2, Laws.PTook>,
  ih: @+sc: X.Scan -> @+w: Spec.W -> @+raw: List<&2, U32> -> @+pr: List<&2, Laws.PTook> -> Waits2(sc, w, raw) ->
    RA(List.reverse(&2, Laws.PTook, pr), Laws.reads.go(t, sc), Laws.px.go(Bytes.to_list(Bytes.concat(t)), Laws.PGo{w, raw}, pr))) ->
  RA(ra, Laws.reads.at(sd, s2 => Laws.reads.go(t, s2)), then(pre(ra, f), Bytes.to_list(Bytes.concat(t)))):
  match sd f:
    case X.Scanned{+ts, tl} Laws.PScanned{+us, u}:
      (hts, ht) = hs
      reads.tail(ts, tl, us, u, hts, ht, t, ra, ih)

def reads.con(+r: Bytes(), +t: List<&2, Bytes()>, +sc: X.Scan, +w: Spec.W, +raw: List<&2, U32>,
  +pr: List<&2, Laws.PTook>, wt: Waits2(sc, w, raw),
  ih: @+sc: X.Scan -> @+w: Spec.W -> @+raw: List<&2, U32> -> @+pr: List<&2, Laws.PTook> -> Waits2(sc, w, raw) ->
    RA(List.reverse(&2, Laws.PTook, pr), Laws.reads.go(t, sc), Laws.px.go(Bytes.to_list(Bytes.concat(t)), Laws.PGo{w, raw}, pr))) ->
  RA(List.reverse(&2, Laws.PTook, pr), Laws.reads.go(Con{r, t}, sc),
    then(pre(List.reverse(&2, Laws.PTook, pr), Laws.px.go(Bytes.to_list(r), Laws.PGo{w, raw}, Nil{})),
      Bytes.to_list(Bytes.concat(t)))):
  reads.step(X.scan(r, sc), Laws.px.go(Bytes.to_list(r), Laws.PGo{w, raw}, Nil{}),
    read.is(r, sc, w, raw, wt), t, List.reverse(&2, Laws.PTook, pr), ih)

# LEMMA: a connection's reads. Whatever the reads, from a scan that
# agrees with a walk, the connection agrees with the walk over the reads
# joined, the requests the walk took before in front.
def reads.is(rs: List<&2, Bytes()>, +sc: X.Scan, +w: Spec.W, +raw: List<&2, U32>, +pr: List<&2, Laws.PTook>,
  wt: Waits2(sc, w, raw)) ->
  RA(List.reverse(&2, Laws.PTook, pr), Laws.reads.go(rs, sc),
    Laws.px.go(Bytes.to_list(Bytes.concat(rs)), Laws.PGo{w, raw}, pr)):
  match rs:
    case Nil{}:
      (app.nil(Eng.Req, Laws.took.reqs(List.reverse(&2, Laws.PTook, pr))), wt)
    case Con{+r, +t}:
      %Equal.sym(List<&2, U32>, Bytes.to_list(Bytes.append(r, Bytes.concat(t))),
        List.append(&2, U32, Bytes.to_list(r), Bytes.to_list(Bytes.concat(t))),
        Bytes.to_list_append(r, Bytes.concat(t))) :
        RA(List.reverse(&2, Laws.PTook, pr), Laws.reads.go(Con{r, t}, sc), Laws.px.go(_, Laws.PGo{w, raw}, pr))
      %Equal.sym(Laws.PScanned,
        Laws.px.go(List.append(&2, U32, Bytes.to_list(r), Bytes.to_list(Bytes.concat(t))), Laws.PGo{w, raw}, pr),
        then(Laws.px.go(Bytes.to_list(r), Laws.PGo{w, raw}, pr), Bytes.to_list(Bytes.concat(t))),
        go.app(Bytes.to_list(r), Bytes.to_list(Bytes.concat(t)), Laws.PGo{w, raw}, pr)) :
        RA(List.reverse(&2, Laws.PTook, pr), Laws.reads.go(Con{r, t}, sc), _)
      %Equal.sym(Laws.PScanned, Laws.px.go(Bytes.to_list(r), Laws.PGo{w, raw}, pr),
        pre(List.reverse(&2, Laws.PTook, pr), Laws.px.go(Bytes.to_list(r), Laws.PGo{w, raw}, Nil{})),
        go.acc(Bytes.to_list(r), Laws.PGo{w, raw}, pr)) :
        RA(List.reverse(&2, Laws.PTook, pr), Laws.reads.go(Con{r, t}, sc), then(_, Bytes.to_list(Bytes.concat(t))))
      reads.con(r, t, sc, w, raw, pr, wt,
        sc2 => w2 => raw2 => pr2 => wt2 => reads.is(t, sc2, w2, raw2, pr2, wt2))

# the scan the proxy waits with, as the laws state it
def waits.of(sc: X.Scan, -w: Spec.W, -raw: List<&2, U32>, h: Waits2(sc, w, raw)) -> Laws.Waits(sc, w, raw):
  match sc:
    case X.Scan{p, n}:
      match p:
        case Eng.P{st, pd, o}:
          (hp, h2) = h
          (hw, h3) = h2
          (hr, ho) = h3
          %Equal.sym(List<&2, Eng.Req>, o, Nil{}, ho) :
            {Eng.P{st, pd, _} == Eng.feed(raw, Eng.p.new()) : Eng.P} & {w == Spec.walk(raw, Laws.w0()) : Spec.W}
          (hp, hw)

def tails.of(t: X.Tail, u: Laws.PTail, h: Tails2(t, u)) -> Laws.Tails(t, u):
  match t u:
    case X.TWait{sc} Laws.PWait{w, raw}:
      waits.of(sc, w, raw, h)
    case X.TBad{} Laws.PRefused{}:
      Unit{}
    case X.TUp{} Laws.PUpgraded{}:
      Unit{}
    case X.TWait{sc} Laws.PRefused{}:
      match h:
    case X.TWait{sc} Laws.PUpgraded{}:
      match h:
    case X.TBad{} Laws.PWait{w, raw}:
      match h:
    case X.TBad{} Laws.PUpgraded{}:
      match h:
    case X.TUp{} Laws.PWait{w, raw}:
      match h:
    case X.TUp{} Laws.PRefused{}:
      match h:

def ra.conns(c: Laws.Conn, f: Laws.PScanned, h: RA(Nil{}, c, f)) -> Laws.Conns(c, f):
  match c f:
    case Laws.Conn{ts, t} Laws.PScanned{us, u}:
      (h1, h2) = h
      (h1, tails.of(t, u, h2))

def Laws.scan_is_spec(rs):
  ra.conns(Laws.reads(rs), Laws.frame(Bytes.to_list(Bytes.concat(rs))),
    reads.is(rs, X.scan.new(), Laws.w0(), Nil{}, Nil{}, ({==}, ({==}, ({==}, {==})))))

# spec.bend's walk and the requests it has done
# ==============================================
#
# frames_agree: the reference framing restarts a fresh walk after each
# request, frame() walks on. The two are one walk because nothing the
# walk does looks at the requests it has done: every step only puts one
# more in front of them. shift puts a list of done requests behind a
# walk's own; each of spec.bend's step functions, given done requests o,
# is the same function given none, shifted by o.

def shift(w: Spec.W, o: List<&2, Eng.Req>) -> Spec.W:
  match w:
    case Spec.W{m, x, s}:
      Spec.W{m, List.append(&2, Eng.Req, x, o), s}

def emit.go.par(r: Eng.Req, -o: List<&2, Eng.Req>) ->
  {Spec.emit.go(r, o) == shift(Spec.emit.go(r, Nil{}), o) : Spec.W}:
  match r:
    case Eng.Req{m, p, b, cl, ws, k, d}:
      {==}

def emit.par(+h: Spec.Head, +body: List<&2, U32>, -o: List<&2, Eng.Req>) ->
  {Spec.emit(h, body, o) == shift(Spec.emit(h, body, Nil{}), o) : Spec.W}:
  emit.go.par(Spec.req(h, body), o)

def head.body.par(z: Bool, +n: U32, +h: Spec.Head, -o: List<&2, Eng.Req>, -s: List<&2, U32>) ->
  {Spec.head.body(z, n, h, o, s) == shift(Spec.head.body(z, n, h, Nil{}, s), o) : Spec.W}:
  match z:
    case True{}:
      emit.par(h, Nil{}, o)
    case False{}:
      {==}

def head.at.par(ok: Bool, b: Spec.Body, +h: Spec.Head, -o: List<&2, Eng.Req>, -s: List<&2, U32>) ->
  {Spec.head.at(ok, b, h, o, s) == shift(Spec.head.at(ok, b, h, Nil{}, s), o) : Spec.W}:
  match ok b:
    case False{} _:
      {==}
    case True{} Spec.BBad{}:
      {==}
    case True{} Spec.BNone{}:
      emit.par(h, Nil{}, o)
    case True{} Spec.BLen{+n}:
      head.body.par(U32.is_zero(n), n, h, o, s)
    case True{} Spec.BChunked{}:
      {==}

def head.done.par(h: Spec.Head, -o: List<&2, Eng.Req>, -s: List<&2, U32>) ->
  {Spec.head.done(h, o, s) == shift(Spec.head.done(h, Nil{}, s), o) : Spec.W}:
  match h:
    case Spec.Head{m, t, +l, cl, +hs, k, u, c, v, f, hx}:
      match f:
        case Eng.Fx{+v10, ka, +te}:
          head.at.par(Spec.hosts.ok(v10, hs), Spec.body.of(te, v10, l),
            Spec.Head{m, t, l, cl, hs, k, u, c, v, Eng.Fx{v10, ka, te}, hx}, o, s)

def chunk.paid.par(over: Bool, +h: Spec.Head, +at: Spec.At, +n: U32, +got: List<&2, U32>, +left: U32,
  -o: List<&2, Eng.Req>, -s: List<&2, U32>) ->
  {Spec.chunk.paid(over, h, at, n, got, left, o, s) == shift(Spec.chunk.paid(over, h, at, n, got, left, Nil{}, s), o) : Spec.W}:
  match over:
    case True{}:
      {==}
    case False{}:
      {==}

def chunk.to.par(paid: Bool, +h: Spec.Head, +at: Spec.At, +n: U32, +got: List<&2, U32>, +left: U32,
  -o: List<&2, Eng.Req>, -s: List<&2, U32>) ->
  {Spec.chunk.to(paid, h, at, n, got, left, o, s) == shift(Spec.chunk.to(paid, h, at, n, got, left, Nil{}, s), o) : Spec.W}:
  match paid:
    case True{}:
      chunk.paid.par(U32.is_le(left, n), h, at, n, got, left, o, s)
    case False{}:
      {==}

def chunk.line.par(z: Bool, +h: Spec.Head, +n: U32, +got: List<&2, U32>, +left: U32, -o: List<&2, Eng.Req>,
  -s: List<&2, U32>) ->
  {Spec.chunk.line(z, h, n, got, left, o, s) == shift(Spec.chunk.line(z, h, n, got, left, Nil{}, s), o) : Spec.W}:
  match z:
    case True{}:
      {==}
    case False{}:
      {==}

def chunk.go.par(g: Spec.Go, +h: Spec.Head, +n: U32, +got: List<&2, U32>, +left: U32, -o: List<&2, Eng.Req>,
  -s: List<&2, U32>) ->
  {Spec.chunk.go(g, h, n, got, left, o, s) == shift(Spec.chunk.go(g, h, n, got, left, Nil{}, s), o) : Spec.W}:
  match g:
    case Spec.GBad{}:
      {==}
    case Spec.GTo{at, paid}:
      chunk.to.par(paid, h, at, n, got, left, o, s)
    case Spec.GDigit{+d}:
      chunk.paid.par(U32.is_le(left, (n * 16 + d : U32)), h, Spec.ASize{}, (n * 16 + d : U32), got, left, o, s)
    case Spec.GLine{}:
      chunk.line.par(U32.is_zero(n), h, n, got, left, o, s)
    case Spec.GDone{}:
      emit.par(h, got, o)

def data.byte.par(more: Nat, +c: U32, +h: Spec.Head, +got: List<&2, U32>, +left: U32, -o: List<&2, Eng.Req>,
  -s: List<&2, U32>) ->
  {Spec.data.byte(more, c, h, got, left, o, s) == shift(Spec.data.byte(more, c, h, got, left, Nil{}, s), o) : Spec.W}:
  match more:
    case 0n:
      {==}
    case 1n+q:
      {==}

def req.ok.par(v11: Bool, v10: Bool, +m: List<&2, U32>, +t: List<&2, U32>, -o: List<&2, Eng.Req>,
  -s: List<&2, U32>) ->
  {Spec.req.ok(v11, v10, m, t, o, s) == shift(Spec.req.ok(v11, v10, m, t, Nil{}, s), o) : Spec.W}:
  match v11 v10:
    case True{} _:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def req.cr.par(v: Spec.RLine, -o: List<&2, Eng.Req>, -s: List<&2, U32>) ->
  {Spec.req.cr(v, o, s) == shift(Spec.req.cr(v, Nil{}, s), o) : Spec.W}:
  match v:
    case Spec.RNone{}:
      {==}
    case Spec.RVer{m, t, +ver}:
      req.ok.par(Spec.eq(Bytes.from_list(ver), "HTTP/1.1"), Spec.eq(Bytes.from_list(ver), "HTTP/1.0"), m, t, o, s)
    case Spec.RMeth{m}:
      {==}
    case Spec.RTarget{m, t}:
      {==}
    case Spec.RBad{}:
      {==}

def field.next.par(mh: Maybe<&2, Spec.Head>, -o: List<&2, Eng.Req>, -s: List<&2, U32>) ->
  {Spec.field.next(mh, o, s) == shift(Spec.field.next(mh, Nil{}, s), o) : Spec.W}:
  match mh:
    case Some{h}:
      {==}
    case None{}:
      {==}

def field.cr.par(+h: Spec.Head, v: Spec.FLine, -o: List<&2, Eng.Req>, -s: List<&2, U32>) ->
  {Spec.field.cr(h, v, o, s) == shift(Spec.field.cr(h, v, Nil{}, s), o) : Spec.W}:
  match v:
    case Spec.FEmpty{}:
      {==}
    case Spec.FVal{val}:
      field.next.par(Spec.field.done(h, val), o, s)
    case Spec.FName{n}:
      {==}
    case Spec.FBad{}:
      {==}

def req.byte.par(k: Eng.Cls, +c: U32, +cur: List<&2, U32>, -o: List<&2, Eng.Req>, -s: List<&2, U32>) ->
  {Spec.req.byte(k, c, cur, o, s) == shift(Spec.req.byte(k, c, cur, Nil{}, s), o) : Spec.W}:
  match k:
    case Eng.KSp{}:
      {==}
    case Eng.KHt{}:
      {==}
    case Eng.KCr{}:
      req.cr.par(Spec.req.view(cur), o, s)
    case Eng.KLf{}:
      {==}
    case Eng.KCo{}:
      {==}
    case Eng.KCm{}:
      {==}
    case Eng.KDg{}:
      {==}
    case Eng.KTk{}:
      {==}
    case Eng.KVc{}:
      {==}
    case Eng.KCt{}:
      {==}

def field.byte.par(k: Eng.Cls, +c: U32, +h: Spec.Head, +cur: List<&2, U32>, -o: List<&2, Eng.Req>,
  -s: List<&2, U32>) ->
  {Spec.field.byte(k, c, h, cur, o, s) == shift(Spec.field.byte(k, c, h, cur, Nil{}, s), o) : Spec.W}:
  match k:
    case Eng.KSp{}:
      {==}
    case Eng.KHt{}:
      {==}
    case Eng.KCr{}:
      field.cr.par(h, Spec.field.view(cur), o, s)
    case Eng.KLf{}:
      {==}
    case Eng.KCo{}:
      {==}
    case Eng.KCm{}:
      {==}
    case Eng.KDg{}:
      {==}
    case Eng.KTk{}:
      {==}
    case Eng.KVc{}:
      {==}
    case Eng.KCt{}:
      {==}

def blank.byte.par(k: Eng.Cls, -o: List<&2, Eng.Req>, -s: List<&2, U32>) ->
  {Spec.blank.byte(k, o, s) == shift(Spec.blank.byte(k, Nil{}, s), o) : Spec.W}:
  match k:
    case Eng.KSp{}:
      {==}
    case Eng.KHt{}:
      {==}
    case Eng.KCr{}:
      {==}
    case Eng.KLf{}:
      {==}
    case Eng.KCo{}:
      {==}
    case Eng.KCm{}:
      {==}
    case Eng.KDg{}:
      {==}
    case Eng.KTk{}:
      {==}
    case Eng.KVc{}:
      {==}
    case Eng.KCt{}:
      {==}

def eol.byte.par(k: Eng.Cls, +h: Spec.Head, -o: List<&2, Eng.Req>, -s: List<&2, U32>) ->
  {Spec.eol.byte(k, h, o, s) == shift(Spec.eol.byte(k, h, Nil{}, s), o) : Spec.W}:
  match k:
    case Eng.KSp{}:
      {==}
    case Eng.KHt{}:
      {==}
    case Eng.KCr{}:
      {==}
    case Eng.KLf{}:
      {==}
    case Eng.KCo{}:
      {==}
    case Eng.KCm{}:
      {==}
    case Eng.KDg{}:
      {==}
    case Eng.KTk{}:
      {==}
    case Eng.KVc{}:
      {==}
    case Eng.KCt{}:
      {==}

def eoh.byte.par(k: Eng.Cls, +h: Spec.Head, -o: List<&2, Eng.Req>, -s: List<&2, U32>) ->
  {Spec.eoh.byte(k, h, o, s) == shift(Spec.eoh.byte(k, h, Nil{}, s), o) : Spec.W}:
  match k:
    case Eng.KSp{}:
      {==}
    case Eng.KHt{}:
      {==}
    case Eng.KCr{}:
      {==}
    case Eng.KLf{}:
      head.done.par(h, o, s)
    case Eng.KCo{}:
      {==}
    case Eng.KCm{}:
      {==}
    case Eng.KDg{}:
      {==}
    case Eng.KTk{}:
      {==}
    case Eng.KVc{}:
      {==}
    case Eng.KCt{}:
      {==}

def body.byte.par(more: Nat, +c: U32, +h: Spec.Head, +got: List<&2, U32>, -o: List<&2, Eng.Req>,
  -s: List<&2, U32>) ->
  {Spec.body.byte(more, c, h, got, o, s) == shift(Spec.body.byte(more, c, h, got, Nil{}, s), o) : Spec.W}:
  match more:
    case 0n:
      emit.par(h, Spec.snoc(got, c), o)
    case 1n+q:
      {==}

def next.at.par(mode: Spec.Mode, +k: Eng.Cls, +c: U32, -o: List<&2, Eng.Req>, -s: List<&2, U32>) ->
  {Spec.next.at(mode, k, c, o, s) == shift(Spec.next.at(mode, k, c, Nil{}, s), o) : Spec.W}:
  match mode:
    case Spec.MReq{cur}:
      req.byte.par(k, c, cur, o, s)
    case Spec.MBlank{}:
      blank.byte.par(k, o, s)
    case Spec.MField{h, cur}:
      field.byte.par(k, c, h, cur, o, s)
    case Spec.MEol{h}:
      eol.byte.par(k, h, o, s)
    case Spec.MEoh{h}:
      eoh.byte.par(k, h, o, s)
    case Spec.MBody{h, more, got}:
      body.byte.par(more, c, h, got, o, s)
    case Spec.MChunk{h, at, n, got, left}:
      chunk.go.par(Spec.chunk.step(at, Spec.xk.of(k, c)), h, n, got, left, o, s)
    case Spec.MData{h, more, got, left}:
      data.byte.par(more, c, h, got, left, o, s)
    case Spec.MUp{got}:
      {==}
    case Spec.MBad{}:
      {==}

# LEMMA: a step does not look at the requests done
def next.par(+m: Spec.Mode, -o: List<&2, Eng.Req>, +s: List<&2, U32>, +c: U32) ->
  {Spec.next(Spec.W{m, o, s}, c) == shift(Spec.next(Spec.W{m, Nil{}, s}, c), o) : Spec.W}:
  next.at.par(m, Spec.cls(c), c, o, Spec.snoc(s, c))

# and when a step does a request, it is the only one, and the walk
# starts again: a fresh line, nothing since, or what follows an upgrade
def Shape(w: Spec.W) -> Type:
  match w:
    case Spec.W{m, x, s}:
      match x:
        case Nil{}:
          Unit
        case Con{r, t}:
          {t == Nil{} : List<&2, Eng.Req>} & {s == Nil{} : List<&2, U32>} & {m == Spec.emit.mode(Eng.req.ws(r)) : Spec.Mode}

def emit.go.shape(r: Eng.Req) ->
  Shape(Spec.emit.go(r, Nil{})):
  match r:
    case Eng.Req{m, p, b, cl, ws, k, d}:
      ({==}, ({==}, {==}))

def emit.shape(+h: Spec.Head, +body: List<&2, U32>) ->
  Shape(Spec.emit(h, body, Nil{})):
  emit.go.shape(Spec.req(h, body))

def head.body.shape(z: Bool, +n: U32, +h: Spec.Head, -s: List<&2, U32>) ->
  Shape(Spec.head.body(z, n, h, Nil{}, s)):
  match z:
    case True{}:
      emit.shape(h, Nil{})
    case False{}:
      Unit{}

def head.at.shape(ok: Bool, b: Spec.Body, +h: Spec.Head, -s: List<&2, U32>) ->
  Shape(Spec.head.at(ok, b, h, Nil{}, s)):
  match ok b:
    case False{} _:
      Unit{}
    case True{} Spec.BBad{}:
      Unit{}
    case True{} Spec.BNone{}:
      emit.shape(h, Nil{})
    case True{} Spec.BLen{+n}:
      head.body.shape(U32.is_zero(n), n, h, s)
    case True{} Spec.BChunked{}:
      Unit{}

def head.done.shape(h: Spec.Head, -s: List<&2, U32>) ->
  Shape(Spec.head.done(h, Nil{}, s)):
  match h:
    case Spec.Head{m, t, +l, cl, +hs, k, u, c, v, f, hx}:
      match f:
        case Eng.Fx{+v10, ka, +te}:
          head.at.shape(Spec.hosts.ok(v10, hs), Spec.body.of(te, v10, l),
            Spec.Head{m, t, l, cl, hs, k, u, c, v, Eng.Fx{v10, ka, te}, hx}, s)

def chunk.paid.shape(over: Bool, +h: Spec.Head, +at: Spec.At, +n: U32, +got: List<&2, U32>, +left: U32,
  -s: List<&2, U32>) ->
  Shape(Spec.chunk.paid(over, h, at, n, got, left, Nil{}, s)):
  match over:
    case True{}:
      Unit{}
    case False{}:
      Unit{}

def chunk.to.shape(paid: Bool, +h: Spec.Head, +at: Spec.At, +n: U32, +got: List<&2, U32>, +left: U32,
  -s: List<&2, U32>) ->
  Shape(Spec.chunk.to(paid, h, at, n, got, left, Nil{}, s)):
  match paid:
    case True{}:
      chunk.paid.shape(U32.is_le(left, n), h, at, n, got, left, s)
    case False{}:
      Unit{}

def chunk.line.shape(z: Bool, +h: Spec.Head, +n: U32, +got: List<&2, U32>, +left: U32,
  -s: List<&2, U32>) ->
  Shape(Spec.chunk.line(z, h, n, got, left, Nil{}, s)):
  match z:
    case True{}:
      Unit{}
    case False{}:
      Unit{}

def chunk.go.shape(g: Spec.Go, +h: Spec.Head, +n: U32, +got: List<&2, U32>, +left: U32,
  -s: List<&2, U32>) ->
  Shape(Spec.chunk.go(g, h, n, got, left, Nil{}, s)):
  match g:
    case Spec.GBad{}:
      Unit{}
    case Spec.GTo{at, paid}:
      chunk.to.shape(paid, h, at, n, got, left, s)
    case Spec.GDigit{+d}:
      chunk.paid.shape(U32.is_le(left, (n * 16 + d : U32)), h, Spec.ASize{}, (n * 16 + d : U32), got, left, s)
    case Spec.GLine{}:
      chunk.line.shape(U32.is_zero(n), h, n, got, left, s)
    case Spec.GDone{}:
      emit.shape(h, got)

def data.byte.shape(more: Nat, +c: U32, +h: Spec.Head, +got: List<&2, U32>, +left: U32,
  -s: List<&2, U32>) ->
  Shape(Spec.data.byte(more, c, h, got, left, Nil{}, s)):
  match more:
    case 0n:
      Unit{}
    case 1n+q:
      Unit{}

def req.ok.shape(v11: Bool, v10: Bool, +m: List<&2, U32>, +t: List<&2, U32>,
  -s: List<&2, U32>) ->
  Shape(Spec.req.ok(v11, v10, m, t, Nil{}, s)):
  match v11 v10:
    case True{} _:
      Unit{}
    case False{} True{}:
      Unit{}
    case False{} False{}:
      Unit{}

def req.cr.shape(v: Spec.RLine, -s: List<&2, U32>) ->
  Shape(Spec.req.cr(v, Nil{}, s)):
  match v:
    case Spec.RNone{}:
      Unit{}
    case Spec.RVer{m, t, +ver}:
      req.ok.shape(Spec.eq(Bytes.from_list(ver), "HTTP/1.1"), Spec.eq(Bytes.from_list(ver), "HTTP/1.0"), m, t, s)
    case Spec.RMeth{m}:
      Unit{}
    case Spec.RTarget{m, t}:
      Unit{}
    case Spec.RBad{}:
      Unit{}

def field.next.shape(mh: Maybe<&2, Spec.Head>, -s: List<&2, U32>) ->
  Shape(Spec.field.next(mh, Nil{}, s)):
  match mh:
    case Some{h}:
      Unit{}
    case None{}:
      Unit{}

def field.cr.shape(+h: Spec.Head, v: Spec.FLine, -s: List<&2, U32>) ->
  Shape(Spec.field.cr(h, v, Nil{}, s)):
  match v:
    case Spec.FEmpty{}:
      Unit{}
    case Spec.FVal{val}:
      field.next.shape(Spec.field.done(h, val), s)
    case Spec.FName{n}:
      Unit{}
    case Spec.FBad{}:
      Unit{}

def req.byte.shape(k: Eng.Cls, +c: U32, +cur: List<&2, U32>, -s: List<&2, U32>) ->
  Shape(Spec.req.byte(k, c, cur, Nil{}, s)):
  match k:
    case Eng.KSp{}:
      Unit{}
    case Eng.KHt{}:
      Unit{}
    case Eng.KCr{}:
      req.cr.shape(Spec.req.view(cur), s)
    case Eng.KLf{}:
      Unit{}
    case Eng.KCo{}:
      Unit{}
    case Eng.KCm{}:
      Unit{}
    case Eng.KDg{}:
      Unit{}
    case Eng.KTk{}:
      Unit{}
    case Eng.KVc{}:
      Unit{}
    case Eng.KCt{}:
      Unit{}

def field.byte.shape(k: Eng.Cls, +c: U32, +h: Spec.Head, +cur: List<&2, U32>,
  -s: List<&2, U32>) ->
  Shape(Spec.field.byte(k, c, h, cur, Nil{}, s)):
  match k:
    case Eng.KSp{}:
      Unit{}
    case Eng.KHt{}:
      Unit{}
    case Eng.KCr{}:
      field.cr.shape(h, Spec.field.view(cur), s)
    case Eng.KLf{}:
      Unit{}
    case Eng.KCo{}:
      Unit{}
    case Eng.KCm{}:
      Unit{}
    case Eng.KDg{}:
      Unit{}
    case Eng.KTk{}:
      Unit{}
    case Eng.KVc{}:
      Unit{}
    case Eng.KCt{}:
      Unit{}

def blank.byte.shape(k: Eng.Cls, -s: List<&2, U32>) ->
  Shape(Spec.blank.byte(k, Nil{}, s)):
  match k:
    case Eng.KSp{}:
      Unit{}
    case Eng.KHt{}:
      Unit{}
    case Eng.KCr{}:
      Unit{}
    case Eng.KLf{}:
      Unit{}
    case Eng.KCo{}:
      Unit{}
    case Eng.KCm{}:
      Unit{}
    case Eng.KDg{}:
      Unit{}
    case Eng.KTk{}:
      Unit{}
    case Eng.KVc{}:
      Unit{}
    case Eng.KCt{}:
      Unit{}

def eol.byte.shape(k: Eng.Cls, +h: Spec.Head, -s: List<&2, U32>) ->
  Shape(Spec.eol.byte(k, h, Nil{}, s)):
  match k:
    case Eng.KSp{}:
      Unit{}
    case Eng.KHt{}:
      Unit{}
    case Eng.KCr{}:
      Unit{}
    case Eng.KLf{}:
      Unit{}
    case Eng.KCo{}:
      Unit{}
    case Eng.KCm{}:
      Unit{}
    case Eng.KDg{}:
      Unit{}
    case Eng.KTk{}:
      Unit{}
    case Eng.KVc{}:
      Unit{}
    case Eng.KCt{}:
      Unit{}

def eoh.byte.shape(k: Eng.Cls, +h: Spec.Head, -s: List<&2, U32>) ->
  Shape(Spec.eoh.byte(k, h, Nil{}, s)):
  match k:
    case Eng.KSp{}:
      Unit{}
    case Eng.KHt{}:
      Unit{}
    case Eng.KCr{}:
      Unit{}
    case Eng.KLf{}:
      head.done.shape(h, s)
    case Eng.KCo{}:
      Unit{}
    case Eng.KCm{}:
      Unit{}
    case Eng.KDg{}:
      Unit{}
    case Eng.KTk{}:
      Unit{}
    case Eng.KVc{}:
      Unit{}
    case Eng.KCt{}:
      Unit{}

def body.byte.shape(more: Nat, +c: U32, +h: Spec.Head, +got: List<&2, U32>,
  -s: List<&2, U32>) ->
  Shape(Spec.body.byte(more, c, h, got, Nil{}, s)):
  match more:
    case 0n:
      emit.shape(h, Spec.snoc(got, c))
    case 1n+q:
      Unit{}

def next.at.shape(mode: Spec.Mode, +k: Eng.Cls, +c: U32, -s: List<&2, U32>) ->
  Shape(Spec.next.at(mode, k, c, Nil{}, s)):
  match mode:
    case Spec.MReq{cur}:
      req.byte.shape(k, c, cur, s)
    case Spec.MBlank{}:
      blank.byte.shape(k, s)
    case Spec.MField{h, cur}:
      field.byte.shape(k, c, h, cur, s)
    case Spec.MEol{h}:
      eol.byte.shape(k, h, s)
    case Spec.MEoh{h}:
      eoh.byte.shape(k, h, s)
    case Spec.MBody{h, more, got}:
      body.byte.shape(more, c, h, got, s)
    case Spec.MChunk{h, at, n, got, left}:
      chunk.go.shape(Spec.chunk.step(at, Spec.xk.of(k, c)), h, n, got, left, s)
    case Spec.MData{h, more, got, left}:
      data.byte.shape(more, c, h, got, left, s)
    case Spec.MUp{got}:
      Unit{}
    case Spec.MBad{}:
      Unit{}

# LEMMA: a step from no requests done does at most one
def next.shape(+m: Spec.Mode, +s: List<&2, U32>, +c: U32) -> Shape(Spec.next(Spec.W{m, Nil{}, s}, c)):
  next.at.shape(m, Spec.cls(c), c, Spec.snoc(s, c))


# The walk over two parts, and over what follows an upgrade
# ---------------------------------------------------------

def walk.app(xs: List<&2, U32>, -ys: List<&2, U32>, +w: Spec.W) ->
  {Spec.walk(List.append(&2, U32, xs, ys), w) == Spec.walk(ys, Spec.walk(xs, w)) : Spec.W}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      walk.app(t, ys, Spec.next(w, x))

# after an upgrade, what follows is not HTTP: the walk does no more
def up.agrees(bs: List<&2, U32>, +g: List<&2, U32>, +o: List<&2, Eng.Req>, +s: List<&2, U32>,
  -us: List<&2, Laws.PTook>, hu: {Laws.took.reqs(us) == List.reverse(&2, Eng.Req, o) : List<&2, Eng.Req>}) ->
  Laws.Agrees(Laws.PScanned{us, Laws.PUpgraded{}}, Spec.finish(Spec.walk(bs, Spec.W{Spec.MUp{g}, o, s}))):
  match bs:
    case Nil{}:
      (hu, {==})
    case Con{+c, t}:
      up.agrees(t, Spec.snoc(g, c), o, Spec.snoc(s, c), us, hu)

# A refusal stays
# ---------------
#
# Once frame() refuses the bytes so far, it refuses every longer input,
# with the same requests before the refusal. The engine's reader says
# so for the spec: it is refused where frame() is (frame_sim), a refused
# reader stays refused (bad_feeds), and frame_sim again of the longer
# input can then only say refused, with the reader's requests.

def st.is.bad(st: Eng.St, h: {EL.look.st(st) == EL.Refusing{} : EL.Look}) -> {st == Eng.Bad{} : Eng.St}:
  match st:
    case Eng.Pre{}:
      look.no({Eng.Pre{} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.PreLf{}:
      look.no({Eng.PreLf{} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.InM{m0}:
      look.no({Eng.InM{m0} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.InT{p0}:
      look.no({Eng.InT{p0} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.InV{v0}:
      look.no({Eng.InV{v0} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.CrM{}:
      look.no({Eng.CrM{} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.Lin{}:
      look.no({Eng.Lin{} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.InN{n0}:
      look.no({Eng.InN{n0} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.InL0{}:
      look.no({Eng.InL0{} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.InL{v0}:
      look.no({Eng.InL{v0} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.InLt{v0}:
      look.no({Eng.InLt{v0} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.InLc{t0, cl0, up0, ka0, ms0}:
      look.no({Eng.InLc{t0, cl0, up0, ka0, ms0} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.InLu{t0, ws0}:
      look.no({Eng.InLu{t0, ws0} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.InLk0{}:
      look.no({Eng.InLk0{} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.InLk{k0}:
      look.no({Eng.InLk{k0} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.InLv{v0}:
      look.no({Eng.InLv{v0} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.InLx{v0}:
      look.no({Eng.InLx{v0} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.InLe0{}:
      look.no({Eng.InLe0{} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.InLe{v0}:
      look.no({Eng.InLe{v0} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.CrL{}:
      look.no({Eng.CrL{} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.Bod{r0, b0}:
      look.no({Eng.Bod{r0, b0} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.Chk{pos0, n0, b0, left0}:
      look.no({Eng.Chk{pos0, n0, b0, left0} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.Chd{r0, b0, left0}:
      look.no({Eng.Chd{r0, b0, left0} == Eng.Bad{} : Eng.St}, EL.Reading{}, EL.Refusing{}, h)
    case Eng.Rest{bs0}:
      look.no({Eng.Rest{bs0} == Eng.Bad{} : Eng.St}, EL.Handing{}, EL.Refusing{}, h)
    case Eng.Bad{}:
      {==}

def agree.to(-a: Eng.P, -b: Eng.P, e: {a == b : Eng.P}, -g: Spec.Frames, x: EL.agree(a, g)) -> EL.agree(b, g):
  %e : EL.agree(_, g)
  x

def bad.final.at(-pd: Eng.Pend, +out: List<&2, Eng.Req>, rs2: List<&2, Eng.Req>, e: Spec.End,
  ag: EL.agree.end(Eng.P{Eng.Bad{}, pd, out}, rs2, e)) ->
  {Spec.Frames{rs2, e} == Spec.Frames{List.reverse(&2, Eng.Req, out), Spec.Refused{}} : Spec.Frames}:
  match e:
    case Spec.Open{rest}:
      (l, q) = ag
      look.no({Spec.Frames{rs2, Spec.Open{rest}} == Spec.Frames{List.reverse(&2, Eng.Req, out), Spec.Refused{}} :
        Spec.Frames}, EL.Refusing{}, EL.Reading{},
        Equal.cong(List<&2, Eng.Req> & EL.Look, EL.Look, lk.snd, (List.reverse(&2, Eng.Req, out), EL.Refusing{}),
          (rs2, EL.Reading{}), l))
    case Spec.Refused{}:
      %Equal.cong(List<&2, Eng.Req> & EL.Look, List<&2, Eng.Req>, lk.fst, (List.reverse(&2, Eng.Req, out), EL.Refusing{}),
        (rs2, EL.Refusing{}), ag) :
        {Spec.Frames{_, Spec.Refused{}} == Spec.Frames{List.reverse(&2, Eng.Req, out), Spec.Refused{}} : Spec.Frames}
      {==}
    case Spec.Upgraded{b}:
      no({Spec.Frames{rs2, Spec.Upgraded{b}} == Spec.Frames{List.reverse(&2, Eng.Req, out), Spec.Refused{}} :
        Spec.Frames},
        Equal.cong(Eng.P, Bool, p => st.bad(st.of(p)), Eng.P{Eng.Rest{b}, Eng.pend.new(), List.reverse(&2, Eng.Req, rs2)},
          Eng.P{Eng.Bad{}, pd, out},
          Equal.sym(Eng.P, Eng.P{Eng.Bad{}, pd, out}, Eng.P{Eng.Rest{b}, Eng.pend.new(), List.reverse(&2, Eng.Req, rs2)}, ag)))

def bad.final(-pd: Eng.Pend, +out: List<&2, Eng.Req>, g: Spec.Frames, ag: EL.agree(Eng.P{Eng.Bad{}, pd, out}, g)) ->
  {g == Spec.Frames{List.reverse(&2, Eng.Req, out), Spec.Refused{}} : Spec.Frames}:
  match g:
    case Spec.Frames{rs2, e}:
      bad.final.at(pd, out, rs2, e, ag)

def bad.go(+pre: List<&2, U32>, +bs: List<&2, U32>, st: Eng.St, +pd: Eng.Pend, +out: List<&2, Eng.Req>,
  hq: {Eng.feed(pre, Eng.p.new()) == Eng.P{st, pd, out} : Eng.P}, hs: {st == Eng.Bad{} : Eng.St}) ->
  {Spec.frame(List.append(&2, U32, pre, bs)) == Spec.Frames{List.reverse(&2, Eng.Req, out), Spec.Refused{}} :
    Spec.Frames}:
  bad.final(pd, out, Spec.frame(List.append(&2, U32, pre, bs)),
    agree.to(Eng.feed(List.append(&2, U32, pre, bs), Eng.p.new()), Eng.P{Eng.Bad{}, pd, out},
      Equal.trans(Eng.P, Eng.feed(List.append(&2, U32, pre, bs), Eng.p.new()), Eng.feed(bs, Eng.P{st, pd, out}),
        Eng.P{Eng.Bad{}, pd, out},
        Equal.trans(Eng.P, Eng.feed(List.append(&2, U32, pre, bs), Eng.p.new()), Eng.feed(bs, Eng.feed(pre, Eng.p.new())),
          Eng.feed(bs, Eng.P{st, pd, out}), EL.feed_split(pre, bs, Eng.p.new()),
          Equal.cong(Eng.P, Eng.P, q => Eng.feed(bs, q), Eng.feed(pre, Eng.p.new()), Eng.P{st, pd, out}, hq)),
        %Equal.sym(Eng.St, st, Eng.Bad{}, hs) : {Eng.feed(bs, Eng.P{_, pd, out}) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}
        EL.bad_feeds(bs, pd, out)),
      Spec.frame(List.append(&2, U32, pre, bs)), EL.frame_sim(List.append(&2, U32, pre, bs))))

def bad.at2(+pre: List<&2, U32>, +bs: List<&2, U32>, +st: Eng.St, +pd: Eng.Pend, +out: List<&2, Eng.Req>,
  hq: {Eng.feed(pre, Eng.p.new()) == Eng.P{st, pd, out} : Eng.P}, rs: List<&2, Eng.Req>,
  e2: {List.reverse(&2, Eng.Req, out) == rs : List<&2, Eng.Req>} & {EL.look.st(st) == EL.Refusing{} : EL.Look}) ->
  {Spec.frame(List.append(&2, U32, pre, bs)) == Spec.Frames{rs, Spec.Refused{}} : Spec.Frames}:
  (hr, hl) = e2
  %hr : {Spec.frame(List.append(&2, U32, pre, bs)) == Spec.Frames{_, Spec.Refused{}} : Spec.Frames}
  bad.go(pre, bs, st, pd, out, hq, st.is.bad(st, hl))

def bad.at(+pre: List<&2, U32>, +bs: List<&2, U32>, q: Eng.P, hq: {Eng.feed(pre, Eng.p.new()) == q : Eng.P},
  rs: List<&2, Eng.Req>, lq: {EL.look(q) == (rs, EL.Refusing{}) : List<&2, Eng.Req> & EL.Look}) ->
  {Spec.frame(List.append(&2, U32, pre, bs)) == Spec.Frames{rs, Spec.Refused{}} : Spec.Frames}:
  match q:
    case Eng.P{+st, +pd, +out}:
      bad.at2(pre, bs, st, pd, out, hq, rs,
        pair.eqs(List.reverse(&2, Eng.Req, out), EL.look.st(st), rs, EL.Refusing{}, lq))

# LEMMA: a refusal stays
def bad.stays(+pre: List<&2, U32>, +bs: List<&2, U32>, rs: List<&2, Eng.Req>,
  h: {Spec.frame(pre) == Spec.Frames{rs, Spec.Refused{}} : Spec.Frames}) ->
  {Spec.frame(List.append(&2, U32, pre, bs)) == Spec.Frames{rs, Spec.Refused{}} : Spec.Frames}:
  bad.at(pre, bs, Eng.feed(pre, Eng.p.new()), {==}, rs,
    %h : EL.agree(Eng.feed(pre, Eng.p.new()), _)
    EL.frame_sim(pre))

# The framing a request at a time, against the walk that walks on
# ---------------------------------------------------------------
#
# FRel says where frame()'s walk over the bytes taken so far (pre) is,
# given where the reference framing is: reading with walk w, the walk
# is w with the requests taken behind it; just after a request (or an
# upgrade), it is a fresh walk (or what follows an upgrade) with that
# request in front; refused, frame() of the bytes so far is refused.

def FRel(st: Laws.PStp, acc: List<&2, Laws.PTook>, pre: List<&2, U32>) -> Type:
  match st:
    case Laws.PGo{w, raw}:
      match w:
        case Spec.W{m, x, s}:
          {x == Nil{} : List<&2, Eng.Req>} & {Spec.walk(pre, Laws.w0()) == Spec.W{m, Laws.took.reqs(acc), s} : Spec.W}
    case Laws.PMsg{raw, r}:
      {Spec.walk(pre, Laws.w0()) == Spec.W{Spec.MReq{Nil{}}, Con{r, Laws.took.reqs(acc)}, Nil{}} : Spec.W}
    case Laws.PUp{raw, r}:
      {Spec.walk(pre, Laws.w0()) == Spec.W{Spec.MUp{Nil{}}, Con{r, Laws.took.reqs(acc)}, Nil{}} : Spec.W}
    case Laws.PBad{}:
      {Spec.frame(pre) == Spec.Frames{List.reverse(&2, Eng.Req, Laws.took.reqs(acc)), Spec.Refused{}} : Spec.Frames}

def fa.end(+m2: Spec.Mode, +s2: List<&2, U32>, e: Spec.End, he: {Spec.finish.end(m2, s2) == e : Spec.End},
  -raw2: List<&2, U32>, +acc: List<&2, Laws.PTook>, +pre2: List<&2, U32>,
  hw: {Spec.walk(pre2, Laws.w0()) == Spec.W{m2, Laws.took.reqs(acc), s2} : Spec.W}) ->
  FRel(Laws.px.end(e, Spec.W{m2, Nil{}, s2}, raw2), acc, pre2):
  match e:
    case Spec.Refused{}:
      %Equal.sym(Spec.W, Spec.walk(pre2, Laws.w0()), Spec.W{m2, Laws.took.reqs(acc), s2}, hw) :
        {Spec.finish(_) == Spec.Frames{List.reverse(&2, Eng.Req, Laws.took.reqs(acc)), Spec.Refused{}} : Spec.Frames}
      %Equal.sym(Spec.End, Spec.finish.end(m2, s2), Spec.Refused{}, he) :
        {Spec.Frames{List.reverse(&2, Eng.Req, Laws.took.reqs(acc)), _} ==
          Spec.Frames{List.reverse(&2, Eng.Req, Laws.took.reqs(acc)), Spec.Refused{}} : Spec.Frames}
      {==}
    case Spec.Open{rest}:
      ({==}, hw)
    case Spec.Upgraded{b}:
      ({==}, hw)

def fa.req(b: Bool, -r: Eng.Req, -raw2: List<&2, U32>, -acc: List<&2, Laws.PTook>, -pre2: List<&2, U32>,
  hw: {Spec.walk(pre2, Laws.w0()) == Spec.W{Spec.emit.mode(b), Con{r, Laws.took.reqs(acc)}, Nil{}} : Spec.W}) ->
  FRel(Laws.px.req(b, raw2, r), acc, pre2):
  match b:
    case True{}:
      hw
    case False{}:
      hw

def fa.emit(+m2: Spec.Mode, +r: Eng.Req, +t2: List<&2, Eng.Req>, +s2: List<&2, U32>, +o: List<&2, Eng.Req>,
  sh: {t2 == Nil{} : List<&2, Eng.Req>} & {s2 == Nil{} : List<&2, U32>} & {m2 == Spec.emit.mode(Eng.req.ws(r)) : Spec.Mode}) ->
  {Spec.W{m2, Con{r, List.append(&2, Eng.Req, t2, o)}, s2} == Spec.W{Spec.emit.mode(Eng.req.ws(r)), Con{r, o}, Nil{}} :
    Spec.W}:
  (ht, hr) = sh
  (hs, hm) = hr
  %Equal.sym(List<&2, Eng.Req>, t2, Nil{}, ht) :
    {Spec.W{m2, Con{r, List.append(&2, Eng.Req, _, o)}, s2} == Spec.W{Spec.emit.mode(Eng.req.ws(r)), Con{r, o}, Nil{}} :
      Spec.W}
  %Equal.sym(List<&2, U32>, s2, Nil{}, hs) :
    {Spec.W{m2, Con{r, o}, _} == Spec.W{Spec.emit.mode(Eng.req.ws(r)), Con{r, o}, Nil{}} : Spec.W}
  %Equal.sym(Spec.Mode, m2, Spec.emit.mode(Eng.req.ws(r)), hm) :
    {Spec.W{_, Con{r, o}, Nil{}} == Spec.W{Spec.emit.mode(Eng.req.ws(r)), Con{r, o}, Nil{}} : Spec.W}
  {==}

def fa.of(w2: Spec.W, +raw2: List<&2, U32>, +acc: List<&2, Laws.PTook>, +pre2: List<&2, U32>, sh: Shape(w2),
  hw: {Spec.walk(pre2, Laws.w0()) == shift(w2, Laws.took.reqs(acc)) : Spec.W}) ->
  FRel(Laws.px.of(w2, raw2), acc, pre2):
  match w2:
    case Spec.W{+m2, x2, +s2}:
      match x2:
        case Nil{}:
          fa.end(m2, s2, Spec.finish.end(m2, s2), {==}, raw2, acc, pre2, hw)
        case Con{+r, +t2}:
          fa.req(Eng.req.ws(r), r, raw2, acc, pre2,
            Equal.trans(Spec.W, Spec.walk(pre2, Laws.w0()),
              Spec.W{m2, Con{r, List.append(&2, Eng.Req, t2, Laws.took.reqs(acc))}, s2},
              Spec.W{Spec.emit.mode(Eng.req.ws(r)), Con{r, Laws.took.reqs(acc)}, Nil{}},
              hw, fa.emit(m2, r, t2, s2, Laws.took.reqs(acc), sh)))

# one byte, on both
def fa.stp(+m: Spec.Mode, x: List<&2, Eng.Req>, +s: List<&2, U32>, +raw: List<&2, U32>, +c: U32,
  +acc: List<&2, Laws.PTook>, +pre: List<&2, U32>, rel: FRel(Laws.PGo{Spec.W{m, x, s}, raw}, acc, pre)) ->
  FRel(Laws.px.stp(Spec.W{m, x, s}, c, raw), acc, Spec.snoc(pre, c)):
  (hx, hf) = rel
  %Equal.sym(List<&2, Eng.Req>, x, Nil{}, hx) :
    FRel(Laws.px.stp(Spec.W{m, _, s}, c, raw), acc, Spec.snoc(pre, c))
  fa.of(Spec.next(Spec.W{m, Nil{}, s}, c), Spec.snoc(raw, c), acc, Spec.snoc(pre, c), next.shape(m, s, c),
    Equal.trans(Spec.W, Spec.walk(Spec.snoc(pre, c), Laws.w0()), Spec.next(Spec.W{m, Laws.took.reqs(acc), s}, c),
      shift(Spec.next(Spec.W{m, Nil{}, s}, c), Laws.took.reqs(acc)),
      Equal.trans(Spec.W, Spec.walk(Spec.snoc(pre, c), Laws.w0()), Spec.next(Spec.walk(pre, Laws.w0()), c),
        Spec.next(Spec.W{m, Laws.took.reqs(acc), s}, c), walk.snoc(pre, c, Laws.w0()),
        Equal.cong(Spec.W, Spec.W, w => Spec.next(w, c), Spec.walk(pre, Laws.w0()), Spec.W{m, Laws.took.reqs(acc), s}, hf)),
      next.par(m, Laws.took.reqs(acc), s, c)))

# the rest of a stream: the bytes so far and what follows are the whole
def fa.split(+pre: List<&2, U32>, +c: U32, +t: List<&2, U32>) ->
  {List.append(&2, U32, Spec.snoc(pre, c), t) == List.append(&2, U32, pre, Con{c, t}) : List<&2, U32>}:
  app.assoc(U32, pre, Con{c, Nil{}}, t)

def fa.nil.go(w: Spec.W, +raw: List<&2, U32>, +acc: List<&2, Laws.PTook>, +pre: List<&2, U32>,
  rel: FRel(Laws.PGo{w, raw}, acc, pre)) ->
  Laws.Agrees(Laws.px.go(Nil{}, Laws.PGo{w, raw}, acc), Spec.frame(List.append(&2, U32, pre, Nil{}))):
  match w:
    case Spec.W{+m, +x, +s}:
      (hx, hf) = rel
      %Equal.sym(List<&2, U32>, List.append(&2, U32, pre, Nil{}), pre, app.nil(U32, pre)) :
        Laws.Agrees(Laws.px.go(Nil{}, Laws.PGo{Spec.W{m, x, s}, raw}, acc), Spec.frame(_))
      %Equal.sym(Spec.W, Spec.walk(pre, Laws.w0()), Spec.W{m, Laws.took.reqs(acc), s}, hf) :
        Laws.Agrees(Laws.px.go(Nil{}, Laws.PGo{Spec.W{m, x, s}, raw}, acc), Spec.finish(_))
      (treqs.rev(acc), {==})

def fa.con.go(+c: U32, +t: List<&2, U32>, w: Spec.W, +raw: List<&2, U32>, +acc: List<&2, Laws.PTook>,
  +pre: List<&2, U32>, rel: FRel(Laws.PGo{w, raw}, acc, pre),
  ih: @+s2: Laws.PStp -> @+a2: List<&2, Laws.PTook> -> @+p2: List<&2, U32> -> FRel(s2, a2, p2) ->
    Laws.Agrees(Laws.px.go(t, s2, a2), Spec.frame(List.append(&2, U32, p2, t)))) ->
  Laws.Agrees(Laws.px.go(Con{c, t}, Laws.PGo{w, raw}, acc), Spec.frame(List.append(&2, U32, pre, Con{c, t}))):
  match w:
    case Spec.W{+m, +x, +s}:
      %fa.split(pre, c, t) :
        Laws.Agrees(Laws.px.go(Con{c, t}, Laws.PGo{Spec.W{m, x, s}, raw}, acc), Spec.frame(_))
      ih(Laws.px.stp(Spec.W{m, x, s}, c, raw), acc, Spec.snoc(pre, c), fa.stp(m, x, s, raw, c, acc, pre, rel))

def fa.go(bs: List<&2, U32>, st: Laws.PStp, +acc: List<&2, Laws.PTook>, +pre: List<&2, U32>, rel: FRel(st, acc, pre)) ->
  Laws.Agrees(Laws.px.go(bs, st, acc), Spec.frame(List.append(&2, U32, pre, bs))):
  match bs st:
    case Nil{} Laws.PGo{w, raw}:
      fa.nil.go(w, raw, acc, pre, rel)
    case Nil{} Laws.PMsg{+raw, +r}:
      %Equal.sym(List<&2, U32>, List.append(&2, U32, pre, Nil{}), pre, app.nil(U32, pre)) :
        Laws.Agrees(Laws.px.go(Nil{}, Laws.PMsg{raw, r}, acc), Spec.frame(_))
      %Equal.sym(Spec.W, Spec.walk(pre, Laws.w0()), Spec.W{Spec.MReq{Nil{}}, Con{r, Laws.took.reqs(acc)}, Nil{}}, rel) :
        Laws.Agrees(Laws.px.go(Nil{}, Laws.PMsg{raw, r}, acc), Spec.finish(_))
      (treqs.rev(Con{Laws.PTook{raw, r}, acc}), {==})
    case Nil{} Laws.PUp{+raw, +r}:
      %Equal.sym(List<&2, U32>, List.append(&2, U32, pre, Nil{}), pre, app.nil(U32, pre)) :
        Laws.Agrees(Laws.px.go(Nil{}, Laws.PUp{raw, r}, acc), Spec.frame(_))
      %Equal.sym(Spec.W, Spec.walk(pre, Laws.w0()), Spec.W{Spec.MUp{Nil{}}, Con{r, Laws.took.reqs(acc)}, Nil{}}, rel) :
        Laws.Agrees(Laws.px.go(Nil{}, Laws.PUp{raw, r}, acc), Spec.finish(_))
      (treqs.rev(Con{Laws.PTook{raw, r}, acc}), {==})
    case Nil{} Laws.PBad{}:
      %Equal.sym(List<&2, U32>, List.append(&2, U32, pre, Nil{}), pre, app.nil(U32, pre)) :
        Laws.Agrees(Laws.px.go(Nil{}, Laws.PBad{}, acc), Spec.frame(_))
      %Equal.sym(Spec.Frames, Spec.frame(pre), Spec.Frames{List.reverse(&2, Eng.Req, Laws.took.reqs(acc)), Spec.Refused{}},
        rel) : Laws.Agrees(Laws.px.go(Nil{}, Laws.PBad{}, acc), _)
      (treqs.rev(acc), {==})
    case Con{+c, +t} Laws.PBad{}:
      %Equal.sym(Spec.Frames, Spec.frame(List.append(&2, U32, pre, Con{c, t})),
        Spec.Frames{List.reverse(&2, Eng.Req, Laws.took.reqs(acc)), Spec.Refused{}},
        bad.stays(pre, Con{c, t}, List.reverse(&2, Eng.Req, Laws.took.reqs(acc)), rel)) :
        Laws.Agrees(Laws.px.go(Con{c, t}, Laws.PBad{}, acc), _)
      (treqs.rev(acc), {==})
    case Con{+c, +t} Laws.PUp{+raw, +r}:
      %Equal.sym(Spec.W, Spec.walk(List.append(&2, U32, pre, Con{c, t}), Laws.w0()),
        Spec.walk(Con{c, t}, Spec.walk(pre, Laws.w0())), walk.app(pre, Con{c, t}, Laws.w0())) :
        Laws.Agrees(Laws.px.go(Con{c, t}, Laws.PUp{raw, r}, acc), Spec.finish(_))
      %Equal.sym(Spec.W, Spec.walk(pre, Laws.w0()), Spec.W{Spec.MUp{Nil{}}, Con{r, Laws.took.reqs(acc)}, Nil{}}, rel) :
        Laws.Agrees(Laws.px.go(Con{c, t}, Laws.PUp{raw, r}, acc), Spec.finish(Spec.walk(Con{c, t}, _)))
      up.agrees(Con{c, t}, Nil{}, Con{r, Laws.took.reqs(acc)}, Nil{},
        List.reverse(&2, Laws.PTook, Con{Laws.PTook{raw, r}, acc}), treqs.rev(Con{Laws.PTook{raw, r}, acc}))
    case Con{+c, +t} Laws.PGo{w, raw}:
      fa.con.go(c, t, w, raw, acc, pre, rel, s2 => a2 => p2 => r2 => fa.go(t, s2, a2, p2, r2))
    case Con{+c, +t} Laws.PMsg{+raw, +r}:
      %fa.split(pre, c, t) :
        Laws.Agrees(Laws.px.go(Con{c, t}, Laws.PMsg{raw, r}, acc), Spec.frame(_))
      fa.go(t, Laws.px.stp(Laws.w0(), c, Nil{}), Con{Laws.PTook{raw, r}, acc}, Spec.snoc(pre, c),
        fa.stp(Spec.MReq{Nil{}}, Nil{}, Nil{}, Nil{}, c, Con{Laws.PTook{raw, r}, acc}, pre, ({==}, rel)))

def Laws.frames_agree(bs):
  fa.go(bs, Laws.PGo{Laws.w0(), Nil{}}, Nil{}, Nil{}, ({==}, {==}))

# Forwarding
# ==========

def bytes.rt(b: Bytes()) -> {Bytes.from_list(Bytes.to_list(b)) == b : Bytes()}:
  match b:
    case SNil{}:
      {==}
    case SCon{Chr{c}, t}:
      Equal.cong(Bytes(), Bytes(), x => SCon{Chr{c}, x}, Bytes.from_list(Bytes.to_list(t)), t, bytes.rt(t))

def conns.took(c: Laws.Conn, f: Laws.PScanned, h: Laws.Conns(c, f)) ->
  {Laws.conn.took(c) == Laws.took.reqs(Laws.scanned.took(f)) : List<&2, Eng.Req>}:
  match c f:
    case Laws.Conn{ts, t} Laws.PScanned{us, u}:
      (h1, h2) = h
      h1

def Laws.forward_canonical(w, rs):
  Equal.cong(List<&2, Eng.Req>, Bytes(), ts => X.wire(w, ts), Laws.conn.took(Laws.reads(rs)),
    Laws.took.reqs(Laws.scanned.took(Laws.frame(Bytes.to_list(Bytes.concat(rs))))),
    conns.took(Laws.reads(rs), Laws.frame(Bytes.to_list(Bytes.concat(rs))), Laws.scan_is_spec(rs)))

# A refusal forwards nothing
# --------------------------

def agrees.nil(f: Laws.PScanned, ag: Laws.Agrees(f, Spec.Frames{Nil{}, Spec.Refused{}})) ->
  {Laws.took.reqs(Laws.scanned.took(f)) == Nil{} : List<&2, Eng.Req>}:
  match f:
    case Laws.PScanned{us, u}:
      (h1, h2) = ag
      h1

def Laws.refused_not_forwarded(rs, r):
  Equal.trans(List<&2, Eng.Req>, Laws.conn.took(Laws.reads(rs)),
    Laws.took.reqs(Laws.scanned.took(Laws.frame(Bytes.to_list(Bytes.concat(rs))))), Nil{},
    conns.took(Laws.reads(rs), Laws.frame(Bytes.to_list(Bytes.concat(rs))), Laws.scan_is_spec(rs)),
    agrees.nil(Laws.frame(Bytes.to_list(Bytes.concat(rs))),
      %r : Laws.Agrees(Laws.frame(Bytes.to_list(Bytes.concat(rs))), _)
      Laws.frames_agree(Bytes.to_list(Bytes.concat(rs)))))

# The hop's fields
# ----------------

def clean.app.at(x: Bool, -c1: Bool, -c2: Bool, -c12: Bool, e: {c12 == (c1 && c2) : Bool}) ->
  {(x && c12) == (x && c1 && c2) : Bool}:
  match x:
    case True{}:
      e
    case False{}:
      {==}

def clean.app(~m: @+n: Bytes() -> Bool, +ns: List<&2, Bytes()>, a: List<&2, Wr.Field>, -b: List<&2, Wr.Field>) ->
  {Laws.clean(~m, ns, List.append(&2, Wr.Field, a, b)) == (Laws.clean(~m, ns, a) && Laws.clean(~m, ns, b)) : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{f, t}:
      match f:
        case Wr.Field{+n, v}:
          clean.app.at(m(n) || Bool.not(Laws.hop(ns, n)), Laws.clean(~m, ns, t), Laws.clean(~m, ns, b),
            Laws.clean(~m, ns, List.append(&2, Wr.Field, t, b)), clean.app(~m, ns, t, b))

# a field kept is not a hop's
def and3.mid(a: Bool, b: Bool, -c: Bool, h: {(a && Bool.not(b) && c) == True{} : Bool}) -> {b == False{} : Bool}:
  match a b:
    case True{} True{}:
      no({True{} == False{} : Bool}, h)
    case True{} False{}:
      {==}
    case False{} True{}:
      no({True{} == False{} : Bool}, h)
    case False{} False{}:
      {==}

def and2.fst(a: Bool, -c: Bool, h: {(Bool.not(a) && c) == True{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      no({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def or.true(a: Bool) -> {(a || True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# the laws' own list of the hop's fields is core.bend's
def named.eq(+n: Bytes(), ns: List<&2, Bytes()>) -> {Laws.named(n, ns) == X.in.names(n, ns) : Bool}:
  match ns:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Equal.cong(Bool, Bool, b => Eng.bytes.eq(n, x) || b, Laws.named(n, t), X.in.names(n, t), named.eq(n, t))

def hop.eq(+ns: List<&2, Bytes()>, +n: Bytes()) -> {Laws.hop(ns, n) == X.hop(ns, n) : Bool}:
  Equal.cong(Bool, Bool, b => Laws.hop.fixed(n) || b, Laws.named(n, ns), X.in.names(n, ns), named.eq(n, ns))

# a field kept, then the rest clean
def kept.clean(~m: @+n: Bytes() -> Bool, +ns: List<&2, Bytes()>, +n: Bytes(), hb: {X.hop(ns, n) == False{} : Bool},
  -rest: List<&2, Wr.Field>, ih: {Laws.clean(~m, ns, rest) == True{} : Bool}) ->
  {((m(n) || Bool.not(Laws.hop(ns, n))) && Laws.clean(~m, ns, rest)) == True{} : Bool}:
  %Equal.sym(Bool, Laws.hop(ns, n), X.hop(ns, n), hop.eq(ns, n)) :
    {((m(n) || Bool.not(_)) && Laws.clean(~m, ns, rest)) == True{} : Bool}
  %Equal.sym(Bool, X.hop(ns, n), False{}, hb) :
    {((m(n) || Bool.not(_)) && Laws.clean(~m, ns, rest)) == True{} : Bool}
  %Equal.sym(Bool, (m(n) || True{}), True{}, or.true(m(n))) :
    {(_ && Laws.clean(~m, ns, rest)) == True{} : Bool}
  ih

def ends.at(~m: @+n: Bytes() -> Bool, +ns: List<&2, Bytes()>, k: Bool, +n: Bytes(), v: Bytes(), -t: List<&2, Wr.Field>,
  hk: {X.keeps(ns, n) == k : Bool}, ih: {Laws.clean(~m, ns, X.ends(ns, t)) == True{} : Bool}) ->
  {Laws.clean(~m, ns, X.ends.put(k, Wr.Field{n, v}, X.ends(ns, t))) == True{} : Bool}:
  match k:
    case True{}:
      kept.clean(~m, ns, n,
        and3.mid(X.is.other(Eng.fld.of(n)), X.hop(ns, n), Bool.not(X.own(n)), hk), X.ends(ns, t), ih)
    case False{}:
      ih

# LEMMA: what ends keeps is clean
def ends.clean(~m: @+n: Bytes() -> Bool, +ns: List<&2, Bytes()>, fs: List<&2, Wr.Field>) ->
  {Laws.clean(~m, ns, X.ends(ns, fs)) == True{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case Con{f, t}:
      match f:
        case Wr.Field{+n, v}:
          ends.at(~m, ns, X.keeps(ns, n), n, v, t, {==}, ends.clean(~m, ns, t))

def rends.at(~m: @+n: Bytes() -> Bool, +ns: List<&2, Bytes()>, +len: Bool, k: Bool, +n: Bytes(), v: Bytes(),
  -t: List<&2, Wr.Field>, hk: {X.rkeeps(ns, len, n) == k : Bool},
  ih: {Laws.clean(~m, ns, X.rends(ns, len, t)) == True{} : Bool}) ->
  {Laws.clean(~m, ns, X.ends.put(k, Wr.Field{n, v}, X.rends(ns, len, t))) == True{} : Bool}:
  match k:
    case True{}:
      kept.clean(~m, ns, n,
        and2.fst(X.hop(ns, n), len || Bool.not(Eng.bytes.eq(n, "content-length")), hk), X.rends(ns, len, t), ih)
    case False{}:
      ih

def rends.clean(~m: @+n: Bytes() -> Bool, +ns: List<&2, Bytes()>, +len: Bool, fs: List<&2, Wr.Field>) ->
  {Laws.clean(~m, ns, X.rends(ns, len, fs)) == True{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case Con{f, t}:
      match f:
        case Wr.Field{+n, v}:
          rends.at(~m, ns, len, X.rkeeps(ns, len, n), n, v, t, {==}, rends.clean(~m, ns, len, t))

def and.true(a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {(a && b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {(_ && b) == True{} : Bool}
  hb

def Laws.hop_by_hop_removed(w, hd, target, body):
  match w hd:
    case X.Fwd{host, proto, +ip, via} Eng.Hd{meth, v10, fs0, +cn}:
      +fs = X.trims(fs0)
      +t4 : List<&2, Wr.Field> = [Wr.Field{"x-forwarded-for", X.join(List.append(&2, Bytes(), X.values("x-forwarded-for", fs), [ip]))},
        Wr.Field{"x-forwarded-proto", proto}, Wr.Field{"x-forwarded-host", X.first(X.values("host", fs), "")},
        Wr.Field{"via", via}]
      %Equal.sym(Bool, Laws.clean(~Laws.own5, cn, List.append(&2, Wr.Field, X.ends(cn, fs), t4)),
        (Laws.clean(~Laws.own5, cn, X.ends(cn, fs)) && Laws.clean(~Laws.own5, cn, t4)),
        clean.app(~Laws.own5, cn, X.ends(cn, fs), t4)) :
        {_ == True{} : Bool}
      and.true(Laws.clean(~Laws.own5, cn, X.ends(cn, fs)),
        Laws.clean(~Laws.own5, cn, t4), ends.clean(~Laws.own5, cn, fs), {==})

def Laws.hop_by_hop_removed_rsp(via, ns, len, fs):
  %Equal.sym(Bool, Laws.clean(~Laws.is.via, ns, List.append(&2, Wr.Field, X.rends(ns, len, fs), [Wr.Field{"via", via}])),
    (Laws.clean(~Laws.is.via, ns, X.rends(ns, len, fs)) && Laws.clean(~Laws.is.via, ns, [Wr.Field{"via", via}])),
    clean.app(~Laws.is.via, ns, X.rends(ns, len, fs), [Wr.Field{"via", via}])) : {_ == True{} : Bool}
  and.true(Laws.clean(~Laws.is.via, ns, X.rends(ns, len, fs)), Laws.clean(~Laws.is.via, ns, [Wr.Field{"via", via}]),
    rends.clean(~Laws.is.via, ns, len, fs), {==})

# Reading it back
# ===============
#
# no_smuggle: the upstream, reading what the proxy sent by spec.bend's
# frame(), reads one request for each one forwarded -- its method,
# target and body -- and nothing more. A forwarded request passed valid
# (core.bend), and what valid checks is what spec.bend's walk needs to
# read each line of it as the line it is: bytes a line may hold
# (gathered, no CR or LF among them), a request line split at its two
# spaces, a field line at its colon with a name no framing reads, and a
# Content-Length read back as the body's length.

# no CR and no LF: a line's bytes
def ncl(k: Eng.Cls) -> Bool:
  match k:
    case Eng.KCr{}:
      False{}
    case Eng.KLf{}:
      False{}
    case _:
      True{}

def PL(xs: List<&2, U32>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{x, t}:
      {ncl(Spec.cls(x)) == True{} : Bool} & PL(t)

# every byte one a token may hold
def AA(t: Spec.Tok, xs: List<&2, U32>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{x, r}:
      {Spec.allows(t, Spec.cls(x)) == True{} : Bool} & AA(t, r)

# no token holds a CR or an LF
def allows.ncl(t: Spec.Tok, k: Eng.Cls, h: {Spec.allows(t, k) == True{} : Bool}) -> {ncl(k) == True{} : Bool}:
  match t k:
    case Spec.TMeth{} Eng.KSp{}:
      no({ncl(Eng.KSp{}) == True{} : Bool}, h)
    case Spec.TMeth{} Eng.KHt{}:
      no({ncl(Eng.KHt{}) == True{} : Bool}, h)
    case Spec.TMeth{} Eng.KCr{}:
      no({ncl(Eng.KCr{}) == True{} : Bool}, h)
    case Spec.TMeth{} Eng.KLf{}:
      no({ncl(Eng.KLf{}) == True{} : Bool}, h)
    case Spec.TMeth{} Eng.KCo{}:
      no({ncl(Eng.KCo{}) == True{} : Bool}, h)
    case Spec.TMeth{} Eng.KCm{}:
      no({ncl(Eng.KCm{}) == True{} : Bool}, h)
    case Spec.TMeth{} Eng.KDg{}:
      {==}
    case Spec.TMeth{} Eng.KTk{}:
      {==}
    case Spec.TMeth{} Eng.KVc{}:
      no({ncl(Eng.KVc{}) == True{} : Bool}, h)
    case Spec.TMeth{} Eng.KCt{}:
      no({ncl(Eng.KCt{}) == True{} : Bool}, h)
    case Spec.TTarget{} Eng.KSp{}:
      no({ncl(Eng.KSp{}) == True{} : Bool}, h)
    case Spec.TTarget{} Eng.KHt{}:
      no({ncl(Eng.KHt{}) == True{} : Bool}, h)
    case Spec.TTarget{} Eng.KCr{}:
      no({ncl(Eng.KCr{}) == True{} : Bool}, h)
    case Spec.TTarget{} Eng.KLf{}:
      no({ncl(Eng.KLf{}) == True{} : Bool}, h)
    case Spec.TTarget{} Eng.KCo{}:
      {==}
    case Spec.TTarget{} Eng.KCm{}:
      {==}
    case Spec.TTarget{} Eng.KDg{}:
      {==}
    case Spec.TTarget{} Eng.KTk{}:
      {==}
    case Spec.TTarget{} Eng.KVc{}:
      {==}
    case Spec.TTarget{} Eng.KCt{}:
      no({ncl(Eng.KCt{}) == True{} : Bool}, h)
    case Spec.TVer{} Eng.KSp{}:
      no({ncl(Eng.KSp{}) == True{} : Bool}, h)
    case Spec.TVer{} Eng.KHt{}:
      no({ncl(Eng.KHt{}) == True{} : Bool}, h)
    case Spec.TVer{} Eng.KCr{}:
      no({ncl(Eng.KCr{}) == True{} : Bool}, h)
    case Spec.TVer{} Eng.KLf{}:
      no({ncl(Eng.KLf{}) == True{} : Bool}, h)
    case Spec.TVer{} Eng.KCo{}:
      no({ncl(Eng.KCo{}) == True{} : Bool}, h)
    case Spec.TVer{} Eng.KCm{}:
      no({ncl(Eng.KCm{}) == True{} : Bool}, h)
    case Spec.TVer{} Eng.KDg{}:
      {==}
    case Spec.TVer{} Eng.KTk{}:
      {==}
    case Spec.TVer{} Eng.KVc{}:
      {==}
    case Spec.TVer{} Eng.KCt{}:
      no({ncl(Eng.KCt{}) == True{} : Bool}, h)
    case Spec.TName{} Eng.KSp{}:
      no({ncl(Eng.KSp{}) == True{} : Bool}, h)
    case Spec.TName{} Eng.KHt{}:
      no({ncl(Eng.KHt{}) == True{} : Bool}, h)
    case Spec.TName{} Eng.KCr{}:
      no({ncl(Eng.KCr{}) == True{} : Bool}, h)
    case Spec.TName{} Eng.KLf{}:
      no({ncl(Eng.KLf{}) == True{} : Bool}, h)
    case Spec.TName{} Eng.KCo{}:
      no({ncl(Eng.KCo{}) == True{} : Bool}, h)
    case Spec.TName{} Eng.KCm{}:
      no({ncl(Eng.KCm{}) == True{} : Bool}, h)
    case Spec.TName{} Eng.KDg{}:
      {==}
    case Spec.TName{} Eng.KTk{}:
      {==}
    case Spec.TName{} Eng.KVc{}:
      no({ncl(Eng.KVc{}) == True{} : Bool}, h)
    case Spec.TName{} Eng.KCt{}:
      no({ncl(Eng.KCt{}) == True{} : Bool}, h)
    case Spec.TOws{} Eng.KSp{}:
      {==}
    case Spec.TOws{} Eng.KHt{}:
      {==}
    case Spec.TOws{} Eng.KCr{}:
      no({ncl(Eng.KCr{}) == True{} : Bool}, h)
    case Spec.TOws{} Eng.KLf{}:
      no({ncl(Eng.KLf{}) == True{} : Bool}, h)
    case Spec.TOws{} Eng.KCo{}:
      no({ncl(Eng.KCo{}) == True{} : Bool}, h)
    case Spec.TOws{} Eng.KCm{}:
      no({ncl(Eng.KCm{}) == True{} : Bool}, h)
    case Spec.TOws{} Eng.KDg{}:
      no({ncl(Eng.KDg{}) == True{} : Bool}, h)
    case Spec.TOws{} Eng.KTk{}:
      no({ncl(Eng.KTk{}) == True{} : Bool}, h)
    case Spec.TOws{} Eng.KVc{}:
      no({ncl(Eng.KVc{}) == True{} : Bool}, h)
    case Spec.TOws{} Eng.KCt{}:
      no({ncl(Eng.KCt{}) == True{} : Bool}, h)
    case Spec.TVal{} Eng.KSp{}:
      {==}
    case Spec.TVal{} Eng.KHt{}:
      {==}
    case Spec.TVal{} Eng.KCr{}:
      no({ncl(Eng.KCr{}) == True{} : Bool}, h)
    case Spec.TVal{} Eng.KLf{}:
      no({ncl(Eng.KLf{}) == True{} : Bool}, h)
    case Spec.TVal{} Eng.KCo{}:
      {==}
    case Spec.TVal{} Eng.KCm{}:
      {==}
    case Spec.TVal{} Eng.KDg{}:
      {==}
    case Spec.TVal{} Eng.KTk{}:
      {==}
    case Spec.TVal{} Eng.KVc{}:
      {==}
    case Spec.TVal{} Eng.KCt{}:
      no({ncl(Eng.KCt{}) == True{} : Bool}, h)

def aa.pl(+t: Spec.Tok, xs: List<&2, U32>, h: AA(t, xs)) -> PL(xs):
  match xs:
    case Nil{}:
      Unit{}
    case Con{+x, r}:
      (h1, h2) = h
      (allows.ncl(t, Spec.cls(x), h1), aa.pl(t, r, h2))

def pl.app(a: List<&2, U32>, -b: List<&2, U32>, pa: PL(a), pb: PL(b)) -> PL(List.append(&2, U32, a, b)):
  match a:
    case Nil{}:
      pb
    case Con{x, t}:
      (h1, h2) = pa
      (h1, pl.app(t, b, h2, pb))

def and.split(a: Bool, -b: Bool, h: {(a && b) == True{} : Bool}) -> {a == True{} : Bool} & {b == True{} : Bool}:
  match a:
    case True{}:
      ({==}, h)
    case False{}:
      no({False{} == True{} : Bool} & {b == True{} : Bool}, h)

# the proxy's check, byte by byte, as spec.bend's classes
def aa.each.at(+t: Spec.Tok, +c: U32, -r: Bytes(),
  h: {Spec.allows(t, Eng.cls(c)) == True{} : Bool} & {X.ok.each(t, r) == True{} : Bool},
  ih: {X.ok.each(t, r) == True{} : Bool} -> AA(t, Bytes.to_list(r))) ->
  AA(t, Con{c, Bytes.to_list(r)}):
  (h1, h2) = h
  (%EL.cls_every(c) : {Spec.allows(t, _) == True{} : Bool}
   h1, ih(h2))

def aa.each(+t: Spec.Tok, s: Bytes(), h: {X.ok.each(t, s) == True{} : Bool}) -> AA(t, Bytes.to_list(s)):
  match s:
    case SNil{}:
      Unit{}
    case SCon{Chr{+c}, r}:
      aa.each.at(t, c, r, and.split(Spec.allows(t, Eng.cls(c)), X.ok.each(t, r), h), h2 => aa.each(t, r, h2))

# the bytes a range covers are ones the token holds
def e.val.sym(co: Bool, cm: Bool, tk: Bool) ->
  {Spec.allows(Spec.TVal{}, Eng.cls.sym(co, cm, tk)) == True{} : Bool}:
  match co cm tk:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def e.val.vis(+c: U32, al: Bool, dg: Bool) ->
  {Spec.allows(Spec.TVal{}, Eng.cls.vis(c, al, dg)) == True{} : Bool}:
  match al dg:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      e.val.sym(U32.is_eq(c, 58), U32.is_eq(c, 44), Eng.tsym(c))

def e.val.go(+c: U32, x: Bool, y: Bool) ->
  {Bool.and(Bool.not(x), Bool.not(y)) == True{} : Bool} ->
  {Spec.allows(Spec.TVal{}, Eng.cls.go(c, x, y)) == True{} : Bool}:
  match x y:
    case True{} True{}:
      e => no({Spec.allows(Spec.TVal{}, Eng.cls.go(c, True{}, True{})) == True{} : Bool}, e)
    case True{} False{}:
      e => no({Spec.allows(Spec.TVal{}, Eng.cls.go(c, True{}, False{})) == True{} : Bool}, e)
    case False{} True{}:
      e => no({Spec.allows(Spec.TVal{}, Eng.cls.go(c, False{}, True{})) == True{} : Bool}, e)
    case False{} False{}:
      e => e.val.vis(c, Eng.alpha(c), Eng.digit(c))

def e.val.sp(ht: Bool, cr: Bool, lf: Bool) ->
  {Spec.allows(Spec.TVal{}, Eng.cls.low(True{}, ht, cr, lf)) == True{} : Bool}:
  match ht cr lf:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def e.val.in.at(+c: U32, x: Bool, +e: {Bytes.span.in(c, 32, 127) == True{} : Bool}) ->
  {U32.is_lt(c, 33) == x : Bool} ->
  {Spec.allows(Spec.TVal{}, Eng.cls.go(c, x, U32.is_le(127, c))) == True{} : Bool}:
  match x:
    case True{}:
      xe =>
        %Equal.sym(Bool, U32.is_eq(c, 32), True{},
          U32.eq_of_lt_succ(c, 32, 33,
            Bool.and_l(Bool.not(U32.is_lt(c, 32)), Bool.not(U32.is_le(127, c)), e), xe, {==})) :
          {Spec.allows(Spec.TVal{}, Eng.cls.low(_, U32.is_eq(c, 9), U32.is_eq(c, 13), U32.is_eq(c, 10))) ==
            True{} : Bool}
        e.val.sp(U32.is_eq(c, 9), U32.is_eq(c, 13), U32.is_eq(c, 10))
    case False{}:
      xe => e.val.go(c, False{}, U32.is_le(127, c))(
        Bool.and_r(Bool.not(U32.is_lt(c, 32)), Bool.not(U32.is_le(127, c)), e))

def e.val.in(+c: U32, +e: {Bytes.span.in(c, 32, 127) == True{} : Bool}) ->
  {Spec.allows(Spec.TVal{}, Eng.cls(c)) == True{} : Bool}:
  e.val.in.at(c, U32.is_lt(c, 33), e)({==})

# a name's small letters: a letter, a token byte
def e.nm.tk(+c: U32, dg: Bool) ->
  {Spec.allows(Spec.TName{}, Eng.cls.vis(c, True{}, dg)) == True{} : Bool}:
  match dg:
    case True{}:
      {==}
    case False{}:
      {==}

def e.nm.alpha(+c: U32, +e: {Bytes.span.in(c, 97, 123) == True{} : Bool}) ->
  {Eng.alpha(c) == True{} : Bool}:
  %Equal.sym(Bool, U32.is_le(97, c), True{}, Bytes.span.in_lo(c, 97, 123, e)) :
    {Bool.or(Bool.and(U32.is_le(65, c), U32.is_le(c, 90)), Bool.and(_, U32.is_le(c, 122))) ==
      True{} : Bool}
  %Equal.sym(Bool, U32.is_le(c, 122), True{},
    Equal.trans(Bool, U32.is_le(c, 122), U32.is_lt(c, 123), True{},
      Equal.sym(Bool, U32.is_lt(c, 123), U32.is_le(c, 122), U32.lt_succ(c, 122, 123, {==})),
      Bytes.span.in_hi(c, 97, 123, e))) :
    {Bool.or(Bool.and(U32.is_le(65, c), U32.is_le(c, 90)), Bool.and(True{}, _)) == True{} : Bool}
  Bool.or_true(Bool.and(U32.is_le(65, c), U32.is_le(c, 90)))

def e.nm.in(+c: U32, +e: {Bytes.span.in(c, 97, 123) == True{} : Bool}) ->
  {Spec.allows(Spec.TName{}, Eng.cls(c)) == True{} : Bool}:
  +w = Bytes.span.in_widen(c, 97, 123, 33, 127, e, {==}, {==})
  %Equal.sym(Bool, U32.is_lt(c, 33), False{},
    Bool.not_true(U32.is_lt(c, 33), Bool.and_l(Bool.not(U32.is_lt(c, 33)), Bool.not(U32.is_le(127, c)), w))) :
    {Spec.allows(Spec.TName{}, Eng.cls.go(c, _, U32.is_le(127, c))) == True{} : Bool}
  %Equal.sym(Bool, U32.is_le(127, c), False{},
    Bool.not_true(U32.is_le(127, c), Bool.and_r(Bool.not(U32.is_lt(c, 33)), Bool.not(U32.is_le(127, c)), w))) :
    {Spec.allows(Spec.TName{}, Eng.cls.go(c, False{}, _)) == True{} : Bool}
  %Equal.sym(Bool, Eng.alpha(c), True{}, e.nm.alpha(c, e)) :
    {Spec.allows(Spec.TName{}, Eng.cls.vis(c, _, Eng.digit(c))) == True{} : Bool}
  e.nm.tk(c, Eng.digit(c))

# a target's visible ASCII: whatever the byte is past 32 and below 127
def e.tg.sym(co: Bool, cm: Bool, tk: Bool) ->
  {Spec.allows(Spec.TTarget{}, Eng.cls.sym(co, cm, tk)) == True{} : Bool}:
  match co cm tk:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def e.tg.vis(+c: U32, al: Bool, dg: Bool) ->
  {Spec.allows(Spec.TTarget{}, Eng.cls.vis(c, al, dg)) == True{} : Bool}:
  match al dg:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      e.tg.sym(U32.is_eq(c, 58), U32.is_eq(c, 44), Eng.tsym(c))

def e.tg.in(+c: U32, +e: {Bytes.span.in(c, 33, 127) == True{} : Bool}) ->
  {Spec.allows(Spec.TTarget{}, Eng.cls(c)) == True{} : Bool}:
  %Equal.sym(Bool, U32.is_lt(c, 33), False{},
    Bool.not_true(U32.is_lt(c, 33), Bool.and_l(Bool.not(U32.is_lt(c, 33)), Bool.not(U32.is_le(127, c)), e))) :
    {Spec.allows(Spec.TTarget{}, Eng.cls.go(c, _, U32.is_le(127, c))) == True{} : Bool}
  %Equal.sym(Bool, U32.is_le(127, c), False{},
    Bool.not_true(U32.is_le(127, c), Bool.and_r(Bool.not(U32.is_lt(c, 33)), Bool.not(U32.is_le(127, c)), e))) :
    {Spec.allows(Spec.TTarget{}, Eng.cls.go(c, False{}, _)) == True{} : Bool}
  e.tg.vis(c, Eng.alpha(c), Eng.digit(c))

# a method's capitals: a letter, a token byte
def e.mt.tk(+c: U32, dg: Bool) ->
  {Spec.allows(Spec.TMeth{}, Eng.cls.vis(c, True{}, dg)) == True{} : Bool}:
  match dg:
    case True{}:
      {==}
    case False{}:
      {==}

def e.mt.alpha(+c: U32, +e: {Bytes.span.in(c, 65, 91) == True{} : Bool}) -> {Eng.alpha(c) == True{} : Bool}:
  %Equal.sym(Bool, U32.is_le(65, c), True{}, Bytes.span.in_lo(c, 65, 91, e)) :
    {Bool.or(Bool.and(_, U32.is_le(c, 90)), Bool.and(U32.is_le(97, c), U32.is_le(c, 122))) == True{} : Bool}
  %Equal.sym(Bool, U32.is_le(c, 90), True{},
    Equal.trans(Bool, U32.is_le(c, 90), U32.is_lt(c, 91), True{},
      Equal.sym(Bool, U32.is_lt(c, 91), U32.is_le(c, 90), U32.lt_succ(c, 90, 91, {==})),
      Bytes.span.in_hi(c, 65, 91, e))) :
    {Bool.or(Bool.and(True{}, _), Bool.and(U32.is_le(97, c), U32.is_le(c, 122))) == True{} : Bool}
  {==}

def e.mt.in(+c: U32, +e: {Bytes.span.in(c, 65, 91) == True{} : Bool}) ->
  {Spec.allows(Spec.TMeth{}, Eng.cls(c)) == True{} : Bool}:
  +w = Bytes.span.in_widen(c, 65, 91, 33, 127, e, {==}, {==})
  %Equal.sym(Bool, U32.is_lt(c, 33), False{},
    Bool.not_true(U32.is_lt(c, 33), Bool.and_l(Bool.not(U32.is_lt(c, 33)), Bool.not(U32.is_le(127, c)), w))) :
    {Spec.allows(Spec.TMeth{}, Eng.cls.go(c, _, U32.is_le(127, c))) == True{} : Bool}
  %Equal.sym(Bool, U32.is_le(127, c), False{},
    Bool.not_true(U32.is_le(127, c), Bool.and_r(Bool.not(U32.is_lt(c, 33)), Bool.not(U32.is_le(127, c)), w))) :
    {Spec.allows(Spec.TMeth{}, Eng.cls.go(c, False{}, _)) == True{} : Bool}
  %Equal.sym(Bool, Eng.alpha(c), True{}, e.mt.alpha(c, e)) :
    {Spec.allows(Spec.TMeth{}, Eng.cls.vis(c, _, Eng.digit(c))) == True{} : Bool}
  e.mt.tk(c, Eng.digit(c))

# a buffer from its first byte, and the length of one after its first
def drop0(t: Bytes()) -> {String.drop(t, 0n) == t : Bytes()}:
  match t:
    case SNil{}:
      {==}
    case SCon{h, u}:
      {==}

def len_shift(t: Bytes()) -> {String.length.go(t, 1n) == 1n+String.length.go(t, 0n) : Nat}:
  Bytes.len.shift(t, 0n)

# a string all in a range the token holds holds only bytes it holds
def aa.conv(-t: Spec.Tok, +c: U32, h: {Spec.allows(t, Eng.cls(c)) == True{} : Bool}) ->
  {Spec.allows(t, Spec.cls(c)) == True{} : Bool}:
  %EL.cls_every(c) : {Spec.allows(t, _) == True{} : Bool}
  h

def aa.len1(-x: Nat, +r: Bytes(), e: {Nat.is_eq(x, String.length.go(r, 1n)) == True{} : Bool}) ->
  {Nat.is_eq(x, 1n+String.length.go(r, 0n)) == True{} : Bool}:
  %len_shift(r) : {Nat.is_eq(x, _) == True{} : Bool}
  e

def aa.go.at(+t: Spec.Tok, +lo: U32, +hi: U32, +c: U32, +r: Bytes(), b: Bool,
  inr: {Bytes.span.in(c, lo, hi) == True{} : Bool} -> {Spec.allows(t, Eng.cls(c)) == True{} : Bool},
  ih: {Nat.is_eq(Bytes.span.go(r, lo, hi), String.length.go(r, 0n)) == True{} : Bool} -> AA(t, Bytes.to_list(r)),
  e: {Nat.is_eq(Bytes.span.at(b, r, lo, hi), 1n+String.length.go(r, 0n)) == True{} : Bool}) ->
  {Bytes.span.in(c, lo, hi) == b : Bool} -> AA(t, Con{c, Bytes.to_list(r)}):
  match b:
    case True{}:
      eb => (aa.conv(t, c, inr(eb)), ih(e))
    case False{}:
      eb => no(AA(t, Con{c, Bytes.to_list(r)}), e)

def aa.go(~t: Spec.Tok, ~lo: U32, ~hi: U32,
  ~inr: @+c: U32 -> {Bytes.span.in(c, lo, hi) == True{} : Bool} -> {Spec.allows(t, Eng.cls(c)) == True{} : Bool}, s: Bytes(),
  e: {Nat.is_eq(Bytes.span.go(s, lo, hi), String.length.go(s, 0n)) == True{} : Bool}) -> AA(t, Bytes.to_list(s)):
  match s:
    case SNil{}:
      Unit{}
    case SCon{Chr{+c}, +r}:
      aa.go.at(t, lo, hi, c, r, Bytes.span.in(c, lo, hi), inr(c), h2 => aa.go(~t, ~lo, ~hi, ~inr, r, h2),
        aa.len1(Bytes.span.at(Bytes.span.in(c, lo, hi), r, lo, hi), r, e))({==})

def aa.fast(t: Spec.Tok, +s: Bytes(), e: {X.ok.fast(t, s) == True{} : Bool}) -> AA(t, Bytes.to_list(s)):
  match t:
    case Spec.TMeth{}:
      aa.go(~Spec.TMeth{}, ~65, ~91, ~(c => h => e.mt.in(c, h)), s,
        %drop0(s) : {Nat.is_eq(Bytes.span.go(_, 65, 91), String.length.go(s, 0n)) == True{} : Bool}
        e)
    case Spec.TTarget{}:
      aa.go(~Spec.TTarget{}, ~33, ~127, ~(c => h => e.tg.in(c, h)), s,
        %drop0(s) : {Nat.is_eq(Bytes.span.go(_, 33, 127), String.length.go(s, 0n)) == True{} : Bool}
        e)
    case Spec.TVer{}:
      no(AA(Spec.TVer{}, Bytes.to_list(s)), e)
    case Spec.TName{}:
      aa.go(~Spec.TName{}, ~97, ~123, ~(c => h => e.nm.in(c, h)), s,
        %drop0(s) : {Nat.is_eq(Bytes.span.go(_, 97, 123), String.length.go(s, 0n)) == True{} : Bool}
        e)
    case Spec.TOws{}:
      no(AA(Spec.TOws{}, Bytes.to_list(s)), e)
    case Spec.TVal{}:
      aa.go(~Spec.TVal{}, ~32, ~127, ~(c => h => e.val.in(c, h)), s,
        %drop0(s) : {Nat.is_eq(Bytes.span.go(_, 32, 127), String.length.go(s, 0n)) == True{} : Bool}
        e)

def aa.of.at(fast: Bool, +t: Spec.Tok, +s: Bytes(), ef: {X.ok.fast(t, s) == fast : Bool},
  h: {X.ok.all.at(fast, t, s) == True{} : Bool}) -> AA(t, Bytes.to_list(s)):
  match fast:
    case True{}:
      aa.fast(t, s, ef)
    case False{}:
      aa.each(t, s, h)

def aa.of(+t: Spec.Tok, +s: Bytes(), h: {X.ok.all(t, s) == True{} : Bool}) -> AA(t, Bytes.to_list(s)):
  aa.of.at(X.ok.fast(t, s), t, s, {==}, h)

# a span over bytes its token holds, stopped by one it does not
def span.to(+t: Spec.Tok, xs: List<&2, U32>, +c: U32, +rest: List<&2, U32>, h: AA(t, xs),
  hc: {Spec.allows(t, Spec.cls(c)) == False{} : Bool}) ->
  {Spec.span(t, List.append(&2, U32, xs, Con{c, rest})) == Spec.Span{xs, Spec.SAt{Spec.cls(c), c, rest}} : Spec.Span}:
  match xs:
    case Nil{}:
      %Equal.sym(Bool, Spec.allows(t, Spec.cls(c)), False{}, hc) :
        {Spec.span.pick(_, Spec.cls(c), c, rest, Spec.span(t, rest)) == Spec.Span{Nil{}, Spec.SAt{Spec.cls(c), c, rest}} :
          Spec.Span}
      {==}
    case Con{+x, +r}:
      (h1, h2) = h
      %Equal.sym(Bool, Spec.allows(t, Spec.cls(x)), True{}, h1) :
        {Spec.span.pick(_, Spec.cls(x), x, List.append(&2, U32, r, Con{c, rest}),
          Spec.span(t, List.append(&2, U32, r, Con{c, rest}))) ==
          Spec.Span{Con{x, r}, Spec.SAt{Spec.cls(c), c, rest}} : Spec.Span}
      %Equal.sym(Spec.Span, Spec.span(t, List.append(&2, U32, r, Con{c, rest})), Spec.Span{r, Spec.SAt{Spec.cls(c), c, rest}},
        span.to(t, r, c, rest, h2, hc)) : {Spec.span.push(x, _) == Spec.Span{Con{x, r}, Spec.SAt{Spec.cls(c), c, rest}} :
        Spec.Span}
      {==}

# and a span over bytes its token all holds, to the end
def span.all(+t: Spec.Tok, xs: List<&2, U32>, h: AA(t, xs)) -> {Spec.span(t, xs) == Spec.Span{xs, Spec.SEnd{}} : Spec.Span}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      (h1, h2) = h
      %Equal.sym(Bool, Spec.allows(t, Spec.cls(x)), True{}, h1) :
        {Spec.span.pick(_, Spec.cls(x), x, r, Spec.span(t, r)) == Spec.Span{Con{x, r}, Spec.SEnd{}} : Spec.Span}
      %Equal.sym(Spec.Span, Spec.span(t, r), Spec.Span{r, Spec.SEnd{}}, span.all(t, r, h2)) : {Spec.span.push(x, _) == Spec.Span{Con{x, r}, Spec.SEnd{}} : Spec.Span}
      {==}

# a line's byte is gathered
def req.plain(k: Eng.Cls, -x: U32, -cur: List<&2, U32>, -o: List<&2, Eng.Req>, -s: List<&2, U32>,
  h: {ncl(k) == True{} : Bool}) ->
  {Spec.req.byte(k, x, cur, o, s) == Spec.W{Spec.MReq{Spec.snoc(cur, x)}, o, s} : Spec.W}:
  match k:
    case Eng.KSp{}:
      {==}
    case Eng.KHt{}:
      {==}
    case Eng.KCr{}:
      no({Spec.req.byte(Eng.KCr{}, x, cur, o, s) == Spec.W{Spec.MReq{Spec.snoc(cur, x)}, o, s} : Spec.W}, h)
    case Eng.KLf{}:
      no({Spec.req.byte(Eng.KLf{}, x, cur, o, s) == Spec.W{Spec.MReq{Spec.snoc(cur, x)}, o, s} : Spec.W}, h)
    case Eng.KCo{}:
      {==}
    case Eng.KCm{}:
      {==}
    case Eng.KDg{}:
      {==}
    case Eng.KTk{}:
      {==}
    case Eng.KVc{}:
      {==}
    case Eng.KCt{}:
      {==}

def field.plain(k: Eng.Cls, -x: U32, -hd: Spec.Head, -cur: List<&2, U32>, -o: List<&2, Eng.Req>, -s: List<&2, U32>,
  h: {ncl(k) == True{} : Bool}) ->
  {Spec.field.byte(k, x, hd, cur, o, s) == Spec.W{Spec.MField{hd, Spec.snoc(cur, x)}, o, s} : Spec.W}:
  match k:
    case Eng.KSp{}:
      {==}
    case Eng.KHt{}:
      {==}
    case Eng.KCr{}:
      no({Spec.field.byte(Eng.KCr{}, x, hd, cur, o, s) == Spec.W{Spec.MField{hd, Spec.snoc(cur, x)}, o, s} : Spec.W}, h)
    case Eng.KLf{}:
      no({Spec.field.byte(Eng.KLf{}, x, hd, cur, o, s) == Spec.W{Spec.MField{hd, Spec.snoc(cur, x)}, o, s} : Spec.W}, h)
    case Eng.KCo{}:
      {==}
    case Eng.KCm{}:
      {==}
    case Eng.KDg{}:
      {==}
    case Eng.KTk{}:
      {==}
    case Eng.KVc{}:
      {==}
    case Eng.KCt{}:
      {==}

def snoc.app(+a: List<&2, U32>, +x: U32, +t: List<&2, U32>) ->
  {List.append(&2, U32, Spec.snoc(a, x), t) == List.append(&2, U32, a, Con{x, t}) : List<&2, U32>}:
  app.assoc(U32, a, Con{x, Nil{}}, t)

# LEMMA: a request line's bytes are gathered
def gather.req(xs: List<&2, U32>, +rest: List<&2, U32>, +cur: List<&2, U32>, +o: List<&2, Eng.Req>,
  +s: List<&2, U32>, pl: PL(xs)) ->
  {Spec.walk(List.append(&2, U32, xs, rest), Spec.W{Spec.MReq{cur}, o, s}) ==
    Spec.walk(rest, Spec.W{Spec.MReq{List.append(&2, U32, cur, xs)}, o, List.append(&2, U32, s, xs)}) : Spec.W}:
  match xs:
    case Nil{}:
      %Equal.sym(List<&2, U32>, List.append(&2, U32, cur, Nil{}), cur, app.nil(U32, cur)) : {Spec.walk(rest, Spec.W{Spec.MReq{cur}, o, s}) ==
        Spec.walk(rest, Spec.W{Spec.MReq{_}, o, List.append(&2, U32, s, Nil{})}) : Spec.W}
      %Equal.sym(List<&2, U32>, List.append(&2, U32, s, Nil{}), s, app.nil(U32, s)) : {Spec.walk(rest, Spec.W{Spec.MReq{cur}, o, s}) ==
        Spec.walk(rest, Spec.W{Spec.MReq{cur}, o, _}) : Spec.W}
      {==}
    case Con{+x, +t}:
      (h1, h2) = pl
      %Equal.sym(Spec.W, Spec.req.byte(Spec.cls(x), x, cur, o, Spec.snoc(s, x)),
        Spec.W{Spec.MReq{Spec.snoc(cur, x)}, o, Spec.snoc(s, x)}, req.plain(Spec.cls(x), x, cur, o, Spec.snoc(s, x), h1)) :
        {Spec.walk(List.append(&2, U32, t, rest), _) ==
          Spec.walk(rest, Spec.W{Spec.MReq{List.append(&2, U32, cur, Con{x, t})}, o, List.append(&2, U32, s, Con{x, t})}) :
          Spec.W}
      %Equal.sym(Spec.W, Spec.walk(List.append(&2, U32, t, rest), Spec.W{Spec.MReq{Spec.snoc(cur, x)}, o, Spec.snoc(s, x)}),
        Spec.walk(rest, Spec.W{Spec.MReq{List.append(&2, U32, Spec.snoc(cur, x), t)}, o, List.append(&2, U32, Spec.snoc(s, x), t)}),
        gather.req(t, rest, Spec.snoc(cur, x), o, Spec.snoc(s, x), h2)) : {_ ==
          Spec.walk(rest, Spec.W{Spec.MReq{List.append(&2, U32, cur, Con{x, t})}, o, List.append(&2, U32, s, Con{x, t})}) :
          Spec.W}
      %Equal.sym(List<&2, U32>, List.append(&2, U32, Spec.snoc(cur, x), t), List.append(&2, U32, cur, Con{x, t}),
        snoc.app(cur, x, t)) : {Spec.walk(rest, Spec.W{Spec.MReq{_}, o, List.append(&2, U32, Spec.snoc(s, x), t)}) ==
          Spec.walk(rest, Spec.W{Spec.MReq{List.append(&2, U32, cur, Con{x, t})}, o, List.append(&2, U32, s, Con{x, t})}) :
          Spec.W}
      %Equal.sym(List<&2, U32>, List.append(&2, U32, Spec.snoc(s, x), t), List.append(&2, U32, s, Con{x, t}),
        snoc.app(s, x, t)) : {Spec.walk(rest, Spec.W{Spec.MReq{List.append(&2, U32, cur, Con{x, t})}, o, _}) ==
          Spec.walk(rest, Spec.W{Spec.MReq{List.append(&2, U32, cur, Con{x, t})}, o, List.append(&2, U32, s, Con{x, t})}) :
          Spec.W}
      {==}

# LEMMA: and a field line's
def gather.field(xs: List<&2, U32>, +rest: List<&2, U32>, +hd: Spec.Head, +cur: List<&2, U32>, +o: List<&2, Eng.Req>,
  +s: List<&2, U32>, pl: PL(xs)) ->
  {Spec.walk(List.append(&2, U32, xs, rest), Spec.W{Spec.MField{hd, cur}, o, s}) ==
    Spec.walk(rest, Spec.W{Spec.MField{hd, List.append(&2, U32, cur, xs)}, o, List.append(&2, U32, s, xs)}) : Spec.W}:
  match xs:
    case Nil{}:
      %Equal.sym(List<&2, U32>, List.append(&2, U32, cur, Nil{}), cur, app.nil(U32, cur)) : {Spec.walk(rest, Spec.W{Spec.MField{hd, cur}, o, s}) ==
        Spec.walk(rest, Spec.W{Spec.MField{hd, _}, o, List.append(&2, U32, s, Nil{})}) : Spec.W}
      %Equal.sym(List<&2, U32>, List.append(&2, U32, s, Nil{}), s, app.nil(U32, s)) : {Spec.walk(rest, Spec.W{Spec.MField{hd, cur}, o, s}) ==
        Spec.walk(rest, Spec.W{Spec.MField{hd, cur}, o, _}) : Spec.W}
      {==}
    case Con{+x, +t}:
      (h1, h2) = pl
      %Equal.sym(Spec.W, Spec.field.byte(Spec.cls(x), x, hd, cur, o, Spec.snoc(s, x)),
        Spec.W{Spec.MField{hd, Spec.snoc(cur, x)}, o, Spec.snoc(s, x)}, field.plain(Spec.cls(x), x, hd, cur, o, Spec.snoc(s, x), h1)) :
        {Spec.walk(List.append(&2, U32, t, rest), _) ==
          Spec.walk(rest, Spec.W{Spec.MField{hd, List.append(&2, U32, cur, Con{x, t})}, o, List.append(&2, U32, s, Con{x, t})}) :
          Spec.W}
      %Equal.sym(Spec.W, Spec.walk(List.append(&2, U32, t, rest), Spec.W{Spec.MField{hd, Spec.snoc(cur, x)}, o, Spec.snoc(s, x)}),
        Spec.walk(rest, Spec.W{Spec.MField{hd, List.append(&2, U32, Spec.snoc(cur, x), t)}, o, List.append(&2, U32, Spec.snoc(s, x), t)}),
        gather.field(t, rest, hd, Spec.snoc(cur, x), o, Spec.snoc(s, x), h2)) : {_ ==
          Spec.walk(rest, Spec.W{Spec.MField{hd, List.append(&2, U32, cur, Con{x, t})}, o, List.append(&2, U32, s, Con{x, t})}) :
          Spec.W}
      %Equal.sym(List<&2, U32>, List.append(&2, U32, Spec.snoc(cur, x), t), List.append(&2, U32, cur, Con{x, t}),
        snoc.app(cur, x, t)) : {Spec.walk(rest, Spec.W{Spec.MField{hd, _}, o, List.append(&2, U32, Spec.snoc(s, x), t)}) ==
          Spec.walk(rest, Spec.W{Spec.MField{hd, List.append(&2, U32, cur, Con{x, t})}, o, List.append(&2, U32, s, Con{x, t})}) :
          Spec.W}
      %Equal.sym(List<&2, U32>, List.append(&2, U32, Spec.snoc(s, x), t), List.append(&2, U32, s, Con{x, t}),
        snoc.app(s, x, t)) : {Spec.walk(rest, Spec.W{Spec.MField{hd, List.append(&2, U32, cur, Con{x, t})}, o, _}) ==
          Spec.walk(rest, Spec.W{Spec.MField{hd, List.append(&2, U32, cur, Con{x, t})}, o, List.append(&2, U32, s, Con{x, t})}) :
          Spec.W}
      {==}

# What the proxy sends, as a list of bytes
# ----------------------------------------

def tl.app(+a: Bytes(), +b: Bytes()) ->
  {Bytes.to_list(Bytes.append(a, b)) == List.append(&2, U32, Bytes.to_list(a), Bytes.to_list(b)) : List<&2, U32>}:
  Bytes.to_list_append(a, b)

def RLl(+meth: Bytes(), +target: Bytes()) -> List<&2, U32>:
  List.append(&2, U32, Bytes.to_list(meth), Con{32, List.append(&2, U32, Bytes.to_list(target), Bytes.to_list(" HTTP/1.1"))})

def FLl(f: Wr.Field) -> List<&2, U32>:
  match f:
    case Wr.Field{n, v}:
      List.append(&2, U32, Bytes.to_list(n), Con{58, Con{32, Bytes.to_list(v)}})

def FLSl(fs: List<&2, Wr.Field>) -> List<&2, U32>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{f, t}:
      List.append(&2, U32, FLl(f), Con{13, Con{10, FLSl(t)}})

def rl.list(+meth: Bytes(), +target: Bytes()) -> {Bytes.to_list(X.rl.ser(meth, target)) == RLl(meth, target) : List<&2, U32>}:
  %Equal.sym(List<&2, U32>, Bytes.to_list(X.rl.ser(meth, target)),
    List.append(&2, U32, Bytes.to_list(meth), Bytes.to_list(Bytes.append(" ", Bytes.append(target, " HTTP/1.1")))),
    tl.app(meth, Bytes.append(" ", Bytes.append(target, " HTTP/1.1")))) :
    {_ == RLl(meth, target) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, Bytes.to_list(Bytes.append(target, " HTTP/1.1")),
    List.append(&2, U32, Bytes.to_list(target), Bytes.to_list(" HTTP/1.1")), tl.app(target, " HTTP/1.1")) :
    {List.append(&2, U32, Bytes.to_list(meth), Con{32, _}) == RLl(meth, target) : List<&2, U32>}
  {==}

def fl.list(f: Wr.Field) -> {Bytes.to_list(X.fl.ser(f)) == FLl(f) : List<&2, U32>}:
  match f:
    case Wr.Field{+n, +v}:
      %Equal.sym(List<&2, U32>, Bytes.to_list(Bytes.append(n, Bytes.append(": ", v))),
        List.append(&2, U32, Bytes.to_list(n), Bytes.to_list(Bytes.append(": ", v))), tl.app(n, Bytes.append(": ", v))) :
        {_ == FLl(Wr.Field{n, v}) : List<&2, U32>}
      {==}

def fls.list(fs: List<&2, Wr.Field>) -> {Bytes.to_list(X.fls.ser(fs)) == FLSl(fs) : List<&2, U32>}:
  match fs:
    case Nil{}:
      {==}
    case Con{+f, +t}:
      %Equal.sym(List<&2, U32>, Bytes.to_list(X.fls.ser(Con{f, t})),
        List.append(&2, U32, Bytes.to_list(X.fl.ser(f)), Bytes.to_list(Bytes.append("\r\n", X.fls.ser(t)))),
        tl.app(X.fl.ser(f), Bytes.append("\r\n", X.fls.ser(t)))) :
        {_ == FLSl(Con{f, t}) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, Bytes.to_list(X.fl.ser(f)), FLl(f), fl.list(f)) :
        {List.append(&2, U32, _, Con{13, Con{10, Bytes.to_list(X.fls.ser(t))}}) == FLSl(Con{f, t}) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, Bytes.to_list(X.fls.ser(t)), FLSl(t), fls.list(t)) :
        {List.append(&2, U32, FLl(f), Con{13, Con{10, _}}) == FLSl(Con{f, t}) : List<&2, U32>}
      {==}

def fls.app(a: List<&2, Wr.Field>, +b: List<&2, Wr.Field>) ->
  {FLSl(List.append(&2, Wr.Field, a, b)) == List.append(&2, U32, FLSl(a), FLSl(b)) : List<&2, U32>}:
  match a:
    case Nil{}:
      {==}
    case Con{+f, +t}:
      %Equal.sym(List<&2, U32>, FLSl(List.append(&2, Wr.Field, t, b)), List.append(&2, U32, FLSl(t), FLSl(b)),
        fls.app(t, b)) :
        {List.append(&2, U32, FLl(f), Con{13, Con{10, _}}) ==
          List.append(&2, U32, List.append(&2, U32, FLl(f), Con{13, Con{10, FLSl(t)}}), FLSl(b)) : List<&2, U32>}
      Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, FLl(f), Con{13, Con{10, FLSl(t)}}), FLSl(b)),
        List.append(&2, U32, FLl(f), Con{13, Con{10, List.append(&2, U32, FLSl(t), FLSl(b))}}),
        app.assoc(U32, FLl(f), Con{13, Con{10, FLSl(t)}}, FLSl(b)))

def SERl(m: X.Msg) -> List<&2, U32>:
  match m:
    case X.Msg{+meth, +target, +host, fs, +body, +framed}:
      List.append(&2, U32, RLl(meth, target),
        Con{13, Con{10, List.append(&2, U32, FLSl(X.allf(host, fs, framed, body)), Con{13, Con{10, Bytes.to_list(body)}})}})

def ser.list(m: X.Msg) -> {Bytes.to_list(X.ser(m)) == SERl(m) : List<&2, U32>}:
  match m:
    case X.Msg{+meth, +target, +host, +fs, +body, +framed}:
      +fls = X.fls.ser(X.allf(host, fs, framed, body))
      %Equal.sym(List<&2, U32>,
        Bytes.to_list(Bytes.append(X.rl.ser(meth, target), Bytes.append("\r\n", Bytes.append(fls, Bytes.append("\r\n", body))))),
        List.append(&2, U32, Bytes.to_list(X.rl.ser(meth, target)),
          Bytes.to_list(Bytes.append("\r\n", Bytes.append(fls, Bytes.append("\r\n", body))))),
        tl.app(X.rl.ser(meth, target), Bytes.append("\r\n", Bytes.append(fls, Bytes.append("\r\n", body))))) :
        {_ == SERl(X.Msg{meth, target, host, fs, body, framed}) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, Bytes.to_list(X.rl.ser(meth, target)), RLl(meth, target), rl.list(meth, target)) :
        {List.append(&2, U32, _, Con{13, Con{10, Bytes.to_list(Bytes.append(fls, Bytes.append("\r\n", body)))}}) ==
          SERl(X.Msg{meth, target, host, fs, body, framed}) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, Bytes.to_list(Bytes.append(fls, Bytes.append("\r\n", body))),
        List.append(&2, U32, Bytes.to_list(fls), Bytes.to_list(Bytes.append("\r\n", body))),
        tl.app(fls, Bytes.append("\r\n", body))) :
        {List.append(&2, U32, RLl(meth, target), Con{13, Con{10, _}}) == SERl(X.Msg{meth, target, host, fs, body, framed}) :
          List<&2, U32>}
      %Equal.sym(List<&2, U32>, Bytes.to_list(fls), FLSl(X.allf(host, fs, framed, body)), fls.list(X.allf(host, fs, framed, body))) :
        {List.append(&2, U32, RLl(meth, target), Con{13, Con{10, List.append(&2, U32, _, Con{13, Con{10, Bytes.to_list(body)}})}}) ==
          SERl(X.Msg{meth, target, host, fs, body, framed}) : List<&2, U32>}
      {==}

# The lines read back
# -------------------

def lit.ver() -> List<&2, U32>:
  Bytes.to_list("HTTP/1.1")

def not.full(-s: Bytes(), h: {X.full(s) == True{} : Bool}) -> Type:
  Unit

# a request line: split at its two spaces into the method and target
def view.req(meth: Bytes(), target: Bytes(), am: AA(Spec.TMeth{}, Bytes.to_list(meth)),
  at: AA(Spec.TTarget{}, Bytes.to_list(target)), nm: {X.full(meth) == True{} : Bool},
  nt: {X.full(target) == True{} : Bool}) ->
  {Spec.req.view(RLl(meth, target)) == Spec.RVer{Bytes.to_list(meth), Bytes.to_list(target), lit.ver()} : Spec.RLine}:
  match meth target:
    case SNil{} _:
      no({Spec.req.view(RLl(SNil{}, target)) == Spec.RVer{Nil{}, Bytes.to_list(target), lit.ver()} : Spec.RLine}, nm)
    case SCon{Chr{m0}, mr} SNil{}:
      no({Spec.req.view(RLl(SCon{Chr{m0}, mr}, SNil{})) == Spec.RVer{Bytes.to_list(SCon{Chr{m0}, mr}), Nil{}, lit.ver()} :
        Spec.RLine}, nt)
    case SCon{Chr{+m0}, +mr} SCon{Chr{+t0}, +tr}:
      %Equal.sym(Spec.Span, Spec.span(Spec.TMeth{}, List.append(&2, U32, Con{m0, Bytes.to_list(mr)},
          Con{32, List.append(&2, U32, Con{t0, Bytes.to_list(tr)}, Bytes.to_list(" HTTP/1.1"))})),
        Spec.Span{Con{m0, Bytes.to_list(mr)}, Spec.SAt{Spec.cls(32), 32,
          List.append(&2, U32, Con{t0, Bytes.to_list(tr)}, Bytes.to_list(" HTTP/1.1"))}},
        span.to(Spec.TMeth{}, Con{m0, Bytes.to_list(mr)}, 32,
          List.append(&2, U32, Con{t0, Bytes.to_list(tr)}, Bytes.to_list(" HTTP/1.1")), am, {==})) :
        {Spec.req.meth(_) == Spec.RVer{Con{m0, Bytes.to_list(mr)}, Con{t0, Bytes.to_list(tr)}, lit.ver()} : Spec.RLine}
      %Equal.sym(Spec.Span, Spec.span(Spec.TTarget{}, List.append(&2, U32, Con{t0, Bytes.to_list(tr)}, Con{32, lit.ver()})),
        Spec.Span{Con{t0, Bytes.to_list(tr)}, Spec.SAt{Spec.cls(32), 32, lit.ver()}},
        span.to(Spec.TTarget{}, Con{t0, Bytes.to_list(tr)}, 32, lit.ver(), at, {==})) :
        {Spec.req.target(Con{m0, Bytes.to_list(mr)}, _) ==
          Spec.RVer{Con{m0, Bytes.to_list(mr)}, Con{t0, Bytes.to_list(tr)}, lit.ver()} : Spec.RLine}
      {==}

def pl.ver() -> PL(Bytes.to_list(" HTTP/1.1")):
  ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, Unit{})))))))))

# LEMMA: the request line is read, and the fields begin
def line.req(+meth: Bytes(), +target: Bytes(), +rest: List<&2, U32>, +o: List<&2, Eng.Req>, +s: List<&2, U32>,
  +hm: {X.ok.all(Spec.TMeth{}, meth) == True{} : Bool}, +ht: {X.ok.all(Spec.TTarget{}, target) == True{} : Bool},
  nm: {X.full(meth) == True{} : Bool}, nt: {X.full(target) == True{} : Bool}) ->
  {Spec.walk(List.append(&2, U32, RLl(meth, target), Con{13, Con{10, rest}}), Spec.W{Spec.MReq{Nil{}}, o, s}) ==
    Spec.walk(rest, Spec.W{Spec.MField{Spec.head.new(Bytes.to_list(meth), Bytes.to_list(target), False{}), Nil{}}, o,
      Spec.snoc(Spec.snoc(List.append(&2, U32, s, RLl(meth, target)), 13), 10)}) : Spec.W}:
  +h0 = Spec.head.new(Bytes.to_list(meth), Bytes.to_list(target), False{})
  +s1 = List.append(&2, U32, s, RLl(meth, target))
  %Equal.sym(Spec.W, Spec.walk(List.append(&2, U32, RLl(meth, target), Con{13, Con{10, rest}}), Spec.W{Spec.MReq{Nil{}}, o, s}),
    Spec.walk(Con{13, Con{10, rest}}, Spec.W{Spec.MReq{RLl(meth, target)}, o, s1}),
    gather.req(RLl(meth, target), Con{13, Con{10, rest}}, Nil{}, o, s,
      pl.app(Bytes.to_list(meth), Con{32, List.append(&2, U32, Bytes.to_list(target), Bytes.to_list(" HTTP/1.1"))},
        aa.pl(Spec.TMeth{}, Bytes.to_list(meth), aa.of(Spec.TMeth{}, meth, hm)),
        ({==}, pl.app(Bytes.to_list(target), Bytes.to_list(" HTTP/1.1"), aa.pl(Spec.TTarget{}, Bytes.to_list(target), aa.of(Spec.TTarget{}, target, ht)),
          pl.ver()))))) :
    {_ == Spec.walk(rest, Spec.W{Spec.MField{h0, Nil{}}, o, Spec.snoc(Spec.snoc(s1, 13), 10)}) : Spec.W}
  %Equal.sym(Spec.RLine, Spec.req.view(RLl(meth, target)), Spec.RVer{Bytes.to_list(meth), Bytes.to_list(target), lit.ver()},
    view.req(meth, target, aa.of(Spec.TMeth{}, meth, hm), aa.of(Spec.TTarget{}, target, ht), nm, nt)) :
    {Spec.walk(rest, Spec.next(Spec.req.cr(_, o, Spec.snoc(s1, 13)), 10)) ==
      Spec.walk(rest, Spec.W{Spec.MField{h0, Nil{}}, o, Spec.snoc(Spec.snoc(s1, 13), 10)}) : Spec.W}
  {==}

# LEMMA: a field line is read, what it says taken into the head
def line.field(+f: Wr.Field, +rest: List<&2, U32>, +h: Spec.Head, +h2: Spec.Head, +o: List<&2, Eng.Req>,
  +s: List<&2, U32>, +val: Spec.Val, pl: PL(FLl(f)), hv: {Spec.field.view(FLl(f)) == Spec.FVal{val} : Spec.FLine},
  hd: {Spec.field.done(h, val) == Some{h2} : Maybe<&2, Spec.Head>}) ->
  {Spec.walk(List.append(&2, U32, FLl(f), Con{13, Con{10, rest}}), Spec.W{Spec.MField{h, Nil{}}, o, s}) ==
    Spec.walk(rest, Spec.W{Spec.MField{h2, Nil{}}, o, Spec.snoc(Spec.snoc(List.append(&2, U32, s, FLl(f)), 13), 10)}) :
    Spec.W}:
  +s1 = List.append(&2, U32, s, FLl(f))
  %Equal.sym(Spec.W, Spec.walk(List.append(&2, U32, FLl(f), Con{13, Con{10, rest}}), Spec.W{Spec.MField{h, Nil{}}, o, s}),
    Spec.walk(Con{13, Con{10, rest}}, Spec.W{Spec.MField{h, FLl(f)}, o, s1}),
    gather.field(FLl(f), Con{13, Con{10, rest}}, h, Nil{}, o, s, pl)) :
    {_ == Spec.walk(rest, Spec.W{Spec.MField{h2, Nil{}}, o, Spec.snoc(Spec.snoc(s1, 13), 10)}) : Spec.W}
  %Equal.sym(Spec.FLine, Spec.field.view(FLl(f)), Spec.FVal{val}, hv) :
    {Spec.walk(rest, Spec.next(Spec.field.cr(h, _, o, Spec.snoc(s1, 13)), 10)) ==
      Spec.walk(rest, Spec.W{Spec.MField{h2, Nil{}}, o, Spec.snoc(Spec.snoc(s1, 13), 10)}) : Spec.W}
  %Equal.sym(Maybe<&2, Spec.Head>, Spec.field.done(h, val), Some{h2}, hd) :
    {Spec.walk(rest, Spec.next(Spec.field.next(_, o, Spec.snoc(s1, 13)), 10)) ==
      Spec.walk(rest, Spec.W{Spec.MField{h2, Nil{}}, o, Spec.snoc(Spec.snoc(s1, 13), 10)}) : Spec.W}
  {==}

def is.other.eq(f: Eng.Fld, h: {X.is.other(f) == True{} : Bool}) -> {f == Eng.FOther{} : Eng.Fld}:
  match f:
    case Eng.FTe{}:
      no({Eng.FTe{} == Eng.FOther{} : Eng.Fld}, h)
    case Eng.FCl{}:
      no({Eng.FCl{} == Eng.FOther{} : Eng.Fld}, h)
    case Eng.FConn{}:
      no({Eng.FConn{} == Eng.FOther{} : Eng.Fld}, h)
    case Eng.FUp{}:
      no({Eng.FUp{} == Eng.FOther{} : Eng.Fld}, h)
    case Eng.FKey{}:
      no({Eng.FKey{} == Eng.FOther{} : Eng.Fld}, h)
    case Eng.FHost{}:
      no({Eng.FHost{} == Eng.FOther{} : Eng.Fld}, h)
    case Eng.FVer{}:
      no({Eng.FVer{} == Eng.FOther{} : Eng.Fld}, h)
    case Eng.FOther{}:
      {==}

# a name no framing reads, by spec.bend's lookup
def name.other(+n: Bytes(), hc: {X.is.other(Eng.fld.of(Eng.lows(n))) == True{} : Bool}) ->
  {Spec.field(Spec.lows(Bytes.from_list(Bytes.to_list(n)))) == Eng.FOther{} : Eng.Fld}:
  Equal.trans(Eng.Fld, Spec.field(Spec.lows(Bytes.from_list(Bytes.to_list(n)))), Spec.field(Spec.lows(n)), Eng.FOther{},
    Equal.cong(Bytes(), Eng.Fld, x => Spec.field(Spec.lows(x)), Bytes.from_list(Bytes.to_list(n)), n, bytes.rt(n)),
    Equal.trans(Eng.Fld, Spec.field(Spec.lows(n)), Spec.field(Eng.lows(n)), Eng.FOther{},
      Equal.cong(Bytes(), Eng.Fld, x => Spec.field(x), Spec.lows(n), Eng.lows(n), EP.br.lows(n)),
      Equal.trans(Eng.Fld, Spec.field(Eng.lows(n)), Eng.fld.of(Eng.lows(n)), Eng.FOther{},
        Equal.sym(Eng.Fld, Eng.fld.of(Eng.lows(n)), Spec.field(Eng.lows(n)), EL.field_by_bytes(Eng.lows(n))),
        is.other.eq(Eng.fld.of(Eng.lows(n)), hc))))

# an end-to-end field's line reads as one no framing reads
def view.other.at(n: Bytes(), +v: Bytes(), hn: {X.full(n) == True{} : Bool}, an: AA(Spec.TName{}, Bytes.to_list(n)),
  fo: {Spec.field(Spec.lows(Bytes.from_list(Bytes.to_list(n)))) == Eng.FOther{} : Eng.Fld},
  av: AA(Spec.TVal{}, Bytes.to_list(v))) ->
  {Spec.field.view(FLl(Wr.Field{n, v})) == Spec.FVal{Spec.VSkip{Spec.lows(Bytes.from_list(Bytes.to_list(n))), Con{32, Bytes.to_list(v)}}} : Spec.FLine}:
  match n:
    case SNil{}:
      no({Spec.field.view(FLl(Wr.Field{SNil{}, v})) ==
        Spec.FVal{Spec.VSkip{Spec.lows(Bytes.from_list(Bytes.to_list(SNil{}))), Con{32, Bytes.to_list(v)}}} : Spec.FLine}, hn)
    case SCon{Chr{+n0}, +nr}:
      +k = Spec.lows(Bytes.from_list(Con{n0, Bytes.to_list(nr)}))
      %Equal.sym(Spec.Span, Spec.span(Spec.TName{}, List.append(&2, U32, Con{n0, Bytes.to_list(nr)}, Con{58, Con{32, Bytes.to_list(v)}})),
        Spec.Span{Con{n0, Bytes.to_list(nr)}, Spec.SAt{Spec.cls(58), 58, Con{32, Bytes.to_list(v)}}},
        span.to(Spec.TName{}, Con{n0, Bytes.to_list(nr)}, 58, Con{32, Bytes.to_list(v)}, an, {==})) :
        {Spec.field.name(_) == Spec.FVal{Spec.VSkip{k, Con{32, Bytes.to_list(v)}}} : Spec.FLine}
      %Equal.sym(Eng.Fld, Spec.field(k), Eng.FOther{}, fo) :
        {Spec.field.of(_, k, Con{32, Bytes.to_list(v)}) == Spec.FVal{Spec.VSkip{k, Con{32, Bytes.to_list(v)}}} : Spec.FLine}
      %Equal.sym(Spec.Span, Spec.span(Spec.TVal{}, Bytes.to_list(v)), Spec.Span{Bytes.to_list(v), Spec.SEnd{}},
        span.all(Spec.TVal{}, Bytes.to_list(v), av)) :
        {Spec.skip.view(k, Spec.span.push(32, _)) == Spec.FVal{Spec.VSkip{k, Con{32, Bytes.to_list(v)}}} : Spec.FLine}
      {==}

def view.other(+n: Bytes(), +v: Bytes(), hn: {X.full(n) == True{} : Bool}, +ht: {X.ok.all(Spec.TName{}, n) == True{} : Bool},
  hc: {X.is.other(Eng.fld.of(Eng.lows(n))) == True{} : Bool}, +hv: {X.ok.all(Spec.TVal{}, v) == True{} : Bool}) ->
  {Spec.field.view(FLl(Wr.Field{n, v})) == Spec.FVal{Spec.VSkip{Spec.lows(Bytes.from_list(Bytes.to_list(n))), Con{32, Bytes.to_list(v)}}} : Spec.FLine}:
  view.other.at(n, v, hn, aa.of(Spec.TName{}, n, ht), name.other(n, hc), aa.of(Spec.TVal{}, v, hv))

def pl.other(+n: Bytes(), +v: Bytes(), +ht: {X.ok.all(Spec.TName{}, n) == True{} : Bool},
  +hv: {X.ok.all(Spec.TVal{}, v) == True{} : Bool}) -> PL(FLl(Wr.Field{n, v})):
  pl.app(Bytes.to_list(n), Con{58, Con{32, Bytes.to_list(v)}}, aa.pl(Spec.TName{}, Bytes.to_list(n), aa.of(Spec.TName{}, n, ht)),
    ({==}, ({==}, aa.pl(Spec.TVal{}, Bytes.to_list(v), aa.of(Spec.TVal{}, v, hv)))))

# the Host line
def view.host(+hv: Bytes(), +hh: {X.ok.all(Spec.TVal{}, hv) == True{} : Bool}) ->
  {Spec.field.view(FLl(Wr.Field{"host", hv})) == Spec.FVal{Spec.VHost{"host", Con{32, Bytes.to_list(hv)}}} : Spec.FLine}:
  %Equal.sym(Spec.Span, Spec.span(Spec.TVal{}, Bytes.to_list(hv)), Spec.Span{Bytes.to_list(hv), Spec.SEnd{}},
    span.all(Spec.TVal{}, Bytes.to_list(hv), aa.of(Spec.TVal{}, hv, hh))) :
    {Spec.host.view("host", Spec.span.push(32, _)) == Spec.FVal{Spec.VHost{"host", Con{32, Bytes.to_list(hv)}}} : Spec.FLine}
  {==}

def pl.host(+hv: Bytes(), +hh: {X.ok.all(Spec.TVal{}, hv) == True{} : Bool}) -> PL(FLl(Wr.Field{"host", hv})):
  ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, aa.pl(Spec.TVal{}, Bytes.to_list(hv), aa.of(Spec.TVal{}, hv, hh))))))))

# the Content-Length line: read as its value is
def view.cl(+d: Bytes()) ->
  {Spec.field.view(FLl(Wr.Field{"content-length", d})) == Spec.len.view(Spec.span(Spec.TOws{}, Con{32, Bytes.to_list(d)})) :
    Spec.FLine}:
  {==}

def pl.cl(+d: Bytes(), +hd: {X.ok.all(Spec.TVal{}, d) == True{} : Bool}) -> PL(FLl(Wr.Field{"content-length", d})):
  ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, 
    aa.pl(Spec.TVal{}, Bytes.to_list(d), aa.of(Spec.TVal{}, d, hd))))))))))))))))))

# The fields in the middle
# ------------------------

def SF(fs: List<&2, Wr.Field>, s: List<&2, U32>) -> List<&2, U32>:
  match fs:
    case Nil{}:
      s
    case Con{f, t}:
      SF(t, Spec.snoc(Spec.snoc(List.append(&2, U32, s, FLl(f)), 13), 10))

def split4(a: Bool, b: Bool, c: Bool, -d: Bool, h: {(a && b && c && d) == True{} : Bool}) ->
  {a == True{} : Bool} & {b == True{} : Bool} & {c == True{} : Bool} & {d == True{} : Bool}:
  match a b c:
    case True{} True{} True{}:
      ({==}, ({==}, ({==}, h)))
    case False{} _ _:
      no({False{} == True{} : Bool} & {b == True{} : Bool} & {c == True{} : Bool} & {d == True{} : Bool}, h)
    case True{} False{} _:
      no({True{} == True{} : Bool} & {False{} == True{} : Bool} & {c == True{} : Bool} & {d == True{} : Bool}, h)
    case True{} True{} False{}:
      no({True{} == True{} : Bool} & {True{} == True{} : Bool} & {False{} == True{} : Bool} & {d == True{} : Bool}, h)

def ok.field.split(+n: Bytes(), +v: Bytes(), h: {X.ok.field(Wr.Field{n, v}) == True{} : Bool}) ->
  {X.full(n) == True{} : Bool} & {X.ok.all(Spec.TName{}, n) == True{} : Bool} &
    {X.is.other(Eng.fld.of(Eng.lows(n))) == True{} : Bool} & {X.ok.all(Spec.TVal{}, v) == True{} : Bool}:
  split4(X.full(n), X.ok.all(Spec.TName{}, n), X.is.other(Eng.fld.of(Eng.lows(n))), X.ok.all(Spec.TVal{}, v), h)

def line.other(+n: Bytes(), +v: Bytes(), +rest: List<&2, U32>, +h: Spec.Head, +o: List<&2, Eng.Req>, +s: List<&2, U32>,
  hn: {X.full(n) == True{} : Bool}, +ht: {X.ok.all(Spec.TName{}, n) == True{} : Bool},
  hc: {X.is.other(Eng.fld.of(Eng.lows(n))) == True{} : Bool}, +hv: {X.ok.all(Spec.TVal{}, v) == True{} : Bool}) ->
  {Spec.walk(List.append(&2, U32, FLl(Wr.Field{n, v}), Con{13, Con{10, rest}}), Spec.W{Spec.MField{h, Nil{}}, o, s}) ==
    Spec.walk(rest, Spec.W{Spec.MField{Spec.head.fld(h, Spec.lows(Bytes.from_list(Bytes.to_list(n))), Con{32, Bytes.to_list(v)}), Nil{}}, o,
      Spec.snoc(Spec.snoc(List.append(&2, U32, s, FLl(Wr.Field{n, v})), 13), 10)}) : Spec.W}:
  line.field(Wr.Field{n, v}, rest, h, Spec.head.fld(h, Spec.lows(Bytes.from_list(Bytes.to_list(n))), Con{32, Bytes.to_list(v)}), o, s,
    Spec.VSkip{Spec.lows(Bytes.from_list(Bytes.to_list(n))), Con{32, Bytes.to_list(v)}}, pl.other(n, v, ht, hv), view.other(n, v, hn, ht, hc, hv), {==})

def line.other4(+n: Bytes(), +v: Bytes(), +rest: List<&2, U32>, +h: Spec.Head, +o: List<&2, Eng.Req>, +s: List<&2, U32>,
  fk: {X.full(n) == True{} : Bool} & {X.ok.all(Spec.TName{}, n) == True{} : Bool} &
    {X.is.other(Eng.fld.of(Eng.lows(n))) == True{} : Bool} & {X.ok.all(Spec.TVal{}, v) == True{} : Bool}) ->
  {Spec.walk(List.append(&2, U32, FLl(Wr.Field{n, v}), Con{13, Con{10, rest}}), Spec.W{Spec.MField{h, Nil{}}, o, s}) ==
    Spec.walk(rest, Spec.W{Spec.MField{Spec.head.fld(h, Spec.lows(Bytes.from_list(Bytes.to_list(n))), Con{32, Bytes.to_list(v)}), Nil{}}, o,
      Spec.snoc(Spec.snoc(List.append(&2, U32, s, FLl(Wr.Field{n, v})), 13), 10)}) : Spec.W}:
  (hn, r1) = fk
  (ht, r2) = r1
  (hc, hv) = r2
  line.other(n, v, rest, h, o, s, hn, ht, hc, hv)

# the head after the end-to-end fields: each passed on, as spec.bend's
# view reads its line (the name lowercased, the value after the colon)
def HF(fs: List<&2, Wr.Field>, h: Spec.Head) -> Spec.Head:
  match fs:
    case Nil{}:
      h
    case Con{f, t}:
      match f:
        case Wr.Field{+n, v}:
          HF(t, Spec.head.fld(h, Spec.lows(Bytes.from_list(Bytes.to_list(n))), Con{32, Bytes.to_list(v)}))

# LEMMA: the end-to-end fields are read, and passed on
def fields.con(+n: Bytes(), +v: Bytes(), +t: List<&2, Wr.Field>, +rest: List<&2, U32>, +h: Spec.Head, +o: List<&2, Eng.Req>,
  +s: List<&2, U32>, hh: {X.ok.field(Wr.Field{n, v}) == True{} : Bool} & {X.ok.fields(t) == True{} : Bool},
  ih: @+h2: Spec.Head -> @+s2: List<&2, U32> -> {X.ok.fields(t) == True{} : Bool} ->
    {Spec.walk(List.append(&2, U32, FLSl(t), rest), Spec.W{Spec.MField{h2, Nil{}}, o, s2}) ==
      Spec.walk(rest, Spec.W{Spec.MField{HF(t, h2), Nil{}}, o, SF(t, s2)}) : Spec.W}) ->
  {Spec.walk(List.append(&2, U32, FLSl(Con{Wr.Field{n, v}, t}), rest), Spec.W{Spec.MField{h, Nil{}}, o, s}) ==
    Spec.walk(rest, Spec.W{Spec.MField{HF(Con{Wr.Field{n, v}, t}, h), Nil{}}, o, SF(Con{Wr.Field{n, v}, t}, s)}) : Spec.W}:
  (h1, h2) = hh
  +s1 = Spec.snoc(Spec.snoc(List.append(&2, U32, s, FLl(Wr.Field{n, v})), 13), 10)
  +hn = Spec.head.fld(h, Spec.lows(Bytes.from_list(Bytes.to_list(n))), Con{32, Bytes.to_list(v)})
  %Equal.sym(List<&2, U32>,
    List.append(&2, U32, List.append(&2, U32, FLl(Wr.Field{n, v}), Con{13, Con{10, FLSl(t)}}), rest),
    List.append(&2, U32, FLl(Wr.Field{n, v}), Con{13, Con{10, List.append(&2, U32, FLSl(t), rest)}}),
    app.assoc(U32, FLl(Wr.Field{n, v}), Con{13, Con{10, FLSl(t)}}, rest)) :
    {Spec.walk(_, Spec.W{Spec.MField{h, Nil{}}, o, s}) == Spec.walk(rest, Spec.W{Spec.MField{HF(t, hn), Nil{}}, o, SF(t, s1)}) : Spec.W}
  Equal.trans(Spec.W,
    Spec.walk(List.append(&2, U32, FLl(Wr.Field{n, v}), Con{13, Con{10, List.append(&2, U32, FLSl(t), rest)}}),
      Spec.W{Spec.MField{h, Nil{}}, o, s}),
    Spec.walk(List.append(&2, U32, FLSl(t), rest), Spec.W{Spec.MField{hn, Nil{}}, o, s1}),
    Spec.walk(rest, Spec.W{Spec.MField{HF(t, hn), Nil{}}, o, SF(t, s1)}),
    line.other4(n, v, List.append(&2, U32, FLSl(t), rest), h, o, s, ok.field.split(n, v, h1)),
    ih(hn, s1, h2))

def fields.walk(fs: List<&2, Wr.Field>, +rest: List<&2, U32>, +h: Spec.Head, +o: List<&2, Eng.Req>, +s: List<&2, U32>,
  hok: {X.ok.fields(fs) == True{} : Bool}) ->
  {Spec.walk(List.append(&2, U32, FLSl(fs), rest), Spec.W{Spec.MField{h, Nil{}}, o, s}) ==
    Spec.walk(rest, Spec.W{Spec.MField{HF(fs, h), Nil{}}, o, SF(fs, s)}) : Spec.W}:
  match fs:
    case Nil{}:
      {==}
    case Con{f, +t}:
      match f:
        case Wr.Field{+n, +v}:
          fields.con(n, v, t, rest, h, o, s, and.split(X.ok.field(Wr.Field{n, v}), X.ok.fields(t), hok),
            h2 => s2 => e2 => fields.walk(t, rest, h2, o, s2, e2))

# The body
# --------

# LEMMA: a body of known length is counted off to its last byte, and the
# request goes out with it
def body.walk(t: Bytes(), +c: U32, +h: Spec.Head, +got: List<&2, U32>, +o: List<&2, Eng.Req>, +s: List<&2, U32>) ->
  {Spec.walk(Con{c, Bytes.to_list(t)}, Spec.W{Spec.MBody{h, Bytes.len(t), got}, o, s}) ==
    Spec.emit(h, List.append(&2, U32, got, Con{c, Bytes.to_list(t)}), o) : Spec.W}:
  match t:
    case SNil{}:
      {==}
    case SCon{Chr{+c2}, +t2}:
      %Equal.sym(Nat, Bytes.len(SCon{Chr{c2}, t2}), 1n+Bytes.len(t2), Bytes.len.shift(t2, 0n)) :
        {Spec.walk(Con{c, Con{c2, Bytes.to_list(t2)}}, Spec.W{Spec.MBody{h, _, got}, o, s}) ==
          Spec.emit(h, List.append(&2, U32, got, Con{c, Con{c2, Bytes.to_list(t2)}}), o) : Spec.W}
      %snoc.app(got, c, Con{c2, Bytes.to_list(t2)}) :
        {Spec.walk(Con{c2, Bytes.to_list(t2)}, Spec.W{Spec.MBody{h, Bytes.len(t2), Spec.snoc(got, c)}, o, Spec.snoc(s, c)}) ==
          Spec.emit(h, _, o) : Spec.W}
      body.walk(t2, c2, h, Spec.snoc(got, c), o, Spec.snoc(s, c))

# The head's end, and the body after it
# -------------------------------------

def nat.eq(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      no({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      no({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, x => 1n+x, p, q, nat.eq(p, q, h))

# the request spec.bend reads, from the bytes the proxy sent
def RQ(+meth: Bytes(), +target: Bytes(), +x: Eng.Hx, +body: Bytes()) -> Eng.Req:
  Eng.Req{Spec.method(meth), target, body, False{}, False{}, "", Spec.hd(x, False{})}

def rq.rt(+meth: Bytes(), +target: Bytes(), +x: Eng.Hx, +body: Bytes()) ->
  {Eng.Req{Spec.method(Bytes.from_list(Bytes.to_list(meth))), Bytes.from_list(Bytes.to_list(target)),
    Bytes.from_list(Bytes.to_list(body)), False{}, False{}, "", Spec.hd(x, False{})} == RQ(meth, target, x, body) : Eng.Req}:
  %Equal.sym(Bytes(), Bytes.from_list(Bytes.to_list(meth)), meth, bytes.rt(meth)) : {Eng.Req{Spec.method(_), Bytes.from_list(Bytes.to_list(target)),
    Bytes.from_list(Bytes.to_list(body)), False{}, False{}, "", Spec.hd(x, False{})} == RQ(meth, target, x, body) : Eng.Req}
  %Equal.sym(Bytes(), Bytes.from_list(Bytes.to_list(target)), target, bytes.rt(target)) : {Eng.Req{Spec.method(meth), _, Bytes.from_list(Bytes.to_list(body)), False{}, False{}, "", Spec.hd(x, False{})} ==
    RQ(meth, target, x, body) : Eng.Req}
  %Equal.sym(Bytes(), Bytes.from_list(Bytes.to_list(body)), body, bytes.rt(body)) : {Eng.Req{Spec.method(meth), target, _, False{}, False{}, "", Spec.hd(x, False{})} == RQ(meth, target, x, body) : Eng.Req}
  {==}

def H1(+meth: Bytes(), +target: Bytes(), +x: Eng.Hx) -> Spec.Head:
  Spec.Head{Spec.method(Bytes.from_list(Bytes.to_list(meth))), Bytes.to_list(target), None{}, False{}, 1n, Nil{}, False{},
    False{}, False{}, Eng.Fx{False{}, False{}, False{}}, x}

def H2(+meth: Bytes(), +target: Bytes(), +x: Eng.Hx, +n: U32) -> Spec.Head:
  Spec.Head{Spec.method(Bytes.from_list(Bytes.to_list(meth))), Bytes.to_list(target), Some{n}, False{}, 1n, Nil{}, False{},
    False{}, False{}, Eng.Fx{False{}, False{}, False{}}, x}

def W.done(+meth: Bytes(), +target: Bytes(), +x: Eng.Hx, +body: Bytes(), o: List<&2, Eng.Req>) -> Spec.W:
  Spec.W{Spec.MReq{Nil{}}, Con{RQ(meth, target, x, body), o}, Nil{}}

# no length: the head ends the request, whose body is empty
def tail.none(+meth: Bytes(), +target: Bytes(), +x: Eng.Hx, body: Bytes(), +o: List<&2, Eng.Req>, +s: List<&2, U32>,
  hb: {String.is_empty(body) == True{} : Bool}) ->
  {Spec.walk(Con{13, Con{10, Bytes.to_list(body)}}, Spec.W{Spec.MField{H1(meth, target, x), Nil{}}, o, s}) ==
    W.done(meth, target, x, body, o) : Spec.W}:
  match body:
    case SNil{}:
      Equal.cong(Eng.Req, Spec.W, r => Spec.W{Spec.MReq{Nil{}}, Con{r, o}, Nil{}},
        Eng.Req{Spec.method(Bytes.from_list(Bytes.to_list(meth))), Bytes.from_list(Bytes.to_list(target)),
          Bytes.from_list(Bytes.to_list("")), False{}, False{}, "", Spec.hd(x, False{})}, RQ(meth, target, x, ""), rq.rt(meth, target, x, ""))
    case SCon{c, t}:
      no({Spec.walk(Con{13, Con{10, Bytes.to_list(SCon{c, t})}}, Spec.W{Spec.MField{H1(meth, target, x), Nil{}}, o, s}) ==
        W.done(meth, target, x, SCon{c, t}, o) : Spec.W}, hb)

def sub0(x: Nat) -> {Nat.sub(x, 0n) == x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def tail.z(z: Bool, +meth: Bytes(), +target: Bytes(), +x: Eng.Hx, body: Bytes(), +n: U32, +o: List<&2, Eng.Req>, +s: List<&2, U32>,
  hz: {X.same(z, String.is_empty(body)) == True{} : Bool}, hn: {Nat.is_eq(U32.to_nat(n), Bytes.len(body)) == True{} : Bool}) ->
  {Spec.walk(Bytes.to_list(body), Spec.head.body(z, n, H2(meth, target, x, n), o, s)) == W.done(meth, target, x, body, o) : Spec.W}:
  match z body:
    case True{} SNil{}:
      Equal.cong(Eng.Req, Spec.W, r => Spec.W{Spec.MReq{Nil{}}, Con{r, o}, Nil{}},
        Eng.Req{Spec.method(Bytes.from_list(Bytes.to_list(meth))), Bytes.from_list(Bytes.to_list(target)),
          Bytes.from_list(Bytes.to_list("")), False{}, False{}, "", Spec.hd(x, False{})}, RQ(meth, target, x, ""), rq.rt(meth, target, x, ""))
    case True{} SCon{c, t}:
      no({Spec.walk(Bytes.to_list(SCon{c, t}), Spec.head.body(True{}, n, H2(meth, target, x, n), o, s)) ==
        W.done(meth, target, x, SCon{c, t}, o) : Spec.W}, hz)
    case False{} SNil{}:
      no({Spec.walk(Nil{}, Spec.head.body(False{}, n, H2(meth, target, x, n), o, s)) == W.done(meth, target, x, SNil{}, o) : Spec.W}, hz)
    case False{} SCon{Chr{+c}, +t}:
      %Equal.sym(Nat, U32.to_nat(n), Bytes.len(SCon{Chr{c}, t}), nat.eq(U32.to_nat(n), Bytes.len(SCon{Chr{c}, t}), hn)) :
        {Spec.walk(Con{c, Bytes.to_list(t)}, Spec.W{Spec.MBody{H2(meth, target, x, n), Nat.sub(_, 1n), Nil{}}, o, s}) ==
          W.done(meth, target, x, SCon{Chr{c}, t}, o) : Spec.W}
      %Equal.sym(Nat, Bytes.len(SCon{Chr{c}, t}), 1n+Bytes.len(t), Bytes.len.shift(t, 0n)) :
        {Spec.walk(Con{c, Bytes.to_list(t)}, Spec.W{Spec.MBody{H2(meth, target, x, n), Nat.sub(_, 1n), Nil{}}, o, s}) ==
          W.done(meth, target, x, SCon{Chr{c}, t}, o) : Spec.W}
      %Equal.sym(Nat, Nat.sub(Bytes.len(t), 0n), Bytes.len(t), sub0(Bytes.len(t))) :
        {Spec.walk(Con{c, Bytes.to_list(t)}, Spec.W{Spec.MBody{H2(meth, target, x, n), _, Nil{}}, o, s}) ==
          W.done(meth, target, x, SCon{Chr{c}, t}, o) : Spec.W}
      Equal.trans(Spec.W, Spec.walk(Con{c, Bytes.to_list(t)}, Spec.W{Spec.MBody{H2(meth, target, x, n), Bytes.len(t), Nil{}}, o, s}),
        Spec.emit(H2(meth, target, x, n), Con{c, Bytes.to_list(t)}, o), W.done(meth, target, x, SCon{Chr{c}, t}, o),
        body.walk(t, c, H2(meth, target, x, n), Nil{}, o, s),
        Equal.cong(Eng.Req, Spec.W, r => Spec.W{Spec.MReq{Nil{}}, Con{r, o}, Nil{}},
          Eng.Req{Spec.method(Bytes.from_list(Bytes.to_list(meth))), Bytes.from_list(Bytes.to_list(target)),
            Bytes.from_list(Bytes.to_list(SCon{Chr{c}, t})), False{}, False{}, "", Spec.hd(x, False{})},
          RQ(meth, target, x, SCon{Chr{c}, t}), rq.rt(meth, target, x, SCon{Chr{c}, t})))

# a length: the body counted off by it
def tail.len(+meth: Bytes(), +target: Bytes(), +x: Eng.Hx, +body: Bytes(), +n: U32, +o: List<&2, Eng.Req>, +s: List<&2, U32>,
  hz: {X.same(U32.is_zero(n), String.is_empty(body)) == True{} : Bool},
  hn: {Nat.is_eq(U32.to_nat(n), Bytes.len(body)) == True{} : Bool}) ->
  {Spec.walk(Con{13, Con{10, Bytes.to_list(body)}}, Spec.W{Spec.MField{H2(meth, target, x, n), Nil{}}, o, s}) ==
    W.done(meth, target, x, body, o) : Spec.W}:
  tail.z(U32.is_zero(n), meth, target, x, body, n, o, Spec.snoc(Spec.snoc(s, 13), 10), hz, hn)

# A request, read back whole
# --------------------------

def T7(a: Bool, b: Bool, c: Bool, d: Bool, e: Bool, f: Bool, g: Bool) -> Type:
  {a == True{} : Bool} & {b == True{} : Bool} & {c == True{} : Bool} & {d == True{} : Bool} & {e == True{} : Bool} &
    {f == True{} : Bool} & {g == True{} : Bool}

def split7(a: Bool, b: Bool, c: Bool, d: Bool, e: Bool, f: Bool, -g: Bool,
  h: {(a && b && c && d && e && f && g) == True{} : Bool}) -> T7(a, b, c, d, e, f, g):
  match a:
    case False{}:
      no(T7(False{}, b, c, d, e, f, g), h)
    case True{}:
      match b:
        case False{}:
          no(T7(True{}, False{}, c, d, e, f, g), h)
        case True{}:
          match c:
            case False{}:
              no(T7(True{}, True{}, False{}, d, e, f, g), h)
            case True{}:
              match d:
                case False{}:
                  no(T7(True{}, True{}, True{}, False{}, e, f, g), h)
                case True{}:
                  match e:
                    case False{}:
                      no(T7(True{}, True{}, True{}, True{}, False{}, f, g), h)
                    case True{}:
                      match f:
                        case False{}:
                          no(T7(True{}, True{}, True{}, True{}, True{}, False{}, g), h)
                        case True{}:
                          ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, h))))))

def E.tail(body: Bytes()) -> List<&2, U32>:
  Con{13, Con{10, Bytes.to_list(body)}}

def mw.cl.len(+meth: Bytes(), +target: Bytes(), +x: Eng.Hx, +body: Bytes(), +d: Bytes(), +n: U32, +ws: Bool, +o: List<&2, Eng.Req>,
  +s: List<&2, U32>, +ad: {X.ok.all(Spec.TVal{}, d) == True{} : Bool},
  hlv: {Spec.len.view(Spec.span(Spec.TOws{}, Con{32, Bytes.to_list(d)})) == Spec.FVal{Spec.VLen{n, ws}} : Spec.FLine},
  hk: {X.same(U32.is_zero(n), String.is_empty(body)) == True{} : Bool} &
    {Nat.is_eq(U32.to_nat(n), Bytes.len(body)) == True{} : Bool}) ->
  {Spec.walk(List.append(&2, U32, FLl(Wr.Field{"content-length", d}), Con{13, Con{10, E.tail(body)}}),
    Spec.W{Spec.MField{H1(meth, target, x), Nil{}}, o, s}) == W.done(meth, target, x, body, o) : Spec.W}:
  (hz, hn) = hk
  Equal.trans(Spec.W,
    Spec.walk(List.append(&2, U32, FLl(Wr.Field{"content-length", d}), Con{13, Con{10, E.tail(body)}}),
      Spec.W{Spec.MField{H1(meth, target, x), Nil{}}, o, s}),
    Spec.walk(E.tail(body), Spec.W{Spec.MField{H2(meth, target, x, n), Nil{}}, o,
      Spec.snoc(Spec.snoc(List.append(&2, U32, s, FLl(Wr.Field{"content-length", d})), 13), 10)}),
    W.done(meth, target, x, body, o),
    line.field(Wr.Field{"content-length", d}, E.tail(body), H1(meth, target, x), H2(meth, target, x, n), o, s, Spec.VLen{n, ws},
      pl.cl(d, ad),
      Equal.trans(Spec.FLine, Spec.field.view(FLl(Wr.Field{"content-length", d})),
        Spec.len.view(Spec.span(Spec.TOws{}, Con{32, Bytes.to_list(d)})), Spec.FVal{Spec.VLen{n, ws}}, view.cl(d), hlv),
      {==}),
    tail.len(meth, target, x, body, n, o, Spec.snoc(Spec.snoc(List.append(&2, U32, s, FLl(Wr.Field{"content-length", d})), 13), 10),
      hz, hn))

def mw.cl.val(val: Spec.Val, +meth: Bytes(), +target: Bytes(), +x: Eng.Hx, +body: Bytes(), +d: Bytes(), +o: List<&2, Eng.Req>,
  +s: List<&2, U32>, +ad: {X.ok.all(Spec.TVal{}, d) == True{} : Bool},
  hlv: {Spec.len.view(Spec.span(Spec.TOws{}, Con{32, Bytes.to_list(d)})) == Spec.FVal{val} : Spec.FLine},
  ak: {X.ok.len.at(Spec.FVal{val}, body) == True{} : Bool}) ->
  {Spec.walk(List.append(&2, U32, FLl(Wr.Field{"content-length", d}), Con{13, Con{10, E.tail(body)}}),
    Spec.W{Spec.MField{H1(meth, target, x), Nil{}}, o, s}) == W.done(meth, target, x, body, o) : Spec.W}:
  match val:
    case Spec.VLen{+n, +ws}:
      mw.cl.len(meth, target, x, body, d, n, ws, o, s, ad, hlv,
        and.split(X.same(U32.is_zero(n), String.is_empty(body)), Nat.is_eq(U32.to_nat(n), Bytes.len(body)), ak))
    case Spec.VLen0{}:
      no({Spec.walk(List.append(&2, U32, FLl(Wr.Field{"content-length", d}), Con{13, Con{10, E.tail(body)}}),
        Spec.W{Spec.MField{H1(meth, target, x), Nil{}}, o, s}) == W.done(meth, target, x, body, o) : Spec.W}, ak)
    case Spec.VConn{dn, cu}:
      no({Spec.walk(List.append(&2, U32, FLl(Wr.Field{"content-length", d}), Con{13, Con{10, E.tail(body)}}),
        Spec.W{Spec.MField{H1(meth, target, x), Nil{}}, o, s}) == W.done(meth, target, x, body, o) : Spec.W}, ak)
    case Spec.VUp{dn, cu}:
      no({Spec.walk(List.append(&2, U32, FLl(Wr.Field{"content-length", d}), Con{13, Con{10, E.tail(body)}}),
        Spec.W{Spec.MField{H1(meth, target, x), Nil{}}, o, s}) == W.done(meth, target, x, body, o) : Spec.W}, ak)
    case Spec.VKey0{}:
      no({Spec.walk(List.append(&2, U32, FLl(Wr.Field{"content-length", d}), Con{13, Con{10, E.tail(body)}}),
        Spec.W{Spec.MField{H1(meth, target, x), Nil{}}, o, s}) == W.done(meth, target, x, body, o) : Spec.W}, ak)
    case Spec.VKey{k}:
      no({Spec.walk(List.append(&2, U32, FLl(Wr.Field{"content-length", d}), Con{13, Con{10, E.tail(body)}}),
        Spec.W{Spec.MField{H1(meth, target, x), Nil{}}, o, s}) == W.done(meth, target, x, body, o) : Spec.W}, ak)
    case Spec.VVer{v}:
      no({Spec.walk(List.append(&2, U32, FLl(Wr.Field{"content-length", d}), Con{13, Con{10, E.tail(body)}}),
        Spec.W{Spec.MField{H1(meth, target, x), Nil{}}, o, s}) == W.done(meth, target, x, body, o) : Spec.W}, ak)
    case Spec.VTe0{}:
      no({Spec.walk(List.append(&2, U32, FLl(Wr.Field{"content-length", d}), Con{13, Con{10, E.tail(body)}}),
        Spec.W{Spec.MField{H1(meth, target, x), Nil{}}, o, s}) == W.done(meth, target, x, body, o) : Spec.W}, ak)
    case Spec.VTe{t}:
      no({Spec.walk(List.append(&2, U32, FLl(Wr.Field{"content-length", d}), Con{13, Con{10, E.tail(body)}}),
        Spec.W{Spec.MField{H1(meth, target, x), Nil{}}, o, s}) == W.done(meth, target, x, body, o) : Spec.W}, ak)
    case Spec.VHost{hn0, hv0}:
      no({Spec.walk(List.append(&2, U32, FLl(Wr.Field{"content-length", d}), Con{13, Con{10, E.tail(body)}}),
        Spec.W{Spec.MField{H1(meth, target, x), Nil{}}, o, s}) == W.done(meth, target, x, body, o) : Spec.W}, ak)
    case Spec.VSkip{sn0, sv0}:
      no({Spec.walk(List.append(&2, U32, FLl(Wr.Field{"content-length", d}), Con{13, Con{10, E.tail(body)}}),
        Spec.W{Spec.MField{H1(meth, target, x), Nil{}}, o, s}) == W.done(meth, target, x, body, o) : Spec.W}, ak)

def mw.cl.view(lv: Spec.FLine, +meth: Bytes(), +target: Bytes(), +x: Eng.Hx, +body: Bytes(), +d: Bytes(), +o: List<&2, Eng.Req>,
  +s: List<&2, U32>, +ad: {X.ok.all(Spec.TVal{}, d) == True{} : Bool},
  hlv: {Spec.len.view(Spec.span(Spec.TOws{}, Con{32, Bytes.to_list(d)})) == lv : Spec.FLine},
  ak: {X.ok.len.at(lv, body) == True{} : Bool}) ->
  {Spec.walk(List.append(&2, U32, FLl(Wr.Field{"content-length", d}), Con{13, Con{10, E.tail(body)}}),
    Spec.W{Spec.MField{H1(meth, target, x), Nil{}}, o, s}) == W.done(meth, target, x, body, o) : Spec.W}:
  match lv:
    case Spec.FVal{val}:
      mw.cl.val(val, meth, target, x, body, d, o, s, ad, hlv, ak)
    case Spec.FEmpty{}:
      no({Spec.walk(List.append(&2, U32, FLl(Wr.Field{"content-length", d}), Con{13, Con{10, E.tail(body)}}),
        Spec.W{Spec.MField{H1(meth, target, x), Nil{}}, o, s}) == W.done(meth, target, x, body, o) : Spec.W}, ak)
    case Spec.FName{nm}:
      no({Spec.walk(List.append(&2, U32, FLl(Wr.Field{"content-length", d}), Con{13, Con{10, E.tail(body)}}),
        Spec.W{Spec.MField{H1(meth, target, x), Nil{}}, o, s}) == W.done(meth, target, x, body, o) : Spec.W}, ak)
    case Spec.FBad{}:
      no({Spec.walk(List.append(&2, U32, FLl(Wr.Field{"content-length", d}), Con{13, Con{10, E.tail(body)}}),
        Spec.W{Spec.MField{H1(meth, target, x), Nil{}}, o, s}) == W.done(meth, target, x, body, o) : Spec.W}, ak)

def mw.cl(+meth: Bytes(), +target: Bytes(), +x: Eng.Hx, +body: Bytes(), +o: List<&2, Eng.Req>, +s: List<&2, U32>,
  al: {X.ok.all(Spec.TVal{}, Nat.show(Bytes.len(body))) == True{} : Bool} &
    {X.ok.len.at(Spec.len.view(Spec.span(Spec.TOws{}, Con{32, Bytes.to_list(Nat.show(Bytes.len(body)))})), body) == True{} :
      Bool}) ->
  {Spec.walk(List.append(&2, U32, FLl(Wr.Field{"content-length", Nat.show(Bytes.len(body))}), Con{13, Con{10, E.tail(body)}}),
    Spec.W{Spec.MField{H1(meth, target, x), Nil{}}, o, s}) == W.done(meth, target, x, body, o) : Spec.W}:
  (ad, ak) = al
  mw.cl.view(Spec.len.view(Spec.span(Spec.TOws{}, Con{32, Bytes.to_list(Nat.show(Bytes.len(body)))})), meth, target, x, body,
    Nat.show(Bytes.len(body)), o, s, ad, {==}, ak)

# the length, or none
def mw.len(b: Bool, +meth: Bytes(), +target: Bytes(), +x: Eng.Hx, +body: Bytes(), +o: List<&2, Eng.Req>, +s: List<&2, U32>,
  al: {X.ok.len.on(b, body) == True{} : Bool}) ->
  {Spec.walk(List.append(&2, U32, FLSl(X.clf.at(b, body)), E.tail(body)), Spec.W{Spec.MField{H1(meth, target, x), Nil{}}, o, s}) ==
    W.done(meth, target, x, body, o) : Spec.W}:
  match b:
    case False{}:
      tail.none(meth, target, x, body, o, s, al)
    case True{}:
      %Equal.sym(List<&2, U32>,
        List.append(&2, U32, List.append(&2, U32, FLl(Wr.Field{"content-length", Nat.show(Bytes.len(body))}), Con{13, Con{10, Nil{}}}),
          E.tail(body)),
        List.append(&2, U32, FLl(Wr.Field{"content-length", Nat.show(Bytes.len(body))}), Con{13, Con{10, E.tail(body)}}),
        app.assoc(U32, FLl(Wr.Field{"content-length", Nat.show(Bytes.len(body))}), Con{13, Con{10, Nil{}}}, E.tail(body))) :
        {Spec.walk(_, Spec.W{Spec.MField{H1(meth, target, x), Nil{}}, o, s}) == W.done(meth, target, x, body, o) : Spec.W}
      mw.cl(meth, target, x, body, o, s,
        and.split(X.ok.all(Spec.TVal{}, Nat.show(Bytes.len(body))),
          X.ok.len.at(Spec.len.view(Spec.span(Spec.TOws{}, Con{32, Bytes.to_list(Nat.show(Bytes.len(body)))})), body), al))

def WF(+h: Spec.Head, +o: List<&2, Eng.Req>, +s: List<&2, U32>) -> Spec.W:
  Spec.W{Spec.MField{h, Nil{}}, o, s}

# the fields passed on, as the head holds them
def convs(fs: List<&2, Wr.Field>) -> List<&2, Wr.Field>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{f, t}:
      match f:
        case Wr.Field{+n, v}:
          Con{Wr.Field{Spec.lows(Bytes.from_list(Bytes.to_list(n))), Bytes.from_list(Con{32, Bytes.to_list(v)})}, convs(t)}

def NM(fs: List<&2, Wr.Field>, nm: Bytes()) -> Bytes():
  match fs:
    case Nil{}:
      nm
    case Con{f, t}:
      match f:
        case Wr.Field{+n, v}:
          NM(t, Spec.lows(Bytes.from_list(Bytes.to_list(n))))

def hf.h1(fs: List<&2, Wr.Field>, +meth: Bytes(), +target: Bytes(), +mb: Bytes(), +nm: Bytes(), +acc: List<&2, Wr.Field>,
  +cn: List<&2, Bytes()>) ->
  {HF(fs, H1(meth, target, Eng.Hx{mb, nm, acc, cn})) ==
    H1(meth, target, Eng.Hx{mb, NM(fs, nm), List.reverse.go(&2, Wr.Field, convs(fs), acc), cn}) : Spec.Head}:
  match fs:
    case Nil{}:
      {==}
    case Con{f, t}:
      match f:
        case Wr.Field{+n, +v}:
          hf.h1(t, meth, target, mb, Spec.lows(Bytes.from_list(Bytes.to_list(n))),
            Con{Wr.Field{Spec.lows(Bytes.from_list(Bytes.to_list(n))), Bytes.from_list(Con{32, Bytes.to_list(v)})}, acc}, cn)

# the fields as the head holds them are the fields the proxy sent
def convs.sent(fs: List<&2, Wr.Field>) -> {convs(fs) == Laws.sent(fs) : List<&2, Wr.Field>}:
  match fs:
    case Nil{}:
      {==}
    case Con{f, t}:
      match f:
        case Wr.Field{+n, +v}:
          %Equal.sym(Bytes(), Bytes.from_list(Bytes.to_list(n)), n, bytes.rt(n)) :
            {Con{Wr.Field{Spec.lows(_), Bytes.from_list(Con{32, Bytes.to_list(v)})}, convs(t)} ==
              Laws.sent(Con{Wr.Field{n, v}, t}) : List<&2, Wr.Field>}
          %Equal.sym(Bytes(), Bytes.from_list(Bytes.to_list(v)), v, bytes.rt(v)) :
            {Con{Wr.Field{Spec.lows(n), SCon{Chr{32}, _}}, convs(t)} ==
              Laws.sent(Con{Wr.Field{n, v}, t}) : List<&2, Wr.Field>}
          %Equal.sym(List<&2, Wr.Field>, convs(t), Laws.sent(t), convs.sent(t)) :
            {Con{Wr.Field{Spec.lows(n), SCon{Chr{32}, v}}, _} == Laws.sent(Con{Wr.Field{n, v}, t}) : List<&2, Wr.Field>}
          {==}

# the head handed on is the one the proxy sent: its method, the Host,
# then the fields in order
def hd.sent(+meth: Bytes(), +host: Bytes(), +fs: List<&2, Wr.Field>, +nm: Bytes()) ->
  {Spec.hd(Eng.Hx{Bytes.from_list(Bytes.to_list(meth)), nm, List.reverse.go(&2, Wr.Field, convs(fs), Con{Wr.Field{"host", Bytes.from_list(Con{32, Bytes.to_list(host)})}, Nil{}}), Nil{}}, False{}) ==
    Eng.Hd{meth, False{}, Con{Wr.Field{"host", Bytes.append(" ", host)}, Laws.sent(fs)}, Nil{}} : Eng.Hd}:
  %Equal.sym(Bytes(), Bytes.from_list(Bytes.to_list(meth)), meth, bytes.rt(meth)) :
    {Eng.Hd{_, False{}, List.reverse(&2, Wr.Field, List.reverse(&2, Wr.Field, Con{Wr.Field{"host", Bytes.from_list(Con{32, Bytes.to_list(host)})}, convs(fs)})), Nil{}} ==
      Eng.Hd{meth, False{}, Con{Wr.Field{"host", Bytes.append(" ", host)}, Laws.sent(fs)}, Nil{}} : Eng.Hd}
  %Equal.sym(List<&2, Wr.Field>, List.reverse(&2, Wr.Field, List.reverse(&2, Wr.Field, Con{Wr.Field{"host", Bytes.from_list(Con{32, Bytes.to_list(host)})}, convs(fs)})),
    Con{Wr.Field{"host", Bytes.from_list(Con{32, Bytes.to_list(host)})}, convs(fs)}, rev.rev(Wr.Field, Con{Wr.Field{"host", Bytes.from_list(Con{32, Bytes.to_list(host)})}, convs(fs)})) :
    {Eng.Hd{meth, False{}, _, Nil{}} ==
      Eng.Hd{meth, False{}, Con{Wr.Field{"host", Bytes.append(" ", host)}, Laws.sent(fs)}, Nil{}} : Eng.Hd}
  %Equal.sym(Bytes(), Bytes.from_list(Bytes.to_list(host)), host, bytes.rt(host)) :
    {Eng.Hd{meth, False{}, Con{Wr.Field{"host", SCon{Chr{32}, _}}, convs(fs)}, Nil{}} ==
      Eng.Hd{meth, False{}, Con{Wr.Field{"host", Bytes.append(" ", host)}, Laws.sent(fs)}, Nil{}} : Eng.Hd}
  %Equal.sym(List<&2, Wr.Field>, convs(fs), Laws.sent(fs), convs.sent(fs)) :
    {Eng.Hd{meth, False{}, Con{Wr.Field{"host", SCon{Chr{32}, host}}, _}, Nil{}} ==
      Eng.Hd{meth, False{}, Con{Wr.Field{"host", Bytes.append(" ", host)}, Laws.sent(fs)}, Nil{}} : Eng.Hd}
  {==}

# LEMMA: a request the proxy checked, sent, is read back as itself: its
# line, its Host, the end-to-end fields passed on, its length and its
# body, and the walk is back where a request begins
def mw.at(+meth: Bytes(), +target: Bytes(), +host: Bytes(), +fs: List<&2, Wr.Field>, +body: Bytes(), +framed: Bool,
  +o: List<&2, Eng.Req>, +s: List<&2, U32>,
  v: T7(X.full(meth), X.ok.all(Spec.TMeth{}, meth), X.full(target), X.ok.all(Spec.TTarget{}, target),
    X.ok.all(Spec.TVal{}, host), X.ok.fields(fs), X.ok.len.on(X.clen.on(framed, body), body))) ->
  {Spec.walk(SERl(X.Msg{meth, target, host, fs, body, framed}), Spec.W{Spec.MReq{Nil{}}, o, s}) ==
    W.done(meth, target, Eng.Hx{Bytes.from_list(Bytes.to_list(meth)), NM(fs, "host"), List.reverse.go(&2, Wr.Field, convs(fs), Con{Wr.Field{"host", Bytes.from_list(Con{32, Bytes.to_list(host)})}, Nil{}}), Nil{}},
      body, o) : Spec.W}:
  (nm, v1) = v
  (hm, v2) = v1
  (nt, v3) = v2
  (ht, v4) = v3
  (+hh, v5) = v4
  (hfs, hl) = v5
  +hf : Wr.Field = Wr.Field{"host", host}
  +clf = X.clf.at(X.clen.on(framed, body), body)
  +tl = E.tail(body)
  +x0 : Eng.Hx = Eng.Hx{Bytes.from_list(Bytes.to_list(meth)), "host", Con{Wr.Field{"host", Bytes.from_list(Con{32, Bytes.to_list(host)})}, Nil{}}, Nil{}}
  +xf : Eng.Hx = Eng.Hx{Bytes.from_list(Bytes.to_list(meth)), NM(fs, "host"), List.reverse.go(&2, Wr.Field, convs(fs), Con{Wr.Field{"host", Bytes.from_list(Con{32, Bytes.to_list(host)})}, Nil{}}), Nil{}}
  +h0 = Spec.head.new(Bytes.to_list(meth), Bytes.to_list(target), False{})
  +h1 = H1(meth, target, x0)
  +s1 = Spec.snoc(Spec.snoc(List.append(&2, U32, s, RLl(meth, target)), 13), 10)
  +s2 = Spec.snoc(Spec.snoc(List.append(&2, U32, s1, FLl(hf)), 13), 10)
  +r = List.append(&2, Wr.Field, fs, clf)
  Equal.trans(Spec.W, Spec.walk(SERl(X.Msg{meth, target, host, fs, body, framed}), Spec.W{Spec.MReq{Nil{}}, o, s}),
    Spec.walk(List.append(&2, U32, FLSl(Con{hf, r}), tl), WF(h0, o, s1)),
    W.done(meth, target, xf, body, o),
    line.req(meth, target, List.append(&2, U32, FLSl(Con{hf, r}), tl), o, s, hm, ht, nm, nt),
    Equal.trans(Spec.W, Spec.walk(List.append(&2, U32, FLSl(Con{hf, r}), tl), WF(h0, o, s1)),
      Spec.walk(List.append(&2, U32, FLl(hf), Con{13, Con{10, List.append(&2, U32, FLSl(r), tl)}}), WF(h0, o, s1)),
      W.done(meth, target, xf, body, o),
      Equal.cong(List<&2, U32>, Spec.W, xs => Spec.walk(xs, WF(h0, o, s1)),
        List.append(&2, U32, List.append(&2, U32, FLl(hf), Con{13, Con{10, FLSl(r)}}), tl),
        List.append(&2, U32, FLl(hf), Con{13, Con{10, List.append(&2, U32, FLSl(r), tl)}}),
        app.assoc(U32, FLl(hf), Con{13, Con{10, FLSl(r)}}, tl)),
      Equal.trans(Spec.W,
        Spec.walk(List.append(&2, U32, FLl(hf), Con{13, Con{10, List.append(&2, U32, FLSl(r), tl)}}), WF(h0, o, s1)),
        Spec.walk(List.append(&2, U32, FLSl(r), tl), WF(h1, o, s2)),
        W.done(meth, target, xf, body, o),
        line.field(hf, List.append(&2, U32, FLSl(r), tl), h0, h1, o, s1, Spec.VHost{"host", Con{32, Bytes.to_list(host)}},
          pl.host(host, hh), view.host(host, hh), {==}),
        Equal.trans(Spec.W, Spec.walk(List.append(&2, U32, FLSl(r), tl), WF(h1, o, s2)),
          Spec.walk(List.append(&2, U32, FLSl(fs), List.append(&2, U32, FLSl(clf), tl)), WF(h1, o, s2)),
          W.done(meth, target, xf, body, o),
          Equal.cong(List<&2, U32>, Spec.W, xs => Spec.walk(xs, WF(h1, o, s2)),
            List.append(&2, U32, FLSl(r), tl), List.append(&2, U32, FLSl(fs), List.append(&2, U32, FLSl(clf), tl)),
            Equal.trans(List<&2, U32>, List.append(&2, U32, FLSl(r), tl),
              List.append(&2, U32, List.append(&2, U32, FLSl(fs), FLSl(clf)), tl),
              List.append(&2, U32, FLSl(fs), List.append(&2, U32, FLSl(clf), tl)),
              Equal.cong(List<&2, U32>, List<&2, U32>, xs => List.append(&2, U32, xs, tl), FLSl(r),
                List.append(&2, U32, FLSl(fs), FLSl(clf)), fls.app(fs, clf)),
              app.assoc(U32, FLSl(fs), FLSl(clf), tl))),
          Equal.trans(Spec.W, Spec.walk(List.append(&2, U32, FLSl(fs), List.append(&2, U32, FLSl(clf), tl)), WF(h1, o, s2)),
            Spec.walk(List.append(&2, U32, FLSl(clf), tl), WF(HF(fs, h1), o, SF(fs, s2))),
            W.done(meth, target, xf, body, o),
            fields.walk(fs, List.append(&2, U32, FLSl(clf), tl), h1, o, s2, hfs),
            %Equal.sym(Spec.Head, HF(fs, h1), H1(meth, target, xf),
              hf.h1(fs, meth, target, Bytes.from_list(Bytes.to_list(meth)), "host", Con{Wr.Field{"host", Bytes.from_list(Con{32, Bytes.to_list(host)})}, Nil{}}, Nil{})) :
              {Spec.walk(List.append(&2, U32, FLSl(clf), tl), WF(_, o, SF(fs, s2))) == W.done(meth, target, xf, body, o) : Spec.W}
            mw.len(X.clen.on(framed, body), meth, target, xf, body, o, SF(fs, s2), hl))))))

def msg.walk(m: X.Msg, v: {X.valid(m) == True{} : Bool}, +o: List<&2, Eng.Req>, +s: List<&2, U32>) ->
  {Spec.walk(SERl(m), Spec.W{Spec.MReq{Nil{}}, o, s}) == Spec.W{Spec.MReq{Nil{}}, Con{Laws.spec.req(m), o}, Nil{}} : Spec.W}:
  match m:
    case X.Msg{+meth, +target, +host, +fs, +body, +framed}:
      +xf : Eng.Hx = Eng.Hx{Bytes.from_list(Bytes.to_list(meth)), NM(fs, "host"), List.reverse.go(&2, Wr.Field, convs(fs), Con{Wr.Field{"host", Bytes.from_list(Con{32, Bytes.to_list(host)})}, Nil{}}), Nil{}}
      Equal.trans(Spec.W, Spec.walk(SERl(X.Msg{meth, target, host, fs, body, framed}), Spec.W{Spec.MReq{Nil{}}, o, s}),
        W.done(meth, target, xf, body, o),
        Spec.W{Spec.MReq{Nil{}}, Con{Laws.spec.req(X.Msg{meth, target, host, fs, body, framed}), o}, Nil{}},
        mw.at(meth, target, host, fs, body, framed, o, s,
          split7(X.full(meth), X.ok.all(Spec.TMeth{}, meth), X.full(target), X.ok.all(Spec.TTarget{}, target),
            X.ok.all(Spec.TVal{}, host), X.ok.fields(fs), X.ok.len.on(X.clen.on(framed, body), body), v)),
        Equal.cong(Eng.Hd, Spec.W,
          d => Spec.W{Spec.MReq{Nil{}}, Con{Eng.Req{Spec.method(meth), target, body, False{}, False{}, "", d}, o}, Nil{}},
          Spec.hd(xf, False{}), Eng.Hd{meth, False{}, Con{Wr.Field{"host", Bytes.append(" ", host)}, Laws.sent(fs)}, Nil{}},
          hd.sent(meth, host, fs, NM(fs, "host"))))

# What goes upstream passed the check
# -----------------------------------

def OK(mm: Maybe<&2, X.Msg>) -> Type:
  match mm:
    case Some{x}:
      {X.valid(x) == True{} : Bool}
    case None{}:
      Unit

def pick.ok(b: Bool, +m: X.Msg, e: {X.valid(m) == b : Bool}) -> OK(Bool.pick(Maybe<&2, X.Msg>, b, Some{m}, None{})):
  match b:
    case True{}:
      e
    case False{}:
      Unit{}

def fwd.ok(+w: X.Fwd, t: Eng.Req) -> OK(X.fwd(w, t)):
  match t:
    case Eng.Req{meth, +path, +body, close, ws, key, +hd}:
      pick.ok(X.valid(X.msg.of(w, hd, path, body)), X.msg.of(w, hd, path, body), {==})

# The whole stream upstream, read back
# ------------------------------------

def WR(+o: List<&2, Eng.Req>) -> Spec.W:
  Spec.W{Spec.MReq{Nil{}}, o, Nil{}}

def ns.at(mm: Maybe<&2, X.Msg>, ok: OK(mm), +rest: Bytes(), +rq: List<&2, X.Msg>, +o: List<&2, Eng.Req>,
  ih: @+o2: List<&2, Eng.Req> -> {Spec.walk(Bytes.to_list(rest), WR(o2)) ==
    WR(List.reverse.go(&2, Eng.Req, Laws.spec.reqs(rq), o2)) : Spec.W}) ->
  {Spec.walk(Bytes.to_list(X.wire.at(mm, rest)), WR(o)) ==
    WR(List.reverse.go(&2, Eng.Req, Laws.spec.reqs(Laws.fwd.msgs.at(mm, rq)), o)) : Spec.W}:
  match mm:
    case None{}:
      {==}
    case Some{+x}:
      Equal.trans(Spec.W, Spec.walk(Bytes.to_list(Bytes.append(X.ser(x), rest)), WR(o)),
        Spec.walk(List.append(&2, U32, SERl(x), Bytes.to_list(rest)), WR(o)),
        WR(List.reverse.go(&2, Eng.Req, Laws.spec.reqs(rq), Con{Laws.spec.req(x), o})),
        Equal.cong(List<&2, U32>, Spec.W, xs => Spec.walk(xs, WR(o)), Bytes.to_list(Bytes.append(X.ser(x), rest)),
          List.append(&2, U32, SERl(x), Bytes.to_list(rest)),
          Equal.trans(List<&2, U32>, Bytes.to_list(Bytes.append(X.ser(x), rest)),
            List.append(&2, U32, Bytes.to_list(X.ser(x)), Bytes.to_list(rest)),
            List.append(&2, U32, SERl(x), Bytes.to_list(rest)),
            tl.app(X.ser(x), rest),
            Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.append(&2, U32, ys, Bytes.to_list(rest)),
              Bytes.to_list(X.ser(x)), SERl(x), ser.list(x)))),
        Equal.trans(Spec.W, Spec.walk(List.append(&2, U32, SERl(x), Bytes.to_list(rest)), WR(o)),
          Spec.walk(Bytes.to_list(rest), Spec.walk(SERl(x), WR(o))),
          WR(List.reverse.go(&2, Eng.Req, Laws.spec.reqs(rq), Con{Laws.spec.req(x), o})),
          walk.app(SERl(x), Bytes.to_list(rest), WR(o)),
          Equal.trans(Spec.W, Spec.walk(Bytes.to_list(rest), Spec.walk(SERl(x), WR(o))),
            Spec.walk(Bytes.to_list(rest), WR(Con{Laws.spec.req(x), o})),
            WR(List.reverse.go(&2, Eng.Req, Laws.spec.reqs(rq), Con{Laws.spec.req(x), o})),
            Equal.cong(Spec.W, Spec.W, u => Spec.walk(Bytes.to_list(rest), u), Spec.walk(SERl(x), WR(o)),
              WR(Con{Laws.spec.req(x), o}), msg.walk(x, ok, o, Nil{})),
            ih(Con{Laws.spec.req(x), o}))))

def ns.go(+w: X.Fwd, ts: List<&2, Eng.Req>, +o: List<&2, Eng.Req>) ->
  {Spec.walk(Bytes.to_list(X.wire(w, ts)), WR(o)) ==
    WR(List.reverse.go(&2, Eng.Req, Laws.spec.reqs(Laws.fwd.msgs(w, ts)), o)) : Spec.W}:
  match ts:
    case Nil{}:
      {==}
    case Con{+t, +r}:
      ns.at(X.fwd(w, t), fwd.ok(w, t), X.wire(w, r), Laws.fwd.msgs(w, r), o, o2 => ns.go(w, r, o2))

def Laws.no_smuggle(w, ts):
  +xs = Laws.spec.reqs(Laws.fwd.msgs(w, ts))
  Equal.trans(Spec.Frames, Spec.finish(Spec.walk(Bytes.to_list(X.wire(w, ts)), WR(Nil{}))),
    Spec.finish(WR(List.reverse(&2, Eng.Req, xs))),
    Spec.Frames{xs, Spec.Open{Nil{}}},
    Equal.cong(Spec.W, Spec.Frames, u => Spec.finish(u), Spec.walk(Bytes.to_list(X.wire(w, ts)), WR(Nil{})),
      WR(List.reverse(&2, Eng.Req, xs)), ns.go(w, ts, Nil{})),
    Equal.cong(List<&2, Eng.Req>, Spec.Frames, ys => Spec.Frames{ys, Spec.Open{Nil{}}},
      List.reverse(&2, Eng.Req, List.reverse(&2, Eng.Req, xs)), xs, rev.rev(Eng.Req, xs)))

# The response read back
# ======================
#
# rsp_reframed: what the proxy sends a client, read by wire/http1's
# spec.bend, is one final response -- the upstream's status and body,
# the connection's fate the proxy chose -- and nothing after it. As for
# a request, the proof walks the spec over the bytes the proxy writes:
# the status line, the fields that change nothing, the length, the
# Connection, the blank line, the body.

# U32 equality is equality
def beq(ab: Bool, bb: Bool, h: {Cmp.is_eq(Bool.cmp(ab, bb)) == True{} : Bool}) -> {ab == bb : Bool}:
  match ab bb:
    case True{} True{}:
      {==}
    case False{} False{}:
      {==}
    case True{} False{}:
      no({True{} == False{} : Bool}, h)
    case False{} True{}:
      no({False{} == True{} : Bool}, h)

def fin.eq(+ab: Bool, +bb: Bool, t: Cmp, h: {Cmp.is_eq(Word.cmp.fin(ab, bb, t)) == True{} : Bool}) ->
  {Cmp.is_eq(t) == True{} : Bool} & {ab == bb : Bool}:
  match t:
    case LT{}:
      no({Cmp.is_eq(LT{}) == True{} : Bool} & {ab == bb : Bool}, h)
    case GT{}:
      no({Cmp.is_eq(GT{}) == True{} : Bool} & {ab == bb : Bool}, h)
    case EQ{}:
      ({==}, beq(ab, bb, h))

def word.at(p: Nat, +ab: Bool, +at: Word(p), +bb: Bool, +bt: Word(p),
  hh: {Cmp.is_eq(Word.cmp(p, at, bt)) == True{} : Bool} & {ab == bb : Bool},
  ih: {Cmp.is_eq(Word.cmp(p, at, bt)) == True{} : Bool} -> {at == bt : Word(p)}) ->
  {WCon{ab, at} == WCon{bb, bt} : Word(1n+p)}:
  (e1, e2) = hh
  %e2 : {WCon{ab, at} == WCon{_, bt} : Word(1n+p)}
  Equal.cong(Word(p), Word(1n+p), w => WCon{ab, w}, at, bt, ih(e1))

def word.eq(n: Nat, a: Word(n), b: Word(n), h: {Cmp.is_eq(Word.cmp(n, a, b)) == True{} : Bool}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+(+p):
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          word.at(p, ab, at, bb, bt, fin.eq(ab, bb, Word.cmp(p, at, bt), h), e => word.eq(p, at, bt, e))

def u32.eq(a: U32, b: U32, h: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  match a b:
    case U32{x} U32{y}:
      Equal.cong(Word(32n), U32, w => U32{w}, x, y, word.eq(32n, x, y, h))

def not.true(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      no({True{} == False{} : Bool}, h)
    case False{}:
      {==}

# the proxy's own 502, read back
def r502(head: Bool, +closing: Bool, +v10: Bool, +code: U32, +body: Bytes()) ->
  {RS.response(X.rask(head), Bytes.to_list(X.reply(None{}, head, closing, v10))) ==
    Laws.rlook(None{}, head, code, body, closing) : R.Look}:
  match head:
    case True{}:
      {==}
    case False{}:
      {==}

# no token of the response's lines holds a CR or an LF
def rncl(k: R.Cls) -> Bool:
  match k:
    case R.KCr{}:
      False{}
    case R.KLf{}:
      False{}
    case _:
      True{}

def RPL(xs: List<&2, U32>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{x, t}:
      {rncl(R.cls(x)) == True{} : Bool} & RPL(t)

def RAA(t: RS.Tok, xs: List<&2, U32>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{x, r}:
      {RS.allows(t, R.cls(x)) == True{} : Bool} & RAA(t, r)

def rallows.ncl(t: RS.Tok, k: R.Cls, h: {RS.allows(t, k) == True{} : Bool}) -> {rncl(k) == True{} : Bool}:
  match t k:
    case RS.TVer{} R.KCr{}:
      no({rncl(R.KCr{}) == True{} : Bool}, h)
    case RS.TVer{} R.KLf{}:
      no({rncl(R.KLf{}) == True{} : Bool}, h)
    case RS.TDig{} R.KCr{}:
      no({rncl(R.KCr{}) == True{} : Bool}, h)
    case RS.TDig{} R.KLf{}:
      no({rncl(R.KLf{}) == True{} : Bool}, h)
    case RS.TName{} R.KCr{}:
      no({rncl(R.KCr{}) == True{} : Bool}, h)
    case RS.TName{} R.KLf{}:
      no({rncl(R.KLf{}) == True{} : Bool}, h)
    case RS.TOws{} R.KCr{}:
      no({rncl(R.KCr{}) == True{} : Bool}, h)
    case RS.TOws{} R.KLf{}:
      no({rncl(R.KLf{}) == True{} : Bool}, h)
    case RS.TVal{} R.KCr{}:
      no({rncl(R.KCr{}) == True{} : Bool}, h)
    case RS.TVal{} R.KLf{}:
      no({rncl(R.KLf{}) == True{} : Bool}, h)
    case _ R.KSp{}:
      {==}
    case _ R.KHt{}:
      {==}
    case _ R.KCo{}:
      {==}
    case _ R.KCm{}:
      {==}
    case _ R.KDg{}:
      {==}
    case _ R.KTk{}:
      {==}
    case _ R.KVc{}:
      {==}
    case _ R.KCt{}:
      {==}

def raa.pl(+t: RS.Tok, xs: List<&2, U32>, h: RAA(t, xs)) -> RPL(xs):
  match xs:
    case Nil{}:
      Unit{}
    case Con{+x, r}:
      (h1, h2) = h
      (rallows.ncl(t, R.cls(x), h1), raa.pl(t, r, h2))

def rpl.app(a: List<&2, U32>, -b: List<&2, U32>, pa: RPL(a), pb: RPL(b)) -> RPL(List.append(&2, U32, a, b)):
  match a:
    case Nil{}:
      pb
    case Con{x, t}:
      (h1, h2) = pa
      (h1, rpl.app(t, b, h2, pb))

def raa.each.at(+t: RS.Tok, +c: U32, -r: Bytes(),
  h: {RS.allows(t, R.cls(c)) == True{} : Bool} & {X.rok.each(t, r) == True{} : Bool},
  ih: {X.rok.each(t, r) == True{} : Bool} -> RAA(t, Bytes.to_list(r))) ->
  RAA(t, Con{c, Bytes.to_list(r)}):
  (h1, h2) = h
  (h1, ih(h2))

def raa.each(+t: RS.Tok, s: Bytes(), h: {X.rok.each(t, s) == True{} : Bool}) -> RAA(t, Bytes.to_list(s)):
  match s:
    case SNil{}:
      Unit{}
    case SCon{Chr{+c}, r}:
      raa.each.at(t, c, r, and.split(RS.allows(t, R.cls(c)), X.rok.each(t, r), h), h2 => raa.each(t, r, h2))

# the bytes a range covers are ones the token holds
def r.val.sym(co: Bool, cm: Bool, tk: Bool) ->
  {RS.allows(RS.TVal{}, R.cls.sym(co, cm, tk)) == True{} : Bool}:
  match co cm tk:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def r.val.vis(+c: U32, al: Bool, dg: Bool) ->
  {RS.allows(RS.TVal{}, R.cls.vis(c, al, dg)) == True{} : Bool}:
  match al dg:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      r.val.sym(U32.is_eq(c, 58), U32.is_eq(c, 44), R.tsym(c))

def r.val.go(+c: U32, x: Bool, y: Bool) ->
  {Bool.and(Bool.not(x), Bool.not(y)) == True{} : Bool} ->
  {RS.allows(RS.TVal{}, R.cls.go(c, x, y)) == True{} : Bool}:
  match x y:
    case True{} True{}:
      e => no({RS.allows(RS.TVal{}, R.cls.go(c, True{}, True{})) == True{} : Bool}, e)
    case True{} False{}:
      e => no({RS.allows(RS.TVal{}, R.cls.go(c, True{}, False{})) == True{} : Bool}, e)
    case False{} True{}:
      e => no({RS.allows(RS.TVal{}, R.cls.go(c, False{}, True{})) == True{} : Bool}, e)
    case False{} False{}:
      e => r.val.vis(c, R.alpha(c), R.digit(c))

def r.val.sp(ht: Bool, cr: Bool, lf: Bool) ->
  {RS.allows(RS.TVal{}, R.cls.low(True{}, ht, cr, lf)) == True{} : Bool}:
  match ht cr lf:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def r.val.in.at(+c: U32, x: Bool, +e: {Bytes.span.in(c, 32, 127) == True{} : Bool}) ->
  {U32.is_lt(c, 33) == x : Bool} ->
  {RS.allows(RS.TVal{}, R.cls.go(c, x, U32.is_le(127, c))) == True{} : Bool}:
  match x:
    case True{}:
      xe =>
        %Equal.sym(Bool, U32.is_eq(c, 32), True{},
          U32.eq_of_lt_succ(c, 32, 33,
            Bool.and_l(Bool.not(U32.is_lt(c, 32)), Bool.not(U32.is_le(127, c)), e), xe, {==})) :
          {RS.allows(RS.TVal{}, R.cls.low(_, U32.is_eq(c, 9), U32.is_eq(c, 13), U32.is_eq(c, 10))) ==
            True{} : Bool}
        r.val.sp(U32.is_eq(c, 9), U32.is_eq(c, 13), U32.is_eq(c, 10))
    case False{}:
      xe => r.val.go(c, False{}, U32.is_le(127, c))(
        Bool.and_r(Bool.not(U32.is_lt(c, 32)), Bool.not(U32.is_le(127, c)), e))

def r.val.in(+c: U32, +e: {Bytes.span.in(c, 32, 127) == True{} : Bool}) ->
  {RS.allows(RS.TVal{}, R.cls(c)) == True{} : Bool}:
  r.val.in.at(c, U32.is_lt(c, 33), e)({==})

# a name's small letters: a letter, a token byte
def r.nm.tk(+c: U32, dg: Bool) ->
  {RS.allows(RS.TName{}, R.cls.vis(c, True{}, dg)) == True{} : Bool}:
  match dg:
    case True{}:
      {==}
    case False{}:
      {==}

def r.nm.alpha(+c: U32, +e: {Bytes.span.in(c, 97, 123) == True{} : Bool}) ->
  {R.alpha(c) == True{} : Bool}:
  %Equal.sym(Bool, U32.is_le(97, c), True{}, Bytes.span.in_lo(c, 97, 123, e)) :
    {Bool.or(Bool.and(U32.is_le(65, c), U32.is_le(c, 90)), Bool.and(_, U32.is_le(c, 122))) ==
      True{} : Bool}
  %Equal.sym(Bool, U32.is_le(c, 122), True{},
    Equal.trans(Bool, U32.is_le(c, 122), U32.is_lt(c, 123), True{},
      Equal.sym(Bool, U32.is_lt(c, 123), U32.is_le(c, 122), U32.lt_succ(c, 122, 123, {==})),
      Bytes.span.in_hi(c, 97, 123, e))) :
    {Bool.or(Bool.and(U32.is_le(65, c), U32.is_le(c, 90)), Bool.and(True{}, _)) == True{} : Bool}
  Bool.or_true(Bool.and(U32.is_le(65, c), U32.is_le(c, 90)))

def r.nm.in(+c: U32, +e: {Bytes.span.in(c, 97, 123) == True{} : Bool}) ->
  {RS.allows(RS.TName{}, R.cls(c)) == True{} : Bool}:
  +w = Bytes.span.in_widen(c, 97, 123, 33, 127, e, {==}, {==})
  %Equal.sym(Bool, U32.is_lt(c, 33), False{},
    Bool.not_true(U32.is_lt(c, 33), Bool.and_l(Bool.not(U32.is_lt(c, 33)), Bool.not(U32.is_le(127, c)), w))) :
    {RS.allows(RS.TName{}, R.cls.go(c, _, U32.is_le(127, c))) == True{} : Bool}
  %Equal.sym(Bool, U32.is_le(127, c), False{},
    Bool.not_true(U32.is_le(127, c), Bool.and_r(Bool.not(U32.is_lt(c, 33)), Bool.not(U32.is_le(127, c)), w))) :
    {RS.allows(RS.TName{}, R.cls.go(c, False{}, _)) == True{} : Bool}
  %Equal.sym(Bool, R.alpha(c), True{}, r.nm.alpha(c, e)) :
    {RS.allows(RS.TName{}, R.cls.vis(c, _, R.digit(c))) == True{} : Bool}
  r.nm.tk(c, R.digit(c))

# a string all in a range the token holds holds only bytes it holds
def raa.len1(-x: Nat, +r: Bytes(), e: {Nat.is_eq(x, String.length.go(r, 1n)) == True{} : Bool}) ->
  {Nat.is_eq(x, 1n+String.length.go(r, 0n)) == True{} : Bool}:
  %len_shift(r) : {Nat.is_eq(x, _) == True{} : Bool}
  e

def raa.go.at(+t: RS.Tok, +lo: U32, +hi: U32, +c: U32, +r: Bytes(), b: Bool,
  inr: {Bytes.span.in(c, lo, hi) == True{} : Bool} -> {RS.allows(t, R.cls(c)) == True{} : Bool},
  ih: {Nat.is_eq(Bytes.span.go(r, lo, hi), String.length.go(r, 0n)) == True{} : Bool} -> RAA(t, Bytes.to_list(r)),
  e: {Nat.is_eq(Bytes.span.at(b, r, lo, hi), 1n+String.length.go(r, 0n)) == True{} : Bool}) ->
  {Bytes.span.in(c, lo, hi) == b : Bool} -> RAA(t, Con{c, Bytes.to_list(r)}):
  match b:
    case True{}:
      eb => (inr(eb), ih(e))
    case False{}:
      eb => no(RAA(t, Con{c, Bytes.to_list(r)}), e)

def raa.go(~t: RS.Tok, ~lo: U32, ~hi: U32,
  ~inr: @+c: U32 -> {Bytes.span.in(c, lo, hi) == True{} : Bool} -> {RS.allows(t, R.cls(c)) == True{} : Bool}, s: Bytes(),
  e: {Nat.is_eq(Bytes.span.go(s, lo, hi), String.length.go(s, 0n)) == True{} : Bool}) -> RAA(t, Bytes.to_list(s)):
  match s:
    case SNil{}:
      Unit{}
    case SCon{Chr{+c}, +r}:
      raa.go.at(t, lo, hi, c, r, Bytes.span.in(c, lo, hi), inr(c), h2 => raa.go(~t, ~lo, ~hi, ~inr, r, h2),
        raa.len1(Bytes.span.at(Bytes.span.in(c, lo, hi), r, lo, hi), r, e))({==})

def raa.fast(t: RS.Tok, +s: Bytes(), e: {X.rok.fast(t, s) == True{} : Bool}) -> RAA(t, Bytes.to_list(s)):
  match t:
    case RS.TVer{}:
      no(RAA(RS.TVer{}, Bytes.to_list(s)), e)
    case RS.TDig{}:
      no(RAA(RS.TDig{}, Bytes.to_list(s)), e)
    case RS.TName{}:
      raa.go(~RS.TName{}, ~97, ~123, ~(c => h => r.nm.in(c, h)), s,
        %drop0(s) : {Nat.is_eq(Bytes.span.go(_, 97, 123), String.length.go(s, 0n)) == True{} : Bool}
        e)
    case RS.TOws{}:
      no(RAA(RS.TOws{}, Bytes.to_list(s)), e)
    case RS.TVal{}:
      raa.go(~RS.TVal{}, ~32, ~127, ~(c => h => r.val.in(c, h)), s,
        %drop0(s) : {Nat.is_eq(Bytes.span.go(_, 32, 127), String.length.go(s, 0n)) == True{} : Bool}
        e)

def raa.of.at(fast: Bool, +t: RS.Tok, +s: Bytes(), ef: {X.rok.fast(t, s) == fast : Bool},
  h: {X.rok.all.at(fast, t, s) == True{} : Bool}) -> RAA(t, Bytes.to_list(s)):
  match fast:
    case True{}:
      raa.fast(t, s, ef)
    case False{}:
      raa.each(t, s, h)

def raa.of(+t: RS.Tok, +s: Bytes(), h: {X.rok.all(t, s) == True{} : Bool}) -> RAA(t, Bytes.to_list(s)):
  raa.of.at(X.rok.fast(t, s), t, s, {==}, h)

def rspan.to(+t: RS.Tok, xs: List<&2, U32>, +c: U32, +rest: List<&2, U32>, h: RAA(t, xs),
  hc: {RS.allows(t, R.cls(c)) == False{} : Bool}) ->
  {RS.span(t, List.append(&2, U32, xs, Con{c, rest})) == RS.Span{xs, RS.SAt{R.cls(c), c, rest}} : RS.Span}:
  match xs:
    case Nil{}:
      %Equal.sym(Bool, RS.allows(t, R.cls(c)), False{}, hc) :
        {RS.span.pick(_, R.cls(c), c, rest, RS.span(t, rest)) == RS.Span{Nil{}, RS.SAt{R.cls(c), c, rest}} : RS.Span}
      {==}
    case Con{+x, +r}:
      (h1, h2) = h
      %Equal.sym(Bool, RS.allows(t, R.cls(x)), True{}, h1) :
        {RS.span.pick(_, R.cls(x), x, List.append(&2, U32, r, Con{c, rest}),
          RS.span(t, List.append(&2, U32, r, Con{c, rest}))) ==
          RS.Span{Con{x, r}, RS.SAt{R.cls(c), c, rest}} : RS.Span}
      %Equal.sym(RS.Span, RS.span(t, List.append(&2, U32, r, Con{c, rest})), RS.Span{r, RS.SAt{R.cls(c), c, rest}},
        rspan.to(t, r, c, rest, h2, hc)) : {RS.span.push(x, _) == RS.Span{Con{x, r}, RS.SAt{R.cls(c), c, rest}} : RS.Span}
      {==}

def rspan.all(+t: RS.Tok, xs: List<&2, U32>, h: RAA(t, xs)) -> {RS.span(t, xs) == RS.Span{xs, RS.SEnd{}} : RS.Span}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      (h1, h2) = h
      %Equal.sym(Bool, RS.allows(t, R.cls(x)), True{}, h1) :
        {RS.span.pick(_, R.cls(x), x, r, RS.span(t, r)) == RS.Span{Con{x, r}, RS.SEnd{}} : RS.Span}
      %Equal.sym(RS.Span, RS.span(t, r), RS.Span{r, RS.SEnd{}}, rspan.all(t, r, h2)) :
        {RS.span.push(x, _) == RS.Span{Con{x, r}, RS.SEnd{}} : RS.Span}
      {==}

# a line's byte is gathered
def rline.plain(k: R.Cls, -c: U32, -cur: List<&2, U32>, -cr: RS.Mode, -more: List<&2, U32> -> RS.Mode,
  h: {rncl(k) == True{} : Bool}) -> {RS.line.byte(k, c, cur, cr, more) == more(RS.snoc(cur, c)) : RS.Mode}:
  match k:
    case R.KSp{}:
      {==}
    case R.KHt{}:
      {==}
    case R.KCr{}:
      no({RS.line.byte(R.KCr{}, c, cur, cr, more) == more(RS.snoc(cur, c)) : RS.Mode}, h)
    case R.KLf{}:
      no({RS.line.byte(R.KLf{}, c, cur, cr, more) == more(RS.snoc(cur, c)) : RS.Mode}, h)
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

def rsnoc.app(+a: List<&2, U32>, +x: U32, +t: List<&2, U32>) ->
  {List.append(&2, U32, RS.snoc(a, x), t) == List.append(&2, U32, a, Con{x, t}) : List<&2, U32>}:
  app.assoc(U32, a, Con{x, Nil{}}, t)


def rgather.st(xs: List<&2, U32>, +rest: List<&2, U32>, +cur: List<&2, U32>, +e: R.Ask, +o: List<&2, U32>,
  pl: RPL(xs)) ->
  {RS.walk(e, List.append(&2, U32, xs, rest), RS.W{RS.MStatus{cur}, o}) ==
    RS.walk(e, rest, RS.W{RS.MStatus{List.append(&2, U32, cur, xs)}, o}) : RS.W}:
  match xs:
    case Nil{}:
      Equal.cong(List<&2, U32>, RS.W, l => RS.walk(e, rest, RS.W{RS.MStatus{l}, o}), cur, List.append(&2, U32, cur, Nil{}),
        Equal.sym(List<&2, U32>, List.append(&2, U32, cur, Nil{}), cur, app.nil(U32, cur)))
    case Con{+x, +t}:
      (h1, h2) = pl
      Equal.trans(RS.W, RS.walk(e, List.append(&2, U32, Con{x, t}, rest), RS.W{RS.MStatus{cur}, o}),
        RS.walk(e, List.append(&2, U32, t, rest), RS.W{RS.MStatus{RS.snoc(cur, x)}, o}),
        RS.walk(e, rest, RS.W{RS.MStatus{List.append(&2, U32, cur, Con{x, t})}, o}),
        Equal.cong(RS.Mode, RS.W, m => RS.walk(e, List.append(&2, U32, t, rest), RS.W{m, o}),
          RS.line.byte(R.cls(x), x, cur, RS.status.cr(RS.status.view(cur)), y => RS.MStatus{y}), RS.MStatus{RS.snoc(cur, x)},
          rline.plain(R.cls(x), x, cur, RS.status.cr(RS.status.view(cur)), y => RS.MStatus{y}, h1)),
        Equal.trans(RS.W, RS.walk(e, List.append(&2, U32, t, rest), RS.W{RS.MStatus{RS.snoc(cur, x)}, o}),
          RS.walk(e, rest, RS.W{RS.MStatus{List.append(&2, U32, RS.snoc(cur, x), t)}, o}),
          RS.walk(e, rest, RS.W{RS.MStatus{List.append(&2, U32, cur, Con{x, t})}, o}),
          rgather.st(t, rest, RS.snoc(cur, x), e, o, h2),
          Equal.cong(List<&2, U32>, RS.W, l => RS.walk(e, rest, RS.W{RS.MStatus{l}, o}),
            List.append(&2, U32, RS.snoc(cur, x), t), List.append(&2, U32, cur, Con{x, t}), rsnoc.app(cur, x, t))))

def rgather.fl(xs: List<&2, U32>, +rest: List<&2, U32>, +hd: R.Head, +cur: List<&2, U32>, +e: R.Ask, +o: List<&2, U32>,
  pl: RPL(xs)) ->
  {RS.walk(e, List.append(&2, U32, xs, rest), RS.W{RS.MField{hd, cur}, o}) ==
    RS.walk(e, rest, RS.W{RS.MField{hd, List.append(&2, U32, cur, xs)}, o}) : RS.W}:
  match xs:
    case Nil{}:
      Equal.cong(List<&2, U32>, RS.W, l => RS.walk(e, rest, RS.W{RS.MField{hd, l}, o}), cur, List.append(&2, U32, cur, Nil{}),
        Equal.sym(List<&2, U32>, List.append(&2, U32, cur, Nil{}), cur, app.nil(U32, cur)))
    case Con{+x, +t}:
      (h1, h2) = pl
      Equal.trans(RS.W, RS.walk(e, List.append(&2, U32, Con{x, t}, rest), RS.W{RS.MField{hd, cur}, o}),
        RS.walk(e, List.append(&2, U32, t, rest), RS.W{RS.MField{hd, RS.snoc(cur, x)}, o}),
        RS.walk(e, rest, RS.W{RS.MField{hd, List.append(&2, U32, cur, Con{x, t})}, o}),
        Equal.cong(RS.Mode, RS.W, m => RS.walk(e, List.append(&2, U32, t, rest), RS.W{m, o}),
          RS.line.byte(R.cls(x), x, cur, RS.field.cr(e, hd, RS.field.view(e, cur)), y => RS.MField{hd, y}), RS.MField{hd, RS.snoc(cur, x)},
          rline.plain(R.cls(x), x, cur, RS.field.cr(e, hd, RS.field.view(e, cur)), y => RS.MField{hd, y}, h1)),
        Equal.trans(RS.W, RS.walk(e, List.append(&2, U32, t, rest), RS.W{RS.MField{hd, RS.snoc(cur, x)}, o}),
          RS.walk(e, rest, RS.W{RS.MField{hd, List.append(&2, U32, RS.snoc(cur, x), t)}, o}),
          RS.walk(e, rest, RS.W{RS.MField{hd, List.append(&2, U32, cur, Con{x, t})}, o}),
          rgather.fl(t, rest, hd, RS.snoc(cur, x), e, o, h2),
          Equal.cong(List<&2, U32>, RS.W, l => RS.walk(e, rest, RS.W{RS.MField{hd, l}, o}),
            List.append(&2, U32, RS.snoc(cur, x), t), List.append(&2, U32, cur, Con{x, t}), rsnoc.app(cur, x, t))))

# The status line
# ---------------

def SLl(+cd: Bytes(), +why: Bytes()) -> List<&2, U32>:
  List.append(&2, U32, Bytes.to_list("HTTP/1.1 "), List.append(&2, U32, Bytes.to_list(cd), Con{32, Bytes.to_list(why)}))

def sl.list(+cd: Bytes(), +why: Bytes()) -> {Bytes.to_list(X.sl.ser(cd, why)) == SLl(cd, why) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, Bytes.to_list(X.sl.ser(cd, why)),
    List.append(&2, U32, Bytes.to_list("HTTP/1.1 "), Bytes.to_list(Bytes.append(cd, Bytes.append(" ", why)))),
    SLl(cd, why),
    tl.app("HTTP/1.1 ", Bytes.append(cd, Bytes.append(" ", why))),
    Equal.cong(List<&2, U32>, List<&2, U32>, l => List.append(&2, U32, Bytes.to_list("HTTP/1.1 "), l),
      Bytes.to_list(Bytes.append(cd, Bytes.append(" ", why))),
      List.append(&2, U32, Bytes.to_list(cd), Con{32, Bytes.to_list(why)}),
      tl.app(cd, Bytes.append(" ", why))))

def rpl.st(+cd: Bytes(), +why: Bytes(), +ad: {X.rok.all(RS.TDig{}, cd) == True{} : Bool}, +aw: {X.rok.all(RS.TVal{}, why) == True{} : Bool}) ->
  RPL(SLl(cd, why)):
  rpl.app(Bytes.to_list("HTTP/1.1 "), List.append(&2, U32, Bytes.to_list(cd), Con{32, Bytes.to_list(why)}),
    ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, Unit{}))))))))),
    rpl.app(Bytes.to_list(cd), Con{32, Bytes.to_list(why)}, raa.pl(RS.TDig{}, Bytes.to_list(cd), raa.of(RS.TDig{}, cd, ad)),
      ({==}, raa.pl(RS.TVal{}, Bytes.to_list(why), raa.of(RS.TVal{}, why, aw)))))

# LEMMA: the status line reads as HTTP/1.1, the code, a reason
def rview.st(+cd: Bytes(), +why: Bytes(), +ad: {X.rok.all(RS.TDig{}, cd) == True{} : Bool},
  cw: {RS.code.whole(Bytes.to_list(cd)) == True{} : Bool}, +aw: {X.rok.all(RS.TVal{}, why) == True{} : Bool}) ->
  {RS.status.view(SLl(cd, why)) == RS.VWhy{False{}, RS.num(Bytes.to_list(cd))} : RS.SView}:
  %Equal.sym(RS.Span, RS.span(RS.TDig{}, List.append(&2, U32, Bytes.to_list(cd), Con{32, Bytes.to_list(why)})),
    RS.Span{Bytes.to_list(cd), RS.SAt{R.cls(32), 32, Bytes.to_list(why)}},
    rspan.to(RS.TDig{}, Bytes.to_list(cd), 32, Bytes.to_list(why), raa.of(RS.TDig{}, cd, ad), {==})) :
    {RS.sv.code(False{}, _) == RS.VWhy{False{}, RS.num(Bytes.to_list(cd))} : RS.SView}
  %Equal.sym(Bool, RS.code.whole(Bytes.to_list(cd)), True{}, cw) :
    {RS.sv.code.sp(_, False{}, Bytes.to_list(cd), Bytes.to_list(why)) == RS.VWhy{False{}, RS.num(Bytes.to_list(cd))} : RS.SView}
  %Equal.sym(RS.Span, RS.span(RS.TVal{}, Bytes.to_list(why)), RS.Span{Bytes.to_list(why), RS.SEnd{}},
    rspan.all(RS.TVal{}, Bytes.to_list(why), raa.of(RS.TVal{}, why, aw))) :
    {RS.sv.why(False{}, RS.num(Bytes.to_list(cd)), _) == RS.VWhy{False{}, RS.num(Bytes.to_list(cd))} : RS.SView}
  {==}

# LEMMA: the status line is read, and the fields begin
def rline.st(+cd: Bytes(), +why: Bytes(), +rest: List<&2, U32>, +e: R.Ask, +o: List<&2, U32>,
  +ad: {X.rok.all(RS.TDig{}, cd) == True{} : Bool}, cw: {RS.code.whole(Bytes.to_list(cd)) == True{} : Bool},
  +aw: {X.rok.all(RS.TVal{}, why) == True{} : Bool}) ->
  {RS.walk(e, List.append(&2, U32, SLl(cd, why), Con{13, Con{10, rest}}), RS.W{RS.MStatus{Nil{}}, o}) ==
    RS.walk(e, rest, RS.W{RS.MField{R.head.new(False{}, RS.num(Bytes.to_list(cd))), Nil{}}, o}) : RS.W}:
  Equal.trans(RS.W, RS.walk(e, List.append(&2, U32, SLl(cd, why), Con{13, Con{10, rest}}), RS.W{RS.MStatus{Nil{}}, o}),
    RS.walk(e, Con{13, Con{10, rest}}, RS.W{RS.MStatus{List.append(&2, U32, Nil{}, SLl(cd, why))}, o}),
    RS.walk(e, rest, RS.W{RS.MField{R.head.new(False{}, RS.num(Bytes.to_list(cd))), Nil{}}, o}),
    rgather.st(SLl(cd, why), Con{13, Con{10, rest}}, Nil{}, e, o, rpl.st(cd, why, ad, aw)),
    Equal.cong(RS.SView, RS.W, v => RS.walk(e, rest, RS.next(e, RS.W{RS.status.cr(v), o}, 10)),
      RS.status.view(SLl(cd, why)), RS.VWhy{False{}, RS.num(Bytes.to_list(cd))}, rview.st(cd, why, ad, cw, aw)))

# The field lines
# ---------------

def rother(f: RS.Fld, h: {X.ris.other(f) == True{} : Bool}) -> {f == RS.FOther{} : RS.Fld}:
  match f:
    case RS.FOther{}:
      {==}
    case RS.FCl{}:
      no({RS.FCl{} == RS.FOther{} : RS.Fld}, h)
    case RS.FTe{}:
      no({RS.FTe{} == RS.FOther{} : RS.Fld}, h)
    case RS.FConn{}:
      no({RS.FConn{} == RS.FOther{} : RS.Fld}, h)

# LEMMA: a field the check passed reads as one that changes nothing
def rview.other(+e: R.Ask, n: Bytes(), +v: Bytes(), hn: {X.full(n) == True{} : Bool}, +ht: {X.rok.all(RS.TName{}, n) == True{} : Bool},
  hc: {X.ris.other(RS.field(RS.lows(Bytes.to_list(n)))) == True{} : Bool}, +hv: {X.rok.all(RS.TVal{}, v) == True{} : Bool}) ->
  {RS.field.view(e, FLl(Wr.Field{n, v})) == RS.FVal{RS.VSkip{}} : RS.FLine}:
  match n:
    case SNil{}:
      no({RS.field.view(e, FLl(Wr.Field{SNil{}, v})) == RS.FVal{RS.VSkip{}} : RS.FLine}, hn)
    case SCon{Chr{+c}, +r}:
      %Equal.sym(RS.Span, RS.span(RS.TName{}, List.append(&2, U32, Con{c, Bytes.to_list(r)}, Con{58, Con{32, Bytes.to_list(v)}})),
        RS.Span{Con{c, Bytes.to_list(r)}, RS.SAt{R.cls(58), 58, Con{32, Bytes.to_list(v)}}},
        rspan.to(RS.TName{}, Con{c, Bytes.to_list(r)}, 58, Con{32, Bytes.to_list(v)}, raa.of(RS.TName{}, SCon{Chr{c}, r}, ht), {==})) :
        {RS.field.name(e, _) == RS.FVal{RS.VSkip{}} : RS.FLine}
      %Equal.sym(RS.Fld, RS.field(RS.lows(Con{c, Bytes.to_list(r)})), RS.FOther{},
        rother(RS.field(RS.lows(Con{c, Bytes.to_list(r)})), hc)) :
        {RS.field.of(e, _, Con{32, Bytes.to_list(v)}) == RS.FVal{RS.VSkip{}} : RS.FLine}
      %Equal.sym(RS.Span, RS.span(RS.TVal{}, Bytes.to_list(v)), RS.Span{Bytes.to_list(v), RS.SEnd{}},
        rspan.all(RS.TVal{}, Bytes.to_list(v), raa.of(RS.TVal{}, v, hv))) :
        {RS.skip.view(RS.span.push(32, _)) == RS.FVal{RS.VSkip{}} : RS.FLine}
      {==}

def rpl.fl(+n: Bytes(), +v: Bytes(), +ht: {X.rok.all(RS.TName{}, n) == True{} : Bool}, +hv: {X.rok.all(RS.TVal{}, v) == True{} : Bool}) ->
  RPL(FLl(Wr.Field{n, v})):
  rpl.app(Bytes.to_list(n), Con{58, Con{32, Bytes.to_list(v)}}, raa.pl(RS.TName{}, Bytes.to_list(n), raa.of(RS.TName{}, n, ht)),
    ({==}, ({==}, raa.pl(RS.TVal{}, Bytes.to_list(v), raa.of(RS.TVal{}, v, hv)))))

# LEMMA: a field line is read, what it says taken into the head
def rline.fl(f: Wr.Field, +rest: List<&2, U32>, +h: R.Head, h2: R.Head, +e: R.Ask, +o: List<&2, U32>, val: RS.Val,
  pl: RPL(FLl(f)), hv: {RS.field.view(e, FLl(f)) == RS.FVal{val} : RS.FLine},
  hd: {RS.field.done(e, h, val) == Some{h2} : Maybe<&2, R.Head>}) ->
  {RS.walk(e, List.append(&2, U32, FLl(f), Con{13, Con{10, rest}}), RS.W{RS.MField{h, Nil{}}, o}) ==
    RS.walk(e, rest, RS.W{RS.MField{h2, Nil{}}, o}) : RS.W}:
  Equal.trans(RS.W, RS.walk(e, List.append(&2, U32, FLl(f), Con{13, Con{10, rest}}), RS.W{RS.MField{h, Nil{}}, o}),
    RS.walk(e, Con{13, Con{10, rest}}, RS.W{RS.MField{h, List.append(&2, U32, Nil{}, FLl(f))}, o}),
    RS.walk(e, rest, RS.W{RS.MField{h2, Nil{}}, o}),
    rgather.fl(FLl(f), Con{13, Con{10, rest}}, h, Nil{}, e, o, pl),
    Equal.trans(RS.W, RS.walk(e, rest, RS.next(e, RS.W{RS.field.cr(e, h, RS.field.view(e, FLl(f))), o}, 10)),
      RS.walk(e, rest, RS.next(e, RS.W{RS.field.cr(e, h, RS.FVal{val}), o}, 10)),
      RS.walk(e, rest, RS.W{RS.MField{h2, Nil{}}, o}),
      Equal.cong(RS.FLine, RS.W, x => RS.walk(e, rest, RS.next(e, RS.W{RS.field.cr(e, h, x), o}, 10)),
        RS.field.view(e, FLl(f)), RS.FVal{val}, hv),
      Equal.cong(Maybe<&2, R.Head>, RS.W, m => RS.walk(e, rest, RS.next(e, RS.W{RS.field.next(m), o}, 10)),
        RS.field.done(e, h, val), Some{h2}, hd)))

def rok.field.split(+n: Bytes(), +v: Bytes(), h: {X.rok.field(Wr.Field{n, v}) == True{} : Bool}) ->
  {X.full(n) == True{} : Bool} & {X.rok.all(RS.TName{}, n) == True{} : Bool} &
    {X.ris.other(RS.field(RS.lows(Bytes.to_list(n)))) == True{} : Bool} & {X.rok.all(RS.TVal{}, v) == True{} : Bool}:
  split4(X.full(n), X.rok.all(RS.TName{}, n), X.ris.other(RS.field(RS.lows(Bytes.to_list(n)))), X.rok.all(RS.TVal{}, v), h)

def rpl.fl.at(+n: Bytes(), +v: Bytes(), fk: {X.full(n) == True{} : Bool} & {X.rok.all(RS.TName{}, n) == True{} : Bool} &
    {X.ris.other(RS.field(RS.lows(Bytes.to_list(n)))) == True{} : Bool} & {X.rok.all(RS.TVal{}, v) == True{} : Bool}) -> RPL(FLl(Wr.Field{n, v})):
  (hn, r1) = fk
  (ht, r2) = r1
  (hc, hv) = r2
  rpl.fl(n, v, ht, hv)

def rview.other.at(+e: R.Ask, +n: Bytes(), +v: Bytes(), fk: {X.full(n) == True{} : Bool} & {X.rok.all(RS.TName{}, n) == True{} : Bool} &
    {X.ris.other(RS.field(RS.lows(Bytes.to_list(n)))) == True{} : Bool} & {X.rok.all(RS.TVal{}, v) == True{} : Bool}) ->
  {RS.field.view(e, FLl(Wr.Field{n, v})) == RS.FVal{RS.VSkip{}} : RS.FLine}:
  (hn, r1) = fk
  (ht, r2) = r1
  (hc, hv) = r2
  rview.other(e, n, v, hn, ht, hc, hv)

def rline.other4(+n: Bytes(), +v: Bytes(), +rest: List<&2, U32>, +h: R.Head, +e: R.Ask, +o: List<&2, U32>,
  +hk: {X.rok.field(Wr.Field{n, v}) == True{} : Bool}) ->
  {RS.walk(e, List.append(&2, U32, FLl(Wr.Field{n, v}), Con{13, Con{10, rest}}), RS.W{RS.MField{h, Nil{}}, o}) ==
    RS.walk(e, rest, RS.W{RS.MField{h, Nil{}}, o}) : RS.W}:
  rline.fl(Wr.Field{n, v}, rest, h, h, e, o, RS.VSkip{}, rpl.fl.at(n, v, rok.field.split(n, v, hk)),
    rview.other.at(e, n, v, rok.field.split(n, v, hk)), {==})

def rfields.con(+n: Bytes(), +v: Bytes(), +t: List<&2, Wr.Field>, +rest: List<&2, U32>, +h: R.Head, +e: R.Ask,
  +o: List<&2, U32>, hh: {X.rok.field(Wr.Field{n, v}) == True{} : Bool} & {X.rok.fields(t) == True{} : Bool},
  ih: {X.rok.fields(t) == True{} : Bool} ->
    {RS.walk(e, List.append(&2, U32, FLSl(t), rest), RS.W{RS.MField{h, Nil{}}, o}) ==
      RS.walk(e, rest, RS.W{RS.MField{h, Nil{}}, o}) : RS.W}) ->
  {RS.walk(e, List.append(&2, U32, FLSl(Con{Wr.Field{n, v}, t}), rest), RS.W{RS.MField{h, Nil{}}, o}) ==
    RS.walk(e, rest, RS.W{RS.MField{h, Nil{}}, o}) : RS.W}:
  (h1, h2) = hh
  Equal.trans(RS.W, RS.walk(e, List.append(&2, U32, FLSl(Con{Wr.Field{n, v}, t}), rest), RS.W{RS.MField{h, Nil{}}, o}),
    RS.walk(e, List.append(&2, U32, FLl(Wr.Field{n, v}), Con{13, Con{10, List.append(&2, U32, FLSl(t), rest)}}),
      RS.W{RS.MField{h, Nil{}}, o}),
    RS.walk(e, rest, RS.W{RS.MField{h, Nil{}}, o}),
    Equal.cong(List<&2, U32>, RS.W, l => RS.walk(e, l, RS.W{RS.MField{h, Nil{}}, o}),
      List.append(&2, U32, List.append(&2, U32, FLl(Wr.Field{n, v}), Con{13, Con{10, FLSl(t)}}), rest),
      List.append(&2, U32, FLl(Wr.Field{n, v}), Con{13, Con{10, List.append(&2, U32, FLSl(t), rest)}}),
      app.assoc(U32, FLl(Wr.Field{n, v}), Con{13, Con{10, FLSl(t)}}, rest)),
    Equal.trans(RS.W,
      RS.walk(e, List.append(&2, U32, FLl(Wr.Field{n, v}), Con{13, Con{10, List.append(&2, U32, FLSl(t), rest)}}),
        RS.W{RS.MField{h, Nil{}}, o}),
      RS.walk(e, List.append(&2, U32, FLSl(t), rest), RS.W{RS.MField{h, Nil{}}, o}),
      RS.walk(e, rest, RS.W{RS.MField{h, Nil{}}, o}),
      rline.other4(n, v, List.append(&2, U32, FLSl(t), rest), h, e, o, h1),
      ih(h2)))

# LEMMA: the fields the proxy carries on leave the head as it was
def rfields.walk(fs: List<&2, Wr.Field>, +rest: List<&2, U32>, +h: R.Head, +e: R.Ask, +o: List<&2, U32>,
  hok: {X.rok.fields(fs) == True{} : Bool}) ->
  {RS.walk(e, List.append(&2, U32, FLSl(fs), rest), RS.W{RS.MField{h, Nil{}}, o}) ==
    RS.walk(e, rest, RS.W{RS.MField{h, Nil{}}, o}) : RS.W}:
  match fs:
    case Nil{}:
      {==}
    case Con{f, +t}:
      match f:
        case Wr.Field{+n, +v}:
          rfields.con(n, v, t, rest, h, e, o, and.split(X.rok.field(Wr.Field{n, v}), X.rok.fields(t), hok),
            h2 => rfields.walk(t, rest, h, e, o, h2))

# The body
# --------

# LEMMA: a body of known length is counted off to its last byte, and the
# response is final
def rbody.walk(t: Bytes(), +c: U32, +h: R.Head, +got: List<&2, U32>, +e: R.Ask, +o: List<&2, U32>) ->
  {RS.walk(e, Con{c, Bytes.to_list(t)}, RS.W{RS.MBody{h, Bytes.len(t), got}, o}) ==
    RS.W{RS.MDone{RS.resp(h, List.append(&2, U32, got, Con{c, Bytes.to_list(t)}), False{}), Nil{}}, o} : RS.W}:
  match t:
    case SNil{}:
      {==}
    case SCon{Chr{+c2}, +t2}:
      %Equal.sym(Nat, Bytes.len(SCon{Chr{c2}, t2}), 1n+Bytes.len(t2), Bytes.len.shift(t2, 0n)) :
        {RS.walk(e, Con{c, Con{c2, Bytes.to_list(t2)}}, RS.W{RS.MBody{h, _, got}, o}) ==
          RS.W{RS.MDone{RS.resp(h, List.append(&2, U32, got, Con{c, Con{c2, Bytes.to_list(t2)}}), False{}), Nil{}}, o} : RS.W}
      %rsnoc.app(got, c, Con{c2, Bytes.to_list(t2)}) :
        {RS.walk(e, Con{c2, Bytes.to_list(t2)}, RS.W{RS.MBody{h, Bytes.len(t2), RS.snoc(got, c)}, o}) ==
          RS.W{RS.MDone{RS.resp(h, _, False{}), Nil{}}, o} : RS.W}
      rbody.walk(t2, c2, h, RS.snoc(got, c), e, o)

def rtail.z(z: Bool, +h: R.Head, body: Bytes(), +n: U32, +e: R.Ask, +o: List<&2, U32>,
  hz: {X.same(z, String.is_empty(body)) == True{} : Bool}, hn: {Nat.is_eq(U32.to_nat(n), Bytes.len(body)) == True{} : Bool}) ->
  {RS.walk(e, Bytes.to_list(body), RS.W{RS.head.body(z, h, n), o}) ==
    RS.W{RS.MDone{RS.resp(h, Bytes.to_list(body), False{}), Nil{}}, o} : RS.W}:
  match z body:
    case True{} SNil{}:
      {==}
    case True{} SCon{c, t}:
      no({RS.walk(e, Bytes.to_list(SCon{c, t}), RS.W{RS.head.body(True{}, h, n), o}) ==
        RS.W{RS.MDone{RS.resp(h, Bytes.to_list(SCon{c, t}), False{}), Nil{}}, o} : RS.W}, hz)
    case False{} SNil{}:
      no({RS.walk(e, Nil{}, RS.W{RS.head.body(False{}, h, n), o}) ==
        RS.W{RS.MDone{RS.resp(h, Nil{}, False{}), Nil{}}, o} : RS.W}, hz)
    case False{} SCon{Chr{+c}, +t}:
      %Equal.sym(Nat, U32.to_nat(n), Bytes.len(SCon{Chr{c}, t}), nat.eq(U32.to_nat(n), Bytes.len(SCon{Chr{c}, t}), hn)) :
        {RS.walk(e, Con{c, Bytes.to_list(t)}, RS.W{RS.MBody{h, Nat.sub(_, 1n), Nil{}}, o}) ==
          RS.W{RS.MDone{RS.resp(h, Con{c, Bytes.to_list(t)}, False{}), Nil{}}, o} : RS.W}
      %Equal.sym(Nat, Bytes.len(SCon{Chr{c}, t}), 1n+Bytes.len(t), Bytes.len.shift(t, 0n)) :
        {RS.walk(e, Con{c, Bytes.to_list(t)}, RS.W{RS.MBody{h, Nat.sub(_, 1n), Nil{}}, o}) ==
          RS.W{RS.MDone{RS.resp(h, Con{c, Bytes.to_list(t)}, False{}), Nil{}}, o} : RS.W}
      %Equal.sym(Nat, Nat.sub(Bytes.len(t), 0n), Bytes.len(t), sub0(Bytes.len(t))) :
        {RS.walk(e, Con{c, Bytes.to_list(t)}, RS.W{RS.MBody{h, _, Nil{}}, o}) ==
          RS.W{RS.MDone{RS.resp(h, Con{c, Bytes.to_list(t)}, False{}), Nil{}}, o} : RS.W}
      rbody.walk(t, c, h, Nil{}, e, o)

# The blank line, and the framing
# -------------------------------

# the head the proxy's fields leave: HTTP/1.1, the code, a length or
# none, no coding, closing as the proxy closes
def HC(+code: U32, +l: Maybe<&2, U32>, +closing: Bool, +v10: Bool) -> R.Head:
  R.Head{False{}, code, l, False{}, closing, v10 && Bool.not(closing)}

# LEMMA: with a code of 200 or more, the framing is none (HEAD, 204,
# 304) or the length
def rfr(head: Bool, +code: U32, +l: Maybe<&2, U32>, +cl: Bool, +ka: Bool, hlt: {U32.is_lt(code, 200) == False{} : Bool}) ->
  {RS.framing(X.rask(head), R.Head{False{}, code, l, False{}, cl, ka}) ==
    RS.frame.pick(X.rbodyless(head, code), R.FNone{}, RS.frame.len(l)) : R.Frame}:
  match head:
    case True{}:
      Equal.cong(Bool, R.Frame, b => RS.frame.pick(False{}, R.FBad{}, RS.frame.pick(b && Bool.not(U32.is_eq(code, 101)), R.FNext{},
        RS.frame.pick(True{} || b || U32.is_eq(code, 204) || U32.is_eq(code, 304), R.FNone{},
          RS.frame.pick(False{}, R.FChunked{}, RS.frame.len(l))))), U32.is_lt(code, 200), False{}, hlt)
    case False{}:
      Equal.cong(Bool, R.Frame, b => RS.frame.pick(False{}, R.FBad{}, RS.frame.pick(b && Bool.not(U32.is_eq(code, 101)), R.FNext{},
        RS.frame.pick(False{} || b || U32.is_eq(code, 204) || U32.is_eq(code, 304), R.FNone{},
          RS.frame.pick(False{}, R.FChunked{}, RS.frame.len(l))))), U32.is_lt(code, 200), False{}, hlt)

def rend.none(+head: Bool, +code: U32, +l: Maybe<&2, U32>, +cl: Bool, +ka: Bool,
  hlt: {U32.is_lt(code, 200) == False{} : Bool}, hb: {X.rbodyless(head, code) == True{} : Bool}) ->
  {RS.walk(X.rask(head), Con{13, Con{10, Nil{}}}, RS.W{RS.MField{R.Head{False{}, code, l, False{}, cl, ka}, Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{RS.resp(R.Head{False{}, code, l, False{}, cl, ka}, Nil{}, False{}), Nil{}}, Nil{}} : RS.W}:
  +h : R.Head = R.Head{False{}, code, l, False{}, cl, ka}
  Equal.trans(RS.W, RS.head.at(X.rask(head), RS.framing(X.rask(head), h), h, Nil{}),
    RS.head.at(X.rask(head), RS.frame.pick(X.rbodyless(head, code), R.FNone{}, RS.frame.len(l)), h, Nil{}),
    RS.W{RS.MDone{RS.resp(h, Nil{}, False{}), Nil{}}, Nil{}},
    Equal.cong(R.Frame, RS.W, f => RS.head.at(X.rask(head), f, h, Nil{}), RS.framing(X.rask(head), h),
      RS.frame.pick(X.rbodyless(head, code), R.FNone{}, RS.frame.len(l)), rfr(head, code, l, cl, ka, hlt)),
    Equal.cong(Bool, RS.W, b => RS.head.at(X.rask(head), RS.frame.pick(b, R.FNone{}, RS.frame.len(l)), h, Nil{}),
      X.rbodyless(head, code), True{}, hb))

def rend.len(+head: Bool, +code: U32, +n: U32, +cl: Bool, +ka: Bool, +body: Bytes(),
  hlt: {U32.is_lt(code, 200) == False{} : Bool}, hb: {X.rbodyless(head, code) == False{} : Bool},
  hz: {X.same(U32.is_zero(n), String.is_empty(body)) == True{} : Bool},
  hn: {Nat.is_eq(U32.to_nat(n), Bytes.len(body)) == True{} : Bool}) ->
  {RS.walk(X.rask(head), Con{13, Con{10, Bytes.to_list(body)}},
    RS.W{RS.MField{R.Head{False{}, code, Some{n}, False{}, cl, ka}, Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{RS.resp(R.Head{False{}, code, Some{n}, False{}, cl, ka}, Bytes.to_list(body), False{}), Nil{}}, Nil{}} : RS.W}:
  +h : R.Head = R.Head{False{}, code, Some{n}, False{}, cl, ka}
  Equal.trans(RS.W, RS.walk(X.rask(head), Bytes.to_list(body), RS.head.at(X.rask(head), RS.framing(X.rask(head), h), h, Nil{})),
    RS.walk(X.rask(head), Bytes.to_list(body),
      RS.head.at(X.rask(head), RS.frame.pick(X.rbodyless(head, code), R.FNone{}, R.FLen{n}), h, Nil{})),
    RS.W{RS.MDone{RS.resp(h, Bytes.to_list(body), False{}), Nil{}}, Nil{}},
    Equal.cong(R.Frame, RS.W, f => RS.walk(X.rask(head), Bytes.to_list(body), RS.head.at(X.rask(head), f, h, Nil{})),
      RS.framing(X.rask(head), h), RS.frame.pick(X.rbodyless(head, code), R.FNone{}, R.FLen{n}),
      rfr(head, code, Some{n}, cl, ka, hlt)),
    Equal.trans(RS.W, RS.walk(X.rask(head), Bytes.to_list(body),
        RS.head.at(X.rask(head), RS.frame.pick(X.rbodyless(head, code), R.FNone{}, R.FLen{n}), h, Nil{})),
      RS.walk(X.rask(head), Bytes.to_list(body), RS.head.at(X.rask(head), R.FLen{n}, h, Nil{})),
      RS.W{RS.MDone{RS.resp(h, Bytes.to_list(body), False{}), Nil{}}, Nil{}},
      Equal.cong(Bool, RS.W, b => RS.walk(X.rask(head), Bytes.to_list(body),
          RS.head.at(X.rask(head), RS.frame.pick(b, R.FNone{}, R.FLen{n}), h, Nil{})),
        X.rbodyless(head, code), False{}, hb),
      rtail.z(U32.is_zero(n), h, body, n, X.rask(head), Nil{}, hz, hn)))

# the response the client reads: the code, HTTP/1.1, closing as the
# proxy closes
def rresp.eq(+code: U32, +l: Maybe<&2, U32>, closing: Bool, +v10: Bool, +got: List<&2, U32>,
  h101: {U32.is_eq(code, 101) == False{} : Bool}) ->
  {RS.resp(HC(code, l, closing, v10), got, False{}) == R.Resp{code, False{}, closing, Bytes.from_list(got)} : R.Resp}:
  match closing:
    case True{}:
      {==}
    case False{}:
      Equal.cong(Bool, R.Resp, b => R.Resp{code, False{}, False{} || (False{} && Bool.not(v10 && Bool.not(False{}))) || b || False{},
        Bytes.from_list(got)}, U32.is_eq(code, 101), False{}, h101)

def rafter.none(+head: Bool, +code: U32, +l: Maybe<&2, U32>, +closing: Bool, +v10: Bool,
  hlt: {U32.is_lt(code, 200) == False{} : Bool}, h101: {U32.is_eq(code, 101) == False{} : Bool},
  hb: {X.rbodyless(head, code) == True{} : Bool}) ->
  {RS.walk(X.rask(head), Con{13, Con{10, Nil{}}}, RS.W{RS.MField{HC(code, l, closing, v10), Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, ""}, Nil{}}, Nil{}} : RS.W}:
  Equal.trans(RS.W, RS.walk(X.rask(head), Con{13, Con{10, Nil{}}}, RS.W{RS.MField{HC(code, l, closing, v10), Nil{}}, Nil{}}),
    RS.W{RS.MDone{RS.resp(HC(code, l, closing, v10), Nil{}, False{}), Nil{}}, Nil{}},
    RS.W{RS.MDone{R.Resp{code, False{}, closing, ""}, Nil{}}, Nil{}},
    rend.none(head, code, l, closing, v10 && Bool.not(closing), hlt, hb),
    Equal.cong(R.Resp, RS.W, r => RS.W{RS.MDone{r, Nil{}}, Nil{}}, RS.resp(HC(code, l, closing, v10), Nil{}, False{}),
      R.Resp{code, False{}, closing, ""}, rresp.eq(code, l, closing, v10, Nil{}, h101)))

def rafter.len(+head: Bool, +code: U32, +n: U32, +closing: Bool, +v10: Bool, +body: Bytes(),
  hlt: {U32.is_lt(code, 200) == False{} : Bool}, h101: {U32.is_eq(code, 101) == False{} : Bool},
  hb: {X.rbodyless(head, code) == False{} : Bool},
  hz: {X.same(U32.is_zero(n), String.is_empty(body)) == True{} : Bool},
  hn: {Nat.is_eq(U32.to_nat(n), Bytes.len(body)) == True{} : Bool}) ->
  {RS.walk(X.rask(head), Con{13, Con{10, Bytes.to_list(body)}}, RS.W{RS.MField{HC(code, Some{n}, closing, v10), Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, body}, Nil{}}, Nil{}} : RS.W}:
  Equal.trans(RS.W,
    RS.walk(X.rask(head), Con{13, Con{10, Bytes.to_list(body)}}, RS.W{RS.MField{HC(code, Some{n}, closing, v10), Nil{}}, Nil{}}),
    RS.W{RS.MDone{RS.resp(HC(code, Some{n}, closing, v10), Bytes.to_list(body), False{}), Nil{}}, Nil{}},
    RS.W{RS.MDone{R.Resp{code, False{}, closing, body}, Nil{}}, Nil{}},
    rend.len(head, code, n, closing, v10 && Bool.not(closing), body, hlt, hb, hz, hn),
    Equal.trans(RS.W, RS.W{RS.MDone{RS.resp(HC(code, Some{n}, closing, v10), Bytes.to_list(body), False{}), Nil{}}, Nil{}},
      RS.W{RS.MDone{R.Resp{code, False{}, closing, Bytes.from_list(Bytes.to_list(body))}, Nil{}}, Nil{}},
      RS.W{RS.MDone{R.Resp{code, False{}, closing, body}, Nil{}}, Nil{}},
      Equal.cong(R.Resp, RS.W, r => RS.W{RS.MDone{r, Nil{}}, Nil{}}, RS.resp(HC(code, Some{n}, closing, v10), Bytes.to_list(body), False{}),
        R.Resp{code, False{}, closing, Bytes.from_list(Bytes.to_list(body))},
        rresp.eq(code, Some{n}, closing, v10, Bytes.to_list(body), h101)),
      Equal.cong(Bytes(), RS.W, b => RS.W{RS.MDone{R.Resp{code, False{}, closing, b}, Nil{}}, Nil{}},
        Bytes.from_list(Bytes.to_list(body)), body, bytes.rt(body))))

# The Connection
# --------------

def rhc(h: R.Head, closing: Bool, v10: Bool) -> R.Head:
  match closing:
    case True{}:
      RS.head.conn(h, True{}, False{})
    case False{}:
      match v10:
        case True{}:
          RS.head.conn(h, False{}, True{})
        case False{}:
          h

# LEMMA: the Connection sent says what the proxy does
def rconn(closing: Bool, v10: Bool, +h: R.Head, +rest: List<&2, U32>, +e: R.Ask, +o: List<&2, U32>) ->
  {RS.walk(e, List.append(&2, U32, FLSl(X.rconf(X.conn.val(closing, v10))), rest), RS.W{RS.MField{h, Nil{}}, o}) ==
    RS.walk(e, rest, RS.W{RS.MField{rhc(h, closing, v10), Nil{}}, o}) : RS.W}:
  match closing:
    case True{}:
      {==}
    case False{}:
      match v10:
        case True{}:
          {==}
        case False{}:
          {==}

def rhc.form(closing: Bool, v10: Bool, +code: U32, +l: Maybe<&2, U32>) ->
  {rhc(R.Head{False{}, code, l, False{}, False{}, False{}}, closing, v10) == HC(code, l, closing, v10) : R.Head}:
  match closing v10:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def rconn.to(+code: U32, +l: Maybe<&2, U32>, +closing: Bool, +v10: Bool, +rest: List<&2, U32>, +e: R.Ask) ->
  {RS.walk(e, List.append(&2, U32, FLSl(X.rconf(X.conn.val(closing, v10))), rest),
    RS.W{RS.MField{R.Head{False{}, code, l, False{}, False{}, False{}}, Nil{}}, Nil{}}) ==
    RS.walk(e, rest, RS.W{RS.MField{HC(code, l, closing, v10), Nil{}}, Nil{}}) : RS.W}:
  Equal.trans(RS.W, RS.walk(e, List.append(&2, U32, FLSl(X.rconf(X.conn.val(closing, v10))), rest),
      RS.W{RS.MField{R.Head{False{}, code, l, False{}, False{}, False{}}, Nil{}}, Nil{}}),
    RS.walk(e, rest, RS.W{RS.MField{rhc(R.Head{False{}, code, l, False{}, False{}, False{}}, closing, v10), Nil{}}, Nil{}}),
    RS.walk(e, rest, RS.W{RS.MField{HC(code, l, closing, v10), Nil{}}, Nil{}}),
    rconn(closing, v10, R.Head{False{}, code, l, False{}, False{}, False{}}, rest, e, Nil{}),
    Equal.cong(R.Head, RS.W, h => RS.walk(e, rest, RS.W{RS.MField{h, Nil{}}, Nil{}}),
      rhc(R.Head{False{}, code, l, False{}, False{}, False{}}, closing, v10), HC(code, l, closing, v10),
      rhc.form(closing, v10, code, l)))

# The length, the Connection, the end
# -----------------------------------

def TAIL(clen: Bytes(), +conn: Bytes(), +b: Bytes()) -> List<&2, U32>:
  List.append(&2, U32, FLSl(List.append(&2, Wr.Field, X.rclf(clen), X.rconf(conn))), Con{13, Con{10, Bytes.to_list(b)}})

# no length: a response with no body by its framing
def rtail.nil(bl: Bool, +head: Bool, +code: U32, +closing: Bool, +v10: Bool, +body: Bytes(),
  hbl: {X.rbodyless(head, code) == bl : Bool}, hlt: {U32.is_lt(code, 200) == False{} : Bool},
  h101: {U32.is_eq(code, 101) == False{} : Bool}, ak: {bl == True{} : Bool}) ->
  {RS.walk(X.rask(head), TAIL("", X.conn.val(closing, v10), Bool.pick(Bytes(), bl, "", body)),
    RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), bl, "", body)}, Nil{}}, Nil{}} : RS.W}:
  match bl:
    case False{}:
      no({RS.walk(X.rask(head), TAIL("", X.conn.val(closing, v10), body),
        RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}) ==
        RS.W{RS.MDone{R.Resp{code, False{}, closing, body}, Nil{}}, Nil{}} : RS.W}, ak)
    case True{}:
      Equal.trans(RS.W, RS.walk(X.rask(head), TAIL("", X.conn.val(closing, v10), ""),
          RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}),
        RS.walk(X.rask(head), Con{13, Con{10, Nil{}}}, RS.W{RS.MField{HC(code, None{}, closing, v10), Nil{}}, Nil{}}),
        RS.W{RS.MDone{R.Resp{code, False{}, closing, ""}, Nil{}}, Nil{}},
        rconn.to(code, None{}, closing, v10, Con{13, Con{10, Nil{}}}, X.rask(head)),
        rafter.none(head, code, None{}, closing, v10, hlt, h101, hbl))

def rafter.len.pr(+head: Bool, +code: U32, +n: U32, +closing: Bool, +v10: Bool, +body: Bytes(),
  hlt: {U32.is_lt(code, 200) == False{} : Bool}, h101: {U32.is_eq(code, 101) == False{} : Bool},
  hb: {X.rbodyless(head, code) == False{} : Bool},
  hh: {X.same(U32.is_zero(n), String.is_empty(body)) == True{} : Bool} &
    {Nat.is_eq(U32.to_nat(n), Bytes.len(body)) == True{} : Bool}) ->
  {RS.walk(X.rask(head), Con{13, Con{10, Bytes.to_list(body)}}, RS.W{RS.MField{HC(code, Some{n}, closing, v10), Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, body}, Nil{}}, Nil{}} : RS.W}:
  (hz, hn) = hh
  rafter.len(head, code, n, closing, v10, body, hlt, h101, hb, hz, hn)

def rtail.fin(bl: Bool, +head: Bool, +code: U32, +n: U32, +closing: Bool, +v10: Bool, +body: Bytes(),
  hbl: {X.rbodyless(head, code) == bl : Bool}, hlt: {U32.is_lt(code, 200) == False{} : Bool},
  h101: {U32.is_eq(code, 101) == False{} : Bool},
  hrest: {(bl || (X.same(U32.is_zero(n), String.is_empty(body)) && Nat.is_eq(U32.to_nat(n), Bytes.len(body)))) == True{} : Bool}) ->
  {RS.walk(X.rask(head), Con{13, Con{10, Bytes.to_list(Bool.pick(Bytes(), bl, "", body))}},
    RS.W{RS.MField{HC(code, Some{n}, closing, v10), Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), bl, "", body)}, Nil{}}, Nil{}} : RS.W}:
  match bl:
    case True{}:
      rafter.none(head, code, Some{n}, closing, v10, hlt, h101, hbl)
    case False{}:
      rafter.len.pr(head, code, n, closing, v10, body, hlt, h101, hbl,
        and.split(X.same(U32.is_zero(n), String.is_empty(body)), Nat.is_eq(U32.to_nat(n), Bytes.len(body)), hrest))

def rpl.cl(+d: Bytes(), +ad: {X.rok.all(RS.TVal{}, d) == True{} : Bool}) -> RPL(FLl(Wr.Field{"content-length", d})):
  rpl.app(Bytes.to_list("content-length"), Con{58, Con{32, Bytes.to_list(d)}},
    ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, Unit{})))))))))))))),
    ({==}, ({==}, raa.pl(RS.TVal{}, Bytes.to_list(d), raa.of(RS.TVal{}, d, ad)))))

# a length the client reads as the check did
def rtail.n(+n: U32, +ws: Bool, +head: Bool, +code: U32, +d: Bytes(), +closing: Bool, +v10: Bool, +bl: Bool, +body: Bytes(),
  hbl: {X.rbodyless(head, code) == bl : Bool}, hlt: {U32.is_lt(code, 200) == False{} : Bool},
  h101: {U32.is_eq(code, 101) == False{} : Bool}, +ad: {X.rok.all(RS.TVal{}, d) == True{} : Bool},
  hlv: {RS.len.view(X.rask(head), RS.span(RS.TOws{}, Con{32, Bytes.to_list(d)})) == RS.FVal{RS.VLen{n, ws}} : RS.FLine},
  al: {Bool.not(U32.is_lt(268435455, n)) == True{} : Bool} & {(bl || (X.same(U32.is_zero(n), String.is_empty(body)) &&
    Nat.is_eq(U32.to_nat(n), Bytes.len(body)))) == True{} : Bool}) ->
  {RS.walk(X.rask(head), List.append(&2, U32, FLl(Wr.Field{"content-length", d}),
      Con{13, Con{10, List.append(&2, U32, FLSl(X.rconf(X.conn.val(closing, v10))),
        Con{13, Con{10, Bytes.to_list(Bool.pick(Bytes(), bl, "", body))}})}}),
    RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), bl, "", body)}, Nil{}}, Nil{}} : RS.W}:
  (hcap, hrest) = al
  +e2 : List<&2, U32> = Con{13, Con{10, Bytes.to_list(Bool.pick(Bytes(), bl, "", body))}}
  +h1 : R.Head = R.Head{False{}, code, Some{n}, False{}, False{}, False{}}
  Equal.trans(RS.W,
    RS.walk(X.rask(head), List.append(&2, U32, FLl(Wr.Field{"content-length", d}),
      Con{13, Con{10, List.append(&2, U32, FLSl(X.rconf(X.conn.val(closing, v10))), e2)}}),
      RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}),
    RS.walk(X.rask(head), List.append(&2, U32, FLSl(X.rconf(X.conn.val(closing, v10))), e2), RS.W{RS.MField{h1, Nil{}}, Nil{}}),
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), bl, "", body)}, Nil{}}, Nil{}},
    rline.fl(Wr.Field{"content-length", d}, List.append(&2, U32, FLSl(X.rconf(X.conn.val(closing, v10))), e2),
      R.head.new(False{}, code), h1, X.rask(head), Nil{}, RS.VLen{n, ws}, rpl.cl(d, ad), hlv,
      Equal.cong(Bool, Maybe<&2, R.Head>, b => RS.head.big(b, R.head.new(False{}, code), n), U32.is_lt(268435455, n), False{},
        not.true(U32.is_lt(268435455, n), hcap))),
    Equal.trans(RS.W,
      RS.walk(X.rask(head), List.append(&2, U32, FLSl(X.rconf(X.conn.val(closing, v10))), e2), RS.W{RS.MField{h1, Nil{}}, Nil{}}),
      RS.walk(X.rask(head), e2, RS.W{RS.MField{HC(code, Some{n}, closing, v10), Nil{}}, Nil{}}),
      RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), bl, "", body)}, Nil{}}, Nil{}},
      rconn.to(code, Some{n}, closing, v10, e2, X.rask(head)),
      rtail.fin(bl, head, code, n, closing, v10, body, hbl, hlt, h101, hrest)))

def rtail.val(val: RS.Val, +head: Bool, +code: U32, +d: Bytes(), +closing: Bool, +v10: Bool, +bl: Bool, +body: Bytes(),
  hbl: {X.rbodyless(head, code) == bl : Bool}, hlt: {U32.is_lt(code, 200) == False{} : Bool},
  h101: {U32.is_eq(code, 101) == False{} : Bool}, +ad: {X.rok.all(RS.TVal{}, d) == True{} : Bool},
  hlv: {RS.len.view(X.rask(head), RS.span(RS.TOws{}, Con{32, Bytes.to_list(d)})) == RS.FVal{val} : RS.FLine},
  al: {X.rok.len.at(RS.FVal{val}, bl, body) == True{} : Bool}) ->
  {RS.walk(X.rask(head), List.append(&2, U32, FLl(Wr.Field{"content-length", d}),
      Con{13, Con{10, List.append(&2, U32, FLSl(X.rconf(X.conn.val(closing, v10))),
        Con{13, Con{10, Bytes.to_list(Bool.pick(Bytes(), bl, "", body))}})}}),
    RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), bl, "", body)}, Nil{}}, Nil{}} : RS.W}:
  match val:
    case RS.VLen{+n, +ws}:
      rtail.n(n, ws, head, code, d, closing, v10, bl, body, hbl, hlt, h101, ad, hlv,
        and.split(Bool.not(U32.is_lt(268435455, n)), bl || (X.same(U32.is_zero(n), String.is_empty(body)) &&
          Nat.is_eq(U32.to_nat(n), Bytes.len(body))), al))
    case RS.VLen0{}:
      no({RS.walk(X.rask(head), List.append(&2, U32, FLl(Wr.Field{"content-length", d}),
      Con{13, Con{10, List.append(&2, U32, FLSl(X.rconf(X.conn.val(closing, v10))),
        Con{13, Con{10, Bytes.to_list(Bool.pick(Bytes(), bl, "", body))}})}}),
    RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), bl, "", body)}, Nil{}}, Nil{}} : RS.W}, al)
    case RS.VTe0{}:
      no({RS.walk(X.rask(head), List.append(&2, U32, FLl(Wr.Field{"content-length", d}),
      Con{13, Con{10, List.append(&2, U32, FLSl(X.rconf(X.conn.val(closing, v10))),
        Con{13, Con{10, Bytes.to_list(Bool.pick(Bytes(), bl, "", body))}})}}),
    RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), bl, "", body)}, Nil{}}, Nil{}} : RS.W}, al)
    case RS.VTe{t}:
      no({RS.walk(X.rask(head), List.append(&2, U32, FLl(Wr.Field{"content-length", d}),
      Con{13, Con{10, List.append(&2, U32, FLSl(X.rconf(X.conn.val(closing, v10))),
        Con{13, Con{10, Bytes.to_list(Bool.pick(Bytes(), bl, "", body))}})}}),
    RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), bl, "", body)}, Nil{}}, Nil{}} : RS.W}, al)
    case RS.VConn{dn, cu}:
      no({RS.walk(X.rask(head), List.append(&2, U32, FLl(Wr.Field{"content-length", d}),
      Con{13, Con{10, List.append(&2, U32, FLSl(X.rconf(X.conn.val(closing, v10))),
        Con{13, Con{10, Bytes.to_list(Bool.pick(Bytes(), bl, "", body))}})}}),
    RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), bl, "", body)}, Nil{}}, Nil{}} : RS.W}, al)
    case RS.VSkip{}:
      no({RS.walk(X.rask(head), List.append(&2, U32, FLl(Wr.Field{"content-length", d}),
      Con{13, Con{10, List.append(&2, U32, FLSl(X.rconf(X.conn.val(closing, v10))),
        Con{13, Con{10, Bytes.to_list(Bool.pick(Bytes(), bl, "", body))}})}}),
    RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), bl, "", body)}, Nil{}}, Nil{}} : RS.W}, al)

def rtail.lv(lv: RS.FLine, +head: Bool, +code: U32, +d: Bytes(), +closing: Bool, +v10: Bool, +bl: Bool, +body: Bytes(),
  hbl: {X.rbodyless(head, code) == bl : Bool}, hlt: {U32.is_lt(code, 200) == False{} : Bool},
  h101: {U32.is_eq(code, 101) == False{} : Bool}, +ad: {X.rok.all(RS.TVal{}, d) == True{} : Bool},
  hlv: {RS.len.view(X.rask(head), RS.span(RS.TOws{}, Con{32, Bytes.to_list(d)})) == lv : RS.FLine},
  al: {X.rok.len.at(lv, bl, body) == True{} : Bool}) ->
  {RS.walk(X.rask(head), List.append(&2, U32, FLl(Wr.Field{"content-length", d}),
      Con{13, Con{10, List.append(&2, U32, FLSl(X.rconf(X.conn.val(closing, v10))),
        Con{13, Con{10, Bytes.to_list(Bool.pick(Bytes(), bl, "", body))}})}}),
    RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), bl, "", body)}, Nil{}}, Nil{}} : RS.W}:
  match lv:
    case RS.FVal{val}:
      rtail.val(val, head, code, d, closing, v10, bl, body, hbl, hlt, h101, ad, hlv, al)
    case RS.FEmpty{}:
      no({RS.walk(X.rask(head), List.append(&2, U32, FLl(Wr.Field{"content-length", d}),
      Con{13, Con{10, List.append(&2, U32, FLSl(X.rconf(X.conn.val(closing, v10))),
        Con{13, Con{10, Bytes.to_list(Bool.pick(Bytes(), bl, "", body))}})}}),
    RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), bl, "", body)}, Nil{}}, Nil{}} : RS.W}, al)
    case RS.FName{nm}:
      no({RS.walk(X.rask(head), List.append(&2, U32, FLl(Wr.Field{"content-length", d}),
      Con{13, Con{10, List.append(&2, U32, FLSl(X.rconf(X.conn.val(closing, v10))),
        Con{13, Con{10, Bytes.to_list(Bool.pick(Bytes(), bl, "", body))}})}}),
    RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), bl, "", body)}, Nil{}}, Nil{}} : RS.W}, al)
    case RS.FBad{}:
      no({RS.walk(X.rask(head), List.append(&2, U32, FLl(Wr.Field{"content-length", d}),
      Con{13, Con{10, List.append(&2, U32, FLSl(X.rconf(X.conn.val(closing, v10))),
        Con{13, Con{10, Bytes.to_list(Bool.pick(Bytes(), bl, "", body))}})}}),
    RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), bl, "", body)}, Nil{}}, Nil{}} : RS.W}, al)

def rtail.cl2(+c: Char, +t: Bytes(), +head: Bool, +code: U32, +closing: Bool, +v10: Bool, +bl: Bool, +body: Bytes(),
  hbl: {X.rbodyless(head, code) == bl : Bool}, hlt: {U32.is_lt(code, 200) == False{} : Bool},
  h101: {U32.is_eq(code, 101) == False{} : Bool},
  hh: {X.rok.all(RS.TVal{}, SCon{c, t}) == True{} : Bool} &
    {X.rok.len.at(RS.len.view(X.rask(head), RS.span(RS.TOws{}, Con{32, Bytes.to_list(SCon{c, t})})), bl, body) == True{} : Bool}) ->
  {RS.walk(X.rask(head), TAIL(SCon{c, t}, X.conn.val(closing, v10), Bool.pick(Bytes(), bl, "", body)),
    RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), bl, "", body)}, Nil{}}, Nil{}} : RS.W}:
  (ad, al) = hh
  +d : Bytes() = SCon{c, t}
  +e2 : List<&2, U32> = Con{13, Con{10, Bytes.to_list(Bool.pick(Bytes(), bl, "", body))}}
  +cf : List<&2, U32> = FLSl(X.rconf(X.conn.val(closing, v10)))
  Equal.trans(RS.W, RS.walk(X.rask(head), TAIL(d, X.conn.val(closing, v10), Bool.pick(Bytes(), bl, "", body)),
      RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}),
    RS.walk(X.rask(head), List.append(&2, U32, FLl(Wr.Field{"content-length", d}), Con{13, Con{10, List.append(&2, U32, cf, e2)}}),
      RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}),
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), bl, "", body)}, Nil{}}, Nil{}},
    Equal.cong(List<&2, U32>, RS.W, l => RS.walk(X.rask(head), l, RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}),
      List.append(&2, U32, List.append(&2, U32, FLl(Wr.Field{"content-length", d}), Con{13, Con{10, cf}}), e2),
      List.append(&2, U32, FLl(Wr.Field{"content-length", d}), Con{13, Con{10, List.append(&2, U32, cf, e2)}}),
      app.assoc(U32, FLl(Wr.Field{"content-length", d}), Con{13, Con{10, cf}}, e2)),
    rtail.lv(RS.len.view(X.rask(head), RS.span(RS.TOws{}, Con{32, Bytes.to_list(d)})), head, code, d, closing, v10, bl, body, hbl, hlt, h101, ad, {==}, al))

def rtail.cl(+c: Char, +t: Bytes(), +head: Bool, +code: U32, +closing: Bool, +v10: Bool, +bl: Bool, +body: Bytes(),
  hbl: {X.rbodyless(head, code) == bl : Bool}, hlt: {U32.is_lt(code, 200) == False{} : Bool},
  h101: {U32.is_eq(code, 101) == False{} : Bool}, ak: {X.rok.len(head, bl, SCon{c, t}, body) == True{} : Bool}) ->
  {RS.walk(X.rask(head), TAIL(SCon{c, t}, X.conn.val(closing, v10), Bool.pick(Bytes(), bl, "", body)),
    RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), bl, "", body)}, Nil{}}, Nil{}} : RS.W}:
  +d : Bytes() = SCon{c, t}
  rtail.cl2(c, t, head, code, closing, v10, bl, body, hbl, hlt, h101, and.split(X.rok.all(RS.TVal{}, d), X.rok.len.at(RS.len.view(X.rask(head), RS.span(RS.TOws{}, Con{32, Bytes.to_list(d)})), bl, body), ak))

def rtail(clen: Bytes(), +head: Bool, +code: U32, +closing: Bool, +v10: Bool, +bl: Bool, +body: Bytes(),
  hbl: {X.rbodyless(head, code) == bl : Bool}, hlt: {U32.is_lt(code, 200) == False{} : Bool},
  h101: {U32.is_eq(code, 101) == False{} : Bool}, ak: {X.rok.len(head, bl, clen, body) == True{} : Bool}) ->
  {RS.walk(X.rask(head), TAIL(clen, X.conn.val(closing, v10), Bool.pick(Bytes(), bl, "", body)),
    RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), bl, "", body)}, Nil{}}, Nil{}} : RS.W}:
  match clen:
    case SNil{}:
      rtail.nil(bl, head, code, closing, v10, body, hbl, hlt, h101, ak)
    case SCon{+c, +t}:
      rtail.cl(c, t, head, code, closing, v10, bl, body, hbl, hlt, h101, ak)


# The whole response
# ------------------

def RSERl(+cd: Bytes(), +why: Bytes(), fs: List<&2, Wr.Field>, clen: Bytes(), +conn: Bytes(), +b: Bytes()) -> List<&2, U32>:
  List.append(&2, U32, SLl(cd, why),
    Con{13, Con{10, List.append(&2, U32, FLSl(X.rall(fs, clen, conn)), Con{13, Con{10, Bytes.to_list(b)}})}})

def rser.list(+cd: Bytes(), +why: Bytes(), +fs: List<&2, Wr.Field>, +clen: Bytes(), +conn: Bytes(), +body: Bytes(), +bl: Bool) ->
  {Bytes.to_list(X.rser(X.Rsp{cd, why, fs, clen, body, bl}, conn)) ==
    RSERl(cd, why, fs, clen, conn, Bool.pick(Bytes(), bl, "", body)) : List<&2, U32>}:
  +f = X.fls.ser(X.rall(fs, clen, conn))
  +b = Bool.pick(Bytes(), bl, "", body)
  Equal.trans(List<&2, U32>, Bytes.to_list(X.rser(X.Rsp{cd, why, fs, clen, body, bl}, conn)),
    List.append(&2, U32, Bytes.to_list(X.sl.ser(cd, why)), Bytes.to_list(Bytes.append("\r\n", Bytes.append(f, Bytes.append("\r\n", b))))),
    RSERl(cd, why, fs, clen, conn, b),
    tl.app(X.sl.ser(cd, why), Bytes.append("\r\n", Bytes.append(f, Bytes.append("\r\n", b)))),
    Equal.trans(List<&2, U32>,
      List.append(&2, U32, Bytes.to_list(X.sl.ser(cd, why)), Con{13, Con{10, Bytes.to_list(Bytes.append(f, Bytes.append("\r\n", b)))}}),
      List.append(&2, U32, SLl(cd, why), Con{13, Con{10, Bytes.to_list(Bytes.append(f, Bytes.append("\r\n", b)))}}),
      RSERl(cd, why, fs, clen, conn, b),
      Equal.cong(List<&2, U32>, List<&2, U32>,
        l => List.append(&2, U32, l, Con{13, Con{10, Bytes.to_list(Bytes.append(f, Bytes.append("\r\n", b)))}}),
        Bytes.to_list(X.sl.ser(cd, why)), SLl(cd, why), sl.list(cd, why)),
      Equal.cong(List<&2, U32>, List<&2, U32>, l => List.append(&2, U32, SLl(cd, why), Con{13, Con{10, l}}),
        Bytes.to_list(Bytes.append(f, Bytes.append("\r\n", b))),
        List.append(&2, U32, FLSl(X.rall(fs, clen, conn)), Con{13, Con{10, Bytes.to_list(b)}}),
        Equal.trans(List<&2, U32>, Bytes.to_list(Bytes.append(f, Bytes.append("\r\n", b))),
          List.append(&2, U32, Bytes.to_list(f), Bytes.to_list(Bytes.append("\r\n", b))),
          List.append(&2, U32, FLSl(X.rall(fs, clen, conn)), Con{13, Con{10, Bytes.to_list(b)}}),
          tl.app(f, Bytes.append("\r\n", b)),
          Equal.cong(List<&2, U32>, List<&2, U32>, l => List.append(&2, U32, l, Con{13, Con{10, Bytes.to_list(b)}}),
            Bytes.to_list(f), FLSl(X.rall(fs, clen, conn)), fls.list(X.rall(fs, clen, conn)))))))

def T5(a: Bool, b: Bool, c: Bool, d: Bool, e: Bool) -> Type:
  {a == True{} : Bool} & {b == True{} : Bool} & {c == True{} : Bool} & {d == True{} : Bool} & {e == True{} : Bool}

def split5(a: Bool, b: Bool, c: Bool, d: Bool, -e: Bool, h: {(a && b && c && d && e) == True{} : Bool}) -> T5(a, b, c, d, e):
  match a b c d:
    case True{} True{} True{} True{}:
      ({==}, ({==}, ({==}, ({==}, h))))
    case False{} _ _ _:
      no(T5(False{}, b, c, d, e), h)
    case True{} False{} _ _:
      no(T5(True{}, False{}, c, d, e), h)
    case True{} True{} False{} _:
      no(T5(True{}, True{}, False{}, d, e), h)
    case True{} True{} True{} False{}:
      no(T5(True{}, True{}, True{}, False{}, e), h)

# LEMMA: a response the check passed, sent, is read back as the one that
# came, to its end
def rmain.at(+cd: Bytes(), +why: Bytes(), +fs: List<&2, Wr.Field>, +clen: Bytes(), +head: Bool, +code: U32, +body: Bytes(),
  +closing: Bool, +v10: Bool,
  hc: T5(X.rok.all(RS.TDig{}, cd), RS.code.whole(Bytes.to_list(cd)), U32.is_eq(RS.num(Bytes.to_list(cd)), code),
    Bool.not(U32.is_lt(code, 200)), Bool.not(U32.is_eq(code, 101))),
  +aw: {X.rok.all(RS.TVal{}, why) == True{} : Bool}, hfs: {X.rok.fields(fs) == True{} : Bool},
  hl: {X.rok.len(head, X.rbodyless(head, code), clen, body) == True{} : Bool}) ->
  {RS.walk(X.rask(head), Bytes.to_list(X.rser(X.Rsp{cd, why, fs, clen, body, X.rbodyless(head, code)}, X.conn.val(closing, v10))),
    RS.W{RS.MStatus{Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), X.rbodyless(head, code), "", body)}, Nil{}}, Nil{}} : RS.W}:
  (+ad, r1) = hc
  (cw, r2) = r1
  (heq, r3) = r2
  (hlt0, h1010) = r3
  +e = X.rask(head)
  +conn = X.conn.val(closing, v10)
  +bl = X.rbodyless(head, code)
  +b = Bool.pick(Bytes(), bl, "", body)
  +e2 : List<&2, U32> = Con{13, Con{10, Bytes.to_list(b)}}
  +cf : List<&2, Wr.Field> = List.append(&2, Wr.Field, X.rclf(clen), X.rconf(conn))
  Equal.trans(RS.W, RS.walk(e, Bytes.to_list(X.rser(X.Rsp{cd, why, fs, clen, body, bl}, conn)), RS.W{RS.MStatus{Nil{}}, Nil{}}),
    RS.walk(e, RSERl(cd, why, fs, clen, conn, b), RS.W{RS.MStatus{Nil{}}, Nil{}}),
    RS.W{RS.MDone{R.Resp{code, False{}, closing, b}, Nil{}}, Nil{}},
    Equal.cong(List<&2, U32>, RS.W, l => RS.walk(e, l, RS.W{RS.MStatus{Nil{}}, Nil{}}),
      Bytes.to_list(X.rser(X.Rsp{cd, why, fs, clen, body, bl}, conn)), RSERl(cd, why, fs, clen, conn, b),
      rser.list(cd, why, fs, clen, conn, body, bl)),
    Equal.trans(RS.W, RS.walk(e, RSERl(cd, why, fs, clen, conn, b), RS.W{RS.MStatus{Nil{}}, Nil{}}),
      RS.walk(e, List.append(&2, U32, FLSl(X.rall(fs, clen, conn)), e2),
        RS.W{RS.MField{R.head.new(False{}, RS.num(Bytes.to_list(cd))), Nil{}}, Nil{}}),
      RS.W{RS.MDone{R.Resp{code, False{}, closing, b}, Nil{}}, Nil{}},
      rline.st(cd, why, List.append(&2, U32, FLSl(X.rall(fs, clen, conn)), e2), e, Nil{}, ad, cw, aw),
      Equal.trans(RS.W, RS.walk(e, List.append(&2, U32, FLSl(X.rall(fs, clen, conn)), e2),
          RS.W{RS.MField{R.head.new(False{}, RS.num(Bytes.to_list(cd))), Nil{}}, Nil{}}),
        RS.walk(e, List.append(&2, U32, FLSl(X.rall(fs, clen, conn)), e2), RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}),
        RS.W{RS.MDone{R.Resp{code, False{}, closing, b}, Nil{}}, Nil{}},
        Equal.cong(U32, RS.W, x => RS.walk(e, List.append(&2, U32, FLSl(X.rall(fs, clen, conn)), e2),
            RS.W{RS.MField{R.head.new(False{}, x), Nil{}}, Nil{}}),
          RS.num(Bytes.to_list(cd)), code, u32.eq(RS.num(Bytes.to_list(cd)), code, heq)),
        Equal.trans(RS.W,
          RS.walk(e, List.append(&2, U32, FLSl(X.rall(fs, clen, conn)), e2), RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}),
          RS.walk(e, List.append(&2, U32, FLSl(fs), List.append(&2, U32, FLSl(cf), e2)),
            RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}),
          RS.W{RS.MDone{R.Resp{code, False{}, closing, b}, Nil{}}, Nil{}},
          Equal.cong(List<&2, U32>, RS.W, l => RS.walk(e, l, RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}),
            List.append(&2, U32, FLSl(X.rall(fs, clen, conn)), e2),
            List.append(&2, U32, FLSl(fs), List.append(&2, U32, FLSl(cf), e2)),
            Equal.trans(List<&2, U32>, List.append(&2, U32, FLSl(X.rall(fs, clen, conn)), e2),
              List.append(&2, U32, List.append(&2, U32, FLSl(fs), FLSl(cf)), e2),
              List.append(&2, U32, FLSl(fs), List.append(&2, U32, FLSl(cf), e2)),
              Equal.cong(List<&2, U32>, List<&2, U32>, l => List.append(&2, U32, l, e2), FLSl(X.rall(fs, clen, conn)),
                List.append(&2, U32, FLSl(fs), FLSl(cf)), fls.app(fs, cf)),
              app.assoc(U32, FLSl(fs), FLSl(cf), e2))),
          Equal.trans(RS.W,
            RS.walk(e, List.append(&2, U32, FLSl(fs), List.append(&2, U32, FLSl(cf), e2)),
              RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}),
            RS.walk(e, List.append(&2, U32, FLSl(cf), e2), RS.W{RS.MField{R.head.new(False{}, code), Nil{}}, Nil{}}),
            RS.W{RS.MDone{R.Resp{code, False{}, closing, b}, Nil{}}, Nil{}},
            rfields.walk(fs, List.append(&2, U32, FLSl(cf), e2), R.head.new(False{}, code), e, Nil{}, hfs),
            rtail(clen, head, code, closing, v10, bl, body, {==}, not.true(U32.is_lt(code, 200), hlt0),
              not.true(U32.is_eq(code, 101), h1010), hl))))))

def rmain.split(+cd: Bytes(), +why: Bytes(), +fs: List<&2, Wr.Field>, +clen: Bytes(), +head: Bool, +code: U32, +body: Bytes(),
  +closing: Bool, +v10: Bool,
  hh: {X.rok.code(cd, code) == True{} : Bool} & {X.rok.all(RS.TVal{}, why) == True{} : Bool} &
    {X.rok.fields(fs) == True{} : Bool} & {X.rok.len(head, X.rbodyless(head, code), clen, body) == True{} : Bool}) ->
  {RS.walk(X.rask(head), Bytes.to_list(X.rser(X.Rsp{cd, why, fs, clen, body, X.rbodyless(head, code)}, X.conn.val(closing, v10))),
    RS.W{RS.MStatus{Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), X.rbodyless(head, code), "", body)}, Nil{}}, Nil{}} : RS.W}:
  (hk, r1) = hh
  (aw, r2) = r1
  (hfs, hl) = r2
  rmain.at(cd, why, fs, clen, head, code, body, closing, v10,
    split5(X.rok.all(RS.TDig{}, cd), RS.code.whole(Bytes.to_list(cd)), U32.is_eq(RS.num(Bytes.to_list(cd)), code),
      Bool.not(U32.is_lt(code, 200)), Bool.not(U32.is_eq(code, 101)), hk), aw, hfs, hl)

def rmain(+cd: Bytes(), +why: Bytes(), +fs: List<&2, Wr.Field>, +clen: Bytes(), +head: Bool, +code: U32, +body: Bytes(),
  +closing: Bool, +v10: Bool,
  hv: {X.rvalid(head, code, X.Rsp{cd, why, fs, clen, body, X.rbodyless(head, code)}) == True{} : Bool}) ->
  {RS.walk(X.rask(head), Bytes.to_list(X.rser(X.Rsp{cd, why, fs, clen, body, X.rbodyless(head, code)}, X.conn.val(closing, v10))),
    RS.W{RS.MStatus{Nil{}}, Nil{}}) ==
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), X.rbodyless(head, code), "", body)}, Nil{}}, Nil{}} : RS.W}:
  rmain.split(cd, why, fs, clen, head, code, body, closing, v10,
    split4(X.rok.code(cd, code), X.rok.all(RS.TVal{}, why), X.rok.fields(fs), X.rok.len(head, X.rbodyless(head, code), clen, body), hv))

# The law
# -------

def rr.valid(+cd: Bytes(), +why: Bytes(), +fs: List<&2, Wr.Field>, +hlen: Bytes(), +head: Bool, +code: U32, +body: Bytes(),
  +closing: Bool, +v10: Bool,
  hv: {X.rvalid(head, code, X.rsp.fin(head, code, X.RHead{cd, why, fs, hlen}, body)) == True{} : Bool}) ->
  {RS.response(X.rask(head), Bytes.to_list(X.reply(Some{X.rsp.fin(head, code, X.RHead{cd, why, fs, hlen}, body)}, head, closing, v10))) ==
    Laws.rlook(Some{X.rsp.fin(head, code, X.RHead{cd, why, fs, hlen}, body)}, head, code, body, closing) : R.Look}:
  +clen = X.rclen(head, X.rbodyless(head, code), hlen, body)
  Equal.cong(RS.W, R.Look, w => RS.finish(X.rask(head), w),
    RS.walk(X.rask(head), Bytes.to_list(X.rser(X.Rsp{cd, why, fs, clen, body, X.rbodyless(head, code)}, X.conn.val(closing, v10))),
      RS.W{RS.MStatus{Nil{}}, Nil{}}),
    RS.W{RS.MDone{R.Resp{code, False{}, closing, Bool.pick(Bytes(), X.rbodyless(head, code), "", body)}, Nil{}}, Nil{}},
    rmain(cd, why, fs, clen, head, code, body, closing, v10, hv))

def rr.h(h: X.RHead, +head: Bool, +code: U32, +body: Bytes(), +closing: Bool, +v10: Bool,
  hv: {X.rvalid(head, code, X.rsp.fin(head, code, h, body)) == True{} : Bool}) ->
  {RS.response(X.rask(head), Bytes.to_list(X.reply(Some{X.rsp.fin(head, code, h, body)}, head, closing, v10))) ==
    Laws.rlook(Some{X.rsp.fin(head, code, h, body)}, head, code, body, closing) : R.Look}:
  match h:
    case X.RHead{+cd, +why, +fs, +hlen}:
      rr.valid(cd, why, fs, hlen, head, code, body, closing, v10, hv)

def rr.pick(b: Bool, +head: Bool, +code: U32, +h: X.RHead, +body: Bytes(), +closing: Bool, +v10: Bool,
  e: {X.rvalid(head, code, X.rsp.fin(head, code, h, body)) == b : Bool}) ->
  {RS.response(X.rask(head), Bytes.to_list(X.reply(Bool.pick(Maybe<&2, X.Rsp>, b, Some{X.rsp.fin(head, code, h, body)}, None{}),
    head, closing, v10))) ==
    Laws.rlook(Bool.pick(Maybe<&2, X.Rsp>, b, Some{X.rsp.fin(head, code, h, body)}, None{}), head, code, body, closing) : R.Look}:
  match b:
    case True{}:
      rr.h(h, head, code, body, closing, v10, e)
    case False{}:
      r502(head, closing, v10, code, body)

def rr.at(+head: Bool, +code: U32, mh: Maybe<&2, X.RHead>, +body: Bytes(), +closing: Bool, +v10: Bool) ->
  {RS.response(X.rask(head), Bytes.to_list(X.reply(X.rsp.at(head, code, mh, body), head, closing, v10))) ==
    Laws.rlook(X.rsp.at(head, code, mh, body), head, code, body, closing) : R.Look}:
  match mh:
    case Some{+h}:
      rr.pick(X.rvalid(head, code, X.rsp.fin(head, code, h, body)), head, code, h, body, closing, v10, {==})
    case None{}:
      r502(head, closing, v10, code, body)

def Laws.rsp_reframed(via, head, k, code, got, body, closing, v10):
  rr.at(head, code, X.rhead.of(via, X.rfinal(k, got)), body, closing, v10)
