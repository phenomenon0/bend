# The proofs of the HTTP engine laws.
#
# feed_split and bad_feeds are inductions on the chunk: feed walks the
# string structurally and ++ builds it the same way, so in the cons
# case both sides step the reader once and the induction hypothesis is
# already the goal. bad_absorbs and the five reply laws compute: the
# machine's last row sends Bad{} to Bad{} whatever the byte class is,
# and each written-out reply normalises to the same string the builder
# does.
import Base
import ./main.bend as Eng
import ./sha1.bend as Sha1
import ./b64.bend as B64
import ./ws.bend as Ws
import ./spec.bend as Spec
import ./LAWS.bend as Laws

def Laws.feed_split(a, b, p):
  match a:
    case Nil{}:
      {==}
    case Con{c, t}:
      Laws.feed_split(t, b, Eng.step(p, c))

def Laws.bad_absorbs(c, pd, out):
  {==}

def Laws.bad_feeds(s, pd, out):
  match s:
    case Nil{}:
      {==}
    case Con{c, t}:
      Laws.bad_feeds(t, pd, out)

# Framing
# =======
#
# cls_is_spec, lower_is_spec and the vectors compute. field_by_bytes is
# an induction over the table: at each entry both lookups test the same
# name, the engine with bytes.eq and the reference with Spec.eq, and
# eq_is_spec says those two are one function. The laws with a class in
# their premise go through one lemma each over the ten classes: where
# the premise says the class is allowed, it reads True == False and the
# case is refuted through BD; everywhere else the step computes to Bad.

# a type chosen by a Bool, for refuting True == False
def BD(b: Bool, tc: Type, fc: Type) -> Type:
  match b:
    case True{}:
      tc
    case False{}:
      fc

def eq_is_spec(+a: List<&2, U32>, +b: List<&2, U32>) ->
  {Eng.bytes.eq(a, b) == Spec.eq(a, b) : Bool}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, u}:
      {==}
    case Con{x, t} Nil{}:
      {==}
    case Con{x, t} Con{y, u}:
      %eq_is_spec(t, u) : {Bool.and(U32.is_eq(x, y), Eng.bytes.eq(t, u)) ==
        Bool.and(U32.is_eq(x, y), _) : Bool}
      {==}

def find_is_spec(+k: List<&2, U32>, tbl: List<&2, Eng.Known>) ->
  {Eng.fld.find(k, tbl) == Spec.find(k, tbl) : Eng.Fld}:
  match tbl:
    case Nil{}:
      {==}
    case Con{h, t}:
      match h:
        case Eng.Known{n, f}:
          %find_is_spec(k, t) : {Eng.fld.pick(Eng.bytes.eq(k, n), f, Eng.fld.find(k, t)) ==
            Eng.fld.pick(Spec.eq(k, n), f, _) : Eng.Fld}
          %eq_is_spec(k, n) : {Eng.fld.pick(Eng.bytes.eq(k, n), f, Eng.fld.find(k, t)) ==
            Eng.fld.pick(_, f, Eng.fld.find(k, t)) : Eng.Fld}
          {==}

def Laws.cls_is_spec():
  {==}

def Laws.lower_is_spec():
  {==}

def Laws.field_by_bytes(k):
  find_is_spec(k, Eng.fld.table())

def Laws.te_refused(k, pd, out, e):
  %Equal.sym(Eng.Fld, Eng.fld.of(k), Spec.field(k), Laws.field_by_bytes(k)) :
    {Eng.step.name(_, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}
  %Equal.sym(Bool, Spec.eq(k, Spec.name("transfer-encoding")), True{}, e) :
    {Eng.step.name(Eng.fld.pick(_, Eng.FTe{}, Spec.find(k, Spec.fields.rest())), pd, out) ==
      Eng.P{Eng.Bad{}, pd, out} : Eng.P}
  {==}

def Laws.clen_disagree(v, w, m, path, cl, h, ws, out, e):
  %Equal.sym(Bool, U32.is_eq(w, v), False{}, e) :
    {Eng.step.clen.dup(Eng.Pend{m, path, Eng.Has{v}, cl, h, ws}, out, _) ==
      Eng.P{Eng.Bad{}, Eng.Pend{m, path, Eng.Has{v}, cl, h, ws}, out} : Eng.P}
  {==}

def Laws.host_once(m, path, l, cl, h, ws, out, e):
  match l h:
    case Eng.NoCl{} Eng.H0{}:
      {==}
    case Eng.Has{v} Eng.H0{}:
      {==}
    case Eng.NoCl{} Eng.H2{}:
      {==}
    case Eng.Has{v} Eng.H2{}:
      {==}
    case Eng.NoCl{} Eng.H1{}:
      %e : BD(_, Unit, {Eng.step(Eng.P{Eng.CrL{}, Eng.Pend{m, path, Eng.NoCl{}, cl, Eng.H1{}, ws}, out}, 10) ==
        Eng.P{Eng.Bad{}, Eng.Pend{m, path, Eng.NoCl{}, cl, Eng.H1{}, ws}, out} : Eng.P})
      Unit{}
    case Eng.Has{v} Eng.H1{}:
      %e : BD(_, Unit, {Eng.step(Eng.P{Eng.CrL{}, Eng.Pend{m, path, Eng.Has{v}, cl, Eng.H1{}, ws}, out}, 10) ==
        Eng.P{Eng.Bad{}, Eng.Pend{m, path, Eng.Has{v}, cl, Eng.H1{}, ws}, out} : Eng.P})
      Unit{}

def Laws.rest_feeds(s, bs, pd, out):
  match s:
    case Nil{}:
      {==}
    case Con{c, t}:
      Laws.rest_feeds(t, Con{c, bs}, pd, out)

def name_bad(
  k: Eng.Cls, c: U32, n: List<&2, U32>, pd: Eng.Pend, out: List<&2, Eng.Req>,
  e: {Spec.in.name(k) == False{} : Bool}
) -> {Eng.step.at(Eng.InN{n}, k, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}:
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
      %e : BD(_, Unit, {Eng.step.at(Eng.InN{n}, Eng.KCo{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KCm{}:
      {==}
    case Eng.KDg{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InN{n}, Eng.KDg{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KTk{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InN{n}, Eng.KTk{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KVc{}:
      {==}
    case Eng.KCt{}:
      {==}

def Laws.name_refuses(c, n, pd, out, e):
  name_bad(Eng.cls(c), c, n, pd, out, e)

def line_bad(
  k: Eng.Cls, c: U32, pd: Eng.Pend, out: List<&2, Eng.Req>,
  e: {Spec.in.line(k) == False{} : Bool}
) -> {Eng.step.at(Eng.Lin{}, k, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}:
  match k:
    case Eng.KSp{}:
      {==}
    case Eng.KHt{}:
      {==}
    case Eng.KCr{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.Lin{}, Eng.KCr{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KLf{}:
      {==}
    case Eng.KCo{}:
      {==}
    case Eng.KCm{}:
      {==}
    case Eng.KDg{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.Lin{}, Eng.KDg{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KTk{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.Lin{}, Eng.KTk{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KVc{}:
      {==}
    case Eng.KCt{}:
      {==}

def Laws.line_refuses(c, pd, out, e):
  line_bad(Eng.cls(c), c, pd, out, e)

def clen_bad(
  k: Eng.Cls, c: U32, v: U32, pd: Eng.Pend, out: List<&2, Eng.Req>,
  e: {Spec.in.clen(k) == False{} : Bool}
) -> {Eng.step.at(Eng.InL{v}, k, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}:
  match k:
    case Eng.KSp{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InL{v}, Eng.KSp{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KHt{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InL{v}, Eng.KHt{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KCr{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InL{v}, Eng.KCr{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KLf{}:
      {==}
    case Eng.KCo{}:
      {==}
    case Eng.KCm{}:
      {==}
    case Eng.KDg{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InL{v}, Eng.KDg{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KTk{}:
      {==}
    case Eng.KVc{}:
      {==}
    case Eng.KCt{}:
      {==}

def Laws.clen_refuses(c, v, pd, out, e):
  clen_bad(Eng.cls(c), c, v, pd, out, e)

def target_bad(
  k: Eng.Cls, c: U32, p: List<&2, U32>, pd: Eng.Pend, out: List<&2, Eng.Req>,
  e: {Spec.in.target(k) == False{} : Bool}
) -> {Eng.step.at(Eng.InT{p}, k, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}:
  match k:
    case Eng.KSp{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InT{p}, Eng.KSp{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KHt{}:
      {==}
    case Eng.KCr{}:
      {==}
    case Eng.KLf{}:
      {==}
    case Eng.KCo{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InT{p}, Eng.KCo{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KCm{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InT{p}, Eng.KCm{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KDg{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InT{p}, Eng.KDg{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KTk{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InT{p}, Eng.KTk{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KVc{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InT{p}, Eng.KVc{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KCt{}:
      {==}

def Laws.target_refuses(c, p, pd, out, e):
  target_bad(Eng.cls(c), c, p, pd, out, e)

def value_bad(
  k: Eng.Cls, c: U32, pd: Eng.Pend, out: List<&2, Eng.Req>,
  e: {Spec.in.value(k) == False{} : Bool}
) -> {Eng.step.at(Eng.InLx{}, k, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}:
  match k:
    case Eng.KSp{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLx{}, Eng.KSp{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KHt{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLx{}, Eng.KHt{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KCr{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLx{}, Eng.KCr{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KLf{}:
      {==}
    case Eng.KCo{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLx{}, Eng.KCo{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KCm{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLx{}, Eng.KCm{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KDg{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLx{}, Eng.KDg{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KTk{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLx{}, Eng.KTk{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KVc{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLx{}, Eng.KVc{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KCt{}:
      {==}

def Laws.value_refuses(c, pd, out, e):
  value_bad(Eng.cls(c), c, pd, out, e)

def conn_bad(
  k: Eng.Cls, c: U32, t: List<&2, U32>, a: Bool, b: Bool, pd: Eng.Pend, out: List<&2, Eng.Req>,
  e: {Spec.in.value(k) == False{} : Bool}
) -> {Eng.step.at(Eng.InLc{t, a, b}, k, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P}:
  match k:
    case Eng.KSp{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLc{t, a, b}, Eng.KSp{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KHt{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLc{t, a, b}, Eng.KHt{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KCr{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLc{t, a, b}, Eng.KCr{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KLf{}:
      {==}
    case Eng.KCo{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLc{t, a, b}, Eng.KCo{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KCm{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLc{t, a, b}, Eng.KCm{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KDg{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLc{t, a, b}, Eng.KDg{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KTk{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLc{t, a, b}, Eng.KTk{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KVc{}:
      %e : BD(_, Unit, {Eng.step.at(Eng.InLc{t, a, b}, Eng.KVc{}, c, pd, out) == Eng.P{Eng.Bad{}, pd, out} : Eng.P})
      Unit{}
    case Eng.KCt{}:
      {==}

def Laws.conn_refuses(c, t, a, b, pd, out, e):
  conn_bad(Eng.cls(c), c, t, a, b, pd, out, e)


def Laws.parse_get():
  {==}

def Laws.parse_body():
  {==}

def Laws.parse_hash_twin():
  {==}

def Laws.parse_agree():
  {==}

def Laws.parse_upgrade():
  {==}

def Laws.rest_upgrade():
  {==}

def Laws.refuse_space_colon():
  {==}

def Laws.refuse_te_space_colon():
  {==}

def Laws.refuse_te():
  {==}

def Laws.refuse_two_lengths():
  {==}

def Laws.refuse_wrap():
  {==}

def Laws.refuse_past_cap():
  {==}

def Laws.refuse_not_digits():
  {==}

def Laws.refuse_list():
  {==}

def Laws.refuse_fold():
  {==}

def Laws.refuse_bare_lf():
  {==}

def Laws.refuse_no_colon():
  {==}

def Laws.refuse_target_cr():
  {==}

def Laws.refuse_no_host():
  {==}

def Laws.refuse_two_hosts():
  {==}

def Laws.refuse_version():
  {==}

def Laws.refuse_after_one():
  {==}

def Laws.path_query():
  {==}

def Laws.health_closing():
  {==}

def Laws.health_is_built():
  {==}

def Laws.root_is_built():
  {==}

def Laws.missing_is_built():
  {==}

def Laws.method_is_built():
  {==}

def Laws.bad_is_built():
  {==}

def Laws.head_of_health():
  {==}

def Laws.head_of_missing():
  {==}

def Laws.route_health():
  {==}

def Laws.route_root():
  {==}

def Laws.route_echo():
  {==}

def Laws.route_events():
  {==}

def Laws.route_missing():
  {==}

def Laws.route_files():
  {==}

def Laws.route_files_index():
  {==}

def Laws.route_files_fixed():
  {==}

def Laws.routes_distinct():
  {==}

def Laws.routes_distinct_root():
  {==}

def Laws.route_empty(path):
  {==}

def Laws.norm_climb():
  {==}

def Laws.norm_deep_climb():
  {==}

def Laws.norm_dots():
  {==}

def Laws.norm_flat():
  {==}

# Once the normaliser has refused, nothing after revives the path.
def lem.norm_none(ss: List<&2, List<&2, U32>>) ->
  {None{} == Eng.norm.go(ss, None{}) : Maybe<&2, List<&2, List<&2, U32>>>}:
  match ss:
    case Nil{}:
      {==}
    case Con{s, t}:
      lem.norm_none(t)

def Laws.norm_climb_refused(ss):
  %lem.norm_none(ss) : {Eng.norm.rev(_) == None{} : Maybe<&2, List<&2, List<&2, U32>>>}
  {==}

def Laws.norm_climb_cancels(s, ss, e):
  %Equal.sym(Eng.Piece, Eng.piece(s), Eng.Name{}, e) :
    {Eng.norm.rev(Eng.norm.go(Con{[46, 46], ss}, Eng.norm.step(_, s, Nil{}))) ==
      Eng.norm(ss) : Maybe<&2, List<&2, List<&2, U32>>>}
  {==}

# path_safe: the rule LAWS.bend states is, segment by segment, the rule
# the guard in fnames.of checks, so whatever the guard lets through
# keeps it; the clean gate only ever refuses more.
def lem.bytes(bs: List<&2, U32>) -> {Laws.seg_bytes(bs) == Eng.fname.bytes(bs) : Bool}:
  match bs:
    case Nil{}:
      {==}
    case Con{c, t}:
      %lem.bytes(t) : {Bool.and(Laws.seg_byte(c), Laws.seg_bytes(t)) ==
        Bool.and(Eng.fname.byte(c), _) : Bool}
      {==}

def lem.seg(dot: Bool, s: List<&2, U32>) -> {Laws.seg_ok(dot, s) == Eng.fname.ok(dot, s) : Bool}:
  match dot:
    case True{}:
      match s:
        case Nil{}:
          {==}
        case Con{c, t}:
          %lem.bytes(Con{c, t}) : {Bool.and(Laws.seg_lead(True{}, c, Con{c, t}),
            Laws.seg_bytes(Con{c, t})) == Bool.and(Eng.fname.lead(True{}, c, Con{c, t}), _) : Bool}
          {==}
    case False{}:
      match s:
        case Nil{}:
          {==}
        case Con{c, t}:
          %lem.bytes(Con{c, t}) : {Bool.and(Laws.seg_lead(False{}, c, Con{c, t}),
            Laws.seg_bytes(Con{c, t})) == Bool.and(Eng.fname.lead(False{}, c, Con{c, t}), _) : Bool}
          {==}

def lem.segs(+dot: Bool, ss: List<&2, List<&2, U32>>) ->
  {Laws.segs_ok(dot, ss) == Eng.fnames.ok(dot, ss) : Bool}:
  match ss:
    case Nil{}:
      {==}
    case Con{s, t}:
      %lem.segs(dot, t) : {Bool.and(Laws.seg_ok(dot, s), Laws.segs_ok(dot, t)) ==
        Bool.and(Eng.fname.ok(dot, s), _) : Bool}
      %lem.seg(dot, s) : {Bool.and(Laws.seg_ok(dot, s), Laws.segs_ok(dot, t)) ==
        Bool.and(_, Laws.segs_ok(dot, t)) : Bool}
      {==}

def lem.keep(+dot: Bool, +ss: List<&2, List<&2, U32>>, b: Bool) ->
  {Eng.fnames.ok(dot, ss) == b : Bool} ->
  {Laws.safe(dot, Eng.fnames.keep(ss, b)) == True{} : Bool}:
  match b:
    case True{}:
      e => Equal.trans(Bool, Laws.segs_ok(dot, ss), Eng.fnames.ok(dot, ss), True{},
        lem.segs(dot, ss), e)
    case False{}:
      e => {==}

def lem.guard(+dot: Bool, may: Maybe<&2, List<&2, List<&2, U32>>>) ->
  {Laws.safe(dot, Eng.fnames.guard(dot, may)) == True{} : Bool}:
  match may:
    case None{}:
      {==}
    case Some{+ss}:
      lem.keep(dot, ss, Eng.fnames.ok(dot, ss))({==})

def lem.gate(+dot: Bool, ok: Bool, may: Maybe<&2, List<&2, List<&2, U32>>>) ->
  {Laws.safe(dot, may) == True{} : Bool} ->
  {Laws.safe(dot, Eng.fnames.gate(ok, may)) == True{} : Bool}:
  match ok:
    case True{}:
      h => h
    case False{}:
      h => {==}

def Laws.path_safe(dot, t):
  lem.gate(dot, Eng.clean(t), Eng.fnames.guard(dot, Eng.norm(Eng.segs(t))))(
    lem.guard(dot, Eng.norm(Eng.segs(t))))

# clean_refuses_control: a refused byte makes the running verdict False,
# and False stays False to the end of the target.
def lem.clean_false(bs: List<&2, U32>) -> {Eng.clean.go(bs, False{}) == False{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case Con{c, t}:
      lem.clean_false(t)

def lem.clean(
  a: List<&2, U32>, +b: List<&2, U32>, +c: U32,
  e: {(U32.is_lt(c, 32) || U32.is_eq(c, 127)) == True{} : Bool}, ok: Bool
) -> {Eng.clean.go(List.append(&2, U32, a, Con{c, b}), ok) == False{} : Bool}:
  match a:
    case Nil{}:
      match ok:
        case False{}:
          lem.clean_false(b)
        case True{}:
          %Equal.sym(Bool, (U32.is_lt(c, 32) || U32.is_eq(c, 127)), True{}, e) :
            {Eng.clean.go(b, Eng.clean.pick(_, c)) == False{} : Bool}
          lem.clean_false(b)
    case Con{+h, t}:
      lem.clean(t, b, c, e, Bool.and(ok, Eng.clean.pick(Eng.ctl(h), h)))

def Laws.clean_refuses_control(a, b, c, e):
  lem.clean(a, b, c, e, True{})

def Laws.unclean_names_nothing(dot, t, e):
  %Equal.sym(Bool, Eng.clean(t), False{}, e) :
    {Eng.fnames.gate(_, Eng.fnames.guard(dot, Eng.norm(Eng.segs(t)))) == None{} :
      Maybe<&2, List<&2, List<&2, U32>>>}
  {==}

def Laws.fnames_dotfile():
  {==}

def Laws.fnames_dotdir():
  {==}

def Laws.fnames_backslash():
  {==}

def Laws.fnames_nul():
  {==}

def Laws.fnames_dots():
  {==}

def Laws.fnames_plain():
  {==}

def Laws.sha1_empty():
  {==}

def Laws.sha1_abc():
  {==}

def Laws.sha1_two_blocks():
  {==}

def Laws.b64_empty():
  {==}

def Laws.b64_f():
  {==}

def Laws.b64_fo():
  {==}

def Laws.b64_foo():
  {==}

def Laws.b64_foob():
  {==}

def Laws.b64_fooba():
  {==}

def Laws.b64_foobar():
  {==}

def Laws.ws_accept():
  {==}

def Laws.ws_feed_split(a, b, w):
  match a:
    case Nil{}:
      {==}
    case Con{c, t}:
      Laws.ws_feed_split(t, b, Ws.step(w, c))

def Laws.ws_bad_absorbs(c, out):
  {==}

def Laws.ws_bad_feeds(s, out):
  match s:
    case Nil{}:
      {==}
    case Con{c, t}:
      Laws.ws_bad_feeds(t, out)

# ws_feed_buf: the two walks step the same machine on the same byte, so
# the cons case is the hypothesis on the stepped state.
def Laws.ws_feed_buf(b, w):
  match b:
    case SNil{}:
      {==}
    case SCon{Chr{c}, t}:
      Laws.ws_feed_buf(t, Ws.step(w, c))

# ws_feed_buf_split: through the lists. Each buffer walk is the list
# walk of its bytes, the bytes of a join are the join of the bytes, and
# the list reader splits.
def Laws.ws_feed_buf_split(a, b, w):
  Equal.trans(Ws.W, Ws.feed_buf(Bytes.append(a, b), w),
    Ws.feed(Bytes.to_list(Bytes.append(a, b)), w),
    Ws.feed_buf(b, Ws.feed_buf(a, w)),
    Laws.ws_feed_buf(Bytes.append(a, b), w),
    Equal.trans(Ws.W, Ws.feed(Bytes.to_list(Bytes.append(a, b)), w),
      Ws.feed(List.append(&2, U32, Bytes.to_list(a), Bytes.to_list(b)), w),
      Ws.feed_buf(b, Ws.feed_buf(a, w)),
      Equal.cong(List<&2, U32>, Ws.W, xs => Ws.feed(xs, w),
        Bytes.to_list(Bytes.append(a, b)),
        List.append(&2, U32, Bytes.to_list(a), Bytes.to_list(b)),
        Bytes.to_list_append(a, b)),
      Equal.trans(Ws.W,
        Ws.feed(List.append(&2, U32, Bytes.to_list(a), Bytes.to_list(b)), w),
        Ws.feed(Bytes.to_list(b), Ws.feed(Bytes.to_list(a), w)),
        Ws.feed_buf(b, Ws.feed_buf(a, w)),
        Laws.ws_feed_split(Bytes.to_list(a), Bytes.to_list(b), w),
        Equal.trans(Ws.W,
          Ws.feed(Bytes.to_list(b), Ws.feed(Bytes.to_list(a), w)),
          Ws.feed(Bytes.to_list(b), Ws.feed_buf(a, w)),
          Ws.feed_buf(b, Ws.feed_buf(a, w)),
          Equal.cong(Ws.W, Ws.W, v => Ws.feed(Bytes.to_list(b), v),
            Ws.feed(Bytes.to_list(a), w), Ws.feed_buf(a, w),
            Equal.sym(Ws.W, Ws.feed_buf(a, w), Ws.feed(Bytes.to_list(a), w),
              Laws.ws_feed_buf(a, w))),
          Equal.sym(Ws.W, Ws.feed_buf(b, Ws.feed_buf(a, w)),
            Ws.feed(Bytes.to_list(b), Ws.feed_buf(a, w)),
            Laws.ws_feed_buf(b, Ws.feed_buf(a, w)))))))

def Laws.ws_bad_feeds_buf(s, out):
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{c}, t}:
      Laws.ws_bad_feeds_buf(t, out)

def Laws.ws_read_text():
  {==}

def Laws.ws_read_ping():
  {==}

def Laws.ws_read_text_buf():
  {==}

def Laws.ws_read_text_buf_cut():
  {==}

def Laws.ws_read_ping_buf():
  {==}

def Laws.ws_unmasked_is_bad():
  {==}

def Laws.ws_fragment_is_bad():
  {==}

def Laws.ws_reserved_is_bad():
  {==}

def Laws.ws_unmasked_is_bad_buf():
  {==}

def Laws.ws_fragment_is_bad_buf():
  {==}

def Laws.ws_reserved_is_bad_buf():
  {==}

def Laws.ws_frame_short():
  {==}

def Laws.ws_len_two_bytes():
  {==}

def Laws.ws_close_code():
  {==}

# batch_under: the comparison is generalised with its equation. Below
# the cap what stays is k, and the equation says k is below it; at or
# past it what stays is 0, which the checker compares with the cap.
law batch_under.go:
  for +k: U32
  for +c: Cmp
  for e: {c == U32.cmp(k, Eng.send.cap()) : Cmp}
  {U32.is_lt(Eng.batch.keep(c, k), Eng.send.cap()) == True{} : Bool}

def batch_under.go(k, c, e):
  match c:
    case LT{}:
      %e : {Cmp.is_lt(_) == True{} : Bool}
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def Laws.batch_under(k):
  batch_under.go(k, U32.cmp(k, Eng.send.cap()), {==})

# long_at and long_past: long walks the count and the list together, so
# each step of the list is a step of the count
def Laws.long_at(bs):
  match bs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Laws.long_at(t)

def Laws.long_past(bs, c):
  match bs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Laws.long_past(t, h)

def Laws.hw_rest(hw):
  {==}

def Laws.hw_keeps(t0, n):
  {==}

def Laws.key_rfc():
  {==}

def Laws.key_short():
  {==}

def Laws.key_alphabet():
  {==}

def Laws.key_padding():
  {==}

def Laws.parse_version_13():
  {==}

def Laws.parse_version_other():
  {==}
