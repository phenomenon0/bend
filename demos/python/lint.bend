# Proofs-as-lint over the parser's wire AST (S.Json). L1: the totality fragment
# T0 and local reachability. `certificate` is the trusted kernel: it recomputes
# every condition from the actual AST and contracts; a witness only supplies
# call ranks. `analyze` is untrusted search in front of it. See SOUNDNESS.md.
# L2: the ownership fragment O0 (`own`, the same kernel) and the alias/effect
# advisories (`alias`). Coverage (finite match domains) is lane L3; module
# summaries are L4.
import Base
import ./syntax.bend as S
import ./nodes.bend as N

type Grade is Data:
  Proven{}
  Refuted{}
  Unknown{}
  Advisory{}

type Diag is Data:
  Diag{loc: S.Json, rule: String, grade: Grade, msg: String}

# A primitive's contract is an assumption about CPython (SOUNDNESS.md, A3);
# a call is granted it only at this arity and only if pure and total.
type Contract is Data:
  Contract{name: String, arity: Nat, pure: Bool, total: Bool}

# One witness entry: every resolved callee must hold a strictly smaller rank.
type Rank is Data:
  Rank{name: String, rank: Nat}

type Fact is Data:
  Bad{loc: S.Json, why: String}
  Calls{name: String}

type Env is Data:
  Env{locals: List<&2, String>, defs: List<&2, String>, contracts: List<&2, Contract>}

def contracts() -> List<&2, Contract>:
  [Contract{"len", 1n, True{}, True{}}, Contract{"str", 1n, True{}, True{}},
   Contract{"bool", 1n, True{}, True{}}, Contract{"sorted", 1n, True{}, True{}}]

# ---- helpers ----

def count(xs: List<&2, String>, +k: String) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      Nat.add(Bool.pick(Nat, String.eq(h, k), 1n, 0n), count(t, k))

def has(xs: List<&2, String>, +k: String) -> Bool:
  Nat.is_gt(count(xs, k), 0n)

def field(j: S.Json, key: String) -> S.Json:
  match j:
    case S.JObj{fs}:
      N.get(fs, key)
    case _:
      S.JNull{}

def tag_of(j: S.Json) -> String:
  N.string(field(j, "tag"))

def is_null(j: S.Json) -> Bool:
  match j:
    case S.JNull{}:
      True{}
    case _:
      False{}

def is_empty(j: S.Json) -> Bool:
  match j:
    case S.JArr{S.JEnd{}}:
      True{}
    case _:
      False{}

def items(j: S.Json) -> S.Json:
  match j:
    case S.JArr{xs}:
      xs
    case _:
      S.JEnd{}

def size(xs: S.Json) -> Nat:
  match xs:
    case S.JItem{h, t}:
      1n+size(t)
    case _:
      0n

def line(loc: S.Json) -> Nat:
  match loc:
    case S.JArr{S.JItem{S.JNum{l}, rest}}:
      l
    case _:
      0n

def col(loc: S.Json) -> Nat:
  match loc:
    case S.JArr{S.JItem{l, S.JItem{S.JNum{c}, rest}}}:
      c
    case _:
      0n

def at(+loc: S.Json) -> String:
  " at " ++ Nat.show(line(loc)) ++ ":" ++ Nat.show(col(loc))

def contract(cs: List<&2, Contract>, +k: String) -> Maybe<&2, Contract>:
  match cs:
    case Nil{}:
      None{}
    case Contract{+name, arity, pure, total} <> t:
      S.choose(Maybe<&2, Contract>, String.eq(name, k), u => Some{Contract{name, arity, pure, total}}, u => contract(t, k))

def rank(w: List<&2, Rank>, +k: String) -> Maybe<&2, Nat>:
  match w:
    case Nil{}:
      None{}
    case Rank{name, r} <> t:
      S.choose(Maybe<&2, Nat>, String.eq(name, k), u => Some{r}, u => rank(t, k))

# ---- resolve: bindings and call targets ----

# Every name a function binds: parameters and Store targets.
def binds(j: S.Json) -> List<&2, String>:
  match j:
    case S.JObj{+fs}:
      +tag = N.string(N.get(fs, "tag"))
      own = S.choose(List<&2, String>, String.eq(tag, "arg"), u => [N.string(N.get(fs, "arg"))], u =>
        S.choose(List<&2, String>, String.eq(tag, "Name") && String.eq(tag_of(N.get(fs, "ctx")), "Store"), u =>
          [N.string(N.get(fs, "id"))], u => []))
      List.append(&2, String, own, binds(fs))
    case S.JField{key, value, rest}:
      List.append(&2, String, binds(value), binds(rest))
    case S.JArr{xs}:
      binds(xs)
    case S.JItem{h, t}:
      List.append(&2, String, binds(h), binds(t))
    case _:
      []

def granted(c: Maybe<&2, Contract>, +id: String, +n: Nat, +loc: S.Json) -> List<&2, Fact>:
  match c:
    case None{}:
      [Bad{loc, "unresolved call " ++ id ++ at(loc)}]
    case Some{Contract{name, arity, pure, total}}:
      S.choose(List<&2, Fact>, pure && total && Nat.is_eq(arity, n), u => [], u =>
        [Bad{loc, "contract of " ++ id ++ " does not grant this call" ++ at(loc)}])

# The callee of Call{func, args, ..}: spelling is not authority. A local or a
# module def of a contracted name revokes the contract; only a unique module
# def or an unshadowed contracted primitive resolves.
def callee(+func: S.Json, +args: S.Json, +env: Env) -> List<&2, Fact>:
  Env{locals, defs, +cs} = env
  +loc = field(func, "_loc")
  +id = N.string(field(func, "id"))
  +n = count(defs, id)
  S.choose(List<&2, Fact>, Bool.not(String.eq(tag_of(func), "Name")), u =>
    [Bad{loc, "dynamic call" ++ at(loc)}], u =>
    S.choose(List<&2, Fact>, (has(locals, id) || Nat.is_gt(n, 0n)) && Maybe.is_some(&2, Contract, contract(cs, id)), u =>
      [Bad{loc, "shadowed builtin " ++ id ++ at(loc)}], u =>
      S.choose(List<&2, Fact>, has(locals, id), u =>
        [Bad{loc, "call through local " ++ id ++ at(loc)}], u =>
        S.choose(List<&2, Fact>, Nat.is_eq(n, 1n), u => [Calls{id}], u =>
          S.choose(List<&2, Fact>, Nat.is_gt(n, 1n), u =>
            [Bad{loc, "ambiguous def " ++ id ++ at(loc)}], u =>
            granted(contract(cs, id), id, size(items(args)), loc))))))

# ---- effects and termination: fragment membership ----

# Pure, non-mutating forms plus For (a structural fold: nothing in the fragment
# mutates, so the iterated str/list is finite and fixed; Break/Continue only
# shorten it).
def admitted(+t: String) -> Bool:
  has(["Return", "Assign", "If", "For", "Break", "Continue", "Pass", "Expr", "Name", "Constant", "BoolOp", "UnaryOp",
    "BinOp", "Compare", "IfExp", "List", "Call", "Load", "Store", "And", "Or", "Not", "Add",
    "Eq", "NotEq", "Lt", "LtE", "Gt", "GtE", "Is", "IsNot", "In", "NotIn"], t)

def judge(+tag: String, +fs: S.Json, +loc: S.Json, +env: Env) -> List<&2, Fact>:
  Env{locals, defs, cs} = env
  +id = N.string(N.get(fs, "id"))
  S.choose(List<&2, Fact>, String.eq(tag, "While"), u =>
    [Bad{loc, "unbounded loop While" ++ at(loc)}], u =>
    S.choose(List<&2, Fact>, Bool.not(admitted(tag)), u =>
      [Bad{loc, "outside fragment: " ++ tag ++ at(loc)}], u =>
      S.choose(List<&2, Fact>, String.eq(tag, "Name") && String.eq(tag_of(N.get(fs, "ctx")), "Load") && Bool.not(has(locals, id)), u =>
        [Bad{loc, "unresolved name " ++ id ++ at(loc)}], u => [])))

# `near` is the closest enclosing span: operator nodes carry none.
def scan(j: S.Json, +parent: String, +near: S.Json, +env: Env) -> List<&2, Fact>:
  match j:
    case S.JObj{+fs}:
      +tag = N.string(N.get(fs, "tag"))
      +own = N.get(fs, "_loc")
      +loc = S.choose(S.Json, is_null(own), u => near, u => own)
      List.append(&2, Fact, judge(tag, fs, loc, env), scan(fs, tag, loc, env))
    case S.JField{+key, +value, +rest}:
      S.choose(List<&2, Fact>, String.eq(parent, "Call") && String.eq(key, "func"), u =>
        List.append(&2, Fact, callee(value, N.get(rest, "args"), env), scan(rest, parent, near, env)), u =>
        List.append(&2, Fact, scan(value, "", near, env), scan(rest, parent, near, env)))
    case S.JArr{xs}:
      scan(xs, "", near, env)
    case S.JItem{h, t}:
      List.append(&2, Fact, scan(h, "", near, env), scan(t, "", near, env))
    case _:
      []

# Annotations state assumption A1: str, bool, int, list[T], T | None.
def ann_ok(j: S.Json, +names: List<&2, String>, +tags: List<&2, String>) -> Bool:
  match j:
    case S.JObj{+fs}:
      +tag = N.string(N.get(fs, "tag"))
      S.choose(Bool, String.eq(tag, "Name"), u => has(names, N.string(N.get(fs, "id"))), u =>
        S.choose(Bool, String.eq(tag, "Constant"), u => String.eq(N.string(N.get(fs, "_raw")), "None"), u =>
          has(tags, tag) && ann_ok(fs, names, tags)))
    case S.JField{key, value, rest}:
      ann_ok(value, names, tags) && ann_ok(rest, names, tags)
    case _:
      True{}

def typed(+j: S.Json) -> Bool:
  Bool.not(is_null(j)) && ann_ok(j, ["str", "bool", "int", "list"], ["Subscript", "BinOp", "BitOr", "Load"])

def all_typed(xs: S.Json) -> Bool:
  match xs:
    case S.JItem{h, t}:
      typed(field(h, "annotation")) && all_typed(t)
    case _:
      True{}

def header(+f: S.Json) -> List<&2, Fact>:
  +a = field(f, "args")
  +loc = field(f, "_loc")
  plain = is_empty(field(f, "decorator_list")) && is_empty(field(a, "posonlyargs")) && is_empty(field(a, "kwonlyargs")) &&
    is_empty(field(a, "defaults")) && is_null(field(a, "vararg")) && is_null(field(a, "kwarg"))
  S.choose(List<&2, Fact>, Bool.not(plain), u => [Bad{loc, "decorated or non-simple parameters"}], u =>
    S.choose(List<&2, Fact>, all_typed(items(field(a, "args"))) && typed(field(f, "returns")), u => [], u =>
      [Bad{loc, "missing or non-builtin annotation"}]))

# A closed module: defs and a docstring only, so module globals after import
# are exactly the def names (A2).
def closed(xs: S.Json) -> List<&2, Fact>:
  match xs:
    case S.JItem{+h, t}:
      +tag = tag_of(h)
      ok = String.eq(tag, "FunctionDef") || (String.eq(tag, "Expr") && String.eq(tag_of(field(h, "value")), "Constant"))
      List.append(&2, Fact, S.choose(List<&2, Fact>, ok, u => [], u =>
        [Bad{field(h, "_loc"), "module not closed: " ++ tag ++ at(field(h, "_loc"))}]), closed(t))
    case _:
      []

def def_names(xs: S.Json) -> List<&2, String>:
  match xs:
    case S.JItem{+h, t}:
      List.append(&2, String, S.choose(List<&2, String>, String.eq(tag_of(h), "FunctionDef"), u =>
        [N.string(field(h, "name"))], u => []), def_names(t))
    case _:
      []

def find_def(xs: S.Json, +name: String) -> S.Json:
  match xs:
    case S.JItem{+h, t}:
      S.choose(S.Json, String.eq(tag_of(h), "FunctionDef") && String.eq(N.string(field(h, "name")), name), u => h, u =>
        find_def(t, name))
    case _:
      S.JNull{}

def consts(xs: S.Json) -> Bool:
  match xs:
    case S.JItem{+h, t}:
      String.eq(tag_of(h), "Constant") && has(["None", "True", "False"], N.string(field(h, "_raw"))) && consts(t)
    case _:
      True{}

def any_tag(xs: S.Json, +tags: List<&2, String>) -> Bool:
  match xs:
    case S.JItem{h, t}:
      has(tags, tag_of(h)) || any_tag(t, tags)
    case _:
      False{}

# O0's extra condition: `is` observes sharing, except against None/True/False.
def ident(j: S.Json) -> List<&2, Fact>:
  match j:
    case S.JObj{+fs}:
      +loc = N.get(fs, "_loc")
      bad = String.eq(N.string(N.get(fs, "tag")), "Compare") && any_tag(items(N.get(fs, "ops")), ["Is", "IsNot"]) &&
        Bool.not(consts(items(N.get(fs, "comparators"))))
      List.append(&2, Fact, S.choose(List<&2, Fact>, bad, u => [Bad{loc, "identity comparison observes sharing" ++ at(loc)}], u => []), ident(fs))
    case S.JField{key, value, rest}:
      List.append(&2, Fact, ident(value), ident(rest))
    case S.JArr{xs}:
      ident(xs)
    case S.JItem{h, t}:
      List.append(&2, Fact, ident(h), ident(t))
    case _:
      []

# Every condition of "name is in T0" (`o`: in O0), recomputed from the AST.
def check_fn(+body: S.Json, +cs: List<&2, Contract>, +name: String, o: Bool) -> List<&2, Fact>:
  +f = find_def(body, name)
  +defs = def_names(body)
  unique = S.choose(List<&2, Fact>, Nat.is_eq(count(defs, name), 1n), u => [], u =>
    [Bad{field(f, "_loc"), "no unique def " ++ name}])
  List.append(&2, Fact, closed(body), List.append(&2, Fact, unique, List.append(&2, Fact, header(f),
    List.append(&2, Fact, scan(field(f, "body"), "", field(f, "_loc"), Env{binds(f), defs, cs}),
      S.choose(List<&2, Fact>, o, u => ident(f), u => [])))))

# ---- verify: the kernel ----

# "" when every fact is discharged: no Bad, every callee ranked below `r`.
def discharge(fs: List<&2, Fact>, +w: List<&2, Rank>, +r: Nat) -> String:
  match fs:
    case Nil{}:
      ""
    case Bad{loc, why} <> t:
      why
    case Calls{+g} <> t:
      S.choose(String, Nat.is_lt(Maybe.default(&2, Nat, rank(w, g), r), r), u => discharge(t, w, r), u =>
        "callee " ++ g ++ " holds no smaller rank")

def entries(es: List<&2, Rank>, +w: List<&2, Rank>, +body: S.Json, +cs: List<&2, Contract>, +o: Bool) -> String:
  match es:
    case Nil{}:
      ""
    case Rank{+name, +r} <> t:
      +why = discharge(check_fn(body, cs, name, o), w, r)
      S.choose(String, String.is_empty(why), u => entries(t, w, body, cs, o), u => name ++ ": " ++ why)

# "" iff every entry of the witness checks against the actual AST/contracts.
# By induction on rank every entry is then total (SOUNDNESS.md, T0).
def certificate(m: S.Module, +cs: List<&2, Contract>, +w: List<&2, Rank>, +o: Bool) -> String:
  S.Module{body} = m
  entries(w, w, body, cs, o)

def def_loc(m: S.Module, name: String) -> S.Json:
  S.Module{body} = m
  field(find_def(body, name), "_loc")

def rule_of(o: Bool) -> String:
  Bool.pick(String, o, "ownership", "total")

def holds(o: Bool) -> String:
  Bool.pick(String, o, "value semantics is faithful: no mutation, identity test or retained reference (O0)",
    "terminates on exact built-in arguments (T0)")

# The witness entry is consulted first, so no entry means no proof by
# computation alone (the law below).
def verdict(entry: Maybe<&2, Nat>, +m: S.Module, +cs: List<&2, Contract>, +w: List<&2, Rank>, +name: String, +o: Bool) -> Diag:
  match entry:
    case None{}:
      Diag{def_loc(m, name), rule_of(o), Unknown{}, "no certificate"}
    case Some{r}:
      +why = certificate(m, cs, w, o)
      S.choose(Diag, String.is_empty(why), u =>
        Diag{def_loc(m, name), rule_of(o), Proven{}, holds(o)}, u =>
        Diag{def_loc(m, name), rule_of(o), Refuted{}, "certificate refuted: " ++ why})

def verify(+m: S.Module, +cs: List<&2, Contract>, +w: List<&2, Rank>, +name: String) -> Diag:
  verdict(rank(w, name), m, cs, w, name, False{})

# The same kernel over O0 = T0 without identity tests (SOUNDNESS.md, O0).
def own(+m: S.Module, +cs: List<&2, Contract>, +w: List<&2, Rank>, +name: String) -> Diag:
  verdict(rank(w, name), m, cs, w, name, True{})

def is_proven(d: Diag) -> Bool:
  match d:
    case Diag{loc, rule, Proven{}, msg}:
      True{}
    case _:
      False{}

# A certificate is required: with none, nothing is ever Proven.
law no_certificate_no_proof:
  for +m: S.Module
  for +cs: List<&2, Contract>
  for +name: String
  {is_proven(verify(m, cs, Nil{}, name)) == False{} : Bool}

def no_certificate_no_proof(m, cs, name):
  {==}

law no_certificate_no_ownership:
  for +m: S.Module
  for +cs: List<&2, Contract>
  for +name: String
  {is_proven(own(m, cs, Nil{}, name)) == False{} : Bool}

def no_certificate_no_ownership(m, cs, name):
  {==}

# ---- analyze: untrusted witness search, then the kernel ----

def why_not(fs: List<&2, Fact>, +w: List<&2, Rank>) -> String:
  match fs:
    case Nil{}:
      ""
    case Bad{loc, why} <> t:
      why
    case Calls{+g} <> t:
      S.choose(String, Maybe.is_some(&2, Nat, rank(w, g)), u => why_not(t, w), u =>
        "callee " ++ g ++ " is not proven (cycle or Unknown)")

# One round: rank `r` for each unranked def whose callees were ranked earlier.
def round(names: List<&2, String>, +w: List<&2, Rank>, +body: S.Json, +cs: List<&2, Contract>, +o: Bool, +r: Nat) -> List<&2, Rank>:
  match names:
    case Nil{}:
      []
    case +h <> t:
      ok = Maybe.is_none(&2, Nat, rank(w, h)) && String.is_empty(why_not(check_fn(body, cs, h, o), w))
      List.append(&2, Rank, S.choose(List<&2, Rank>, ok, u => [Rank{h, r}], u => []), round(t, w, body, cs, o, r))

def infer(fuel: Nat, +names: List<&2, String>, +w: List<&2, Rank>, +body: S.Json, +cs: List<&2, Contract>, +o: Bool, +r: Nat) -> List<&2, Rank>:
  match fuel:
    case 0n:
      w
    case 1n+p:
      infer(p, names, List.append(&2, Rank, w, round(names, w, body, cs, o, r)), body, cs, o, 1n+r)

def totals(names: List<&2, String>, +w: List<&2, Rank>, +valid: Bool, +body: S.Json, +cs: List<&2, Contract>, +o: Bool) -> List<&2, Diag>:
  match names:
    case Nil{}:
      []
    case +h <> t:
      +loc = field(find_def(body, h), "_loc")
      d = S.choose(Diag, valid && Maybe.is_some(&2, Nat, rank(w, h)), u =>
        Diag{loc, rule_of(o), Proven{}, holds(o)}, u =>
        Diag{loc, rule_of(o), Unknown{}, why_not(check_fn(body, cs, h, o), w)})
      d <> totals(t, w, valid, body, cs, o)

# Advisory: a binding spelled like a contracted primitive.
def shadows(j: S.Json, +cs: List<&2, Contract>) -> List<&2, Diag>:
  match j:
    case S.JObj{+fs}:
      +tag = N.string(N.get(fs, "tag"))
      +id = S.choose(String, String.eq(tag, "arg"), u => N.string(N.get(fs, "arg")), u =>
        S.choose(String, String.eq(tag, "FunctionDef"), u => N.string(N.get(fs, "name")), u =>
          S.choose(String, String.eq(tag, "Name") && String.eq(tag_of(N.get(fs, "ctx")), "Store"), u =>
            N.string(N.get(fs, "id")), u => "")))
      List.append(&2, Diag, S.choose(List<&2, Diag>, Maybe.is_some(&2, Contract, contract(cs, id)), u =>
        [Diag{N.get(fs, "_loc"), "shadowed-builtin", Advisory{}, id ++ " is rebound; calls to it are not granted the builtin's contract"}], u => []),
        shadows(fs, cs))
    case S.JField{key, value, rest}:
      List.append(&2, Diag, shadows(value, cs), shadows(rest, cs))
    case S.JArr{xs}:
      shadows(xs, cs)
    case S.JItem{h, t}:
      List.append(&2, Diag, shadows(h, cs), shadows(t, cs))
    case _:
      []

# Local reachability R0: the statement after an unconditional transfer in the
# same block never runs (finally bodies run, but control does not come back).
def after(+h: S.Json, t: S.Json) -> List<&2, Diag>:
  match t:
    case S.JItem{next, rest}:
      +tag = tag_of(h)
      +loc = field(next, "_loc")
      S.choose(List<&2, Diag>, has(["Return", "Raise", "Break", "Continue"], tag), u =>
        [Diag{loc, "unreachable", Proven{}, "follows " ++ tag ++ " in the same block"}], u =>
        S.choose(List<&2, Diag>, String.eq(tag, "While") && String.eq(N.string(field(field(h, "test"), "_raw")), "True"), u =>
          [Diag{loc, "unreachable", Unknown{}, "follows while True; break analysis is outside R0"}], u => []))
    case _:
      []

def dead(j: S.Json) -> List<&2, Diag>:
  match j:
    case S.JObj{fs}:
      dead(fs)
    case S.JField{key, value, rest}:
      List.append(&2, Diag, dead(value), dead(rest))
    case S.JArr{xs}:
      dead(xs)
    case S.JItem{+h, +t}:
      List.append(&2, Diag, after(h, t), List.append(&2, Diag, dead(h), dead(t)))
    case _:
      []

# ---- deterministic order and rendering ----

def le(a: Diag, b: Diag) -> Bool:
  Diag{+la, ra, ga, ma} = a
  Diag{+lb, rb, gb, mb} = b
  +l1 = line(la)
  +l2 = line(lb)
  +c1 = col(la)
  +c2 = col(lb)
  Nat.is_lt(l1, l2) || (Nat.is_eq(l1, l2) && (Nat.is_lt(c1, c2) || (Nat.is_eq(c1, c2) && String.is_le(ra, rb))))

def grade(g: Grade) -> String:
  match g:
    case Proven{}:
      "Proven"
    case Refuted{}:
      "Refuted"
    case Unknown{}:
      "Unknown"
    case Advisory{}:
      "Advisory"

def span(loc: S.Json) -> String:
  match loc:
    case S.JArr{S.JItem{S.JNum{a}, S.JItem{S.JNum{b}, S.JItem{S.JNum{c}, S.JItem{S.JNum{d}, rest}}}}}:
      Nat.show(a) ++ ":" ++ Nat.show(b) ++ "-" ++ Nat.show(c) ++ ":" ++ Nat.show(d)
    case _:
      "?"

def show(+path: String, d: Diag) -> String:
  Diag{loc, rule, g, msg} = d
  path ++ ":" ++ span(loc) ++ " " ++ rule ++ " " ++ grade(g) ++ " " ++ msg

def render(+path: String, ds: List<&2, Diag>) -> String:
  match ds:
    case Nil{}:
      ""
    case h <> t:
      show(path, h) ++ "\n" ++ render(path, t)

def analyze(+m: S.Module, +cs: List<&2, Contract>) -> List<&2, Diag>:
  S.Module{+body} = m
  +names = def_names(body)
  +w = infer(List.length(&2, String, names), names, [], body, cs, False{}, 0n)
  +valid = String.is_empty(certificate(m, cs, w, False{}))
  List.sort(~Diag, ~le, List.append(&2, Diag, totals(names, w, valid, body, cs, False{}),
    List.append(&2, Diag, shadows(body, cs), dead(body))))

# ---- L2: alias/effect advisories (no certificate, no guarantee) ----

# What one function body says about names. May-alias is flow-insensitive
# (branch joins and rebinding both merge), so repeated use is never an event.
type Ev is Data:
  Edge{x: String, y: String, loc: S.Json}
  Bind{name: String, val: S.Json, imm: Bool}
  Mut{name: String, loc: S.Json, how: String}
  Esc{name: String, loc: S.Json, how: String}
  Use{name: String, loc: S.Json}

def mutators() -> List<&2, String>:
  ["append", "extend", "insert", "pop", "remove", "clear", "sort", "reverse", "update", "add", "discard", "setdefault", "popitem"]

# Names an expression may evaluate to: `a`, `a if c else d`, `a or d`.
def sources(j: S.Json, +parent: String) -> List<&2, String>:
  match j:
    case S.JObj{+fs}:
      +tag = N.string(N.get(fs, "tag"))
      S.choose(List<&2, String>, String.eq(tag, "Name"), u => [N.string(N.get(fs, "id"))], u =>
        S.choose(List<&2, String>, has(["IfExp", "BoolOp"], tag), u => sources(fs, tag), u => []))
    case S.JField{key, value, +rest}:
      S.choose(List<&2, String>, has(["body", "orelse", "values"], key), u =>
        List.append(&2, String, sources(value, ""), sources(rest, parent)), u => sources(rest, parent))
    case S.JArr{xs}:
      sources(xs, "")
    case S.JItem{h, t}:
      List.append(&2, String, sources(h, ""), sources(t, ""))
    case _:
      []

def edges(ys: List<&2, String>, +x: String, +loc: S.Json) -> List<&2, Ev>:
  match ys:
    case Nil{}:
      []
    case y <> t:
      Edge{x, y, loc} <> edges(t, x, loc)

def first(xs: S.Json) -> S.Json:
  match xs:
    case S.JItem{h, t}:
      h
    case _:
      S.JNull{}

# The name bound by `b = v`, `b: T = v` or `b += v`; "" for any other target.
def bound(+tag: String, +fs: S.Json) -> String:
  +ts = items(N.get(fs, "targets"))
  +t = S.choose(S.Json, String.eq(tag, "Assign"), u =>
    S.choose(S.Json, Nat.is_eq(size(ts), 1n), u => first(ts), u => S.JNull{}), u =>
    S.choose(S.Json, has(["AnnAssign", "AugAssign"], tag), u => N.get(fs, "target"), u => S.JNull{}))
  S.choose(String, String.eq(tag_of(t), "Name"), u => N.string(field(t, "id")), u => "")

def quiet(fs: List<&2, Fact>, +safe: List<&2, String>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case Bad{loc, why} <> t:
      False{}
    case Calls{g} <> t:
      has(safe, g) && quiet(t, safe)

def escapes(xs: S.Json, +how: String) -> List<&2, Ev>:
  match xs:
    case S.JItem{+h, t}:
      List.append(&2, Ev, S.choose(List<&2, Ev>, String.eq(tag_of(h), "Name"), u =>
        [Esc{N.string(field(h, "id")), field(h, "_loc"), how}], u => []), escapes(t, how))
    case _:
      []

# A call mutates its receiver by method spelling (advisory: spelling is not
# authority) and lets its Name arguments escape unless the callee is a granted
# pure primitive or an O0-certified def (`safe`).
def call(+fs: S.Json, +loc: S.Json, +env: Env, +safe: List<&2, String>) -> List<&2, Ev>:
  +func = N.get(fs, "func")
  +recv = field(func, "value")
  +attr = N.string(field(func, "attr"))
  +method = String.eq(tag_of(func), "Attribute")
  how = "passed to " ++ S.choose(String, method, u => "." ++ attr, u =>
    S.choose(String, String.eq(tag_of(func), "Name"), u => N.string(field(func, "id")), u => "a dynamic call"))
  List.append(&2, Ev, S.choose(List<&2, Ev>, method && String.eq(tag_of(recv), "Name") && has(mutators(), attr), u =>
    [Mut{N.string(field(recv, "id")), loc, "." ++ attr}], u => []),
    S.choose(List<&2, Ev>, quiet(callee(func, N.get(fs, "args"), env), safe), u => [], u => escapes(items(N.get(fs, "args")), how)))

def notes(+tag: String, +fs: S.Json, +env: Env, +safe: List<&2, String>) -> List<&2, Ev>:
  +loc = N.get(fs, "_loc")
  +id = N.string(N.get(fs, "id"))
  +ctx = tag_of(N.get(fs, "ctx"))
  +b = bound(tag, fs)
  +held = N.get(fs, "value")
  +note = N.get(fs, "annotation")
  S.choose(List<&2, Ev>, String.eq(tag, "arg"), u =>
    [Bind{N.string(N.get(fs, "arg")), S.JNull{}, Bool.not(is_null(note)) && ann_ok(note, ["str", "bool", "int"], ["BinOp", "BitOr", "Load"])}], u =>
    S.choose(List<&2, Ev>, Bool.not(String.is_empty(b)), u =>
      Bind{b, held, False{}} <> List.append(&2, Ev, edges(sources(held, ""), b, loc),
        S.choose(List<&2, Ev>, String.eq(tag, "AugAssign"), u => [Mut{b, loc, "augmented assignment"}], u => [])), u =>
      S.choose(List<&2, Ev>, String.eq(tag, "Name"), u =>
        S.choose(List<&2, Ev>, String.eq(ctx, "Load"), u => [Use{id, loc}], u => [Bind{id, S.JNull{}, False{}}]), u =>
        S.choose(List<&2, Ev>, has(["Subscript", "Attribute"], tag) && has(["Store", "Del"], ctx) && String.eq(tag_of(held), "Name"), u =>
          [Mut{N.string(field(held, "id")), loc, "item or attribute store"}], u =>
          S.choose(List<&2, Ev>, String.eq(tag, "Call"), u => call(fs, loc, env, safe), u => [])))))

# `skip`: the plain Name target of a binding is already a Bind with its value.
def walk(j: S.Json, +skip: Bool, +env: Env, +safe: List<&2, String>) -> List<&2, Ev>:
  match j:
    case S.JObj{+fs}:
      +tag = N.string(N.get(fs, "tag"))
      List.append(&2, Ev, notes(tag, fs, env, safe), walk(fs, Bool.not(String.is_empty(bound(tag, fs))), env, safe))
    case S.JField{key, value, +rest}:
      S.choose(List<&2, Ev>, skip && has(["targets", "target"], key), u => walk(rest, skip, env, safe), u =>
        List.append(&2, Ev, walk(value, False{}, env, safe), walk(rest, skip, env, safe)))
    case S.JArr{xs}:
      walk(xs, False{}, env, safe)
    case S.JItem{h, t}:
      List.append(&2, Ev, walk(h, False{}, env, safe), walk(t, False{}, env, safe))
    case _:
      []

# Immutable reuse: an expression over constants, operators and immutable names
# is immutable on exact str/bool/int/None (A1).
def imm_expr(j: S.Json, +imm: List<&2, String>) -> Bool:
  match j:
    case S.JObj{+fs}:
      +tag = N.string(N.get(fs, "tag"))
      S.choose(Bool, String.eq(tag, "Name"), u => has(imm, N.string(N.get(fs, "id"))), u =>
        has(["Constant", "BinOp", "BoolOp", "UnaryOp", "Compare", "IfExp", "Load", "And", "Or", "Not", "USub", "UAdd", "Add", "Sub",
          "Mult", "Div", "FloorDiv", "Mod", "Pow", "Eq", "NotEq", "Lt", "LtE", "Gt", "GtE", "Is", "IsNot", "In", "NotIn"], tag) &&
          imm_expr(fs, imm))
    case S.JField{key, value, rest}:
      imm_expr(value, imm) && imm_expr(rest, imm)
    case S.JArr{xs}:
      imm_expr(xs, imm)
    case S.JItem{h, t}:
      imm_expr(h, imm) && imm_expr(t, imm)
    case _:
      True{}

def bound_imm(es: List<&2, Ev>, +n: String, +imm: List<&2, String>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Bind{name, +val, ok} <> t:
      (Bool.not(String.eq(name, n)) || ok || (Bool.not(is_null(val)) && imm_expr(val, imm))) && bound_imm(t, n, imm)
    case Edge{x, y, loc} <> t:
      bound_imm(t, n, imm)
    case Mut{name, loc, how} <> t:
      bound_imm(t, n, imm)
    case Esc{name, loc, how} <> t:
      bound_imm(t, n, imm)
    case Use{name, loc} <> t:
      bound_imm(t, n, imm)

def keep(ns: List<&2, String>, +es: List<&2, Ev>, +imm: List<&2, String>) -> List<&2, String>:
  match ns:
    case Nil{}:
      []
    case +h <> t:
      List.append(&2, String, S.choose(List<&2, String>, bound_imm(es, h, imm), u => [h], u => []), keep(t, es, imm))

# Greatest fixpoint: start from every bound name, drop what has a mutable binding.
def settle(fuel: Nat, +es: List<&2, Ev>, +imm: List<&2, String>) -> List<&2, String>:
  match fuel:
    case 0n:
      imm
    case 1n+p:
      settle(p, es, keep(imm, es, imm))

def grow(es: List<&2, Ev>, +seen: List<&2, String>) -> List<&2, String>:
  match es:
    case Nil{}:
      seen
    case Edge{+x, +y, loc} <> t:
      grow(t, S.choose(List<&2, String>, has(seen, x) && Bool.not(has(seen, y)), u => y <> seen, u =>
        S.choose(List<&2, String>, has(seen, y) && Bool.not(has(seen, x)), u => x <> seen, u => seen)))
    case Bind{name, val, ok} <> t:
      grow(t, seen)
    case Mut{name, loc, how} <> t:
      grow(t, seen)
    case Esc{name, loc, how} <> t:
      grow(t, seen)
    case Use{name, loc} <> t:
      grow(t, seen)

def reach(fuel: Nat, +es: List<&2, Ev>, +seen: List<&2, String>) -> List<&2, String>:
  match fuel:
    case 0n:
      seen
    case 1n+p:
      reach(p, es, grow(es, seen))

def num_at(n: Nat, xs: S.Json) -> Nat:
  match n:
    case 0n:
      line(S.JArr{xs})
    case 1n+p:
      match xs:
        case S.JItem{h, t}:
          num_at(p, t)
        case _:
          0n

# `l` starts at or after the end of `e`.
def past(+l: S.Json, +e: S.Json) -> Bool:
  +el = num_at(2n, items(e))
  Nat.is_gt(line(l), el) || (Nat.is_eq(line(l), el) && Bool.not(Nat.is_lt(col(l), num_at(3n, items(e)))))

# ponytail: textual order only; a read earlier in the same loop body is missed.
# Upgrade path: treat every Use inside an enclosing For/While as later.
def later(es: List<&2, Ev>, +a: String, +loc: S.Json) -> S.Json:
  match es:
    case Nil{}:
      S.JNull{}
    case Use{name, +l} <> t:
      S.choose(S.Json, String.eq(name, a) && past(l, loc), u => l, u => later(t, a, loc))
    case Edge{x, y, l} <> t:
      later(t, a, loc)
    case Bind{name, val, ok} <> t:
      later(t, a, loc)
    case Mut{name, l, how} <> t:
      later(t, a, loc)
    case Esc{name, l, how} <> t:
      later(t, a, loc)

def edge_at(es: List<&2, Ev>, +a: String) -> S.Json:
  match es:
    case Nil{}:
      S.JNull{}
    case Edge{x, y, +l} <> t:
      S.choose(S.Json, String.eq(x, a) || String.eq(y, a), u => l, u => edge_at(t, a))
    case Bind{name, val, ok} <> t:
      edge_at(t, a)
    case Mut{name, l, how} <> t:
      edge_at(t, a)
    case Esc{name, l, how} <> t:
      edge_at(t, a)
    case Use{name, l} <> t:
      edge_at(t, a)

# The first mutable alias of `b` still observable after `loc`: read later, or a
# parameter (the caller holds it).
def hazard(cs: List<&2, String>, +b: String, +loc: S.Json, +rule: String, +what: String, +es: List<&2, Ev>, +params: List<&2, String>, +imm: List<&2, String>) -> List<&2, Diag>:
  match cs:
    case Nil{}:
      []
    case +a <> t:
      +l = later(es, a, loc)
      S.choose(List<&2, Diag>, String.eq(a, b) || has(imm, a) || (is_null(l) && Bool.not(has(params, a))), u =>
        hazard(t, b, loc, rule, what, es, params, imm), u =>
        [Diag{loc, rule, Advisory{}, what ++ "; " ++ a ++ " may alias it (binding" ++ at(edge_at(es, a)) ++ ") and is " ++
          S.choose(String, is_null(l), u => "a parameter", u => "read" ++ at(l))}])

def flags(todo: List<&2, Ev>, +es: List<&2, Ev>, +params: List<&2, String>, +imm: List<&2, String>, +n: Nat) -> List<&2, Diag>:
  match todo:
    case Nil{}:
      []
    case Mut{+name, +loc, +how} <> t:
      List.append(&2, Diag, S.choose(List<&2, Diag>, has(imm, name), u => [], u =>
        List.append(&2, Diag, S.choose(List<&2, Diag>, has(params, name), u =>
          [Diag{loc, "param-mutation", Advisory{}, how ++ " mutates parameter " ++ name ++ ": the caller observes it"}], u => []),
          hazard(reach(n, es, [name]), name, loc, "alias-mutation", how ++ " mutates " ++ name, es, params, imm))),
        flags(t, es, params, imm, n))
    case Esc{+name, +loc, +how} <> t:
      List.append(&2, Diag, S.choose(List<&2, Diag>, has(imm, name), u => [], u =>
        hazard(reach(n, es, [name]), name, loc, "alias-escape", name ++ " is " ++ how ++ ", which may mutate or keep it", es, params, imm)),
        flags(t, es, params, imm, n))
    case Edge{x, y, loc} <> t:
      flags(t, es, params, imm, n)
    case Bind{name, val, ok} <> t:
      flags(t, es, params, imm, n)
    case Use{name, loc} <> t:
      flags(t, es, params, imm, n)

# ponytail: top-level defs only, nested scopes share the def's names, and
# reach is recomputed per event. Upgrade path: scope-aware walk, memoized classes.
def fn_flags(xs: S.Json, +defs: List<&2, String>, +cs: List<&2, Contract>, +safe: List<&2, String>) -> List<&2, Diag>:
  match xs:
    case S.JItem{+h, t}:
      +names = binds(h)
      +es = walk(h, False{}, Env{names, defs, cs}, safe)
      +n = List.length(&2, String, names)
      List.append(&2, Diag, S.choose(List<&2, Diag>, String.eq(tag_of(h), "FunctionDef"), u =>
        flags(es, es, binds(field(h, "args")), settle(n, es, names), n), u => []), fn_flags(t, defs, cs, safe))
    case _:
      []

def ranked(w: List<&2, Rank>) -> List<&2, String>:
  match w:
    case Nil{}:
      []
    case Rank{name, r} <> t:
      name <> ranked(t)

# `ownership` per def through the kernel (O0), then the advisories. Passing a
# name to an O0-certified def is not an escape.
def alias(+m: S.Module, +cs: List<&2, Contract>) -> List<&2, Diag>:
  S.Module{+body} = m
  +names = def_names(body)
  +w = infer(List.length(&2, String, names), names, [], body, cs, True{}, 0n)
  +valid = String.is_empty(certificate(m, cs, w, True{}))
  List.sort(~Diag, ~le, List.append(&2, Diag, totals(names, w, valid, body, cs, True{}),
    fn_flags(body, names, cs, S.choose(List<&2, String>, valid, u => ranked(w), u => []))))

def grade_of(d: Diag) -> String:
  Diag{loc, rule, g, msg} = d
  grade(g)
