# Proofs-as-lint over the parser's wire AST (S.Json). L1: the totality fragment
# T0 and local reachability. `certificate` is the trusted kernel: it recomputes
# every condition from the actual AST and contracts; a witness only supplies
# call ranks. `analyze` is untrusted search in front of it. See SOUNDNESS.md.
# Coverage (finite match domains) is lane L3; module summaries are L4.
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
def ann_ok(j: S.Json) -> Bool:
  match j:
    case S.JObj{+fs}:
      +tag = N.string(N.get(fs, "tag"))
      S.choose(Bool, String.eq(tag, "Name"), u => has(["str", "bool", "int", "list"], N.string(N.get(fs, "id"))), u =>
        S.choose(Bool, String.eq(tag, "Constant"), u => String.eq(N.string(N.get(fs, "_raw")), "None"), u =>
          has(["Subscript", "BinOp", "BitOr", "Load"], tag) && ann_ok(fs)))
    case S.JField{key, value, rest}:
      ann_ok(value) && ann_ok(rest)
    case _:
      True{}

def typed(+j: S.Json) -> Bool:
  Bool.not(is_null(j)) && ann_ok(j)

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

# Every condition of "name is in T0", recomputed from the AST.
def check_fn(+body: S.Json, +cs: List<&2, Contract>, +name: String) -> List<&2, Fact>:
  +f = find_def(body, name)
  +defs = def_names(body)
  unique = S.choose(List<&2, Fact>, Nat.is_eq(count(defs, name), 1n), u => [], u =>
    [Bad{field(f, "_loc"), "no unique def " ++ name}])
  List.append(&2, Fact, closed(body), List.append(&2, Fact, unique, List.append(&2, Fact, header(f),
    scan(field(f, "body"), "", field(f, "_loc"), Env{binds(f), defs, cs}))))

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

def entries(es: List<&2, Rank>, +w: List<&2, Rank>, +body: S.Json, +cs: List<&2, Contract>) -> String:
  match es:
    case Nil{}:
      ""
    case Rank{+name, +r} <> t:
      +why = discharge(check_fn(body, cs, name), w, r)
      S.choose(String, String.is_empty(why), u => entries(t, w, body, cs), u => name ++ ": " ++ why)

# "" iff every entry of the witness checks against the actual AST/contracts.
# By induction on rank every entry is then total (SOUNDNESS.md, T0).
def certificate(m: S.Module, +cs: List<&2, Contract>, +w: List<&2, Rank>) -> String:
  S.Module{body} = m
  entries(w, w, body, cs)

def def_loc(m: S.Module, name: String) -> S.Json:
  S.Module{body} = m
  field(find_def(body, name), "_loc")

# The witness entry is consulted first, so no entry means no proof by
# computation alone (the law below).
def verdict(entry: Maybe<&2, Nat>, +m: S.Module, +cs: List<&2, Contract>, +w: List<&2, Rank>, +name: String) -> Diag:
  match entry:
    case None{}:
      Diag{def_loc(m, name), "total", Unknown{}, "no certificate"}
    case Some{r}:
      +why = certificate(m, cs, w)
      S.choose(Diag, String.is_empty(why), u =>
        Diag{def_loc(m, name), "total", Proven{}, "terminates on exact built-in arguments (T0)"}, u =>
        Diag{def_loc(m, name), "total", Refuted{}, "certificate refuted: " ++ why})

def verify(+m: S.Module, +cs: List<&2, Contract>, +w: List<&2, Rank>, +name: String) -> Diag:
  verdict(rank(w, name), m, cs, w, name)

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
def round(names: List<&2, String>, +w: List<&2, Rank>, +body: S.Json, +cs: List<&2, Contract>, +r: Nat) -> List<&2, Rank>:
  match names:
    case Nil{}:
      []
    case +h <> t:
      ok = Maybe.is_none(&2, Nat, rank(w, h)) && String.is_empty(why_not(check_fn(body, cs, h), w))
      List.append(&2, Rank, S.choose(List<&2, Rank>, ok, u => [Rank{h, r}], u => []), round(t, w, body, cs, r))

def infer(fuel: Nat, +names: List<&2, String>, +w: List<&2, Rank>, +body: S.Json, +cs: List<&2, Contract>, +r: Nat) -> List<&2, Rank>:
  match fuel:
    case 0n:
      w
    case 1n+p:
      infer(p, names, List.append(&2, Rank, w, round(names, w, body, cs, r)), body, cs, 1n+r)

def totals(names: List<&2, String>, +w: List<&2, Rank>, +valid: Bool, +body: S.Json, +cs: List<&2, Contract>) -> List<&2, Diag>:
  match names:
    case Nil{}:
      []
    case +h <> t:
      +loc = field(find_def(body, h), "_loc")
      d = S.choose(Diag, valid && Maybe.is_some(&2, Nat, rank(w, h)), u =>
        Diag{loc, "total", Proven{}, "terminates on exact built-in arguments (T0)"}, u =>
        Diag{loc, "total", Unknown{}, why_not(check_fn(body, cs, h), w)})
      d <> totals(t, w, valid, body, cs)

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
  +w = infer(List.length(&2, String, names), names, [], body, cs, 0n)
  +valid = String.is_empty(certificate(m, cs, w))
  List.sort(~Diag, ~le, List.append(&2, Diag, totals(names, w, valid, body, cs),
    List.append(&2, Diag, shadows(body, cs), dead(body))))
