# The translator, first slice (T1): wire AST -> TypedIR -> Bend, faithful mode
# only (docs/omen/plans/translator-modes.md, tiers 1-2; no rewrite layer).
# `elaborate` is untrusted search; `verify` is the kernel: it recomputes every
# binding, type and primitive contract from the IR itself, and `emit` renders
# only what `verify` accepted. Anything unknown is a positioned diagnostic,
# never a guess. The T1 fragment is exactly what `normalize_stem` needs: one
# `return` of method calls on `str` granted by a contract, names and plain
# literals. ICall/ILet/IBranch/IFold fix the T2/T3 interface and are refused.
# Ownership: every T1 value is an immutable exact `str` (SOUNDNESS.md A1), so
# B1-B3 hold trivially; see docs/omen/lanes/translator-t1.md for the boundary.
import Base
import ./syntax.bend as S
import ./nodes.bend as N
import ./intake.bend as I
import ./lexer.bend as L
import ./parser.bend as P
import ./lint.bend as Lint

type Ty is Data:
  TBool{}
  TStr{}
  TInt{}
  TList{of: Ty}
  TMaybe{of: Ty}

type Eff is Data:
  Pure{}
  Impure{}

# IArg/IEnd chain argument lists inside the one recursive ADT (as S.Json does):
# mutual recursion between a node walker and a list walker is not allowed.
# Every node carries `loc`, the Python span [line, col, line, col] it came from.
type Ir is Data:
  IVar{name: String, ty: Ty, loc: S.Json}
  ILit{text: String, ty: Ty, loc: S.Json}
  IPrim{bend: String, args: Ir, ty: Ty, loc: S.Json}
  ICall{name: String, args: Ir, ty: Ty, loc: S.Json}
  ILet{name: String, val: Ir, body: Ir, loc: S.Json}
  IBranch{test: Ir, yes: Ir, no: Ir, ty: Ty, loc: S.Json}
  IFold{item: String, over: Ir, acc: String, init: Ir, step: Ir, ty: Ty, loc: S.Json}
  IReturn{val: Ir, loc: S.Json}
  IArg{head: Ir, rest: Ir}
  IEnd{}

type Param is Data:
  Param{name: String, ty: Ty, loc: S.Json}

type Fn is Data:
  Fn{name: String, params: List<&2, Param>, ret: Ty, eff: Eff, body: Ir, loc: S.Json}

# A primitive's contract is an assumption about CPython and Base on the value
# contract (printable ASCII plus the six ASCII whitespace), like SOUNDNESS.md
# A3: `recv.method(args)` on an exact `recv` means `bend(recv, args)`. The
# receiver's static type resolves the method (A1: exact `str`, no subclass),
# so spelling alone is never authority. A call is granted only if pure and total.
type Contract is Data:
  Contract{recv: Ty, method: String, args: List<&2, Ty>, ret: Ty, bend: String, pure: Bool, total: Bool}

def contracts() -> List<&2, Contract>:
  [Contract{TStr{}, "strip", [], TStr{}, "String.trim", True{}, True{}},
   Contract{TStr{}, "lower", [], TStr{}, "String.to_lower", True{}, True{}},
   Contract{TStr{}, "replace", [TStr{}, TStr{}], TStr{}, "String.replace", True{}, True{}}]

# ---- types ----

# The Bend spelling of a type; injective, so it also decides type equality.
def ty(t: Ty) -> String:
  match t:
    case TBool{}:
      "Bool"
    case TStr{}:
      "String"
    case TInt{}:
      "Int"
    case TList{of}:
      "List<&2, " ++ ty(of) ++ ">"
    case TMaybe{of}:
      "Maybe<&2, " ++ ty(of) ++ ">"

def tys(ts: List<&2, Ty>) -> String:
  match ts:
    case Nil{}:
      ""
    case h <> t:
      ty(h) ++ ";" ++ tys(t)

# "" for a chain or a refused node: it equals no type.
def ty_of(e: Ir) -> String:
  match e:
    case IVar{name, t, loc}:
      ty(t)
    case ILit{text, t, loc}:
      ty(t)
    case IPrim{bend, args, t, loc}:
      ty(t)
    case _:
      ""

def arg_tys(e: Ir) -> String:
  match e:
    case IArg{h, t}:
      ty_of(h) ++ ";" ++ arg_tys(t)
    case _:
      ""

def fail(b, -A: Kind(b), k: S.ErrorKind, +loc: S.Json, msg: String) -> Result<&2, b, S.Error, A>:
  Fail{S.error(k, S.Pos{Lint.line(loc), Lint.col(loc)}, msg)}

def refuse(b, -A: Kind(b), +loc: S.Json, msg: String) -> Result<&2, b, S.Error, A>:
  fail(b, A, S.Unsupported{}, loc, msg ++ Lint.at(loc))

# ---- literals ----

def plain(s: String, +q: U32) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{h, t}:
      +n = Char.to_u32(h)
      U32.is_ge(n, 32) && U32.is_le(n, 126) && Bool.not(U32.is_eq(n, 92)) && Bool.not(U32.is_eq(n, q)) && plain(t, q)

def quoted(s: String) -> Bool:
  match s:
    case SCon{h, t}:
      +n = Char.to_u32(h)
      U32.is_eq(n, 34) || U32.is_eq(n, 39)
    case SNil{}:
      False{}

def closes(last: Maybe<&2, Char>, +q: U32) -> Bool:
  match last:
    case Some{c}:
      U32.is_eq(Char.to_u32(c), q)
    case None{}:
      False{}

# The literal contract: one '...' or "..." token of printable ASCII with no
# backslash and no inner closing quote (so no prefix, escape, triple quote or
# adjacent literal). Its value is then its body, by inspection of the grammar.
def literal(+raw: String) -> Maybe<&2, String>:
  match raw:
    case SNil{}:
      None{}
    case SCon{h, +t}:
      +q = Char.to_u32(h)
      +body = String.drop_end(t, 1n)
      ok = (U32.is_eq(q, 34) || U32.is_eq(q, 39)) && closes(String.get_end(t, 1n), q) && plain(body, q)
      S.choose(Maybe<&2, String>, ok, u => Some{body}, u => None{})

def lit(m: Maybe<&2, String>, +loc: S.Json) -> Result<&2, &2, S.Error, Ir>:
  match m:
    case Some{s}:
      Done{ILit{s, TStr{}, loc}}
    case None{}:
      refuse(&2, Ir, loc, "literal outside the T1 contract (one plain ASCII string, no escapes)")

# ---- elaborate: untrusted search ----

def lookup(env: List<&2, Param>, +id: String, +loc: S.Json) -> Result<&2, &2, S.Error, Ir>:
  match env:
    case Nil{}:
      refuse(&2, Ir, loc, "unresolved name " ++ id)
    case Param{name, t, at} <> rest:
      S.choose(Result<&2, &2, S.Error, Ir>, String.eq(name, id), u => Done{IVar{id, t, loc}}, u => lookup(rest, id, loc))

def grant(cs: List<&2, Contract>, +recv: Ir, +args: Ir, +attr: String, +loc: S.Json) -> Result<&2, &2, S.Error, Ir>:
  match cs:
    case Nil{}:
      refuse(&2, Ir, loc, "no verified contract for ." ++ attr ++ " on (" ++ ty_of(recv) ++ ") with (" ++ arg_tys(args) ++ ")")
    case Contract{r, method, as, ret, bend, pure, total} <> rest:
      ok = String.eq(method, attr) && String.eq(ty(r), ty_of(recv)) && String.eq(tys(as), arg_tys(args)) && pure && total
      S.choose(Result<&2, &2, S.Error, Ir>, ok, u => Done{IPrim{bend, IArg{recv, args}, ret, loc}}, u =>
        grant(rest, recv, args, attr, loc))

def tail_of(xs: S.Json) -> S.Json:
  match xs:
    case S.JItem{h, t}:
      t
    case _:
      S.JEnd{}

# One def walks nodes and argument chains (JItem). Fuel is the JSON size, a
# bound on depth: exhaustion is a Limit diagnostic, not a partial tree. The
# receiver is elaborated before the arguments, left to right, as Python
# evaluates them (unobservable here: every granted primitive is pure and total).
def expr(fuel: Nat, +j: S.Json, +env: List<&2, Param>, +cs: List<&2, Contract>) -> Result<&2, &2, S.Error, Ir>:
  match fuel:
    case 0n:
      fail(&2, Ir, S.Limit{}, S.JNull{}, "elaboration fuel exhausted")
    case 1n+p:
      +left = p
      +tag = Lint.tag_of(j)
      +loc = Lint.field(j, "_loc")
      +func = Lint.field(j, "func")
      S.choose(Result<&2, &2, S.Error, Ir>, Lint.is_empty(S.JArr{j}), u => Done{IEnd{}}, u =>
        S.choose(Result<&2, &2, S.Error, Ir>, Nat.is_gt(Lint.size(j), 0n), u =>
          do Result<&2, &2, S.Error, Ir>:
            h : Ir <- expr(left, Lint.first(j), env, cs)
            t : Ir <- expr(left, tail_of(j), env, cs)
            Done{IArg{h, t}}, u =>
          S.choose(Result<&2, &2, S.Error, Ir>, String.eq(tag, "Name") && String.eq(Lint.tag_of(Lint.field(j, "ctx")), "Load"), u =>
            lookup(env, N.string(Lint.field(j, "id")), loc), u =>
            S.choose(Result<&2, &2, S.Error, Ir>, String.eq(tag, "Constant"), u =>
              lit(literal(String.trim(N.string(Lint.field(j, "_raw")))), loc), u =>
              S.choose(Result<&2, &2, S.Error, Ir>, String.eq(tag, "Call") && String.eq(Lint.tag_of(func), "Attribute") && Lint.is_empty(Lint.field(j, "keywords")), u =>
                do Result<&2, &2, S.Error, Ir>:
                  recv : Ir <- expr(left, Lint.field(func, "value"), env, cs)
                  args : Ir <- expr(left, Lint.items(Lint.field(j, "args")), env, cs)
                  grant(cs, recv, args, N.string(Lint.field(func, "attr")), loc), u =>
                refuse(&2, Ir, loc, "outside the T1 fragment: " ++ tag))))))

def weight(j: S.Json) -> Nat:
  match j:
    case S.JObj{fs}:
      1n+weight(fs)
    case S.JArr{xs}:
      1n+weight(xs)
    case S.JField{key, value, rest}:
      1n+Nat.add(weight(value), weight(rest))
    case S.JItem{h, t}:
      1n+Nat.add(weight(h), weight(t))
    case _:
      1n

def docstring(+s: S.Json) -> Bool:
  +v = Lint.field(s, "value")
  String.eq(Lint.tag_of(s), "Expr") && String.eq(Lint.tag_of(v), "Constant") && quoted(String.trim(N.string(Lint.field(v, "_raw"))))

# A leading docstring is a constant expression statement: skipped. Then exactly
# one `return e`. Falling off the end (implicit None) is refused.
def block(xs: S.Json, first: Bool, +near: S.Json, +env: List<&2, Param>, +cs: List<&2, Contract>) -> Result<&2, &2, S.Error, Ir>:
  match xs:
    case S.JItem{+h, +t}:
      +loc = Lint.field(h, "_loc")
      +val = Lint.field(h, "value")
      S.choose(Result<&2, &2, S.Error, Ir>, first && docstring(h), u => block(t, False{}, near, env, cs), u =>
        S.choose(Result<&2, &2, S.Error, Ir>, Bool.not(String.eq(Lint.tag_of(h), "Return")) || Lint.is_null(val), u =>
          refuse(&2, Ir, loc, "outside the T1 fragment: statement " ++ Lint.tag_of(h)), u =>
          S.choose(Result<&2, &2, S.Error, Ir>, Nat.is_gt(Lint.size(t), 0n), u =>
            refuse(&2, Ir, Lint.field(Lint.first(t), "_loc"), "statement after return"), u =>
            do Result<&2, &2, S.Error, Ir>:
              e : Ir <- expr(weight(val), val, env, cs)
              Done{IReturn{e, loc}})))
    case _:
      refuse(&2, Ir, near, "no return: falling off the end is outside the T1 fragment")

def ann(+j: S.Json, +near: S.Json) -> Result<&2, &2, S.Error, Ty>:
  S.choose(Result<&2, &2, S.Error, Ty>, String.eq(Lint.tag_of(j), "Name") && String.eq(N.string(Lint.field(j, "id")), "str"), u =>
    Done{TStr{}}, u => refuse(&2, Ty, S.choose(S.Json, Lint.is_null(j), u => near, u => Lint.field(j, "_loc")), "annotation outside the T1 fragment (str only)"))

def params(xs: S.Json) -> Result<&2, &2, S.Error, List<&2, Param>>:
  match xs:
    case S.JItem{+h, t}:
      do Result<&2, &2, S.Error, List<&2, Param>>:
        a : Ty <- ann(Lint.field(h, "annotation"), Lint.field(h, "_loc"))
        ps : List<&2, Param> <- params(t)
        Done{Param{N.string(Lint.field(h, "arg")), a, Lint.field(h, "_loc")} <> ps}
    case _:
      Done{[]}

def header(fs: List<&2, Lint.Fact>, +loc: S.Json) -> Result<&2, &2, S.Error, Unit>:
  match fs:
    case Nil{}:
      Done{Unit{}}
    case Lint.Bad{at, msg} <> t:
      fail(&2, Unit, S.Unsupported{}, loc, msg)
    case Lint.Calls{g} <> t:
      header(t, loc)

# The module must be closed and the def unique with a plain typed header: the
# same conditions, by the same code, as Lint's T0 kernel (SOUNDNESS.md A2).
def elaborate(m: S.Module, +cs: List<&2, Contract>, +name: String) -> Result<&2, &2, S.Error, Fn>:
  S.Module{+body} = m
  +f = Lint.find_def(body, name)
  +loc = Lint.field(f, "_loc")
  unique = S.choose(List<&2, Lint.Fact>, Nat.is_eq(Lint.count(Lint.def_names(body), name), 1n), u => [], u =>
    [Lint.Bad{loc, "no unique def " ++ name}])
  do Result<&2, &2, S.Error, Fn>:
    ok : Unit <- header(List.append(&2, Lint.Fact, unique, List.append(&2, Lint.Fact, Lint.closed(body), Lint.header(f))), loc)
    +env : List<&2, Param> <- params(Lint.items(Lint.field(Lint.field(f, "args"), "args")))
    ret : Ty <- ann(Lint.field(f, "returns"), loc)
    e : Ir <- block(Lint.items(Lint.field(f, "body")), True{}, loc, env, cs)
    Done{Fn{name, env, ret, Pure{}, e, loc}}

# ---- verify: the kernel ----

def spanned(loc: S.Json) -> Bool:
  Bool.not(String.eq(Lint.span(loc), "?"))

def bound(env: List<&2, Param>, +id: String, +want: String) -> Bool:
  match env:
    case Nil{}:
      False{}
    case Param{name, t, loc} <> rest:
      S.choose(Bool, String.eq(name, id), u => String.eq(ty(t), want), u => bound(rest, id, want))

def granted(cs: List<&2, Contract>, +bend: String, +args: String, +ret: String) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Contract{r, method, as, out, b, pure, total} <> rest:
      (String.eq(b, bend) && String.eq(ty(r) ++ ";" ++ tys(as), args) && String.eq(ty(out), ret) && pure && total) || granted(rest, bend, args, ret)

# "" iff the node is inside the emittable fragment: bound, typed, spanned,
# every primitive granted by a contract. Recomputed from the IR alone.
def why(e: Ir, +env: List<&2, Param>, +cs: List<&2, Contract>) -> String:
  match e:
    case IVar{+name, t, +loc}:
      S.choose(String, spanned(loc) && bound(env, name, ty(t)), u => "", u => "unbound or mistyped name " ++ name ++ Lint.at(loc))
    case ILit{text, t, +loc}:
      S.choose(String, spanned(loc) && String.eq(ty(t), "String") && plain(text, 0), u => "", u => "literal outside the contract" ++ Lint.at(loc))
    case IPrim{+bend, +args, t, +loc}:
      S.choose(String, spanned(loc) && granted(cs, bend, arg_tys(args), ty(t)), u => why(args, env, cs), u =>
        "primitive " ++ bend ++ " is not granted by a contract" ++ Lint.at(loc))
    case IArg{h, t}:
      +first = why(h, env, cs)
      S.choose(String, String.is_empty(first), u => why(t, env, cs), u => first)
    case IEnd{}:
      ""
    case IReturn{val, +loc}:
      S.choose(String, spanned(loc), u => why(val, env, cs), u => "return without a span")
    case ICall{name, args, t, loc}:
      "IR node Call is not emittable in T1" ++ Lint.at(loc)
    case ILet{name, val, body, loc}:
      "IR node Let is not emittable in T1" ++ Lint.at(loc)
    case IBranch{test, yes, no, t, loc}:
      "IR node Branch is not emittable in T1" ++ Lint.at(loc)
    case IFold{item, over, acc, init, step, t, loc}:
      "IR node Fold is not emittable in T1" ++ Lint.at(loc)

def ident_tail(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{h, t}:
      +n = Char.to_u32(h)
      ((U32.is_ge(n, 97) && U32.is_le(n, 122)) || (U32.is_ge(n, 48) && U32.is_le(n, 57)) || U32.is_eq(n, 95)) && ident_tail(t)

# ponytail: lower-case ASCII names only, and no reserved-word list: a Python
# name that is a Bend keyword fails the strict check (C1) loudly. Upgrade: mangle.
def ident(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{h, t}:
      +n = Char.to_u32(h)
      U32.is_ge(n, 97) && U32.is_le(n, 122) && ident_tail(t)

def idents(ps: List<&2, Param>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Param{name, t, loc} <> rest:
      ident(name) && spanned(loc) && idents(rest)

# A return is a statement: only the body's root may be one.
def returned(e: Ir) -> String:
  match e:
    case IReturn{val, loc}:
      ty_of(val)
    case _:
      ""

def is_pure(e: Eff) -> Bool:
  match e:
    case Pure{}:
      True{}
    case Impure{}:
      False{}

def verify(f: Fn, +cs: List<&2, Contract>) -> Result<&2, &2, S.Error, Fn>:
  Fn{+name, +ps, +ret, +eff, +body, +loc} = f
  +bad = why(body, ps, cs)
  S.choose(Result<&2, &2, S.Error, Fn>, Bool.not(ident(name) && idents(ps) && spanned(loc)), u =>
    refuse(&2, Fn, loc, "name or span not emittable"), u =>
    S.choose(Result<&2, &2, S.Error, Fn>, Bool.not(String.is_empty(bad)), u => fail(&2, Fn, S.Unsupported{}, loc, bad), u =>
      S.choose(Result<&2, &2, S.Error, Fn>, Bool.not(String.eq(returned(body), ty(ret))), u =>
        refuse(&2, Fn, loc, "body does not return " ++ ty(ret)), u =>
        S.choose(Result<&2, &2, S.Error, Fn>, Bool.not(is_pure(eff)), u => refuse(&2, Fn, loc, "effect is not Pure"), u =>
          Done{Fn{name, ps, ret, eff, body, loc}}))))

# ---- emit: render what the kernel accepted ----

def sep(e: Ir) -> String:
  match e:
    case IArg{h, t}:
      ", "
    case _:
      ""

# A refused node renders as a hole, which C1 rejects; `emit` never reaches it.
def show(e: Ir) -> String:
  match e:
    case IVar{name, t, loc}:
      name
    case ILit{text, t, loc}:
      S.quote(text)
    case IPrim{bend, args, t, loc}:
      bend ++ "(" ++ show(args) ++ ")"
    case IArg{h, +t}:
      show(h) ++ sep(t) ++ show(t)
    case IEnd{}:
      ""
    case IReturn{val, loc}:
      show(val)
    case _:
      "?refused"

def kind(e: Ir) -> String:
  match e:
    case IVar{name, t, loc}:
      "Var " ++ name
    case ILit{text, t, loc}:
      "Lit " ++ S.quote(text)
    case IPrim{bend, args, t, loc}:
      "Prim " ++ bend
    case IReturn{val, loc}:
      "Return"
    case _:
      "?"

def own_loc(e: Ir) -> S.Json:
  match e:
    case IVar{name, t, loc}:
      loc
    case ILit{text, t, loc}:
      loc
    case IPrim{bend, args, t, loc}:
      loc
    case IReturn{val, loc}:
      loc
    case _:
      S.JNull{}

def row(+e: Ir, +line: Nat, +col: Nat) -> String:
  "# " ++ Nat.show(line) ++ ":" ++ Nat.show(col) ++ "-" ++ Nat.show(line) ++ ":" ++ Nat.show(Nat.add(col, String.length(show(e)))) ++
    " <- py " ++ Lint.span(own_loc(e)) ++ " " ++ kind(e) ++ " : " ++ ty_of(e) ++ returned(e) ++ "\n"

# The span map: one row per IR node, emitted-Bend span <- Python span.
def spans(e: Ir, +line: Nat, +col: Nat) -> String:
  match e:
    case IPrim{+bend, +args, +t, +loc}:
      row(IPrim{bend, args, t, loc}, line, col) ++ spans(args, line, Nat.add(col, 1n+String.length(bend)))
    case IArg{+h, +t}:
      spans(h, line, col) ++ spans(t, line, Nat.add(col, Nat.add(String.length(show(h)), String.length(sep(t)))))
    case IReturn{+val, +loc}:
      row(IReturn{val, loc}, line, col) ++ spans(val, line, col)
    case IEnd{}:
      ""
    case +other:
      row(other, line, col)

def sig(ps: List<&2, Param>, lead: String) -> String:
  match ps:
    case Nil{}:
      ""
    case Param{name, t, loc} <> rest:
      lead ++ name ++ ": " ++ ty(t) ++ sig(rest, ", ")

def param_rows(ps: List<&2, Param>, +col: Nat) -> String:
  match ps:
    case Nil{}:
      ""
    case Param{+name, +t, loc} <> rest:
      +w = String.length(name ++ ": " ++ ty(t))
      "# 4:" ++ Nat.show(col) ++ "-4:" ++ Nat.show(Nat.add(col, w)) ++ " <- py " ++ Lint.span(loc) ++ " Param " ++ name ++ " : " ++ ty(t) ++ "\n" ++
        param_rows(rest, Nat.add(col, Nat.add(w, 2n)))

# The def is line 4 and its body line 5 col 2 of the emitted file.
def render(f: Fn) -> String:
  Fn{+name, +ps, ret, eff, +body, loc} = f
  "# Faithful translation (tiers 1-2) of Python `" ++ name ++ "` " ++ Lint.span(loc) ++ " by demos/python/translate.bend.\n" ++
    "import Base\n\ndef " ++ name ++ "(" ++ sig(ps, "") ++ ") -> " ++ ty(ret) ++ ":\n  " ++ show(body) ++ "\n\n" ++
    "# spans: emitted Bend <- Python source, node : type\n" ++ param_rows(ps, Nat.add(5n, String.length(name))) ++ spans(body, 5n, 2n)

def emit(f: Fn, +cs: List<&2, Contract>) -> Result<&2, &2, S.Error, String>:
  do Result<&2, &2, S.Error, String>:
    ok : Fn <- verify(f, cs)
    Done{render(ok)}

def translate(source: String, +cs: List<&2, Contract>, name: String) -> Result<&2, &2, S.Error, String>:
  do Result<&2, &2, S.Error, String>:
    ts : List<&2, S.Tok> <- L.lex(source)
    m : S.Module <- P.parse(ts)
    f : Fn <- elaborate(m, cs, name)
    emit(f, cs)

# PY_SOURCE names a UTF-8 file, PY_DEF the def to translate.
def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("PY_SOURCE"))
    name : String <- IO.try(String, IO.get_env("PY_DEF"))
    source : String <- I.load(path)
    out : String <- I.unwrap(&2, String, translate(source, contracts(), name))
    IO.print(out)
