# The IR kernel: `emit` renders only what `verify` recomputes from the IR and
# the contracts. `honest` is the elaborator's own IR for normalize_stem; every
# other case forges one thing (a TypedIR is data, like a Lint certificate) and
# must be refused. `assumed` is the trust boundary on purpose: a contract that
# lies about purity is refused, but one that lies about meaning cannot be seen.
# T2: each new node (Let, Branch, Fold, Some, Maybe, Stop) has honest controls
# and forgeries of its position, types, binders and guard; Call is still refused.
import Base
import ../../demos/python/syntax.bend as S
import ../../demos/python/translate.bend as Tr

def at(a: Nat, b: Nat) -> S.Json:
  S.JArr{S.JItem{S.JNum{1n}, S.JItem{S.JNum{a}, S.JItem{S.JNum{1n}, S.JItem{S.JNum{b}, S.JEnd{}}}}}}

def s() -> Tr.Ir:
  Tr.IVar{"s", Tr.TStr{}, at(0n, 1n)}

def call(bend: String, args: Tr.Ir) -> Tr.Ir:
  Tr.IPrim{bend, args, Tr.TStr{}, at(0n, 9n)}

def one(x: Tr.Ir) -> Tr.Ir:
  Tr.IArg{x, Tr.IEnd{}}

def fn(name: String, ret: Tr.Ty, eff: Tr.Eff, body: Tr.Ir) -> Tr.Fn:
  Tr.Fn{name, [Tr.Param{"s", Tr.TStr{}, at(0n, 1n)}], ret, eff, body, at(0n, 9n)}

def ret(x: Tr.Ir) -> Tr.Fn:
  fn("f", Tr.TStr{}, Tr.Pure{}, Tr.IReturn{x, at(0n, 9n)})

def line(r: Result<&2, &2, S.Error, String>) -> String:
  match r:
    case Done{text}:
      "emitted"
    case Fail{e}:
      S.error_text(e)

def try(label: String, f: Tr.Fn) -> String:
  label ++ ": " ++ line(Tr.emit(f, Tr.contracts())) ++ "\n"

def lying() -> List<&2, Tr.Contract>:
  [Tr.Contract{Tr.TStr{}, "strip", [], Tr.TStr{}, "String.trim", False{}, True{}, "", ""}]

def ms() -> Tr.Ty:
  Tr.TMaybe{Tr.TStr{}}

def yes() -> Tr.Ir:
  Tr.ILit{"True", Tr.TBool{}, at(2n, 3n)}

def none() -> Tr.Ir:
  Tr.ILit{"None", ms(), at(2n, 3n)}

def m() -> Tr.Ir:
  Tr.IVar{"m", ms(), at(4n, 5n)}

def has(sep: String) -> Tr.Ir:
  Tr.IPrim{"String.contains", Tr.IArg{s(), one(Tr.ILit{sep, Tr.TStr{}, at(2n, 3n)})}, Tr.TBool{}, at(1n, 3n)}

def after(sep: String) -> Tr.Ir:
  Tr.IPrim{"Py.after", Tr.IArg{s(), one(Tr.ILit{sep, Tr.TStr{}, at(6n, 7n)})}, Tr.TStr{}, at(5n, 8n)}

def rs(x: Tr.Ir) -> Tr.Ir:
  Tr.IReturn{x, at(0n, 9n)}

# f(s: str, xs: list[str]) -> str
def tail(body: Tr.Ir) -> Tr.Fn:
  Tr.Fn{"f", [Tr.Param{"s", Tr.TStr{}, at(0n, 1n)}, Tr.Param{"xs", Tr.TList{Tr.TStr{}}, at(2n, 3n)}], Tr.TStr{}, Tr.Pure{}, body, at(0n, 9n)}

def fold(item: String, over: Tr.Ir, acc: String, step: Tr.Ir) -> Tr.Ir:
  rs(Tr.IFold{item, over, acc, s(), step, Tr.TStr{}, at(3n, 4n)})

def xs() -> Tr.Ir:
  Tr.IVar{"xs", Tr.TList{Tr.TStr{}}, at(2n, 3n)}

def x() -> Tr.Ir:
  Tr.IVar{"x", Tr.TStr{}, at(7n, 8n)}

def opt(on: String, none: Tr.Ir, some: Tr.Ir) -> Tr.Ir:
  Tr.ILet{"m", Tr.ISome{s(), ms(), at(1n, 2n)}, rs(Tr.IMaybe{on, none, some, Tr.TStr{}, at(3n, 4n)}), at(0n, 4n)}

def t2() -> String:
  try("let", tail(Tr.ILet{"x", s(), rs(x()), at(0n, 4n)})) ++
  try("let in argument", ret(call("String.trim", one(Tr.ILet{"x", s(), s(), at(0n, 4n)})))) ++
  try("let retyped", tail(Tr.ILet{"s", yes(), rs(s()), at(0n, 4n)})) ++
  try("let name", tail(Tr.ILet{"_c", s(), rs(s()), at(0n, 4n)})) ++
  try("let scope", tail(Tr.ILet{"x", x(), rs(s()), at(0n, 4n)})) ++
  try("return in argument", ret(call("String.trim", one(rs(s()))))) ++
  try("branch", tail(Tr.IBranch{has("."), rs(s()), rs(s()), Tr.TStr{}, at(0n, 4n)})) ++
  try("branch test", tail(Tr.IBranch{s(), rs(s()), rs(s()), Tr.TStr{}, at(0n, 4n)})) ++
  try("branch arm type", tail(Tr.IBranch{has("."), rs(s()), rs(yes()), Tr.TStr{}, at(0n, 4n)})) ++
  try("branch falls", tail(Tr.IBranch{has("."), rs(s()), s(), Tr.TStr{}, at(0n, 4n)})) ++
  try("helper names", ret(Tr.IBranch{has("."), Tr.IBranch{has("."), s(), s(), Tr.TStr{}, at(0n, 4n)}, s(), Tr.TStr{}, at(0n, 4n)})) ++
  try("guarded", tail(Tr.IBranch{has("."), rs(after(".")), rs(s()), Tr.TStr{}, at(0n, 4n)})) ++
  try("guard wrong arm", tail(Tr.IBranch{has("."), rs(s()), rs(after(".")), Tr.TStr{}, at(0n, 4n)})) ++
  try("guard absent", ret(after("."))) ++
  try("guard other sep", tail(Tr.IBranch{has("."), rs(after("-")), rs(s()), Tr.TStr{}, at(0n, 4n)})) ++
  try("guard empty sep", tail(Tr.IBranch{has(""), rs(after("")), rs(s()), Tr.TStr{}, at(0n, 4n)})) ++
  try("guard rebound", tail(Tr.IBranch{has("."), Tr.ILet{"s", call("String.trim", one(s())), rs(after(".")), at(0n, 4n)}, rs(s()), Tr.TStr{}, at(0n, 4n)})) ++
  try("fold", tail(fold("x", xs(), "acc", x()))) ++
  try("fold stop", tail(fold("x", xs(), "acc", Tr.IStop{x(), at(5n, 6n)}))) ++
  try("fold over", tail(fold("x", s(), "acc", x()))) ++
  try("fold item is acc", tail(fold("x", xs(), "x", x()))) ++
  try("fold step type", tail(fold("x", xs(), "acc", yes()))) ++
  try("fold step returns", tail(fold("x", xs(), "acc", rs(x())))) ++
  try("fold step rebinds capture", tail(fold("x", xs(), "acc", Tr.ILet{"s", x(), x(), at(5n, 6n)}))) ++
  try("stop outside", tail(Tr.IStop{s(), at(0n, 4n)})) ++
  try("stop type", tail(fold("x", xs(), "acc", Tr.IStop{yes(), at(5n, 6n)}))) ++
  try("maybe", tail(opt("m", s(), Tr.IVar{"m", Tr.TStr{}, at(4n, 5n)}))) ++
  try("maybe on str", tail(opt("s", s(), s()))) ++
  try("maybe none reads", tail(opt("m", Tr.IPrim{"String.trim", one(m()), Tr.TStr{}, at(5n, 6n)}, s()))) ++
  try("maybe unnarrowed", tail(opt("m", s(), m()))) ++
  try("maybe arm type", tail(opt("m", s(), yes()))) ++
  try("some type", tail(Tr.ILet{"m", Tr.ISome{yes(), ms(), at(1n, 2n)}, rs(s()), at(0n, 4n)})) ++
  try("none at bool", tail(Tr.IBranch{Tr.ILit{"None", Tr.TBool{}, at(0n, 1n)}, rs(s()), rs(s()), Tr.TStr{}, at(0n, 4n)})) ++
  try("bool literal", tail(Tr.IBranch{Tr.ILit{"Maybe", Tr.TBool{}, at(0n, 1n)}, rs(s()), rs(s()), Tr.TStr{}, at(0n, 4n)}))

def main() -> String:
  try("honest", ret(call("String.replace", Tr.IArg{call("String.to_lower", one(call("String.trim", one(s())))),
    Tr.IArg{Tr.ILit{" ", Tr.TStr{}, at(2n, 5n)}, one(Tr.ILit{"-", Tr.TStr{}, at(6n, 9n)})}}))) ++
  try("unknown prim", ret(call("String.reverse", one(s())))) ++
  try("arity", ret(call("String.replace", one(s())))) ++
  try("arg type", ret(call("String.trim", one(Tr.IVar{"s", Tr.TBool{}, at(0n, 1n)})))) ++
  try("result type", ret(Tr.IPrim{"String.trim", one(s()), Tr.TBool{}, at(0n, 9n)})) ++
  try("unbound", ret(Tr.IVar{"t", Tr.TStr{}, at(0n, 1n)})) ++
  try("literal", ret(Tr.ILit{"a\nb", Tr.TStr{}, at(0n, 1n)})) ++
  try("no span", ret(Tr.IVar{"s", Tr.TStr{}, S.JNull{}})) ++
  try("call", ret(Tr.ICall{"g", one(s()), Tr.TStr{}, at(0n, 4n)})) ++
  try("no return", fn("f", Tr.TStr{}, Tr.Pure{}, s())) ++
  try("return type", fn("f", Tr.TBool{}, Tr.Pure{}, Tr.IReturn{s(), at(0n, 9n)})) ++
  try("effect", fn("f", Tr.TStr{}, Tr.Impure{}, Tr.IReturn{s(), at(0n, 9n)})) ++
  try("identifier", fn("F-x", Tr.TStr{}, Tr.Pure{}, Tr.IReturn{s(), at(0n, 9n)})) ++
  "assumed: " ++ line(Tr.emit(ret(call("String.trim", one(s()))), lying())) ++ "\n" ++
  t2()
#|"honest: emitted\nunknown prim: error Unsupported 1 0 primitive String.reverse is not granted by a contract (or its guard is not known here) at 1:0\narity: error Unsupported 1 0 primitive String.replace is not granted by a contract (or its guard is not known here) at 1:0\narg type: error Unsupported 1 0 primitive String.trim is not granted by a contract (or its guard is not known here) at 1:0\nresult type: error Unsupported 1 0 primitive String.trim is not granted by a contract (or its guard is not known here) at 1:0\nunbound: error Unsupported 1 0 unbound or mistyped name t at 1:0\nliteral: error Unsupported 1 0 literal outside the contract at 1:0\nno span: error Unsupported 1 0 unbound or mistyped name s at 0:0\ncall: error Unsupported 1 0 IR node Call is not emittable in T2 at 1:0\nno return: error Unsupported 1 0 body does not return String at 1:0\nreturn type: error Unsupported 1 0 body does not return Bool at 1:0\neffect: error Unsupported 1 0 effect is not Pure at 1:0\nidentifier: error Unsupported 1 0 name or span not emittable at 1:0\nassumed: error Unsupported 1 0 primitive String.trim is not granted by a contract (or its guard is not known here) at 1:0\nlet: emitted\nlet in argument: error Unsupported 1 0 let of x: in argument position, retyped, or rebinding a captured name inside a fold step at 1:0\nlet retyped: error Unsupported 1 0 let of s: in argument position, retyped, or rebinding a captured name inside a fold step at 1:0\nlet name: error Unsupported 1 0 let of _c: in argument position, retyped, or rebinding a captured name inside a fold step at 1:0\nlet scope: error Unsupported 1 0 unbound or mistyped name x at 1:7\nreturn in argument: error Unsupported 1 0 return outside tail position at 1:0\nbranch: emitted\nbranch test: error Unsupported 1 0 branch on a non-Bool test, or arms of another type at 1:0\nbranch arm type: error Unsupported 1 0 branch on a non-Bool test, or arms of another type at 1:0\nbranch falls: error Unsupported 1 0 body does not return String at 1:0\nhelper names: error Unsupported 1 0 two helper defs share a name at 1:0\nguarded: emitted\nguard wrong arm: error Unsupported 1 0 primitive Py.after is not granted by a contract (or its guard is not known here) at 1:5\nguard absent: error Unsupported 1 0 primitive Py.after is not granted by a contract (or its guard is not known here) at 1:5\nguard other sep: error Unsupported 1 0 primitive Py.after is not granted by a contract (or its guard is not known here) at 1:5\nguard empty sep: error Unsupported 1 0 primitive Py.after is not granted by a contract (or its guard is not known here) at 1:5\nguard rebound: error Unsupported 1 0 primitive Py.after is not granted by a contract (or its guard is not known here) at 1:5\nfold: emitted\nfold stop: emitted\nfold over: error Unsupported 1 0 fold over a non-list, item = accumulator, or a step of another type at 1:3\nfold item is acc: error Unsupported 1 0 fold over a non-list, item = accumulator, or a step of another type at 1:3\nfold step type: error Unsupported 1 0 fold over a non-list, item = accumulator, or a step of another type at 1:3\nfold step returns: error Unsupported 1 0 return outside tail position at 1:0\nfold step rebinds capture: error Unsupported 1 0 let of s: in argument position, retyped, or rebinding a captured name inside a fold step at 1:5\nstop outside: error Unsupported 1 0 break outside a fold step, or not of the accumulator's type at 1:0\nstop type: error Unsupported 1 0 fold over a non-list, item = accumulator, or a step of another type at 1:3\nmaybe: emitted\nmaybe on str: error Unsupported 1 0 Optional match on a name that is not Optional, a None arm that reads it, or arms of another type at 1:3\nmaybe none reads: error Unsupported 1 0 Optional match on a name that is not Optional, a None arm that reads it, or arms of another type at 1:3\nmaybe unnarrowed: error Unsupported 1 0 Optional match on a name that is not Optional, a None arm that reads it, or arms of another type at 1:3\nmaybe arm type: error Unsupported 1 0 Optional match on a name that is not Optional, a None arm that reads it, or arms of another type at 1:3\nsome type: error Unsupported 1 0 Some of a mistyped value at 1:1\nnone at bool: error Unsupported 1 0 literal outside the contract at 1:0\nbool literal: error Unsupported 1 0 literal outside the contract at 1:0\n"
