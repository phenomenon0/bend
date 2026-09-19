# The IR kernel: `emit` renders only what `verify` recomputes from the IR and
# the contracts. `honest` is the elaborator's own IR for normalize_stem; every
# other case forges one thing (a TypedIR is data, like a Lint certificate) and
# must be refused. `assumed` is the trust boundary on purpose: a contract that
# lies about purity is refused, but one that lies about meaning cannot be seen.
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
  [Tr.Contract{Tr.TStr{}, "strip", [], Tr.TStr{}, "String.trim", False{}, True{}}]

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
  try("let", ret(Tr.ILet{"x", s(), s(), at(0n, 4n)})) ++
  try("branch", ret(Tr.IBranch{s(), s(), s(), Tr.TStr{}, at(0n, 4n)})) ++
  try("fold", ret(Tr.IFold{"c", s(), "acc", s(), s(), Tr.TStr{}, at(0n, 4n)})) ++
  try("no return", fn("f", Tr.TStr{}, Tr.Pure{}, s())) ++
  try("return type", fn("f", Tr.TBool{}, Tr.Pure{}, Tr.IReturn{s(), at(0n, 9n)})) ++
  try("effect", fn("f", Tr.TStr{}, Tr.Impure{}, Tr.IReturn{s(), at(0n, 9n)})) ++
  try("identifier", fn("F-x", Tr.TStr{}, Tr.Pure{}, Tr.IReturn{s(), at(0n, 9n)})) ++
  "assumed: " ++ line(Tr.emit(ret(call("String.trim", one(s()))), lying())) ++ "\n"
#|"honest: emitted\nunknown prim: error Unsupported 1 0 primitive String.reverse is not granted by a contract at 1:0\narity: error Unsupported 1 0 primitive String.replace is not granted by a contract at 1:0\narg type: error Unsupported 1 0 primitive String.trim is not granted by a contract at 1:0\nresult type: error Unsupported 1 0 primitive String.trim is not granted by a contract at 1:0\nunbound: error Unsupported 1 0 unbound or mistyped name t at 1:0\nliteral: error Unsupported 1 0 literal outside the contract at 1:0\nno span: error Unsupported 1 0 unbound or mistyped name s at 0:0\ncall: error Unsupported 1 0 IR node Call is not emittable in T1 at 1:0\nlet: error Unsupported 1 0 IR node Let is not emittable in T1 at 1:0\nbranch: error Unsupported 1 0 IR node Branch is not emittable in T1 at 1:0\nfold: error Unsupported 1 0 IR node Fold is not emittable in T1 at 1:0\nno return: error Unsupported 1 0 body does not return String at 1:0\nreturn type: error Unsupported 1 0 body does not return Bool at 1:0\neffect: error Unsupported 1 0 effect is not Pure at 1:0\nidentifier: error Unsupported 1 0 name or span not emittable at 1:0\nassumed: error Unsupported 1 0 primitive String.trim is not granted by a contract at 1:0\n"
