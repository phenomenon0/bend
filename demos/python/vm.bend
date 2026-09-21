# The Python VM spike: source -> house lexer -> house parser -> typed AST ->
# bytecode -> a stack VM. The subset (v1): non-negative ints, bools, + - * // %,
# comparisons, and/or/not, if/elif/else, while, def/call/recursion, return,
# print. No strings, objects, dicts, exceptions, f-strings. The dispatch is
# the one dense U32 match over the contiguous opcode rows 0..26 -- the new
# compiler's table shape; what it lowers to is measured in the lane report.
#   PY_SOURCE=prog.py bun bend2/main.ts demos/python/vm.bend
import Base
import ./syntax.bend as S
import ./intake.bend as I
import ./lexer.bend as L
import ./parser.bend as P
import ./nodes.bend as N

# Types
# =====

type Val is Data:
  VInt{n: Nat}
  VBool{b: Bool}
  VNone{}

# op is U32 and DENSE 0..26 (contiguous rows only); a and b are operands.
type Instr is Data:
  Instr{op: U32, a: Nat, b: Nat}

type Def is Data:
  Def{name: String, params: List<&2, String>, nparams: Nat, body: S.Json}

type Func is Data:
  Func{nparams: Nat, nlocals: Nat, code: List<&2, Instr>}

type VFrame is Data:
  VFrame{here: List<&2, Instr>, rest: List<&2, Instr>, locals: List<&2, Val>}

type Prog is Data:
  Prog{funcs: List<&2, Func>, consts: List<&2, Val>, nglobals: Nat, code: List<&2, Instr>}

# One compilation threads the tables through every fragment: the const pool
# and the global name table grow, the local table is fixed per unit.
type Env is Data:
  Env{consts: List<&2, Val>, nconsts: Nat, globals: List<&2, String>, nglobals: Nat,
      funcs: List<&2, Def>, names: List<&2, String>, nnames: Nat}

# A compiled fragment, REVERSED (the latest instr at the head), with its
# length: jump targets are absolute positions computed from the sub-lengths.
# A fault is an unsupported construct; it compiles to nothing and rides out.
type Cx is Data:
  Cx{code: List<&2, Instr>, len: Nat, env: Env, fault: String}

type Frg is Data:
  Frg{code: List<&2, Instr>, len: Nat, op: U32}

type Pop is Data:
  Pop{args: List<&2, Val>, more: List<&2, Val>}

type Run is Data:
  Run{funcs: List<&2, Func>, consts: List<&2, Val>, stack: List<&2, Val>,
      here: List<&2, Instr>, rest: List<&2, Instr>, locals: List<&2, Val>,
      globals: List<&2, Val>, frames: List<&2, VFrame>, out: List<&2, String>,
      fault: String}

# Opcodes, dense and contiguous:
#   0 CONST a      6 ADD      11 LT     17 NOT      23 CALL a b
#   1 LOAD_L a     7 SUB      12 LTE    18 JUMP a   24 RET
#   2 STORE_L a    8 MUL      13 GT     19 JIF a    25 PRINT b
#   3 LOAD_G a     9 DIV      14 GTE    20 JIT a    26 HALT
#   4 STORE_G a   10 MOD      15 EQ     21 JIFK a
#   5 POP                     16 NEQ    22 JITK a

# S.Json access
# ===========

def jfields(+j: S.Json) -> S.Json:
  match j:
    case S.JObj{fs}:
      fs
    case _:
      S.JEnd{}

def jtag(+j: S.Json) -> String:
  N.string(N.get(jfields(j), "tag"))

def jfield(+j: S.Json, +key: String) -> S.Json:
  N.get(jfields(j), key)

def jstr(+j: S.Json) -> String:
  match j:
    case S.JStr{s}:
      s
    case _:
      ""

def jnull(+j: S.Json) -> Bool:
  match j:
    case S.JNull{}:
      True{}
    case _:
      False{}

def jitems(+j: S.Json) -> S.Json:
  match j:
    case S.JArr{xs}:
      xs
    case _:
      S.JEnd{}

def jend(+j: S.Json) -> Bool:
  match j:
    case S.JEnd{}:
      True{}
    case _:
      False{}

def first_of(+js: S.Json) -> S.Json:
  match js:
    case S.JItem{h, t}:
      h
    case _:
      S.JNull{}

# The number of entries in a JSON item chain (an argument list, a statement list).
def jcount(+j: S.Json) -> Nat:
  match j:
    case S.JItem{h, t}:
      (1n + jcount(t) : Nat)
    case _:
      0n

# Fragments
# =========

# join(later, earlier): both reversed; the result is the program
# earlier ++ later, still reversed -- which in the reversed shape is the
# plain append later ++ earlier. O(|later|), one cons per instruction.
def join(+later: List<&2, Instr>, earlier: List<&2, Instr>) -> List<&2, Instr>:
  match later:
    case Nil{}:
      earlier
    case Con{h, t}:
      Con{h, join(t, earlier)}

def one(+op: U32, +a: Nat, +b: Nat) -> List<&2, Instr>:
  Con{Instr{op, a, b}, Nil{}}

def pick_fault(+a: String, +b: String) -> String:
  S.choose(String, String.is_empty(a), u => b, u => a)

def count(+js: S.Json, +n: Nat) -> Nat:
  match js:
    case S.JEnd{}:
      n
    case S.JItem{one, rest}:
      count(rest, 1n+n)
    case _:
      n

def headc(+s: String) -> Char:
  match s:
    case SNil{}:
      Chr{0}
    case SCon{h, t}:
      h

# A computed Cx is read through its accessors: a pattern-let of a computed
# value is not a legal scrutinee, a parameter is.
def cx_code(+c: Cx) -> List<&2, Instr>:
  match c:
    case Cx{code, len, env, fault}:
      code

def cx_len(+c: Cx) -> Nat:
  match c:
    case Cx{code, len, env, fault}:
      len

def cx_env(+c: Cx) -> Env:
  match c:
    case Cx{code, len, env, fault}:
      env

def cx_fault(+c: Cx) -> String:
  match c:
    case Cx{code, len, env, fault}:
      fault

# Number literals
# ===============

def digit_ok(+c: Char, +base: Nat) -> Bool:
  +n = Char.to_u32(c)
  S.choose(Bool, U32.is_ge(n, 48) && U32.is_le(n, 57), u => Nat.is_lt((U32.to_nat(n) - 48n : Nat), base), u =>
    S.choose(Bool, U32.is_ge(n, 65) && U32.is_le(n, 70), u => Nat.is_lt((U32.to_nat(n) - 55n : Nat), base), u =>
      S.choose(Bool, U32.is_ge(n, 97) && U32.is_le(n, 102), u => Nat.is_lt((U32.to_nat(n) - 87n : Nat), base), u => False{})))

def digit_val(+c: Char) -> Nat:
  +n = Char.to_u32(c)
  S.choose(Nat, U32.is_ge(n, 48) && U32.is_le(n, 57), u => (U32.to_nat(n) - 48n : Nat), u =>
    S.choose(Nat, U32.is_ge(n, 65) && U32.is_le(n, 70), u => (U32.to_nat(n) - 55n : Nat), u =>
      (U32.to_nat(n) - 87n : Nat)))

type NV is Data:
  NV{n: Nat, fault: String}

def nv_n(+p: NV) -> Nat:
  match p:
    case NV{n, fault}:
      n

def nv_f(+p: NV) -> String:
  match p:
    case NV{n, fault}:
      fault

def digits(+s: String, +base: Nat, +acc: Nat) -> NV:
  match s:
    case SNil{}:
      NV{acc, ""}
    case SCon{+h, +t}:
      S.choose(NV, Char.is_eq(h, '_'), u => digits(t, base, acc), u =>
        S.choose(NV, Char.is_eq(h, '.') || Char.is_eq(h, 'e') || Char.is_eq(h, 'E') || Char.is_eq(h, 'j') || Char.is_eq(h, 'J'),
          u => NV{0n, "floats and complex literals are outside the subset"}, u =>
          S.choose(NV, digit_ok(h, base), u => digits(t, base, (base * acc + digit_val(h) : Nat)), u => NV{0n, "invalid digit in literal"})))

def number_value(+raw: String) -> NV:
  S.choose(NV, String.starts_with(raw, "0x") || String.starts_with(raw, "0X"), u => digits(String.drop(raw, 2n), 16n, 0n), u =>
    S.choose(NV, String.starts_with(raw, "0o") || String.starts_with(raw, "0O"), u => digits(String.drop(raw, 2n), 8n, 0n), u =>
      S.choose(NV, String.starts_with(raw, "0b") || String.starts_with(raw, "0B"), u => digits(String.drop(raw, 2n), 2n, 0n), u =>
        digits(raw, 10n, 0n))))

# Tables
# ======

type AC is Data:
  AC{env: Env, idx: Nat}

def ac_env(+p: AC) -> Env:
  match p:
    case AC{env, idx}:
      env

def ac_idx(+p: AC) -> Nat:
  match p:
    case AC{env, idx}:
      idx

def add_const(+env: Env, +v: Val) -> AC:
  Env{+cs, nc, +gs, ng, +fs, +ns, nn} = env
  AC{Env{Con{v, cs}, 1n+nc, gs, ng, fs, ns, nn}, nc}

def local_find(+ns: List<&2, String>, +name: String, +i: Nat) -> Maybe<&2, Nat>:
  match ns:
    case Nil{}:
      None{}
    case Con{h, t}:
      S.choose(Maybe<&2, Nat>, String.eq(h, name), u => Some{i}, u => local_find(t, name, 1n+i))

def global_find(+gs: List<&2, String>, +name: String, +i: Nat) -> Maybe<&2, Nat>:
  match gs:
    case Nil{}:
      None{}
    case Con{h, t}:
      S.choose(Maybe<&2, Nat>, String.eq(h, name), u => Some{i}, u => global_find(t, name, 1n+i))

type GS is Data:
  GS{env: Env, slot: Nat}

def gs_env(+p: GS) -> Env:
  match p:
    case GS{env, slot}:
      env

def gs_slot(+p: GS) -> Nat:
  match p:
    case GS{env, slot}:
      slot

# The global slot: found by name, else a fresh row at the end.
def gslot_put(+found: Maybe<&2, Nat>, +env: Env, +name: String, +gs: List<&2, String>, +ng: Nat) -> GS:
  match found:
    case Some{i}:
      GS{env, Nat.sub(ng, 1n+i)}
    case None{}:
      Env{+cs, nc, gs2, ng2, +fs, +ns, nn} = env
      GS{Env{cs, nc, Con{name, gs}, 1n+ng, fs, ns, nn}, ng}

def gslot(+env: Env, +name: String) -> GS:
  Env{+cs, nc, +gs, +ng, +fs, +ns, nn} = env
  gslot_put(global_find(gs, name, 0n), Env{cs, nc, gs, ng, fs, ns, nn}, name, gs, ng)

def func_hit(+fs: List<&2, Def>, +name: String) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case Con{Def{nm, params, np, body}, t}:
      S.choose(Bool, String.eq(nm, name), u => True{}, u => func_hit(t, name))

def func_ix(+fs: List<&2, Def>, +name: String, +i: Nat) -> Nat:
  match fs:
    case Nil{}:
      0n
    case Con{Def{nm, params, np, body}, t}:
      S.choose(Nat, String.eq(nm, name), u => i, u => func_ix(t, name, 1n+i))

def func_find(+fs: List<&2, Def>, +name: String, +i: Nat) -> Maybe<&2, Nat>:
  match fs:
    case Nil{}:
      None{}
    case Con{Def{nm, params, np, body}, t}:
      S.choose(Maybe<&2, Nat>, String.eq(nm, name), u => Some{i}, u => func_find(t, name, 1n+i))

def f_np(+f: Func) -> Nat:
  match f:
    case Func{np, nl, code}:
      np

def f_nl(+f: Func) -> Nat:
  match f:
    case Func{np, nl, code}:
      nl

def f_code(+f: Func) -> List<&2, Instr>:
  match f:
    case Func{np, nl, code}:
      code

def nparams_at(+fs: List<&2, Def>, i: Nat) -> Nat:
  match fs i:
    case Con{Def{nm, params, np, body}, t} 0n:
      np
    case Con{d, t} 1n+p:
      nparams_at(t, p)
    case _ _:
      0n

# Operator tags -> dense opcode rows; 99 is not an opcode.
def binop_code(+tag: String) -> U32:
  S.choose(U32, String.eq(tag, "Add"), u => 6, u =>
    S.choose(U32, String.eq(tag, "Sub"), u => 7, u =>
      S.choose(U32, String.eq(tag, "Mult"), u => 8, u =>
        S.choose(U32, String.eq(tag, "FloorDiv"), u => 9, u =>
          S.choose(U32, String.eq(tag, "Mod"), u => 10, u => 99)))))

def cmp_code(+tag: String) -> U32:
  S.choose(U32, String.eq(tag, "Lt"), u => 11, u =>
    S.choose(U32, String.eq(tag, "LtE"), u => 12, u =>
      S.choose(U32, String.eq(tag, "Gt"), u => 13, u =>
        S.choose(U32, String.eq(tag, "GtE"), u => 14, u =>
          S.choose(U32, String.eq(tag, "Eq"), u => 15, u =>
            S.choose(U32, String.eq(tag, "NotEq"), u => 16, u => 99))))))

# The local table of a function: params first, then every assigned name
# (Python's own rule: a name assigned anywhere in the body is local).
def has_name(+ns: List<&2, String>, +name: String) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case Con{h, t}:
      S.choose(Bool, String.eq(h, name), u => True{}, u => has_name(t, name))

def add_name(+ns: List<&2, String>, +name: String) -> List<&2, String>:
  Bool.pick(List<&2, String>, has_name(ns, name), ns, Con{name, ns})

def prewalk_target(+j: S.Json, +ns: List<&2, String>) -> List<&2, String>:
  S.choose(List<&2, String>, String.eq(jtag(j), "Name"), u => add_name(ns, jstr(jfield(j, "id"))), u => ns)

def prewalk_targets(+js: S.Json, +ns: List<&2, String>) -> List<&2, String>:
  match js:
    case S.JEnd{}:
      ns
    case S.JItem{one, rest}:
      prewalk_targets(rest, prewalk_target(one, ns))
    case _:
      ns

type PW is Data:
  PWOne{tag: String, j: S.Json}
  PWChain{js: S.Json}

# The local-name prewalk: one self-recursive def (a chain and a statement
# would be mutually recursive otherwise), the leaf helpers beside it.
def prewalk(fuel: Nat, job: PW, +ns: List<&2, String>) -> List<&2, String>:
  match fuel job:
    case 0n _:
      ns
    case 1n++left PWChain{js}:
      match js:
        case S.JItem{+one, rest}:
          +tag : String = jtag(one)
          prewalk(left, PWChain{rest}, prewalk(left, PWOne{tag, one}, ns))
        case _:
          ns
    case 1n++left PWOne{+tag, +j}:
      match tag:
        case "Assign":
          prewalk_targets(jitems(jfield(j, "targets")), ns)
        case "AugAssign":
          prewalk_target(jfield(j, "target"), ns)
        case "AnnAssign":
          S.choose(List<&2, String>, jnull(jfield(j, "value")), u => ns, u => prewalk_target(jfield(j, "target"), ns))
        case "If":
          prewalk(left, PWChain{jitems(jfield(j, "orelse"))}, prewalk(left, PWChain{jitems(jfield(j, "body"))}, ns))
        case "While":
          prewalk(left, PWChain{jitems(jfield(j, "orelse"))}, prewalk(left, PWChain{jitems(jfield(j, "body"))}, ns))
        case _:
          ns

# Fuels are derived from the module (runtime data), never written as one
# long constant: a folded constant fuel expands unary in the emitter.
def stmt_fuel(+body: S.Json) -> Nat:
  Nat.mul(Nat.mul(100n, 100n), Nat.add(count(body, 1n), 1n))

# Pass 1: the module's defs, collected reversed.
type GD is Data:
  GD{defs: List<&2, Def>, fault: String}

def gd_defs(+p: GD) -> List<&2, Def>:
  match p:
    case GD{defs, fault}:
      defs

def gd_flt(+p: GD) -> String:
  match p:
    case GD{defs, fault}:
      fault

type PN is Data:
  PN{names: List<&2, String>, fault: String}

def pn_names(+p: PN) -> List<&2, String>:
  match p:
    case PN{names, fault}:
      names

def pn_flt(+p: PN) -> String:
  match p:
    case PN{names, fault}:
      fault

def param_names(+js: S.Json, +acc: List<&2, String>, +flt: String) -> PN:
  match js:
    case S.JEnd{}:
      PN{acc, flt}
    case S.JItem{one, rest}:
      S.choose(PN, String.eq(jtag(one), "arg"), u =>
        param_names(rest, Con{jstr(jfield(one, "arg")), acc}, flt), u => PN{acc, "expected parameter"})
    case _:
      PN{acc, "expected parameter"}

def take_def(+j: S.Json, +defs: List<&2, Def>) -> GD:
  +decorated = jitems(jfield(j, "decorator_list"))
  +arguments = jfield(j, "args")
  S.choose(GD, Bool.not(jnull(jfield(arguments, "vararg"))) || Bool.not(jnull(jfield(arguments, "kwarg"))) || Bool.not(jend(jitems(jfield(arguments, "kwonlyargs")))),
    u => GD{defs, "*args, keyword-only and **kwargs parameters are outside the subset"}, u =>
    S.choose(GD, Bool.not(jend(decorated)), u => GD{defs, "decorators are outside the subset"}, u =>
      +po : PN = param_names(jitems(jfield(arguments, "posonlyargs")), Nil{}, "")
      +pa : PN = param_names(jitems(jfield(arguments, "args")), pn_names(po), "")
      S.choose(GD, String.is_empty(pn_flt(po)) && String.is_empty(pn_flt(pa)), u =>
        +params = List.reverse(&2, String, pn_names(pa))
        GD{Con{Def{jstr(jfield(j, "name")), params, List.length(&2, String, params), jitems(jfield(j, "body"))}, defs}, ""}, u =>
        GD{defs, pick_fault(pn_flt(po), pn_flt(pa))})))


def collect(+js: S.Json, +defs: List<&2, Def>) -> GD:
  match js:
    case S.JEnd{}:
      GD{defs, ""}
    case S.JItem{+one, +rest}:
      +got : GD = collect(rest, defs)
      +tag : String = jtag(one)
      S.choose(GD, String.eq(tag, "FunctionDef"), u =>
        +td : GD = take_def(one, gd_defs(got))
        GD{gd_defs(td), pick_fault(gd_flt(got), gd_flt(td))}, u =>
        got)
    case _:
      GD{defs, ""}

# Pass 2 prep: the module body minus its defs.
def skip_defs(+js: S.Json) -> S.Json:
  match js:
    case S.JEnd{}:
      S.JEnd{}
    case S.JItem{one, rest}:
      S.choose(S.Json, String.eq(jtag(one), "FunctionDef"), u => skip_defs(rest), u => S.JItem{one, skip_defs(rest)})
    case _:
      S.JEnd{}

# Expressions
# ===========

def bop_put(+frags: List<&2, Frg>, +end: Nat, +is_and: Bool, +first: Nat, +acc: List<&2, Instr>) -> List<&2, Instr>:
  match frags first:
    case Nil{} _:
      acc
    case Con{Frg{c, l, op}, t} 0n:
      bop_put(t, end, is_and, 1n, join(c, acc))
    case Con{Frg{c, l, op}, t} 1n+p:
      bop_put(t, end, is_and, 1n+p, join(acc, Con{Instr{Bool.pick(U32, is_and, 21, 22), end, 0n}, c}))

# Chained comparisons: a < b < c asks (a<b) and (b<c); the middle operand is
# evaluated twice (the subset's middles are pure; noted in the report).
def cmp_put(+frags: List<&2, Frg>, +end: Nat, +first: Nat, +acc: List<&2, Instr>) -> List<&2, Instr>:
  match frags first:
    case Nil{} _:
      acc
    case Con{Frg{c, l, 98}, t} _:
      cmp_put(t, end, 1n, join(acc, c))
    case Con{Frg{c, l, op}, t} 0n:
      cmp_put(t, end, 1n, join(one(op, 0n, 0n), c))
    case Con{Frg{c, l, op}, t} 1n+p:
      cmp_put(t, end, 1n+p, join(acc, Con{Instr{5, 0n, 0n}, Con{Instr{19, end, 0n}, join(one(op, 0n, 0n), c)}}))

# One self-recursive def compiles every expression shape. Many is a JItem
# chain (call and print arguments, in order). BOp and CmpJ are the two-pass
# chains: the values are compiled first (the walk), then assembled with the
# end target every keep-jump needs. Tag1 re-enters with the tag as a field,
def const_cx(+env: Env, +v: Val) -> Cx:
  +made : AC = add_const(env, v)
  Cx{one(0, ac_idx(made), 0n), 1n, ac_env(made), ""}

# One self-recursive def compiles every expression shape. Many is a JItem
# chain (call and print arguments, in order). BOp and CmpJ are the two-pass
# chains: the values are compiled first (the walk), then assembled with the
# end target every keep-jump needs. Tag1 re-enters with the tag as a field,
# the one legal scrutinee for the dispatch.
type Job is Data:
  One{j: S.Json}
  Many{js: S.Json}
  BOp{js: S.Json, base0: Nat, acc: List<&2, Frg>, sum: Nat, n: Nat, flt: String, is_and: Bool}
  CmpJ{ops: S.Json, vals: S.Json, base0: Nat, acc: List<&2, Frg>, sum: Nat, n: Nat, flt: String}
  Tag1{tag: String, j: S.Json}

def slot_put(+found: Maybe<&2, Nat>, +env: Env, +name: String, is_store: Bool) -> Cx:
  match found:
    case Some{i}:
      Cx{one(Bool.pick(U32, is_store, 2, 1), i, 0n), 1n, env, ""}
    case None{}:
      +slot : GS = gslot(env, name)
      Cx{one(Bool.pick(U32, is_store, 4, 3), gs_slot(slot), 0n), 1n, gs_env(slot), ""}

def name_cx(+env: Env, +name: String, +is_store: Bool) -> Cx:
  Env{+cs, nc, +gs, ng, +fs, +ns, nn} = env
  slot_put(local_find(ns, name, 0n), Env{cs, nc, gs, ng, fs, ns, nn}, name, is_store)

def store_target(+j: S.Json, +base: Nat, +env: Env) -> Cx:
  S.choose(Cx, String.eq(jtag(j), "Name"), u => name_cx(env, jstr(jfield(j, "id")), True{}), u =>
    Cx{Nil{}, 0n, env, "the assignment target is outside the subset"})

def load_target(+j: S.Json, +base: Nat, +env: Env) -> Cx:
  S.choose(Cx, String.eq(jtag(j), "Name"), u => name_cx(env, jstr(jfield(j, "id")), False{}), u =>
    Cx{Nil{}, 0n, env, "the assignment target is outside the subset"})

def cexp(+fuel: Nat, +job: Job, +base: Nat, +env: Env) -> Cx:
  match fuel job:
    case 0n _:
      Cx{Nil{}, 0n, env, "the compiler ran out of fuel"}
    case 1n++left Many{js}:
      match js:
        case S.JEnd{}:
          Cx{Nil{}, 0n, env, ""}
        case S.JItem{+one, +rest}:
          +head : Cx = cexp(left, One{one}, base, env)
          +tail : Cx = cexp(left, Many{rest}, (cx_len(head) + base : Nat), cx_env(head))
          Cx{join(cx_code(tail), cx_code(head)), (cx_len(head) + cx_len(tail) : Nat), cx_env(tail), pick_fault(cx_fault(head), cx_fault(tail))}
        case _:
          Cx{Nil{}, 0n, env, ""}
    case 1n++left BOp{js, base0, acc, sum, n, flt, is_and}:
      match js:
        case S.JEnd{}:
          +extra : Nat = Nat.sub(n, 1n)
          +total = (sum + extra : Nat)
          Cx{bop_put(acc, (total + base0 : Nat), is_and, 0n, Nil{}), total, env, flt}
        case S.JItem{+one, +rest}:
          +head : Cx = cexp(left, One{one}, base, env)
          cexp(left, BOp{rest, base0, Con{Frg{cx_code(head), cx_len(head), 0}, acc}, (sum + cx_len(head) : Nat), 1n+n, pick_fault(flt, cx_fault(head)), is_and},
            (cx_len(head) + base + 1n : Nat), cx_env(head))
        case _:
          Cx{Nil{}, 0n, env, flt}
    case 1n++left CmpJ{ops, vals, base0, acc, sum, n, flt}:
      match ops vals:
        case S.JEnd{} _:
          +extra : Nat = Nat.sub((3n * n : Nat), 2n)
          +total = (sum + extra : Nat)
          Cx{cmp_put(acc, (total + base0 : Nat), 0n, Nil{}), total, env, flt}
        case S.JItem{+op, +opr} S.JItem{+one, +rest}:
          +code = cmp_code(jstr(jfield(op, "tag")))
          S.choose(Cx, U32.is_eq(code, 99), u => Cx{Nil{}, 0n, env, "the comparison is outside the subset"}, u =>
            +head : Cx = cexp(left, One{one}, base, env)
            cexp(left, CmpJ{opr, rest, base0, Con{Frg{cx_code(head), cx_len(head), code}, acc}, (sum + cx_len(head) : Nat), 1n+n, pick_fault(flt, cx_fault(head))},
              (cx_len(head) + base + 3n : Nat), cx_env(head)))
        case _ _:
          Cx{Nil{}, 0n, env, flt}
    case 1n++left One{j}:
      cexp(left, Tag1{jtag(j), j}, base, env)
    case 1n++left Tag1{tag, j}:
      match tag:
        case "Constant":
          +raw = jstr(jfield(j, "_raw"))
          S.choose(Cx, String.eq(raw, "True"), u => const_cx(env, VBool{True{}}), u =>
            S.choose(Cx, String.eq(raw, "False"), u => const_cx(env, VBool{False{}}), u =>
              S.choose(Cx, String.eq(raw, "None"), u => const_cx(env, VNone{}), u =>
                S.choose(Cx, Char.is_digit(headc(raw)) || Char.is_eq(headc(raw), '.'), u =>
                  +nv : NV = number_value(raw)
                  S.choose(Cx, String.is_empty(nv_f(nv)), u => const_cx(env, VInt{nv_n(nv)}), u => Cx{Nil{}, 0n, env, nv_f(nv)}), u =>
                  Cx{Nil{}, 0n, env, "strings are outside the subset"}))))
        case "Name":
          name_cx(env, jstr(jfield(j, "id")), False{})
        case "BinOp":
          +lft : Cx = cexp(left, One{jfield(j, "left")}, base, env)
          +rgt : Cx = cexp(left, One{jfield(j, "right")}, (cx_len(lft) + base : Nat), cx_env(lft))
          +code = binop_code(jstr(jfield(jfield(j, "op"), "tag")))
          S.choose(Cx, U32.is_eq(code, 99), u => Cx{Nil{}, 0n, cx_env(rgt), "the operator is outside the subset"}, u =>
            Cx{join(one(code, 0n, 0n), join(cx_code(rgt), cx_code(lft))), 1n+(cx_len(lft) + cx_len(rgt) : Nat), cx_env(rgt),
              pick_fault(cx_fault(lft), cx_fault(rgt))})
        case "UnaryOp":
          +op = jstr(jfield(jfield(j, "op"), "tag"))
          S.choose(Cx, String.eq(op, "UAdd"), u => cexp(left, One{jfield(j, "operand")}, base, env), u =>
            S.choose(Cx, String.eq(op, "Not"), u =>
              +inner : Cx = cexp(left, One{jfield(j, "operand")}, base, env)
              Cx{join(one(17, 0n, 0n), cx_code(inner)), 1n+cx_len(inner), cx_env(inner), cx_fault(inner)}, u =>
              Cx{Nil{}, 0n, env, "negatives and ~ are outside the subset"}))
        case "BoolOp":
          cexp(left, BOp{jitems(jfield(j, "values")), base, Nil{}, 0n, 0n, "", String.eq(jstr(jfield(jfield(j, "op"), "tag")), "And")}, base, env)
        case "Compare":
          +ops = jitems(jfield(j, "ops"))
          S.choose(Cx, Nat.is_eq(jcount(ops), 1n), u =>
            +lft : Cx = cexp(left, One{jfield(j, "left")}, base, env)
            cexp(left, CmpJ{ops, jitems(jfield(j, "comparators")), base, Con{Frg{cx_code(lft), cx_len(lft), 98}, Nil{}}, cx_len(lft), 0n, cx_fault(lft)},
              (cx_len(lft) + base : Nat), cx_env(lft)), u =>
            Cx{Nil{}, 0n, env, "chained comparisons are outside the subset"})
        case "Call":
          Env{+cs, +nc, +gs, +ng, +fs, +ns, +nn} = env
          +fn = jfield(j, "func")
          +kw = jitems(jfield(j, "keywords"))
          +args = jitems(jfield(j, "args"))
          S.choose(Cx, Bool.not(String.eq(jtag(fn), "Name")), u => Cx{Nil{}, 0n, Env{cs, nc, gs, ng, fs, ns, nn}, "calling a non-name is outside the subset"}, u =>
            S.choose(Cx, Bool.not(jend(kw)), u => Cx{Nil{}, 0n, Env{cs, nc, gs, ng, fs, ns, nn}, "keyword arguments are outside the subset"}, u =>
              +name = jstr(jfield(fn, "id"))
              S.choose(Cx, String.eq(name, "print"), u =>
                +argv : Cx = cexp(left, Many{args}, base, Env{cs, nc, gs, ng, fs, ns, nn})
                Cx{join(one(25, 0n, jcount(args)), cx_code(argv)), 1n+cx_len(argv), cx_env(argv), cx_fault(argv)}, u =>
                S.choose(Cx, func_hit(fs, name), u =>
                  +i : Nat = func_ix(fs, name, 0n)
                  +argv : Cx = cexp(left, Many{args}, base, Env{cs, nc, gs, ng, fs, ns, nn})
                  S.choose(Cx, Nat.is_eq(jcount(args), nparams_at(fs, i)), u =>
                    Cx{join(one(23, i, jcount(args)), cx_code(argv)), 1n+cx_len(argv), cx_env(argv), cx_fault(argv)}, u =>
                    Cx{Nil{}, 0n, cx_env(argv), String.append(name, " is called with the wrong number of arguments")}), u =>
                  Cx{Nil{}, 0n, Env{cs, nc, gs, ng, fs, ns, nn}, String.append(name, " is not a defined function")}))))
        case "IfExp":
          +test : Cx = cexp(left, One{jfield(j, "test")}, base, env)
          +body : Cx = cexp(left, One{jfield(j, "body")}, (cx_len(test) + base + 1n : Nat), cx_env(test))
          +other : Cx = cexp(left, One{jfield(j, "orelse")}, (cx_len(test) + base + cx_len(body) + 2n : Nat), cx_env(body))
          Cx{join(cx_code(other), join(one(18, (cx_len(test) + base + cx_len(body) + cx_len(other) + 2n : Nat), 0n),
              join(cx_code(body), join(one(19, (cx_len(test) + base + cx_len(body) + 2n : Nat), 0n), cx_code(test))))),
            (cx_len(test) + cx_len(body) + cx_len(other) + 2n : Nat), cx_env(other),
            pick_fault(cx_fault(test), pick_fault(cx_fault(body), cx_fault(other)))}
        case _:
          Cx{Nil{}, 0n, env, "the expression is outside the subset"}

# `a and b and c`: each value but the last keeps itself on the stack when it
# decides the answer (JIFK for and, JITK for or), else pops and asks the
# next -- CPython's operand-values semantics, not a bare short-circuit.
# Statements
# ==========

# Walk compiles a JItem chain; TagS re-enters with the statement's tag as a
# field and compiles exactly one statement, then joins the chain's rest.
type SJ is Data:
  Walk{js: S.Json}
  TagS{tag: String, one: S.Json, rest: S.Json}

def store_join(+fuel: Nat, +target: S.Json, +value: Cx, +base: Nat) -> Cx:
  Cx{vcode, vlen, venv, vfault} = value
  +stored : Cx = store_target(target, (vlen + base : Nat), venv)
  Cx{join(cx_code(stored), vcode), (vlen + cx_len(stored) : Nat), cx_env(stored), pick_fault(vfault, cx_fault(stored))}

def aug_assign(+fuel: Nat, +sj: S.Json, +base: Nat, +env: Env) -> Cx:
  +code = binop_code(jstr(jfield(jfield(sj, "op"), "tag")))
  S.choose(Cx, U32.is_eq(code, 99), u => Cx{Nil{}, 0n, env, "the augmented operator is outside the subset"}, u =>
    +loaded : Cx = load_target(jfield(sj, "target"), base, env)
    +value : Cx = cexp(fuel, One{jfield(sj, "value")}, (cx_len(loaded) + base : Nat), cx_env(loaded))
    +stored : Cx = store_target(jfield(sj, "target"), (cx_len(loaded) + base + cx_len(value) + 1n : Nat), cx_env(value))
    Cx{join(cx_code(stored), join(one(code, 0n, 0n), join(cx_code(value), cx_code(loaded)))),
      (cx_len(loaded) + cx_len(value) + cx_len(stored) + 1n : Nat), cx_env(stored),
      pick_fault(cx_fault(loaded), pick_fault(cx_fault(value), cx_fault(stored)))})

def cstmt(+fuel: Nat, +job: SJ, +base: Nat, +env: Env) -> Cx:
  match fuel job:
    case 0n _:
      Cx{Nil{}, 0n, env, "the compiler ran out of fuel"}
    case 1n++left Walk{js}:
      match js:
        case S.JEnd{}:
          Cx{Nil{}, 0n, env, ""}
        case S.JItem{+h, +t}:
          cstmt(left, TagS{jtag(h), h, t}, base, env)
        case _:
          Cx{Nil{}, 0n, env, ""}
    case 1n++left TagS{+tag, +sj, +rest}:
      +self : Cx = S.choose(Cx, String.eq(tag, "Pass"), u => Cx{Nil{}, 0n, env, ""}, u =>
        S.choose(Cx, String.eq(tag, "Expr"), u =>
          +inner : Cx = cexp(left, One{jfield(sj, "value")}, base, env)
          Cx{join(one(5, 0n, 0n), cx_code(inner)), 1n+cx_len(inner), cx_env(inner), cx_fault(inner)}, u =>
        S.choose(Cx, String.eq(tag, "Assign"), u =>
          +targets = jitems(jfield(sj, "targets"))
          S.choose(Cx, Nat.is_eq(count(targets, 0n), 1n), u =>
            +value : Cx = cexp(left, One{jfield(sj, "value")}, base, env)
            store_join(left, first_of(targets), value, base), u =>
            Cx{Nil{}, 0n, env, "multiple assignment targets are outside the subset"}), u =>
        S.choose(Cx, String.eq(tag, "AugAssign"), u => aug_assign(left, sj, base, env), u =>
        S.choose(Cx, String.eq(tag, "AnnAssign"), u =>
          S.choose(Cx, jnull(jfield(sj, "value")), u => Cx{Nil{}, 0n, env, ""}, u =>
            +value : Cx = cexp(left, One{jfield(sj, "value")}, base, env)
            store_join(left, jfield(sj, "target"), value, base)), u =>
        S.choose(Cx, String.eq(tag, "Return"), u =>
          S.choose(Cx, jnull(jfield(sj, "value")), u =>
            +made : AC = add_const(env, VNone{})
            Cx{join(one(24, 0n, 0n), one(0, ac_idx(made), 0n)), 2n, ac_env(made), ""}, u =>
            +value : Cx = cexp(left, One{jfield(sj, "value")}, base, env)
            Cx{join(one(24, 0n, 0n), cx_code(value)), 1n+cx_len(value), cx_env(value), cx_fault(value)}), u =>
        S.choose(Cx, String.eq(tag, "If"), u =>
          +test : Cx = cexp(left, One{jfield(sj, "test")}, base, env)
          +body : Cx = cstmt(left, Walk{jitems(jfield(sj, "body"))}, (cx_len(test) + base + 1n : Nat), cx_env(test))
          +other : Cx = cstmt(left, Walk{jitems(jfield(sj, "orelse"))}, (cx_len(test) + base + cx_len(body) + 2n : Nat), cx_env(body))
          Cx{join(cx_code(other), join(one(18, (cx_len(test) + base + cx_len(body) + cx_len(other) + 2n : Nat), 0n),
              join(cx_code(body), join(one(19, (cx_len(test) + base + cx_len(body) + 2n : Nat), 0n), cx_code(test))))),
            (cx_len(test) + cx_len(body) + cx_len(other) + 2n : Nat), cx_env(other),
            pick_fault(cx_fault(test), pick_fault(cx_fault(body), cx_fault(other)))}, u =>
        S.choose(Cx, String.eq(tag, "While"), u =>
          +test : Cx = cexp(left, One{jfield(sj, "test")}, base, env)
          +body : Cx = cstmt(left, Walk{jitems(jfield(sj, "body"))}, (cx_len(test) + base + 1n : Nat), cx_env(test))
          +other : Cx = cstmt(left, Walk{jitems(jfield(sj, "orelse"))}, (cx_len(test) + base + cx_len(body) + 2n : Nat), cx_env(body))
          Cx{join(cx_code(other), join(one(18, base, 0n),
              join(cx_code(body), join(one(19, (cx_len(test) + base + cx_len(body) + 2n : Nat), 0n), cx_code(test))))),
            (cx_len(test) + cx_len(body) + cx_len(other) + 2n : Nat), cx_env(other),
            pick_fault(cx_fault(test), pick_fault(cx_fault(body), cx_fault(other)))}, u =>
          Cx{Nil{}, 0n, env, "the statement is outside the subset"}))))))))
      +after : Cx = cstmt(left, Walk{rest}, (cx_len(self) + base : Nat), cx_env(self))
      Cx{join(cx_code(after), cx_code(self)), (cx_len(self) + cx_len(after) : Nat), cx_env(after), pick_fault(cx_fault(self), cx_fault(after))}

# Assign/AnnAssign: the value, then the store.
type BD is Data:
  BD{func: Func, env: Env, fault: String}

def bd_func(+p: BD) -> Func:
  match p:
    case BD{func, env, fault}:
      func

def bd_env(+p: BD) -> Env:
  match p:
    case BD{func, env, fault}:
      env

def bd_flt(+p: BD) -> String:
  match p:
    case BD{func, env, fault}:
      fault

def compile_def(+d: Def, +env: Env) -> BD:
  Def{name, +params, np, body} = d
  Env{+cs, +nc, +gs, +ng, +fs, +ns, +nn} = env
  +assigned = prewalk(stmt_fuel(body), PWChain{body}, Nil{})
  +names = List.append(&2, String, params, List.reverse(&2, String, assigned))
  +nnames = List.length(&2, String, names)
  +inner : Cx = cstmt(stmt_fuel(body), Walk{body}, 0n, Env{cs, nc, gs, ng, fs, names, nnames})
  +made : AC = add_const(cx_env(inner), VNone{})
  +full = join(one(24, 0n, 0n), join(one(0, ac_idx(made), 0n), cx_code(inner)))
  BD{Func{np, nnames, List.reverse(&2, Instr, full)}, ac_env(made), cx_fault(inner)}

type Built is Data:
  Built{funcs: List<&2, Func>, env: Env, fault: String}

def bu_funcs(+p: Built) -> List<&2, Func>:
  match p:
    case Built{funcs, env, fault}:
      funcs

def bu_env(+p: Built) -> Env:
  match p:
    case Built{funcs, env, fault}:
      env

def bu_flt(+p: Built) -> String:
  match p:
    case Built{funcs, env, fault}:
      fault

def compile_defs(+defs: List<&2, Def>, env: Env, acc: List<&2, Func>) -> Built:
  match defs:
    case Nil{}:
      Built{List.reverse(&2, Func, acc), env, ""}
    case Con{d, t}:
      +made : BD = compile_def(d, env)
      +rest : Built = compile_defs(t, bd_env(made), Con{bd_func(made), acc})
      Built{bu_funcs(rest), bu_env(rest), pick_fault(bd_flt(made), bu_flt(rest))}

def env_consts(+e: Env) -> List<&2, Val>:
  match e:
    case Env{cs, nc, gs, ng, fs, ns, nn}:
      cs

def env_nglobals(+e: Env) -> Nat:
  match e:
    case Env{cs, nc, gs, ng, fs, ns, nn}:
      ng

def build(+m: S.Module) -> Result<&2, &2, S.Error, Prog>:
  S.Module{body} = m
  +got : GD = collect(body, Nil{})
  +defs = List.reverse(&2, Def, gd_defs(got))
  +clean : S.Json = skip_defs(body)
  +main : Cx = cstmt(stmt_fuel(clean), Walk{clean}, 0n, Env{Nil{}, 0n, Nil{}, 0n, defs, Nil{}, 0n})
  +done : Built = compile_defs(defs, cx_env(main), Nil{})
  +halted : List<&2, Instr> = Con{Instr{26, 0n, 0n}, cx_code(main)}
  +fault = pick_fault(gd_flt(got), pick_fault(cx_fault(main), bu_flt(done)))
  +fin : Env = bu_env(done)
  S.choose(Result<&2, &2, S.Error, Prog>, String.is_empty(fault), u =>
    Done{Prog{bu_funcs(done), List.reverse(&2, Val, env_consts(fin)), env_nglobals(fin), List.reverse(&2, Instr, halted)}}, u =>
    Fail{S.PErr{S.Unsupported{}, S.Pos{1n, 0n}, fault}})

# Runtime
# =======

def val_at(+xs: List<&2, Val>, n: Nat) -> Val:
  match xs n:
    case Nil{} _:
      VNone{}
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+p:
      val_at(t, p)

def val_set(+xs: List<&2, Val>, n: Nat, +v: Val) -> List<&2, Val>:
  match xs n:
    case Nil{} _:
      Nil{}
    case Con{h, t} 0n:
      Con{v, t}
    case Con{h, t} 1n+p:
      Con{h, val_set(t, p, v)}

def func_at(+fs: List<&2, Func>, n: Nat) -> Func:
  match fs n:
    case Nil{} _:
      Func{0n, 0n, Nil{}}
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+p:
      func_at(t, p)

# Popping n values leaves them in stack order: the head of the result is the
# TOP of the stack -- the last value pushed, the right operand of a binop.
# Argument lists want the other order and reverse it at the two call sites.
def pop_vals(+p: Pop) -> List<&2, Val>:
  match p:
    case Pop{args, more}:
      args

def pop_more(+p: Pop) -> List<&2, Val>:
  match p:
    case Pop{args, more}:
      more

def pop_any(+p: Pop) -> Bool:
  match p:
    case Pop{args, more}:
      match args:
        case Nil{}:
          False{}
        case Con{h, t}:
          True{}

def pop_head(+p: Pop) -> Val:
  match p:
    case Pop{args, more}:
      val_at(args, 0n)

def pop_second(+p: Pop) -> Val:
  match p:
    case Pop{args, more}:
      val_at(args, 1n)

def frames_ok(+fs: List<&2, VFrame>) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case Con{h, t}:
      True{}

def frame_of(+fs: List<&2, VFrame>) -> VFrame:
  match fs:
    case Nil{}:
      VFrame{Nil{}, Nil{}, Nil{}}
    case Con{h, t}:
      h

def frames_tail(+fs: List<&2, VFrame>) -> List<&2, VFrame>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      t

def vh_here(+f: VFrame) -> List<&2, Instr>:
  match f:
    case VFrame{here, rest, locals}:
      here

def vh_rest(+f: VFrame) -> List<&2, Instr>:
  match f:
    case VFrame{here, rest, locals}:
      rest

def vh_locals(+f: VFrame) -> List<&2, Val>:
  match f:
    case VFrame{here, rest, locals}:
      locals

def cmp_pick(+which: Nat, +x: Nat, +y: Nat) -> Bool:
  match which:
    case 0n:
      Nat.is_ne(x, y)
    case 11n:
      Nat.is_lt(x, y)
    case 12n:
      Nat.is_le(x, y)
    case 13n:
      Nat.is_gt(x, y)
    case 14n:
      Nat.is_ge(x, y)
    case 15n:
      Nat.is_eq(x, y)
    case 1n+p:
      Nat.is_ne(x, y)


def pop_args(+n: Nat, +stack: List<&2, Val>) -> Pop:
  match n stack:
    case 0n _:
      Pop{Nil{}, stack}
    case 1n+p Con{v, t}:
      +below : Pop = pop_args(p, t)
      Pop{Con{v, pop_vals(below)}, pop_more(below)}
    case 1n+p Nil{}:
      Pop{Nil{}, Nil{}}

def nones(+n: Nat, +xs: List<&2, Val>) -> List<&2, Val>:
  match n:
    case 0n:
      xs
    case 1n+p:
      Con{VNone{}, nones(p, xs)}

def truthy(+v: Val) -> Bool:
  match v:
    case VInt{n}:
      Nat.is_ne(n, 0n)
    case VBool{b}:
      b
    case VNone{}:
      False{}

# CPython's bools are ints: True is 1 in arithmetic and comparison.
def nums_ok(+a: Val, +b: Val) -> Bool:
  match a b:
    case VInt{x} VInt{y}:
      True{}
    case VInt{x} VBool{q}:
      True{}
    case VBool{p} VInt{y}:
      True{}
    case VBool{p} VBool{q}:
      True{}
    case _ _:
      False{}

type NN is Data:
  NN{x: Nat, y: Nat}

def num2(+a: Val, +b: Val) -> NN:
  match a b:
    case VInt{x} VInt{y}:
      NN{x, y}
    case VInt{x} VBool{q}:
      NN{x, Bool.pick(Nat, q, 1n, 0n)}
    case VBool{p} VInt{y}:
      NN{Bool.pick(Nat, p, 1n, 0n), y}
    case VBool{p} VBool{q}:
      NN{Bool.pick(Nat, p, 1n, 0n), Bool.pick(Nat, q, 1n, 0n)}
    case _ _:
      NN{0n, 0n}

def nn_x(+p: NN) -> Nat:
  match p:
    case NN{x, y}:
      x

def nn_y(+p: NN) -> Nat:
  match p:
    case NN{x, y}:
      y

def vtext(+v: Val) -> String:
  match v:
    case VInt{n}:
      Nat.show(n)
    case VBool{b}:
      Bool.pick(String, b, "True", "False")
    case VNone{}:
      "None"

def line(+vs: List<&2, Val>, acc: String, first: Bool) -> String:
  match vs:
    case Nil{}:
      String.append(acc, "\n")
    case Con{h, t}:
      S.choose(String, first, u => line(t, vtext(h), False{}), u => line(t, String.append(String.append(acc, " "), vtext(h)), False{}))

def fault_run(funcs: List<&2, Func>, consts: List<&2, Val>, stack: List<&2, Val>, here: List<&2, Instr>,
  locals: List<&2, Val>, globals: List<&2, Val>, frames: List<&2, VFrame>, out: List<&2, String>, msg: String) -> Run:
  Run{funcs, consts, stack, here, Nil{}, locals, globals, frames, out, msg}

# The VM. One step per instruction: the fetch is the head of `rest` (a zipper,
# O(1)), a jump re-drops from `here`, a call saves the caller's zipper in a
# frame. The dispatch is the dense U32 match over op -- contiguous 0..26.
# The opcode kind: one constructor per dense opcode row. The dispatch over
# the run is a total constructor match (every body emitted once, no bit
# tree); op -> kind is the dense U32 match, contiguous 0..26 -- the new
# compiler's table shape, and what it lowers to is measured in the report.
type OpKind is Data:
  KConst{}
  KLoadL{}
  KStoreL{}
  KLoadG{}
  KStoreG{}
  KPop{}
  KAdd{}
  KSub{}
  KMul{}
  KDiv{}
  KMod{}
  KLt{}
  KLtE{}
  KGt{}
  KGtE{}
  KEq{}
  KNeq{}
  KNot{}
  KJump{}
  KJif{}
  KJit{}
  KJifk{}
  KJitk{}
  KCall{}
  KRet{}
  KPrint{}
  KHalt{}
  KBad{}

def op_kind(op: U32) -> OpKind:
  match op:
    case 0:
      KConst{}
    case 1:
      KLoadL{}
    case 2:
      KStoreL{}
    case 3:
      KLoadG{}
    case 4:
      KStoreG{}
    case 5:
      KPop{}
    case 6:
      KAdd{}
    case 7:
      KSub{}
    case 8:
      KMul{}
    case 9:
      KDiv{}
    case 10:
      KMod{}
    case 11:
      KLt{}
    case 12:
      KLtE{}
    case 13:
      KGt{}
    case 14:
      KGtE{}
    case 15:
      KEq{}
    case 16:
      KNeq{}
    case 17:
      KNot{}
    case 18:
      KJump{}
    case 19:
      KJif{}
    case 20:
      KJit{}
    case 21:
      KJifk{}
    case 22:
      KJitk{}
    case 23:
      KCall{}
    case 24:
      KRet{}
    case 25:
      KPrint{}
    case 26:
      KHalt{}
    case _:
      KBad{}

# The VM. One step per instruction: the fetch is the head of `rest` (a zipper,
# O(1)), a jump re-drops from `here`, a call saves the caller's zipper in a
# frame. Go fetches the next instruction and re-enters with its kind; the
# kind arms are the dispatch. Every stack match rides in a helper body: an
# arm of a literal match that matches an outer binder directly trips the
# checker's flatten.
# The VM's step mode. Go fetches the next instruction and re-enters flat: the
# kind match must be the arm's first statement (an intervening binder
# consumes the field's quantity in the checker's flatten), so Op carries the
# run's ten fields directly. One step per instruction: the fetch is the head
# of `rest` (a zipper, O(1)), a jump re-drops from `here`, a call saves the
# caller's zipper in a frame.
type Step is Data:
  Go{run: Run}
  Op{kind: OpKind, a: Nat, b: Nat, more: List<&2, Instr>, funcs: List<&2, Func>, consts: List<&2, Val>,
     stack: List<&2, Val>, here: List<&2, Instr>, rest: List<&2, Instr>, locals: List<&2, Val>,
     globals: List<&2, Val>, frames: List<&2, VFrame>, out: List<&2, String>, fault: String}

def step(+fuel: Nat, +job: Step) -> Run:
  match fuel job:
    case 0n _:
      Run{Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, "the VM ran out of fuel"}
    case 1n++left Go{Run{+funcs, +consts, +stack, +here, +rest, +locals, +globals, +frames, +out, +fault}}:
      match rest:
        case Nil{}:
          fault_run(funcs, consts, stack, here, locals, globals, frames, out, "stepped past the end of the code")
        case Con{Instr{op, a, b}, more}:
          step(left, Op{op_kind(op), a, b, more, funcs, consts, stack, here, rest, locals, globals, frames, out, fault})
    case 1n++left Op{+kind, +a, +b, +more, +funcs, +consts, +stack, +here, +rest, +locals, +globals, +frames, +out, +fault}:
      match kind:
        case KConst{}:
          step(left, Go{Run{funcs, consts, Con{val_at(consts, a), stack}, here, more, locals, globals, frames, out, fault}})
        case KLoadL{}:
          step(left, Go{Run{funcs, consts, Con{val_at(locals, a), stack}, here, more, locals, globals, frames, out, fault}})
        case KStoreL{}:
          +picked : Pop = pop_args(1n, stack)
          S.choose(Run, pop_any(picked), u =>
            step(left, Go{Run{funcs, consts, pop_more(picked), here, more, val_set(locals, a, pop_head(picked)), globals, frames, out, fault}}), u =>
            fault_run(funcs, consts, stack, here, locals, globals, frames, out, "stack underflow"))
        case KLoadG{}:
          step(left, Go{Run{funcs, consts, Con{val_at(globals, a), stack}, here, more, locals, globals, frames, out, fault}})
        case KStoreG{}:
          +picked : Pop = pop_args(1n, stack)
          S.choose(Run, pop_any(picked), u =>
            step(left, Go{Run{funcs, consts, pop_more(picked), here, more, locals, val_set(globals, a, pop_head(picked)), frames, out, fault}}), u =>
            fault_run(funcs, consts, stack, here, locals, globals, frames, out, "stack underflow"))
        case KPop{}:
          +picked : Pop = pop_args(1n, stack)
          S.choose(Run, pop_any(picked), u =>
            step(left, Go{Run{funcs, consts, pop_more(picked), here, more, locals, globals, frames, out, fault}}), u =>
            fault_run(funcs, consts, stack, here, locals, globals, frames, out, "stack underflow"))
        case KAdd{}:
          +picked : Pop = pop_args(2n, stack)
          S.choose(Run, nums_ok(pop_head(picked), pop_second(picked)), u =>
            +xy : NN = num2(pop_second(picked), pop_head(picked))
            step(left, Go{Run{funcs, consts, Con{VInt{(nn_x(xy) + nn_y(xy) : Nat)}, pop_more(picked)}, here, more, locals, globals, frames, out, fault}}), u =>
            fault_run(funcs, consts, stack, here, locals, globals, frames, out, "a non-number in +"))
        case KSub{}:
          +picked : Pop = pop_args(2n, stack)
          S.choose(Run, nums_ok(pop_head(picked), pop_second(picked)), u =>
            +xy : NN = num2(pop_second(picked), pop_head(picked))
            S.choose(Run, Nat.is_ge(nn_x(xy), nn_y(xy)), u =>
              step(left, Go{Run{funcs, consts, Con{VInt{Nat.sub(nn_x(xy), nn_y(xy))}, pop_more(picked)}, here, more, locals, globals, frames, out, fault}}), u =>
              fault_run(funcs, consts, stack, here, locals, globals, frames, out, "a negative result is outside the subset")), u =>
            fault_run(funcs, consts, stack, here, locals, globals, frames, out, "a non-number in -"))
        case KMul{}:
          +picked : Pop = pop_args(2n, stack)
          S.choose(Run, nums_ok(pop_head(picked), pop_second(picked)), u =>
            +xy : NN = num2(pop_second(picked), pop_head(picked))
            step(left, Go{Run{funcs, consts, Con{VInt{(nn_x(xy) * nn_y(xy) : Nat)}, pop_more(picked)}, here, more, locals, globals, frames, out, fault}}), u =>
            fault_run(funcs, consts, stack, here, locals, globals, frames, out, "a non-number in *"))
        case KDiv{}:
          +picked : Pop = pop_args(2n, stack)
          S.choose(Run, nums_ok(pop_head(picked), pop_second(picked)), u =>
            +xy : NN = num2(pop_second(picked), pop_head(picked))
            S.choose(Run, Nat.is_ne(nn_y(xy), 0n), u =>
              step(left, Go{Run{funcs, consts, Con{VInt{Nat.div(nn_x(xy), nn_y(xy))}, pop_more(picked)}, here, more, locals, globals, frames, out, fault}}), u =>
              fault_run(funcs, consts, stack, here, locals, globals, frames, out, "division by zero")), u =>
            fault_run(funcs, consts, stack, here, locals, globals, frames, out, "a non-number in //"))
        case KMod{}:
          +picked : Pop = pop_args(2n, stack)
          S.choose(Run, nums_ok(pop_head(picked), pop_second(picked)), u =>
            +xy : NN = num2(pop_second(picked), pop_head(picked))
            S.choose(Run, Nat.is_ne(nn_y(xy), 0n), u =>
              step(left, Go{Run{funcs, consts, Con{VInt{Nat.mod(nn_x(xy), nn_y(xy))}, pop_more(picked)}, here, more, locals, globals, frames, out, fault}}), u =>
              fault_run(funcs, consts, stack, here, locals, globals, frames, out, "division by zero")), u =>
            fault_run(funcs, consts, stack, here, locals, globals, frames, out, "a non-number in %"))
        case KLt{}:
          +picked : Pop = pop_args(2n, stack)
          S.choose(Run, nums_ok(pop_head(picked), pop_second(picked)), u =>
            +xy : NN = num2(pop_second(picked), pop_head(picked))
            step(left, Go{Run{funcs, consts, Con{VBool{cmp_pick(11n, nn_x(xy), nn_y(xy))}, pop_more(picked)}, here, more, locals, globals, frames, out, fault}}), u =>
            fault_run(funcs, consts, stack, here, locals, globals, frames, out, "a non-number in a comparison"))
        case KLtE{}:
          +picked : Pop = pop_args(2n, stack)
          S.choose(Run, nums_ok(pop_head(picked), pop_second(picked)), u =>
            +xy : NN = num2(pop_second(picked), pop_head(picked))
            step(left, Go{Run{funcs, consts, Con{VBool{cmp_pick(12n, nn_x(xy), nn_y(xy))}, pop_more(picked)}, here, more, locals, globals, frames, out, fault}}), u =>
            fault_run(funcs, consts, stack, here, locals, globals, frames, out, "a non-number in a comparison"))
        case KGt{}:
          +picked : Pop = pop_args(2n, stack)
          S.choose(Run, nums_ok(pop_head(picked), pop_second(picked)), u =>
            +xy : NN = num2(pop_second(picked), pop_head(picked))
            step(left, Go{Run{funcs, consts, Con{VBool{cmp_pick(13n, nn_x(xy), nn_y(xy))}, pop_more(picked)}, here, more, locals, globals, frames, out, fault}}), u =>
            fault_run(funcs, consts, stack, here, locals, globals, frames, out, "a non-number in a comparison"))
        case KGtE{}:
          +picked : Pop = pop_args(2n, stack)
          S.choose(Run, nums_ok(pop_head(picked), pop_second(picked)), u =>
            +xy : NN = num2(pop_second(picked), pop_head(picked))
            step(left, Go{Run{funcs, consts, Con{VBool{cmp_pick(14n, nn_x(xy), nn_y(xy))}, pop_more(picked)}, here, more, locals, globals, frames, out, fault}}), u =>
            fault_run(funcs, consts, stack, here, locals, globals, frames, out, "a non-number in a comparison"))
        case KEq{}:
          +picked : Pop = pop_args(2n, stack)
          S.choose(Run, nums_ok(pop_head(picked), pop_second(picked)), u =>
            +xy : NN = num2(pop_second(picked), pop_head(picked))
            step(left, Go{Run{funcs, consts, Con{VBool{cmp_pick(15n, nn_x(xy), nn_y(xy))}, pop_more(picked)}, here, more, locals, globals, frames, out, fault}}), u =>
            fault_run(funcs, consts, stack, here, locals, globals, frames, out, "a non-number in a comparison"))
        case KNeq{}:
          +picked : Pop = pop_args(2n, stack)
          S.choose(Run, nums_ok(pop_head(picked), pop_second(picked)), u =>
            +xy : NN = num2(pop_second(picked), pop_head(picked))
            step(left, Go{Run{funcs, consts, Con{VBool{cmp_pick(16n, nn_x(xy), nn_y(xy))}, pop_more(picked)}, here, more, locals, globals, frames, out, fault}}), u =>
            fault_run(funcs, consts, stack, here, locals, globals, frames, out, "a non-number in a comparison"))
        case KNot{}:
          +picked : Pop = pop_args(1n, stack)
          S.choose(Run, pop_any(picked), u =>
            step(left, Go{Run{funcs, consts, Con{VBool{Bool.not(truthy(pop_head(picked)))}, pop_more(picked)}, here, more, locals, globals, frames, out, fault}}), u =>
            fault_run(funcs, consts, stack, here, locals, globals, frames, out, "stack underflow"))
        case KJump{}:
          step(left, Go{Run{funcs, consts, stack, here, List.drop(&2, Instr, here, a), locals, globals, frames, out, fault}})
        case KJif{}:
          +picked : Pop = pop_args(1n, stack)
          S.choose(Run, pop_any(picked), u =>
            S.choose(Run, truthy(pop_head(picked)), u =>
              step(left, Go{Run{funcs, consts, pop_more(picked), here, more, locals, globals, frames, out, fault}}), u =>
              step(left, Go{Run{funcs, consts, pop_more(picked), here, List.drop(&2, Instr, here, a), locals, globals, frames, out, fault}})), u =>
            fault_run(funcs, consts, stack, here, locals, globals, frames, out, "stack underflow"))
        case KJit{}:
          +picked : Pop = pop_args(1n, stack)
          S.choose(Run, pop_any(picked), u =>
            S.choose(Run, truthy(pop_head(picked)), u =>
              step(left, Go{Run{funcs, consts, pop_more(picked), here, List.drop(&2, Instr, here, a), locals, globals, frames, out, fault}}), u =>
              step(left, Go{Run{funcs, consts, pop_more(picked), here, more, locals, globals, frames, out, fault}})), u =>
            fault_run(funcs, consts, stack, here, locals, globals, frames, out, "stack underflow"))
        case KJifk{}:
          +picked : Pop = pop_args(1n, stack)
          S.choose(Run, pop_any(picked), u =>
            S.choose(Run, truthy(pop_head(picked)), u =>
              step(left, Go{Run{funcs, consts, pop_more(picked), here, more, locals, globals, frames, out, fault}}), u =>
              step(left, Go{Run{funcs, consts, stack, here, List.drop(&2, Instr, here, a), locals, globals, frames, out, fault}})), u =>
            fault_run(funcs, consts, stack, here, locals, globals, frames, out, "stack underflow"))
        case KJitk{}:
          +picked : Pop = pop_args(1n, stack)
          S.choose(Run, pop_any(picked), u =>
            S.choose(Run, truthy(pop_head(picked)), u =>
              step(left, Go{Run{funcs, consts, stack, here, List.drop(&2, Instr, here, a), locals, globals, frames, out, fault}}), u =>
              step(left, Go{Run{funcs, consts, pop_more(picked), here, more, locals, globals, frames, out, fault}})), u =>
            fault_run(funcs, consts, stack, here, locals, globals, frames, out, "stack underflow"))
        case KCall{}:
          +callee : Func = func_at(funcs, a)
          S.choose(Run, Nat.is_eq(b, f_np(callee)), u =>
            +picked : Pop = pop_args(b, stack)
            step(left, Go{Run{funcs, consts, pop_more(picked), f_code(callee), f_code(callee),
              List.append(&2, Val, List.reverse(&2, Val, pop_vals(picked)), nones(Nat.sub(f_nl(callee), b), Nil{})), globals, Con{VFrame{here, more, locals}, frames}, out, fault}}), u =>
            fault_run(funcs, consts, stack, here, locals, globals, frames, out, "a call with the wrong number of arguments"))
        case KRet{}:
          +picked : Pop = pop_args(1n, stack)
          S.choose(Run, pop_any(picked) && frames_ok(frames), u =>
            step(left, Go{Run{funcs, consts, Con{pop_head(picked), pop_more(picked)}, vh_here(frame_of(frames)), vh_rest(frame_of(frames)), vh_locals(frame_of(frames)), globals, frames_tail(frames), out, fault}}), u =>
            fault_run(funcs, consts, stack, here, locals, globals, frames, out, "return outside a call"))
        case KPrint{}:
          +picked : Pop = pop_args(b, stack)
          step(left, Go{Run{funcs, consts, Con{VNone{}, pop_more(picked)}, here, more, locals, globals, frames, Con{line(List.reverse(&2, Val, pop_vals(picked)), "", True{}), out}, fault}})
        case KHalt{}:
          Run{funcs, consts, stack, here, more, locals, globals, frames, out, fault}
        case KBad{}:
          Run{Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, "a bad opcode"}

# Boot
# ====

# Composed, never written long: big Nat literals expand unary in the checker.
def fuel() -> Nat:
  Nat.mul(Nat.mul(100n, 100n), Nat.mul(100n, 100n))

def vm_run(+prog: Prog) -> Run:
  Prog{funcs, consts, nglobals, code} = prog
  step(fuel(), Go{Run{funcs, consts, Nil{}, code, code, Nil{}, List.replicate(Val, nglobals, VNone{}), Nil{}, Nil{}, ""}})

# Composed, never written long: big Nat literals expand unary in the checker.
def finish(+r: Run) -> IO(Unit):
  match r:
    case Run{+funcs, +consts, +stack, +here, +rest, +locals, +globals, +frames, +out, +fault}:
      S.choose(IO(Unit), String.is_empty(fault), u => IO.write(String.concat(List.reverse(&2, String, out))), u =>
        IO.die(Unit, 1, String.append("vm: ", fault)))

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("PY_SOURCE"))
    source : String <- I.load(path)
    ts : List<&2, S.Tok> <- I.unwrap(&2, List<&2, S.Tok>, L.lex(source))
    m : S.Module <- I.unwrap(&2, S.Module, P.parse(ts))
    prog : Prog <- I.unwrap(&2, Prog, build(m))
    r : Run <- IO.pure(Run, vm_run(prog))
    finish(r)