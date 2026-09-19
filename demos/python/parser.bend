# Direct recursion with precedence climbing. No explicit continuation frames.
# Each mode entry consumes residual fuel; the first Nat separately proves descent.
import Base
import ./syntax.bend as S
import ./parse_state.bend as P
import ./nodes.bend as N
import ./operators.bend as O
import ./lexer.bend as L
import ./scanner.bend as C
import ./fstring.bend as F

# These are grammar modes, not saved continuations: recursive results return
# through the ordinary Bend call stack.
type Mode is Data:
  Expression{minimum: Nat}
  Prefix{minimum: Nat}
  Rest{minimum: Nat, left: S.Expr}
  Strings{raw: String, kind: S.Json, start: S.Pos, end: S.Pos}
  Joined{kind: S.Json, start: S.Pos, end: S.Pos, values: S.Json, parts: S.Json}
  FString{ctx: F.Ctx, level: Nat, rest: String, pos: S.Pos, values: S.Json, parts: S.Json}
  Item{minimum: Nat}
  TestList{minimum: Nat}
  Comma{minimum: Nat, items: S.Json, start: S.Pos, end: S.Pos}
  Sequence{kind: String, start: S.Pos, close: String, items: S.Json, separator: Bool}
  Dictionary{start: S.Pos, keys: S.Json, values: S.Json, separator: Bool}
  Arguments{fn: S.Expr, open: S.Pos, args: S.Json, keywords: S.Json, seen_kw: Bool, separator: Bool}
  Boolean{minimum: Nat, level: Nat, operator: String, values: S.Json, start: S.Pos, end: S.Pos}
  Comparison{minimum: Nat, left: S.Expr, ops: S.Json, values: S.Json, start: S.Pos, end: S.Pos}
  Block{top: Bool, statements: S.Json, end: S.Pos}
  Line{}
  Simple{statements: S.Json}
  Small{}
  AfterSmall{first: S.Expr, start: S.Pos, soft: Bool}
  Assignment{targets: S.Json, start: S.Pos}
  Compound{kind: String, start: S.Pos}
  Suite{}
  Clause{word: String, end: S.Pos}
  Optional{word: String, star: Bool}
  Lambda{start: S.Pos}
  Params{close: String, ann: Bool, sig: N.Sig, phase: Nat, separator: Bool}
  Decorators{items: S.Json}
  Def{start: S.Pos, decorators: S.Json}
  For{start: S.Pos}
  Try{start: S.Pos}
  Handlers{start: S.Pos, body: S.Expr, handlers: S.Json, end: S.Pos}
  With{paren: Bool}
  Items{items: S.Json, paren: Bool, separator: Bool}
  Names{kind: String, start: S.Pos, names: S.Json}
  From{start: S.Pos, level: Nat}
  Dotted{dotted: Bool, text: String, start: S.Pos}
  Aliases{dotted: Bool, paren: Bool, names: S.Json, separator: Bool}
  Class{start: S.Pos, decorators: S.Json}
  Slice{}
  Bound{}
  Slices{items: S.Json, start: S.Pos, end: S.Pos}
  Comp{kind: String, head: S.Json, start: S.Pos, close: String, gens: S.Json}
  Ifs{items: S.Json}
  Star{}

# Primitive helpers classify unsupported productions before a syntax error.
def expected(-A: Data, +t: S.Tok, msg: String) -> P.M(A):
  S.choose(P.M(A), O.unsupported(t), u => P.unsupported(A, "production " ++ P.tok_text(t)), u => P.syntax(A, msg))

def non_ascii(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, tail}:
      U32.is_ge(Char.to_u32(c), 128) || non_ascii(tail)


def expression_name(+t: S.Tok) -> P.M(S.Expr):
  # Identifier normalization (NFKC) is a later language expansion.
  S.choose(P.M(S.Expr), Bool.not(non_ascii(P.tok_text(t))), u =>
    do P.M<S.Expr>:
      drop : S.Tok <- P.take
      return N.name(t), u => P.unsupported(S.Expr, "Unicode identifier normalization"))


def comp_start(+t: S.Tok) -> Bool:
  P.is_text(t, "for") || P.is_text(t, "async")

# `async` is a statement prefix of `def`, `for` and `with` only; the word it prefixes is what the statement dispatches on.
def async_word(+t: S.Tok) -> P.M(S.Tok):
  S.choose(P.M(S.Tok), Bool.not(P.is_text(t, "async")), u => P.M.pure(S.Tok, t), u =>
    do P.M<S.Tok>:
      +w : S.Tok <- P.peek
      S.choose(P.M(S.Tok), P.is_text(w, "def") || P.is_text(w, "for") || P.is_text(w, "with"), u => P.take, u => P.syntax(S.Tok, "expected def, for or with after async")))

def ident_token(+t: S.Tok) -> P.M(S.Tok):
  S.choose(P.M(S.Tok), non_ascii(P.tok_text(t)), u => P.unsupported(S.Tok, "Unicode identifier normalization"), u => P.M.pure(S.Tok, t))

def ident() -> P.M(S.Tok):
  do P.M<S.Tok>:
    t : S.Tok <- P.expect("NAME")
    ident_token(t)

def wrap(+e: S.Expr) -> S.Expr:
  N.block(N.one(e), N.get_finish(e))

def literal_kind(+raw: String) -> S.Json:
  S.choose(S.Json, String.starts_with(raw, "u'" ) || String.starts_with(raw, "u\""), u => S.JStr{"u"}, u => S.JNull{})

def fstring(+raw: String) -> Bool:
  +s = String.to_lower(String.take(raw, 2n))
  String.starts_with(s, "f") || String.eq(s, "rf")

def bytes_literal(raw: String) -> Bool:
  +prefix = String.to_lower(String.take(String.trim_start(raw), 2n))
  String.starts_with(prefix, "b") || String.eq(prefix, "rb")

# A run of adjacent STRING tokens: does it hold an f-string, and where does it end.
def run_f(ts: List<&2, S.Tok>) -> Bool:
  match ts:
    case Nil{}:
      False{}
    case Con{+t, rest}:
      S.choose(Bool, P.is_kind(t, "STRING"), u => S.choose(Bool, fstring(P.tok_text(t)), u => True{}, u => run_f(rest)), u => False{})

def run_end(ts: List<&2, S.Tok>, +end: S.Pos) -> S.Pos:
  match ts:
    case Nil{}:
      end
    case Con{+t, rest}:
      S.choose(S.Pos, P.is_kind(t, "STRING"), u => run_end(rest, P.tok_end(t)), u => end)

def empty_text(+o: F.Open) -> Bool:
  F.Open{raw, +body, offset} = o
  S.choose(Bool, raw, u => String.is_empty(body), u => F.vanishes(body))

def conversion(+t: F.Tail) -> S.Json:
  +c = F.conversion(t)
  S.choose(S.Json, Bool.not(Nat.is_eq(c, 0n)), u => S.JNum{c}, u =>
    S.choose(S.Json, String.is_empty(F.debug(t)) || F.has_spec(t), u => S.JNeg{1n}, u => S.JNum{114n}))

def syntax_result(r: P.Reply<S.Expr>) -> Result<&2, &2, S.Error, S.Module>:
  match r:
    case P.Reply{body, P.State{Nil{}, last, fuel}}:
      Done{S.Module{N.get_body(body)}}
    case P.Reply{body, P.State{Con{t, rest}, last, fuel}}:
      Fail{S.PErr{S.Syntax{}, P.tok_start(t), "tokens after EOF"}}

# K bounds dispatches, including no-consumption transitions, per token.
# P2 deterministic grammar fuzz records the observed global high-water mark.
def fuel_k() -> Nat:
  32n

def budget(ts: List<&2, S.Tok>) -> Nat:
  fuel_k() * (S.fuel_weight(ts, 0n) + 1n)

def go(+fuel: Nat, +mode: Mode) -> P.M(S.Expr):
  match fuel mode:
    case 0n _:
      P.error(S.Expr, S.Limit{}, "parser recursion fuel")
    case 1n+left Expression{minimum}:
      P.meter(S.Expr, do P.M<S.Expr>:
        first : S.Expr <- go(left, Prefix{minimum})
        go(left, Rest{minimum, first}))
    case 1n+left Prefix{minimum}:
      P.meter(S.Expr, do P.M<S.Expr>:
        +t : S.Tok <- P.peek
        S.choose(P.M(S.Expr), P.is_kind(t, "NAME"), u => expression_name(t), u =>
          S.choose(P.M(S.Expr), P.is_kind(t, "NUMBER") || P.is_text(t, "True") || P.is_text(t, "False") || P.is_text(t, "None") || P.is_text(t, "..."), u =>
            do P.M<S.Expr>:
              drop : S.Tok <- P.take
              return N.atom_constant(t), u =>
            S.choose(P.M(S.Expr), P.is_kind(t, "STRING"), u =>
              do P.M<S.Expr>:
                +ts : List<&2, S.Tok> <- P.tokens
                S.choose(P.M(S.Expr), run_f(ts), u =>
                  go(left, Joined{literal_kind(P.tok_text(t)), P.tok_start(t), run_end(ts, P.tok_start(t)), S.JEnd{}, S.JEnd{}}), u =>
                  go(left, Strings{"", literal_kind(P.tok_text(t)), P.tok_start(t), P.tok_end(t)})), u =>
              S.choose(P.M(S.Expr), ((P.is_text(t, "+") || P.is_text(t, "-") || P.is_text(t, "~")) && Nat.is_le(minimum, 13n)) || (P.is_text(t, "not") && Nat.is_le(minimum, 4n)), u =>
                do P.M<S.Expr>:
                  drop : S.Tok <- P.take
                  operand : S.Expr <- go(left, Expression{Bool.pick(Nat, P.is_text(t, "not"), 4n, 12n)})
                  return N.unary(O.unary(P.tok_text(t)), P.tok_start(t), operand), u =>
                # `await_primary`: AWAIT primary. Minimum 14 is a primary: no operator, unary, `not`, lambda or second await.
                S.choose(P.M(S.Expr), P.is_text(t, "await") && Nat.is_le(minimum, 13n), u =>
                  do P.M<S.Expr>:
                    drop : S.Tok <- P.take
                    +operand : S.Expr <- go(left, Expression{14n})
                    return N.statement("Await", S.expr(operand), P.tok_start(t), N.get_finish(operand)), u =>
                S.choose(P.M(S.Expr), P.is_text(t, "("), u =>
                  do P.M<S.Expr>:
                    drop : S.Tok <- P.take
                    +next : S.Tok <- P.peek
                    S.choose(P.M(S.Expr), P.is_text(next, ")"), u =>
                      do P.M<S.Expr>:
                        +end : S.Tok <- P.take
                        return N.group(N.collection("Tuple", S.JEnd{}, P.tok_start(t), P.tok_end(end)), P.tok_start(t), P.tok_end(end)), u =>
                      do P.M<S.Expr>:
                        +inner : S.Expr <- go(left, Star{})
                        +word : S.Tok <- P.peek
                        S.choose(P.M(S.Expr), String.eq(N.get_tag(inner), "Starred"), u => P.syntax(S.Expr, "starred expression requires tuple comma"), u =>
                          S.choose(P.M(S.Expr), comp_start(word) && Bool.not(String.starts_with(N.get_tag(inner), "Yield") && Bool.not(N.is_grouped(inner))), u =>
                            S.choose(P.M(S.Expr), String.eq(N.get_tag(inner), "Tuple") && Bool.not(N.is_grouped(inner)), u => P.syntax(S.Expr, "unparenthesized comprehension element"), u =>
                              go(left, Comp{"GeneratorExp", S.JField{"elt", S.expr(inner), S.JEnd{}}, P.tok_start(t), ")", S.JEnd{}})), u =>
                            do P.M<S.Expr>:
                              end : S.Tok <- P.expect(")")
                              return N.group(inner, P.tok_start(t), P.tok_end(end))))), u =>
                  S.choose(P.M(S.Expr), P.is_text(t, "["), u =>
                    do P.M<S.Expr>:
                      drop : S.Tok <- P.take
                      go(left, Sequence{"List", P.tok_start(t), "]", S.JEnd{}, False{}}), u =>
                    S.choose(P.M(S.Expr), P.is_text(t, "lambda") && Nat.is_le(minimum, 1n), u =>
                      do P.M<S.Expr>:
                        drop : S.Tok <- P.take
                        go(left, Lambda{P.tok_start(t)}), u =>
                    S.choose(P.M(S.Expr), P.is_text(t, "{"), u =>
                      do P.M<S.Expr>:
                        drop : S.Tok <- P.take
                        +next : S.Tok <- P.peek
                        S.choose(P.M(S.Expr), P.is_text(next, "}") || P.is_text(next, "**"), u =>
                          go(left, Dictionary{P.tok_start(t), S.JEnd{}, S.JEnd{}, False{}}), u =>
                          do P.M<S.Expr>:
                            +key : S.Expr <- go(left, Item{0n})
                            next : S.Tok <- P.peek
                            S.choose(P.M(S.Expr), P.is_text(next, ":"), u =>
                              do P.M<S.Expr>:
                                drop : S.Tok <- P.take
                                S.choose(P.M(S.Expr), String.eq(N.get_tag(key), "Starred"), u => P.syntax(S.Expr, "starred dictionary key"), u =>
                                  do P.M<S.Expr>:
                                    value : S.Expr <- go(left, Expression{0n})
                                    go(left, Dictionary{P.tok_start(t), N.one(key), N.one(value), True{}})), u =>
                              go(left, Sequence{"Set", P.tok_start(t), "}", N.one(key), True{}}))), u =>
                      expected(S.Expr, t, "expected expression")))))))))))
    case 1n+left Strings{raw, kind, start, end}:
      P.meter(S.Expr, do P.M<S.Expr>:
        +t : S.Tok <- P.peek
        S.choose(P.M(S.Expr), P.is_kind(t, "STRING"), u =>
          S.choose(P.M(S.Expr), Bool.not(String.is_empty(raw)) && Bool.xor(bytes_literal(raw), bytes_literal(P.tok_text(t))), u =>
            P.syntax(S.Expr, "cannot mix bytes and nonbytes literals"), u =>
            do P.M<S.Expr>:
              drop : S.Tok <- P.take
              go(left, Strings{raw ++ " " ++ P.tok_text(t), kind, start, P.tok_end(t)})), u =>
          P.M.pure(S.Expr, N.constant(raw, kind, start, end))))
    case 1n+left Joined{+kind, +start, +end, +values, +parts}:
      P.meter(S.Expr, do P.M<S.Expr>:
        +t : S.Tok <- P.peek
        S.choose(P.M(S.Expr), Bool.not(P.is_kind(t, "STRING")), u => P.M.pure(S.Expr, N.joined(N.flush(values, parts, kind, start, end), start, end)), u =>
          S.choose(P.M(S.Expr), bytes_literal(P.tok_text(t)), u => P.syntax(S.Expr, "cannot mix bytes and nonbytes literals"), u =>
            do P.M<S.Expr>:
              drop : S.Tok <- P.take
              +o : F.Open <- P.M.pure(F.Open, F.open(P.tok_text(t)))
              S.choose(P.M(S.Expr), fstring(P.tok_text(t)), u =>
                do P.M<S.Expr>:
                  +st : S.Expr <- go(left, FString{F.Ctx{F.is_raw(o), kind, start, end, P.tok_start(t), P.tok_end(t)}, 0n, F.body(o), F.shift(P.tok_start(t), F.offset(o)), values, parts})
                  go(left, Joined{kind, start, end, N.get(N.get_fields(st), "values"), N.get(N.get_fields(st), "parts")}), u =>
                go(left, Joined{kind, start, end, values, S.choose(S.Json, empty_text(o), u => parts, u => S.JItem{N.part("s", P.tok_text(t)), parts})})))))
    # CPython 3.11: a spec's closing text Constant takes its own token's span and no kind; all else the run's.
    case 1n+left FString{ctx, +level, rest, pos, +values, parts}:
      F.Ctx{+raw, +kind, +lo, +hi, +tlo, +thi} = ctx
      P.meter(S.Expr, do P.M<S.Expr>:
        +lit : F.Cut <- P.lift(F.Cut, F.literal(rest, raw, level, 0n, pos, ""))
        +parts : S.Json <- P.M.pure(S.Json, S.choose(S.Json, empty_text(F.Open{raw, F.text_of(lit), 0n}), u => parts, u =>
          S.JItem{N.part(Bool.pick(String, raw, "v", "f"), F.text_of(lit)), parts}))
        S.choose(P.M(S.Expr), Bool.not(Char.is_eq(C.head(F.rest_of(lit)), '{')), u => P.M.pure(S.Expr, N.fstate(values, parts, F.rest_of(lit), F.pos_of(lit))), u =>
          S.choose(P.M(S.Expr), Nat.is_le(2n, level), u => P.lift(S.Expr, F.fail(S.Expr, F.pos_of(lit), "f-string: expressions nested too deeply")), u =>
            do P.M<S.Expr>:
              +e : F.Cut <- P.lift(F.Cut, F.field(String.drop(F.rest_of(lit), 1n), F.shift(F.pos_of(lit), 1n)))
              +sub : List<&2, S.Tok> <- P.lift(List<&2, S.Tok>, L.lex_at("(" ++ F.text_of(e) ++ ")", F.pos_of(lit)))
              +value : S.Expr <- P.within(S.Expr, sub, budget(sub), do P.M<S.Expr>:
                inner : S.Expr <- go(left, Expression{0n})
                drop : S.Tok <- P.expect("NEWLINE")
                return inner)
              +tl : F.Tail <- P.lift(F.Tail, F.tail(F.rest_of(e), F.pos_of(e)))
              +cut : F.Cut <- P.M.pure(F.Cut, F.tail_cut(tl))
              +spec : S.Expr <- S.choose(P.M(S.Expr), F.has_spec(tl), u =>
                go(left, FString{F.Ctx{raw, kind, lo, hi, tlo, thi}, 1n+level, F.rest_of(cut), F.pos_of(cut), S.JEnd{}, S.JEnd{}}), u =>
                P.M.pure(S.Expr, N.fstate(S.JEnd{}, S.JEnd{}, F.rest_of(cut), F.pos_of(cut))))
              +fs : S.Json <- P.M.pure(S.Json, N.get_fields(spec))
              +after : String <- P.M.pure(String, N.string(N.get(fs, "rest")))
              S.choose(P.M(S.Expr), Bool.not(Char.is_eq(C.head(after), '}')), u => P.lift(S.Expr, F.fail(S.Expr, N.get_begin(spec), "f-string: expecting '}'")), u =>
                go(left, FString{F.Ctx{raw, kind, lo, hi, tlo, thi}, level, String.drop(after, 1n), F.shift(N.get_begin(spec), 1n),
                  S.JItem{S.expr(N.formatted(value, conversion(tl),
                    S.choose(S.Json, F.has_spec(tl), u => S.expr(N.joined(N.flush(N.get(fs, "values"), N.get(fs, "parts"), S.JNull{}, tlo, thi), tlo, thi)), u => S.JNull{}), lo, hi)),
                    N.flush(values, S.choose(S.Json, String.is_empty(F.debug(tl)), u => parts, u => S.JItem{N.part("v", F.text_of(e) ++ F.debug(tl)), parts}), kind, lo, hi)},
                  S.JEnd{}})))))
    case 1n+left Item{+minimum}:
      P.meter(S.Expr, do P.M<S.Expr>:
        +t : S.Tok <- P.peek
        S.choose(P.M(S.Expr), P.is_text(t, "*"), u =>
          do P.M<S.Expr>:
            drop : S.Tok <- P.take
            value : S.Expr <- go(left, Expression{6n})
            return N.starred(P.tok_start(t), value), u => go(left, Expression{minimum})))
    case 1n+left TestList{+minimum}:
      P.meter(S.Expr, do P.M<S.Expr>:
        +first : S.Expr <- go(left, Item{minimum})
        +t : S.Tok <- P.peek
        S.choose(P.M(S.Expr), P.is_text(t, ","), u =>
          do P.M<S.Expr>:
            drop : S.Tok <- P.take
            go(left, Comma{minimum, N.one(first), N.get_begin(first), P.tok_end(t)}), u =>
          P.M.pure(S.Expr, first)))
    case 1n+left Comma{+minimum, items, start, end}:
      P.meter(S.Expr, do P.M<S.Expr>:
        t : S.Tok <- P.peek
        S.choose(P.M(S.Expr), O.is_end(t), u => P.M.pure(S.Expr, N.collection("Tuple", items, start, end)), u =>
          do P.M<S.Expr>:
            +value : S.Expr <- go(left, Item{minimum})
            +next : S.Tok <- P.peek
            S.choose(P.M(S.Expr), P.is_text(next, ","), u =>
              do P.M<S.Expr>:
                drop : S.Tok <- P.take
                go(left, Comma{minimum, S.JItem{S.expr(value), items}, start, P.tok_end(next)}), u =>
              P.M.pure(S.Expr, N.collection("Tuple", S.JItem{S.expr(value), items}, start, N.get_finish(value))))))
    case 1n+left Sequence{kind, start, close, +items, +separator}:
      P.meter(S.Expr, do P.M<S.Expr>:
        +t : S.Tok <- P.peek
        S.choose(P.M(S.Expr), P.is_text(t, close), u =>
          do P.M<S.Expr>:
            end : S.Tok <- P.take
            return N.collection(kind, items, start, P.tok_end(end)), u =>
          S.choose(P.M(S.Expr), comp_start(t), u =>
            S.choose(P.M(S.Expr), separator && N.sole(items), u =>
              go(left, Comp{kind ++ "Comp", S.JField{"elt", N.head(items), S.JEnd{}}, start, close, S.JEnd{}}), u => P.syntax(S.Expr, "comprehension takes one unstarred element")), u =>
          S.choose(P.M(S.Expr), O.unsupported(t), u => P.unsupported(S.Expr, "expression"), u =>
            S.choose(P.M(S.Expr), separator, u =>
              do P.M<S.Expr>:
                drop : S.Tok <- P.expect(",")
                go(left, Sequence{kind, start, close, items, False{}}), u =>
              do P.M<S.Expr>:
                value : S.Expr <- go(left, Item{0n})
                go(left, Sequence{kind, start, close, S.JItem{S.expr(value), items}, True{}}))))))
    case 1n+left Dictionary{start, +keys, values, +separator}:
      P.meter(S.Expr, do P.M<S.Expr>:
        +t : S.Tok <- P.peek
        S.choose(P.M(S.Expr), P.is_text(t, "}"), u =>
          do P.M<S.Expr>:
            end : S.Tok <- P.take
            return N.dict(keys, values, start, P.tok_end(end)), u =>
          S.choose(P.M(S.Expr), comp_start(t), u =>
            S.choose(P.M(S.Expr), separator && N.sole(keys), u =>
              go(left, Comp{"DictComp", S.JField{"key", N.head(keys), S.JField{"value", N.head(values), S.JEnd{}}}, start, "}", S.JEnd{}}), u => P.syntax(S.Expr, "dict comprehension takes one key: value")), u =>
          S.choose(P.M(S.Expr), O.unsupported(t), u => P.unsupported(S.Expr, "dictionary item"), u =>
            S.choose(P.M(S.Expr), separator, u =>
              do P.M<S.Expr>:
                drop : S.Tok <- P.expect(",")
                go(left, Dictionary{start, keys, values, False{}}), u =>
              S.choose(P.M(S.Expr), P.is_text(t, "**"), u =>
                do P.M<S.Expr>:
                  drop : S.Tok <- P.take
                  value : S.Expr <- go(left, Expression{6n})
                  go(left, Dictionary{start, S.JItem{S.JNull{}, keys}, S.JItem{S.expr(value), values}, True{}}), u =>
                do P.M<S.Expr>:
                  key : S.Expr <- go(left, Expression{0n})
                  colon : S.Tok <- P.expect(":")
                  value : S.Expr <- go(left, Expression{0n})
                  go(left, Dictionary{start, S.JItem{S.expr(key), keys}, S.JItem{S.expr(value), values}, True{}})))))))
    case 1n+left Rest{minimum, first}:
      P.meter(S.Expr, do P.M<S.Expr>:
        +t : S.Tok <- P.peek
        +level : Nat = O.precedence(P.tok_text(t))
        S.choose(P.M(S.Expr), P.is_text(t, "."), u =>
          do P.M<S.Expr>:
            drop : S.Tok <- P.take
            +id : S.Tok <- P.expect("NAME")
            S.choose(P.M(S.Expr), non_ascii(P.tok_text(id)), u => P.unsupported(S.Expr, "Unicode attribute normalization"), u =>
              go(left, Rest{minimum, N.attr(first, id)})), u =>
          S.choose(P.M(S.Expr), P.is_text(t, "("), u =>
            do P.M<S.Expr>:
              drop : S.Tok <- P.take
              call : S.Expr <- go(left, Arguments{first, P.tok_start(t), S.JEnd{}, S.JEnd{}, False{}, False{}})
              go(left, Rest{minimum, call}), u =>
            S.choose(P.M(S.Expr), P.is_text(t, "["), u =>
              do P.M<S.Expr>:
                drop : S.Tok <- P.take
                +index : S.Expr <- go(left, Slice{})
                +next : S.Tok <- P.peek
                slices : S.Expr <- S.choose(P.M(S.Expr), P.is_text(next, ","), u =>
                  do P.M<S.Expr>:
                    drop : S.Tok <- P.take
                    go(left, Slices{N.one(index), N.get_begin(index), P.tok_end(next)}), u =>
                  P.M.pure(S.Expr, N.index(index)))
                end : S.Tok <- P.expect("]")
                go(left, Rest{minimum, N.subscript(first, slices, P.tok_end(end))}), u =>
              S.choose(P.M(S.Expr), Nat.is_eq(level, 0n) || Nat.is_lt(level, minimum), u => P.M.pure(S.Expr, first), u =>
                S.choose(P.M(S.Expr), Nat.is_eq(level, 1n), u =>
                  do P.M<S.Expr>:
                    drop : S.Tok <- P.take
                    test : S.Expr <- go(left, Expression{2n})
                    drop : S.Tok <- P.expect("else")
                    other : S.Expr <- go(left, Expression{1n})
                    go(left, Rest{minimum, N.conditional(first, test, other)}), u =>
                  S.choose(P.M(S.Expr), Nat.is_eq(level, 5n), u =>
                    go(left, Comparison{minimum, first, S.JEnd{}, S.JEnd{}, N.get_begin(first), N.get_finish(first)}), u =>
                    S.choose(P.M(S.Expr), Nat.is_le(level, 3n), u =>
                      go(left, Boolean{minimum, level, P.tok_text(t), N.one(first), N.get_begin(first), N.get_finish(first)}), u =>
                      do P.M<S.Expr>:
                        drop : S.Tok <- P.take
                        second : S.Expr <- go(left, Expression{Bool.pick(Nat, Nat.is_eq(level, 13n), 12n, 1n+level)})
                        go(left, Rest{minimum, N.binary(first, O.tag(P.tok_text(t)), second)})))))))))
    # One subscript element: `[lower] ':' [upper] [':' [step]]`, else an ordinary (starred) expression.
    case 1n+left Slice{}:
      P.meter(S.Expr, do P.M<S.Expr>:
        +t : S.Tok <- P.peek
        +lower : S.Expr <- S.choose(P.M(S.Expr), P.is_text(t, ":"), u => P.M.pure(S.Expr, N.none()), u => go(left, Item{0n}))
        colon : S.Tok <- P.peek
        S.choose(P.M(S.Expr), Bool.not(P.is_text(colon, ":")), u => P.M.pure(S.Expr, lower), u =>
          S.choose(P.M(S.Expr), String.eq(N.get_tag(lower), "Starred"), u => P.syntax(S.Expr, "starred slice bound"), u =>
            do P.M<S.Expr>:
              drop : S.Tok <- P.take
              upper : S.Expr <- go(left, Bound{})
              second : S.Tok <- P.peek
              step : S.Expr <- S.choose(P.M(S.Expr), P.is_text(second, ":"), u =>
                do P.M<S.Expr>:
                  drop : S.Tok <- P.take
                  go(left, Bound{}), u => P.M.pure(S.Expr, N.none()))
              end : S.Pos <- P.end
              return N.slice(lower, upper, step, S.choose(S.Pos, N.is_none(lower), u => P.tok_start(t), u => N.get_begin(lower)), end))))
    case 1n+left Bound{}:
      P.meter(S.Expr, do P.M<S.Expr>:
        +t : S.Tok <- P.peek
        S.choose(P.M(S.Expr), P.is_text(t, ":") || P.is_text(t, ",") || P.is_text(t, "]"), u => P.M.pure(S.Expr, N.none()), u => go(left, Expression{0n})))
    # Comma with slice elements; a subscript tuple always closes on `]`.
    case 1n+left Slices{items, start, end}:
      P.meter(S.Expr, do P.M<S.Expr>:
        t : S.Tok <- P.peek
        S.choose(P.M(S.Expr), P.is_text(t, "]"), u => P.M.pure(S.Expr, N.collection("Tuple", items, start, end)), u =>
          do P.M<S.Expr>:
            +value : S.Expr <- go(left, Slice{})
            +next : S.Tok <- P.peek
            S.choose(P.M(S.Expr), P.is_text(next, ","), u =>
              do P.M<S.Expr>:
                drop : S.Tok <- P.take
                go(left, Slices{S.JItem{S.expr(value), items}, start, P.tok_end(next)}), u =>
              P.M.pure(S.Expr, N.collection("Tuple", S.JItem{S.expr(value), items}, start, N.get_finish(value))))))
    # `for` clauses after the head, then the close. A clause's iter and `if`s are disjunctions: no bare ternary or lambda.
    case 1n+left Comp{kind, head, start, close, gens}:
      P.meter(S.Expr, do P.M<S.Expr>:
        +t : S.Tok <- P.peek
        S.choose(P.M(S.Expr), comp_start(t), u =>
          do P.M<S.Expr>:
            drop : S.Tok <- P.take
            word : S.Tok <- S.choose(P.M(S.Tok), P.is_text(t, "async"), u => P.expect("for"), u => P.M.pure(S.Tok, t))
            first : S.Expr <- go(left, TestList{6n})
            target : S.Json <- P.lift(S.Json, N.target(first, False{}))
            word : S.Tok <- P.expect("in")
            iter : S.Expr <- go(left, Expression{2n})
            ifs : S.Expr <- go(left, Ifs{S.JEnd{}})
            go(left, Comp{kind, head, start, close, S.JItem{N.clause(target, iter, N.carried(ifs), P.is_text(t, "async")), gens}}), u =>
          do P.M<S.Expr>:
            end : S.Tok <- P.expect(close)
            return N.comp(kind, head, gens, start, P.tok_end(end))))
    case 1n+left Ifs{items}:
      P.meter(S.Expr, do P.M<S.Expr>:
        t : S.Tok <- P.peek
        S.choose(P.M(S.Expr), P.is_text(t, "if"), u =>
          do P.M<S.Expr>:
            drop : S.Tok <- P.take
            test : S.Expr <- go(left, Expression{2n})
            go(left, Ifs{S.JItem{S.expr(test), items}}), u =>
          P.M.pure(S.Expr, N.carry(N.arr(items)))))
    # `yield_expr | star_expressions`: a statement's head, an assignment's value, what a group holds. `yield from` takes one expression.
    case 1n+left Star{}:
      P.meter(S.Expr, do P.M<S.Expr>:
        +t : S.Tok <- P.peek
        S.choose(P.M(S.Expr), Bool.not(P.is_text(t, "yield")), u => go(left, TestList{0n}), u =>
          do P.M<S.Expr>:
            drop : S.Tok <- P.take
            +next : S.Tok <- P.peek
            S.choose(P.M(S.Expr), O.is_end(next), u => P.M.pure(S.Expr, N.statement("Yield", S.JNull{}, P.tok_start(t), P.tok_end(t))), u =>
              do P.M<S.Expr>:
                value : S.Expr <- S.choose(P.M(S.Expr), P.is_text(next, "from"), u =>
                  do P.M<S.Expr>:
                    drop : S.Tok <- P.take
                    go(left, Expression{0n}), u => go(left, TestList{0n}))
                end : S.Pos <- P.end
                return N.statement(Bool.pick(String, P.is_text(next, "from"), "YieldFrom", "Yield"), S.expr(value), P.tok_start(t), end))))
    case 1n+left Boolean{minimum, level, operator, values, start, end}:
      P.meter(S.Expr, do P.M<S.Expr>:
        t : S.Tok <- P.peek
        S.choose(P.M(S.Expr), P.is_text(t, operator), u =>
          do P.M<S.Expr>:
            drop : S.Tok <- P.take
            +value : S.Expr <- go(left, Expression{1n+level})
            go(left, Boolean{minimum, level, operator, S.JItem{S.expr(value), values}, start, N.get_finish(value)}), u =>
          go(left, Rest{minimum, N.boolean(O.tag(operator), values, start, end)})))
    case 1n+left Comparison{minimum, first, ops, values, start, end}:
      P.meter(S.Expr, do P.M<S.Expr>:
        t : S.Tok <- P.peek
        S.choose(P.M(S.Expr), Nat.is_eq(O.precedence(P.tok_text(t)), 5n), u =>
          do P.M<S.Expr>:
            operator : String <- O.comparison()
            +value : S.Expr <- go(left, Expression{6n})
            go(left, Comparison{minimum, first, S.JItem{N.op(operator), ops}, S.JItem{S.expr(value), values}, start, N.get_finish(value)}), u =>
          go(left, Rest{minimum, N.compare(first, ops, values, start, end)})))
    case 1n+left Arguments{+fn, open, +args, +keywords, seen_kw, +separator}:
      P.meter(S.Expr, do P.M<S.Expr>:
        +t : S.Tok <- P.peek
        S.choose(P.M(S.Expr), P.is_text(t, ")"), u =>
          do P.M<S.Expr>:
            end : S.Tok <- P.take
            return N.call(fn, args, keywords, P.tok_end(end)), u =>
          # A bare generator is a call's only argument; a class takes none.
          S.choose(P.M(S.Expr), comp_start(t), u =>
            S.choose(P.M(S.Expr), separator && N.sole(args) && N.empty(keywords) && Bool.not(String.eq(N.get_tag(fn), "$json")), u =>
              do P.M<S.Expr>:
                +gen : S.Expr <- go(left, Comp{"GeneratorExp", S.JField{"elt", N.head(args), S.JEnd{}}, open, ")", S.JEnd{}})
                return N.call(fn, N.one(gen), S.JEnd{}, N.get_finish(gen)), u => P.syntax(S.Expr, "generator expression must be parenthesized")), u =>
          S.choose(P.M(S.Expr), O.unsupported(t), u => P.unsupported(S.Expr, "argument"), u =>
            S.choose(P.M(S.Expr), separator, u =>
              do P.M<S.Expr>:
                drop : S.Tok <- P.expect(",")
                go(left, Arguments{fn, open, args, keywords, seen_kw, False{}}), u =>
              do P.M<S.Expr>:
                +next : S.Tok <- P.second
                S.choose(P.M(S.Expr), P.is_text(t, "**"), u =>
                  do P.M<S.Expr>:
                    drop : S.Tok <- P.take
                    value : S.Expr <- go(left, Expression{0n})
                    go(left, Arguments{fn, open, args, S.JItem{N.kw(S.JNull{}, value, P.tok_start(t)), keywords}, True{}, True{}}), u =>
                  S.choose(P.M(S.Expr), P.is_kind(t, "NAME") && P.is_text(next, "="), u =>
                    S.choose(P.M(S.Expr), non_ascii(P.tok_text(t)), u => P.unsupported(S.Expr, "Unicode keyword normalization"), u =>
                      do P.M<S.Expr>:
                        drop : S.Tok <- P.take
                        drop : S.Tok <- P.take
                        value : S.Expr <- go(left, Expression{0n})
                        go(left, Arguments{fn, open, args, S.JItem{N.kw(S.JStr{P.tok_text(t)}, value, P.tok_start(t)), keywords}, True{}, True{}})), u =>
                    S.choose(P.M(S.Expr), seen_kw && Bool.not(P.is_text(t, "*")), u => P.syntax(S.Expr, "positional argument follows keyword"), u =>
                      S.choose(P.M(S.Expr), P.is_text(t, "*"), u =>
                        S.choose(P.M(S.Expr), N.has_unpack(keywords), u => P.syntax(S.Expr, "iterable unpack follows keyword unpack"), u =>
                          do P.M<S.Expr>:
                            drop : S.Tok <- P.take
                            value : S.Expr <- go(left, Expression{0n})
                            go(left, Arguments{fn, open, S.JItem{S.expr(N.starred(P.tok_start(t), value)), args}, keywords, seen_kw, True{}})), u =>
                        do P.M<S.Expr>:
                          value : S.Expr <- go(left, Expression{0n})
                          go(left, Arguments{fn, open, S.JItem{S.expr(value), args}, keywords, seen_kw, True{}}))))))))))
    case 1n+left Block{top, statements, end}:
      P.meter(S.Expr, do P.M<S.Expr>:
        +t : S.Tok <- P.peek
        S.choose(P.M(S.Expr), P.is_kind(t, "ENDMARKER"), u =>
          S.choose(P.M(S.Expr), top, u =>
            do P.M<S.Expr>:
              drop : S.Tok <- P.take
              return N.block(statements, end), u => P.syntax(S.Expr, "expected dedent")), u =>
          S.choose(P.M(S.Expr), P.is_kind(t, "DEDENT"), u =>
            S.choose(P.M(S.Expr), top, u => P.syntax(S.Expr, "unexpected dedent"), u =>
              do P.M<S.Expr>:
                  drop : S.Tok <- P.take
                return N.block(statements, end)), u =>
            S.choose(P.M(S.Expr), P.is_kind(t, "NEWLINE"), u =>
              do P.M<S.Expr>:
                drop : S.Tok <- P.take
                go(left, Block{top, statements, end}), u =>
              do P.M<S.Expr>:
                +line : S.Expr <- go(left, Line{})
                go(left, Block{top, S.fields_append(statements, N.get_body(line)), N.get_finish(line)})))))
    case 1n+left Line{}:
      P.meter(S.Expr, do P.M<S.Expr>:
        +t : S.Tok <- P.peek
        S.choose(P.M(S.Expr), P.is_text(t, "if") || P.is_text(t, "while"), u =>
          do P.M<S.Expr>:
            drop : S.Tok <- P.take
            compound : S.Expr <- go(left, Compound{Bool.pick(String, P.is_text(t, "if"), "If", "While"), P.tok_start(t)})
            return wrap(compound), u =>
          S.choose(P.M(S.Expr), P.is_text(t, "@"), u => go(left, Decorators{S.JEnd{}}), u =>
            S.choose(P.M(S.Expr), P.is_text(t, "def") || P.is_text(t, "class") || P.is_text(t, "for") || P.is_text(t, "try") || P.is_text(t, "with") || P.is_text(t, "async"), u =>
              do P.M<S.Expr>:
                drop : S.Tok <- P.take
                +w : S.Tok <- async_word(t)
                +next : S.Tok <- P.peek
                +start : S.Pos = P.tok_start(t)
                compound : S.Expr <- S.choose(P.M(S.Expr), P.is_text(w, "def"), u => go(left, Def{start, S.JArr{S.JEnd{}}}), u =>
                  S.choose(P.M(S.Expr), P.is_text(w, "class"), u => go(left, Class{start, S.JArr{S.JEnd{}}}), u =>
                  S.choose(P.M(S.Expr), P.is_text(w, "for"), u => go(left, For{start}), u =>
                    S.choose(P.M(S.Expr), P.is_text(w, "try"), u => go(left, Try{start}), u =>
                      # CPython tries the parenthesized item list first; it must end in `):`.
                      # Only the header backtracks: a body inside the choice would reparse 2^depth times.
                      do P.M<S.Expr>:
                        items : S.Expr <- S.choose(P.M(S.Expr), P.is_text(next, "("), u =>
                          P.either(S.Expr, go(left, With{True{}}), go(left, With{False{}})), u =>
                          go(left, With{False{}}))
                        body : S.Expr <- go(left, Suite{})
                        return N.context(N.carried(items), body, start)))))
                return wrap(N.async(compound, P.is_text(t, "async"))), u =>
              go(left, Simple{S.JEnd{}})))))
    case 1n+left Simple{statements}:
      P.meter(S.Expr, do P.M<S.Expr>:
        +small : S.Expr <- go(left, Small{})
        +t : S.Tok <- P.peek
        +body : S.Json = S.fields_append(statements, N.one(small))
        S.choose(P.M(S.Expr), P.is_text(t, ";"), u =>
          do P.M<S.Expr>:
            semi : S.Tok <- P.take
            next : S.Tok <- P.peek
            S.choose(P.M(S.Expr), P.is_kind(next, "NEWLINE"), u =>
              do P.M<S.Expr>:
                drop : S.Tok <- P.take
                # A compound statement ends at its last non-whitespace token: the trailing `;`.
                return N.block(body, P.tok_end(semi)), u => go(left, Simple{body})), u =>
          S.choose(P.M(S.Expr), P.is_kind(t, "NEWLINE"), u =>
            do P.M<S.Expr>:
              drop : S.Tok <- P.take
              return N.block(body, N.get_finish(small)), u => expected(S.Expr, t, "expected statement separator"))))
    case 1n+left Small{}:
      P.meter(S.Expr, do P.M<S.Expr>:
        +t : S.Tok <- P.peek
        S.choose(P.M(S.Expr), P.is_text(t, "pass") || P.is_text(t, "break") || P.is_text(t, "continue"), u =>
          do P.M<S.Expr>:
            drop : S.Tok <- P.take
            return N.node(Bool.pick(String, P.is_text(t, "pass"), "Pass", Bool.pick(String, P.is_text(t, "break"), "Break", "Continue")), S.JEnd{}, P.tok_start(t), P.tok_end(t)), u =>
          S.choose(P.M(S.Expr), P.is_text(t, "return"), u =>
            do P.M<S.Expr>:
              drop : S.Tok <- P.take
              next : S.Tok <- P.peek
              S.choose(P.M(S.Expr), O.is_end(next), u => P.M.pure(S.Expr, N.statement("Return", S.JNull{}, P.tok_start(t), P.tok_end(t))), u =>
                do P.M<S.Expr>:
                  value : S.Expr <- go(left, TestList{0n})
                  end : S.Pos <- P.end
                  return N.statement("Return", S.expr(value), P.tok_start(t), end)), u =>
            S.choose(P.M(S.Expr), O.unsupported(t), u => P.unsupported(S.Expr, "statement " ++ P.tok_text(t)), u =>
              S.choose(P.M(S.Expr), P.is_text(t, "import") || P.is_text(t, "from"), u =>
                do P.M<S.Expr>:
                  drop : S.Tok <- P.take
                  S.choose(P.M(S.Expr), P.is_text(t, "from"), u => go(left, From{P.tok_start(t), 0n}), u =>
                    do P.M<S.Expr>:
                      names : S.Expr <- go(left, Aliases{True{}, False{}, S.JEnd{}, False{}})
                      end : S.Pos <- P.end
                      return N.node("Import", S.JField{"names", N.carried(names), S.JEnd{}}, P.tok_start(t), end)), u =>
              S.choose(P.M(S.Expr), P.is_text(t, "global") || P.is_text(t, "nonlocal"), u =>
                do P.M<S.Expr>:
                  drop : S.Tok <- P.take
                  go(left, Names{Bool.pick(String, P.is_text(t, "global"), "Global", "Nonlocal"), P.tok_start(t), S.JEnd{}}), u =>
                S.choose(P.M(S.Expr), P.is_text(t, "del"), u =>
                  do P.M<S.Expr>:
                    drop : S.Tok <- P.take
                    value : S.Expr <- go(left, TestList{0n})
                    targets : S.Json <- P.lift(S.Json, N.del_targets(value))
                    end : S.Pos <- P.end
                    return N.node("Delete", S.JField{"targets", targets, S.JEnd{}}, P.tok_start(t), end), u =>
                  S.choose(P.M(S.Expr), P.is_text(t, "assert"), u =>
                    do P.M<S.Expr>:
                      drop : S.Tok <- P.take
                      test : S.Expr <- go(left, Expression{0n})
                      msg : S.Expr <- go(left, Optional{",", False{}})
                      end : S.Pos <- P.end
                      return N.node("Assert", S.JField{"test", S.expr(test), S.JField{"msg", N.opt(msg), S.JEnd{}}}, P.tok_start(t), end), u =>
                    S.choose(P.M(S.Expr), P.is_text(t, "raise"), u =>
                      do P.M<S.Expr>:
                        drop : S.Tok <- P.take
                        +next : S.Tok <- P.peek
                        exc : S.Expr <- S.choose(P.M(S.Expr), P.is_text(next, "from"), u => P.syntax(S.Expr, "expected exception before from"), u => S.choose(P.M(S.Expr), O.is_end(next), u => P.M.pure(S.Expr, N.none()), u => go(left, Expression{0n})))
                        cause : S.Expr <- go(left, Optional{"from", False{}})
                        end : S.Pos <- P.end
                        return N.node("Raise", S.JField{"exc", N.opt(exc), S.JField{"cause", N.opt(cause), S.JEnd{}}}, P.tok_start(t), end), u =>
                      do P.M<S.Expr>:
                        first : S.Expr <- go(left, Star{})
                        go(left, AfterSmall{first, P.tok_start(t), P.is_text(t, "match")}))))))))))
    # `target: annotation [= value]`. `match (x):` and `match [x]:` read as a target up to the `:`; only a match header ends the line there.
    case 1n+left AfterSmall{+first, +start, soft}:
      P.meter(S.Expr, do P.M<S.Expr>:
        +t : S.Tok <- P.peek
        S.choose(P.M(S.Expr), P.is_text(t, "="), u =>
          do P.M<S.Expr>:
            target : S.Json <- P.lift(S.Json, N.target(first, False{}))
            drop : S.Tok <- P.take
            go(left, Assignment{S.JItem{target, S.JEnd{}}, start}), u =>
          S.choose(P.M(S.Expr), O.augmented(P.tok_text(t)), u =>
            do P.M<S.Expr>:
              target : S.Json <- P.lift(S.Json, N.target(first, True{}))
              drop : S.Tok <- P.take
              value : S.Expr <- go(left, Star{})
              end : S.Pos <- P.end
              return N.augmented(target, O.tag(String.drop_end(P.tok_text(t), 1n)), value, start, end), u =>
            S.choose(P.M(S.Expr), P.is_text(t, ":"), u =>
              do P.M<S.Expr>:
                drop : S.Tok <- P.take
                next : S.Tok <- P.peek
                S.choose(P.M(S.Expr), soft && P.is_kind(next, "NEWLINE"), u => P.unsupported(S.Expr, "match statement"), u =>
                  do P.M<S.Expr>:
                    target : S.Json <- P.lift(S.Json, N.ann_target(first, start))
                    note : S.Expr <- go(left, Expression{0n})
                    eq : S.Tok <- P.peek
                    value : S.Expr <- S.choose(P.M(S.Expr), P.is_text(eq, "="), u =>
                      do P.M<S.Expr>:
                        drop : S.Tok <- P.take
                        go(left, Star{}), u => P.M.pure(S.Expr, N.none()))
                    end : S.Pos <- P.end
                    return N.annotated(target, note, value, String.eq(N.get_tag(first), "Name") && Bool.not(N.is_grouped(first)), start, end)), u =>
              S.choose(P.M(S.Expr), String.eq(N.get_tag(first), "Name") &&
                String.eq(N.string(N.get(N.get_fields(first), "id")), "match") && Bool.not(O.is_end(t)), u =>
                P.unsupported(S.Expr, "match statement"), u =>
                do P.M<S.Expr>:
                  end : S.Pos <- P.end
                  return N.statement("Expr", S.expr(first), start, end))))))
    case 1n+left Assignment{targets, start}:
      P.meter(S.Expr, do P.M<S.Expr>:
        +value : S.Expr <- go(left, Star{})
        t : S.Tok <- P.peek
        S.choose(P.M(S.Expr), P.is_text(t, "="), u =>
          do P.M<S.Expr>:
            target : S.Json <- P.lift(S.Json, N.target(value, False{}))
            drop : S.Tok <- P.take
            go(left, Assignment{S.JItem{target, targets}, start}), u =>
          do P.M<S.Expr>:
            end : S.Pos <- P.end
            return N.assignment(targets, value, start, end)))
    case 1n+left Compound{kind, start}:
      P.meter(S.Expr, do P.M<S.Expr>:
        +test : S.Expr <- go(left, Expression{0n})
        colon : S.Tok <- P.expect(":")
        +body : S.Expr <- go(left, Suite{})
        +t : S.Tok <- P.peek
        S.choose(P.M(S.Expr), String.eq(kind, "If") && P.is_text(t, "elif"), u =>
          do P.M<S.Expr>:
            drop : S.Tok <- P.take
            +other : S.Expr <- go(left, Compound{"If", P.tok_start(t)})
            return N.compound(kind, test, body, N.block(N.one(other), N.get_finish(other)), start), u =>
          S.choose(P.M(S.Expr), P.is_text(t, "else"), u =>
            do P.M<S.Expr>:
              drop : S.Tok <- P.take
              colon : S.Tok <- P.expect(":")
              other : S.Expr <- go(left, Suite{})
              return N.compound(kind, test, body, other, start), u =>
            P.M.pure(S.Expr, N.compound(kind, test, body, N.block(S.JEnd{}, N.get_finish(body)), start)))))
    case 1n+left Suite{}:
      P.meter(S.Expr, do P.M<S.Expr>:
        +t : S.Tok <- P.peek
        S.choose(P.M(S.Expr), P.is_kind(t, "NEWLINE"), u =>
          do P.M<S.Expr>:
            drop : S.Tok <- P.take
            indent : S.Tok <- P.expect("INDENT")
            go(left, Block{False{}, S.JEnd{}, S.Pos{1n, 0n}}), u => go(left, Simple{S.JEnd{}})))
    case 1n+left Clause{word, end}:
      P.meter(S.Expr, do P.M<S.Expr>:
        t : S.Tok <- P.peek
        S.choose(P.M(S.Expr), P.is_text(t, word), u =>
          do P.M<S.Expr>:
            drop : S.Tok <- P.take
            colon : S.Tok <- P.expect(":")
            go(left, Suite{}), u => P.M.pure(S.Expr, N.block(S.JEnd{}, end))))
    case 1n+left Optional{word, star}:
      P.meter(S.Expr, do P.M<S.Expr>:
        t : S.Tok <- P.peek
        S.choose(P.M(S.Expr), P.is_text(t, word), u =>
          do P.M<S.Expr>:
            drop : S.Tok <- P.take
            go(left, Bool.pick(Mode, star, Item{0n}, Expression{0n})), u => P.M.pure(S.Expr, N.none())))
    case 1n+left Lambda{start}:
      P.meter(S.Expr, do P.M<S.Expr>:
        args : S.Expr <- go(left, Params{":", False{}, N.sig_new(), 0n, False{}})
        colon : S.Tok <- P.expect(":")
        body : S.Expr <- go(left, Expression{0n})
        return N.lambda(start, N.carried(args), body))
    # phase: 0 positional, 1 after `/`, 2 after a bare `*`, 3 keyword-only, 4 after `**`.
    case 1n+left Params{+close, +ann, +sig, +phase, separator}:
      P.meter(S.Expr, do P.M<S.Expr>:
        +t : S.Tok <- P.peek
        S.choose(P.M(S.Expr), P.is_text(t, close), u =>
          S.choose(P.M(S.Expr), Nat.is_eq(phase, 2n), u => P.syntax(S.Expr, "named arguments must follow bare *"), u =>
            P.M.pure(S.Expr, N.carry(N.arguments(sig)))), u =>
          S.choose(P.M(S.Expr), separator, u =>
            do P.M<S.Expr>:
              drop : S.Tok <- P.expect(",")
              go(left, Params{close, ann, sig, phase, False{}}), u =>
            S.choose(P.M(S.Expr), Nat.is_eq(phase, 4n), u => P.syntax(S.Expr, "arguments cannot follow var-keyword argument"), u =>
              S.choose(P.M(S.Expr), P.is_text(t, "/"), u =>
                S.choose(P.M(S.Expr), Nat.is_eq(phase, 0n) && N.sig_has_args(sig), u =>
                  do P.M<S.Expr>:
                    drop : S.Tok <- P.take
                    go(left, Params{close, ann, N.sig_slash(sig), 1n, True{}}), u => P.syntax(S.Expr, "invalid /")), u =>
                S.choose(P.M(S.Expr), P.is_text(t, "*") || P.is_text(t, "**"), u =>
                  S.choose(P.M(S.Expr), Bool.pick(Bool, P.is_text(t, "*"), Nat.is_le(phase, 1n), Bool.not(Nat.is_eq(phase, 2n))), u =>
                    do P.M<S.Expr>:
                      drop : S.Tok <- P.take
                      next : S.Tok <- P.peek
                      S.choose(P.M(S.Expr), P.is_text(t, "*") && Bool.not(P.is_kind(next, "NAME")), u =>
                        go(left, Params{close, ann, sig, 2n, True{}}), u =>
                        do P.M<S.Expr>:
                          id : S.Tok <- ident()
                          note : S.Expr <- S.choose(P.M(S.Expr), ann, u => go(left, Optional{":", P.is_text(t, "*")}), u => P.M.pure(S.Expr, N.none()))
                          end : S.Pos <- P.end
                          +one : S.Json = N.arg(id, note, end)
                          go(left, S.choose(Mode, P.is_text(t, "*"), u =>
                            Params{close, ann, N.sig_vararg(sig, one), 3n, True{}}, u =>
                            Params{close, ann, N.sig_kwarg(sig, one), 4n, True{}}))), u =>
                    P.syntax(S.Expr, "invalid * parameter")), u =>
                  S.choose(P.M(S.Expr), P.is_kind(t, "NAME"), u =>
                    do P.M<S.Expr>:
                      id : S.Tok <- ident()
                      note : S.Expr <- S.choose(P.M(S.Expr), ann, u => go(left, Optional{":", False{}}), u => P.M.pure(S.Expr, N.none()))
                      end : S.Pos <- P.end
                      value : S.Expr <- go(left, Optional{"=", False{}})
                      next : N.Sig <- P.lift(N.Sig, N.sig_add(sig, N.arg(id, note, end), value, Nat.is_ge(phase, 2n), P.tok_start(t)))
                      go(left, Params{close, ann, next, Bool.pick(Nat, Nat.is_eq(phase, 2n), 3n, phase), True{}}), u =>
                    expected(S.Expr, t, "expected parameter"))))))))
    case 1n+left Decorators{items}:
      P.meter(S.Expr, do P.M<S.Expr>:
        +t : S.Tok <- P.peek
        S.choose(P.M(S.Expr), P.is_text(t, "@"), u =>
          do P.M<S.Expr>:
            drop : S.Tok <- P.take
            value : S.Expr <- go(left, Expression{0n})
            line : S.Tok <- P.expect("NEWLINE")
            go(left, Decorators{S.JItem{S.expr(value), items}}), u =>
          S.choose(P.M(S.Expr), P.is_text(t, "def") || P.is_text(t, "class") || P.is_text(t, "async"), u =>
            do P.M<S.Expr>:
              drop : S.Tok <- P.take
              w : S.Tok <- S.choose(P.M(S.Tok), P.is_text(t, "async"), u => P.expect("def"), u => P.M.pure(S.Tok, t))
              function : S.Expr <- S.choose(P.M(S.Expr), P.is_text(t, "class"), u => go(left, Class{P.tok_start(t), N.arr(items)}), u =>
                go(left, Def{P.tok_start(t), N.arr(items)}))
              return wrap(N.async(function, P.is_text(t, "async"))), u => expected(S.Expr, t, "expected def or class after decorator"))))
    case 1n+left Def{start, decorators}:
      P.meter(S.Expr, do P.M<S.Expr>:
        id : S.Tok <- ident()
        open : S.Tok <- P.expect("(")
        args : S.Expr <- go(left, Params{")", True{}, N.sig_new(), 0n, False{}})
        close : S.Tok <- P.expect(")")
        returns : S.Expr <- go(left, Optional{"->", False{}})
        colon : S.Tok <- P.expect(":")
        body : S.Expr <- go(left, Suite{})
        return N.function(id, N.carried(args), body, decorators, returns, start))
    # `class`: the base list is a call's argument list on a placeholder callee.
    case 1n+left Class{+start, decorators}:
      P.meter(S.Expr, do P.M<S.Expr>:
        id : S.Tok <- ident()
        +t : S.Tok <- P.peek
        bases : S.Expr <- S.choose(P.M(S.Expr), P.is_text(t, "("), u =>
          do P.M<S.Expr>:
            drop : S.Tok <- P.take
            go(left, Arguments{N.dotted("", start, start), start, S.JEnd{}, S.JEnd{}, False{}, False{}}), u =>
          P.M.pure(S.Expr, N.call(N.dotted("", start, start), S.JEnd{}, S.JEnd{}, start)))
        colon : S.Tok <- P.expect(":")
        body : S.Expr <- go(left, Suite{})
        return N.class(id, bases, body, decorators, start))
    case 1n+left For{start}:
      P.meter(S.Expr, do P.M<S.Expr>:
        first : S.Expr <- go(left, TestList{6n})
        target : S.Json <- P.lift(S.Json, N.target(first, False{}))
        word : S.Tok <- P.expect("in")
        iter : S.Expr <- go(left, TestList{0n})
        colon : S.Tok <- P.expect(":")
        +body : S.Expr <- go(left, Suite{})
        other : S.Expr <- go(left, Clause{"else", N.get_finish(body)})
        return N.loop(target, iter, body, other, start))
    case 1n+left Try{start}:
      P.meter(S.Expr, do P.M<S.Expr>:
        colon : S.Tok <- P.expect(":")
        +body : S.Expr <- go(left, Suite{})
        go(left, Handlers{start, body, S.JEnd{}, N.get_finish(body)}))
    case 1n+left Handlers{start, body, +handlers, +end}:
      P.meter(S.Expr, do P.M<S.Expr>:
        +t : S.Tok <- P.peek
        S.choose(P.M(S.Expr), P.is_text(t, "except"), u =>
          do P.M<S.Expr>:
            drop : S.Tok <- P.take
            +next : S.Tok <- P.peek
            S.choose(P.M(S.Expr), P.is_text(next, "*"), u => P.unsupported(S.Expr, "except*"), u =>
              do P.M<S.Expr>:
                kind : S.Expr <- S.choose(P.M(S.Expr), P.is_text(next, ":"), u => P.M.pure(S.Expr, N.none()), u => go(left, Expression{0n}))
                +word : S.Tok <- P.peek
                name : S.Json <- S.choose(P.M(S.Json), P.is_text(word, "as") && Bool.not(P.is_text(next, ":")), u =>
                  do P.M<S.Json>:
                    drop : S.Tok <- P.take
                    id : S.Tok <- ident()
                    return S.JStr{P.tok_text(id)}, u => P.M.pure(S.Json, S.JNull{}))
                colon : S.Tok <- P.expect(":")
                +suite : S.Expr <- go(left, Suite{})
                go(left, Handlers{start, body, S.JItem{S.expr(N.handler(kind, name, suite, P.tok_start(t))), handlers}, N.get_finish(suite)})), u =>
          S.choose(P.M(S.Expr), N.empty(handlers) && Bool.not(P.is_text(t, "finally")), u => P.syntax(S.Expr, "expected except or finally"), u =>
            do P.M<S.Expr>:
              +other : S.Expr <- S.choose(P.M(S.Expr), N.empty(handlers), u => P.M.pure(S.Expr, N.block(S.JEnd{}, end)), u => go(left, Clause{"else", end}))
              final : S.Expr <- go(left, Clause{"finally", N.get_finish(other)})
              return N.attempt(body, handlers, other, final, start))))
    case 1n+left With{+paren}:
      P.meter(S.Expr, do P.M<S.Expr>:
        open : S.Tok <- S.choose(P.M(S.Tok), paren, u => P.take, u => P.peek)
        items : S.Expr <- go(left, Items{S.JEnd{}, paren, False{}})
        close : S.Tok <- S.choose(P.M(S.Tok), paren, u => P.expect(")"), u => P.peek)
        colon : S.Tok <- P.expect(":")
        return items)
    case 1n+left Items{+items, +paren, separator}:
      P.meter(S.Expr, do P.M<S.Expr>:
        +t : S.Tok <- P.peek
        S.choose(P.M(S.Expr), separator, u =>
          S.choose(P.M(S.Expr), P.is_text(t, ","), u =>
            do P.M<S.Expr>:
              drop : S.Tok <- P.take
              go(left, Items{items, paren, False{}}), u => P.M.pure(S.Expr, N.carry(N.arr(items)))), u =>
          S.choose(P.M(S.Expr), paren && P.is_text(t, ")") && Bool.not(N.empty(items)), u => P.M.pure(S.Expr, N.carry(N.arr(items))), u =>
            do P.M<S.Expr>:
              value : S.Expr <- go(left, Expression{0n})
              word : S.Tok <- P.peek
              vars : S.Json <- S.choose(P.M(S.Json), P.is_text(word, "as"), u =>
                do P.M<S.Json>:
                  drop : S.Tok <- P.take
                  first : S.Expr <- go(left, Item{6n})
                  P.lift(S.Json, N.target(first, False{})), u => P.M.pure(S.Json, S.JNull{}))
              go(left, Items{S.JItem{N.withitem(value, vars), items}, paren, True{}}))))
    case 1n+left Names{kind, start, names}:
      P.meter(S.Expr, do P.M<S.Expr>:
        id : S.Tok <- ident()
        +all : S.Json = S.JItem{S.JStr{P.tok_text(id)}, names}
        t : S.Tok <- P.peek
        S.choose(P.M(S.Expr), P.is_text(t, ","), u =>
          do P.M<S.Expr>:
            drop : S.Tok <- P.take
            go(left, Names{kind, start, all}), u =>
          do P.M<S.Expr>:
            end : S.Pos <- P.end
            return N.node(kind, S.JField{"names", N.arr(all), S.JEnd{}}, start, end)))
    # `from`: leading dots count the level (`...` is one token); a bare relative import has no module.
    case 1n+left From{+start, +level}:
      P.meter(S.Expr, do P.M<S.Expr>:
        +t : S.Tok <- P.peek
        S.choose(P.M(S.Expr), P.is_text(t, ".") || P.is_text(t, "..."), u =>
          do P.M<S.Expr>:
            drop : S.Tok <- P.take
            go(left, From{start, level + Bool.pick(Nat, P.is_text(t, "."), 1n, 3n)}), u =>
          do P.M<S.Expr>:
            module : S.Json <- S.choose(P.M(S.Json), P.is_text(t, "import") && Bool.not(Nat.is_eq(level, 0n)), u => P.M.pure(S.Json, S.JNull{}), u =>
              do P.M<S.Json>:
                name : S.Expr <- go(left, Dotted{True{}, "", P.tok_start(t)})
                return N.carried(name))
            word : S.Tok <- P.expect("import")
            +next : S.Tok <- P.peek
            names : S.Json <- S.choose(P.M(S.Json), P.is_text(next, "*"), u =>
              do P.M<S.Json>:
                drop : S.Tok <- P.take
                return S.JArr{S.JItem{N.alias(N.dotted("*", P.tok_start(next), P.tok_end(next)), S.JNull{}, P.tok_end(next)), S.JEnd{}}}, u =>
              do P.M<S.Json>:
                open : S.Tok <- S.choose(P.M(S.Tok), P.is_text(next, "("), u => P.take, u => P.peek)
                items : S.Expr <- go(left, Aliases{False{}, P.is_text(next, "("), S.JEnd{}, False{}})
                close : S.Tok <- S.choose(P.M(S.Tok), P.is_text(next, "("), u => P.expect(")"), u => P.peek)
                return N.carried(items))
            end : S.Pos <- P.end
            return N.node("ImportFrom", S.JField{"module", module, S.JField{"names", names, S.JField{"level", S.JNum{level}, S.JEnd{}}}}, start, end)))
    case 1n+left Dotted{+dotted, text, start}:
      P.meter(S.Expr, do P.M<S.Expr>:
        +id : S.Tok <- ident()
        +all : String = text ++ P.tok_text(id)
        t : S.Tok <- P.peek
        S.choose(P.M(S.Expr), dotted && P.is_text(t, "."), u =>
          do P.M<S.Expr>:
            drop : S.Tok <- P.take
            go(left, Dotted{dotted, all ++ ".", start}), u =>
          P.M.pure(S.Expr, N.dotted(all, start, P.tok_end(id)))))
    # A trailing comma needs the parentheses: without them the next name is required.
    case 1n+left Aliases{+dotted, +paren, +names, separator}:
      P.meter(S.Expr, do P.M<S.Expr>:
        +t : S.Tok <- P.peek
        S.choose(P.M(S.Expr), separator, u =>
          S.choose(P.M(S.Expr), P.is_text(t, ","), u =>
            do P.M<S.Expr>:
              drop : S.Tok <- P.take
              go(left, Aliases{dotted, paren, names, False{}}), u => P.M.pure(S.Expr, N.carry(N.arr(names)))), u =>
          S.choose(P.M(S.Expr), paren && P.is_text(t, ")") && Bool.not(N.empty(names)), u => P.M.pure(S.Expr, N.carry(N.arr(names))), u =>
            do P.M<S.Expr>:
              name : S.Expr <- go(left, Dotted{dotted, "", P.tok_start(t)})
              word : S.Tok <- P.peek
              asname : S.Json <- S.choose(P.M(S.Json), P.is_text(word, "as"), u =>
                do P.M<S.Json>:
                  drop : S.Tok <- P.take
                  id : S.Tok <- ident()
                  return S.JStr{P.tok_text(id)}, u => P.M.pure(S.Json, S.JNull{}))
              end : S.Pos <- P.end
              go(left, Aliases{dotted, paren, S.JItem{N.alias(name, asname, end), names}, True{}}))))


def raw_result(+ts: List<&2, S.Tok>) -> Result<&2, &2, S.Error, P.Reply<S.Expr>>:
  +fuel = budget(ts)
  go(fuel, Block{True{}, S.JEnd{}, S.Pos{1n, 0n}}, P.State{ts, S.Pos{1n, 0n}, fuel})


def parse(+ts: List<&2, S.Tok>) -> Result<&2, &2, S.Error, S.Module>:
  do Result<&2, &2, S.Error, S.Module>:
    result : P.Reply<S.Expr> <- raw_result(ts)
    syntax_result(result)

def statistics(count: Nat, +fuel: Nat, r: P.Reply<S.Expr>) -> S.Json:
  P.Reply{body, P.State{ts, end, remaining}} = r
  S.JObj{S.JField{"tokens", S.JNum{count}, S.JField{"budget", S.JNum{fuel},
    S.JField{"used", S.JNum{fuel - remaining}, S.JEnd{}}}}}

def stats(+ts: List<&2, S.Tok>) -> Result<&2, &2, S.Error, S.Json>:
  do Result<&2, &2, S.Error, S.Json>:
    result : P.Reply<S.Expr> <- raw_result(ts)
    return statistics(S.token_count(ts, 0n), budget(ts), result)
