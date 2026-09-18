# Direct recursion with precedence climbing. No explicit continuation frames.
# Each mode entry consumes residual fuel; the first Nat separately proves descent.
import Base
import ./syntax.bend as S
import ./parse_state.bend as P
import ./nodes.bend as N
import ./operators.bend as O

# These are grammar modes, not saved continuations: recursive results return
# through the ordinary Bend call stack.
type Mode is Data:
  Expression{minimum: Nat}
  Prefix{minimum: Nat}
  Rest{minimum: Nat, left: S.Expr}
  Strings{raw: String, kind: S.Json, start: S.Pos, end: S.Pos}
  Item{}
  TestList{}
  Comma{items: S.Json, start: S.Pos, end: S.Pos}
  Sequence{kind: String, start: S.Pos, close: String, items: S.Json, separator: Bool}
  Dictionary{start: S.Pos, keys: S.Json, values: S.Json, separator: Bool}
  Arguments{fn: S.Expr, args: S.Json, keywords: S.Json, seen_kw: Bool, separator: Bool}
  Boolean{minimum: Nat, level: Nat, operator: String, values: S.Json, start: S.Pos, end: S.Pos}
  Comparison{minimum: Nat, left: S.Expr, ops: S.Json, values: S.Json, start: S.Pos, end: S.Pos}
  Block{top: Bool, statements: S.Json, end: S.Pos}
  Line{}
  Simple{statements: S.Json}
  Small{}
  AfterSmall{first: S.Expr, start: S.Pos}
  Assignment{targets: S.Json, start: S.Pos}
  Compound{kind: String, start: S.Pos}
  Suite{}

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


def literal_kind(+raw: String) -> S.Json:
  S.choose(S.Json, String.starts_with(raw, "u'" ) || String.starts_with(raw, "u\""), u => S.JStr{"u"}, u => S.JNull{})

def fstring(+raw: String) -> Bool:
  +s = String.to_lower(String.take(raw, 2n))
  String.starts_with(s, "f") || String.eq(s, "rf")

def bytes_literal(raw: String) -> Bool:
  +prefix = String.to_lower(String.take(String.trim_start(raw), 2n))
  String.starts_with(prefix, "b") || String.eq(prefix, "rb")

def syntax_result(r: P.Reply<S.Expr>) -> Result<&2, &2, S.Error, S.Module>:
  match r:
    case P.Reply{body, P.State{Nil{}, last, fuel}}:
      Done{S.Module{N.get_body(body)}}
    case P.Reply{body, P.State{Con{t, rest}, last, fuel}}:
      Fail{S.PErr{S.Syntax{}, P.tok_start(t), "tokens after EOF"}}

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
              go(left, Strings{"", literal_kind(P.tok_text(t)), P.tok_start(t), P.tok_end(t)}), u =>
              S.choose(P.M(S.Expr), P.is_text(t, "+") || P.is_text(t, "-") || P.is_text(t, "~") || (P.is_text(t, "not") && Nat.is_le(minimum, 4n)), u =>
                do P.M<S.Expr>:
                  drop : S.Tok <- P.take
                  operand : S.Expr <- go(left, Expression{Bool.pick(Nat, P.is_text(t, "not"), 4n, 12n)})
                  return N.unary(O.unary(P.tok_text(t)), P.tok_start(t), operand), u =>
                S.choose(P.M(S.Expr), P.is_text(t, "("), u =>
                  do P.M<S.Expr>:
                    drop : S.Tok <- P.take
                    +next : S.Tok <- P.peek
                    S.choose(P.M(S.Expr), P.is_text(next, ")"), u =>
                      do P.M<S.Expr>:
                        +end : S.Tok <- P.take
                        return N.group(N.collection("Tuple", S.JEnd{}, P.tok_start(t), P.tok_end(end)), P.tok_start(t), P.tok_end(end)), u =>
                      do P.M<S.Expr>:
                        +inner : S.Expr <- go(left, TestList{})
                        S.choose(P.M(S.Expr), String.eq(N.get_tag(inner), "Starred"), u => P.syntax(S.Expr, "starred expression requires tuple comma"), u =>
                          do P.M<S.Expr>:
                            end : S.Tok <- P.expect(")")
                            return N.group(inner, P.tok_start(t), P.tok_end(end)))), u =>
                  S.choose(P.M(S.Expr), P.is_text(t, "["), u =>
                    do P.M<S.Expr>:
                      drop : S.Tok <- P.take
                      go(left, Sequence{"List", P.tok_start(t), "]", S.JEnd{}, False{}}), u =>
                    S.choose(P.M(S.Expr), P.is_text(t, "{"), u =>
                      do P.M<S.Expr>:
                        drop : S.Tok <- P.take
                        +next : S.Tok <- P.peek
                        S.choose(P.M(S.Expr), P.is_text(next, "}") || P.is_text(next, "**"), u =>
                          go(left, Dictionary{P.tok_start(t), S.JEnd{}, S.JEnd{}, False{}}), u =>
                          do P.M<S.Expr>:
                            +key : S.Expr <- go(left, Item{})
                            next : S.Tok <- P.peek
                            S.choose(P.M(S.Expr), P.is_text(next, ":"), u =>
                              do P.M<S.Expr>:
                                drop : S.Tok <- P.take
                                S.choose(P.M(S.Expr), String.eq(N.get_tag(key), "Starred"), u => P.syntax(S.Expr, "starred dictionary key"), u =>
                                  do P.M<S.Expr>:
                                    value : S.Expr <- go(left, Expression{0n})
                                    go(left, Dictionary{P.tok_start(t), N.one(key), N.one(value), True{}})), u =>
                              go(left, Sequence{"Set", P.tok_start(t), "}", N.one(key), True{}}))), u =>
                      expected(S.Expr, t, "expected expression")))))))))
    case 1n+left Strings{raw, kind, start, end}:
      P.meter(S.Expr, do P.M<S.Expr>:
        +t : S.Tok <- P.peek
        S.choose(P.M(S.Expr), P.is_kind(t, "STRING"), u =>
          S.choose(P.M(S.Expr), fstring(P.tok_text(t)), u => P.unsupported(S.Expr, "f-string"), u =>
            S.choose(P.M(S.Expr), Bool.not(String.is_empty(raw)) && Bool.xor(bytes_literal(raw), bytes_literal(P.tok_text(t))), u =>
              P.syntax(S.Expr, "cannot mix bytes and nonbytes literals"), u =>
              do P.M<S.Expr>:
                drop : S.Tok <- P.take
                go(left, Strings{raw ++ " " ++ P.tok_text(t), kind, start, P.tok_end(t)}))), u =>
          P.M.pure(S.Expr, N.constant(raw, kind, start, end))))
    case 1n+left Item{}:
      P.meter(S.Expr, do P.M<S.Expr>:
        +t : S.Tok <- P.peek
        S.choose(P.M(S.Expr), P.is_text(t, "*"), u =>
          do P.M<S.Expr>:
            drop : S.Tok <- P.take
            value : S.Expr <- go(left, Expression{6n})
            return N.starred(P.tok_start(t), value), u => go(left, Expression{0n})))
    case 1n+left TestList{}:
      P.meter(S.Expr, do P.M<S.Expr>:
        +first : S.Expr <- go(left, Item{})
        +t : S.Tok <- P.peek
        S.choose(P.M(S.Expr), P.is_text(t, ","), u =>
          do P.M<S.Expr>:
            drop : S.Tok <- P.take
            go(left, Comma{N.one(first), N.get_begin(first), P.tok_end(t)}), u =>
          P.M.pure(S.Expr, first)))
    case 1n+left Comma{items, start, end}:
      P.meter(S.Expr, do P.M<S.Expr>:
        t : S.Tok <- P.peek
        S.choose(P.M(S.Expr), O.is_end(t), u => P.M.pure(S.Expr, N.collection("Tuple", items, start, end)), u =>
          do P.M<S.Expr>:
            +value : S.Expr <- go(left, Item{})
            +next : S.Tok <- P.peek
            S.choose(P.M(S.Expr), P.is_text(next, ","), u =>
              do P.M<S.Expr>:
                drop : S.Tok <- P.take
                go(left, Comma{S.JItem{S.expr(value), items}, start, P.tok_end(next)}), u =>
              P.M.pure(S.Expr, N.collection("Tuple", S.JItem{S.expr(value), items}, start, N.get_finish(value))))))
    case 1n+left Sequence{kind, start, close, items, separator}:
      P.meter(S.Expr, do P.M<S.Expr>:
        +t : S.Tok <- P.peek
        S.choose(P.M(S.Expr), P.is_text(t, close), u =>
          do P.M<S.Expr>:
            end : S.Tok <- P.take
            return N.collection(kind, items, start, P.tok_end(end)), u =>
          S.choose(P.M(S.Expr), O.unsupported(t), u => P.unsupported(S.Expr, "comprehension or expression"), u =>
            S.choose(P.M(S.Expr), separator, u =>
              do P.M<S.Expr>:
                drop : S.Tok <- P.expect(",")
                go(left, Sequence{kind, start, close, items, False{}}), u =>
              do P.M<S.Expr>:
                value : S.Expr <- go(left, Item{})
                go(left, Sequence{kind, start, close, S.JItem{S.expr(value), items}, True{}})))))
    case 1n+left Dictionary{start, keys, values, separator}:
      P.meter(S.Expr, do P.M<S.Expr>:
        +t : S.Tok <- P.peek
        S.choose(P.M(S.Expr), P.is_text(t, "}"), u =>
          do P.M<S.Expr>:
            end : S.Tok <- P.take
            return N.dict(keys, values, start, P.tok_end(end)), u =>
          S.choose(P.M(S.Expr), O.unsupported(t), u => P.unsupported(S.Expr, "dictionary comprehension"), u =>
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
                  go(left, Dictionary{start, S.JItem{S.expr(key), keys}, S.JItem{S.expr(value), values}, True{}}))))))
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
              call : S.Expr <- go(left, Arguments{first, S.JEnd{}, S.JEnd{}, False{}, False{}})
              go(left, Rest{minimum, call}), u =>
            S.choose(P.M(S.Expr), P.is_text(t, "["), u =>
              do P.M<S.Expr>:
                drop : S.Tok <- P.take
                +peek : S.Tok <- P.peek
                S.choose(P.M(S.Expr), P.is_text(peek, ":"), u => P.unsupported(S.Expr, "slice"), u =>
                  do P.M<S.Expr>:
                    index : S.Expr <- go(left, TestList{})
                    peek : S.Tok <- P.peek
                    S.choose(P.M(S.Expr), P.is_text(peek, ":"), u => P.unsupported(S.Expr, "slice"), u =>
                      do P.M<S.Expr>:
                        end : S.Tok <- P.expect("]")
                        go(left, Rest{minimum, N.subscript(first, N.index(index), P.tok_end(end))}))), u =>
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
    case 1n+left Arguments{fn, args, keywords, seen_kw, separator}:
      P.meter(S.Expr, do P.M<S.Expr>:
        +t : S.Tok <- P.peek
        S.choose(P.M(S.Expr), P.is_text(t, ")"), u =>
          do P.M<S.Expr>:
            end : S.Tok <- P.take
            return N.call(fn, args, keywords, P.tok_end(end)), u =>
          S.choose(P.M(S.Expr), O.unsupported(t), u => P.unsupported(S.Expr, "generator or argument"), u =>
            S.choose(P.M(S.Expr), separator, u =>
              do P.M<S.Expr>:
                drop : S.Tok <- P.expect(",")
                go(left, Arguments{fn, args, keywords, seen_kw, False{}}), u =>
              do P.M<S.Expr>:
                +next : S.Tok <- P.second
                S.choose(P.M(S.Expr), P.is_text(t, "**"), u =>
                  do P.M<S.Expr>:
                    drop : S.Tok <- P.take
                    value : S.Expr <- go(left, Expression{0n})
                    go(left, Arguments{fn, args, S.JItem{N.kw(S.JNull{}, value, P.tok_start(t)), keywords}, True{}, True{}}), u =>
                  S.choose(P.M(S.Expr), P.is_kind(t, "NAME") && P.is_text(next, "="), u =>
                    S.choose(P.M(S.Expr), non_ascii(P.tok_text(t)), u => P.unsupported(S.Expr, "Unicode keyword normalization"), u =>
                      do P.M<S.Expr>:
                        drop : S.Tok <- P.take
                        drop : S.Tok <- P.take
                        value : S.Expr <- go(left, Expression{0n})
                        go(left, Arguments{fn, args, S.JItem{N.kw(S.JStr{P.tok_text(t)}, value, P.tok_start(t)), keywords}, True{}, True{}})), u =>
                    S.choose(P.M(S.Expr), seen_kw && Bool.not(P.is_text(t, "*")), u => P.syntax(S.Expr, "positional argument follows keyword"), u =>
                      S.choose(P.M(S.Expr), P.is_text(t, "*"), u =>
                        S.choose(P.M(S.Expr), N.has_unpack(keywords), u => P.syntax(S.Expr, "iterable unpack follows keyword unpack"), u =>
                          do P.M<S.Expr>:
                            drop : S.Tok <- P.take
                            value : S.Expr <- go(left, Expression{0n})
                            go(left, Arguments{fn, S.JItem{S.expr(N.starred(P.tok_start(t), value)), args}, keywords, seen_kw, True{}})), u =>
                        do P.M<S.Expr>:
                          value : S.Expr <- go(left, Expression{0n})
                          go(left, Arguments{fn, S.JItem{S.expr(value), args}, keywords, seen_kw, True{}})))))))))
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
            +compound : S.Expr <- go(left, Compound{Bool.pick(String, P.is_text(t, "if"), "If", "While"), P.tok_start(t)})
            return N.block(N.one(compound), N.get_finish(compound)), u =>
          go(left, Simple{S.JEnd{}})))
    case 1n+left Simple{statements}:
      P.meter(S.Expr, do P.M<S.Expr>:
        +small : S.Expr <- go(left, Small{})
        +t : S.Tok <- P.peek
        +body : S.Json = S.fields_append(statements, N.one(small))
        S.choose(P.M(S.Expr), P.is_text(t, ";"), u =>
          do P.M<S.Expr>:
            drop : S.Tok <- P.take
            next : S.Tok <- P.peek
            S.choose(P.M(S.Expr), P.is_kind(next, "NEWLINE"), u =>
              do P.M<S.Expr>:
                drop : S.Tok <- P.take
                return N.block(body, N.get_finish(small)), u => go(left, Simple{body})), u =>
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
                  value : S.Expr <- go(left, TestList{})
                  end : S.Pos <- P.end
                  return N.statement("Return", S.expr(value), P.tok_start(t), end)), u =>
            S.choose(P.M(S.Expr), O.unsupported(t), u => P.unsupported(S.Expr, "statement " ++ P.tok_text(t)), u =>
              do P.M<S.Expr>:
                first : S.Expr <- go(left, TestList{})
                go(left, AfterSmall{first, P.tok_start(t)})))))
    case 1n+left AfterSmall{first, start}:
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
              value : S.Expr <- go(left, TestList{})
              end : S.Pos <- P.end
              return N.augmented(target, O.tag(String.drop_end(P.tok_text(t), 1n)), value, start, end), u =>
            S.choose(P.M(S.Expr), P.is_text(t, ":"), u => P.unsupported(S.Expr, "annotation"), u =>
              S.choose(P.M(S.Expr), String.eq(N.get_tag(first), "Name") &&
                String.eq(N.string(N.get(N.get_fields(first), "id")), "match") && Bool.not(O.is_end(t)), u =>
                P.unsupported(S.Expr, "match statement"), u =>
                do P.M<S.Expr>:
                  end : S.Pos <- P.end
                  return N.statement("Expr", S.expr(first), start, end))))))
    case 1n+left Assignment{targets, start}:
      P.meter(S.Expr, do P.M<S.Expr>:
        +value : S.Expr <- go(left, TestList{})
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

# K bounds dispatches, including no-consumption transitions, per token.
# P2 deterministic grammar fuzz records the observed global high-water mark.
def fuel_k() -> Nat:
  32n


def raw_result(+ts: List<&2, S.Tok>) -> Result<&2, &2, S.Error, P.Reply<S.Expr>>:
  +budget = fuel_k() * (S.token_count(ts, 0n) + 1n)
  go(budget, Block{True{}, S.JEnd{}, S.Pos{1n, 0n}}, P.State{ts, S.Pos{1n, 0n}, budget})


def parse(+ts: List<&2, S.Tok>) -> Result<&2, &2, S.Error, S.Module>:
  do Result<&2, &2, S.Error, S.Module>:
    result : P.Reply<S.Expr> <- raw_result(ts)
    syntax_result(result)

def statistics(count: Nat, r: P.Reply<S.Expr>) -> S.Json:
  P.Reply{body, P.State{ts, end, remaining}} = r
  +n = count
  S.JObj{S.JField{"tokens", S.JNum{n}, S.JField{"budget", S.JNum{fuel_k() * (1n+n)},
    S.JField{"used", S.JNum{fuel_k() * (1n+n) - remaining}, S.JEnd{}}}}}

def stats(+ts: List<&2, S.Tok>) -> Result<&2, &2, S.Error, S.Json>:
  do Result<&2, &2, S.Error, S.Json>:
    result : P.Reply<S.Expr> <- raw_result(ts)
    return statistics(S.token_count(ts, 0n), result)
