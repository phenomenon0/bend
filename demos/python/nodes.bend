# AST builders. Semantic spans and syntactic covers differ for parentheses.
import Base
import ./syntax.bend as S
import ./parse_state.bend as P

def node(tag: String, fields: S.Json, +lo: S.Pos, +hi: S.Pos) -> S.Expr:
  S.Expr{tag, fields, lo, hi, S.Span{lo, hi}, False{}}

def get_tag(e: S.Expr) -> String:
  S.Expr{tag, fs, lo, hi, cover, grouped} = e
  tag

def get_fields(e: S.Expr) -> S.Json:
  S.Expr{tag, fs, lo, hi, cover, grouped} = e
  fs

def get_begin(e: S.Expr) -> S.Pos:
  S.Expr{tag, fs, lo, hi, S.Span{begin, end}, grouped} = e
  begin

def get_finish(e: S.Expr) -> S.Pos:
  S.Expr{tag, fs, lo, hi, S.Span{begin, end}, grouped} = e
  end

def group(+e: S.Expr, +start: S.Pos, +end: S.Pos) -> S.Expr:
  S.Expr{+tag, +fs, lo, hi, cover, grouped} = e
  S.choose(S.Expr, String.eq(tag, "Tuple") && Bool.not(grouped), u =>
    S.Expr{tag, fs, start, end, S.Span{start, end}, True{}}, u =>
    S.Expr{tag, fs, lo, hi, S.Span{start, end}, True{}})

def op(s: String) -> S.Json:
  S.JObj{S.JField{"tag", S.JStr{s}, S.JEnd{}}}

def get(fs: S.Json, +key: String) -> S.Json:
  match fs:
    case S.JField{+k, +v, rest}:
      S.choose(S.Json, String.eq(k, key), u => v, u => get(rest, key))
    case _:
      S.JNull{}

def string(j: S.Json) -> String:
  match j:
    case S.JStr{s}:
      s
    case _:
      ""

def reverse(xs: S.Json, acc: S.Json) -> S.Json:
  match xs:
    case S.JItem{h, t}:
      reverse(t, S.JItem{h, acc})
    case _:
      acc

def arr(xs: S.Json) -> S.Json:
  S.JArr{reverse(xs, S.JEnd{})}

def one(e: S.Expr) -> S.Json:
  S.JItem{S.expr(e), S.JEnd{}}

def name(+t: S.Tok) -> S.Expr:
  node("Name", S.JField{"id", S.JStr{P.tok_text(t)}, S.JField{"ctx", S.context(S.Load{}), S.JEnd{}}}, P.tok_start(t), P.tok_end(t))

def constant(raw: String, kind: S.Json, lo: S.Pos, hi: S.Pos) -> S.Expr:
  node("Constant", S.JField{"_raw", S.JStr{raw}, S.JField{"kind", kind, S.JEnd{}}}, lo, hi)

def atom_constant(+t: S.Tok) -> S.Expr:
  constant(P.tok_text(t), S.JNull{}, P.tok_start(t), P.tok_end(t))

def collection(+kind: String, items: S.Json, lo: S.Pos, hi: S.Pos) -> S.Expr:
  node(kind, S.JField{"elts", arr(items), S.choose(S.Json, String.eq(kind, "Set"), u => S.JEnd{}, u =>
    S.JField{"ctx", S.context(S.Load{}), S.JEnd{}})}, lo, hi)

def unary(operator: String, start: S.Pos, +value: S.Expr) -> S.Expr:
  node("UnaryOp", S.JField{"op", op(operator), S.JField{"operand", S.expr(value), S.JEnd{}}}, start, get_finish(value))

def binary(+left: S.Expr, operator: String, +right: S.Expr) -> S.Expr:
  node("BinOp", S.JField{"left", S.expr(left), S.JField{"op", op(operator), S.JField{"right", S.expr(right), S.JEnd{}}}}, get_begin(left), get_finish(right))

def starred(start: S.Pos, +value: S.Expr) -> S.Expr:
  node("Starred", S.JField{"value", S.expr(value), S.JField{"ctx", S.context(S.Load{}), S.JEnd{}}}, start, get_finish(value))

def boolean(operator: String, values: S.Json, start: S.Pos, end: S.Pos) -> S.Expr:
  node("BoolOp", S.JField{"op", op(operator), S.JField{"values", arr(values), S.JEnd{}}}, start, end)

def compare(left: S.Expr, ops: S.Json, values: S.Json, start: S.Pos, end: S.Pos) -> S.Expr:
  node("Compare", S.JField{"left", S.expr(left), S.JField{"ops", arr(ops), S.JField{"comparators", arr(values), S.JEnd{}}}}, start, end)

def conditional(+body: S.Expr, test: S.Expr, +other: S.Expr) -> S.Expr:
  node("IfExp", S.JField{"test", S.expr(test), S.JField{"body", S.expr(body), S.JField{"orelse", S.expr(other), S.JEnd{}}}}, get_begin(body), get_finish(other))

def attr(+value: S.Expr, +id: S.Tok) -> S.Expr:
  node("Attribute", S.JField{"value", S.expr(value), S.JField{"attr", S.JStr{P.tok_text(id)}, S.JField{"ctx", S.context(S.Load{}), S.JEnd{}}}}, get_begin(value), P.tok_end(id))

def subscript(+value: S.Expr, index: S.Expr, end: S.Pos) -> S.Expr:
  node("Subscript", S.JField{"value", S.expr(value), S.JField{"slice", S.expr(index), S.JField{"ctx", S.context(S.Load{}), S.JEnd{}}}}, get_begin(value), end)

def call(+fn: S.Expr, args: S.Json, keywords: S.Json, end: S.Pos) -> S.Expr:
  node("Call", S.JField{"func", S.expr(fn), S.JField{"args", arr(args), S.JField{"keywords", arr(keywords), S.JEnd{}}}}, get_begin(fn), end)

def kw(arg: S.Json, +value: S.Expr, lo: S.Pos) -> S.Json:
  S.expr(node("keyword", S.JField{"arg", arg, S.JField{"value", S.expr(value), S.JEnd{}}}, lo, get_finish(value)))

def dict(keys: S.Json, values: S.Json, lo: S.Pos, hi: S.Pos) -> S.Expr:
  node("Dict", S.JField{"keys", arr(keys), S.JField{"values", arr(values), S.JEnd{}}}, lo, hi)

# Only target containers and Starred recurse. Attribute.value and Subscript's
# value/slice stay Load; blindly rewriting every descendant ctx is incorrect.
def target_ok(j: S.Json, +mode: String) -> Bool:
  match j:
    case S.JObj{+fs}:
      +tag = string(get(fs, "tag"))
      (String.eq(tag, "Name") || String.eq(tag, "Attribute") || String.eq(tag, "Subscript") ||
        String.eq(tag, "List") || String.eq(tag, "Tuple") || String.eq(tag, "Starred")) && target_ok(fs, tag)
    case S.JField{+key, value, rest}:
      S.choose(Bool, (String.eq(key, "elts") && (String.eq(mode, "Tuple") || String.eq(mode, "List"))) ||
        (String.eq(key, "value") && String.eq(mode, "Starred")), u => target_ok(value, ""), u => True{}) && target_ok(rest, mode)
    case S.JArr{items}:
      target_ok(items, "")
    case S.JItem{h, t}:
      target_ok(h, "") && target_ok(t, "")
    case _:
      True{}

def target_ctx(j: S.Json, +mode: String) -> S.Json:
  match j:
    case S.JObj{+fs}:
      S.JObj{target_ctx(fs, string(get(fs, "tag")))}
    case S.JField{+key, +value, rest}:
      S.JField{key, S.choose(S.Json, String.eq(key, "ctx"), u => S.context(S.Store{}), u =>
        S.choose(S.Json, (String.eq(key, "elts") && (String.eq(mode, "Tuple") || String.eq(mode, "List"))) ||
          (String.eq(key, "value") && String.eq(mode, "Starred")), u => target_ctx(value, ""), u => value)), target_ctx(rest, mode)}
    case S.JArr{items}:
      S.JArr{target_ctx(items, "")}
    case S.JItem{h, t}:
      S.JItem{target_ctx(h, ""), target_ctx(t, "")}
    case _:
      j

def target(+e: S.Expr, +aug: Bool) -> Result<&2, &2, S.Error, S.Json>:
  +j = S.expr(e)
  +t = get_tag(e)
  S.choose(Result<&2, &2, S.Error, S.Json>, target_ok(j, "") && Bool.not(String.eq(t, "Starred")) &&
    (Bool.not(aug) || String.eq(t, "Name") || String.eq(t, "Attribute") || String.eq(t, "Subscript")), u =>
    Done{target_ctx(j, "")}, u => Fail{S.PErr{S.Syntax{}, get_begin(e), "invalid assignment target"}})

def block(items: S.Json, +end: S.Pos) -> S.Expr:
  node("$block", items, end, end)

def get_body(e: S.Expr) -> S.Json:
  get_fields(e)

def statement(tag: String, value: S.Json, lo: S.Pos, hi: S.Pos) -> S.Expr:
  node(tag, S.JField{"value", value, S.JEnd{}}, lo, hi)

def assignment(targets: S.Json, value: S.Expr, lo: S.Pos, hi: S.Pos) -> S.Expr:
  node("Assign", S.JField{"targets", arr(targets), S.JField{"value", S.expr(value), S.JField{"type_comment", S.JNull{}, S.JEnd{}}}}, lo, hi)

def augmented(target: S.Json, operator: String, value: S.Expr, lo: S.Pos, hi: S.Pos) -> S.Expr:
  node("AugAssign", S.JField{"target", target, S.JField{"op", op(operator), S.JField{"value", S.expr(value), S.JEnd{}}}}, lo, hi)

def compound(kind: String, test: S.Expr, body: S.Expr, +other: S.Expr, lo: S.Pos) -> S.Expr:
  node(kind, S.JField{"test", S.expr(test), S.JField{"body", S.JArr{get_fields(body)}, S.JField{"orelse", S.JArr{get_fields(other)}, S.JEnd{}}}}, lo, get_finish(other))

# CPython 3.11 wraps a lone starred subscript in a Tuple even without a comma.
def index(+e: S.Expr) -> S.Expr:
  S.choose(S.Expr, String.eq(get_tag(e), "Starred"), u =>
    collection("Tuple", one(e), get_begin(e), get_finish(e)), u => e)

def null(j: S.Json) -> Bool:
  match j:
    case S.JNull{}:
      True{}
    case _:
      False{}

def has_unpack(xs: S.Json) -> Bool:
  match xs:
    case S.JItem{S.JObj{fs}, tail}:
      null(get(fs, "arg")) || has_unpack(tail)
    case _:
      False{}
