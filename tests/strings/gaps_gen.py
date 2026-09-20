#!/usr/bin/env python3
# The oracle for gaps.bend: prints the whole fixture, every ASCII row's
# expectation computed by CPython's own str methods. run.sh diffs this
# against the checked-in file, so the fixture cannot drift from Python.
# The DEVIATIONS rows are ours by stance (ASCII semantics, total functions);
# their expectations are written by hand and argued in docs/omen/lanes/strgaps.md.


def lit(s):  # a Bend string literal
    return (
        '"'
        + "".join(
            c if 32 <= ord(c) < 127 and c not in '"\\' else "\\u{%x}" % ord(c)
            for c in s
        )
        + '"'
    )


def shown(s):  # the way Bend prints a string
    esc = {"\0": "\\0", "\t": "\\t", "\r": "\\r", "\n": "\\n", '"': '\\"', "\\": "\\\\"}
    return (
        '"'
        + "".join(
            esc.get(c) or (c if ord(c) >= 32 and ord(c) != 127 else "\\u{%x}" % ord(c))
            for c in s
        )
        + '"'
    )


def nat(n):
    return "%dn" % n


def strs(xs):
    return "[" + ", ".join(lit(x) for x in xs) + "]"


PREDS = [
    "isalpha",
    "isdigit",
    "isalnum",
    "isspace",
    "isupper",
    "islower",
    "isascii",
    "isprintable",
    "isidentifier",
    "isdecimal",
    "isnumeric",
    "istitle",
]


def preds(s):
    return "".join("FT"[getattr(s, p)()] for p in PREDS)


def fmt(f, args):
    try:
        return f.format(*args)
    except (ValueError, IndexError, KeyError):
        return "<none>"


rows = []  # (bend expression, expected string)

for s in [
    "",
    "abc",
    "ABC",
    "Abc",
    "abc1",
    "123",
    " \t\n\r\v\f",
    "a b",
    "A1",
    "1",
    "_x1",
    "1x",
    "x-y",
    "_",
    "if",
    "Hello World",
    "Hello world",
    "HELLO",
    "They'Re",
    "they're",
    "3D Tv",
    "3d",
    "A B",
    "aB",
    "\x7f",
    "~ !",
    "a\tb",
    " ",
    "a\x00",
]:
    rows.append(("preds(%s)" % lit(s), preds(s)))

for s, p in [
    ("foobar", "foo"),
    ("foobar", "bar"),
    ("foo", "foobar"),
    ("foo", ""),
    ("", "x"),
    ("foo", "foo"),
    ("aaa", "a"),
]:
    rows.append(("String.remove_prefix(%s, %s)" % (lit(s), lit(p)), s.removeprefix(p)))
    rows.append(("String.remove_suffix(%s, %s)" % (lit(s), lit(p)), s.removesuffix(p)))

for s, w, c in [
    ("ab", 5, "*"),
    ("ab", 4, "*"),
    ("a", 4, "-"),
    ("a", 5, "-"),
    ("abc", 6, " "),
    ("abc", 2, "."),
    ("", 3, "."),
    ("ab", 2, "."),
    ("a", 2, "."),
    ("ab", 3, "."),
    ("", 0, "."),
]:
    rows.append(("String.center(%s, %s, '%s')" % (lit(s), nat(w), c), s.center(w, c)))

for s in [
    "",
    "Hello World 123",
    "they're bill's",
    "3d tv",
    "aBC-dEf_gh",
    "x1y",
    "HELLO wORLD",
    "a\nb\tc",
]:
    rows.append(("String.swapcase(%s)" % lit(s), s.swapcase()))
    rows.append(("String.title(%s)" % lit(s), s.title()))
    rows.append(("String.casefold(%s)" % lit(s), s.casefold()))

for s, n in [
    ("a\tbc\td\n\tx", 4),
    ("\t", 8),
    ("ab\tc", 0),
    ("a\r\tb", 8),
    ("12345678\tx", 8),
    ("x\ty", 1),
    ("", 8),
    ("\t\t", 3),
    ("ab\n\ncd\te", 8),
]:
    rows.append(("String.expandtabs(%s, %s)" % (lit(s), nat(n)), s.expandtabs(n)))

for s, p in [
    ("a,b,,c", ","),
    ("aaa", "aa"),
    ("", ","),
    ("abc", "x"),
    ("a--b--", "--"),
    ("--", "--"),
    ("aaaa", "aa"),
    ("abc", "abc"),
]:
    rows.append(
        ("bars(String.rsplit(%s, %s))" % (lit(s), lit(p)), "|".join(s.rsplit(p)))
    )

for s, p in [
    ("a.b.c", "."),
    ("abc", "."),
    ("aaa", "aa"),
    ("", "x"),
    (".a", "."),
    ("a.", "."),
    ("a--b--c", "--"),
]:
    rows.append(
        ("tri(String.rpartition(%s, %s))" % (lit(s), lit(p)), "|".join(s.rpartition(p)))
    )

for f, args in [
    ("{} {}", ["a", "b"]),
    ("{1}{0}", ["a", "b"]),
    ("{0}{0}", ["a"]),
    ("{{}}", []),
    ("{{{}}}", ["x"]),
    ("{{0}}", ["x"]),
    ("", []),
    ("plain", ["unused"]),
    ("{01}", ["a", "b"]),
    ("{}", []),
    ("{2}", ["a", "b"]),
    ("{", []),
    ("}", []),
    ("a{0", ["x"]),
    ("{0}}", ["x"]),
    ("{0}{}", ["a", "b"]),
    ("{}{0}", ["a", "b"]),
    ("{ 0}", ["a"]),
    ("{a}", ["a"]),
    ("{-1}", ["a"]),
    ("{+1}", ["a", "b"]),
    ("x={}, y={}!", ["1", "2"]),
    ("}}{{", []),
    ("{99999999999999999999999999}", ["a"]),
]:
    rows.append(("fmt(String.format(%s, %s))" % (lit(f), strs(args)), fmt(f, args)))

DEVIATIONS = [
    # ASCII stance: Python says T for isalpha/islower/isprintable/isidentifier
    ('preds("\\u{e9}")', "FFFFFFFFFFFF"),
    # Python's isspace also takes U+001C..U+001F; ours is trim's set
    ('preds("\\u{1c}")', "FFFFFFTFFFFF"),
    # ARABIC-INDIC DIGIT THREE: Python's isdigit/isdecimal/isnumeric/isalnum say T
    ('preds("\\u{663}")', "FFFFFFFFFFFF"),
    # only ASCII letters are cased or letters: Python gives "Éa", "SS"
    ('String.title("\\u{e9}a")', "éA"),
    ('String.swapcase("\\u{df}")', "ß"),
    # total where Python raises ValueError("empty separator")
    ('bars(String.rsplit("abc", ""))', "abc"),
    ('tri(String.rpartition("abc", ""))', "||abc"),
    # v1 has no conversions and no format-spec mini-language
    ('fmt(String.format("{:>5}", ["a"]))', "<none>"),
    ('fmt(String.format("{0!r}", ["a"]))', "<none>"),
]
rows += DEVIATIONS

print(
    """# The Python-gap ops (lane-strgaps). GENERATED by gaps_gen.py, which is the
# oracle: every row above the deviations is CPython's own answer on ASCII
# input; run.sh fails if this file and the generator disagree. preds is one
# letter per predicate: alpha digit alnum space upper lower ascii printable
# identifier decimal numeric title.
import Base

def bit(b: Bool) -> String:
  Bool.pick(String, b, "T", "F")

def preds(+s: String) -> String:
  String.concat([bit(String.is_alpha(s)), bit(String.is_digit(s)),
    bit(String.is_alnum(s)), bit(String.is_space(s)), bit(String.is_upper(s)),
    bit(String.is_lower(s)), bit(String.is_ascii(s)), bit(String.is_printable(s)),
    bit(String.is_identifier(s)), bit(String.is_decimal(s)),
    bit(String.is_numeric(s)), bit(String.is_title(s))])

def bars(xs: List<&2, String>) -> String:
  String.join(xs, "|")

def tri(p: String & (String & String)) -> String:
  (a, (b, c)) = p
  bars([a, b, c])

def fmt(m: Maybe<&2, String>) -> String:
  Maybe.default(&2, String, m, "<none>")

def main() -> List<&2, String>:
  ["""
    + ",\n   ".join(r[0] for r in rows)
    + """]

#|["""
    + ", ".join(shown(r[1]) for r in rows)
    + "]"
)
