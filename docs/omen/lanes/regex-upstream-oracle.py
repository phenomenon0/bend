#!/usr/bin/env python3.11
"""Writes tests/regex/oracle.bend: random (pattern, subject, at) rows in the
slice's grammar, pinned by CPython 3.11 `re` under re.ASCII.

  python3.11 gen.py [--rows 160] [--seed 7] > oracle.bend

A row prints search(s, at) | match(s, at) | fullmatch(s): a match as its
spans (group 0 first, `-` for a group that took no part), a failure as
`none`, a pattern CPython rejects as `err`. `*` and `+` never land on a
body that can match empty (the slice rejects those; CPython does not).
"""

import argparse, random, re, sys, warnings

LITS = "aaabbbcAB12_ -,é😀"
TEXT = "aaabbbcAB12_ -,\n\té😀"
ESCS = ".^$*+?()[]{}|\\-"
CLASS = ["\\d", "\\w", "\\s", "\\D", "\\W", "\\S"]


def lit(r):
    k = r.random()
    if k < 0.08:
        return "\\" + r.choice(ESCS)
    if k < 0.12:
        return r.choice(["\\n", "\\t", "}", "]"])
    return r.choice(LITS)


def cls(r):
    items = []
    for _ in range(r.randint(1, 3)):
        k = r.random()
        if k < 0.3:
            items.append(r.choice(["a-c", "A-C", "0-9", "b-b", "\\n-\\r"]))
        elif k < 0.5:
            items.append(r.choice(CLASS + ["\\n", "\\-", "\\]", "\\\\", "\\b"]))
        else:
            items.append(r.choice("abcAB12_ ,é.$*+?(){}|"))
    head = r.choice(["", "", "", "]", "-", "--/"])
    tail = "-" if r.random() < 0.1 else ""
    return "[" + ("^" if r.random() < 0.25 else "") + head + "".join(items) + tail + "]"


def atom(r, d):
    """(source, nullable, quantifiable)"""
    k = r.random()
    if d > 0 and k < 0.25:
        s, n = alt(r, d - 1)
        return ("(" if r.random() < 0.7 else "(?:") + s + ")", n, True
    if k < 0.37:
        return cls(r), False, True
    if k < 0.44:
        return ".", False, True
    if k < 0.52:
        return r.choice(CLASS), False, True
    if k < 0.60:
        return r.choice(["^", "$", "\\b", "\\B"]), True, False
    return lit(r), False, True


def piece(r, d):
    s, n, q = atom(r, d)
    if not q or r.random() < 0.6:
        return s, n
    ops = ["?", "??"] + ([] if n else ["*", "*?", "+", "+?"])
    op = r.choice(ops)
    return s + op, n or op[0] != "+"


def cat(r, d):
    parts = [piece(r, d) for _ in range(r.randint(0, 3))]
    return "".join(s for s, _ in parts), all(n for _, n in parts)


def alt(r, d):
    branches = [cat(r, d) for _ in range(r.choice([1, 1, 1, 2, 3]))]
    return "|".join(s for s, _ in branches), any(n for _, n in branches)


# Patterns CPython rejects (checked in main); the slice's own cuts, which
# CPython accepts, are pinned in parse.bend instead
BROKEN = [
            "a**",
            "a+?*",
            "*a",
            "a|*b",
            "(*a)",
            "^*",
            "$+",
            "\\b?",
            "(a",
            "a)",
            "(a|b",
            "((a)",
            "[a",
            "[]",
            "[^]",
            "[z-a]",
            "[\\d-z]",
            "[a-\\w]",
            "\\q",
            "a\\",
            "[\\q]",
            "\\1",
        ]


def bend_str(s):
    out = []
    for c in s:
        if c == "\\":
            out.append("\\\\")
        elif c == '"':
            out.append('\\"')
        elif c == "\n":
            out.append("\\n")
        elif c == "\t":
            out.append("\\t")
        elif c == "\r":
            out.append("\\r")
        elif ord(c) < 32:
            out.append("\\u{%X}" % ord(c))
        else:
            out.append(c)
    return '"' + "".join(out) + '"'


def spans(m):
    if m is None:
        return "none"
    return " ".join("-" if a < 0 else "%d-%d" % (a, b) for a, b in m.regs)


def answer(p, s, at):
    try:
        rx = re.compile(p, re.ASCII)
    except re.error:
        return "err"
    return " | ".join(
        spans(m) for m in (rx.search(s, at), rx.match(s, at), rx.fullmatch(s))
    )


HEAD = """\
# the CPython oracle: every row is (pattern, subject, at), run as
# search(s, at) | match(s, at) | fullmatch(s); a match prints its spans,
# group 0 first and - for a group that took no part, a failure none, a
# pattern that fails to compile err. The pins are CPython 3.11's `re`
# under re.ASCII on the same rows (%d rows, seed %d)
import Base

def Row() -> Data:
  Sigma<&2, &2, String, _ => Sigma<&2, &2, String, _ => Nat>>

def span(g: Maybe<&2, Sigma<&2, &2, Nat, _ => Nat>>) -> String:
  match g:
    case Some{(a, b)}:
      Nat.show(a) ++ "-" ++ Nat.show(b)
    case None{}:
      "-"

def spans.go(gs: List<&2, Maybe<&2, Sigma<&2, &2, Nat, _ => Nat>>>) -> String:
  match gs:
    case Nil{}:
      ""
    case g <> t:
      " " ++ span(g) ++ spans.go(t)

def spans(m: Maybe<&2, Regex.Match>) -> String:
  match m:
    case Some{Match{a, b, gs}}:
      span(Some{(a, b)}) ++ spans.go(gs)
    case None{}:
      "none"

def row(r: Result<&2, &2, String, Regex>, +s: String, +at: Nat) -> String:
  match r:
    case Fail{e}:
      "err"
    case Done{+re}:
      spans(Regex.exec(re, s, at)) ++ " | " ++ spans(Regex.match_at(re, s, at))
        ++ " | " ++ spans(Regex.fullmatch(re, s))

def rows(xs: List<&2, Row()>) -> String:
  match xs:
    case Nil{}:
      ""
    case (p, (s, at)) <> t:
      row(Regex.compile(p), s, at) ++ "\\n" ++ rows(t)

def main() -> IO(Unit):
  IO.print(rows([
"""


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--rows", type=int, default=160)
    ap.add_argument("--seed", type=int, default=7)
    a = ap.parse_args()
    assert sys.version_info[:2] == (3, 11), sys.version
    warnings.simplefilter("ignore")
    for p in BROKEN:
        assert answer(p, "", 0) == "err", p
    r = random.Random(a.seed)
    rows = []
    while len(rows) < a.rows:
        p = r.choice(BROKEN) if r.random() < 0.1 else alt(r, 2)[0]
        s = "".join(r.choice(TEXT) for _ in range(r.randint(0, 8)))
        at = r.choice([0, 0, 0, r.randint(0, len(s) + 1)])
        rows.append((p, s, at))
    out = [HEAD % (a.rows, a.seed)]
    out.append(
        ",\n".join(
            "    (%s, (%s, %dn))" % (bend_str(p), bend_str(s), at) for p, s, at in rows
        )
    )
    out.append("]))\n\n")
    out.extend("#|" + answer(p, s, at) + "\n" for p, s, at in rows)
    sys.stdout.write("".join(out))


main()
