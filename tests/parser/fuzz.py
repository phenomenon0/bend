"""Seeded supported-grammar generation, differential checks, and residual fuel measurements."""
from normalize import OUT, oracle, pin
from diff import build, run, compare
from fixtures import EXPRESSIONS, STATEMENTS, INVALID, UNSUPPORTED
import argparse
import ast
import json
import random


def fstring(rng, sub):
    """An implicit-concatenation run with f-strings: fields, conversions, debug `=`, nested specs."""
    def field():
        value = sub()
        if any(c in value for c in '"\\#'):  # 3.11: the expression cannot reuse the quote, nor hold a backslash or comment
            value = "a"
        spec = rng.choice(["", "", ":", ":>10", ":{" + rng.choice(["w", "w!r", "w:>5"]) + "}", ":.{p}f", ": {a}{b} ", ":{{w}}"])
        return "{ " + value + rng.choice(["", " ", "=", " = "]) + rng.choice(["", "", "!r", "!s", "!a"]) + spec + "}"
    def token():
        if rng.randrange(4) == 0:
            return rng.choice(["'s'", "u'é'", "''", "r'\\d'", "'\\n'"])
        body = "".join(rng.choice(["", "a", "{{", "}}", "é😀", "\\n", " x ", "'", "\\N{DIGIT ONE}"]) if rng.randrange(2) else field()
                       for _ in range(rng.randrange(4)))
        return rng.choice(["f", "F", "rf", "fR"]) + '"' + body + '"'
    tokens = [token() for _ in range(rng.randrange(1, 4))]
    tokens[rng.randrange(len(tokens))] = 'f"' + field() + '"'
    return "(" + rng.choice([" ", "\n  "]).join(tokens) + ")"


def comprehension(rng, sub):
    """All four forms: nested `for` clauses, `if` filters, non-name targets, multi-line, the bare call argument."""
    gap = rng.choice([" ", " ", "\n  "])
    target = lambda: rng.choice(["a", "a", "a, b", "a, *b", "*a,", "(a, b)", "[a, (b, *c)]", "a.b", "a[0]", "a[1:2], b.c"])
    clause = lambda: gap + "for " + target() + " in " + sub() + "".join(gap + "if " + sub() for _ in range(rng.randrange(3)))
    clauses = "".join(clause() for _ in range(rng.randrange(1, 4)))
    return rng.choice(["[{0}{2}]", "{{{0}{2}}}", "{{{0}: {1}{2}}}", "({0}{2})", "f({0}{2})", "f( {0}{2} )(a)"]).format(sub(), sub(), clauses)


def annotated(rng, sub):
    """`target: annotation [= value]`: every target kind (parenthesised or not), any expression as annotation, star-expressions as value; some targets the oracle rejects."""
    target = rng.choice(["x", "x", "(x)", "((x))", "a.b", "(a.b)", "a[" + sub() + "]", "(" + sub() + ").c", "(" + sub() + ")[1:2]", "f(" + sub() + ").d",
                         "x, y", "(x, y)", "[x]", "*x", "f()", "(" + sub() + ")"])
    value = rng.choice(["", "", " = " + sub(), " = " + sub() + ", " + sub(), " = *a, " + sub(), " = " + sub() + ","])
    return target + rng.choice([": ", ":", " : "]) + sub() + value


def yielding(rng, sub):
    """`yield_expr | star_expressions` in every slot that takes it, and in some that do not (the oracle rejects those)."""
    y = rng.choice(["yield", "yield", "yield " + sub(), "yield " + sub(), "yield from " + sub(), "yield " + sub() + ", " + sub(), "yield *a, " + sub(), "yield " + sub() + ",",
                    "yield from " + sub() + ", b", "yield yield", "yield from *a"])
    g = "(" + y + ")"
    return rng.choice([y, y, "x = " + y, "x = y = " + y, "x " + rng.choice(["+=", "//=", "@="]) + " " + y, "x: " + sub() + " = " + y, "x: " + g, g, "(" + g + ")", "(\n " + y + "\n)",
                       "f(" + g + ", " + sub() + ", k=" + g + ")", g + ".a[" + g + "] = " + y, "[" + g + ", " + sub() + "]", "{" + g + ": " + g + "}", g + " if " + g + " else " + g, sub() + " + " + g, "not " + g,
                       "[" + g + " for x in " + g + " if " + g + "]", "f'{" + y + "}'", "f'{" + y + "!r:>{" + g + "}}'", "lambda: " + g, "return " + g, "yield " + g, "yield from " + g,
                       "f(" + y + ")", "[" + y + "]", "(" + y + ", 1)", "x = " + sub() + ", " + y, "return " + y, "lambda: " + y, y + " = 1", g + " = 1", y + ": int", "(" + y + " for x in y)", "a[" + y + "]", sub() + " + " + y])


def expression(rng, depth):
    if depth <= 0 or rng.randrange(5) == 0:
        return rng.choice(["a", "b", "c", "0", "17", "0x10", "1.5", "True", "None", "'é😀'", "..."])
    sub = lambda: expression(rng, depth - 1)
    choice = rng.randrange(18)
    if choice >= 15:
        return comprehension(rng, sub)
    if choice >= 13:
        return fstring(rng, sub)
    if choice == 0:
        return rng.choice(["-", "+", "~", "not "]) + "(" + sub() + ")"
    if choice < 4:
        return "(" + sub() + ") " + rng.choice(["+", "-", "*", "**", "@", "/", "//", "%", "<<", ">>", "|", "^", "&", "and", "or", "<", "is not", "not in"]) + " (" + sub() + ")"
    if choice == 4:
        return "(" + sub() + " if " + sub() + " else " + sub() + ")"
    if choice == 5:
        return "f(" + sub() + ", k=" + sub() + ")"
    if choice == 6:
        return "(" + sub() + ").attr[" + sub() + "]"
    if choice == 7:
        return "[" + sub() + ", " + sub() + "]"
    if choice == 8:
        return "{" + sub() + ": " + sub() + "}"
    if choice == 9:
        return "(" + sub() + ", " + sub() + ")"
    if choice == 10:
        return "{" + sub() + ", " + sub() + "}"
    if choice == 11:
        part = lambda: rng.choice(["", sub()])
        return "(" + sub() + ")[" + part() + ":" + part() + rng.choice(["", ":" + part()]) + rng.choice(["", ", " + sub(), ", ::" + part() + ","]) + "]"
    return "(" + sub() + " < " + sub() + " <= " + sub() + ")"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--count", type=int, default=1000)
    args = parser.parse_args()
    pin()
    build()
    rng = random.Random(0xA57A2026)
    sources = EXPRESSIONS + STATEMENTS
    for i in range(args.count):
        value = expression(rng, rng.randrange(1, 5))
        sources.append(rng.choice([value, "x = " + value, "x += " + value,
                                  "if " + value + ":\n    pass\nelse:\n    return x\n",
                                  "while " + value + ":\n    break\n",
                                  "def f(a, b=" + value + ", *c, d: " + value + " = 1, **e) -> " + value + ":\n    return lambda x, y=" + value + ": x;\n",
                                  "@" + value + "\ndef f():\n    for a, *b in " + value + ", c:\n        del a, b[" + value + "]\n    else:\n        assert " + value + ", a\n",
                                  "try:\n    raise " + value + " from " + value + "\nexcept " + value + " as e:\n    global g\nelse:\n    pass\nfinally:\n    x = 1\n",
                                  "import a.b as c, d\nif " + value + ":\n    from ..e.f import (g as h, i,)\n    from . import j; from k import *\n",
                                  "@" + value + "\nclass A(B, " + value + ", *c, metaclass=" + value + ", **k):\n    'doc'\n    x = " + value + "\n    class C: pass\n    @d\n    def f(self):\n        return " + value + "\nclass D(): y = 1; z = 2\n",
                                  "with (" + value + ") as a, " + value + ":\n    pass\nwith (" + value + " as b, c):\n    nonlocal n\n"]))
    # A second stream, so the P2-P9 sources above stay what they were.
    rng = random.Random(0xA57A2010)
    for i in range(args.count // 4):
        line = annotated(rng, lambda: expression(rng, rng.randrange(0, 3)))
        sources.append(rng.choice([line, line, "class A(B):\n    'doc'\n    " + line + "\n    y: int\n    def f(self):\n        self." + line + "\n",
                                  "if a: " + line + "; " + line + "\nelse:\n    " + line + "\n", "def f():\n    " + line + "\n    return x\n"]))
    # A third stream, for the same reason.
    rng = random.Random(0xA57A2011)
    for i in range(args.count // 4):
        line = yielding(rng, lambda: expression(rng, rng.randrange(0, 3)))
        sources.append(rng.choice([line, line, "def f():\n    " + line + "\n    return x\n", "def f(self):\n    while a:\n        " + line + "\n    else:\n        " + line + "; " + line + "\n",
                                  "if a: " + line + "; " + line + "\nelse:\n    " + line + "\n", "class A:\n    def f(self):\n        try:\n            " + line + "\n        finally:\n            pass\n"]))
    # Long lists/chains and nesting deliberately exercise non-consuming transitions.
    for n in [1, 2, 10, 50, 100, 200]:
        sources += ["(" * n + "a" + ")" * n, "[" * n + "a" + "]" * n,
                    "+".join(["a"] * n), " or ".join(["a"] * n),
                    "[" + ",".join(["a"] * n) + "]", "not " * n + "a"]
    records, failures, highwater = [], [], {"ratio": 0}
    path = OUT / "fuzz-input.py"
    for i, source in enumerate(sources):
        path.write_text(source)
        try:
            # Fuel acceptance is tested even if oracle AST conversion exceeds a host stack.
            ast.parse(source, feature_version=(3, 11), type_comments=False)
        except (SyntaxError, RecursionError, MemoryError) as exc:
            records.append({"i": i, "oracle-failure": str(exc)})
            # A generated source the oracle rejects (an f-string shape) is a negative: never parsed.
            if isinstance(exc, SyntaxError) and run(path)["status"] != "syntax":
                failures.append({"i": i, "source": source, "oracle": str(exc), "result": run(path)})
            continue
        result = run(path, mode="stats")
        if result["status"] != "parsed":
            failure = {"i": i, "source": source, "result": result}
            failures.append(failure)
            records.append(failure)
            continue
        stats = result["value"]
        ratio = stats["used"] / (stats["tokens"] + 1)
        if ratio > highwater["ratio"]:
            highwater = {"ratio": ratio, "i": i, **stats}
        rec = {"i": i, **stats}
        try:
            want, _ = oracle(source)
            got = run(path)
            if got["status"] != "parsed":
                failures.append({"i": i, "source": source, "result": got})
            else:
                struct, loc = compare(want, got["value"])
                if struct or loc:
                    failures.append({"i": i, "source": source, "structural": struct, "locations": loc})
            if i % 20 == 0:
                js = run(path, "js")
                if js.get("value") != got.get("value") or js["status"] != got["status"]:
                    failures.append({"i": i, "source": source, "js": js})
        except (RecursionError, MemoryError) as exc:
            rec["normalization-failure"] = str(exc)
        records.append(rec)
    for expected, cases in [("syntax", INVALID), ("unsupported", UNSUPPORTED)]:
        for source in cases:
            path.write_text(source)
            for lane in ("c", "js"):
                got = run(path, lane)
                if got["status"] != expected:
                    failures.append({"source": source, "lane": lane, "expected": expected, "got": got})
    counts = {"generated_and_directed": len(sources), "oracle_accepted": sum("used" in r or "result" in r for r in records),
              "oracle_rejected": sum("oracle-failure" in r for r in records), "fstring_sources": sum("f\"" in s.lower() for s in sources),
              "comprehension_sources": sum(" for " in s or "\n  for " in s for s in sources),
              "annotated_sources": args.count // 4, "yield_sources": args.count // 4,
              "no_limit_on_oracle_accepted": not any(f.get("result", {}).get("status") == "limit" for f in failures),
              "normalization_failures": sum("normalization-failure" in r for r in records),
              "negative_cases": len(INVALID) + len(UNSUPPORTED),
              "negative_runs": 2 * (len(INVALID) + len(UNSUPPORTED)),
              "js_samples": sum(r["i"] % 20 == 0 and "used" in r and "normalization-failure" not in r for r in records), "failures": len(failures), "fuel_k": 32,
              "highwater": highwater}
    (OUT / "fuzz-results.json").write_text(json.dumps({"counts": counts, "failures": failures, "records": records}, indent=2) + "\n")
    print(json.dumps(counts, indent=2))
    return bool(failures)


if __name__ == "__main__":
    raise SystemExit(main())
