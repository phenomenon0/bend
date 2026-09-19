"""Seeded supported-grammar generation, differential checks, and residual fuel measurements."""
from normalize import OUT, oracle, pin
from diff import build, run, compare
from fixtures import EXPRESSIONS, STATEMENTS, INVALID, UNSUPPORTED
import argparse
import ast
import json
import random


def expression(rng, depth):
    if depth <= 0 or rng.randrange(5) == 0:
        return rng.choice(["a", "b", "c", "0", "17", "0x10", "1.5", "True", "None", "'é😀'", "..."])
    sub = lambda: expression(rng, depth - 1)
    choice = rng.randrange(12)
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
                                  "with (" + value + ") as a, " + value + ":\n    pass\nwith (" + value + " as b, c):\n    nonlocal n\n"]))
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
