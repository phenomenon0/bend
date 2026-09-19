"""The translator judge: `judge.py --demo normalize_stem`.

Extracts one allow-listed function by `ast` (its module is never imported or
executed), translates it with demos/python/translate.bend, and reports three
separate claims (plan-astra-v2 §6, translator-modes.md C1-C3):

  C1 checker acceptance: no hole / open goal / @unsafe, strict check, four lanes build and run
  C2 source parity: pinned CPython oracle == check-accepted Bend, on literal examples,
     contract edge cases and seeded generated inputs, identically in every lane
  C3 semantic theorem status: reported as-is, never upgraded by C1 or C2
"""

import os
import sys

ORACLE = "/home/omen/.hermes/hermes-agent/venv/bin/python3"
VERSION = (3, 11, 15)
if os.path.abspath(sys.executable) != ORACLE:
    os.execv(ORACLE, [ORACLE, *sys.argv])
if sys.version_info[:3] != VERSION or sys.implementation.name != "cpython":
    raise SystemExit(f"Pinned oracle changed: {ORACLE}: {sys.version}")

import argparse
import ast
import hashlib
import random
import re
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
WS = " \t\n\r\x0b\x0c"
ALPHABET = (
    "".join(map(chr, range(32, 127))) + WS
)  # the value contract: printable ASCII + six ASCII whitespace

# Allow list. `sha256` pins the reviewed function text: a changed source is re-reviewed, not re-judged.
# `examples` are hand-written literals (the source has a docstring and no doctest: labeled contract
# fixtures per plan §4); the oracle must agree with them before it is trusted for anything else.
DEMOS = {
    "normalize_stem": {
        "path": Path.home() / "Documents/Project/llm-wiki/tools/wiki.py",
        "sha256": "4af82c046d8931ed49c1034276a54fd82481e69d6ca9a3191c60cf99be17434d",
        "examples": [
            ("Hello World", "hello-world"),
            ("  My Page  ", "my-page"),
            ("already-stem", "already-stem"),
            ("A  B", "a--b"),
            ("", ""),
            ("   ", ""),
            ("MiXeD Case 42", "mixed-case-42"),
        ],
        "edges": [
            *WS,
            WS,
            WS + "x" + WS,
            "\tTab Inside\tX\n",
            "a\nb c\r\nd",
            " - ",
            "-",
            "- -",
            "a b",
            " a b ",
            "\x0b\x0c A \x0c\x0b",
            "Z",
            "AZaz@[`{",
            "\"quoted\" 'single'",
            "back\\slash \\n",
            "x" + " " * 40 + "y",
            ALPHABET,
            ALPHABET[::-1],
            "  " + ALPHABET.upper() + "  ",
        ],
        "c3": "tested fragment, no theorem. The for/if/None idioms are unused; the translation rests on three primitive "
        "contracts (str.strip/lower/replace = String.trim/to_lower/replace on the ASCII value contract), assumed "
        "like SOUNDNESS.md A3 and only tested here. Lint grades this def `ownership Unknown` (method call = "
        "dynamic call in T0/O0): B1-B3 are argued from `str` immutability (A1), a paper-argued candidate.",
    },
}


def extract(path, name):
    source = Path(path).read_text(encoding="utf-8")
    found = [
        n
        for n in ast.parse(source, feature_version=(3, 11)).body
        if isinstance(n, ast.FunctionDef) and n.name == name
    ]
    if len(found) != 1:
        raise SystemExit(
            f"FAIL extract: {len(found)} top-level defs named {name} in {path}"
        )
    return ast.get_source_segment(source, found[0]) + "\n", found[0].lineno


def oracle(text, name):
    # The extracted def alone: nothing of its module, and no builtin but the annotation's `str`.
    scope = {"__builtins__": {"str": str}}
    exec(compile(text, name, "exec"), scope)
    return scope[name]


def bend_literal(s):
    named = {"\\": "\\\\", '"': '\\"', "\n": "\\n", "\t": "\\t", "\r": "\\r"}
    return (
        '"'
        + "".join(
            named.get(c) or (c if " " <= c <= "~" else "\\u{%x}" % ord(c)) for c in s
        )
        + '"'
    )


def harness(name, inputs, expected):
    """A house-style test: main prints each result as code points (no escaping convention to trust)."""
    parts = [inputs[i : i + 20] for i in range(0, len(inputs), 20)]
    out = [
        "import Base",
        f"import ./{name}.bend as T",
        "",
        "def codes(s: String) -> String:",
        "  match s:",
        "    case SNil{}:",
        '      "|"',
        "    case SCon{h, t}:",
        '      U32.show(Char.to_u32(h)) ++ " " ++ codes(t)',
        "",
    ]
    for k, part in enumerate(parts):
        out += [
            f"def part{k}() -> String:",
            "  " + " ++\n  ".join(f"codes(T.{name}({bend_literal(s)}))" for s in part),
            "",
        ]
    out += [
        "def main() -> String:",
        "  " + " ++ ".join(f"part{k}()" for k in range(len(parts))),
    ]
    want = '"' + "".join("".join(f"{ord(c)} " for c in e) + "|" for e in expected) + '"'
    return "\n".join(out) + "\n#|" + want + "\n", want


def holes(text):
    """C1, textual half: no hole, open goal or @unsafe outside comments and string literals."""
    code = "\n".join(
        re.sub(r'"(?:\\.|[^"\\])*"', '""', l)
        for l in text.splitlines()
        if not l.lstrip().startswith("#")
    )
    return [w for w in ("@unsafe", "?") if w in code]


CHECK = """import * as B from "./bend2/bend.ts";
const book = B.book_nil();
await B.book_load(book, process.argv[1], "", new Map());
B.book_valid(book);
if (book.hols + book.open) process.exit(1);
console.log("All terms check.");"""


def sh(*cmd, env=None):
    r = subprocess.run(
        cmd,
        cwd=ROOT,
        env={**os.environ, **(env or {})},
        capture_output=True,
        text=True,
        timeout=600,
    )
    return r.returncode, (r.stdout + r.stderr).strip()


def lanes(test, work):
    """{lane: output}; a lane that fails to build or run reports its failure text, never a skip."""
    got = {
        "check": sh("bun", "-e", CHECK, str(test))[1],
        "interpret": sh("bun", "bend2/main.ts", str(test))[1],
    }
    for lane, target, run in (
        ("js", work / "t.js", ["bun", str(work / "t.js")]),
        ("c", work / "t", [str(work / "t"), "--gpu", "off"]),
    ):
        rc, log = sh("bun", "bend2/main.ts", str(test), "-o", str(target))
        got[lane] = sh(*run)[1] if rc == 0 else f"build failed: {log[:300]}"
    return got


def judge(name, show):
    demo = DEMOS[name]
    text, line = extract(demo["path"], name)
    digest = hashlib.sha256(text.encode()).hexdigest()
    print(
        f"source   {demo['path']}:{line} {name} sha256 {digest[:16]} (ast extraction; module never imported)"
    )
    if digest != demo["sha256"]:
        raise SystemExit(
            f"FAIL source text changed (pinned {demo['sha256'][:16]}): re-review the contract, then re-pin"
        )
    fn = oracle(text, name)
    bad = [(i, fn(i), o) for i, o in demo["examples"] if fn(i) != o]
    if bad:
        raise SystemExit(f"FAIL oracle disagrees with the literal examples: {bad}")
    rng = random.Random(20260919)
    generated = [
        "".join(
            rng.choice(ALPHABET if rng.random() < 0.7 else WS + " AZaz-")
            for _ in range(rng.randrange(0, 24))
        )
        for _ in range(160)
    ]
    inputs = [i for i, _ in demo["examples"]] + demo["edges"] + generated
    assert all(set(i) <= set(ALPHABET) for i in inputs), (
        "fixture outside the value contract"
    )
    expected = [fn(i) for i in inputs]

    with tempfile.TemporaryDirectory(prefix="bend-judge.") as tmp:
        work = Path(tmp)
        (work / f"{name}.py").write_text(text, encoding="utf-8")
        rc, emitted = sh(
            "bun",
            "bend2/main.ts",
            "demos/python/translate.bend",
            env={"PY_SOURCE": str(work / f"{name}.py"), "PY_DEF": name},
        )
        if rc != 0:
            raise SystemExit(f"FAIL emission blocked: {emitted}")
        (work / f"{name}.bend").write_text(emitted + "\n", encoding="utf-8")
        if show:
            print(emitted)
        test, want = harness(name, inputs, expected)
        (work / "demo.bend").write_text(test, encoding="utf-8")
        got = lanes(work / "demo.bend", work)

        # Harness controls: a hole must fail C1's text check; an unfaithful translation must fail C2.
        (work / "wrong").mkdir()
        (work / "wrong" / f"{name}.bend").write_text(
            emitted.replace("String.trim(s)", "s") + "\n", encoding="utf-8"
        )
        (work / "wrong" / "demo.bend").write_text(test, encoding="utf-8")
        wrong = sh("bun", "bend2/main.ts", str(work / "wrong" / "demo.bend"))[1]
    controls = (
        holes(emitted.replace("String.trim(s)", "?hole")) == ["?"]
        and "String.trim(s)" in emitted
        and wrong != want
        and wrong.startswith('"')
    )

    c1 = (
        not holes(emitted)
        and got["check"] == "All terms check."
        and all(v.startswith('"') for k, v in got.items() if k != "check")
    )
    same = len({got[k] for k in ("interpret", "js", "c")}) == 1
    per = {
        k: sum(
            a == b
            for a, b in zip(
                got[k].strip('"').split("|"), want.strip('"').split("|")[:-1]
            )
        )
        for k in ("interpret", "js", "c")
    }
    c2 = same and all(got[k] == want for k in per)
    n = len(inputs)
    print(
        f"fixtures {len(demo['examples'])} literal examples + {len(demo['edges'])} contract edges + {len(generated)} generated (seed 20260919) = {n}"
    )
    print(
        f"C1 checker acceptance : {'ok' if c1 else 'FAIL'} (no hole/open goal/@unsafe; strict check; lanes check+interpret+js+c all ran)"
    )
    print(
        f"C2 source parity      : {'ok' if c2 else 'FAIL'} "
        + " ".join(f"{k} {v}/{n}" for k, v in per.items())
        + f"; lanes identical: {same}"
    )
    print(f"C3 theorem status     : {demo['c3']}")
    print(
        f"controls              : {'ok' if controls else 'FAIL'} (injected hole rejected by C1; translation without strip rejected by C2)"
    )
    for k, v in got.items():
        if (k == "check" and v != "All terms check.") or (k != "check" and v != want):
            print(f"  lane {k}: {v[:400]}")
    print(
        f"{name}: C1 {'ok' if c1 else 'FAIL'} · C2 {min(per.values())}/{n} · C3 tested-fragment"
    )
    return c1 and c2 and controls


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--demo", required=True, choices=sorted(DEMOS))
    ap.add_argument("--show", action="store_true", help="print the emitted Bend file")
    args = ap.parse_args()
    sys.exit(0 if judge(args.demo, args.show) else 1)


if __name__ == "__main__":
    main()
