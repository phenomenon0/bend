"""The translator judge: `judge.py --demo normalize_stem | repo_of | first_dash`.

Extracts one allow-listed function by `ast` (its module is never imported or
executed), translates it with demos/python/translate.bend, and reports three
separate claims (plan-astra-v2 §6, translator-modes.md C1-C3):

  C1 checker acceptance: no hole / open goal / @unsafe, strict check, four lanes build and run
  C2 source parity: pinned CPython oracle == check-accepted Bend, on literal examples,
     contract edge cases and seeded generated inputs, identically in every lane
  C3 semantic theorem status: reported as-is, never upgraded by C1 or C2

The doctest adapter (T2) is restricted on purpose. A doctest becomes a law only when
it is a CLOSED LITERAL CALL: `>>> f(<literals>)` of the demo's own def, positional
arguments that `ast.literal_eval` reads as str or list[str], and a want that reads
as a literal str / bool / None (no output = None). Each such example becomes
`law doctest_k: {T.f(args) == want : Ret}` proven by `{==}`, so the CHECKER decides
it by computation. The doctest text is parsed, never executed; every other example
(`is None`, a nested call, a name, a keyword, an exception, ...) is counted and
skipped, not approximated. A closed instance is not a universal theorem: C3 says so.
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
import doctest
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
            (("Hello World",), "hello-world"),
            (("  My Page  ",), "my-page"),
            (("already-stem",), "already-stem"),
            (("A  B",), "a--b"),
            (("",), ""),
            (("   ",), ""),
            (("MiXeD Case 42",), "mixed-case-42"),
        ],
        "builtins": {"str": str},
        "wrong": ("String.trim(s)", "s", "translation without strip"),
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
        "generate": lambda rng: (
            "".join(
                rng.choice(ALPHABET if rng.random() < 0.7 else WS + " AZaz-")
                for _ in range(rng.randrange(0, 24))
            ),
        ),
        "c3": "tested fragment, no theorem. The for/if/None idioms are unused; the translation rests on three primitive "
        "contracts (str.strip/lower/replace = String.trim/to_lower/replace on the ASCII value contract), assumed "
        "like SOUNDNESS.md A3 and only tested here. Lint grades this def `ownership Unknown` (method call = "
        "dynamic call in T0/O0): B1-B3 are argued from `str` immutability (A1), a paper-argued candidate.",
    },
    # Unannotated in the source: the reviewed signature is the stub in `sig`, and the judge
    # passes it as PY_SIG. No doctests: the examples are labeled contract fixtures (plan 4).
    "repo_of": {
        "path": Path.home() / "Documents/Project/llm-wiki/tools/overview.py",
        "sha256": "295c526c1ee5ec2b0381ab376ba7e8250320db37fdb5d6510823092b297e6500",
        "sig": "def repo_of(pid: str, slugs: list[str]) -> str | None:\n    pass\n",
        "builtins": {"len": len},
        "wrong": ('String.append(s, "-")', "s", "translation without the '-' boundary"),
        "examples": [
            (("bend.bend-lang-12", ["bend", "bend-lang"]), "bend-lang"),  # longest prefix
            (("bend.bend-lang-12", ["bend-lang", "bend"]), "bend-lang"),
            (("p.ab-1", ["ab", "ab"]), "ab"),
            (("p.a-b-1", ["a", "a-b", "a-c"]), "a-b"),
            (("p.xy-1", ["xy", "zz", "xy"]), "xy"),
            (("SRC-p.bend-1", ["bend"]), None),  # SRC- guard
            (("nodot", ["nodot"]), None),  # no '.'
            (("p.bend", ["bend"]), "bend"),  # tail == s
            (("p.bendx", ["bend"]), None),  # prefix without the '-' boundary
            (("p.bend-1", []), None),
        ],
        "edges": [
            ("", []),
            (".", [""]),
            (".-", [""]),  # "" + "-" is a prefix of the tail "-"
            ("a.b.c", ["b.c", "b"]),  # split once: the tail keeps its dots
            ("a.b.c-1", ["c", "b.c"]),
            ("src-p.x-1", ["x"]),  # the guard is case-sensitive
            ("xSRC-.x-1", ["x"]),
            ("SRC-", []),
            (".x", ["x", "x"]),
            ("p.ab-cd-ef", ["ab", "ab-cd", "ab-cd-ef", "ab-c"]),  # tail == s wins by length
            ("p.ab-cd", ["ab-cd", "ab", "zz-zz"]),  # same length later does not replace: strict >
            ("p.aa-1", ["aa", "bb"]),
            ("p.--", ["-", ""]),
            ("p. -1", [" ", "\t"]),
            ('p."q"-1', ['"q"', "\\"]),
            ("p." + "s" * 40 + "-t", ["s" * 40, "s" * 39]),
        ],
        "generate": lambda rng: (
            lambda slugs: (
                rng.choice(["", "SRC-", "p.", "p.", "p.", "proj.x.", "."])
                + rng.choice(slugs + ["zz", ""])
                + rng.choice(["", "-1", "-a-b", "x", ".y", "-"]),
                slugs[: rng.randrange(0, len(slugs) + 1)],
            )
        )(
            rng.sample(
                ["bend", "bend-lang", "bend-lang.com", "a", "a-b", "ab", "", "x", "-", "p"],
                6,
            )
        ),
        "c3": "tested fragment, no theorem. if/or/not-in, Optional narrowing and the for-fold are emitted as "
        "helper matches; the translation rests on the primitive contracts (startswith/in/==/+/len/>/not and "
        "guarded split(sep,1)[1] = Py.after under the known fact `sep in s`), assumed like SOUNDNESS.md A3 and "
        "only tested here. The source has no doctests, so no law is stated for it.",
    },
    # A labeled fixture, not a real module: `break` (the Step fold) and the doctest adapter.
    "first_dash": {
        "path": ROOT / "tests/translator/fixtures.py",
        "sha256": "9ee30afe73e14c99e533307134243c8bf9f34defd188fb8d7a5ba17c11ee6e26",
        "builtins": {"str": str, "list": list},
        "wrong": ("      Stop{hit}", "      Continue{hit}", "translation without break"),
        "examples": [
            ((["a", "-b", "-c"],), "-b"),
            (([],), None),
            ((["a", "b"],), None),
            ((["-", "-x"],), "-"),
        ],
        "edges": [([""],), (["", "-"],), (["a-", "-a", "-a"],), ([" -", "--"],)],
        "generate": lambda rng: (
            [
                rng.choice(["a", "-b", "", "-", "c-", "-c d", "\t-"])
                for _ in range(rng.randrange(0, 6))
            ],
        ),
        "c3": "tested fragment, no theorem. `break` is a Step fold (Continue/Stop): items after the stop are "
        "not evaluated. Its closed doctests are checked laws (closed instances, not a universal theorem).",
    },
}


def extract(path, name):
    """(def text, line, def node)."""
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
    return ast.get_source_segment(source, found[0]) + "\n", found[0].lineno, found[0]


def oracle(text, name, builtins):
    # The extracted def alone: nothing of its module, and no builtin but the demo's reviewed few.
    scope = {"__builtins__": builtins}
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


def bend_value(v):
    if v is None:
        return "None{}"
    if isinstance(v, bool):
        return "True{}" if v else "False{}"
    if isinstance(v, str):
        return bend_literal(v)
    return "[" + ", ".join(map(bend_value, v)) + "]"


def bend_type(node):
    """The Bend text of a fragment annotation: str, bool, list[T], T | None."""
    if isinstance(node, ast.Name) and node.id in ("str", "bool"):
        return {"str": "String", "bool": "Bool"}[node.id]
    if isinstance(node, ast.Subscript):
        return f"List<&2, {bend_type(node.slice)}>"
    if isinstance(node, ast.BinOp):
        return f"Maybe<&2, {bend_type(node.left)}>"
    raise SystemExit(f"FAIL annotation outside the fragment: {ast.dump(node)}")


def closed(value, ty):
    return {
        "String": lambda: isinstance(value, str),
        "Bool": lambda: isinstance(value, bool),
        "List<&2, String>": lambda: isinstance(value, list)
        and all(isinstance(x, str) for x in value),
        "Maybe<&2, String>": lambda: value is None or isinstance(value, str),
    }.get(ty, lambda: False)()


def doctest_laws(name, fn_node, sig_node):
    """([(args, want)], skipped): the closed literal-call doctests; parsed, never executed."""
    tys = [bend_type(a.annotation) for a in sig_node.args.args]
    laws, skipped = [], 0
    for ex in doctest.DocTestParser().get_examples(ast.get_docstring(fn_node) or ""):
        try:
            call = ast.parse(ex.source.strip(), mode="eval").body
            assert isinstance(call, ast.Call) and isinstance(call.func, ast.Name)
            assert call.func.id == name and not call.keywords and not ex.exc_msg
            args = tuple(ast.literal_eval(a) for a in call.args)
            want = ast.literal_eval(ex.want.strip()) if ex.want.strip() else None
            assert len(args) == len(tys) and all(map(closed, args, tys))
            assert closed(want, bend_type(sig_node.returns))
            laws.append((args, want))
        except (AssertionError, ValueError, SyntaxError):
            skipped += 1
    return laws, skipped


def law_file(name, ret, laws):
    out = ["import Base", f"import ./{name}.bend as T", ""]
    for k, (args, want) in enumerate(laws):
        call = f"T.{name}({', '.join(map(bend_value, args))})"
        value = bend_value(want)
        if ret.startswith("Maybe") and want is not None:
            value = f"Some{{{value}}}"
        out += [
            f"law doctest_{k}:",
            f"  {{{call} == {value} : {ret}}}",
            "",
            f"def doctest_{k}():",
            "  {==}",
            "",
        ]
    return "\n".join(out + ["def main() -> String:", '  "laws"']) + "\n"


def encode(e, maybe):
    if e is None:
        return "N|"
    return ("S " if maybe else "") + "".join(f"{ord(c)} " for c in e) + "|"


def harness(name, inputs, expected, maybe):
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
    if maybe:
        out += [
            "def shown(m: Maybe<&2, String>) -> String:",
            "  match m:",
            "    case None{}:",
            '      "N|"',
            "    case Some{s}:",
            '      "S " ++ codes(s)',
            "",
        ]
    for k, part in enumerate(parts):
        out += [
            f"def part{k}() -> String:",
            "  "
            + " ++\n  ".join(
                f"{'shown' if maybe else 'codes'}(T.{name}({', '.join(map(bend_value, a))}))"
                for a in part
            ),
            "",
        ]
    out += [
        "def main() -> String:",
        "  " + " ++ ".join(f"part{k}()" for k in range(len(parts))),
    ]
    want = '"' + "".join(encode(e, maybe) for e in expected) + '"'
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
    text, line, node = extract(demo["path"], name)
    sig_node = ast.parse(demo["sig"]).body[0] if "sig" in demo else node
    ret = bend_type(sig_node.returns)
    maybe = ret.startswith("Maybe")
    digest = hashlib.sha256(text.encode()).hexdigest()
    print(
        f"source   {demo['path']}:{line} {name} sha256 {digest[:16]} (ast extraction; module never imported)"
    )
    if digest != demo["sha256"]:
        raise SystemExit(
            f"FAIL source text changed (pinned {demo['sha256'][:16]}): re-review the contract, then re-pin"
        )
    fn = oracle(text, name, demo["builtins"])
    laws, skipped = doctest_laws(name, node, sig_node)
    bad = [(i, fn(*i), o) for i, o in demo["examples"] + laws if fn(*i) != o]
    if bad:
        raise SystemExit(f"FAIL oracle disagrees with the literal examples: {bad}")
    rng = random.Random(20260919)
    generated = [demo["generate"](rng) for _ in range(160)]
    edges = [e if isinstance(e, tuple) else (e,) for e in demo["edges"]]
    inputs = [i for i, _ in demo["examples"]] + edges + generated
    assert all(set(bend_value(a)) <= set(ALPHABET) for i in inputs for a in i), (
        "fixture outside the value contract"
    )
    expected = [fn(*i) for i in inputs]
    old, new, what = demo["wrong"]

    with tempfile.TemporaryDirectory(prefix="bend-judge.") as tmp:
        work = Path(tmp)
        (work / f"{name}.py").write_text(text, encoding="utf-8")
        (work / "sig.py").write_text(demo.get("sig", ""), encoding="utf-8")
        rc, emitted = sh(
            "bun",
            "bend2/main.ts",
            "demos/python/translate.bend",
            env={
                "PY_SOURCE": str(work / f"{name}.py"),
                "PY_DEF": name,
                **({"PY_SIG": str(work / "sig.py")} if "sig" in demo else {}),
            },
        )
        if rc != 0:
            raise SystemExit(f"FAIL emission blocked: {emitted}")
        (work / f"{name}.bend").write_text(emitted + "\n", encoding="utf-8")
        if show:
            print(emitted)
        test, want = harness(name, inputs, expected, maybe)
        (work / "demo.bend").write_text(test, encoding="utf-8")
        got = lanes(work / "demo.bend", work)

        # Harness controls: a hole must fail C1's text check; an unfaithful translation must fail C2.
        (work / "wrong").mkdir()
        (work / "wrong" / f"{name}.bend").write_text(
            emitted.replace(old, new) + "\n", encoding="utf-8"
        )
        (work / "wrong" / "demo.bend").write_text(test, encoding="utf-8")
        wrong = sh("bun", "bend2/main.ts", str(work / "wrong" / "demo.bend"))[1]

        # The doctest laws: the checker decides each by computation; a falsified want must fail.
        lawful = lied = None
        if laws:
            (work / "laws.bend").write_text(law_file(name, ret, laws), encoding="utf-8")
            lawful = sh("bun", "-e", CHECK, str(work / "laws.bend"))[1]
            lie = [(a, "~" if w is None else w + "~") for a, w in laws]
            (work / "laws.bend").write_text(law_file(name, ret, lie), encoding="utf-8")
            lied = sh("bun", "-e", CHECK, str(work / "laws.bend"))[1]
    controls = (
        holes(emitted.replace(old, "?hole")) == ["?"]
        and old in emitted
        and (not laws or "All terms check." not in lied)
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
    c3 = "tested-fragment"
    ok = True
    if laws or skipped:
        ok = lawful in (None, "All terms check.")
        c3 += f" + {len(laws) if ok else 0}/{len(laws)} closed doctest laws"
        print(
            f"doctest laws          : {'ok' if ok else 'FAIL'} {len(laws)} closed literal-call examples checked as laws "
            f"({{==}}, by the checker); {skipped} outside the restriction, skipped and not approximated"
        )
        if not ok:
            print(f"  laws: {lawful[:400]}")
    print(
        f"controls              : {'ok' if controls else 'FAIL'} (injected hole rejected by C1; {what} rejected by C2"
        + ("; falsified doctest laws rejected by the checker)" if laws else ")")
    )
    for k, v in got.items():
        if (k == "check" and v != "All terms check.") or (k != "check" and v != want):
            print(f"  lane {k}: {v[:400]}")
    print(
        f"{name}: C1 {'ok' if c1 else 'FAIL'} · C2 {min(per.values())}/{n} · C3 {c3}"
    )
    return c1 and c2 and ok and controls


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--demo", required=True, choices=sorted(DEMOS))
    ap.add_argument("--show", action="store_true", help="print the emitted Bend file")
    args = ap.parse_args()
    sys.exit(0 if judge(args.demo, args.show) else 1)


if __name__ == "__main__":
    main()
