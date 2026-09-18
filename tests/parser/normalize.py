"""Pinned, non-executing CPython oracle and the two independent comparison passes."""
import os
import sys

ORACLE = "/home/omen/.hermes/hermes-agent/venv/bin/python3"
VERSION = (3, 11, 15)
if sys.version_info[:3] != VERSION or os.path.abspath(sys.executable) != ORACLE:
    os.execv(ORACLE, [ORACLE, *sys.argv])

import ast
import hashlib
import io
import json
import platform
import tokenize
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "tests/parser/_out"
OUT.mkdir(exist_ok=True)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def pin():
    data = {
        "executable": sys.executable, "realpath": os.path.realpath(sys.executable),
        "version": sys.version, "implementation": platform.python_implementation(),
        "sha256": {str(p): sha(p) for p in [sys.executable, ast.__file__, tokenize.__file__]},
        "ast_call": "ast.parse(source, feature_version=(3,11), type_comments=False)",
        "notes": [
            "200 nested parentheses accepted; 201 rejected by ast.parse",
            "ast.parse accepts return/break/continue outside a function/loop (no compile scope checks)",
            "AST columns are UTF-8 bytes; tokenize columns and Bend columns are code points",
            "RecursionError/MemoryError/timeouts are oracle failures, never parser verdicts",
            "Constant value = repr(literal_eval(raw)); implicit strings wrapped in parentheses",
            "type_comments=False; trivia and incidental parentheses are omitted",
        ],
    }
    (OUT / "oracle.json").write_text(json.dumps(data, indent=2) + "\n")
    return data


def intake(raw):
    """Strict UTF-8/BOM, coding cookies excluded before decoding."""
    encoding, _ = tokenize.detect_encoding(io.BytesIO(raw).readline)
    if encoding.lower().replace("_", "-") not in {"utf-8", "utf-8-sig"}:
        raise ValueError("coding-cookie:" + encoding)
    return raw.decode("utf-8-sig")


def boundaries(source):
    result = []
    for line in source.splitlines(keepends=True):
        mapping, byte = {0: 0}, 0
        for col, char in enumerate(line, 1):
            byte += len(char.encode("utf-8"))
            mapping[byte] = col
        result.append(mapping)
    return result


def literal(raw):
    # Newline protects a closing parenthesis from a final concatenation comment.
    return repr(ast.literal_eval("(" + raw + "\n)"))


def oracle(source):
    tree = ast.parse(source, feature_version=(3, 11), type_comments=False)
    maps = boundaries(source)

    def convert(node):
        if isinstance(node, ast.AST):
            d = {"tag": type(node).__name__}
            for field, value in ast.iter_fields(node):
                if isinstance(node, ast.Constant) and field == "value":
                    d[field] = literal(ast.get_source_segment(source, node))
                else:
                    d[field] = convert(value)
            if hasattr(node, "lineno"):
                d["_loc"] = [node.lineno, maps[node.lineno - 1][node.col_offset],
                             node.end_lineno, maps[node.end_lineno - 1][node.end_col_offset]]
            return d
        if isinstance(node, list):
            return [convert(x) for x in node]
        return node

    return convert(tree), tree


def normalize(value):
    """The Bend wire carries raw constants; only literal values use the host."""
    if isinstance(value, list):
        return [normalize(x) for x in value]
    if not isinstance(value, dict):
        return value
    if value.get("tag") == "Constant" and "_raw" in value:
        value = {"tag": "Constant", "value": literal(value["_raw"]),
                 "kind": value.get("kind"), "_loc": value["_loc"]}
    return {k: normalize(v) for k, v in value.items()}


def split(value, path="$", locations=None):
    """Every location is compared by AST path; no span sampling."""
    if locations is None:
        locations = {}
    if isinstance(value, dict):
        if "_loc" in value:
            locations[path] = value["_loc"]
        return ({k: split(v, path + "." + k, locations)[0]
                 for k, v in value.items() if k != "_loc"}, locations)
    if isinstance(value, list):
        return ([split(v, f"{path}[{i}]", locations)[0] for i, v in enumerate(value)], locations)
    return value, locations


def differences(want, got, path="$"):
    if type(want) is not type(got):
        return [{"path": path, "want": want, "got": got}]
    if isinstance(want, dict):
        result = []
        for key in dict.fromkeys([*want, *got]):
            if key not in want or key not in got:
                result.append({"path": path + "." + key, "missing": "want" if key not in want else "got"})
            else:
                result.extend(differences(want[key], got[key], path + "." + key))
        return result
    if isinstance(want, list):
        if len(want) != len(got):
            return [{"path": path, "lengths": [len(want), len(got)]}]
        return [d for i, (a, b) in enumerate(zip(want, got)) for d in differences(a, b, f"{path}[{i}]")]
    return [] if want == got else [{"path": path, "want": want, "got": got}]


SUPPORTED = set("""Module Constant Name Load Store Del Attribute Subscript Tuple List Starred
Set Dict UnaryOp UAdd USub Invert Not BinOp Add Sub Mult MatMult Div FloorDiv Mod Pow
LShift RShift BitOr BitXor BitAnd BoolOp And Or Compare Eq NotEq Lt LtE Gt GtE Is IsNot In NotIn
IfExp Call keyword Assign AugAssign Expr If While Return Pass Break Continue""".split())


def supported(tree):
    return all(type(node).__name__ in SUPPORTED for node in ast.walk(tree))
