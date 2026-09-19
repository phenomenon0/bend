#!/usr/bin/env python3
"""Independent CPython evidence for the lint specimens (empirical, not a proof).

For every tests/lint/*.bend: each embedded Python source must compile; every
`total` span in the #| block must be a FunctionDef span of the pinned oracle's
`ast`; every `unreachable` span must be a statement that follows another in a
block; every function graded `total Proven` by analyze is called on exact
built-in arguments and must terminate (return or raise) within the alarm.
Controls: `spin` and `alias` (graded Unknown) must NOT terminate, so the alarm
detects divergence and the AugAssign exclusion is shown necessary.

L2 (tests/lint/alias_*.bend): every advisory span is an oracle node span; a
function graded `ownership Proven` leaves every argument equal to its deep copy;
in alias_flag a function carries an Advisory iff it really mutates an argument
on some input (`use` is the unflagged one); alias_safe carries no Advisory and
mutates no argument. Control: `same` (total
Proven, ownership Unknown) tells shared arguments from copies, so O0's
identity exclusion is necessary.
"""
import ast, copy, glob, itertools, json, os, re, signal, sys, warnings

warnings.simplefilter("ignore")  # `s is "a"` is a specimen

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "parser"))
import normalize  # re-executes under the pinned CPython 3.11.15 oracle, or exits

LIT = re.compile(r'"(?:\\.|[^"\\])*"')

def sources(text):
    out = []
    for m in re.finditer(r'^def \w+\(\) -> String:\n((?:  +".*\n)+)', text, re.M):
        out.append("".join(json.loads(s) for s in LIT.findall(m.group(1))))
    return out

def values(ann):
    if isinstance(ann, ast.Name):
        return {"str": ["", "a", "héllo wörld"], "bool": [True, False], "int": [0, 3]}[ann.id]
    if isinstance(ann, ast.Subscript):
        inner = values(ann.slice)
        return [[], inner[:1], list(inner), list(inner) * 3]
    if isinstance(ann, ast.BinOp):
        return [None] + values(ann.left)
    raise ValueError(ast.dump(ann))

class Timeout(Exception):
    pass

def alarm(*_):
    raise Timeout()

def terminates(fn, args, limit=1.0):
    signal.signal(signal.SIGALRM, alarm)
    signal.setitimer(signal.ITIMER_REAL, limit)
    try:
        fn(*args)
    except Timeout:
        return False
    except Exception:
        pass  # T0 claims termination, not successful return
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
    return True

def mutated(fn, args):
    """True/False: fn changed an argument; per-input evidence, exceptions included."""
    before = copy.deepcopy(args)
    try:
        fn(*args)
    except Exception:
        pass
    return list(args) != list(before)

def inputs(node):
    return [copy.deepcopy(a) for a in itertools.product(*(values(a.annotation) for a in node.args.args))]

def main():
    fails = calls = spans = kept = hits = 0
    for path in sorted(glob.glob("tests/lint/*.bend")):
        text = open(path, encoding="utf-8").read()
        expected = "".join(json.loads(l[2:]) for l in text.splitlines() if l.startswith("#|"))
        defs, follows, nodes, flagged = {}, set(), set(), set()
        for src in sources(text):
            tree = ast.parse(src)
            env = {}
            for stmt in tree.body:  # one statement at a time: `@cache` raises NameError, the rest still bind
                try:
                    exec(compile(ast.Module([stmt], []), path, "exec"), env)
                except Exception:
                    pass
            for node in ast.walk(tree):
                for block in ("body", "orelse", "finalbody"):
                    for s in getattr(node, block, [])[1:] if isinstance(getattr(node, block, None), list) else []:
                        follows.add((s.lineno, s.col_offset, s.end_lineno, s.end_col_offset))
                if hasattr(node, "end_col_offset"):
                    nodes.add((node.lineno, node.col_offset, node.end_lineno, node.end_col_offset))
                if isinstance(node, ast.FunctionDef):
                    defs[(node.lineno, node.col_offset, node.end_lineno, node.end_col_offset)] = (node, env)
        for m in re.finditer(r"m\.py:(\d+):(\d+)-(\d+):(\d+) (\S+) (\w+)", expected):
            span, rule, grade = tuple(map(int, m.groups()[:4])), m.group(5), m.group(6)
            spans += 1
            if rule == "total" and span not in defs:
                print(f"FAIL {path}: total span {span} is no oracle FunctionDef"); fails += 1
            if rule == "unreachable" and span not in follows:
                print(f"FAIL {path}: unreachable span {span} follows nothing"); fails += 1
            if rule in ("ownership", "alias-mutation", "alias-escape", "param-mutation"):
                if span not in (defs if rule == "ownership" else nodes):
                    print(f"FAIL {path}: {rule} span {span} is no oracle node"); fails += 1
                flagged |= {d for d in defs if grade == "Advisory" and d[0] <= span[0] <= d[2]}
            if rule == "ownership" and grade == "Proven" and "forged" not in path and span in defs:
                node, env = defs[span]
                for args in inputs(node):
                    kept += 1
                    if mutated(env[node.name], args):
                        print(f"FAIL {path}: ownership Proven {node.name}{args} mutated an argument"); fails += 1
            if rule == "total" and grade == "Proven" and "forged" not in path and span in defs:
                node, env = defs[span]
                for args in itertools.product(*(values(a.annotation) for a in node.args.args)):
                    calls += 1
                    if not terminates(env[node.name], args):
                        print(f"FAIL {path}: Proven {node.name}{args} did not terminate"); fails += 1
        if path.endswith("alias_flag.bend") or path.endswith("alias_safe.bend"):
            for span, (node, env) in defs.items():
                real = any(mutated(env[node.name], a) for a in inputs(node))
                if real != (span in flagged) or (real and path.endswith("alias_safe.bend")):
                    print(f"FAIL {path}: {node.name} flagged={span in flagged}, mutates an argument={real}"); fails += 1
                hits += 1
        if path.endswith("alias_boundary.bend"):
            same, xs = defs[(1, 0, 2, 19)][1]["same"], ["a"]
            if same(xs, xs) and not same(list(xs), list(xs)):
                print("ok   control: same tells shared from copied arguments (ownership Unknown)")
            else:
                print("FAIL control: same does not observe sharing"); fails += 1
        if path.endswith("totality_unknown.bend"):
            env = defs[(1, 0, 4, 12)][1]
            for name, args in (("spin", ("a",)), ("alias", (["a"],))):
                if terminates(env[name], args, 0.2):
                    print(f"FAIL control: {name} terminated; the alarm detects nothing"); fails += 1
                else:
                    print(f"ok   control: {name} diverges under CPython (graded Unknown)")
    print(f"semantics: {spans} spans against the oracle, {calls} Proven calls terminated, {kept} ownership-Proven calls kept "
          f"their arguments, {hits} alias controls, {fails} failures")
    return 1 if fails or not calls else 0

if __name__ == "__main__":
    sys.exit(main())
