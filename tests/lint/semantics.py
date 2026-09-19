#!/usr/bin/env python3
"""Independent CPython evidence for the lint specimens (empirical, not a proof).

For every tests/lint/*.bend: each embedded Python source must parse; every
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

L3 (tests/lint/coverage_*.bend): every `exhaustive` span is an oracle Match, every
`dead-case` span an oracle case pattern, in the file its report names. The domain
of the subject is read off the evaluated annotation (`typing`, not M0) and each
function is called on every value of it (other parameters sampled) under
sys.settrace: `exhaustive Proven` = a case body runs whenever the match does and
the domain printed is the oracle's; `not exhaustive: v` = v is in the domain and
no case body runs for it; `dead-case Proven` = that case's body never runs; in w.py
CPython itself refuses to compile an irrefutable case ahead of others, both. Controls: shadowed, fake,
dflt, captured and untyped (graded Unknown) fall through every case on some
input, and `guarded` both runs and skips its guarded case, so each exclusion is
necessary.
"""
import ast, copy, glob, itertools, json, os, re, signal, sys, types, typing, warnings

warnings.simplefilter("ignore")  # `s is "a"` is a specimen

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "parser"))
import normalize  # re-executes under the pinned CPython 3.11.15 oracle, or exits

LIT = re.compile(r'"(?:\\.|[^"\\])*"')

def sources(text):
    out = []
    for m in re.finditer(r'^def (\w+)\(\) -> String:\n((?:  +".*\n)+)', text, re.M):
        out.append((m.group(1), "".join(json.loads(s) for s in LIT.findall(m.group(2)))))
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

def domain(t):
    """The finite value set an evaluated annotation admits, or None."""
    if t is bool:
        return [True, False]
    if t is None or t is type(None):
        return [None]
    if typing.get_origin(t) is typing.Literal:
        return list(typing.get_args(t))
    if typing.get_origin(t) in (typing.Union, types.UnionType):
        parts = [domain(a) for a in typing.get_args(t)]
        return None if any(d is None for d in parts) else sum(parts, [])
    return None

def traced(fn, args):
    """The lines of fn's own frame that run on fn(*args)."""
    lines = set()
    def tr(frame, event, arg):
        if frame.f_code is fn.__code__:
            if event == "line":
                lines.add(frame.f_lineno)
            return tr
    sys.settrace(tr)
    try:
        fn(*args)
    except Exception:
        pass
    finally:
        sys.settrace(None)
    return lines

def trials(fn, node, x):
    """(v, lines run) for every domain value v of parameter x, the others sampled."""
    d = domain(fn.__annotations__[x])
    pools = [d if a.arg == x else values(a.annotation) for a in node.args.args]
    i = [a.arg for a in node.args.args].index(x)
    return d, [(args[i], traced(fn, args)) for args in itertools.product(*pools)]

def inputs(node):
    return [copy.deepcopy(a) for a in itertools.product(*(values(a.annotation) for a in node.args.args))]

def main():
    fails = calls = spans = kept = hits = cov = 0
    for path in sorted(glob.glob("tests/lint/*.bend")):
        text = open(path, encoding="utf-8").read()
        expected = "".join(json.loads(l[2:]) for l in text.splitlines() if l.startswith("#|"))
        defs, follows, nodes, flagged = {}, set(), set(), set()
        where = {name: py for py, name in re.findall(r'report\("(\w+\.py)", parse\((\w+)\(\)\)\)', text)}
        sites, cases, envs, refused = {}, {}, {}, {}
        for name, src in sources(text):
            tree = ast.parse(src)
            py = where.get(name, "m.py")
            env = envs[py] = {}
            try:
                compile(src, py, "exec")
            except SyntaxError as e:
                refused[py] = str(e)
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
                    for mt in (n for n in ast.walk(node) if isinstance(n, ast.Match)):
                        sites[(py, mt.lineno, mt.col_offset, mt.end_lineno, mt.end_col_offset)] = (mt, node, env)
                        for k, c in enumerate(mt.cases):
                            p = c.pattern
                            cases[(py, p.lineno, p.col_offset, p.end_lineno, p.end_col_offset)] = (mt, k, node, env)
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
        for m in re.finditer(r"(\w+\.py):(\d+):(\d+)-(\d+):(\d+) (exhaustive|dead-case) (\w+) (.*)", expected):
            span, rule, grade, msg = (m.group(1), *map(int, m.groups()[1:5])), m.group(6), m.group(7), m.group(8)
            spans += span[0] != "m.py"  # m.py spans are counted by the loop above
            if span not in (sites if rule == "exhaustive" else cases):
                print(f"FAIL {path}: {rule} span {span} is no oracle {'Match' if rule == 'exhaustive' else 'case pattern'}"); fails += 1
                continue
            if "forged" in path or grade not in ("Proven", "Refuted") or "certificate refuted" in msg:
                continue
            mt, k, node, env = (*sites[span][:1], None, *sites[span][1:]) if rule == "exhaustive" else cases[span]
            if node.name not in env:
                # only an irrefutable unguarded case ahead of others: it catches every value, the rest are dead
                if "makes remaining patterns unreachable" not in refused.get(span[0], ""):
                    print(f"FAIL {path}: {node.name} did not compile: {refused.get(span[0])}"); fails += 1
                continue
            d, runs = trials(env[node.name], node, mt.subject.id)
            shown = "{" + ", ".join(map(repr, d)) + "}"
            bodies = [c.body[0].lineno for c in mt.cases]
            if grade == "Proven" and shown not in msg:
                print(f"FAIL {path}: {node.name}: the oracle domain is {shown}: {msg}"); fails += 1
            for v, lines in runs:
                cov += 1
                ran = mt.lineno in lines and any(b in lines for b in bodies)
                if rule == "exhaustive" and grade == "Proven" and mt.lineno in lines and not ran:
                    print(f"FAIL {path}: exhaustive Proven {node.name}: {v!r} ran no case"); fails += 1
                if rule == "exhaustive" and grade == "Refuted" and msg == f"not exhaustive: {v!r} matches no case" and ran:
                    print(f"FAIL {path}: {node.name}: {v!r} is claimed to match no case but ran one"); fails += 1
                if rule == "dead-case" and grade == "Proven" and bodies[k] in lines:
                    print(f"FAIL {path}: dead-case Proven {node.name} case {k} ran on {v!r}"); fails += 1
            if rule == "exhaustive" and grade == "Refuted" and not any(msg == f"not exhaustive: {v!r} matches no case" for v in d):
                print(f"FAIL {path}: {node.name}: the counterexample is outside the oracle domain {shown}: {msg}"); fails += 1
        if path.endswith("coverage_dead.bend"):
            if "makes remaining patterns unreachable" in refused.get("w.py", ""):
                print(f"ok   control: CPython refuses w.py: {refused['w.py']}")
            else:
                print("FAIL control: CPython compiles w.py"); fails += 1
        if path.endswith("coverage_missing.bend"):
            if envs["m.py"]["guarded"](True, True) == 1 and envs["m.py"]["guarded"](True, False) == 2:
                print("ok   control: guarded True runs its case or none, by the guard (graded Unknown)")
            else:
                print("FAIL control: guarded does not depend on its guard"); fails += 1
        if path.endswith("coverage_unknown.bend"):
            for py, name, args in (("n.py", "shadowed", (2,)), ("n.py", "fake", ("b",)), ("m.py", "dflt", ()),
                                   ("m.py", "captured", (True, 5)), ("m.py", "untyped", (2,))):
                if envs[py][name](*args) is None:
                    print(f"ok   control: {name}{args} falls through every case (graded Unknown)")
                else:
                    print(f"FAIL control: {name}{args} reached a case"); fails += 1
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
          f"their arguments, {hits} alias controls, {cov} coverage calls, {fails} failures")
    return 1 if fails or not calls else 0

if __name__ == "__main__":
    sys.exit(main())
