#!/usr/bin/env python3
"""Regex oracle: generated (pattern, flags, text) pairs, Bend vs CPython 3.11 `re.ASCII`.

Every pair is run through find / fullmatch / find_all / split / replace on the
C and JS lanes (all pairs) and the interpreter (a sample); the printed value
must equal, byte for byte, what CPython says: span + every group for search,
fullmatch and each finditer match, the split gaps, the literal substitution.

  tests/regex/oracle.py [--pairs 5000] [--interpret 500] [--seed 34]

Pinned: refuses to run on anything but CPython 3.11.15 (re-execs into PYTHON
below when started by another python); the executable, versions and sha256 of
the executable, the `re` sources, this file, base.bend and the corpus go to
tests/regex/_out/.
Exit 0 only on 0 diffs. `--selftest` corrupts one expectation and passes only
if that diff is detected.
"""

import argparse, hashlib, json, os, random, re, subprocess, sys, tempfile
from concurrent.futures import ThreadPoolExecutor

VERSION = (3, 11, 15)
PYTHON = os.environ.get("PY_ORACLE") or sys.executable  # same pin as tests/parser/normalize.py
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
OUT = os.path.join(ROOT, "tests/regex/_out")
CHUNK = 125
GROUP = 10
LIMIT = 4294967295

# ---- generator: v1 syntax only, as (source, nullable) -----------------------

LITS = "aaabbbcABC12_ -,\n\té😀"
TEXT = "aaaabbbbccABC12__  -,\n\n\té😀\r\x0b\x0c"
META = ".^$*+?{}[]()|\\"


def lit(r):
    c = r.choice(LITS)
    k = r.random()
    if k < 0.06:
        return "\\" + r.choice(META)               # an escaped metachar is itself
    if c == "\n":
        return "\\n" if k < 0.7 else c
    if c == "\t":
        return "\\t"
    if c in " -,":
        return "\\" + c if k < 0.15 else c         # so is escaped punctuation
    if k < 0.12:
        return "\\x%02x" % ord(c) if ord(c) < 256 else "\\U%08x" % ord(c)
    if k < 0.16 and ord(c) < 0x10000:
        return "\\u%04x" % ord(c)
    return c


def cls(r):
    items = []
    for _ in range(r.randint(1, 4)):
        k = r.random()
        if k < 0.3:
            items.append(r.choice(["a-c", "A-C", "0-9", "a-z", "1-2", "b-b"]))
        elif k < 0.5:
            items.append(
                r.choice(
                    [
                        "\\d",
                        "\\w",
                        "\\s",
                        "\\D",
                        "\\W",
                        "\\S",
                        "\\n",
                        "\\t",
                        "\\-",
                        "\\]",
                        "\\\\",
                        "\\x41",
                        "\\b",
                    ]
                )
            )
        else:
            items.append(r.choice("abcABC12_ ,é😀.$^*+?(){}|"[: r.choice([13, 25])]))
    body = "".join(i for n, i in enumerate(items) if not (i == "^" and n == 0))
    if not body:
        body = "a"
    if r.random() < 0.08:
        body += "-"
    return "[" + ("^" if r.random() < 0.25 else "") + body + "]"


def atom(r, d):
    k = r.random()
    if d > 0 and k < 0.22:
        s, n = alt(r, d - 1)
        return ("(" if r.random() < 0.65 else "(?:") + s + ")", n, True
    if k < 0.34:
        return cls(r), False, True
    if k < 0.42:
        return ".", False, True
    if k < 0.50:
        return r.choice(["\\d", "\\w", "\\s", "\\D", "\\W", "\\S"]), False, True
    if k < 0.58:
        return (
            r.choice(["^", "$", "\\b", "\\B"]),
            True,
            False,
        )  # CPython: an anchor takes no quantifier
    return lit(r), False, True


def piece(r, d):
    s, n, quantifiable = atom(r, d)
    if not quantifiable or r.random() < 0.55:
        return s, n
    k = r.random()
    if k < 0.2:
        q, lo, unbounded = "?", 0, False
    elif k < 0.4:
        q, lo, unbounded = "*", 0, True
    elif k < 0.6:
        q, lo, unbounded = "+", 1, True
    elif k < 0.72:
        lo = r.randint(0, 3)
        q, unbounded = "{%d}" % lo, False
    elif k < 0.84:
        lo = r.randint(0, 3)
        q, unbounded = "{%d,}" % lo, True
    else:
        lo = r.randint(0, 3)
        q, unbounded = "{%d,%d}" % (lo, lo + r.randint(0, 2)), False
    if unbounded and n:
        return s, n  # unbounded repeat of a nullable body: outside v1 (NullableRepeat)
    if r.random() < 0.25:
        q += "?"
    return s + q, n or lo == 0


def cat(r, d):
    ps = [piece(r, d) for _ in range(r.choice([1, 1, 2, 2, 3, 4]))]
    return "".join(p for p, _ in ps), all(n for _, n in ps)


def alt(r, d):
    k = r.random()
    bs = [cat(r, d) for _ in range(1 if k < 0.65 else 2 if k < 0.92 else 3)]
    if len(bs) > 1 and r.random() < 0.12:
        bs[r.randrange(len(bs))] = ("", True)
    return "|".join(b for b, _ in bs), any(n for _, n in bs)


def text(r, pat):
    n = r.choice([0, 1, 2, 3, 5, 8, 8, 13, 21, 34, 64])
    n = r.randint(0, n)
    pool = TEXT + "".join(c for c in pat if c.isprintable()) * 2
    return "".join(r.choice(pool) for _ in range(n))


def corpus(seed, count):
    r = random.Random(seed)
    pairs = []
    while len(pairs) < count:
        p, _ = alt(r, 3)
        f = "".join(c for c in "ims" if r.random() < 0.2)
        try:
            re.compile(p, pyflags(f))
        except re.error as e:  # the generator must only emit what CPython accepts
            raise SystemExit("generator bug: %r: %s" % (p, e))
        pairs.append(
            (p, f, text(r, p), r.choice(["", "-", "<é>", "\\1", "\\g<0>&", "😀\n"]))
        )
    return pairs


# ---- CPython side -----------------------------------------------------------


def pyflags(f):
    return (
        re.ASCII
        | (re.I if "i" in f else 0)
        | (re.M if "m" in f else 0)
        | (re.S if "s" in f else 0)
    )


def bend_str(s):
    esc = {10: "\\n", 9: "\\t", 13: "\\r", 0: "\\0", 92: "\\\\", 34: '\\"'}
    out = []
    for c in s:
        n = ord(c)
        out.append(esc.get(n) or ("\\u{%x}" % n if n < 32 or n == 127 else c))
    return '"' + "".join(out) + '"'


def show_match(m):
    if m is None:
        return "None{}"
    gs = [
        "None{}" if m.span(k) == (-1, -1) else "Some{(%dn, %dn)}" % m.span(k)
        for k in range(1, m.re.groups + 1)
    ]
    return "Match{%dn, %dn, [%s]}" % (m.start(), m.end(), ", ".join(gs))


def some(m):
    return "None{}" if m is None else "Some{%s}" % show_match(m)


def expect(pair):
    p, f, s, by = pair
    rx = re.compile(p, pyflags(f))
    ms = list(rx.finditer(s))
    ends = [0] + [m.end() for m in ms]
    gaps = [s[e : m.start()] for e, m in zip(ends, ms)] + [s[ends[-1] :]]
    # the reconstruction is CPython's own split (groups dropped) and sub
    assert rx.split(s)[:: rx.groups + 1] == gaps, pair
    sub = rx.sub(lambda m: by, s)
    assert sub == by.join(gaps), pair
    return "Done{(%s, %s, Done{[%s]}, Done{[%s]}, Done{%s})}" % (
        some(rx.search(s)),
        some(rx.fullmatch(s)),
        ", ".join(show_match(m) for m in ms),
        ", ".join(bend_str(g) for g in gaps),
        bend_str(sub),
    )


# ---- Bend side --------------------------------------------------------------

HEAD = """import Base

def Rec() -> Data:
  Sigma<&2, &2, Maybe<&2, Match>, _ => Sigma<&2, &2, Maybe<&2, Match>, _ => Sigma<&2, &2, Result<&2, &2, Regex.Error, List<&2, Match>>, _ => Sigma<&2, &2, Result<&2, &2, Regex.Error, List<&2, String>>, _ => Result<&2, &2, Regex.Error, String>>>>>

def one(r: Result<&2, &2, Regex.Error, Regex>, +s: String, by: String) -> Result<&2, &2, Regex.Error, Rec()>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+re}:
      Done{(Regex.find(re, s), (Regex.fullmatch(re, s), (Regex.find_all(re, s, %d), (Regex.split(re, s, %d), Regex.replace(re, s, by, %d)))))}

"""

# rows go in defs of GROUP: a literal of 25+ rows is "an arity over 255" on C
PART = """
def part%d() -> List<&2, Result<&2, &2, Regex.Error, Rec()>>:
  [%s]
"""

MAIN = """
def main() -> List<&2, List<&2, Result<&2, &2, Regex.Error, Rec()>>>:
  [%s]
"""


def program(pairs):
    rows = [
        "one(Regex.compile(%s, %s), %s, %s)" % tuple(map(bend_str, pr)) for pr in pairs
    ]
    parts = [rows[i : i + GROUP] for i in range(0, len(rows), GROUP)]
    return (
        HEAD % (LIMIT, LIMIT, LIMIT)
        + "".join(PART % (k, ",\n   ".join(g)) for k, g in enumerate(parts))
        + MAIN % ", ".join("part%d()" % k for k in range(len(parts)))
    )


def split_top(line):
    """The elements of a printed Bend list, split at depth-0 commas outside strings."""
    assert line.startswith("[") and line.endswith("]"), line[:200]
    out, depth, start, i, q = [], 0, 1, 1, False
    while i < len(line) - 1:
        c = line[i]
        if q:
            i += c == "\\"
            q = c != '"'
        elif c == '"':
            q = True
        elif c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif c == "," and depth == 0:
            out.append(line[start:i])
            start = i + 2
        i += 1
    return out + [line[start:-1]] if len(line) > 2 else out


def sh(cmd, timeout):
    p = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, timeout=timeout)
    if p.returncode != 0:
        raise RuntimeError(
            "%s -> %d\n%s"
            % (" ".join(cmd), p.returncode, (p.stdout + p.stderr)[-2000:])
        )
    return p.stdout


def lane(lane_name, src, work, tag):
    if lane_name == "interpret":
        return sh(["bun", "bend2/main.ts", src], 3600)
    exe = os.path.join(work, tag + (".js" if lane_name == "js" else ""))
    sh(["bun", "bend2/main.ts", src, "-o", exe], 1200)
    return sh(["bun", exe] if lane_name == "js" else [exe, "--gpu", "off"], 3600)


def run_chunk(job):
    lane_name, k, pairs, want, work = job
    tag = "%s_%03d" % (lane_name, k)
    src = os.path.join(work, tag + ".bend")
    with open(src, "w") as f:
        f.write(program(pairs))
    try:
        out = lane(lane_name, src, work, tag).rstrip("\n")
        got = [row for part in split_top(out) for row in split_top(part)]
    except Exception as e:
        return [(lane_name, k * CHUNK, pairs[0], "chunk failed", str(e))]
    if len(got) != len(pairs):
        return [
            (
                lane_name,
                k * CHUNK,
                pairs[0],
                "%d rows" % len(pairs),
                "%d rows" % len(got),
            )
        ]
    return [
        (lane_name, k * CHUNK + i, pairs[i], want[i], got[i])
        for i in range(len(pairs))
        if got[i] != want[i]
    ]


def sha(path):
    return hashlib.sha256(open(path, "rb").read()).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--pairs", type=int, default=5000)
    ap.add_argument("--interpret", type=int, default=500)
    ap.add_argument("--seed", type=int, default=34)
    ap.add_argument("--jobs", type=int, default=max(1, (os.cpu_count() or 2) // 2))
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args()
    if sys.implementation.name != "cpython" or sys.version_info[:3] != VERSION:
        if os.environ.get("ORACLE_REEXEC") or not os.path.exists(PYTHON):
            raise SystemExit("oracle is pinned to CPython 3.11.15, not %s" % sys.version)
        os.environ["ORACLE_REEXEC"] = "1"
        os.execv(PYTHON, [PYTHON] + sys.argv)
    if a.selftest:
        a.pairs, a.interpret = 8, 0
    pairs = corpus(a.seed, a.pairs)
    want = [expect(p) for p in pairs]
    if a.selftest:
        want[3] = want[3].replace("Done{(", "Done{(Some{Match{9n, 9n, []}}, ", 1)
    os.makedirs(OUT, exist_ok=True)
    blob = json.dumps(pairs, ensure_ascii=False).encode()
    with tempfile.TemporaryDirectory(prefix="bend-oracle.") as work:
        jobs = []
        for name, n in (("c", a.pairs), ("js", a.pairs), ("interpret", a.interpret)):
            jobs += [
                (name, k, pairs[i : i + CHUNK], want[i : i + CHUNK], work)
                for k, i in enumerate(range(0, n, CHUNK))
            ]
        with ThreadPoolExecutor(a.jobs) as ex:
            diffs = [d for ds in ex.map(run_chunk, jobs) for d in ds]
    for name, i, pr, w, g in diffs[:40]:
        print(
            "DIFF [%s] #%d pattern=%r flags=%r text=%r by=%r\n  want %s\n  got  %s"
            % (name, i, pr[0], pr[1], pr[2], pr[3], w, g)
        )
    counts = {n: sum(d[0] == n for d in diffs) for n in ("c", "js", "interpret")}
    if a.selftest:
        ok = sorted((d[0], d[1]) for d in diffs) == [("c", 3), ("js", 3)]
        print(
            "ok   selftest: corrupted expectation detected on c + js"
            if ok
            else "FAIL selftest: %r" % diffs
        )
        return 0 if ok else 1
    pin = {
        "executable": os.path.realpath(sys.executable),
        "python": sys.version,
        "re_flags": "re.ASCII",
        "bun": sh(["bun", "--version"], 60).strip(),
        "seed": a.seed,
        "pairs": a.pairs,
        "interpret_sample": a.interpret,
        "sha256": {
            "executable": sha(os.path.realpath(sys.executable)),
            "re/__init__.py": sha(re.__file__),
            "re/_parser.py": sha(re._parser.__file__),
            "re/_compiler.py": sha(re._compiler.__file__),
            "oracle.py": sha(os.path.abspath(__file__)),
            "bend2/base.bend": sha(os.path.join(ROOT, "bend2/base.bend")),
            "corpus.json": hashlib.sha256(blob).hexdigest(),
        },
        "diffs": counts,
    }
    with open(os.path.join(OUT, "corpus.json"), "wb") as f:
        f.write(blob)
    with open(os.path.join(OUT, "oracle.json"), "w") as f:
        json.dump(pin, f, indent=2)
    print(json.dumps(pin, indent=2))
    print(
        "\nOracle: %d pairs, diffs c=%d js=%d interpret(%d)=%d"
        % (a.pairs, counts["c"], counts["js"], a.interpret, counts["interpret"])
    )
    return 1 if diffs else 0


if __name__ == "__main__":
    sys.exit(main())
