#!/usr/bin/env python3
"""Times tests/regex/bench.bend at size: its defs, one main per case.

bench.py [--case scan|doubling|rescan|all] [--runs 7] [--ref-k 1024]

scan      4 patterns on 1 MiB of code points (k = 16384 lines of 64 + a tail):
          native on C and JS; the reference VM at --ref-k lines (it is
          superlinear on C, see doubling) and once, untimed-warmup-free, at 1 MiB.
doubling  pattern 2 (fixed m) at n, 2n, 4n: native from 1 MiB, reference from
          --ref-k lines. `base` rows build the text only: the floor to subtract.
rescan    `a.*b|a` on n `a`s: n(n+1)/2 steps. ns/step pins the O(n^2) constant,
          for the native walk and for Regex.find_all (reference VM, budgeted).

Each row: one untimed warm process, then the median wall time of --runs fresh
processes, C with `--gpu off --threads 1`. Rows land in .tmp/regex/bench-<case>.json.
"""

import argparse
import json
from pathlib import Path
import re
import statistics
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
DEFS = re.split(r"^def main\(", (HERE / "bench.bend").read_text(), flags=re.M)[0]
SPAN = "Maybe<&2, Regex.Span()>"
RESCAN = 'Regex.compile("a.*b|a", "")'


def nat(n):  # a Nat literal expands in unary: compute the big ones
    return "%dn" % n if n < 4096 else "Nat.mul(U32.to_nat(%d), %dn)" % (n // 64, 64)


def build(tmp, name, ty, expr, js):
    src = tmp / (name + ".bend")
    src.write_text("%s\ndef main() -> %s:\n  %s\n" % (DEFS, ty, expr))
    out = tmp / (name + (".js" if js else ""))
    b = subprocess.run(
        ["bun", "bend2/main.ts", str(src), "-o", str(out)],
        cwd=ROOT,
        text=True,
        capture_output=True,
        timeout=300,
    )
    assert b.returncode == 0, b.stdout + b.stderr
    return ["bun", str(out)] if js else [str(out), "--gpu", "off", "--threads", "1"]


def measure(cmd, runs, warm=True):
    times, out = [], None
    for i in range(runs + warm):
        t = time.perf_counter()
        r = subprocess.run(cmd, text=True, capture_output=True, timeout=900)
        dt = time.perf_counter() - t
        assert r.returncode == 0, r.stderr[-2000:]
        assert out in (None, r.stdout), "unstable output"
        out = r.stdout
        if i >= warm:
            times.append(dt)
    return statistics.median(times), out.strip()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--case", default="all", choices=["scan", "doubling", "rescan", "all"]
    )
    ap.add_argument("--runs", type=int, default=7)
    ap.add_argument("--ref-k", type=int, default=1024)
    a = ap.parse_args()
    on = lambda c: a.case in (c, "all")
    K = 16384
    rows = []  # (case, label, lane, n, runs, main type, main expr)
    if on("scan"):
        for lane in ("c", "js"):
            rows.append(
                (
                    "scan",
                    "base",
                    lane,
                    64 * K,
                    a.runs,
                    "Nat",
                    "String.length(text(%s))" % nat(K),
                )
            )
            for i in range(4):
                rows.append(
                    (
                        "scan",
                        "native p%d" % i,
                        lane,
                        64 * K,
                        a.runs,
                        SPAN,
                        "native(pat(%dn), text(%s))" % (i, nat(K)),
                    )
                )
        for i in range(4):
            rows.append(
                (
                    "scan",
                    "reference p%d" % i,
                    "c",
                    64 * a.ref_k,
                    a.runs,
                    SPAN,
                    "reference(pat(%dn), text(%s))" % (i, nat(a.ref_k)),
                )
            )
        rows.append(
            (
                "scan",
                "reference p2",
                "c",
                64 * K,
                1,
                SPAN,
                "reference(pat(2n), text(%s))" % nat(K),
            )
        )
    if on("doubling"):
        for k in (K, 2 * K, 4 * K):
            rows.append(
                (
                    "doubling",
                    "base",
                    "c",
                    64 * k,
                    a.runs,
                    "Nat",
                    "String.length(text(%s))" % nat(k),
                )
            )
            rows.append(
                (
                    "doubling",
                    "native p2",
                    "c",
                    64 * k,
                    a.runs,
                    SPAN,
                    "native(pat(2n), text(%s))" % nat(k),
                )
            )
        for k in (a.ref_k, 2 * a.ref_k, 4 * a.ref_k):
            rows.append(
                (
                    "doubling",
                    "reference p2",
                    "c",
                    64 * k,
                    a.runs,
                    SPAN,
                    "reference(pat(2n), text(%s))" % nat(k),
                )
            )
    if on("rescan"):
        for n in (8192, 16384, 32768):
            rows.append(
                (
                    "rescan",
                    "native walk",
                    "c",
                    n,
                    a.runs,
                    "Nat",
                    "rescan(%s, %s)" % (RESCAN, nat(n)),
                )
            )
        for n in (8192, 16384):
            rows.append(
                (
                    "rescan",
                    "native walk",
                    "js",
                    n,
                    a.runs,
                    "Nat",
                    "rescan(%s, %s)" % (RESCAN, nat(n)),
                )
            )
        for n in (512, 1024, 2048):
            rows.append(
                (
                    "rescan",
                    "find_all (reference)",
                    "c",
                    n,
                    a.runs,
                    "Nat",
                    "rescan.all(%s, %s)" % (RESCAN, nat(n)),
                )
            )
    results = []
    with tempfile.TemporaryDirectory(prefix="bend-regex-bench-") as temp:
        for j, (case, label, lane, n, runs, ty, expr) in enumerate(rows):
            cmd = build(Path(temp), "b%d" % j, ty, expr, lane == "js")
            sec, out = measure(cmd, runs, warm=runs > 1)
            row = dict(
                case=case,
                label=label,
                lane=lane,
                n=n,
                runs=runs,
                median_s=round(sec, 4),
                out=out,
            )
            if case == "rescan":
                assert out == "%dn" % n, (label, n, out)
                row["ns_per_step"] = round(sec * 1e9 / (n * (n + 1) / 2), 3)
            else:
                row["ns_per_cp"] = round(sec * 1e9 / n, 2)
            prev = [
                r
                for r in results
                if (r["case"], r["label"], r["lane"]) == (case, label, lane)
                and r["n"] * 2 == n
            ]
            if prev:
                row["x_vs_half"] = round(sec / prev[-1]["median_s"], 2)
            results.append(row)
            print(json.dumps(row, ensure_ascii=False), flush=True)
    out = HERE.parents[1] / ".tmp/regex"
    out.mkdir(parents=True, exist_ok=True)
    (out / ("bench-%s.json" % a.case)).write_text(
        json.dumps(results, indent=2, ensure_ascii=False) + "\n"
    )


if __name__ == "__main__":
    main()
