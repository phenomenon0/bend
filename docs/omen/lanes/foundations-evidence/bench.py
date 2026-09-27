#!/usr/bin/env python3
"""Reproduce the bulk-copy candidate and contiguous-ring counterfactual.

Run from any directory; stdout is JSONL with every sample and load average.
Only temporary emitted C is changed. No fast-math, march, or repo edits.
"""

import fcntl
import json
import os
from pathlib import Path
import statistics
import subprocess
import tempfile
import time

REPO = Path(__file__).resolve().parents[4]
ENV = {**os.environ, "BEND_NO_TELEMETRY": "1"}
FAST = """#if !DEVICE
  // Fresh blocks cannot overlap; keep leaf-sized copies inline.
  if (!keep && n >= 16) {
    memcpy(e.mem + dst, e.mem + src, n * sizeof(Term));
    return;
  }
#endif
"""
CLONE = """import Base

def read(r: Array<U32> & U32) -> U32:
  (a, x) = r
  x

def next(k: U32 -> Array<U32> -> U32, +s: U32, r: Array<U32> & Array<U32>) -> U32:
  (a, b) = r
  k(U32.add(s, read(Array.get(U32, b, s))), a)

def loop(fuel: Nat, +s: U32, a: Array<U32>) -> U32:
  match fuel:
    case 0n:
      s
    case 1n++k:
      next(s => a => loop(k, s, a), s, Array.clone(U32, a))

def main() -> U32:
  loop(REPSn, 0, Array.new(U32, DEPTHn, 7))
"""
SUM = """def sum(a: Array<U32>) -> U32:
  match a:
    case ALeaf{x}:
      x
    case ANode{l, r}:
      U32.add(sum(l), sum(r))

"""


def run(args):
    return subprocess.check_output(args, cwd=REPO, env=ENV, timeout=180)


def emit(source, c):
    run(["bun", "bend2/main.ts", str(source), "-o", str(c)])
    return c.read_text()


def build(path, text):
    path.with_suffix(".c").write_text(text)
    run(
        [
            "clang",
            "-std=c11",
            "-O3",
            "-ffp-contract=off",
            str(path.with_suffix(".c")),
            "-lpthread",
            "-lm",
            "-o",
            str(path),
        ]
    )
    return path


def measure(name, binaries, want, threads=1):
    samples = {label: [] for label in binaries}
    loads = []
    with open("/tmp/bend-bench.lock", "w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        for rep in range(9):
            labels = list(binaries)
            if rep % 2:
                labels.reverse()
            for label in labels:
                loads.append({"variant": label, "load": os.getloadavg()})
                start = time.perf_counter()
                got = run(
                    [str(binaries[label]), "--threads", str(threads), "--gpu", "off"]
                )
                samples[label].append(time.perf_counter() - start)
                assert got == want, (name, label, got, want)
    print(
        json.dumps(
            {
                "bench": name,
                "threads": threads,
                "median": {k: statistics.median(v) for k, v in samples.items()},
                "seconds": samples,
                "loads": loads,
            }
        ),
        flush=True,
    )


with tempfile.TemporaryDirectory(prefix="bend-foundations-") as work:
    work = Path(work)
    for name, depth, reps, tree in [
        ("clone-1m", 18, 8192, False),
        ("clone-8k", 11, 131072, False),
        ("clone-16", 2, 4194304, False),
        ("tree", 11, 4096, True),
    ]:
        source = CLONE.replace("REPS", str(reps)).replace("DEPTH", str(depth))
        want = reps * 7
        if tree:
            source = source.replace("def read(", SUM + "def read(")
            source = source.replace("read(Array.get(U32, b, s))", "sum(b)")
            want *= 1 << depth
        bend = work / (name + ".bend")
        bend.write_text(source + "\n#|" + str(want) + "\n")
        after = emit(bend, work / (name + ".c"))
        assert after.count(FAST) == 1, "candidate block changed; review ablation"
        before = after.replace(FAST, "")
        variants = {
            "before": build(work / (name + "-before"), before),
            "candidate": build(work / (name + "-after"), after),
        }
        measure(name, variants, (str(want) + "\n").encode())

    current = emit(REPO / "tests/power/bench/gemv_par.bend", work / "par.c")
    old = """        u32  step = CUBE_T / LINE;
        Ring row  = r / step * CUBE_T;
        for (Ring rg = row + r % step; rg < row + CUBE_T; rg += step) {"""
    assert current.count(old) == 1, "scheduler changed; review counterfactual"
    contiguous = current.replace(
        old,
        """        for (u32 i = 0; i < LINE; i++) {
          Ring rg = r * LINE + i;""",
    )
    variants = {
        "striped": build(work / "striped", current),
        "contiguous": build(work / "contiguous", contiguous),
    }
    twin = work / "twin"
    run(
        [
            "clang",
            "-std=c11",
            "-O3",
            "-ffp-contract=off",
            str(REPO / "tests/power/bench/twin_gemv_par.c"),
            "-lm",
            "-o",
            str(twin),
        ]
    )
    want = run([str(twin)])
    for threads in (1, 2, 4, 8, 16):
        measure("gemv-par", variants, want, threads)
