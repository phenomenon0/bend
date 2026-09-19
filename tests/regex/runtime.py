#!/usr/bin/env python3
"""Regex natives under ASan/UBSan with allocation counters, against the reference VM.

Two Bend programs over the same rows: one calls Regex.exec / Regex.match_at (the
native rows of comp.ts), the other Regex.exec.go (the reference Pike VM of base,
which has no native row). Their outputs must be byte-identical on C and on JS.
The C builds run sanitized with every heap_alloc/heap_free tracked (double
alloc, double free, class mismatch assert) and the VM scratch block counted:
one per native call, none live at exit. Rows: a seeded slice of the oracle's
corpus at several `at`, plus forged programs (pcs and slots out of range, self
loops, no IMatch, the empty program) that must die quietly, never fault.
The two big forged operands (2^32, 2^24 - 1) are computed, not written: a Nat
literal expands in unary, and `4294967296n` takes the compiler past 4 GB.
"""

import os
from pathlib import Path
import random
import re
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True  # no __pycache__ in tests/: gates/test.ts copies files only
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from oracle import alt, bend_str, text  # noqa: E402  (the R4 generator, reused)

ROOT = Path(__file__).resolve().parents[2]
PAIRS, GROUP = 240, 10

FORGED = [
    "[]",
    "[IMatch{}]",
    "[IJmp{0n}]",
    "[ISplit{0n, 0n}]",
    "[ISplit{1n, 99n}, IChr{97}, IMatch{}]",
    "[ISave{0n}, ISplit{9n, 2n}, IChr{97}, ISave{7n}, IJmp{1n}, ISave{1n}, IMatch{}]",
    "[ISave{0n}, IAny{}, ISave{1n}, ISave{Nat.mul(U32.to_nat(65536), U32.to_nat(65536))}, IMatch{}]",
    "[ISave{0n}, IAny{}, ISplit{1n, 3n}, ISave{1n}, IMatch{}]",
    "[ISave{0n}, IChr{97}, IJmp{U32.to_nat(16777215)}]",
    "[ISave{1n}, ISet{True{}, []}, ISave{0n}, IMatch{}]",
    "[ISave{0n}, IWordB{False{}}, IBol{True{}}, IEol{False{}}, ISave{1n}, IChr{98}]",
]

HEAD = """import Base

def row(r: Result<&2, &2, Regex.Error, Regex>, +s: String, +at: Nat) -> List<&2, Maybe<&2, Match>>:
  match r:
    case Fail{e}:
      []
    case Done{+re}:
      [%s, %s]
"""
NATIVE = ("Regex.exec(re, s, at)", "Regex.match_at(re, s, at)")
REFERENCE = (
    "Regex.exec.go(re, s, at, False{}, False{}, False{})",
    "Regex.exec.go(re, s, at, False{}, True{}, False{})",
)

TRACK = r"""
#include <assert.h>
#include <stdatomic.h>
#define TRACK_SIZE (1u << 20)
static struct { Loc loc; Cls cls; bool live; } tracked[TRACK_SIZE];
static pthread_mutex_t track_lock = PTHREAD_MUTEX_INITIALIZER;
static atomic_ullong track_allocs, track_frees, track_re_calls, track_re_live;
static u32 track_slot(Loc l) {
  u32 i = (u32)(l * 11400714819323198485ull >> 44);
  while (tracked[i].loc && tracked[i].loc != l) { i = (i + 1) & (TRACK_SIZE - 1); }
  return i;
}
static void track_mark(Loc l, Cls cls, bool live) {
  pthread_mutex_lock(&track_lock);
  u32 i = track_slot(l);
  assert(tracked[i].live != live && (live || tracked[i].cls == cls));
  tracked[i].loc = l; tracked[i].cls = cls; tracked[i].live = live;
  pthread_mutex_unlock(&track_lock);
}
__attribute__((destructor)) static void track_report(void) {
  fprintf(stderr, "track allocs=%llu frees=%llu re_calls=%llu re_live=%llu\n",
    (unsigned long long)track_allocs, (unsigned long long)track_frees,
    (unsigned long long)track_re_calls,
    (unsigned long long)track_re_live);
}
INLINE Loc heap_alloc(Env e, Cls cls) {
  Loc l = heap_alloc_impl(e, cls);
  if (!err_seen(e.mem)) { track_mark(l, cls, true); track_allocs++; }
  return l;
}
"""
FREE = r"""
INLINE void heap_free(Env e, Cls cls, Loc l) {
  if (!err_seen(e.mem)) { track_mark(l, cls, false); track_frees++; }
  heap_free_impl(e, cls, l);
}
"""


def sh(args, **kw):
    return subprocess.run(
        args, cwd=ROOT, text=True, capture_output=True, timeout=900, **kw
    )


def rows():
    r = random.Random(56)
    out = []
    while len(out) < PAIRS:
        p, _ = alt(r, 3)
        f = "".join(c for c in "ims" if r.random() < 0.2)
        s = text(r, p)
        at = r.choice([0, 0, 1, len(s), len(s) + 2, r.randint(0, len(s))])
        out.append(
            "row(Regex.compile(%s, %s), %s, %dn)"
            % (bend_str(p), bend_str(f), bend_str(s), at)
        )
    for prog in FORGED:
        for ng in (0, 1):
            for s, at in (("", 0), ("aab\na", 0), ("aab\na", 2), ("é😀a", 9)):
                out.append(
                    "row(Done{Regex{%s, %dn}}, %s, %dn)" % (prog, ng, bend_str(s), at)
                )
    return out


def program(calls):
    rs = rows()
    parts = [rs[i : i + GROUP] for i in range(0, len(rs), GROUP)]
    src = HEAD % calls
    for k, g in enumerate(parts):
        src += "\ndef part%d() -> List<&2, List<&2, Maybe<&2, Match>>>:\n  [%s]\n" % (
            k,
            ",\n   ".join(g),
        )
    src += (
        "\ndef main() -> List<&2, List<&2, List<&2, Maybe<&2, Match>>>>:\n  [%s]\n"
        % ", ".join("part%d()" % k for k in range(len(parts)))
    )
    return src, len(rs)


def instrument(c):
    def sub(old, new, count=1):
        nonlocal c
        assert c.count(old) == count, (old, c.count(old))
        c = c.replace(old, new)

    sub(
        "INLINE Loc heap_alloc(Env e, Cls cls)",
        "INLINE Loc heap_alloc_impl(Env e, Cls cls)",
    )
    sub(
        "INLINE void heap_free(Env e, Cls cls, Loc loc)",
        TRACK + "\nINLINE void heap_free_impl(Env e, Cls cls, Loc loc)",
    )
    sub("// Spare\n// =====", FREE + "\n// Spare\n// =====")
    sub(
        "  Loc P = err_seen(e.mem) ? 0 : heap_alloc(e, cls);",
        "  Loc P = err_seen(e.mem) ? 0 : heap_alloc(e, cls);"
        " if (!err_seen(e.mem)) { track_re_calls++; track_re_live++; }",
    )
    sub("  str_scratch_free(e, cls, P);", "  str_scratch_free(e, cls, P); track_re_live--;")
    return c


def main():
    cc = os.environ.get("CC", "clang")
    flags = [
        "-std=c11",
        "-O1",
        "-g",
        "-fsanitize=address,undefined",
        "-fno-sanitize-recover=undefined",
        "-fno-omit-frame-pointer",
        # ASan's fake stack (a dynamic alloca) meets the runtime's frames on this
        # many rows: clang dies with "Interference usage of base pointer".
        "-fsanitize-address-use-after-return=never",
    ]
    env = {**os.environ, "ASAN_OPTIONS": "detect_leaks=0"}
    outs = {}
    with tempfile.TemporaryDirectory(prefix="bend-regex-runtime-") as temp:
        tmp = Path(temp)
        for name, calls in (("native", NATIVE), ("reference", REFERENCE)):
            src, count = program(calls)
            bend = tmp / (name + ".bend")
            bend.write_text(src)
            cfile, jsfile, binary = (
                tmp / (name + ".c"),
                tmp / (name + ".js"),
                tmp / name,
            )
            for out in (cfile, jsfile):
                b = sh(["bun", "bend2/main.ts", str(bend), "-o", str(out)])
                assert b.returncode == 0, b.stdout + b.stderr
            c = cfile.read_text()
            uses = len(re.findall(r"\bre_exec_take\(e,", c))
            assert (uses > 0) == (name == "native"), (name, uses)
            assert bool(re.search(r"\bre_exec\(re_\d", jsfile.read_text())) == (name == "native"), name
            cfile.write_text(instrument(c))
            b = sh([cc, *flags, str(cfile), "-lpthread", "-lm", "-o", str(binary)])
            assert b.returncode == 0, b.stderr[-4000:]
            for threads in ("1", "8"):
                run = sh([str(binary), "--gpu", "off", "--threads", threads], env=env)
                assert run.returncode == 0 and "runtime error" not in run.stderr, (
                    run.stderr[-4000:]
                )
                m = re.search(
                    r"track allocs=(\d+) frees=(\d+) re_calls=(\d+) re_live=(\d+)", run.stderr
                )
                assert m, run.stderr[-2000:]
                allocs, frees, calls_n, live = map(int, m.groups())
                assert live == 0, (name, threads, live)
                assert calls_n == (2 * count if name == "native" else 0), (
                    name,
                    calls_n,
                    count,
                )
                # What outlives the run is main's printed result alone: the same
                # cells whichever VM made them.
                assert outs.setdefault("kept", allocs - frees) == allocs - frees, (
                    name,
                    threads,
                    allocs - frees,
                )
                assert outs.setdefault("c", run.stdout) == run.stdout, (
                    name,
                    threads,
                    "c parity",
                )
                print(
                    "%-9s c  --threads %s: ASan/UBSan clean, %d tracked allocs, %d kept (the result), %d VM scratch blocks, 0 live"
                    % (name, threads, allocs, allocs - frees, calls_n),
                    flush=True,
                )
            run = sh(["bun", str(jsfile)])
            assert run.returncode == 0, run.stderr[-4000:]
            assert outs["c"] == run.stdout, (name, "js parity")
            print("%-9s js: byte-identical" % name, flush=True)
        print(
            "Regex runtime: ok (%d rows x exec + match_at, %d forged; native == reference on C and JS)"
            % (count, len(FORGED) * 8)
        )


if __name__ == "__main__":
    main()
