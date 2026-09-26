#!/usr/bin/env python3
# Every tests/std/*.bend in each lane -- the check, the interpreter, JS
# (bun) and C -- against its #| lines, from a copy of std/ and tests/std/
# at a scratch root, with the bend given: this repo's (the gate runs the
# same tests on the cluster), or another checkout's, as released Bend's:
#
#   python3 tests/std/lanes.py [--bend path/to/bend2/main.ts] [--packed] [--lanes check,interp,js,c] [NAME...]
import os
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
ARGS = sys.argv[1:]


def opt(name, default):
  if name in ARGS:
    i = ARGS.index(name)
    v = ARGS[i + 1]
    del ARGS[i:i + 2]
    return v
  return default


BEND = opt("--bend", os.path.join(ROOT, "bend2", "main.ts"))
LANES = opt("--lanes", "check,interp,js,c").split(",")
PACKED = "--packed" in ARGS
NAMES = [a for a in ARGS if not a.startswith("--")]


def tidy(s):
  return "\n".join(l.rstrip() for l in s.strip().split("\n"))


def lane(work, f, l, env):
  t = time.time()
  if l == "check":
    r = subprocess.run(["bun", BEND, f, "--check-only"], cwd=work, capture_output=True, text=True, env=env)
    out = r.stdout + r.stderr
    ok = "All terms check." in out or ("TODOs found" in out and "\nError:\n" not in out)
    return ok, time.time() - t, out
  if l == "interp":
    r = subprocess.run(["bun", BEND, f], cwd=work, capture_output=True, text=True, env=env)
  else:
    out = os.path.join(work, "t" + (".js" if l == "js" else ""))
    b = subprocess.run(["bun", BEND, f, "-o", out], cwd=work, capture_output=True, text=True, env=env)
    if b.returncode != 0:
      return False, time.time() - t, b.stdout + b.stderr
    t = time.time()
    r = subprocess.run(["bun", out] if l == "js" else [out], cwd=work, capture_output=True, text=True,
      env=env)
  want = "".join(x[2:] for x in open(os.path.join(work, f)) if x.startswith("#|"))
  got = r.stdout + r.stderr
  return tidy(got) == tidy(want), time.time() - t, got


def main():
  work = tempfile.mkdtemp(prefix="bend-std-lanes.")
  shutil.copytree(os.path.join(ROOT, "std"), os.path.join(work, "std"))
  shutil.copytree(os.path.join(ROOT, "tests", "std"), os.path.join(work, "tests", "std"))
  if PACKED:
    by = os.path.join(work, "std", "bytes.bend")
    src = open(by).read()
    open(by, "w").write(src.replace("import ./bytes_list.bend as Impl",
      "import ./bytes_packed.bend as Impl"))
  env = dict(os.environ, BEND_NO_TELEMETRY="1")
  names = NAMES or sorted(f[:-5] for f in os.listdir(os.path.join(work, "tests", "std")) if f.endswith(".bend"))
  bad = 0
  for n in names:
    f = os.path.join("tests", "std", n + ".bend")
    res = []
    for l in LANES:
      ok, sec, out = lane(work, f, l, env)
      res.append("%s:%s(%.1fs)" % (l, "ok" if ok else "FAIL", sec))
      if not ok:
        bad += 1
        print("--- %s %s\n%s" % (n, l, out[:600]))
    print("%-12s %s" % (n, " ".join(res)))
    sys.stdout.flush()
  shutil.rmtree(work)
  sys.exit(1 if bad else 0)


main()
