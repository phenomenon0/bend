#!/usr/bin/env python3
# std/README.md's snippets are the examples' own text: every ```bend block
# must occur, byte for byte, in the std/examples/*.bend file the README
# names last before the block. Then each example runs (its #| lines are its
# expected output) with the bend given, from a copy of std/ at a scratch
# root, as a user's checkout would hold it:
#
#   python3 tests/std/readme.py [--bend path/to/bend2/main.ts] [--packed] [--lanes interp,js,c]
import os
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
BEND = sys.argv[sys.argv.index("--bend") + 1] if "--bend" in sys.argv else os.path.join(ROOT, "bend2", "main.ts")
LANES = (sys.argv[sys.argv.index("--lanes") + 1] if "--lanes" in sys.argv else "interp,js,c").split(",")


def snippets():
  text = open(os.path.join(ROOT, "std", "README.md")).read()
  bad = 0
  n = 0
  for m in re.finditer(r"```bend\n(.*?)```", text, re.S):
    names = re.findall(r"std/examples/([a-z_]+\.bend)", text[:m.start()])
    if not names:
      print("NO FILE  block at %d" % m.start()); bad += 1; continue
    src = open(os.path.join(ROOT, "std", "examples", names[-1])).read()
    n += 1
    if m.group(1) not in src:
      print("NOT VERBATIM  a block of %s" % names[-1]); bad += 1
  print("snippets: %d / %d verbatim" % (n - bad, n))
  return bad


def run(work, name, lane, env):
  f = os.path.join("std", "examples", name)
  want = "".join(l[2:] for l in open(os.path.join(work, f)) if l.startswith("#|")).rstrip()
  if lane == "interp":
    r = subprocess.run(["bun", BEND, f], cwd=work, capture_output=True, text=True, env=env)
  else:
    out = os.path.join(work, "ex" + (".js" if lane == "js" else ""))
    b = subprocess.run(["bun", BEND, f, "-o", out], cwd=work, capture_output=True, text=True, env=env)
    if b.returncode != 0:
      return False
    r = subprocess.run((["bun", out] if lane == "js" else [out]), cwd=work, capture_output=True, text=True,
      env=env)
  got = "\n".join(l.rstrip() for l in r.stdout.rstrip().split("\n"))
  return got == "\n".join(l.rstrip() for l in want.split("\n"))


def main():
  bad = snippets()
  work = tempfile.mkdtemp(prefix="bend-std-readme.")
  shutil.copytree(os.path.join(ROOT, "std"), os.path.join(work, "std"))
  if "--packed" in sys.argv:
    by = os.path.join(work, "std", "bytes.bend")
    open(by, "w").write(open(by).read().replace("import ./bytes_list.bend as Impl",
      "import ./bytes_packed.bend as Impl"))
  env = dict(os.environ, BEND_NO_TELEMETRY="1")
  for name in sorted(os.listdir(os.path.join(work, "std", "examples"))):
    if not name.endswith(".bend"):
      continue
    res = ["%s:%s" % (l, "ok" if run(work, name, l, env) else "FAIL") for l in LANES]
    bad += sum(1 for r in res if r.endswith("FAIL"))
    print("%-18s %s" % (name, " ".join(res)))
  shutil.rmtree(work)
  sys.exit(1 if bad else 0)


main()
