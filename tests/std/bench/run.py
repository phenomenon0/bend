#!/usr/bin/env python3
# std's benches: a CSV of MB megabytes (tests/power/bench/csv/gen.py's),
# a JSON file (a generated array of GitHub-archive-shaped events unless
# --json names one), and a gzip member (the CSV's first --gz bytes at level
# 6), each through csv_read.bend, json_read.bend and gunzip.bend. Every
# answer is held to CPython's before a time is kept; medians of three
# runs, in CPU seconds (the C lane on one thread).
#
#   python3 tests/std/bench/run.py [--bend path/to/bend2/main.ts] [--packed]
#     [--mb 10 | --csv FILE] [--json FILE | --events 20000] [--gz 30000] [--lanes c,js]
#
# --bend runs another checkout's compiler (released Bend's, say) over a copy
# of this std/; --packed switches the copy's std/bytes.bend to
# bytes_packed.bend (this repo's runtime only).
import csv
import gzip
import json
import os
import random
import resource
import shutil
import statistics
import subprocess
import sys
import tempfile
import zlib

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))


def arg(name, default):
  return sys.argv[sys.argv.index(name) + 1] if name in sys.argv else default


BEND = arg("--bend", os.path.join(ROOT, "bend2", "main.ts"))
MB = int(arg("--mb", "10"))
GZ = int(arg("--gz", "30000"))
EVENTS = int(arg("--events", "20000"))
LANES = arg("--lanes", "c").split(",")


def events(n):
  rng = random.Random(1952)
  kinds = ["PushEvent", "CreateEvent", "WatchEvent", "IssuesEvent", "ForkEvent"]
  out = []
  for i in range(n):
    out.append({"id": str(2489651045 + i), "type": rng.choice(kinds),
      "actor": {"id": rng.randrange(10 ** 7), "login": "user%d" % rng.randrange(5000),
        "gravatar_id": "", "url": "https://api.github.com/users/u%d" % i},
      "repo": {"id": rng.randrange(10 ** 8), "name": "org/repo-%d" % rng.randrange(900)},
      "payload": {"size": rng.randrange(5), "ref": "refs/heads/main",
        "commits": [{"sha": "%040x" % rng.getrandbits(160), "message": "fix été #%d\n\"q\"" % j,
          "distinct": True} for j in range(rng.randrange(3))]},
      "public": True, "created_at": "2015-01-01T15:%02d:%02dZ" % (i // 60 % 60, i % 60)})
  return out


# the child's CPU seconds (user and system): on a shared box, what the
# program cost and not what the other tenants did to the wall clock
def median_run(cmd):
  times, outs = [], set()
  for _ in range(3):
    a = resource.getrusage(resource.RUSAGE_CHILDREN)
    r = subprocess.run(cmd, capture_output=True, text=True)
    b = resource.getrusage(resource.RUSAGE_CHILDREN)
    times.append(b.ru_utime - a.ru_utime + b.ru_stime - a.ru_stime)
    outs.add(r.stdout.strip() + (" exit %d" % r.returncode if r.returncode else ""))
  assert len(outs) == 1, outs
  return statistics.median(times), outs.pop()


def main():
  work = tempfile.mkdtemp(prefix="bend-std-bench.")
  env = dict(os.environ, BEND_NO_TELEMETRY="1")
  shutil.copytree(os.path.join(ROOT, "std"), os.path.join(work, "std"))
  shutil.copytree(os.path.join(ROOT, "tests", "std", "bench"), os.path.join(work, "tests", "std", "bench"))
  if "--packed" in sys.argv:
    by = os.path.join(work, "std", "bytes.bend")
    src = open(by).read()
    open(by, "w").write(src.replace("import ./bytes_list.bend as Impl",
      "import ./bytes_packed.bend as Impl"))
  data = arg("--csv", None)
  if data is None:
    data = os.path.join(work, "bench.csv")
    subprocess.run([sys.executable, os.path.join(ROOT, "tests", "power", "bench", "csv", "gen.py"), data,
      str(MB)], check=True, capture_output=True)
  rows = list(csv.reader(open(data, newline="", encoding="latin-1"), strict=True))
  want_csv = "%d %d %d" % (len(rows), sum(len(r) for r in rows), sum(len(x) for r in rows for x in r))
  jpath = arg("--json", None)
  if jpath is None:
    jpath = os.path.join(work, "events.json")
    json.dump(events(EVENTS), open(jpath, "w"))
  doc = json.load(open(jpath, encoding="utf-8"))
  first = json.dumps(doc[0]["actor"]["login"], ensure_ascii=False)
  want_json = "%d items, %d PushEvent, first login %s" % (len(doc),
    sum(1 for x in doc if x.get("type") == "PushEvent"), first)
  raw = open(data, "rb").read()[:GZ]
  gz = os.path.join(work, "bench.csv.gz")
  open(gz, "wb").write(gzip.compress(raw, 6, mtime=0))
  want_gz = "%d bytes, crc32 %d" % (len(raw), zlib.crc32(raw))
  benches = [("csv", "csv_read", data, want_csv), ("json", "json_read", jpath, want_json),
    ("gunzip", "gunzip", gz, want_gz)]
  print("bend %s%s, %s" % (BEND, " (packed)" if "--packed" in sys.argv else " (list)",
    open("/proc/loadavg").read().split()[0] + " load"))
  print("%-8s %-4s %10s %9s %12s  %s" % ("bench", "lane", "bytes", "cpu s", "MB/s", "answer"))
  for name, prog, path, want in benches:
    for lane in LANES:
      out = os.path.join(work, prog + (".js" if lane == "js" else ""))
      b = subprocess.run(["bun", BEND, os.path.join("tests", "std", "bench", prog + ".bend"), "-o", out],
        cwd=work, env=env, capture_output=True, text=True)
      assert b.returncode == 0, (prog, lane, b.stdout + b.stderr)
      cmd = (["bun", out] if lane == "js" else [out, "--threads", "1"]) + [path]
      sec, got = median_run(cmd)
      assert got == want, (name, lane, got, want)
      size = os.path.getsize(path) if name != "gunzip" else len(raw)
      print("%-8s %-4s %10d %9.2f %12.3f  %s" % (name, lane, size, sec, size / 1e6 / sec, got))
  shutil.rmtree(work)


main()
