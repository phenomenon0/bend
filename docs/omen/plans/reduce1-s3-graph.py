#!/usr/bin/env python3
"""R-lane #1 S3: base.bend usage graph. Orphan = def unreachable from any root.
Roots (conservative): every name mentioned in any tracked file outside base.bend
(.bend/.ts/.md/.lean/.typ/.c/.js/.py/.sh), every def whose name ends in a
".suffix" literal of bend.ts (type-directed operators), every OPERATIONS-named
def is NOT special (an intrinsic nobody calls is still dead). Laws: see --laws."""
import re, subprocess, sys, collections
BASE = "bend2/base.bend"
LAWS_ARE_ROOTS = "--laws" in sys.argv
src = open(BASE, encoding="utf-8").read()
NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z0-9_]+)*")
def refs(text):
    out = set()
    for t in NAME.findall(text):
        parts = t.split(".")
        for i in range(1, len(parts) + 1):
            out.add(".".join(parts[:i]))
    return out
# top-level blocks
heads = [(m.start(), m.group(1), m.group(2)) for m in
         re.finditer(r"^(def|law|type) ([A-Za-z0-9_.]+)", src, re.M)]
blocks = {}
kind = {}
for i, (pos, k, n) in enumerate(heads):
    end = heads[i + 1][0] if i + 1 < len(heads) else len(src)
    blocks[n] = blocks.get(n, "") + src[pos:end]   # law+def may share a name
    kind.setdefault(n, set()).add(k)
strip = lambda b: re.sub(r"#.*", "", b)
graph = {n: (refs(strip(b)) & blocks.keys()) - {n} for n, b in blocks.items()}
# constructors introduce their type
files = subprocess.run(["git", "ls-files"], capture_output=True, text=True).stdout.split("\n")
ext = (".bend", ".ts", ".md", ".lean", ".typ", ".c", ".js", ".py", ".sh", ".html")
roots = set()
for f in files:
    if f == BASE or not f.endswith(ext) or f.startswith("docs/omen/"): continue
    try: roots |= refs(open(f, encoding="utf-8", errors="ignore").read()) & blocks.keys()
    except OSError: pass
sufs = set(re.findall(r'"(\.[a-z_0-9]+)"', open("bend2/bend.ts").read()))
roots |= {n for n in blocks if any(n.endswith(s) for s in sufs)}
if LAWS_ARE_ROOTS: roots |= {n for n in blocks if "law" in kind[n]}
live, todo = set(), list(roots)
while todo:
    n = todo.pop()
    if n in live: continue
    live.add(n); todo += graph[n]
dead = [n for n in blocks if n not in live]
def ttok(t):
    return int(subprocess.run(["ttok"], input=t, capture_output=True, text=True).stdout.strip())
rows = sorted(((ttok(blocks[n]), n, "+".join(sorted(kind[n]))) for n in dead), reverse=True)
fam = collections.Counter()
for t, n, k in rows: fam[n.split(".")[0]] += t
print(f"blocks {len(blocks)}  roots {len(roots)}  live {len(live)}  dead {len(dead)}  "
      f"dead ttok {sum(r[0] for r in rows)}  (laws are roots: {LAWS_ARE_ROOTS})")
print("by family:", dict(fam.most_common()))
for t, n, k in rows: print(f"{t:6d}  {k:8s} {n}")
