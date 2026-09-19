#!/usr/bin/env python3
"""R-lane #1, pass 3: correct row census + cluster savings + real C take-family sizing."""
import re, subprocess, collections

P = "/home/omen/Documents/Project/bend/bend2/comp.ts"
src = open(P, encoding="utf-8").read()
lines = src.splitlines()

def ttok(text):
    r = subprocess.run(["ttok"], input=text, capture_output=True, text=True)
    return int(r.stdout.strip()) if r.returncode == 0 else -1

def balanced(l):
    return l.count("{") == l.count("}")

rowre = re.compile(r'^  ([a-z0-9_]+): (.*)$')
rows = []
i = 0
while i < len(lines):
    m = rowre.match(lines[i])
    if m and 174 <= i + 1 <= 416 and not lines[i].startswith("  ..."):
        name, rest = m.group(1), m.group(2).strip()
        if rest.startswith("{") and not (balanced(lines[i]) and rest.rstrip().endswith("},")):
            blk = [lines[i]]
            j = i + 1
            while j < len(lines):
                blk.append(lines[j])
                if lines[j].rstrip() in ("  },", "  }"):
                    break
                j += 1
            rows.append((i + 1, name, "\n".join(blk)))
            i = j + 1
            continue
        rows.append((i + 1, name, lines[i]))
    i += 1

print(f"OPERATIONS rows (correct): {len(rows)}")
fams = collections.defaultdict(list)
for ln, nm, t in rows:
    fams[nm.split("_")[0]].append((ln, nm, t))
grand = 0
for k, items in sorted(fams.items(), key=lambda x: -len(x[1])):
    tk = ttok("\n".join(t for _, _, t in items))
    grand += tk
    print(f"  {k:8s} {len(items):3d} rows  ttok {tk:5d}")
print(f"  TOTAL: {len(rows)} rows  {grand} ttok")

# clusters n>=2 within families: normalized shape
print("\n== clusters n>=2 (collapse candidates) ==")
est_total = 0
for k, items in sorted(fams.items()):
    sigs = collections.defaultdict(list)
    for ln, nm, t in items:
        body = t.split(":", 1)[1]
        sig = re.sub(r"[A-Za-z0-9_.]+", "X", body)
        sigs[sig].append((ln, nm, t))
    for sig, cl in sigs.items():
        if len(cl) >= 2:
            tk = ttok("\n".join(x[2] for x in cl))
            per = tk / len(cl)
            save = int((len(cl) - 1) * per * 0.55)  # 55% of dup rows recoverable
            est_total += save
            print(f"  {k:8s} x{len(cl):2d} ttok {tk:4d}  est -{save:3d}  [{', '.join(x[1] for x in cl)}]")
print(f"cluster est total: -{est_total} ttok (table-side)")

# real defs of the take family: largest brace-matched candidate per name
print("\n== take-family DEF sizing (largest candidate body) ==")
names = set()
for i, l in enumerate(lines):
    for m in re.finditer(r"\b([a-z0-9_]+_take)\b", l):
        names.add(m.group(1))
defs_total = 0
sizes = []
for n in sorted(names):
    best = (0, -1, -1)
    for occ in [i for i, l in enumerate(lines) if re.search(rf"\b{n}\b", l)]:
        mdef = re.search(rf"^\s*(?:static\s+)?[A-Za-z_][\w \*]*\b{n}\s*\(", lines[occ])
        if not mdef:
            continue
        j = occ
        opened = -1
        while j < min(occ + 6, len(lines)):
            if "{" in lines[j]:
                opened = j
                break
            j += 1
        if opened < 0:
            continue
        depth = 0
        k = opened
        while k < len(lines):
            depth += lines[k].count("{") - lines[k].count("}")
            if depth <= 0 and k > opened:
                break
            k += 1
        seg = "\n".join(lines[opened:k + 1])
        if len(seg) > best[0]:
            best = (len(seg), opened + 1, k + 1, seg)
    if best[0]:
        tk = ttok(best[3])
        defs_total += tk
        sizes.append((tk, n, best[1], best[2]))
sizes.sort(reverse=True)
for tk, n, a, b in sizes[:20]:
    print(f"  {n:24s} lines {a}-{b}  ttok {tk}")
print(f"defs sized: {len(sizes)}, total def ttok: {defs_total}")
takedefs = [s for s in sizes if s[1].split("_")[0] in ("str", "re")]
print(f"str_/re_ defs: {len(takedefs)}, ttok {sum(s[0] for s in takedefs)}")
