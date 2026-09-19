#!/usr/bin/env python3
"""Synthetic service log, deterministic. usage: gen_logs.py OUT [MiB=500]"""
import random, sys

out, mib = sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 500
rng = random.Random(7)
LEVELS = ["INFO"] * 90 + ["WARN"] * 8 + ["ERROR"] * 2
SVC = ["auth", "billing", "search", "gateway", "storage", "mailer"]
MSG = {
    "INFO": ["request served", "cache hit", "session refreshed", "job finished"],
    "WARN": ["slow query", "retrying upstream", "queue depth high"],
    "ERROR": ["upstream timeout", "disk quota exceeded", "null tenant id"],
}
size, n, t = 0, 0, 1_700_000_000
with open(out, "w") as f:
    while size < mib << 20:
        rows = []
        for _ in range(10000):
            n += 1
            t += rng.randint(0, 3)
            lvl = rng.choice(LEVELS)
            rows.append(f"{t} {lvl:5} {rng.choice(SVC)} req={n:08d} "
                        f"{rng.choice(MSG[lvl])} ms={rng.randint(1, 900)}\n")
        chunk = "".join(rows)
        f.write(chunk)
        size += len(chunk)
print(f"{out}: {size} bytes, {n} lines")
