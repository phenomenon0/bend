#!/usr/bin/env python3
"""Self-describing text: record k is the 15-digit number k plus a newline, so
the 16 characters at offset 16*k spell k. usage: gen_records.py OUT [MiB=256]"""
import sys

out, mib = sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 256
n = (mib << 20) // 16
with open(out, "w") as f:
    for lo in range(0, n, 1 << 16):
        f.write("".join(f"{k:015d}\n" for k in range(lo, min(lo + (1 << 16), n))))
print(f"{out}: {n * 16} bytes, {n} records")
