#!/usr/bin/env python3
# The oracle for probe.bend: prints the whole fixture. It builds the table.
# Keys 0..n-1 are inserted one by one with linear probing into a list of M
# slots; displacement is counted per key. The carries across slot boundaries
# come from each key's own (home, displacement) span, not from a recurrence.
# Unsuccessful-search probes are walked slot by slot to the next empty one.
# Knuth's asymptotic means are the same double arithmetic probe.bend does.
import math
import sys


def params(b, d):
    mask = (1 << d) - 1
    return mask, (0x9E3779B1 & mask) | 1, (0x85EBCA6B & mask) | 1


def h(k, b, d):
    mask, c1, c2 = params(b, d)
    x = (k ^ (k >> 11)) & mask
    x = (x * c1) & mask
    x = (x ^ (x >> 9)) & mask
    x = (x * c2) & mask
    return (x ^ (x >> 13)) & mask


def fmt(x):  # floor to 4 decimals, as probe.bend's fmt
    v = math.floor(x * 10000.0)
    return f"{v // 10000}.{v % 10000:04d}"


def line(b, d, pct):
    m = 1 << b
    n = m * pct // 100
    table = [-1] * m
    disp, cross = 0, [0] * (m + 1)
    for k in range(n):
        home = h(k, b, d) >> (d - b)
        j = 0
        while table[(home + j) % m] != -1:
            j += 1
        table[(home + j) % m] = k
        disp += j
        # the key crosses boundaries home .. home+j-1 (cyclically)
        if home + j <= m:
            cross[home] += 1
            cross[home + j] -= 1
        else:
            cross[home] += 1
            cross[m] -= 1
            cross[0] += 1
            cross[home + j - m] -= 1
    run, carry, maxc = 0, 0, 0
    for i in range(m):
        run += cross[i]
        maxc = max(maxc, run)
    unsucc = 0
    for s in range(m):
        j = 0
        while table[(s + j) % m] != -1:
            j += 1
        unsucc += j
    a = n / m
    ks = 0.5 * (1.0 + 1.0 / (1.0 - a))
    ku = 0.5 * (1.0 + 1.0 / ((1.0 - a) * (1.0 - a)))
    return (f"M=2^{b} n={n} disp={disp} maxcarry={maxc} runs={unsucc} | hit {fmt(1.0 + disp / n)}"
            f" knuth {fmt(ks)} | miss {fmt(1.0 + unsucc / m)} knuth {fmt(ku)} | depths 0 4 9: same")


CASES = [(12, 16, 50), (14, 18, 75), (14, 18, 90), (16, 20, 85)]

if __name__ == "__main__":
    for c in CASES:
        out = line(*c)
        print("#|" + out if "--fixture" in sys.argv else out)
