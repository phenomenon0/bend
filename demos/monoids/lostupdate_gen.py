#!/usr/bin/env python3
# The oracle for lostupdate.bend: prints the whole fixture. It does not
# enumerate schedules. It counts them by dynamic programming over the machine
# state (each thread's program counter and register, and x), which is a
# different algorithm from the fork tree's unrank-and-walk, and it agrees with
# the closed forms: C(4n, 2n) schedules in all, C(2n, n) of them correct.
import sys
from functools import lru_cache
from math import comb


def census(n):
    @lru_cache(None)
    def go(pa, pb, ra, rb, x):
        if pa == 2 * n and pb == 2 * n:
            return {x: 1}
        out = {}
        for t in (0, 1):
            p = (pa, pb)[t]
            if p == 2 * n:
                continue
            r = [ra, rb]
            nx = x
            if p % 2 == 0:
                r[t] = x  # LOAD
            else:
                nx = r[t] + 1  # STORE
            sub = go(pa + (t == 0), pb + (t == 1), r[0], r[1], nx)
            for k, v in sub.items():
                out[k] = out.get(k, 0) + v
        return out

    return go(0, 0, 0, 0, 0)


def line(n):
    h = census(n)
    assert sum(h.values()) == comb(4 * n, 2 * n) and h[2 * n] == comb(2 * n, n)
    lo = min(h)
    hist = " ".join(f"{x}:{h[x]}" for x in sorted(h))
    return (f"n={n} schedules={sum(h.values())} min={lo} x{h[lo]} correct={h[2 * n]} "
            f"| {hist} | depths 0 5 11: same")


NS = [2, 3, 4, 5, 6]

if __name__ == "__main__":
    for n in NS:
        out = line(n)
        print("#|" + out if "--fixture" in sys.argv else out)
