#!/usr/bin/env python3
# The oracle for kulisch.bend: prints the whole fixture. The data is rebuilt
# from the same rule (Threefry2x32-20 from the Random123 paper, held to its
# known-answer vectors). The exact answer is found without any accumulator:
# the true sum is a Fraction, and the printed F32 is picked among a handful of
# candidates by exact distance, ties to the even significand -- a search whose
# result can be checked by eye, not a second copy of the rounding logic.
# The naive sums use CPython doubles rounded to F32 after every add: for + on
# two F32s that double rounding is exact (53 >= 2*24 + 2), so it IS F32 add.
import struct
import sys
from fractions import Fraction

M = 0xFFFFFFFF
ROT = [13, 15, 26, 6, 17, 29, 16, 24]


def rotl(x, r):
    return ((x << r) | (x >> (32 - r))) & M


def block(k0, k1, c0, c1):
    ks = [k0, k1, k0 ^ k1 ^ 0x1BD11BDA]
    a, b = (c0 + ks[0]) & M, (c1 + ks[1]) & M
    for r in range(20):
        a = (a + b) & M
        b = rotl(b, ROT[r % 8]) ^ a
        if r % 4 == 3:
            n = r // 4 + 1
            a = (a + ks[n % 3]) & M
            b = (b + ks[(n + 1) % 3] + n) & M
    return a, b


for k, c, want in [
    ((0, 0), (0, 0), (0x6B200159, 0x99BA4EFE)),
    ((M, M), (M, M), (0x1CB996FC, 0xBB002BE7)),
    ((0x13198A2E, 0x03707344), (0x243F6A88, 0x85A308D3), (0xC4923A9C, 0x483DF7A0)),
]:
    assert block(*k, *c) == want


def u32(seed, stream, i):
    return block(seed, stream, i, 0)[0]


def bits(s, e, f):
    return (s << 31) | (e << 23) | (f & 0x7FFFFF)


def draw(seed, i):
    k = i & 1023
    if k == 0:
        r = u32(seed, 1, i)
        return bits(0, 193 + ((r >> 23) & 15), r)
    if k == 512:
        return draw(seed, i - 512) ^ 0x80000000
    r = u32(seed, 2, i)
    return bits(r >> 31, 0 if i % 97 == 0 else 77 + ((r >> 23) & 255) % 39, r)


def f32(b):
    return struct.unpack("<f", struct.pack("<I", b))[0]


def b32(x):
    return struct.unpack("<I", struct.pack("<f", x))[0]


def naive(xs):
    acc = 0.0
    for x in xs:
        acc = f32(b32(acc + x))
    return acc


def tree(d, xs):
    if d == 0:
        return naive(xs)
    h = len(xs) // 2
    return f32(b32(tree(d - 1, xs[:h]) + tree(d - 1, xs[h:])))


def nearest(r):
    """The F32 nearest the rational r, ties to even, by exact comparison."""
    if abs(r) >= 2**128 - 2**103:  # at or past max + half an ulp: overflow
        return 0x7F800000 | (0x80000000 if r < 0 else 0)
    guess = b32(float(r)) if abs(r) < 2**127 else 0x7F7FFFFF | (0x80000000 if r < 0 else 0)
    cands = [b for b in {guess - 1, guess, guess + 1, guess ^ 0x80000000}
             if 0 <= b <= M and (b & 0x7F800000) != 0x7F800000]
    best = min(cands, key=lambda b: (abs(Fraction(f32(b)) - r), b & 1))
    return best & 0x7FFFFFFF if r == 0 else best


def line(name, seed, n):
    bs = [draw(seed, i) for i in range(n)]
    xs = [f32(b) for b in bs]
    true = sum(Fraction(x) for x in xs)
    ex = nearest(true)
    # the certificate, stated once more: no F32 is strictly closer
    for other in (ex - 1, ex + 1):
        assert abs(Fraction(f32(other)) - true) >= abs(Fraction(f32(ex)) - true)
    h = lambda v: "0x%08x" % v
    return (f"{name} n={n} exact={h(ex)} naive seq={h(b32(naive(xs)))} "
            f"tree3={h(b32(tree(3, xs)))} tree7={h(b32(tree(7, xs)))} | exact at 0 3 7 12: same")


EDGES = [  # the same lists kulisch.bend folds, as F32 bits
    [1065353216, 864026624], [1065353217, 864026624], [1065353216, 864026624, 1],
    [1065353215, 855638016], [2139095039, 2139095039],
    [4286578687, 4286578687, 2139095039], [1, 1, 3], [1065353216, 3212836864],
    [1904214016, 2373976064],
]


def edges():
    return "edges: " + " ".join("0x%08x" % nearest(sum(Fraction(f32(b)) for b in xs))
                                for xs in EDGES)


CASES = [("s1", 1, 4096), ("s2", 2, 5000), ("s3", 3, 16384)]

if __name__ == "__main__":
    for c in CASES:
        out = line(*c)
        print("#|" + out if "--fixture" in sys.argv else out)
    print(("#|" if "--fixture" in sys.argv else "") + edges())
