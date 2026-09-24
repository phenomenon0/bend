#!/usr/bin/env python3
# The reference for demos/mesh/option: a European call under Black-Scholes by
# Monte Carlo, written op for op as option.bend and option_twin.c do it, so
# all three print the same accumulator bits. Every floating operation is one
# of IEEE's correctly rounded five (+ - * / sqrt) or floor; exp and log are
# built from them here, because libm's differ between machines and a
# "reproducible" Monte Carlo that calls libm is reproducible on one box only.
#
#   python3 option_ref.py N          the accumulators for paths 0..N-1
#   python3 option_ref.py --bs       the closed-form price (the accuracy check)
import math
import sys

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


assert block(0, 0, 0, 0) == (0x6B200159, 0x99BA4EFE)

S0, K, R, SIG, T = 100.0, 105.0, 0.05, 0.2, 1.0
LN2_HI = 6.93147180369123816490e-01
LN2_LO = 1.90821492927058770002e-10
INV_LN2 = 1.44269504088896338700e+00
SQRT2 = 1.4142135623730951
TWO32 = 4294967296.0


def fact(n):
    f = 1.0
    for i in range(2, n + 1):
        f = f * float(i)
    return f


def exp_(x):
    k = math.floor(x * INV_LN2 + 0.5)
    r = (x - k * LN2_HI) - k * LN2_LO
    p = 1.0 / fact(13)
    for n in range(12, -1, -1):
        p = p * r + 1.0 / fact(n)
    s = 2.0 if k > 0 else 0.5
    for _ in range(int(abs(k))):
        p = p * s
    return p


def log_(y):
    """y in (0, 1]"""
    e = 0.0
    for _ in range(80):
        if y < 1.0:
            y = y * 2.0
            e = e - 1.0
    if y > SQRT2:
        y = y * 0.5
        e = e + 1.0
    t = (y - 1.0) / (y + 1.0)
    t2 = t * t
    q = 1.0 / 25.0
    for k in range(11, -1, -1):
        q = q * t2 + 1.0 / float(2 * k + 1)
    return e * LN2_HI + (e * LN2_LO + 2.0 * t * q)


def unit(w):
    return 2.0 * ((float(w) + 0.5) / TWO32) - 1.0


def normal(seed, i):
    """Marsaglia's polar method on block(seed, i, j, 0), j = 0, 1, ...: 16
    tries (all rejected: p ~ 2e-11 per path), then 0"""
    for j in range(16):
        a, b = block(seed, i, j, 0)
        u, v = unit(a), unit(b)
        s = u * u + v * v
        if 0.0 < s < 1.0:
            return u * math.sqrt((-2.0 * log_(s)) / s)
    return 0.0


MU = (R - 0.5 * SIG * SIG) * T
SD = SIG * math.sqrt(T)


def payoff(seed, i):
    st = S0 * exp_(MU + SD * normal(seed, i))
    return st - K if st > K else 0.0


def acc(seed, lo, n):
    """sum of floor(pay * 2^32) and of floor(pay^2 * 2^16), as integers"""
    s1 = s2 = 0
    for i in range(lo, lo + n):
        p = payoff(seed, i)
        s1 += int(math.floor(p * TWO32))
        s2 += int(math.floor(p * p * 65536.0))
    return s1, s2


def words(s1, s2):
    return [(s1 >> (32 * j)) & M for j in range(3)] + [(s2 >> (32 * j)) & M for j in range(3)]


def price(s1, s2, n):
    disc = math.exp(-R * T)
    mean = s1 / 2**32 / n
    var = s2 / 2**16 / n - mean * mean
    return disc * mean, disc * math.sqrt(max(var, 0.0) / n)


def bs():
    d1 = (math.log(S0 / K) + (R + 0.5 * SIG * SIG) * T) / (SIG * math.sqrt(T))
    d2 = d1 - SIG * math.sqrt(T)
    N = lambda x: 0.5 * (1 + math.erf(x / math.sqrt(2)))
    return S0 * N(d1) - K * math.exp(-R * T) * N(d2)


if __name__ == "__main__":
    if sys.argv[1] == "--bs":
        print("%.10f" % bs())
    else:
        n = int(sys.argv[1]); seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
        s1, s2 = acc(seed, 0, n)
        p, se = price(s1, s2, n)
        # the libm exp/log agree with ours to ~1 ulp; the bits are ours
        assert abs(exp_(0.3) - math.exp(0.3)) < 1e-15 and abs(log_(0.3) - math.log(0.3)) < 1e-15
        print("option paths=%d acc=%s price=%.6f se=%.6f" % (n, " ".join("%08x" % w for w in words(s1, s2)), p, se))
