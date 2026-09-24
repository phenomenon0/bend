#!/usr/bin/env python3
# The oracle for pcg.bend: prints the whole fixture. PCG32 is written here from
# pcg-c-basic (O'Neill, pcg_basic.c: pcg32_srandom_r, pcg32_random_r,
# pcg32_advance_r) on Python's unbounded ints, and held to the reference
# demo's first outputs for seed (42, 54) before any row is emitted. The Monte
# Carlo count is a plain sequential loop over the one stream: no jumps, no tree.
import sys

M64 = (1 << 64) - 1
MULT = 6364136223846793005


class Pcg:
    def __init__(self, initstate, initseq):
        self.state, self.inc = 0, ((initseq << 1) | 1) & M64
        self.next()
        self.state = (self.state + initstate) & M64
        self.next()

    def next(self):
        old = self.state
        self.state = (old * MULT + self.inc) & M64
        xs = (((old >> 18) ^ old) >> 27) & 0xFFFFFFFF
        rot = old >> 59
        return ((xs >> rot) | (xs << ((-rot) & 31))) & 0xFFFFFFFF

    def advance(self, delta):  # pcg_advance_lcg_64, Brown's arbitrary stride
        am, ap, cm, cp = 1, 0, MULT, self.inc
        while delta:
            if delta & 1:
                am, ap = (am * cm) & M64, (ap * cm + cp) & M64
            cp, cm = ((cm + 1) * cp) & M64, (cm * cm) & M64
            delta >>= 1
        self.state = (am * self.state + ap) & M64


# pcg32-demo.c, "pcg32_random_r:" first round for seed 42, sequence 54
DEMO = [0xA15C02B7, 0x7B47F409, 0xBA1D3330, 0x83D2F293, 0xBFA4784B, 0xCBED606E]
r = Pcg(42, 54)
assert [r.next() for _ in DEMO] == DEMO


def hex32(x):
    return "0x%08x" % x


def at(k):  # output k of the (42, 54) stream, by one jump
    r = Pcg(42, 54)
    r.advance(k)
    return r.next()


def darts(npairs, initstate=42, initseq=54):
    r, hits = Pcg(initstate, initseq), 0
    for _ in range(npairs):
        x, y = r.next() >> 17, r.next() >> 17
        hits += x * x + y * y < (1 << 30)
    return hits


def reseeded(d, npairs):
    """The usual mistake: leaf j gets its own seed (42 + j), so the stream --
    and the count -- depend on how many leaves there are."""
    leaves = 1 << d
    return sum(darts(npairs // leaves, 42 + j, 54) for j in range(leaves))


def lines():
    yield "demo " + " ".join(hex32(x) for x in DEMO)
    yield "jump 2^40+7=" + hex32(at(2**40 + 7)) + " 10^12=" + hex32(at(10**12))
    n = 1 << 16
    h = darts(n)
    yield f"darts pairs={n} hits={h} at depths 0 4 9: same | reseeded per leaf, depths 4 9: {reseeded(4, n)} {reseeded(9, n)}"


if __name__ == "__main__":
    for line in lines():
        print("#|" + line if "--fixture" in sys.argv else line)
