#!/usr/bin/env python3
# The oracle for utf8.bend: prints the whole fixture. The bytes are rebuilt
# here from the same slot rule (Threefry2x32-20, written from the Random123
# paper and held to its known-answer vectors), and every verdict comes from
# CPython's own decoder -- bytes.decode("utf-8") -- not from a DFA: validity,
# the code point count, and the dead byte read off the UnicodeDecodeError.
# A reference DFA runs beside it only to assert the two agree.
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


for k, c, want in [
    ((0, 0), (0, 0), (0x6B200159, 0x99BA4EFE)),
    ((M, M), (M, M), (0x1CB996FC, 0xBB002BE7)),
    ((0x13198A2E, 0x03707344), (0x243F6A88, 0x85A308D3), (0xC4923A9C, 0x483DF7A0)),
]:
    assert block(*k, *c) == want


def enc(cp):
    b = chr(cp).encode("utf-8", "surrogatepass")
    return b


def asc(r, sh):
    return bytes([0x30 + ((r >> sh) & 63)])


def cp3(r):
    c = (r >> 3) & 0xFFFF
    c = c + 0x800 if c < 0x800 else c
    return c - 0x800 if 0xD800 <= c < 0xE000 else c


POISON = [
    b"\x80AAA",  # a lone continuation: invalid start byte
    b"\xc0\xafAA",  # an overlong '/': C0 is never a lead
    b"\xed\xa0\x80A",  # U+D800 encoded: ED forbids A0..BF
    b"\xe2\x82AA",  # a euro sign cut short
    b"\xf5AAA",  # past the last plane's lead
    b"\xf4\x90\x80\x80",  # U+110000: F4 forbids 90..BF
    b"\xe0\x80\x80A",  # an overlong NUL: E0 forbids 80..9F
    b"A\xc3AA",  # a two-byte lead with no tail
]


def slot(seed, i, poison):
    if i in poison:
        return POISON[poison[i]]
    r = block(seed, 0, i, 0)[0]
    k = r & 7
    if k < 2:
        return b"".join(asc(r, 3 + 6 * j) for j in range(4))
    if k == 2:
        return enc(0x80 + ((r >> 3) & 0x3FF)) + enc(0x80 + ((r >> 13) & 0x3FF))
    if k == 3:
        return enc(cp3(r)) + asc(r, 19)
    if k == 4:
        return asc(r, 19) + enc(cp3(r))
    if k < 7:
        return enc(0x10000 + ((r >> 3) % 0x100000))
    return enc(0x80 + ((r >> 3) & 0x3FF)) + asc(r, 13) + asc(r, 19)


def corpus(seed, lo, n, poison):
    out = b"".join(slot(seed, i, poison) for i in range((lo + n + 3) // 4))
    assert len(out) == 4 * ((lo + n + 3) // 4)
    return out[lo:lo + n]


# The reference DFA (Unicode 15, table 3-7): 0 ACC, 1-3 need that many tails,
# 4 E0, 5 ED, 6 F0, 7 F4, 8 dead. Only used to cross-check CPython.
def nxt(s, b):
    if s == 0:
        if b < 0x80: return 0
        if 0xC2 <= b < 0xE0: return 1
        if b == 0xE0: return 4
        if b == 0xED: return 5
        if 0xE0 < b < 0xF0: return 2
        if b == 0xF0: return 6
        if 0xF0 < b < 0xF4: return 3
        if b == 0xF4: return 7
        return 8
    lo, hi = {4: (0xA0, 0xC0), 5: (0x80, 0xA0), 6: (0x90, 0xC0), 7: (0x80, 0x90)}.get(s, (0x80, 0xC0))
    if not lo <= b < hi: return 8
    return {1: 0, 2: 1, 3: 2, 4: 1, 5: 1, 6: 2, 7: 2}[s]


def smap(data):
    out = ""
    for s0 in range(8):
        s = s0
        for b in data:
            s = nxt(s, b)
            if s == 8: break
        out += str(s)
    return out


def verdict(data):
    try:
        cps = len(data.decode("utf-8"))
        return "yes", cps, "-"
    except UnicodeDecodeError as e:
        dead = {"invalid start byte": e.start, "invalid continuation byte": e.end,
                "unexpected end of data": len(data)}[e.reason]
        cps = sum(1 for b in data if b & 0xC0 != 0x80)
        return "no", cps, str(dead)


def dfa_dead(data):
    s = 0
    for i, b in enumerate(data):
        s = nxt(s, b)
        if s == 8: return i
    return len(data) if s else None


CASES = [  # name, seed, first byte, n bytes, {slot: poison}
    ("clean", 1, 0, 16384, {}),
    ("cut", 3, 0, 16393, {}),  # ends three tails short of a 4-byte scalar
    ("mid", 3, 1, 16000, {}),  # starts one byte into one: a set of entries
] + [("poison" + str(k), 9 + k, 0, 20001, {1000 + 97 * k: k, 3000: (k + 3) % 8})
     for k in range(8)]

DEPTHS = "0 1 5 11 15"


def lines():
    for name, seed, lo, n, poison in CASES:
        data = corpus(seed, lo, n, poison)
        ok, cps, dead = verdict(data)
        m = smap(data)
        dd = dfa_dead(data)
        assert (m[0] == "0") == (ok == "yes")
        assert dead == ("-" if dd is None else str(dd)), (name, dead, dd)
        yield f"{name} n={n} map={m} valid={ok} cps={cps} dead={dead} splits {DEPTHS}: same"


if __name__ == "__main__":
    for line in lines():
        print("#|" + line if "--fixture" in sys.argv else line)
