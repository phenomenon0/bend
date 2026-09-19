#!/usr/bin/env python3
# The tour's one input: a hostile log. BLOCKS blocks of exactly 65,536 code
# points of whole lines (the shape demos/parallel/knob.bend forks over), each
# opening with a stamp line `#block 000000000000123` whose 15 digits spell the
# block number (what views.bend's scattered visits parse and check). Lines
# carry emoji usernames, é/ß, combining marks, NBSP, ragged whitespace, some
# very long lines, and, as lines 2 and 3 of block 0, one ReDoS-bait line and
# the line behind Stack Overflow's July 20, 2016 outage, rebuilt from their
# postmortem: their comment text, 20,000 spaces, one `x`.
# Deterministic (seeded). Writes the oracles knob.bend / gputext.bend are
# checked against: tokens split on ASCII whitespace only (NBSP is not a space
# in Bend's words), each hashed h = h*33 + code point.
#   gen_log.py <out.log> <blocks>
import random, re, sys

out, blocks = sys.argv[1], int(sys.argv[2])
BLOCK, BAIT = 65536, 4096
rng = random.Random(7)
USERS = [
    "😀ana",
    "josé",
    "straße_ß",
    "e\u0301milie",
    "zoë\u00a0k",
    "李雷",
    "bob",
    "🦀ferris",
    "gpu-bot",
]
LEVEL = ["INFO", "WARN", "ERROR", "DEBUG"]
MSGS = [
    "login ok",
    "cache  miss",
    "payment\tdeclined",
    "naïve retry",
    "gpu lane warm",
    "disk 93% full",
    "café order #42",
    "timeout after 30s",
    "ünïcödé path /tmp/ñ",
]


def line():
    s = (
        " " * rng.randrange(3)
        + f"2026-09-18T{rng.randrange(24):02d}:{rng.randrange(60):02d} "
    )
    s += f"{rng.choice(LEVEL)} user={rng.choice(USERS)} {rng.choice(MSGS)}"
    if rng.randrange(200) == 0:  # a long line: a dumped payload
        s += " dump=" + " ".join(
            rng.choice(MSGS) for _ in range(rng.randrange(200, 900))
        )
    return s + rng.choice(["", " ", "\t", " \u00a0"]) + "\n"


def make_block(head):
    parts, n = [head], len(head)
    while True:
        l = line()
        if n + len(l) > BLOCK - 1:
            break
        parts.append(l)
        n += len(l)
    parts.append(" " * (BLOCK - 1 - n) + "\n")
    return "".join(parts)


def stats(text):  # tokens, sum of per-token rolling hashes, occurrences of "gpu"
    n = h = 0
    for w in re.split(r"[ \t\n\r\f\v]+", text):
        if w:
            x = 0
            for c in w:
                x = (x * 33 + ord(c)) & 0xFFFFFFFF
            n, h = n + 1, (h + x) & 0xFFFFFFFF
    return n, h, text.count("gpu")


STAMP = "#block 000000000000000\n"  # 7 + 15 digits + newline
pool = [make_block(STAMP) for _ in range(32)]  # 32 distinct bodies, drawn at random
pool_stats = [stats(b[len(STAMP) :]) for b in pool]
SO = "-- play happy sound for player to enjoy" + " " * 20000 + "x\n"
first = make_block(STAMP + "bait " + "a" * BAIT + "!\n" + SO)
n, h, g = stats(first[len(STAMP) :])
size = 0
with open(out, "wb") as f:
    for k in range(blocks):
        i = rng.randrange(len(pool))
        body = first if k == 0 else pool[i]
        stamp = f"#block {k:015d}\n"
        data = (stamp + body[len(STAMP) :]).encode()
        f.write(data)
        size += len(data)
        sn, sh, sg = stats(stamp)
        bn, bh, bg = (0, 0, 0) if k == 0 else pool_stats[i]
        n, h, g = n + sn + bn, (h + sh + bh) & 0xFFFFFFFF, g + sg + bg
print(
    f"{out}: {size} bytes, {blocks * BLOCK} code points, {blocks} blocks, oracle {n}:{h}:{g}"
)
with open(out + ".oracle", "w") as f:
    f.write(f"{n}:{h}\n")
with open(out + ".oracle_gpu", "w") as f:
    f.write(f"{n}:{h}:{g}\n")
