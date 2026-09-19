#!/usr/bin/env python3
# Corpus for the parallel demos: BLOCKS blocks of exactly BLOCK code points,
# each a run of whole lines (mixed ASCII / Unicode words, ragged indentation)
# padded with spaces before its last newline. A cut at any multiple of BLOCK
# code points therefore never splits a line or a word, so the chunked scans
# and the whole-text oracle agree. Deterministic (seeded); prints the oracle.
#   gen_corpus.py <out.txt> <blocks> [block_codepoints=65536]
import random, sys

out, blocks = sys.argv[1], int(sys.argv[2])
block = int(sys.argv[3]) if len(sys.argv) > 3 else 65536
rng = random.Random(1)
WORDS = (
    "the quick brown fox jumps over lazy dog bend parallel thread gpu lane "
    "café naïve λ 漢字 😀 future affine linear type check scan words"
).split()


def make_block():
    parts, n = [], 0
    while True:
        line = " " * rng.randrange(4) + " ".join(
            rng.choice(WORDS) for _ in range(rng.randrange(1, 14))
        )
        line += rng.choice(["", " ", "\t"]) + "\n"
        if n + len(line) > block - 1:
            break
        parts.append(line)
        n += len(line)
    parts.append(" " * (block - 1 - n) + "\n")
    return "".join(parts)


# 64 distinct blocks, drawn at random: real variety without hours of Python.
pool = [make_block() for _ in range(64)]


def stats(text):  # the scan's oracle: tokens, sum of per-token rolling hashes
    n = h = 0
    for w in text.split():
        x = 0
        for c in w:
            x = (x * 33 + ord(c)) & 0xFFFFFFFF
        n, h = n + 1, (h + x) & 0xFFFFFFFF
    return n, h


pool_stats = [stats(b) for b in pool]
pool_bytes = [b.encode() for b in pool]
pool_gpu = [b.count("gpu") for b in pool]  # gputext.bend's occurrence count
n = h = g = size = 0
with open(out, "wb") as f:
    for _ in range(blocks):
        i = rng.randrange(len(pool))
        f.write(pool_bytes[i])
        size += len(pool_bytes[i])
        n, h = n + pool_stats[i][0], (h + pool_stats[i][1]) & 0xFFFFFFFF
        g += pool_gpu[i]
print(f"{out}: {size} bytes, {blocks * block} code points, oracle {n}:{h}")
with open(out + ".oracle", "w") as f:
    f.write(f"{n}:{h}\n")
with open(out + ".oracle_gpu", "w") as f:
    f.write(f"{n}:{h}:{g}\n")
