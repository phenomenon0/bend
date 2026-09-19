#!/usr/bin/env python3
"""Prose-shaped corpus from a word list, deterministic.
usage: gen_corpus.py OUT [MiB=300] [DICT=/usr/share/dict/linux.words]
Words are drawn Zipf-style (weight 1/rank over a shuffled dictionary) into a
pool of 4000 paragraphs of capitalized, punctuated sentences; the file is
paragraphs drawn from that pool until it reaches the requested size."""
import random, sys

out = sys.argv[1]
mib = int(sys.argv[2]) if len(sys.argv) > 2 else 300
words = open(sys.argv[3] if len(sys.argv) > 3 else "/usr/share/dict/linux.words").read().split()
rng = random.Random(7)
rng.shuffle(words)
cum, total = [], 0.0
for rank in range(1, len(words) + 1):
    total += 1.0 / rank
    cum.append(total)

def paragraph():
    sentences = []
    for _ in range(rng.randint(3, 8)):
        ws = rng.choices(words, cum_weights=cum, k=rng.randint(6, 18))
        if len(ws) > 9:
            ws[4] += ","
        sentences.append(" ".join(ws).capitalize() + ".")
    return " ".join(sentences) + "\n\n"

pool = [paragraph() for _ in range(4000)]
size = 0
with open(out, "w") as f:
    while size < mib << 20:
        chunk = "".join(rng.choices(pool, k=256))
        f.write(chunk)
        size += len(chunk.encode())
print(f"{out}: {size} bytes")
