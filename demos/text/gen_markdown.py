#!/usr/bin/env python3
"""A big Markdown document, deterministic: numbered chapters built from every
construct md2html knows (plus unclosed markers and raw < > &).
usage: gen_markdown.py OUT [MiB=20]"""
import random, sys

out, mib = sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 20
rng = random.Random(7)
W = ("bend string slice view proof law parallel core gpu affine type checker "
     "runtime word line text fast small value map list fold tree kernel").split()

def words(a, b):
    return " ".join(rng.choices(W, k=rng.randint(a, b)))

def sentence():
    s = words(5, 14)
    deco = rng.random()
    if deco < 0.15: s += f" **{words(1, 3)}**"
    elif deco < 0.30: s += f" *{words(1, 3)}*"
    elif deco < 0.45: s += f" `{words(1, 2).replace(' ', '_')}(x) < y && z`"
    elif deco < 0.55: s += f" [{words(1, 3)}](https://example.com/{rng.randint(1, 9999)}?a=1&b=2)"
    elif deco < 0.58: s += " a lone * star, an open [bracket and 1 < 2 > 0"
    return s.capitalize() + "."

size, n = 0, 0
with open(out, "w") as f:
    while size < mib << 20:
        n += 1
        parts = [f"# Chapter {n}: {words(2, 5)}\n"]
        for sec in range(rng.randint(2, 4)):
            parts.append(f"{'##' if sec % 2 == 0 else '###'} {n}.{sec + 1} {words(2, 4)}\n")
            for _ in range(rng.randint(1, 3)):
                parts.append("\n".join(sentence() for _ in range(rng.randint(2, 5))) + "\n")
            parts.append("\n".join(f"- {sentence()}" for _ in range(rng.randint(2, 6))) + "\n")
            if rng.random() < 0.5:
                parts.append("```\ndef f(x: U32) -> U32:\n  (x * 2 : U32)  # **not bold** <&>\n```\n")
        chunk = "\n".join(parts) + "\n"
        f.write(chunk)
        size += len(chunk)
print(f"{out}: {size} bytes, {n} chapters")
