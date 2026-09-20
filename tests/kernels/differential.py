#!/usr/bin/env python3
"""Independent executable specs versus production, with four-lane exact pins.

SHA outputs also match CPython hashlib; ChaCha word outputs match a Python
transcription of RFC 8439. Finite differential evidence is not a universal proof.
Generated inputs, fixtures, hashes, and runner output remain in --output (or /tmp).
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import platform
import random
import re
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[2]
SEED = 0x2568439


def imports(path):
    return re.findall(r"^import (.+)$", path.read_text(), re.M)


def independence():
    required = {
        "fips.bend": ["Base", "./spec_state.bend as S"],
        "spec_state.bend": ["Base"],
        "rfc8439.bend": ["Base"],
    }
    for name, expected in required.items():
        path = ROOT / "demos/kernels" / name
        if imports(path) != expected:
            raise RuntimeError(f"Specification import boundary changed: {name}")
        code = "\n".join(line.split("#", 1)[0] for line in path.read_text().splitlines())
        if re.search(r"@unsafe|\?", code):
            raise RuntimeError(f"Unsafe annotation or hole in specification: {name}")
    neutral = (ROOT / "demos/kernels/spec_state.bend").read_text()
    if re.search(r"^(def|law)\b", neutral, re.M):
        raise RuntimeError("Neutral state module contains executable helpers or laws")


def literal(values):
    return "[" + ",".join(map(str, values)) + "]"


def array(values):
    if len(values) == 1:
        return "ALeaf{" + str(values[0]) + "}"
    middle = len(values) // 2
    return "ANode{" + array(values[:middle]) + "," + array(values[middle:]) + "}"


def packed(data, rng):
    size = 1 << (max(1, (len(data) + 3) // 4) - 1).bit_length()
    storage = data + rng.randbytes(size * 4 - len(data))
    return [int.from_bytes(storage[i:i + 4], "big") for i in range(0, len(storage), 4)]


def chacha(key, counter, nonce):
    original = [0x61707865, 0x3320646E, 0x79622D32, 0x6B206574, *key, counter, *nonce]
    state = original.copy()
    mask = 0xFFFFFFFF
    def quarter(a, b, c, d):
        for left, right, out, rotation in ((a, b, d, 16), (c, d, b, 12),
                                           (a, b, d, 8), (c, d, b, 7)):
            state[left] = (state[left] + state[right]) & mask
            value = state[out] ^ state[left]
            state[out] = ((value << rotation) | (value >> (32 - rotation))) & mask
    for _ in range(10):
        for indices in ((0,4,8,12), (1,5,9,13), (2,6,10,14), (3,7,11,15),
                        (0,5,10,15), (1,6,11,12), (2,7,8,13), (3,4,9,14)):
            quarter(*indices)
    return [(a + b) & mask for a, b in zip(state, original)]


HELPERS = """
def equal(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}: True{}
    case x <> xt y <> yt: Bool.and(U32.is_eq(x, y), equal(xt, yt))
    case _ _: False{}
"""
SHA_HELPERS = """
def observe(a: Array<U32>) -> List<&2, U32>:
  match a:
    case ALeaf{x}: [x]
    case ANode{left,right}: List.append(&2, U32, observe(left), observe(right))

def result(r: Maybe<&1, Array<U32>>, expected: List<&2, U32>) -> Bool:
  match r:
    case None{}: False{}
    case Some{a}: equal(observe(a), expected)

def rejected(r: Maybe<&1, Array<U32>>) -> Bool:
  match r:
    case None{}: True{}
    case Some{a}: False{}
"""


def fixture(path, imported, definitions, expressions, expected):
    lines = ["import Base"]
    for name, alias in imported:
        relative = "../../source/" + name
        lines.append(f"import {relative} as {alias}")
    lines.extend([HELPERS, *definitions, "def main() -> List<&2, Bool>:",
                  "  [" + ",\n   ".join(expressions) + "]", "", "#|[" + ", ".join("True{}" for _ in expected) + "]"])
    path.parent.mkdir(exist_ok=True)
    path.write_text("\n".join(lines) + "\n")


def generate(directory, random_cases):
    rng = random.Random(SEED)
    lengths = [0, 1, 2, 3, 4, 31, 55, 56, 57, 63, 64, 65, 119, 120, 127, 128, 129, 255]
    messages = [list(rng.randbytes(n)) for n in lengths]
    messages += [[rng.getrandbits(32) for _ in range(rng.randrange(0, 257))]
                 for _ in range(random_cases)]
    definitions, expressions, expected, records = [SHA_HELPERS], [], [], []
    for index, words in enumerate(messages):
        data = bytes(w & 255 for w in words)
        digest = hashlib.sha256(data).digest()
        digest_words = [int.from_bytes(digest[i:i + 4], "big") for i in range(0, 32, 4)]
        storage = packed(data, rng)
        definitions.append(f"def bytes{index}() -> List<&2, U32>:\n  {literal(words)}\n")
        definitions.append(f"def packed{index}() -> Array<U32>:\n  {array(storage)}\n")
        expressions.extend([f"equal(F.sha256(bytes{index}()), {literal(digest_words)})",
                            f"equal(observe(S.digest(bytes{index}())), {literal(digest_words)})",
                            f'String.eq(S.hash(bytes{index}()), "{digest.hex()}")',
                            f"result(B.hash(packed{index}(), {len(data)}n), {literal(digest_words)})",
                            f"rejected(B.hash(packed{index}(), {len(storage) * 4 + 1}n))"])
        expected.extend([True] * 5)
        records.append({"length": len(data), "input_words": words, "packed_words": storage,
                        "expected_sha256": digest.hex()})
    for first in range(0, len(messages), 6):
        last = min(first + 6, len(messages))
        fixture(directory / f"sha_{first:02d}" / "sha_differential.bend",
                [("sha256.bend", "S"), ("buffer.bend", "B"), ("fips.bend", "F")],
                definitions, expressions[first * 5:last * 5], expected[first * 5:last * 5])
    inputs = [([0] * 8, 0, [0] * 3),
              ([int.from_bytes(bytes(range(i, i + 4)), "little") for i in range(0, 32, 4)],
               1, [0x09000000, 0x4A000000, 0])]
    inputs += [([rng.getrandbits(32) for _ in range(8)], rng.getrandbits(32),
                [rng.getrandbits(32) for _ in range(3)]) for _ in range(random_cases)]
    inputs += [([0xFFFFFFFF] * 8, 0xFFFFFFFF, [0xFFFFFFFF] * 3)]
    expressions, expected, chacha_records = [], [], []
    for key, counter, nonce in inputs:
        output = chacha(key, counter, nonce)
        expressions.extend([f"equal(R.block({literal(key)}, {counter}, {literal(nonce)}), {literal(output)})",
                            "equal(C.words(C.block_words(C.ChaKey{" + ",".join(map(str, key)) + "}, " +
                            str(counter) + ", C.Nonce{" + ",".join(map(str, nonce)) + "})), " + literal(output) + ")"])
        expected.extend([True] * 2)
        chacha_records.append({"key": key, "counter": counter, "nonce": nonce, "expected_words": output})
    fixture(directory / "chacha" / "chacha_differential.bend", [("chacha20.bend", "C"), ("rfc8439.bend", "R")],
            [], expressions, expected)
    corpus = {"seed": SEED, "sha256": records, "chacha20": chacha_records}
    (directory / "corpus.json").write_text(json.dumps(corpus, indent=2) + "\n")
    return len(messages), len(inputs)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--random-cases", type=int, default=8)
    parser.add_argument("--timeout", type=int, default=120, help="Per-lane and build wall limit in seconds")
    args = parser.parse_args()
    if args.random_cases < 1 or args.timeout < 1:
        parser.error("random-cases and timeout must be positive")
    independence()
    directory = args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix="bend-kernels-differential-"))
    directory.mkdir(parents=True, exist_ok=True)
    tracked = ["demos/kernels/sha256.bend", "demos/kernels/buffer.bend", "demos/kernels/chacha20.bend",
               "demos/kernels/fips.bend", "demos/kernels/spec_state.bend", "demos/kernels/rfc8439.bend",
               "tests/kernels/differential.py", "tests/kernels/run.sh", "bend2/bend.ts", "bend2/comp.ts", "bend2/base.bend"]
    hashes = {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in tracked}
    # Local imports keep compiler symbols independent of hyphens in checkout paths.
    source = directory / "source"
    source.mkdir(exist_ok=True)
    for name in tracked:
        if name.startswith("demos/kernels/"):
            shutil.copyfile(ROOT / name, source / Path(name).name)
    fixtures = directory / "fixtures"
    fixtures.mkdir(exist_ok=True)
    sha_count, chacha_count = generate(fixtures, args.random_cases)
    env = {**os.environ, "KERNELS_DIR": str(fixtures), "KERNELS_TIMEOUT": str(args.timeout),
           "KERNELS_BUILD_TIMEOUT": str(args.timeout), "CLANG_MODULE_CACHE_PATH": str(directory / "clang-cache")}
    Path(env["CLANG_MODULE_CACHE_PATH"]).mkdir(exist_ok=True)
    started = time.monotonic()
    command = ["bash", "tests/kernels/run.sh"]
    def run_group(group):
        with (directory / (group.name + ".log")).open("w") as log:
            result = subprocess.run(command, cwd=ROOT, env={**env, "KERNELS_DIR": str(group)},
                                    stdout=log, stderr=subprocess.STDOUT)
        return group.name, result.returncode
    groups = sorted(path for path in fixtures.iterdir() if path.is_dir())
    # Independent batches bound interpreter memory and overlap validation, not benchmarks.
    with ThreadPoolExecutor(max_workers=3) as executor:
        outcomes = dict(executor.map(run_group, groups))
    (directory / "lanes.log").write_text("".join(
        f"Batch {name}\n" + (directory / (name + ".log")).read_text() for name in outcomes))
    elapsed = time.monotonic() - started
    after = {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in tracked}
    stable = hashes == after
    receipt = {"status": "pass" if all(code == 0 for code in outcomes.values()) and stable else "fail", "command": command,
               "sha256_cases": sha_count, "sha256_observations_per_case": 5,
               "chacha20_cases": chacha_count, "chacha20_observations_per_case": 2,
               "lanes": ["strict check", "interpret", "JS", "C"], "seed": SEED,
               "elapsed_seconds": elapsed, "python": sys.version, "host": platform.platform(),
               "hashlib": "CPython hashlib.sha256", "source_hashes": hashes, "source_stable": stable,
               "batch_exit_codes": outcomes, "max_parallel_batches": 3,
               "evidence": "finite differential execution; no universal equivalence theorem"}
    (directory / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print((directory / "lanes.log").read_text(), end="")
    print(f"Differential {receipt['status'].upper()}: SHA {sha_count}, ChaCha {chacha_count}; {elapsed:.3f}s; {directory}")
    if receipt["status"] != "pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
