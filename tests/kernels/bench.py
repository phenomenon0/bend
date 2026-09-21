#!/usr/bin/env python3
"""Measure the public packed-array SHA API; retain every digest and raw time.

python3 tests/kernels/bench.py --warmups 1 --samples 3 --timeout 30
Compilation is excluded; process startup, input construction, SHA and hex are
included. Timings are end-to-end observations, never kernel-only throughput.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import signal
import statistics
import subprocess
import sys
import tempfile
import time


ROOT = Path(__file__).resolve().parents[2]
CORPUS = {"empty": 0, "abc": 3, "pattern-55": 55, "pattern-56": 56,
          "pattern-64": 64, "pattern-1024": 1024, "million-a": 1_000_000}
CHECK = """
import * as B from './bend2/bend.ts';
try {
  const book = B.book_nil();
  await B.book_load(book, process.argv[1], '', new Map());
  B.book_valid(book);
  if (book.hols + book.open) throw new Error('hole/open goal');
  console.log('All terms check.');
} catch (e) {
  console.error(e?.$ === 'Err' ? B.err_show(e) : String(e));
  process.exit(1);
}
"""


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def output_text(value):
    return value.decode(errors="replace") if isinstance(value, bytes) else value or ""


def run(command, directory, environment, limit):
    start = time.perf_counter_ns()
    with subprocess.Popen(command, cwd=directory, env=environment,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          text=True, start_new_session=True) as process:
        try:
            stdout, stderr = process.communicate(timeout=limit)
            row = {"status": "ok" if process.returncode == 0 else "error",
                   "returncode": process.returncode, "stdout": stdout, "stderr": stderr}
        except subprocess.TimeoutExpired:
            # A timed-out Bun build may still have a clang child; bound the whole job.
            os.killpg(process.pid, signal.SIGKILL)
            stdout, stderr = process.communicate()
            row = {"status": "timeout", "returncode": None,
                   "stdout": output_text(stdout), "stderr": output_text(stderr)}
    row.update(command=command, wall_seconds=(time.perf_counter_ns() - start) / 1e9,
               wall_limit_seconds=limit)
    return row


def version(command):
    return subprocess.check_output(command, cwd=ROOT, text=True, timeout=15).strip()


def reference(name):
    if name == "abc":
        data = b"abc"
    elif name == "million-a":
        data = b"a" * CORPUS[name]
    else:
        data = bytes((73 * i + 19) & 255 for i in range(CORPUS[name]))
    return hashlib.sha256(data).hexdigest()


def program(name):
    size = CORPUS[name]
    depth = (max(1, (size + 3) // 4) - 1).bit_length()
    value = ("U32.add(i, 97)" if name == "abc" else "97" if name == "million-a"
             else "U32.and(U32.add(U32.mul(i, 73), 19), 255)")
    return f"""import Base
import ./demos/kernels/buffer.bend as B

# Construct every input leaf at runtime, including unused zero capacity.
def byte_if(i: U32, valid: Bool) -> U32:
  match valid:
    case True{{}}:
      {value}
    case False{{}}:
      0

def byte(+i: U32) -> U32:
  byte_if(i, U32.is_lt(i, {size}))

def word(+i: U32) -> U32:
  +b = U32.mul(i, 4)
  U32.or(U32.or(U32.shln(byte(b), 24n), U32.shln(byte(U32.add(b, 1)), 16n)),
    U32.or(U32.shln(byte(U32.add(b, 2)), 8n), byte(U32.add(b, 3))))

def input(+depth: Nat, +offset: U32, width: U32) -> Array<U32>:
  match depth:
    case 0n:
      ALeaf{{word(offset)}}
    case 1n+p:
      +half = U32.shrn(width, 1n)
      ANode{{input(p, offset, half), input(p, U32.add(offset, half), half)}}

def main() -> String:
  B.hex(B.hash(input({depth}n, 0, {1 << depth}), U32.to_nat({size})))
"""


def save(report, path):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(report, indent=2) + "\n")
    temporary.replace(path)


def source_closure():
    sources = {ROOT / "bend2" / name for name in ("main.ts", "comp.ts", "bend.ts", "base.bend")}
    pending = [ROOT / "demos/kernels/buffer.bend"]
    while pending:
        source = pending.pop().resolve()
        if source in sources:
            continue
        source.relative_to(ROOT)
        sources.add(source)
        for imported in re.findall(r"^import\s+(\S+)", source.read_text(), re.M):
            if imported == "Base":
                continue
            if not imported.startswith("."):
                raise ValueError(f"benchmark requires local imports: {source}: {imported}")
            pending.append(source.parent / imported)
    return sorted(sources)


def sample(command, scratch, environment, timeout, expected, phase, index):
    row = run(command, scratch, environment, timeout)
    row.update(phase=phase, index=index, digest_checked=False)
    if row["status"] == "ok":
        try:
            actual = json.loads(row["stdout"])
        except (json.JSONDecodeError, ValueError):
            actual = None
        row["digest"] = actual
        row["digest_checked"] = actual == expected
        if not row["digest_checked"]:
            row["status"] = "digest-mismatch"
    return row


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--warmups", type=int, default=1)
    parser.add_argument("--samples", type=int, default=3)
    parser.add_argument("--timeout", type=float, default=30,
                        help="wall limit for each execution, seconds")
    parser.add_argument("--build-timeout", type=float, default=120)
    parser.add_argument("--cc", default=os.environ.get("CC", "clang"))
    parser.add_argument("--case", action="append", choices=list(CORPUS),
                        help="select cases; default is the entire fixed corpus")
    parser.add_argument("--interpret-million", action="store_true",
                        help="also record a separate interpreter resource probe")
    parser.add_argument("--output", type=Path,
                        default=ROOT / "docs/omen/lanes/kernels-2-evidence/bench.json")
    args = parser.parse_args()
    if args.warmups < 1 or args.samples < 3 or min(args.timeout, args.build_timeout) <= 0:
        parser.error("require warmups >= 1, samples >= 3 and positive wall limits")
    if args.output.exists():
        parser.error("output already exists; choose a new --output to retain raw evidence")
    compiler = shutil.which(args.cc)
    bun = shutil.which("bun")
    if not compiler or not bun:
        parser.error("the selected clang and bun must exist on PATH")
    compiler = str(Path(compiler).resolve())
    compiler_version = version([compiler, "--version"])
    match = re.search(r"^(?:Apple )?(?:\w+ )?clang version (\d+)", compiler_version, re.M)
    if not match or int(match[1]) < 14:
        parser.error("--cc must select clang >= 14; fallback compiler selection is forbidden")
    cpu = platform.processor()
    if Path("/proc/cpuinfo").exists():
        for line in Path("/proc/cpuinfo").read_text().splitlines():
            if line.startswith("model name"):
                cpu = line.split(":", 1)[1].strip()
                break
    report = {
        "schema": 1, "started_utc": datetime.now(timezone.utc).isoformat(),
        "scope": "end-to-end process: input construction + hash + hex + startup/output; compile excluded",
        "api": "B.hex(B.hash(Array<U32>, byte_length))",
        "oracle": "CPython hashlib.sha256; all successful warmups and samples checked",
        "host": {"node": platform.node(), "platform": platform.platform(),
                 "machine": platform.machine(), "cpu": cpu, "logical_cpus": os.cpu_count()},
        "python": sys.version, "bun": {"path": bun, "version": version([bun, "--version"])},
        "compiler": {"path": compiler, "version": compiler_version,
                     "sha256": digest(Path(compiler)), "CC": compiler},
        "git_head": version(["git", "rev-parse", "HEAD"]),
        "git_status": version(["git", "status", "--porcelain"]),
        "warmups": args.warmups, "samples": args.samples, "cases": [],
        "status": "running",
    }
    names = list(dict.fromkeys(args.case or CORPUS))
    report["complete_corpus"] = set(names) == set(CORPUS)
    failed = False
    with tempfile.TemporaryDirectory(prefix="bend-kernel-bench-") as directory:
        scratch = Path(directory)
        hashes = {}
        for source in source_closure():
            relative = source.relative_to(ROOT)
            target = scratch / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, target)
            hashes[str(relative)] = digest(target)
        report["source_sha256"] = hashes
        report["driver_sha256"] = digest(Path(__file__))
        cache = scratch / "clang-module-cache"
        cache.mkdir()
        environment = {**os.environ, "CC": compiler, "CLANG_MODULE_CACHE_PATH": str(cache)}
        report["CLANG_MODULE_CACHE_PATH"] = str(cache)
        save(report, args.output)
        for name in names:
            source = scratch / (name + ".bend")
            source.write_text(program(name))
            expected = reference(name)
            case = {"name": name, "bytes": CORPUS[name], "expected_hashlib_sha256": expected,
                    "input_rule": "abc" if name == "abc" else "repeat 0x61" if name == "million-a"
                                  else "byte[i] = (73*i+19) & 255",
                    "generated_source_sha256": digest(source), "raw_samples": []}
            report["cases"].append(case)
            check = run([bun, "-e", CHECK, str(source)], scratch, environment, args.build_timeout)
            case["strict_check"] = check
            if check["status"] != "ok" or check["stdout"] != "All terms check.\n":
                case["status"] = "strict-check-failed"
                failed = True
                save(report, args.output)
                print(f"{name}: strict-check-failed", flush=True)
                continue
            binary = scratch / name
            build = run([bun, "bend2/main.ts", str(source), "-o", str(binary)],
                        scratch, environment, args.build_timeout)
            case["build"] = build
            if build["status"] != "ok":
                case["status"] = "build-failed"
                failed = True
                save(report, args.output)
                print(f"{name}: build-failed", flush=True)
                continue
            case["binary_sha256"] = digest(binary)
            case["status"] = "ok"
            for index in range(args.warmups + args.samples):
                phase = "warmup" if index < args.warmups else "measured"
                row = sample([str(binary), "--threads", "1", "--gpu", "off"],
                             scratch, environment, args.timeout, expected, phase, index)
                case["raw_samples"].append(row)
                if row["status"] != "ok":
                    case["status"] = row["status"]
                    failed = True
                    if row["status"] == "timeout":
                        case["resource_bound"] = {
                            "observation": "process did not complete within the configured wall limit",
                            "completion_seconds_greater_than": args.timeout,
                            "completion_rate_bytes_per_second_less_than": CORPUS[name] / args.timeout,
                            "scope": "end-to-end completion rate only; no completed digest available"}
                    save(report, args.output)
                    break
                save(report, args.output)
            if case["status"] == "ok":
                measured = [r["wall_seconds"] for r in case["raw_samples"] if r["phase"] == "measured"]
                case["median_seconds"] = statistics.median(measured)
                case["end_to_end_bytes_per_second"] = CORPUS[name] / case["median_seconds"]
            print(f"{name}: {case['status']}" +
                  (f", median {case['median_seconds']:.6f}s, all digests checked"
                   if case["status"] == "ok" else ""), flush=True)
            if args.interpret_million and name == "million-a":
                case["interpreter_probe"] = sample([bun, "bend2/main.ts", str(source)],
                    scratch, environment, args.timeout, expected, "resource-probe", 0)
                probe = case["interpreter_probe"]
                if probe["status"] == "timeout":
                    probe["resource_bound"] = {
                        "completion_seconds_greater_than": args.timeout,
                        "completion_rate_bytes_per_second_less_than": CORPUS[name] / args.timeout,
                        "scope": "interpreter includes loading/checking; no completed digest available"}
                elif probe["status"] != "ok":
                    failed = True
            save(report, args.output)
    report["finished_utc"] = datetime.now(timezone.utc).isoformat()
    report["status"] = "failed" if failed else "ok"
    save(report, args.output)
    print(f"Raw evidence: {args.output}")
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
