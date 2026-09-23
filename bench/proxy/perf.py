"""The performance driver: the same fronts, but against a fast upstream (the
Bend httpd serving /health, pinned), driven by wrk. Server/proxy on core 0,
upstream on core 1, the client on cores 2-3, matching the differential harness'
pinning so the two speak of the same placement.

For each front and each concurrency it records requests/sec, p50 and p99
latency and the front's peak resident set. Writes results/perf.json and
results/perf.md.

Usage: python3 perf.py --httpd /path/to/httpd --out results [--dur 8 --conns 32,256]
"""

import argparse
import json
import os
import re
import subprocess
import sys
import time

import fronts

HERE = os.path.dirname(os.path.abspath(__file__))
UP_PORT = 20411
FRONT_PORT = 20420


def rss_kb(pid):
    try:
        with open("/proc/%d/status" % pid) as f:
            for line in f:
                if line.startswith("VmRSS:"):
                    return int(line.split()[1])
    except OSError:
        pass
    return None


def wrk(port, conns, dur):
    cmd = ["taskset", "-c", "2,3", "wrk", "-t", "2", "-c", str(conns),
           "-d", "%ds" % dur, "--latency", "http://127.0.0.1:%d/health" % port]
    out = subprocess.run(cmd, capture_output=True, text=True).stdout
    rps = _num(re.search(r"Requests/sec:\s*([\d.]+)", out))
    # wrk --latency prints a "Latency Distribution" block: `50%  389.00us`.
    p50 = _lat(re.search(r"\n\s*50%\s+([\d.]+)(us|ms|s)", out))
    p99 = _lat(re.search(r"\n\s*99%\s+([\d.]+)(us|ms|s)", out))
    return {"rps": rps, "p50_ms": p50, "p99_ms": p99, "raw": out}


def _num(m):
    return float(m.group(1)) if m else None


def _lat(m):
    if not m:
        return None
    v, u = float(m.group(1)), m.group(2)
    return v * {"us": 0.001, "ms": 1.0, "s": 1000.0}.get(u, 1.0)


def run_case(front, conns, dur):
    peak = 0
    # warm
    wrk(front.front_port, min(conns, 32), 1)
    # measure with RSS sampling
    import threading
    stop = threading.Event()

    def sampler():
        nonlocal peak
        pid = front.proc.pid if front.proc else None
        while not stop.is_set() and pid:
            r = rss_kb(pid)
            if r and r > peak:
                peak = r
            time.sleep(0.1)

    t = threading.Thread(target=sampler, daemon=True)
    t.start()
    res = wrk(front.front_port, conns, dur)
    stop.set()
    t.join(timeout=1)
    res["peak_rss_kb"] = peak
    res.pop("raw", None)
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--httpd", required=True)
    ap.add_argument("--fronts", default="nginx,haproxy,bend_httpd")
    ap.add_argument("--out", default=os.path.join(HERE, "results"))
    ap.add_argument("--work", default="/tmp/claude-0/proxyperf")
    ap.add_argument("--dur", type=int, default=8)
    ap.add_argument("--conns", default="32,256")
    args = ap.parse_args()

    os.makedirs(args.out, exist_ok=True)
    os.makedirs(args.work, exist_ok=True)
    conns = [int(c) for c in args.conns.split(",")]
    want = args.fronts.split(",")

    # fast upstream: the Bend httpd /health, pinned to core 1
    up = fronts.BendHttpd(args.work, UP_PORT, args.httpd, pin_core=1)
    if not up.start():
        print("upstream httpd failed", file=sys.stderr)
        return 1

    results = {}
    try:
        for w in want:
            if w == "nginx":
                fr = fronts.Nginx(args.work, FRONT_PORT, UP_PORT, pin_core=0)
                port = FRONT_PORT
            elif w == "haproxy":
                fr = fronts.HAProxy(args.work, FRONT_PORT, UP_PORT, pin_core=0)
                port = FRONT_PORT
            elif w == "bend_httpd":
                # the httpd as a direct server IS the fast upstream on core 1
                fr = up
                port = UP_PORT
            else:
                continue
            if fr is not up and not fr.start():
                print("front %s failed" % w, file=sys.stderr)
                continue
            print("== perf front:", w, "==", flush=True)
            results[w] = {}
            for c in conns:
                r = run_case(fr, c, args.dur)
                results[w]["c%d" % c] = r
                print("  c%-4d rps=%.0f p50=%.2fms p99=%.2fms rss=%dKB" % (
                    c, r["rps"] or 0, r["p50_ms"] or 0, r["p99_ms"] or 0,
                    r["peak_rss_kb"] or 0), flush=True)
            if fr is not up:
                fr.stop()
    finally:
        up.stop()

    with open(os.path.join(args.out, "perf.json"), "w") as f:
        json.dump(results, f, indent=1)
    _md(results, conns, args.out)
    print("wrote", os.path.join(args.out, "perf.md"))
    return 0


def _md(results, conns, out):
    lines = ["# Proxy performance", "",
             "wrk against `/health`. Front on core 0, upstream (Bend httpd) on "
             "core 1, client on cores 2-3. `bend_httpd` is the httpd as a "
             "direct server (no proxy hop).", "",
             "| front | conns | req/s | p50 ms | p99 ms | peak RSS KB |",
             "|---|---|---|---|---|---|"]
    for w, cs in results.items():
        for c in conns:
            r = cs.get("c%d" % c)
            if not r:
                continue
            lines.append("| %s | %d | %.0f | %.2f | %.2f | %d |" % (
                w, c, r["rps"] or 0, r["p50_ms"] or 0, r["p99_ms"] or 0,
                r["peak_rss_kb"] or 0))
    with open(os.path.join(out, "perf.md"), "w") as f:
        f.write("\n".join(lines) + "\n")


if __name__ == "__main__":
    sys.exit(main())
