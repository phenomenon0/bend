#!/usr/bin/env python3
"""bend-uptime, checked from outside.

  python3 apps/uptime/check.py --bin ./uptime            the checks
  python3 apps/uptime/check.py --bin ./uptime --soak 180 50 monitors at 1 s: RSS, CPU, drift
  python3 apps/uptime/check.py --js                      the checks on the JS lane (bun)

Starts fake targets (ok, slow, flaky, down, a body mismatch, a webhook
sink that fails its first POST) and the app on ports 29400-29499 (from
--port-base N: N+10, N+11, N+20), then
asserts the API, the state transitions, the webhook and its retry, the
live WebSocket push, persistence across a restart and a clean SIGTERM.
Needs `websockets` (pip install websockets).
"""
import argparse, asyncio, json, os, shutil, signal, subprocess, sys, tempfile, threading, time
import urllib.request, urllib.error
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
TGT, DOWN, APP = 29410, 29411, 29420

# Targets
# -------

class World:
    flaky_up = True
    hooks = []          # the webhook bodies received (after the first failure)
    hook_tries = 0

class Target(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"
    def log_message(self, *a): pass
    def send(self, code, body=b"ok\n"):
        self.send_response(code)
        self.send_header("content-length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)
    def do_GET(self):
        p = self.path
        if p.startswith("/ok"): return self.send(200, b"all good\n")
        if p.startswith("/slow"): time.sleep(1.5); return self.send(200)
        if p.startswith("/flaky"): return self.send(200 if World.flaky_up else 503, b"flaky\n")
        if p.startswith("/text"): return self.send(200, b"nothing to see\n")
        return self.send(404)
    def do_POST(self):
        n = int(self.headers.get("content-length", "0"))
        body = self.rfile.read(n)
        if self.path == "/hook":
            World.hook_tries += 1
            if World.hook_tries == 1:   # the first one fails: the app must retry
                return self.send(500)
            World.hooks.append(json.loads(body))
            return self.send(204, b"")
        if self.path == "/ctl/flaky/down": World.flaky_up = False; return self.send(200)
        if self.path == "/ctl/flaky/up": World.flaky_up = True; return self.send(200)
        return self.send(404)

def targets():
    srv = ThreadingHTTPServer(("127.0.0.1", TGT), Target)
    srv.daemon_threads = True
    srv.handle_error = lambda *a: None   # a probe that timed out closed its socket: not news
    threading.Thread(target=srv.serve_forever, daemon=True).start()
    return srv

# HTTP helpers
# ------------

def req(method, path, body=None, port=None):
    port = port or APP
    data = None if body is None else (body if isinstance(body, bytes) else json.dumps(body).encode())
    r = urllib.request.Request("http://127.0.0.1:%d%s" % (port, path), data=data, method=method)
    if data is not None: r.add_header("content-type", "application/json")
    try:
        with urllib.request.urlopen(r, timeout=5) as f:
            return f.status, dict(f.headers), f.read()
    except urllib.error.HTTPError as e:
        return e.code, dict(e.headers), e.read()

def jreq(method, path, body=None):
    s, h, b = req(method, path, body)
    return s, (json.loads(b) if b else None)

def mons():
    s, j = jreq("GET", "/api/monitors")
    assert s == 200, s
    return {m["name"]: m for m in j}

def until(what, f, secs=8.0):
    t = time.time() + secs
    while time.time() < t:
        try:
            v = f()
            if v: return v
        except (Exception, AssertionError):
            pass
        time.sleep(0.1)
    raise AssertionError("timed out waiting for " + what)

# The app
# -------

def config(d, n_extra=0, every=500):
    ms = [
        {"name": "ok", "url": "http://127.0.0.1:%d/ok" % TGT, "interval_ms": every, "timeout_ms": min(every, 400)},
        {"name": "slow", "url": "http://127.0.0.1:%d/slow" % TGT, "interval_ms": 1000, "timeout_ms": 500},
        {"name": "flaky", "url": "http://127.0.0.1:%d/flaky" % TGT, "interval_ms": every, "timeout_ms": min(every, 400)},
        {"name": "down", "url": "http://127.0.0.1:%d/" % DOWN, "interval_ms": every, "timeout_ms": min(every, 400)},
        {"name": "text", "url": "http://127.0.0.1:%d/text" % TGT, "interval_ms": every, "timeout_ms": min(every, 400),
         "body": "all good"},
    ]
    ms += [{"name": "m%02d" % i, "url": "http://127.0.0.1:%d/ok?%d" % (TGT, i), "interval_ms": every,
            "timeout_ms": min(every, 800)} for i in range(n_extra)]
    p = os.path.join(d, "monitors.json")
    json.dump({"webhook": "http://127.0.0.1:%d/hook" % TGT, "monitors": ms}, open(p, "w"))
    return p

def start(cmd, d, cfg):
    args = ["--config", cfg, "--state", os.path.join(d, "u"), "--port", str(APP), "--host", "127.0.0.1",
            "--web", os.path.join(ROOT, "apps/uptime/web")]
    err = open(os.path.join(d, "stderr.log"), "ab")
    p = subprocess.Popen(cmd + args, stdout=err, stderr=err, cwd=ROOT)
    def up():
        if p.poll() is not None:
            raise SystemExit("the app exited %d:\n%s" % (p.returncode, open(os.path.join(d, "stderr.log")).read()[-2000:]))
        return req("GET", "/health")[0] == 200
    until("the app's /health", up, 120)
    return p

def stop(p, secs=8):
    p.send_signal(signal.SIGTERM)
    try:
        return p.wait(secs)
    except subprocess.TimeoutExpired:
        p.kill(); p.wait()
        return "still running %d s after SIGTERM (killed)" % secs

# WebSocket
# ---------

async def ws_one():
    import websockets
    async with websockets.connect("ws://127.0.0.1:%d/live" % APP) as ws:
        return json.loads(await asyncio.wait_for(ws.recv(), 5))

# The checks
# ----------

PASS, FAIL = [], []

def bad(name):
    FAIL.append(name)
    print("FAIL " + name, flush=True)

def ok(name):
    PASS.append(name)
    print("ok  " + name, flush=True)

def checks(cmd, d):
    cfg = config(d)
    p = start(cmd, d, cfg)
    try:
        m = until("every monitor probed", lambda: (lambda m: m if all(x["last"] for x in m.values()) else None)(mons()))
        assert set(m) == {"ok", "slow", "flaky", "down", "text"}, m.keys()
        ok("GET /api/monitors lists the config's five")
        m = until("the states settle", lambda: (lambda m: m if m["slow"]["state"] == "down" else None)(mons()))
        assert m["ok"]["state"] == "up" and m["ok"]["last"]["code"] == 200, m["ok"]
        assert m["down"]["state"] == "down" and m["down"]["last"]["err"] == "connection refused", m["down"]
        assert m["slow"]["last"]["err"] == "timeout" and m["slow"]["last"]["ms"] < 1200, m["slow"]["last"]
        assert m["text"]["state"] == "down" and "body lacks" in m["text"]["last"]["err"], m["text"]["last"]
        assert m["ok"]["uptime_24h"] == 100 and m["ok"]["checks_24h"] >= 1, m["ok"]
        assert m["down"]["uptime_24h"] == 0, m["down"]
        assert m["ok"]["interval_ms"] == 500 and m["ok"]["timeout_ms"] == 400 and m["ok"]["expect"] == 200
        ok("states: up, down (refused), down (timeout, cut at 500 ms), down (body), uptime %")

        got = asyncio.run(ws_one())
        assert "name" in got and "up" in got and "ms" in got, got
        ok("GET /live pushes each probe (%s)" % got["name"])

        until("flaky up", lambda: mons()["flaky"]["state"] == "up")
        req("POST", "/ctl/flaky/down", b"", port=TGT)
        until("flaky down", lambda: mons()["flaky"]["state"] == "down")
        until("the down webhook", lambda: any(h["event"] == "down" and h["name"] == "flaky" for h in World.hooks))
        assert World.hook_tries >= 2
        ok("up -> down: the webhook, retried after its first 500")
        req("POST", "/ctl/flaky/up", b"", port=TGT)
        until("flaky up again", lambda: mons()["flaky"]["state"] == "up")
        until("the up webhook", lambda: any(h["event"] == "up" and h["name"] == "flaky" for h in World.hooks))
        h = [h for h in World.hooks if h["event"] == "up"][-1]
        assert h["probe"]["code"] == 200 and h["url"].endswith("/flaky"), h
        ok("down -> up: the webhook")
        assert not any(h["name"] in ("down", "slow", "text") for h in World.hooks), World.hooks
        ok("no webhook for pending -> down")

        s, j = jreq("GET", "/api/monitors/ok/history?limit=3")
        assert s == 200 and len(j["history"]) == 3, j
        ts = [x["t"] for x in j["history"]]
        assert ts == sorted(ts, reverse=True), ts
        assert jreq("GET", "/api/monitors/ok/history?limit=0")[0] == 400
        assert jreq("GET", "/api/monitors/ok/history?limit=x")[0] == 400
        assert jreq("GET", "/api/monitors/nope/history")[0] == 404
        ok("history: newest first, limit checked, 404")

        s, j = jreq("POST", "/api/monitors", {"name": "bad name!", "url": "ftp://x", "interval_ms": 5,
                                              "timeout_ms": "1", "expect": 700})
        assert s == 400 and len(j["errors"]) == 5, (s, j)
        s, j = jreq("POST", "/api/monitors", b"{nope")
        assert s == 400 and "not JSON" in j["errors"][0], j
        s, j = jreq("POST", "/api/monitors", [1])
        assert s == 400, j
        s, j = jreq("POST", "/api/monitors", {"name": "t", "url": "http://x/", "interval_ms": 1000, "timeout_ms": 2000})
        assert s == 400 and j["errors"] == ["timeout_ms must not exceed interval_ms"], j
        ok("POST refuses with every reason (400)")
        s, j = jreq("POST", "/api/monitors", {"name": "extra", "url": "http://127.0.0.1:%d/ok" % TGT,
                                              "interval_ms": 300, "timeout_ms": 200, "body": "good"})
        assert s == 201 and j["name"] == "extra", (s, j)
        assert jreq("POST", "/api/monitors", {"name": "extra", "url": "http://127.0.0.1/"})[0] == 409
        until("extra probed", lambda: mons()["extra"]["state"] == "up")
        ok("POST adds a monitor at runtime (201, 409 twice), probed at once")
        jreq("POST", "/api/monitors", {"name": "gone", "url": "http://127.0.0.1:%d/ok" % TGT, "interval_ms": 300,
                                       "timeout_ms": 200})
        until("gone probed", lambda: mons()["gone"]["last"])
        assert req("DELETE", "/api/monitors/gone")[0] == 204
        assert req("DELETE", "/api/monitors/gone")[0] == 404
        assert "gone" not in mons()
        ok("DELETE removes it (204, then 404)")

        s, h, b = req("GET", "/")
        assert s == 200 and b"bend-uptime" in b, s
        assert "default-src 'self'" in h.get("content-security-policy", ""), h
        assert req("GET", "/app.js")[0] == 200 and req("GET", "/../check.py")[0] == 404
        s, h, b = req("GET", "/api/monitors")
        assert h.get("x-content-type-options") == "nosniff", h
        ok("the dashboard's files, the middleware's headers")

        time.sleep(0.5)
        before = {k: v["checks_24h"] for k, v in mons().items()}
        t0 = time.time()
        code = stop(p)
        took = time.time() - t0
        if code == 0: ok("SIGTERM: exit 0 in %.2f s" % took)
        else: bad("SIGTERM: %s" % code)
    finally:
        if p.poll() is None: p.kill()

    p = start(cmd, d, cfg)
    try:
        m = mons()
        assert "extra" in m and "gone" not in m, m.keys()
        assert m["ok"]["checks_24h"] >= before["ok"], (m["ok"], before)
        assert m["down"]["state"] == "down" and m["ok"]["last"] is not None
        s, j = jreq("GET", "/api/monitors/flaky/history?limit=500")
        assert len(j["history"]) >= 5, len(j["history"])
        ok("restart: the added monitor kept, the deleted gone, states and history reloaded")
        stop(p)
    finally:
        if p.poll() is None: p.kill()

# The soak
# --------

def proc_stat(pid):
    f = open("/proc/%d/stat" % pid).read().rsplit(")", 1)[1].split()
    rss = int(open("/proc/%d/status" % pid).read().split("VmRSS:")[1].split()[0])
    return (int(f[11]) + int(f[12])) / os.sysconf("SC_CLK_TCK"), rss

def soak(cmd, d, secs, n, every):
    cfg = config(d, n_extra=n, every=every)
    p = start(cmd, d, cfg)
    try:
        t0 = time.time(); c0, r0 = proc_stat(p.pid)
        samples = []
        while time.time() - t0 < secs:
            time.sleep(min(15, secs / 8))
            c, r = proc_stat(p.pid)
            samples.append((round(time.time() - t0), r))
        c1, r1 = proc_stat(p.pid)
        el = time.time() - t0
        m = mons()
        code = stop(p, 15)
        if code != 0: print("  SIGTERM: %s" % code)
    finally:
        if p.poll() is None: p.kill()
    rows = [json.loads(l) for l in open(os.path.join(d, "u.results.ndjson"))]
    by = {}
    for r in rows: by.setdefault(r["name"], []).append(r)
    gaps, lags = [], []
    for name, rs in by.items():
        if not name.startswith("m"): continue
        lags += [r["lag"] for r in rs[1:]]
        gaps += [b["t"] - a["t"] for a, b in zip(rs, rs[1:])]
    gaps.sort(); lags.sort()
    q = lambda xs, f: xs[min(len(xs) - 1, int(len(xs) * f))]
    exp = n * el * 1000 / every
    got = sum(len(by.get("m%02d" % i, [])) for i in range(n))
    print("soak: %d monitors every %d ms for %.0f s; %d probes of %.0f expected (%.1f%%)" % (n, every, el, got, exp, 100 * got / exp))
    print("  RSS: %d KiB at start, %d KiB at the end; samples (s, KiB): %s" % (r0, r1, samples))
    print("  CPU: %.2f s over %.0f s (%.1f%% of a core)" % (c1 - c0, el, 100 * (c1 - c0) / el))
    print("  start lag past the slot (ms): p50 %d, p99 %d, max %d" % (q(lags, .5), q(lags, .99), lags[-1]))
    print("  gap between probes (ms): p1 %d, p50 %d, p99 %d, max %d" % (q(gaps, .01), q(gaps, .5), q(gaps, .99), gaps[-1]))
    print("  log: %d lines, %d bytes" % (len(rows), os.path.getsize(os.path.join(d, "u.results.ndjson"))))
    t = time.time()
    p = start(cmd, d, cfg)
    print("  restart with that log: /health answered after %.2f s" % (time.time() - t))
    stop(p, 15)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--bin", help="the built app")
    ap.add_argument("--js", action="store_true", help="run on the JS lane: bun bend2/main.ts apps/uptime/main.bend")
    ap.add_argument("--soak", type=int, default=0, help="seconds of 50 monitors at 1 s")
    ap.add_argument("--monitors", type=int, default=50)
    ap.add_argument("--every", type=int, default=1000, help="the soak's interval, ms")
    ap.add_argument("--keep", action="store_true")
    ap.add_argument("--tmp", help="the directory to make the state directory in")
    ap.add_argument("--port-base", type=int, default=29400, help="the ports: N+10 and N+11 the targets, N+20 the app")
    a = ap.parse_args()
    global TGT, DOWN, APP
    TGT, DOWN, APP = a.port_base + 10, a.port_base + 11, a.port_base + 20
    cmd = ["bun", os.path.join(ROOT, "bend2/main.ts"), os.path.join(ROOT, "apps/uptime/main.bend"), "--"] if a.js \
        else [os.path.abspath(a.bin)]
    d = tempfile.mkdtemp(prefix="uptime-", dir=a.tmp)
    srv = targets()
    try:
        if a.soak:
            soak(cmd, d, a.soak, a.monitors, a.every)
        else:
            checks(cmd, d)
            print("PASS: %d / %d" % (len(PASS), len(PASS) + len(FAIL)))
            if FAIL: sys.exit(1)
    finally:
        srv.shutdown()
        if a.keep: print("kept " + d)
        else: shutil.rmtree(d, ignore_errors=True)

if __name__ == "__main__":
    main()
