"""The HTTP/2 downgrade driver: replay the h2 corpus scripts through the `h2`
package at an h2-capable front (an nginx h2c listener that proxies to the
HTTP/1.1 echo-record upstream), and see what survives the downgrade.

The vectors are H2.CL / H2.TE and the h2 abuses: a content-length that
disagrees with the DATA length, transfer-encoding in h2 headers, CRLF injection
in a header value or the :path, and pseudo-header abuse. `h2` is configured with
all outbound validation OFF so the malformed frames actually reach the front.

Classification mirrors the HTTP/1 driver:
  reject       front refused the stream (RST/GOAWAY/4xx, forwarded nothing)
  clean        front forwarded a single clean HTTP/1.1 request upstream
  desync/fwd_reject  front forwarded something the RFC would not, or forwarded
                     a different shape than the h2 request implies

Usage: python3 h2driver.py --out results [--work DIR]
"""

import argparse
import base64
import json
import os
import socket
import subprocess
import sys
import time

import fronts

try:
    import h2.connection
    import h2.config
    HAVE_H2 = True
except Exception:
    HAVE_H2 = False

HERE = os.path.dirname(os.path.abspath(__file__))
CORPUS = os.path.join(HERE, "corpus")
UP_PORT = 20412
FRONT_PORT = 20420


def load_h2_entries():
    with open(os.path.join(CORPUS, "index.json")) as f:
        idx = json.load(f)
    out = []
    for e in idx["entries"]:
        if e["kind"] == "h2":
            with open(os.path.join(CORPUS, e["file"])) as f:
                e["script"] = json.load(f)
            out.append(e)
    return out


def send_h2(port, script, timeout=2.0):
    """Replay an h2 script with prior-knowledge h2c. Returns
    (status_or_None, events) where events is a list of strings."""
    cfg = h2.config.H2Configuration(
        client_side=True,
        validate_outbound_headers=False,
        normalize_outbound_headers=False,
        validate_inbound_headers=False,
        header_encoding="latin1")
    conn = h2.connection.H2Connection(config=cfg)
    events = []
    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    s.settimeout(timeout)
    status = None
    try:
        s.connect(("127.0.0.1", port))
        conn.initiate_connection()
        s.sendall(conn.data_to_send())
        sid = 1
        for op in script:
            headers = [(k, v) for k, v in op["headers"]]
            end = op.get("end_stream", True) and "body" not in op
            conn.send_headers(sid, headers, end_stream=end)
            s.sendall(conn.data_to_send())
            if "body" in op:
                conn.send_data(sid, op["body"].encode("latin1"),
                               end_stream=op.get("end_stream", True))
                s.sendall(conn.data_to_send())
        # read responses / resets
        deadline = time.time() + timeout
        while time.time() < deadline:
            try:
                data = s.recv(65536)
            except socket.timeout:
                break
            if not data:
                break
            for ev in conn.receive_data(data):
                cn = type(ev).__name__
                events.append(cn)
                if cn == "ResponseReceived":
                    for k, v in ev.headers:
                        if k == ":status":
                            status = int(v)
                if cn in ("StreamReset", "ConnectionTerminated"):
                    deadline = 0
            try:
                s.sendall(conn.data_to_send())
            except OSError:
                break
    except Exception as e:
        events.append("EXC:%s" % type(e).__name__)
    finally:
        try:
            s.close()
        except OSError:
            pass
    return status, events


class Tail:
    def __init__(self, path):
        self.path = path
        self.pos = 0

    def mark(self):
        try:
            self.pos = os.path.getsize(self.path)
        except OSError:
            self.pos = 0

    def collect(self):
        evs = []
        try:
            with open(self.path, "rb") as f:
                f.seek(self.pos)
                for line in f.read().splitlines():
                    line = line.strip()
                    if line:
                        try:
                            evs.append(json.loads(line))
                        except ValueError:
                            pass
                self.pos = f.tell()
        except OSError:
            pass
        return evs


def classify(entry, status, events, up_events):
    up_reqs = [e for e in up_events if e.get("ev") == "req"]
    up_err = any(e.get("ev") == "error" for e in up_events)
    fwd = len(up_reqs)
    reset = any(e in ("StreamReset", "ConnectionTerminated") for e in events)
    detail = {"expect": entry["expect"], "h2_status": status,
              "h2_events": events, "forwarded": fwd,
              "up_targets": [e["target"] for e in up_reqs],
              "up_body_len": [e["body_len"] for e in up_reqs],
              "up_error": up_err}

    front_refused = fwd == 0 and (reset or (status is not None and status >= 400)
                                  or status is None)
    if entry["expect"].startswith("accept"):
        if fwd == 1 and not up_err and status and status < 400:
            return "clean", detail
        if fwd == 0:
            return "reject", detail
        return "desync", detail

    # expect reject
    if fwd == 0:
        return "reject", detail
    # forwarded something the RFC/h2 rules should have stopped
    smuggled = any("HTTP/1.1" in t or "\r" in t for t in detail["up_targets"])
    return ("desync" if smuggled else "fwd_reject"), detail


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=os.path.join(HERE, "results"))
    ap.add_argument("--work", default="/tmp/claude-0/proxyh2")
    args = ap.parse_args()

    if not HAVE_H2:
        print("the h2 package is not importable; skipping h2 vectors",
              file=sys.stderr)
        return 0

    os.makedirs(args.out, exist_ok=True)
    os.makedirs(args.work, exist_ok=True)
    entries = load_h2_entries()
    up_log = os.path.join(args.work, "upstream.jsonl")
    open(up_log, "w").close()

    up = subprocess.Popen(
        ["taskset", "-c", "1", sys.executable,
         os.path.join(HERE, "upstream.py"),
         "--port", str(UP_PORT), "--log", up_log],
        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    if not fronts.wait_port("127.0.0.1", UP_PORT):
        print("upstream failed", file=sys.stderr)
        return 1

    fr = fronts.NginxH2(args.work, FRONT_PORT, UP_PORT, pin_core=0)
    results = []
    try:
        if not fr.start():
            print("nginx h2 front failed to start", file=sys.stderr)
            return 1
        tail = Tail(up_log)
        for e in entries:
            tail.mark()
            status, events = send_h2(FRONT_PORT, e["script"])
            time.sleep(0.1)
            up_events = tail.collect()
            label, detail = classify(e, status, events, up_events)
            results.append({"seq": e["seq"], "family": e["family"],
                            "name": e["name"], "label": label, "detail": detail})
            print("  [%s] %s/%s -> %s (status=%s fwd=%d)" % (
                e["expect"], e["family"], e["name"], label, status,
                detail["forwarded"]), flush=True)
    finally:
        fr.stop()
        up.terminate()
        try:
            up.wait(timeout=3)
        except Exception:
            up.kill()

    with open(os.path.join(args.out, "detail_nginx_h2.json"), "w") as f:
        json.dump(results, f, indent=1)
    _md(results, args.out)
    return 0


def _md(results, out):
    from collections import Counter
    fam = {}
    for r in results:
        fam.setdefault(r["family"], Counter())[r["label"]] += 1
    lines = ["# HTTP/2 downgrade vectors (nginx h2c front)", "",
             "Replayed via the `h2` package with outbound validation off. "
             "`forwarded` is what the HTTP/1.1 upstream recorded after the "
             "downgrade.", "",
             "| family | reject | clean | desync | fwd_reject |",
             "|---|---|---|---|---|"]
    for f in sorted(fam):
        c = fam[f]
        lines.append("| %s | %d | %d | %d | %d |" % (
            f, c["reject"], c["clean"], c["desync"], c["fwd_reject"]))
    notable = [r for r in results if r["label"] in ("desync", "fwd_reject")]
    if notable:
        lines += ["", "## notable", "",
                  "A `fwd_reject` with `forwarded == 1` and no smuggled "
                  "HTTP/1.1 request in the target means the front **sanitised** "
                  "the vector: it dropped the forbidden header (transfer-"
                  "encoding, connection) and forwarded a single clean length-"
                  "delimited request. A `desync` would be an actual smuggled "
                  "second request at the backend.", ""]
        for r in notable:
            lines.append("- `%s / %s`: **%s** up_targets=%r body=%r" % (
                r["family"], r["name"], r["label"],
                r["detail"]["up_targets"], r["detail"]["up_body_len"]))
    with open(os.path.join(out, "matrix_h2.md"), "w") as f:
        f.write("\n".join(lines) + "\n")


if __name__ == "__main__":
    sys.exit(main())
