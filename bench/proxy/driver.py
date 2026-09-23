"""The differential driver: send every corpus entry to each front, capture the
client-visible response and what the echo-record upstream recorded, and classify
the front's behaviour against the RFC 9112 reference.

Classes:
  reject       the front refused the entry (4xx, forwarded nothing upstream)
  clean        the front forwarded exactly the boundaries the reference frames
  desync       the upstream framed a different number/boundaries than the
               reference frames on the client bytes, or the client saw a
               different response count than the upstream framed requests
  fwd_reject   the front forwarded (>=1 request) something the reference rejects

For the Bend httpd (a direct server, no upstream) the axis is accept/reject
against the reference on the same bytes:
  match_accept   both accept, same request count
  match_reject   both reject
  httpd_stricter reference accepts, httpd rejects (conservative, safe)
  httpd_looser   reference rejects, httpd accepts (the dangerous direction)

Writes results/matrix_<mode>.json and a combined results/matrix.md.

Usage:
  python3 driver.py --fronts nginx,haproxy,bend_httpd \\
      --httpd /path/to/httpd --out results
"""

import argparse
import base64
import json
import os
import re
import socket
import subprocess
import sys
import time

import fronts
import refparse

HERE = os.path.dirname(os.path.abspath(__file__))
CORPUS = os.path.join(HERE, "corpus")
UP_PORT = 20410
FRONT_PORT = 20420
STATUS_RE = re.compile(rb"^HTTP/1\.[01] (\d{3})", re.M)


def load_corpus():
    with open(os.path.join(CORPUS, "index.json")) as f:
        idx = json.load(f)
    return idx["entries"]


def send_raw(port, data, idle=0.3, cap=2.0):
    """Open a client connection, send the bytes, drain the response. Stops
    when the peer closes, or after `idle` seconds with no new bytes (a
    keep-alive peer holds the connection open, so we cannot wait for close),
    or after a hard cap."""
    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    s.settimeout(idle)
    out = b""
    try:
        s.connect(("127.0.0.1", port))
        s.sendall(data)
        # NB: do not half-close the write side. nginx treats a client
        # half-close mid-request as the client going away and aborts the
        # proxied request, so we rely on the idle timeout below instead.
        end = time.time() + cap
        while time.time() < end:
            try:
                chunk = s.recv(65536)
            except socket.timeout:
                break            # idle: assume the response is complete
            if not chunk:
                break            # peer closed
            out += chunk
    except OSError:
        pass
    finally:
        s.close()
    return out


def frame_responses(resp):
    """Count well-formed HTTP responses in a client byte stream and collect
    their status codes. Responses here come from real servers, so a lenient
    Content-Length / close walk is enough."""
    statuses = []
    p = 0
    n = len(resp)
    while p < n:
        m = re.match(rb"HTTP/1\.[01] (\d{3})", resp[p:])
        if not m:
            break
        statuses.append(int(m.group(1)))
        hend = resp.find(b"\r\n\r\n", p)
        if hend < 0:
            break
        head = resp[p:hend]
        clm = re.search(rb"[Cc]ontent-[Ll]ength:\s*(\d+)", head)
        if b"chunked" in head.lower():
            # walk to terminating 0-chunk
            q = hend + 4
            while True:
                nl = resp.find(b"\r\n", q)
                if nl < 0:
                    q = n
                    break
                size = resp[q:nl].split(b";")[0].strip()
                try:
                    sz = int(size, 16)
                except ValueError:
                    q = n
                    break
                q = nl + 2
                if sz == 0:
                    e = resp.find(b"\r\n\r\n", q - 2)
                    q = (e + 4) if e >= 0 else n
                    break
                q += sz + 2
            p = q
        elif clm:
            p = hend + 4 + int(clm.group(1))
        else:
            p = n
    return statuses


class UpstreamTail:
    """Tail the upstream event log and slice out events per driver window."""
    def __init__(self, path):
        self.path = path
        self.pos = 0

    def mark(self):
        try:
            self.pos = os.path.getsize(self.path)
        except OSError:
            self.pos = 0

    def collect(self):
        events = []
        try:
            with open(self.path, "rb") as f:
                f.seek(self.pos)
                data = f.read()
                self.pos = f.tell()
        except OSError:
            return events
        for line in data.splitlines():
            line = line.strip()
            if not line:
                continue
            try:
                events.append(json.loads(line))
            except ValueError:
                pass
        return events


# statuses that mean the front/server refused to frame the message, as opposed
# to an ordinary application answer (404/405/426) to a request it did frame.
REJECT_STATUS = {400, 413, 414, 431, 501, 505}


def classify_proxy(entry, client_resp, up_events):
    ref = entry["expect"]
    up_reqs = [e for e in up_events if e.get("ev") == "req"]
    up_err = any(e.get("ev") == "error" for e in up_events)
    statuses = frame_responses(client_resp)
    fwd = len(up_reqs)
    up_targets = [e["target"] for e in up_reqs]
    up_bodies = [e["body_len"] for e in up_reqs]

    detail = {"ref": ref, "forwarded": fwd, "up_targets": up_targets,
              "up_bodies": up_bodies, "client_statuses": statuses,
              "up_error": up_err}

    if ref.startswith("accept:"):
        want = int(ref.split(":")[1])
        # reference body lengths on the client bytes, for boundary comparison.
        _d, ref_reqs, _e = refparse.disposition(entry_bytes(entry))
        ref_bodies = [r.body_len for r in ref_reqs]
        if fwd == 0:
            # the front refused (stricter than the reference). Safe: it is not
            # forwarding a different framing, it is forwarding nothing.
            return "front_stricter", detail
        if fwd == want and not up_err and up_bodies == ref_bodies:
            # same request count and same body boundaries: a clean forward.
            # Targets may be rewritten (absolute-form -> origin-form) legitimately.
            return "clean", detail
        # a different number of requests, or a shifted body boundary, reached
        # the backend than the reference frames on the client bytes.
        detail["note"] = "want %d bodies %r, got %d bodies %r" % (
            want, ref_bodies, fwd, up_bodies)
        return "desync", detail

    # reference rejects the client bytes
    if fwd == 0:
        # the front refused before forwarding: the correct outcome.
        return "reject", detail
    # the front forwarded >=1 request the reference will not frame.
    return "fwd_reject", detail


def classify_httpd(entry, client_resp):
    ref = entry["expect"]
    statuses = frame_responses(client_resp)
    n_resp = len(statuses)
    # a request is "framed and accepted" if it drew any answer that is not a
    # framing refusal; a 404/405/426 still means the httpd parsed a request.
    accepted = [s for s in statuses if s not in REJECT_STATUS]
    reject_seen = any(s in REJECT_STATUS for s in statuses)
    detail = {"ref": ref, "client_statuses": statuses}

    if ref.startswith("accept:"):
        want = int(ref.split(":")[1])
        if len(accepted) == want and not reject_seen:
            return "match_accept", detail
        if len(accepted) < want or reject_seen or n_resp == 0:
            # httpd framed fewer requests, or refused: stricter than the RFC.
            return "httpd_stricter", detail
        detail["note"] = "accepted %d > %d" % (len(accepted), want)
        return "httpd_looser", detail

    # reference rejects the stream
    if len(accepted) == 0 or reject_seen or n_resp == 0:
        return "match_reject", detail
    # the httpd framed and answered a request the reference refuses to frame.
    detail["note"] = "accepted %d (statuses %r) for a reject stream" % (
        len(accepted), statuses)
    return "httpd_looser", detail


_BYTES_CACHE = {}


def entry_bytes(entry):
    if entry["seq"] in _BYTES_CACHE:
        return _BYTES_CACHE[entry["seq"]]
    b = base64.b64decode(entry["bytes_b64"])
    _BYTES_CACHE[entry["seq"]] = b
    return b


def run_front(front, entries, up_tail=None):
    results = []
    for e in entries:
        if e["kind"] != "raw":
            continue   # h2 entries handled by h2driver.py
        data = entry_bytes(e)
        if up_tail is not None:
            up_tail.mark()
        resp = send_raw(front.front_port, data)
        time.sleep(0.05)
        if front.is_proxy:
            evs = up_tail.collect() if up_tail else []
            label, detail = classify_proxy(e, resp, evs)
        else:
            label, detail = classify_httpd(e, resp)
        results.append({"seq": e["seq"], "family": e["family"],
                        "name": e["name"], "label": label, "detail": detail})
    return results


def matrix(results):
    """family -> label -> count."""
    m = {}
    for r in results:
        m.setdefault(r["family"], {})
        m[r["family"]][r["label"]] = m[r["family"]].get(r["label"], 0) + 1
    return m


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--fronts", default="nginx,haproxy,bend_httpd")
    ap.add_argument("--httpd", default=None)
    ap.add_argument("--out", default=os.path.join(HERE, "results"))
    ap.add_argument("--work", default="/tmp/claude-0/proxybench")
    ap.add_argument("--render", action="store_true",
                    help="rebuild matrix.md/json from existing detail_*.json, "
                         "without running any front")
    args = ap.parse_args()

    os.makedirs(args.out, exist_ok=True)
    os.makedirs(args.work, exist_ok=True)
    entries = load_corpus()
    want = args.fronts.split(",")

    if args.render:
        mats, dets = {}, {}
        for w in want:
            p = os.path.join(args.out, "detail_%s.json" % w)
            if not os.path.exists(p):
                continue
            with open(p) as f:
                res = json.load(f)
            dets[w] = res
            mats[w] = matrix(res)
        with open(os.path.join(args.out, "matrix.json"), "w") as f:
            json.dump(mats, f, indent=1)
        write_markdown(entries, mats, dets, args.out)
        print("rendered", os.path.join(args.out, "matrix.md"))
        return 0

    all_matrices = {}
    all_details = {}

    # upstream for the proxy fronts
    up_log = os.path.join(args.work, "upstream.jsonl")
    open(up_log, "w").close()
    up_proc = None
    if any(w in ("nginx", "haproxy") for w in want):
        up_proc = subprocess.Popen(
            ["taskset", "-c", "1", sys.executable,
             os.path.join(HERE, "upstream.py"),
             "--port", str(UP_PORT), "--log", up_log],
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        if not fronts.wait_port("127.0.0.1", UP_PORT):
            print("upstream failed to start", file=sys.stderr)
            return 1

    try:
        for w in want:
            if w == "nginx":
                fr = fronts.Nginx(args.work, FRONT_PORT, UP_PORT, pin_core=0)
            elif w == "haproxy":
                fr = fronts.HAProxy(args.work, FRONT_PORT, UP_PORT, pin_core=0)
            elif w == "bend_httpd":
                if not args.httpd:
                    print("skip bend_httpd: no --httpd binary", file=sys.stderr)
                    continue
                fr = fronts.BendHttpd(args.work, FRONT_PORT, args.httpd, pin_core=0)
            else:
                print("unknown front", w, file=sys.stderr)
                continue
            print("== front:", w, "==", flush=True)
            if not fr.start():
                print("  failed to start", w, file=sys.stderr)
                fr.stop()
                continue
            tail = UpstreamTail(up_log) if fr.is_proxy else None
            try:
                res = run_front(fr, entries, tail)
            finally:
                fr.stop()
            all_matrices[w] = matrix(res)
            all_details[w] = res
            with open(os.path.join(args.out, "detail_%s.json" % w), "w") as f:
                json.dump(res, f, indent=1)
    finally:
        if up_proc:
            up_proc.terminate()
            try:
                up_proc.wait(timeout=3)
            except Exception:
                up_proc.kill()

    with open(os.path.join(args.out, "matrix.json"), "w") as f:
        json.dump(all_matrices, f, indent=1)
    write_markdown(entries, all_matrices, all_details, args.out)
    print("wrote", os.path.join(args.out, "matrix.md"))
    return 0


def write_markdown(entries, matrices, details, out):
    fams = sorted(set(e["family"] for e in entries if e["kind"] == "raw"))
    counts = {}
    for e in entries:
        if e["kind"] == "raw":
            counts[e["family"]] = counts.get(e["family"], 0) + 1
    lines = ["# Proxy differential matrix", ""]
    lines.append("Each cell is the count of corpus entries in that family that "
                 "produced each disposition at that front. Reference is the "
                 "strict RFC 9112 framer in `refparse.py`.")
    lines.append("")
    proxy_labels = ["clean", "reject", "front_stricter", "desync", "fwd_reject"]
    httpd_labels = ["match_accept", "match_reject", "httpd_stricter",
                    "httpd_looser"]
    for name, m in matrices.items():
        is_httpd = name == "bend_httpd"
        labels = httpd_labels if is_httpd else proxy_labels
        lines.append("")
        lines.append("## %s" % name)
        lines.append("")
        lines.append("| family | n | " + " | ".join(labels) + " |")
        lines.append("|" + "---|" * (len(labels) + 2))
        for fam in fams:
            row = m.get(fam, {})
            cells = [str(row.get(l, 0)) for l in labels]
            lines.append("| %s | %d | %s |" % (fam, counts[fam], " | ".join(cells)))
        # flag notable rows, and tell apart active smuggling from mere leniency
        flagged = []
        smuggles = 0
        for r in details.get(name, []):
            if r["label"] not in ("desync", "fwd_reject", "httpd_looser"):
                continue
            d = r["detail"]
            fwd = d.get("forwarded")
            if not is_httpd and r["label"] == "fwd_reject":
                # a reject-stream the front forwarded: active smuggling only if
                # the backend saw more than the one request or errored on it.
                active = (fwd is not None and fwd != 1) or d.get("up_error")
                tag = "SMUGGLE" if active else "normalized (backend saw %s req)" % fwd
                if active:
                    smuggles += 1
                flagged.append("- `%s / %s`: **%s** -- %s; up_targets=%r" % (
                    r["family"], r["name"], r["label"], tag, d.get("up_targets")))
            elif not is_httpd and r["label"] == "desync":
                smuggles += 1
                flagged.append("- `%s / %s`: **desync** -- %s" % (
                    r["family"], r["name"], d.get("note", "")))
            else:
                flagged.append("- `%s / %s`: **%s** %s" % (
                    r["family"], r["name"], r["label"], d.get("note", "")))
        if flagged:
            lines.append("")
            lines.append("### notable at %s" % name)
            if not is_httpd:
                lines.append("")
                lines.append("Active smuggling (backend framed a request count "
                             "the front did not answer, or the backend errored): "
                             "**%d**. The rest are leniency: the front accepted a "
                             "stream the strict reference rejects but normalised "
                             "it to a single clean request before forwarding." %
                             smuggles)
            lines.append("")
            lines.extend(flagged)
    with open(os.path.join(out, "matrix.md"), "w") as f:
        f.write("\n".join(lines) + "\n")


if __name__ == "__main__":
    sys.exit(main())
