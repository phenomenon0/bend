"""The echo-record upstream: a backend that records the exact raw bytes a front
forwards on each connection, frames them with the RFC 9112 reference parser
(refparse, an opinion independent of the Bend spec), and answers each request
with a small response naming the request's index and the byte range it framed.

It emits a JSONL event log (one line per event) that the driver tails:
  {"ev":"req",   "conn":C, "seq":S, "ts":T, "method":..., "target":...,
                 "body_len":..., "start":..., "end":..., "req_b64":...}
  {"ev":"error", "conn":C, "ts":T, "code":..., "off":..., "why":...,
                 "raw_b64":...}
  {"ev":"close", "conn":C, "ts":T, "nreq":N, "raw_b64":...}

A front desyncs when the requests recorded here for one corpus entry do not
match what the reference frames on that entry's own client bytes, or when the
client saw a different number of responses than the upstream framed requests.

Usage: python3 upstream.py --port 20410 --log <path> [--host 127.0.0.1]
"""

import argparse
import base64
import json
import socket
import threading
import time

import refparse

_conn_seq = 0
_lock = threading.Lock()


def _next_conn():
    global _conn_seq
    with _lock:
        _conn_seq += 1
        return _conn_seq


class Log:
    def __init__(self, path):
        self.f = open(path, "a", buffering=1)
        self.lk = threading.Lock()

    def emit(self, obj):
        line = json.dumps(obj)
        with self.lk:
            self.f.write(line + "\n")
            self.f.flush()


def _response(conn, seq, req):
    body = json.dumps({
        "conn": conn, "idx": seq,
        "method": req.method.decode("latin1"),
        "target": req.target.decode("latin1"),
        "range": [req.start, req.end],
        "body_len": req.body_len,
    }).encode()
    return (b"HTTP/1.1 200 OK\r\n"
            b"Content-Type: application/json\r\n"
            b"Content-Length: " + str(len(body)).encode() + b"\r\n"
            b"Connection: keep-alive\r\n\r\n" + body)


def _bad():
    body = b'{"upstream":"framing rejected"}'
    return (b"HTTP/1.1 400 Bad Request\r\n"
            b"Content-Type: application/json\r\n"
            b"Content-Length: " + str(len(body)).encode() + b"\r\n"
            b"Connection: close\r\n\r\n" + body)


def handle(sock, log):
    cid = _next_conn()
    sock.settimeout(2.0)
    buf = b""
    responded = 0
    try:
        while True:
            try:
                chunk = sock.recv(65536)
            except socket.timeout:
                break
            if not chunk:
                break
            buf += chunk
            reqs, status, err = refparse.frame(buf)
            # answer any newly complete requests
            for i in range(responded, len(reqs)):
                r = reqs[i]
                log.emit({
                    "ev": "req", "conn": cid, "seq": i, "ts": time.time(),
                    "method": r.method.decode("latin1"),
                    "target": r.target.decode("latin1"),
                    "body_len": r.body_len, "start": r.start, "end": r.end,
                    "req_b64": base64.b64encode(buf[r.start:r.end]).decode(),
                })
                try:
                    sock.sendall(_response(cid, i, r))
                except OSError:
                    break
            responded = len(reqs)
            if status == "error":
                log.emit({
                    "ev": "error", "conn": cid, "ts": time.time(),
                    "code": err.code, "off": err.off, "why": err.why,
                    "raw_b64": base64.b64encode(buf).decode(),
                })
                try:
                    sock.sendall(_bad())
                except OSError:
                    pass
                break
    finally:
        log.emit({
            "ev": "close", "conn": cid, "ts": time.time(),
            "nreq": responded, "raw_b64": base64.b64encode(buf).decode(),
        })
        try:
            sock.close()
        except OSError:
            pass


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--host", default="127.0.0.1")
    ap.add_argument("--port", type=int, required=True)
    ap.add_argument("--log", required=True)
    args = ap.parse_args()

    log = Log(args.log)
    srv = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    srv.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    srv.bind((args.host, args.port))
    srv.listen(128)
    print("echo-record upstream on %s:%d log=%s" % (args.host, args.port, args.log),
          flush=True)
    try:
        while True:
            cli, _ = srv.accept()
            threading.Thread(target=handle, args=(cli, log), daemon=True).start()
    except KeyboardInterrupt:
        pass
    finally:
        srv.close()


if __name__ == "__main__":
    main()
