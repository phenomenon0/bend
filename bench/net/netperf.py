#!/usr/bin/env python3
"""The networking stack's cost per request, counted rather than timed.

    python3 bench/net/netperf.py [--bin DIR] [--pin] [--only a,b] [--hw NAME]
                                 [--reps N] [--wrk SECS]

wrk on a shared box swings by a fifth from run to run; an instruction
count does not. Each bench starts its server alone, on one thread, under
callgrind, drives it with one client over one keep-alive connection, one
request at a time (so every read and write is the same in every run),
and does it twice: LO requests and HI. What the two runs differ by,
over HI - LO, is what one request costs: the server's start, its first
connection and its shutdown are in both and cancel. Syscalls are
counted the same way, under strace -f -c.

The benches: the engine's /health, a 4 KiB file, a 1 MiB file, a gzip
hit (a text file under --gzip, the peer taking gzip), a 304 (If-None-Match
with the file's entity-tag) and a 206 (a 100-byte range); net/'s hello
and its JSON API (GET /notes/1); bend-h2's /health over h2c.

It builds the four programs into DIR (a temporary directory by default;
a binary already there is kept), compares each count with the pin in
_pin_/HW.txt and exits 1 when an instruction count is more than 2% over
its pin, or a syscall count more than 0.1 a request over. --pin runs
every bench three times and writes the medians; --reps N runs each N
times and prints the spread, (max - min) / median. --wrk SECS adds
wrk's requests a second (one thread, 32 connections, the server on one
thread), which a loaded box moves by a fifth: a hint, never a verdict.
The callgrind files stay in DIR (cg.LO.out, cg.HI.out) for
callgrind_annotate. Needs valgrind and strace, and the h2 package for
the h2 bench. Uses ports 26000-26099 and kills every process it starts.
"""
import os, signal, socket, subprocess, sys, tempfile, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
ARGS = sys.argv[1:]

def arg(name, default):
    return ARGS[ARGS.index(name) + 1] if name in ARGS else default

BIN = arg("--bin", None) or tempfile.mkdtemp(prefix="bend-netperf-")
HW = arg("--hw", "linux_x86_64")
PIN = "--pin" in ARGS
ONLY = [x for x in arg("--only", "").split(",") if x]
LO, HI = int(arg("--lo", "100")), int(arg("--hi", "600"))
REPS = int(arg("--reps", "3" if PIN else "1"))
WRK = int(arg("--wrk", "0"))
SLACK = 1.02
SYS_SLACK = 0.1
PORT = [26000]
PROCS = []
PIDS = set()

SOURCES = {
    "httpd": "demos/io_http_engine/main.bend",
    "hello": "net/examples/hello.bend",
    "notes": "net/examples/json_api.bend",
    "h2d": "demos/io_http2/main.bend",
}

def build(name):
    out = os.path.join(BIN, name)
    if not os.path.exists(out):
        r = subprocess.run(["bun", os.path.join(ROOT, "bend2/main.ts"), os.path.join(ROOT, SOURCES[name]),
                            "-o", out], capture_output=True, text=True)
        if not os.path.exists(out):
            sys.exit("could not build " + SOURCES[name] + "\n" + r.stdout + r.stderr)
    return out

# The fixtures: a 4 KiB text file and a 1 MiB binary one
WWW = os.path.join(BIN, "www")

def fixtures():
    os.makedirs(WWW, exist_ok=True)
    line = b"the quick brown fox jumps over the lazy dog, again and again\n"
    with open(os.path.join(WWW, "f4k.txt"), "wb") as f:
        f.write((line * 80)[:4096])
    with open(os.path.join(WWW, "f1m.bin"), "wb") as f:
        f.write(bytes((i * 7) % 251 for i in range(1 << 20)))
    # a fixed mtime, so the entity-tag and Last-Modified are the same every run
    for n in ("f4k.txt", "f1m.bin"):
        os.utime(os.path.join(WWW, n), (1700000000, 1700000000))

# The Client
# ==========

def connect(port, tries=600):
    for _ in range(tries):
        try:
            return socket.create_connection(("127.0.0.1", port), timeout=30)
        except OSError:
            time.sleep(0.05)
    raise SystemExit("never listened on %d" % port)

# Each request is sent only once the server sleeps in its poller, so it
# always takes the same path to it (a read that finds nothing, the wait,
# the wake): which one it took would otherwise turn on a race between
# the client's next send and the server's next read.
SERVER = [0]
WAITS = (7, 23, 232, 270, 271, 281)

def idle(tries=100000):
    pid = SERVER[0]
    for _ in range(tries):
        try:
            ts = os.listdir("/proc/%d/task" % pid)
            st = [open("/proc/%d/task/%s/stat" % (pid, t)).read().rsplit(")", 1)[1].split()[0] for t in ts]
            sc = [open("/proc/%d/task/%s/syscall" % (pid, t)).read().split()[0] for t in ts]
        except (OSError, IndexError):
            time.sleep(0.0002)
            continue
        if all(x == "S" for x in st) and any(x.isdigit() and int(x) in WAITS for x in sc):
            return
        time.sleep(0.0002)
    try:
        why = [(open("/proc/%d/task/%s/stat" % (pid, t)).read().rsplit(")", 1)[1].split()[0],
                open("/proc/%d/task/%s/syscall" % (pid, t)).read().split()[0]) for t in os.listdir("/proc/%d/task" % pid)]
    except OSError:
        why = "it is gone"
    raise SystemExit("the server never went back to its poller: %s" % (why,))

def read_reply(s, buf, head_only):
    """one HTTP/1.1 reply off s: its head and body; what is left of buf"""
    while b"\r\n\r\n" not in buf:
        got = s.recv(1 << 20)
        if not got:
            raise SystemExit("the server closed mid-reply")
        buf += got
    i = buf.index(b"\r\n\r\n") + 4
    head, buf = buf[:i], buf[i:]
    n = 0
    for ln in head.split(b"\r\n"):
        if ln.lower().startswith(b"content-length:"):
            n = int(ln.split(b":", 1)[1])
    if head_only or head.startswith(b"HTTP/1.1 304"):
        n = 0
    while len(buf) < n:
        got = s.recv(1 << 20)
        if not got:
            raise SystemExit("the server closed mid-body")
        buf += got
    return head, buf[:n], buf[n:]

def h1(port, req, n, setup=()):
    s = connect(port)
    buf = b""
    for r in setup:
        idle()
        s.sendall(r)
        head, body, buf = read_reply(s, buf, False)
    for _ in range(n):
        idle()
        s.sendall(req)
        head, body, buf = read_reply(s, buf, False)
        if not head.startswith(b"HTTP/1.1 2") and not head.startswith(b"HTTP/1.1 304"):
            raise SystemExit("unexpected reply: %r" % head[:200])
    s.close()
    return head

def h2(port, path, n, setup=()):
    import h2.config, h2.connection, h2.events
    s = connect(port)
    c = h2.connection.H2Connection(h2.config.H2Configuration(client_side=True))
    c.initiate_connection()
    s.sendall(c.data_to_send())
    for i in range(n):
        idle()
        sid = c.get_next_available_stream_id()
        c.send_headers(sid, [(":method", "GET"), (":path", path), (":scheme", "http"),
                             (":authority", "127.0.0.1")], end_stream=True)
        s.sendall(c.data_to_send())
        done = False
        while not done:
            got = s.recv(1 << 16)
            if not got:
                raise SystemExit("h2: the server closed")
            for e in c.receive_data(got):
                if isinstance(e, h2.events.DataReceived):
                    c.acknowledge_received_data(e.flow_controlled_length, e.stream_id)
                if isinstance(e, h2.events.StreamEnded) and e.stream_id == sid:
                    done = True
            out = c.data_to_send()
            if out:
                s.sendall(out)
    s.close()

def etag(port):
    head = h1(port, b"GET /f4k.txt HTTP/1.1\r\nhost: x\r\n\r\n", 1)
    for ln in head.split(b"\r\n"):
        if ln.lower().startswith(b"etag:"):
            return ln.split(b":", 1)[1].strip()
    raise SystemExit("no etag on /f4k.txt")

def get(path, extra=b""):
    return b"GET " + path + b" HTTP/1.1\r\nhost: x\r\n" + extra + b"\r\n"

# The Benches
# ===========
# name: (program, its flags, the drive: port, n -> ())

GZ = b"accept-encoding: gzip\r\n"

BENCHES = [
    ("engine_health", "httpd", [], lambda p, n: h1(p, get(b"/health"), n)),
    ("engine_file_4k", "httpd", ["--root", WWW], lambda p, n: h1(p, get(b"/f4k.txt"), n)),
    ("engine_file_1m", "httpd", ["--root", WWW], lambda p, n: h1(p, get(b"/f1m.bin"), n)),
    ("engine_gzip_hit", "httpd", ["--root", WWW, "--gzip"], lambda p, n: h1(p, get(b"/f4k.txt", GZ), n)),
    ("engine_304", "httpd", ["--root", WWW],
     lambda p, n: h1(p, get(b"/f4k.txt", b"if-none-match: " + etag(p) + b"\r\n"), n)),
    ("engine_206", "httpd", ["--root", WWW], lambda p, n: h1(p, get(b"/f4k.txt", b"range: bytes=100-199\r\n"), n)),
    ("net_hello", "hello", [], lambda p, n: h1(p, get(b"/"), n)),
    ("net_json", "notes", [], lambda p, n: h1(p, get(b"/notes/1"), n,
     setup=[b"POST /notes HTTP/1.1\r\nhost: x\r\ncontent-length: 16\r\n\r\n{\"text\":\"hello\"}"])),
    ("h2_health", "h2d", [], lambda p, n: h2(p, "/health", n)),
]

# Counting
# ========

def free(pt):
    """nothing listens on pt, and nothing left of an earlier run (a
    connection in TIME_WAIT) keeps a server from binding it"""
    t = socket.socket()
    try:
        t.bind(("0.0.0.0", pt))
        return True
    except OSError:
        return False
    finally:
        t.close()

def port():
    """the next port in 26000-26099 that nothing listens on"""
    for _ in range(100):
        PORT[0] = 26000 + (PORT[0] - 26000 + 1) % 100
        if free(PORT[0]):
            return PORT[0]
    raise SystemExit("no free port in 26000-26099")

def traced(p, exe, pt, tries=2000):
    """the server strace started: the process whose command line is the
    server's own, on its port"""
    want = [w.encode() for w in (exe, "--threads", "1", "--port", str(pt))]
    for _ in range(tries):
        for d in os.listdir("/proc"):
            if d.isdecimal() and int(d) != p.pid:
                try:
                    if open("/proc/%s/cmdline" % d, "rb").read().split(b"\0")[:5] == want:
                        return int(d)
                except OSError:
                    pass
        time.sleep(0.01)
    raise SystemExit("strace never started " + exe)

def stop(p, traced=False):
    if p.poll() is None:
        for k in ([SERVER[0]] if traced else [p.pid]):
            try:
                os.kill(k, signal.SIGTERM)
            except OSError:
                pass
        try:
            p.wait(timeout=60)
        except subprocess.TimeoutExpired:
            p.kill()
            p.wait()
    if p in PROCS:
        PROCS.remove(p)

def one(wrap, prog, flags, drive, n):
    """run the server under wrap, drive n requests, and stop it"""
    pt = port()
    p = subprocess.Popen(wrap + [os.path.join(BIN, prog), "--threads", "1", "--port", str(pt)] + flags,
                         stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    PROCS.append(p)
    try:
        SERVER[0] = traced(p, os.path.join(BIN, prog), pt) if wrap[0] == "strace" else p.pid
        PIDS.add(SERVER[0])
        drive(pt, n)
    finally:
        # the server's last reply is out: stop it once it waits again
        try:
            idle(20000)
        except SystemExit:
            pass
        stop(p, wrap[0] == "strace")

def instrs(prog, flags, drive, n):
    out = os.path.join(BIN, "cg.%d.out" % n)
    if os.path.exists(out):
        os.remove(out)
    one(["valgrind", "--tool=callgrind", "--callgrind-out-file=" + out, "-q"], prog, flags, drive, n)
    for ln in open(out):
        if ln.startswith("totals:") or ln.startswith("summary:"):
            return int(ln.split()[1])
    raise SystemExit("callgrind wrote no totals")

def calls(prog, flags, drive, n):
    out = os.path.join(BIN, "st.out")
    one(["strace", "-f", "-c", "-o", out], prog, flags, drive, n)
    for ln in open(out):
        w = ln.split()
        if w and w[-1] == "total":
            return int(w[3])
    raise SystemExit("strace wrote no total")

def per(f, prog, flags, drive):
    return (f(prog, flags, drive, HI) - f(prog, flags, drive, LO)) / (HI - LO)

def wrk(prog, flags, path):
    """wrk's requests a second against the server alone (not traced)"""
    pt = port()
    p = subprocess.Popen([os.path.join(BIN, prog), "--threads", "1", "--port", str(pt)] + flags,
                         stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    PROCS.append(p)
    PIDS.add(p.pid)
    try:
        connect(pt).close()
        out = subprocess.run(["wrk", "-t1", "-c32", "-d%ds" % WRK, "http://127.0.0.1:%d%s" % (pt, path)],
                             capture_output=True, text=True).stdout
        for ln in out.split("\n"):
            if ln.startswith("Requests/sec:"):
                return float(ln.split()[1])
        return None
    finally:
        stop(p)

WRK_PATHS = {"engine_health": "/health", "engine_file_4k": "/f4k.txt", "engine_file_1m": "/f1m.bin",
             "net_hello": "/", "net_json": "/notes"}

# Pins
# ====

def pin_path():
    return os.path.join(HERE, "_pin_", HW + ".txt")

def pins():
    got = {}
    if os.path.exists(pin_path()):
        for ln in open(pin_path()):
            w = ln.split()
            if len(w) == 3 and not ln.startswith("#"):
                got[w[0]] = (float(w[1]), float(w[2]))
    return got

def main():
    for prog in sorted({b[1] for b in BENCHES if not ONLY or b[0] in ONLY}):
        build(prog)
    fixtures()
    old = pins()
    rows, fails = [], []
    print("%-16s %10s %10s %8s %8s %7s%s%s" % ("bench", "instr/req", "pin", "vs pin", "sys/req", "vs pin",
          "   spread" if REPS > 1 else "", "   wrk req/s (loaded box)" if WRK else ""))
    for name, prog, flags, drive in BENCHES:
        if ONLY and name not in ONLY:
            continue
        got = sorted(per(instrs, prog, flags, drive) for _ in range(REPS))
        ins = got[REPS // 2]
        sc = per(calls, prog, flags, drive)
        rows.append((name, ins, sc))
        pi, ps = old.get(name, (None, None))
        d = "" if pi is None else "%+.2f%%" % (100 * (ins / pi - 1))
        ds = "" if ps is None else "%+.2f" % (sc - ps)
        spread = "   %6.3f%%" % (100 * (got[-1] - got[0]) / ins) if REPS > 1 else ""
        w = ""
        if WRK:
            r = wrk(prog, flags, WRK_PATHS[name]) if name in WRK_PATHS else None
            w = "   %8.0f" % r if r else "   -"
        print("%-16s %10.0f %10s %8s %8.2f %7s%s%s" % (name, ins, "" if pi is None else "%.0f" % pi, d, sc, ds,
              spread, w), flush=True)
        if (pi is not None and ins > pi * SLACK) or (ps is not None and sc > ps + SYS_SLACK):
            fails.append(name)
    if PIN:
        merged = dict(old)
        merged.update({n: (i, s) for n, i, s in rows})
        os.makedirs(os.path.dirname(pin_path()), exist_ok=True)
        cc = subprocess.run(["clang", "--version"], capture_output=True, text=True).stdout.split("\n")[0]
        with open(pin_path(), "w") as f:
            f.write("# %s python3 bench/net/netperf.py --pin (medians of %d runs; %s, %s)\n"
                    % (time.strftime("%Y-%m-%d"), REPS, cc, os.confstr("CS_GNU_LIBC_VERSION")))
            f.write("# bench instructions/request syscalls/request\n")
            for n, _, _, _ in BENCHES:
                if n in merged:
                    f.write("%s %.0f %.2f\n" % (n, merged[n][0], merged[n][1]))
        print("pinned " + pin_path())
    if fails:
        print("OVER THE PIN: " + ", ".join(fails))
        sys.exit(1)

if __name__ == "__main__":
    try:
        main()
    finally:
        for k in PIDS:
            try:
                os.kill(k, signal.SIGKILL)
            except OSError:
                pass
        for p in list(PROCS):
            if p.poll() is None:
                p.kill()
            p.wait()
