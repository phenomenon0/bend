#!/usr/bin/env python3
"""bend-net's behaviour, end to end: the examples built and run, and
every default the library promises checked from the outside.

    python3 net/check.py [--bin DIR] [--port N]

Builds every net/examples/*.bend into DIR (a temporary directory by
default; a binary already there is kept), so no example the docs quote
can rot, and runs hello, json_api, file_server, greet and fetch on
ports N.. (21040 by default): the server's framing,
pipelining, HEAD, keep-alive and close, its refusals (400, 408, 413,
414, 431), its timeouts (head, body, idle), the connection limit,
100-continue and SIGTERM; the router's 404 and 405 with Allow, the JSON
API and the file server; the middleware as templates (greet), the
listening address and the banner that names it, a TLS certificate that
does not load named; and the client against Python peers: plain and
TLS (a self-signed certificate refused, then trusted by --ca), refused
connections and failed names, the exchange's deadline, redirects (the
cap, 303 and 307, credentials kept to their origin), gzip, the body
cap, and a pooled connection reused only when its response allows;
WebSockets on the server: chat_server's room with two ws_chat clients
(its broadcast), its page beside it, its 426 and 400, the 101's Accept
and subprotocol, SIGTERM's 1001, and ws_echo from Python's websockets
(net/ws_check.py --server checks the rest).
Every Bend snippet in guide/NETWORKING.md must be in a file under net/,
word for word. Prints PASS/FAIL per case and exits 1 on any failure.
"""
import gzip, os, shutil, signal, socket, ssl, subprocess, sys, tempfile, threading, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
ARGS = sys.argv[1:]
BIN = ARGS[ARGS.index("--bin") + 1] if "--bin" in ARGS else tempfile.mkdtemp(prefix="bend-net-")
PORT = int(ARGS[ARGS.index("--port") + 1]) if "--port" in ARGS else 21040
os.makedirs(BIN, exist_ok=True)
FAILS = []
PROCS = []

def ok(name, cond, got=""):
    print(("PASS " if cond else "FAIL ") + name + ("" if cond else "  -- got: " + repr(got)[:300]))
    if not cond:
        FAILS.append(name)

def build(name, src):
    out = os.path.join(BIN, name)
    if not os.path.exists(out):
        r = subprocess.run(["bun", os.path.join(ROOT, "bend2/main.ts"), os.path.join(HERE, "examples", src), "-o", out],
                           capture_output=True, text=True)
        if not os.path.exists(out):
            print(r.stdout + r.stderr)
            sys.exit("could not build " + src)
    return out

def up(port, tries=100):
    for _ in range(tries):
        try:
            socket.create_connection(("127.0.0.1", port), timeout=0.2).close()
            return True
        except OSError:
            time.sleep(0.05)
    return False

def start(args, port):
    p = subprocess.Popen(args, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
    PROCS.append(p)
    if not up(port):
        sys.exit("never listened: " + " ".join(args))
    return p

def stop(p):
    if p.poll() is None:
        p.kill()
    p.wait()

def raw(port, data, wait=1.0, total=5.0):
    """send data, read until EOF or wait seconds of silence; the bytes and whether EOF came"""
    s = socket.create_connection(("127.0.0.1", port))
    s.settimeout(wait)
    if data:
        s.sendall(data)
    out, eof, t0 = b"", False, time.time()
    try:
        while time.time() - t0 < total:
            b = s.recv(65536)
            if not b:
                eof = True
                break
            out += b
    except socket.timeout:
        pass
    except ConnectionResetError:
        eof = True
    s.close()
    return out, eof

def head_of(resp):
    return resp.split(b"\r\n\r\n", 1)[0].decode("latin1")

def get(port, path, headers="", method="GET", body=b""):
    req = ("%s %s HTTP/1.1\r\nHost: t\r\n%s" % (method, path, headers)).encode()
    if body:
        req += b"Content-Length: %d\r\n" % len(body)
    return raw(port, req + b"Connection: close\r\n\r\n" + body)[0]

# The server
# ==========

def check_server(hello):
    port = PORT
    p = start([hello, "--port", str(port), "--idle-ms", "700", "--head-ms", "600", "--body-ms", "900",
               "--max-body", "1000", "--max-conns", "4"], port)
    r = get(port, "/")
    ok("server: GET answers 200 with the body", r.startswith(b"HTTP/1.1 200 OK\r\n") and r.endswith(b"\r\n\r\nHello, world!\n"), r)
    ok("server: the length is the body's", b"content-length: 14\r\n" in r, r)
    r = get(port, "/", method="HEAD")
    ok("server: HEAD has GET's length and no body", b"content-length: 14\r\n" in r and r.endswith(b"\r\n\r\n"), r)
    r, eof = raw(port, b"GET /a HTTP/1.1\r\nHost: t\r\n\r\nGET /b HTTP/1.1\r\nHost: t\r\n\r\nGET /c HTTP/1.1\r\nHost: t\r\nConnection: close\r\n\r\n")
    ok("server: three pipelined requests, three responses in order, then close", r.count(b"HTTP/1.1 200") == 3 and eof
       and r.count(b"connection: close") == 1, r)
    r, eof = raw(port, b"GET / HTTP/1.1\r\nHost: t\r\n\r\n", wait=0.3, total=0.3)
    ok("server: keep-alive by default", r.count(b"200 OK") == 1 and not eof, (r, eof))
    r, eof = raw(port, b"GET / HTTP/1.0\r\n\r\n")
    ok("server: HTTP/1.0 closes after its response", b"200 OK" in r and eof and b"connection: close" in r, r)
    r, eof = raw(port, b"GET / HTTP/1.0\r\nConnection: keep-alive\r\n\r\n", wait=0.3, total=0.3)
    ok("server: HTTP/1.0 keep-alive is kept and told so", b"connection: keep-alive" in r and not eof, (r, eof))
    r, eof = raw(port, b"GET / HTTP/1.1\r\n\r\n")
    ok("server: no Host is a 400 that closes", r.startswith(b"HTTP/1.1 400") and eof, r)
    r, eof = raw(port, b"POST / HTTP/1.1\r\nHost: t\r\nContent-Length: 3\r\nTransfer-Encoding: chunked\r\n\r\n0\r\n\r\n")
    ok("server: a body framed two ways is a 400 that closes", r.startswith(b"HTTP/1.1 400") and eof, r)
    r, eof = raw(port, b"GET / HTTP/1.1\r\nHost: t\r\n\r\nGARBAGE\r\n\r\n")
    ok("server: a good request answered, then the broken one refused", r.count(b"200 OK") == 1 and b"400 Bad Request" in r and eof, r)
    t0 = time.time()
    r, eof = raw(port, b"GET / HTTP/1.1\r\nHost: t\r\n", wait=3, total=3)
    dt = time.time() - t0
    ok("server: a head not done within head-ms is a 408, and the connection ends", r.startswith(b"HTTP/1.1 408") and eof and 0.4 < dt < 2.0, (r, dt))
    t0 = time.time()
    r, eof = raw(port, b"POST / HTTP/1.1\r\nHost: t\r\nContent-Length: 10\r\n\r\nab", wait=3, total=3)
    dt = time.time() - t0
    ok("server: a body not done within body-ms is a 408", r.startswith(b"HTTP/1.1 408") and eof and 0.6 < dt < 2.5, (r, dt))
    t0 = time.time()
    r, eof = raw(port, b"", wait=3, total=3)
    dt = time.time() - t0
    ok("server: an idle connection is let go after idle-ms, saying nothing", r == b"" and eof and 0.5 < dt < 2.0, (r, dt))
    r, eof = raw(port, b"POST / HTTP/1.1\r\nHost: t\r\nContent-Length: 5000\r\n\r\n")
    ok("server: a body announced past max-body is a 413 before it is read", r.startswith(b"HTTP/1.1 413") and eof, r)
    r, eof = raw(port, b"GET /" + b"a" * 9000 + b" HTTP/1.1\r\nHost: t\r\n\r\n")
    ok("server: a target past 8 KiB is a 414", r.startswith(b"HTTP/1.1 414") and eof, r)
    r, eof = raw(port, b"GET / HTTP/1.1\r\nHost: t\r\n" + b"X-Big: " + b"b" * 40000 + b"\r\n\r\n")
    ok("server: a head past max-head is a 431", r.startswith(b"HTTP/1.1 431") and eof, r)
    s = socket.create_connection(("127.0.0.1", port)); s.settimeout(2)
    s.sendall(b"POST / HTTP/1.1\r\nHost: t\r\nContent-Length: 4\r\nExpect: 100-continue\r\n\r\n")
    first = s.recv(1000)
    s.sendall(b"abcd")
    rest = s.recv(1000)
    s.close()
    ok("server: Expect: 100-continue is told to send the body, then answered", first == b"HTTP/1.1 100 Continue\r\n\r\n"
       and rest.startswith(b"HTTP/1.1 200"), (first, rest))
    # the connection limit: four idle connections hold every slot; a fifth waits
    held = [socket.create_connection(("127.0.0.1", port)) for _ in range(4)]
    time.sleep(0.2)
    s = socket.create_connection(("127.0.0.1", port)); s.settimeout(0.3)
    s.sendall(b"GET / HTTP/1.1\r\nHost: t\r\nConnection: close\r\n\r\n")
    try:
        early = s.recv(100)
    except socket.timeout:
        early = b""
    for h in held:
        h.close()
    s.settimeout(3)
    late = b""
    try:
        while True:
            b = s.recv(1000)
            if not b:
                break
            late += b
    except socket.timeout:
        pass
    s.close()
    ok("server: past max-conns a connection waits for a slot, then is served", early == b"" and late.startswith(b"HTTP/1.1 200"), (early, late))
    # SIGTERM: an idle connection is let go, and the process ends
    idle = socket.create_connection(("127.0.0.1", port))
    time.sleep(0.1)
    t0 = time.time()
    p.send_signal(signal.SIGTERM)
    try:
        p.wait(timeout=5)
    except subprocess.TimeoutExpired:
        pass
    dt = time.time() - t0
    ok("server: SIGTERM lets an idle connection go and ends the process", p.poll() is not None and dt < 3.0, dt)
    idle.close()
    stop(p)

def check_notes(notes):
    port = PORT + 1
    p = start([notes, "--port", str(port)], port)
    r = get(port, "/notes", body=b'{"text":"hello"}', method="POST")
    ok("json: POST creates, 201 with a Location", r.startswith(b"HTTP/1.1 201") and b"location: /notes/1" in r
       and r.endswith(b'{"id":"1","text":"hello"}'), r)
    r = get(port, "/notes")
    ok("json: the list", r.endswith(b'[{"id":"1","text":"hello"}]'), r)
    r = get(port, "/notes/1")
    ok("json: one by :id", r.startswith(b"HTTP/1.1 200") and r.endswith(b'{"id":"1","text":"hello"}'), r)
    r = get(port, "/notes/1", method="PUT")
    ok("router: 405 lists exactly the methods the path has", r.startswith(b"HTTP/1.1 405") and b"allow: GET, HEAD, DELETE\r\n" in r, r)
    r = get(port, "/nothing")
    ok("router: no route is a 404", r.startswith(b"HTTP/1.1 404"), r)
    r = get(port, "/notes", body=b'{"text":', method="POST")
    ok("json: a body that is not JSON is a 400 saying where", r.startswith(b"HTTP/1.1 400") and b"syntax error" in r, r)
    r = get(port, "/notes", body=b'{"t":1}', method="POST")
    ok("json: a note with no text is a 422", r.startswith(b"HTTP/1.1 422"), r)
    r = get(port, "/notes", body=b'{"text":"' + b"x" * 70000 + b'"}', method="POST")
    ok("json: a body past its budget is a 400", r.startswith(b"HTTP/1.1 400") and b"budget" in r, r)
    r = get(port, "/notes/1", method="DELETE")
    ok("json: DELETE is a 204 with no body", r.startswith(b"HTTP/1.1 204") and r.endswith(b"\r\n\r\n") and b"content-length" not in r, r)
    r = get(port, "/notes/1")
    ok("json: gone after", r.startswith(b"HTTP/1.1 404"), r)
    r = get(port, "/health")
    ok("middleware: the browser's headers are added", b"x-content-type-options: nosniff" in r and b"x-frame-options: DENY" in r, r)
    stop(p)
    log = p.stderr.read().decode()
    ok("middleware: a log line per request", "POST /notes 201" in log and "GET /notes/1 404" in log, log)

def check_greet(greet):
    port = PORT + 6
    p = start([greet, "--port", str(port)], port)
    r = get(port, "/greet?name=Ada")
    ok("greet: a query value, decoded", r.startswith(b"HTTP/1.1 200") and r.endswith(b"Hello, Ada!\n"), r)
    ok("greet: ~Server.logged(~Server.secured(~app)) adds the browser's headers", b"x-frame-options: DENY" in r, r)
    r = get(port, "/add/2/3")
    ok("greet: a handler that can fail, answering", r.endswith(b"\r\n\r\n5\n"), r)
    r = get(port, "/add/2/x")
    ok("greet: a handler's Fail is a plain 500", r.startswith(b"HTTP/1.1 500"), r)
    stop(p)
    log = p.stderr.read().decode()
    ok("greet: the logged template writes a line per request", "GET /greet 200" in log and "GET /add/2/x 500" in log
       and "handler failed: /add wants two numbers" in log, log)

def check_listen(hello, tmp):
    port = PORT + 7
    p = start([hello, "--port", str(port), "--host", "127.0.0.1"], port)
    r = get(port, "/")
    ok("server: --host binds that address", r.endswith(b"Hello, world!\n"), r)
    stop(p)
    log = p.stderr.read().decode()
    ok("server: the banner names the address it listens on", ("listening on http://127.0.0.1:%d" % port) in log, log)
    missing = os.path.join(tmp, "no-such-cert.pem")
    r = subprocess.run([hello, "--port", str(port), "--tls-cert", missing, "--tls-key", missing], capture_output=True,
                       timeout=10)
    err = r.stderr.decode()
    ok("server: a certificate that does not load ends it, saying TLS setup failed and naming the file",
       r.returncode != 0 and "TLS setup failed" in err and "no certificate" in err and missing in err, (r.returncode, err))

def check_files(files, root):
    port = PORT + 2
    p = start([files, "--port", str(port), "--root", root], port)
    r = get(port, "/")
    ok("files: / is index.html, typed", r.startswith(b"HTTP/1.1 200") and b"content-type: text/html" in r and r.endswith(b"<h1>hi</h1>\n"), r)
    r = get(port, "/sub/b.css", method="HEAD")
    ok("files: HEAD has the file's length and no body", b"content-length: 4\r\n" in r and r.endswith(b"\r\n\r\n"), r)
    r = get(port, "/big.bin")
    ok("files: a large file, whole, by sendfile", r.endswith(bytes(i % 251 for i in range(300000))), len(r))
    r = get(port, "/.env")
    ok("files: a dotfile is a 404", r.startswith(b"HTTP/1.1 404"), r)
    r = get(port, "/../../etc/passwd")
    ok("files: a climb out of the root is a 404", r.startswith(b"HTTP/1.1 404"), r)
    r = get(port, "/link")
    ok("files: a symbolic link is not followed", r.startswith(b"HTTP/1.1 404"), r)
    r = get(port, "/x", method="POST")
    ok("files: POST is a 405", r.startswith(b"HTTP/1.1 405"), r)
    stop(p)

# The client
# ==========

class Peer:
    """a Python HTTP/1.1 peer on its own thread: routes by path, counts connections"""
    def __init__(self, port, tls=None):
        self.port, self.conns, self.seen = port, 0, []
        self.sock = socket.socket(); self.sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.sock.bind(("127.0.0.1", port)); self.sock.listen(64)
        self.tls = tls
        threading.Thread(target=self.loop, daemon=True).start()

    def loop(self):
        while True:
            try:
                c, _ = self.sock.accept()
            except OSError:
                return
            self.conns += 1
            threading.Thread(target=self.serve, args=(c, self.conns), daemon=True).start()

    def serve(self, c, n):
        try:
            if self.tls:
                c = self.tls.wrap_socket(c, server_side=True)
            buf = b""
            while True:
                while b"\r\n\r\n" not in buf:
                    b = c.recv(65536)
                    if not b:
                        return
                    buf += b
                head, buf = buf.split(b"\r\n\r\n", 1)
                lines = head.decode("latin1").split("\r\n")
                meth, path, _ = lines[0].split(" ")
                hs = {l.split(":", 1)[0].lower(): l.split(":", 1)[1].strip() for l in lines[1:]}
                n_body = int(hs.get("content-length", "0"))
                while len(buf) < n_body:
                    buf += c.recv(65536)
                body, buf = buf[:n_body], buf[n_body:]
                self.seen.append((meth, path, hs, body))
                out = self.answer(meth, path, hs, body, n)
                if out is None:
                    time.sleep(10)
                    return
                c.sendall(out)
                if b"connection: close" in out.lower():
                    c.close()
                    return
        except Exception:
            return

    def answer(self, meth, path, hs, body, n):
        def resp(code, body=b"", extra=""):
            return ("HTTP/1.1 %d X\r\ncontent-length: %d\r\n%s\r\n" % (code, len(body), extra)).encode() + body
        if path == "/hang":
            return None
        if path.startswith("/r/"):
            k = int(path[3:])
            return resp(302, extra="location: /r/%d\r\n" % (k - 1)) if k > 0 else resp(200, b"landed")
        if path == "/see":
            return resp(303, extra="location: /show\r\n")
        if path == "/tmp":
            return resp(307, extra="location: /show\r\n")
        if path == "/show":
            return resp(200, ("%s %s" % (meth, body.decode())).encode())
        if path.startswith("/away/"):
            return resp(302, extra="location: http://%s:%s/auth\r\n" % (path[6:].split(":")[0], path[6:].split(":")[1]))
        if path == "/auth":
            return resp(200, ("auth=%s" % hs.get("authorization", "none")).encode())
        if path == "/gz":
            z = gzip.compress(b"hello, gzip! " * 100)
            return resp(200, z, "content-encoding: gzip\r\n")
        if path == "/badgz":
            return resp(200, b"not gzip at all", "content-encoding: gzip\r\n")
        if path == "/big":
            return resp(200, b"x" * 5000)
        if path == "/conn":
            return resp(200, b"conn %d" % n)
        if path == "/closing":
            return resp(200, b"conn %d" % n, "connection: close\r\n")
        return resp(404)

def fetch(bin_, *args, timeout=15):
    r = subprocess.run([bin_] + list(args), capture_output=True, timeout=timeout)
    return r.returncode, r.stdout.decode("latin1"), r.stderr.decode("latin1")

def check_client(fetch_bin, hello, tmp):
    port = PORT + 3
    peer = Peer(port)
    u = "http://127.0.0.1:%d" % port
    c, out, err = fetch(fetch_bin, u + "/conn")
    ok("client: a GET", c == 0 and out == "conn 1", (c, out, err))
    c, out, err = fetch(fetch_bin, "-i", "--twice", u + "/conn")
    ok("client: a kept-alive connection is reused from the pool", c == 0 and out.count("conn 2") == 2, (out, err))
    c, out, err = fetch(fetch_bin, "--twice", u + "/closing")
    ns = out.split("conn ")[1:]
    ok("client: a connection its response closed is not reused", c == 0 and len(ns) == 2 and ns[0] != ns[1], (out, err))
    c, out, err = fetch(fetch_bin, "http://127.0.0.1:%d/" % (PORT + 9))
    ok("client: a refused connection is Refused", c == 1 and "connection refused" in err, (c, err))
    c, out, err = fetch(fetch_bin, "http://no-such-host.invalid/")
    ok("client: a name that does not resolve is Dns", c == 1 and "dns:" in err, (c, err))
    c, out, err = fetch(fetch_bin, "ftp://x/")
    ok("client: a URL that is not http(s) is BadUrl", c == 1 and "bad url" in err, (c, err))
    t0 = time.time()
    c, out, err = fetch(fetch_bin, "--timeout", "500", u + "/hang")
    dt = time.time() - t0
    ok("client: the exchange's deadline is a Timeout", c == 1 and "timeout" in err and dt < 3, (c, err, dt))
    c, out, err = fetch(fetch_bin, u + "/r/5")
    ok("client: redirects are followed", c == 0 and out == "landed", (out, err))
    c, out, err = fetch(fetch_bin, u + "/r/11")
    ok("client: at most 10 redirects", c == 1 and "too many redirects" in err, (c, err))
    c, out, err = fetch(fetch_bin, "--max-redirects", "3", u + "/r/4")
    ok("client: the cap is the caller's to lower", c == 1 and "too many redirects" in err, (c, err))
    c, out, err = fetch(fetch_bin, "-X", "POST", "-d", "data", u + "/see")
    ok("client: 303 goes on as GET without the body", out == "GET ", (out, err))
    c, out, err = fetch(fetch_bin, "-X", "POST", "-d", "data", u + "/tmp")
    ok("client: 307 keeps the method and the body", out == "POST data", (out, err))
    c, out, err = fetch(fetch_bin, "-H", "Authorization: Bearer s3cret", u + "/away/127.0.0.1:%d" % port)
    ok("client: credentials go on to the same origin", out == "auth=Bearer s3cret", (out, err))
    c, out, err = fetch(fetch_bin, "-H", "Authorization: Bearer s3cret", u + "/away/localhost:%d" % port)
    ok("client: credentials never go to another origin", out == "auth=none", (out, err))
    c, out, err = fetch(fetch_bin, u + "/gz")
    ok("client: a gzip body is decoded", c == 0 and out == "hello, gzip! " * 100, (out[:60], err))
    c, out, err = fetch(fetch_bin, u + "/badgz")
    ok("client: a body that is not the gzip it says is a Protocol error", c == 1 and "gzip" in err, (c, err))
    c, out, err = fetch(fetch_bin, "--max-body", "1000", u + "/big")
    ok("client: a body past the cap is TooLarge", c == 1 and "too large" in err, (c, err))
    c, out, err = fetch(fetch_bin, "-H", "X-Bad: a\rb", u + "/conn")
    ok("client: a field with a line end in it is refused, not sent", c == 1 and "malformed" in err, (c, err))
    # TLS: a self-signed certificate is refused, and trusted when pinned
    cert, key = os.path.join(tmp, "cert.pem"), os.path.join(tmp, "key.pem")
    subprocess.run(["openssl", "req", "-x509", "-newkey", "rsa:2048", "-keyout", key, "-out", cert, "-days", "2", "-nodes",
                    "-subj", "/CN=localhost", "-addext", "subjectAltName=DNS:localhost"], capture_output=True, check=True)
    ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER); ctx.load_cert_chain(cert, key)
    tport = PORT + 4
    Peer(tport, tls=ctx)
    c, out, err = fetch(fetch_bin, "https://localhost:%d/conn" % tport)
    ok("client: TLS verifies, and refuses a self-signed certificate", c == 1 and "tls:" in err, (c, err))
    c, out, err = fetch(fetch_bin, "--ca", cert, "https://localhost:%d/conn" % tport)
    ok("client: TLS with the certificate pinned by --ca", c == 0 and out.startswith("conn"), (c, out, err))
    c, out, err = fetch(fetch_bin, "--ca", cert, "https://127.0.0.1:%d/conn" % tport)
    ok("client: TLS checks the name: a certificate for localhost is not 127.0.0.1's", c == 1 and "tls:" in err, (c, err))
    # the server over TLS, fetched by the client
    sport = PORT + 5
    p = start([hello, "--port", str(sport), "--tls-cert", cert, "--tls-key", key], sport)
    c, out, err = fetch(fetch_bin, "--ca", cert, "https://localhost:%d/" % sport)
    ok("server: TLS, fetched by the client", c == 0 and out == "Hello, world!\n", (c, out, err))
    stop(p)

# WebSockets on the server
# ========================

def chat(chat_bin, port, name, *says, wait=1500):
    return subprocess.Popen([chat_bin, "ws://127.0.0.1:%d/room" % port, name, *says, "--wait-ms", str(wait)],
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)

def check_ws(room, chat_bin, echo):
    """chat_server and ws_chat together: a room, its broadcast, its page, its refusals, SIGTERM's 1001;
    ws_echo from Python's websockets when it is installed (net/ws_check.py --server has the rest)"""
    port = PORT + 10
    p = start([room, "--port", str(port)], port)
    r = get(port, "/")
    ok("ws: the chat server serves its page beside the room", b" 200 " in r.split(b"\r\n", 1)[0] and b"WebSocket" in r, r[:200])
    r = get(port, "/room")
    ok("ws: a GET at the room that does not ask to upgrade is a 426 naming version 13",
       b" 426 " in r.split(b"\r\n", 1)[0] and b"sec-websocket-version: 13" in r.lower(), r[:300])
    r = raw(port, b"GET /room HTTP/1.1\r\nHost: t\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n"
            b"Sec-WebSocket-Key: short\r\nSec-WebSocket-Version: 13\r\n\r\n")[0]
    ok("ws: a key that is not sixteen bytes in base64 is a 400", b" 400 " in r.split(b"\r\n", 1)[0], r[:200])
    r = raw(port, b"GET /room HTTP/1.1\r\nHost: t\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n"
            b"Sec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==\r\nSec-WebSocket-Version: 13\r\n"
            b"Sec-WebSocket-Protocol: x, chat\r\nSec-WebSocket-Extensions: permessage-deflate\r\n\r\n", wait=0.5)[0]
    h = head_of(r).lower()
    ok("ws: the 101 carries the RFC's Accept, the subprotocol offered, no extension",
       h.startswith("http/1.1 101") and "sec-websocket-accept: s3pplmbitxaq9kygzzhzrbk+xoo=" in h
       and "sec-websocket-protocol: chat" in h and "extension" not in h, h)
    ada = chat(chat_bin, port, "ada", wait=2500)
    time.sleep(0.5)
    bob = chat(chat_bin, port, "bob", "hi all", "second", wait=1000)
    b_out = bob.communicate(timeout=20)[0]
    a_out = ada.communicate(timeout=20)[0]
    ok("ws: a room broadcasts: what bob says, ada hears, in order",
       a_out.split("\n")[:2] == ["< bob: hi all", "< bob: second"] and "left the room (1000)" in a_out, a_out)
    ok("ws: and the sender hears itself", b_out.split("\n")[:2] == ["< bob: hi all", "< bob: second"], b_out)
    # SIGTERM: a member hears 1001, and the server ends
    cy = chat(chat_bin, port, "cy", wait=8000)
    time.sleep(0.5)
    p.send_signal(signal.SIGTERM)
    c_out = cy.communicate(timeout=20)[0]
    try:
        code = p.wait(10)
    except subprocess.TimeoutExpired:
        code = None
    ok("ws: SIGTERM closes the room with 1001, and the server ends", "closed the room: 1001" in c_out and code == 0,
       (c_out, code))
    try:
        import asyncio, websockets
        from websockets.asyncio.client import connect
    except ImportError:
        print("SKIP ws: the echo from Python (pip install websockets)")
        return
    port = PORT + 11
    start([echo, "--port", str(port)], port)

    async def talk():
        async with connect("ws://127.0.0.1:%d/echo" % port, subprotocols=["echo"]) as ws:
            await ws.send("héllo")
            t = await ws.recv()
            await ws.send(bytes(70000))
            b = await ws.recv()
            return ws.subprotocol, t, len(b)
    try:
        got = asyncio.run(talk())
    except Exception as e:
        got = repr(e)
    ok("ws: the echo, from Python's websockets", got == ("echo", "héllo", 70000), got)

def check_guide():
    """every Bend snippet in guide/NETWORKING.md is in a file under net/, word for word"""
    srcs = []
    for d, _, fs in os.walk(HERE):
        srcs += [open(os.path.join(d, f)).read() for f in fs if f.endswith(".bend")]
    guide = open(os.path.join(ROOT, "guide", "NETWORKING.md")).read()
    snips = [b.split("```", 1)[0] for b in guide.split("```python\n")[1:]]
    stale = [b for b in snips if not any(b in src for src in srcs)]
    ok("guide: each of NETWORKING.md's %d snippets is in a file under net/" % len(snips), not stale,
       stale[0][:200] if stale else "")

def main():
    check_guide()
    # every example builds (a doc snippet is copied from one), then the
    # ones below are run
    bins = {f[:-5]: build(f[:-5], f) for f in sorted(os.listdir(os.path.join(HERE, "examples"))) if f.endswith(".bend")}
    ok("every example builds: " + ", ".join(sorted(bins)), True)
    hello, notes, files, fetch_bin, greet = bins["hello"], bins["json_api"], bins["file_server"], bins["fetch"], bins["greet"]
    tmp = tempfile.mkdtemp(prefix="bend-net-www-")
    root = os.path.join(tmp, "www")
    os.makedirs(os.path.join(root, "sub"))
    open(os.path.join(root, "index.html"), "w").write("<h1>hi</h1>\n")
    open(os.path.join(root, "sub", "b.css"), "w").write("b{}\n")
    open(os.path.join(root, ".env"), "w").write("SECRET=1\n")
    open(os.path.join(root, "big.bin"), "wb").write(bytes(i % 251 for i in range(300000)))
    os.symlink("/etc/passwd", os.path.join(root, "link"))
    try:
        check_server(hello)
        check_notes(notes)
        check_files(files, root)
        check_greet(greet)
        check_listen(hello, tmp)
        check_client(fetch_bin, hello, tmp)
        check_ws(bins["chat_server"], bins["ws_chat"], bins["ws_echo"])
    finally:
        for p in PROCS:
            stop(p)
        shutil.rmtree(tmp, ignore_errors=True)
    print("%d failed" % len(FAILS) if FAILS else "all passed")
    sys.exit(1 if FAILS else 0)

if __name__ == "__main__":
    main()
