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
handler's time (a handler that sleeps forever: a 503 that closes), the
listening address and the banner that names it, a TLS certificate that
does not load named; and the client against Python peers: plain and
TLS (a self-signed certificate refused, then trusted by --ca), refused
connections and failed names, the exchange's deadline, redirects (the
cap, 303 and 307, credentials kept to their origin), gzip, the body
cap, and a pooled connection reused only when its response allows;
and streamed bodies (upload): 100 MB by length and chunked in bounded
memory, the stream's cap (413), a stalled body (408), a handler that
returns without reading, 100-continue, pipelining after a streamed body
and before one (a body past max-body and the engine's 1 MiB behind a GET
in one write), a head cut between its blank line's CR and LF, and the
heads the RFC refuses (a bare LF, a fold, two lengths that disagree, a
length past a U32, two Hosts) each a 400 with no byte of its body read;
and streamed responses (export, events): chunked, 1 GB byte for byte in
bounded memory, a declared length exact, short and long, HEAD, HTTP/1.0,
a client gone mid-body, server-sent events with curl -N, a relay that
streams a 100 MB upstream body end to end (relay_stream).
WebSockets on the server: chat_server's room with two ws_chat clients
(its broadcast), its page beside it, its 426 and 400, the 101's Accept
and subprotocol, SIGTERM's 1001, and ws_echo from Python's websockets
(net/ws_check.py --server checks the rest). IPv6, where the machine has a
loopback for it (else said and skipped): the server on ::1 (its banner
[::1]:port, the request's remote ::1) and on :: (IPv4 too), over TLS;
the client to http://[::1]:port/ (Host [::1]:port, pooled), to a name
with both families whichever one listens, over TLS to an IP-literal
(its IP SAN checked, one without refused, no SNI sent); a WebSocket
room on ::1 through ws://[::1]:port/ (its Host bracketed).
Server.argv's refusals (an unknown flag, a value missing, a number that
is none), typed JSON fields (signup: every reason in one 400), and
Server.wrap's log lines and headers over files and a WebSocket route.
Every Bend snippet in guide/NETWORKING.md and guide/net/*.md must be in
a file under net/, word for word. Prints PASS/FAIL per case and exits 1 on any failure.
"""
import gzip, hashlib, os, shutil, signal, socket, ssl, subprocess, sys, tempfile, threading, time

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
    ok("json: a note with no text is a 422 that says so", r.startswith(b"HTTP/1.1 422")
       and r.endswith(b'{"errors":["text is required"]}'), r)
    r = get(port, "/notes", body=b'{"text":7}', method="POST")
    ok("json: a text that is a number is no text (Json.get.str)", r.startswith(b"HTTP/1.1 422")
       and r.endswith(b'{"errors":["text must be a string"]}'), r)
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
    p = start([greet, "--port", str(port), "--handler-ms", "600"], port)
    r = get(port, "/greet?name=Ada")
    ok("greet: a query value, decoded", r.startswith(b"HTTP/1.1 200") and r.endswith(b"Hello, Ada!\n"), r)
    ok("greet: ~Server.logged(~Server.secured(~app)) adds the browser's headers", b"x-frame-options: DENY" in r, r)
    r = get(port, "/add/2/3")
    ok("greet: a handler that can fail, answering", r.endswith(b"\r\n\r\n5\n"), r)
    r = get(port, "/add/2/x")
    ok("greet: a handler's Fail is a plain 500", r.startswith(b"HTTP/1.1 500"), r)
    # the handler's time: /stall sleeps forever; past --handler-ms the
    # server answers 503 that closes, and nothing after it
    t0 = time.time()
    r, eof = raw(port, b"GET /stall HTTP/1.1\r\nHost: t\r\n\r\nGET /greet?name=Late HTTP/1.1\r\nHost: t\r\n\r\n",
                 wait=4, total=4)
    dt = time.time() - t0
    ok("handler time: a handler that never answers is a 503 at --handler-ms, closing, and nothing after it",
       r.startswith(b"HTTP/1.1 503") and b"connection: close" in r.lower() and eof and r.count(b"HTTP/1.1 ") == 1
       and b"Late" not in r and 0.5 < dt < 2.0, (r, eof, dt))
    t0 = time.time()
    r, eof = raw(port, b"GET /greet?name=Ada HTTP/1.1\r\nHost: t\r\n\r\nGET /stall HTTP/1.1\r\nHost: t\r\n\r\n",
                 wait=4, total=4)
    dt = time.time() - t0
    ok("handler time: what was answered before it goes out first, then the 503",
       r.startswith(b"HTTP/1.1 200") and r.count(b"HTTP/1.1 503") == 1 and r.index(b"Hello, Ada!") < r.index(b"HTTP/1.1 503")
       and eof and 0.5 < dt < 2.0, (r, eof, dt))
    held = [socket.create_connection(("127.0.0.1", port)) for _ in range(3)]
    for h in held:
        h.sendall(b"GET /stall HTTP/1.1\r\nHost: t\r\n\r\n")
    time.sleep(0.1)
    r = get(port, "/greet?name=Bo")
    ok("handler time: handlers waiting do not hold the server: another request is answered at once",
       r.startswith(b"HTTP/1.1 200") and r.endswith(b"Hello, Bo!\n"), r)
    for h in held:
        h.close()
    stop(p)
    log = p.stderr.read().decode()
    ok("greet: the logged template writes a line per request", "GET /greet 200" in log and "GET /add/2/x 500" in log
       and "handler failed: /add wants two numbers" in log, log)
    ok("handler time: a handler let go is never logged as answering", "GET /stall" not in log, log)

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

def check_args(hello, files):
    """Server.argv: an unknown flag, a value missing, a number that is none, each refused with a usage line"""
    for args, why in [(["--prot", "80"], "unknown flag --prot"), (["--port"], "--port needs a value (N)"),
                      (["--port", "eighty"], "--port wants a number, not eighty"), (["x"], "unexpected argument x")]:
        r = subprocess.run([hello] + args, capture_output=True, timeout=10)
        err = r.stderr.decode()
        ok("args: %s: refused, exit 2, with a usage line" % " ".join(args),
           r.returncode == 2 and why in err and "usage: [--host A] [--port N]" in err, (r.returncode, err))
    r = subprocess.run([files, "--port", "1", "--nope"], capture_output=True, timeout=10)
    err = r.stderr.decode()
    ok("args: a program's own flags are in its usage line", r.returncode == 2 and "usage: [--root DIR] [--host A]" in err,
       (r.returncode, err))

def check_signup(signup):
    """typed JSON fields: every reason at once"""
    port = PORT + 31
    p = start([signup, "--port", str(port)], port)
    r = get(port, "/signup", body=b'{"name":"Ada","age":36,"email":"ada@x.org","tags":["math"]}', method="POST")
    ok("json: typed fields read, a default for the missing one", r.startswith(b"HTTP/1.1 201")
       and r.endswith(b'{"name":"Ada","age":36,"email":"ada@x.org","tags":1,"newsletter":false}'), r)
    r = get(port, "/signup", body=b'{"name":7,"age":-1,"tags":{},"newsletter":null}', method="POST")
    ok("json: a 400 lists every problem", r.startswith(b"HTTP/1.1 400") and r.endswith(
       b'{"errors":["name must be a string","age must be a whole number from 0 to 4294967295","email is required",'
       b'"tags must be an array","newsletter must be true or false"]}'), r)
    stop(p)

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
    r = get(port, "/sub/b.css")
    ok("files: Server.wrap secures the static files", b"content-security-policy: default-src 'self'" in r
       and b"x-content-type-options: nosniff" in r, r)
    stop(p)
    log = p.stderr.read().decode()
    # a file's line is written before the file is opened: 200 and no length, a 404 or not
    ok("files: Server.wrap logs the static files", "GET /sub/b.css 200" in log and "GET /.env " in log, log[-600:])

# The client
# ==========

class Peer:
    """a Python HTTP/1.1 peer on its own thread: routes by path, counts connections"""
    def __init__(self, port, tls=None, host="127.0.0.1"):
        self.port, self.conns, self.seen = port, 0, []
        self.sock = socket.socket(socket.AF_INET6 if ":" in host else socket.AF_INET)
        self.sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.sock.bind((host, port)); self.sock.listen(64)
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

# Streamed bodies
# ===============

def peak_kb(pid):
    """the process's peak resident set (Linux's VmHWM), or its resident set now"""
    try:
        for l in open("/proc/%d/status" % pid):
            if l.startswith("VmHWM:"):
                return int(l.split()[1])
    except OSError:
        pass
    r = subprocess.run(["ps", "-o", "rss=", "-p", str(pid)], capture_output=True, text=True)
    return int(r.stdout.strip() or 0)

class Peak:
    """the most of peak_kb seen while a with-block runs (sampled where there is no VmHWM)"""
    def __init__(self, pid):
        self.pid, self.most, self.on = pid, peak_kb(pid), True
    def __enter__(self):
        def loop():
            while self.on:
                self.most = max(self.most, peak_kb(self.pid))
                time.sleep(0.05)
        self.t = threading.Thread(target=loop, daemon=True); self.t.start()
        return self
    def __exit__(self, *a):
        self.on = False; self.t.join()
        self.most = max(self.most, peak_kb(self.pid))

def recv_all(s, total=10.0):
    out, t0 = b"", time.time()
    try:
        while time.time() - t0 < total:
            b = s.recv(65536)
            if not b:
                return out, True
            out += b
    except socket.timeout:
        pass
    except ConnectionResetError:
        return out, True
    return out, False

def upload(port, path, n, chunked=False, extra=b""):
    """n bytes of a pattern PUT to path, by length or chunked (odd chunk sizes): the answer,
    whether the connection closed, the seconds it took, and the body's sha256"""
    blk = bytes((i * 7 + 3) % 256 for i in range(1 << 20))
    s = socket.create_connection(("127.0.0.1", port)); s.settimeout(20)
    fr = b"Transfer-Encoding: chunked\r\n" if chunked else b"Content-Length: %d\r\n" % n
    t0, h, left, k = time.time(), hashlib.sha256(), n, 0
    s.sendall(b"PUT " + path.encode() + b" HTTP/1.1\r\nHost: t\r\n" + fr + extra + b"Connection: close\r\n\r\n")
    while left:
        m = min(left, len(blk) - (k % 4093) if chunked else len(blk))
        part = blk[:m]
        h.update(part)
        s.sendall(b"%x;x=%d\r\n" % (m, k) + part + b"\r\n" if chunked else part)
        left -= m; k += 1
    if chunked:
        s.sendall(b"0\r\nX-Trailer: 1\r\n\r\n")
    r, eof = recv_all(s, 20)
    s.close()
    return r, eof, time.time() - t0, h.hexdigest()

def sha_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()

def check_stream(upload_bin, tmp):
    port = PORT + 10
    d = os.path.join(tmp, "up")
    os.makedirs(d)
    p = start([upload_bin, "--port", str(port), "--dir", d, "--max-stream", "150000000", "--progress-ms", "800",
               "--max-body", "1000"], port)
    r = get(port, "/")
    ok("stream: a route not streamed is answered as Server.serve answers it", r.startswith(b"HTTP/1.1 200"), r)
    r = get(port, "/count", method="POST", body=b"one\ntwo\nthree\n")
    ok("stream: a body read a chunk at a time (Stream.read)", r.endswith(b"14 bytes, 3 lines\n"), r)
    N = 100 * 1000 * 1000
    base = peak_kb(p.pid)
    with Peak(p.pid) as pk:
        r, eof, dt, sha = upload(port, "/upload/big.bin", N)
    got = os.path.join(d, "big.bin")
    ok("stream: 100 MB by Content-Length, to a file (Stream.to_file), byte for byte",
       r.endswith(b"saved big.bin: 100000000 bytes\n") and eof and os.path.getsize(got) == N and sha_file(got) == sha, r[-80:])
    ok("stream: its memory bounded: peak RSS %d kB after 100 MB (%d kB before), %.0f MB/s" % (pk.most, base, N / dt / 1e6),
       pk.most < base + 16384, (base, pk.most))
    with Peak(p.pid) as pk:
        r, eof, dt, sha = upload(port, "/upload/big2.bin", N, chunked=True)
    got = os.path.join(d, "big2.bin")
    ok("stream: 100 MB chunked (odd sizes, extensions, a trailer), byte for byte, peak RSS %d kB, %.0f MB/s" % (pk.most, N / dt / 1e6),
       r.endswith(b"saved big2.bin: 100000000 bytes\n") and os.path.getsize(got) == N and sha_file(got) == sha
       and pk.most < base + 16384, (r[-80:], pk.most))
    r, eof = raw(port, b"PUT /upload/x HTTP/1.1\r\nHost: t\r\nContent-Length: 200000000\r\n\r\n")
    ok("stream: a length past --max-stream is a 413 before a byte is read, and closes", r.startswith(b"HTTP/1.1 413") and eof, r)
    r, eof = raw(port, b"PUT /upload/x HTTP/1.1\r\nHost: t\r\nContent-Length: 200000000\r\nExpect: 100-continue\r\n\r\n")
    ok("stream: ... and with Expect: 100-continue, no 100 is sent", r.startswith(b"HTTP/1.1 413") and b" 100 " not in r and eof, r)
    r, eof = raw(port, b"POST /count HTTP/1.1\r\nHost: t\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\nzz\r\n")
    ok("stream: a malformed chunked body is a 400 that closes", r.startswith(b"HTTP/1.1 400") and eof, r)
    t0 = time.time()
    r, eof = raw(port, b"PUT /upload/slow HTTP/1.1\r\nHost: t\r\nContent-Length: 100\r\n\r\nabc", wait=3, total=3)
    dt = time.time() - t0
    ok("stream: a body that stalls past --progress-ms is a 408 that closes (%.2f s)" % dt,
       r.startswith(b"HTTP/1.1 408") and eof and 0.6 < dt < 2.0, (r, dt))
    t0 = time.time()
    s = socket.create_connection(("127.0.0.1", port)); s.settimeout(3)
    s.sendall(b"PUT /upload/trickle HTTP/1.1\r\nHost: t\r\nContent-Length: 6\r\n\r\n")
    for c in b"abcdef":
        time.sleep(0.4); s.sendall(bytes([c]))
    r, eof = recv_all(s, 3); s.close()
    ok("stream: a slow body that keeps making progress is read whole", r.startswith(b"HTTP/1.1 201") and b"6 bytes" in r, r)
    r, eof = raw(port, b"POST /refuse HTTP/1.1\r\nHost: t\r\nContent-Length: 5\r\n\r\nhello"
                      b"GET / HTTP/1.1\r\nHost: t\r\nConnection: close\r\n\r\n")
    ok("stream: a handler that returns without reading: the body drained, the pipelined request answered",
       r.startswith(b"HTTP/1.1 403") and r.count(b"HTTP/1.1 ") == 2 and b"HTTP/1.1 200" in r and eof, r)
    body = (b"GET /smuggled HTTP/1.1\r\nHost: t\r\n\r\n" * 70000)[:2 * 1000 * 1000]
    s = socket.create_connection(("127.0.0.1", port)); s.settimeout(3)
    s.sendall(b"POST /refuse HTTP/1.1\r\nHost: t\r\nContent-Length: %d\r\n\r\n" % len(body))
    try:
        s.sendall(body)
    except OSError:
        pass
    r, eof = recv_all(s, 3); s.close()
    ok("stream: past the drain, an unread body closes the connection, and none of it is read as a request",
       r.startswith(b"HTTP/1.1 403") and b"connection: close" in r and r.count(b"HTTP/1.1 ") == 1 and eof, r)
    s = socket.create_connection(("127.0.0.1", port)); s.settimeout(2)
    s.sendall(b"PUT /upload/c.txt HTTP/1.1\r\nHost: t\r\nContent-Length: 4\r\nExpect: 100-continue\r\n\r\n")
    first = s.recv(1000)
    s.sendall(b"abcd")
    rest, eof = recv_all(s, 1); s.close()
    ok("stream: Expect: 100-continue is told to go on at the handler's first read, then answered",
       first == b"HTTP/1.1 100 Continue\r\n\r\n" and rest.startswith(b"HTTP/1.1 201"), (first, rest))
    r, eof = raw(port, b"POST /refuse HTTP/1.1\r\nHost: t\r\nContent-Length: 4\r\nExpect: 100-continue\r\n\r\n")
    ok("stream: a handler that refuses without reading sends no 100, and the connection closes",
       r.startswith(b"HTTP/1.1 403") and b" 100 " not in r and eof, r)
    r, eof = raw(port, b"PUT /upload/p1 HTTP/1.1\r\nHost: t\r\nTransfer-Encoding: chunked\r\n\r\n3\r\nabc\r\n0\r\n\r\n"
                      b"POST /count HTTP/1.1\r\nHost: t\r\nContent-Length: 2\r\n\r\nhi"
                      b"GET / HTTP/1.1\r\nHost: t\r\nConnection: close\r\n\r\n")
    ok("stream: pipelined after a streamed body, the next requests are read from the bytes after it",
       r.count(b"HTTP/1.1 ") == 3 and b"saved p1: 3 bytes" in r and b"2 bytes, 0 lines" in r and eof, r)
    r, eof = raw(port, b"GET / HTTP/1.1\r\nHost: t\r\n\r\nPOST /count HTTP/1.1\r\nHost: t\r\nContent-Length: 6\r\n"
                      b"Connection: close\r\n\r\nab\ncd\n")
    ok("stream: a stream route's request pipelined behind another in one read is streamed",
       r.count(b"HTTP/1.1 200") == 2 and r.endswith(b"6 bytes, 2 lines\n") and eof, r)
    big = b"line\n" * 400000
    s = socket.create_connection(("127.0.0.1", port)); s.settimeout(3)
    s.sendall(b"GET / HTTP/1.1\r\nHost: t\r\n\r\nPOST /count HTTP/1.1\r\nHost: t\r\nContent-Length: %d\r\n"
              b"Connection: close\r\n\r\n" % len(big) + big)
    r, eof = recv_all(s, 3); s.close()
    ok("stream: ... with a body past --max-body and past the engine's 1 MiB, pipelined in the same write",
       r.count(b"HTTP/1.1 200") == 2 and r.endswith(b"2000000 bytes, 400000 lines\n") and eof, r[-200:])
    s = socket.create_connection(("127.0.0.1", port)); s.settimeout(3)
    s.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
    s.sendall(b"POST /count HTTP/1.1\r\nHost: t\r\nContent-Length: 3\r\nConnection: close\r\n\r")
    time.sleep(0.3)
    s.sendall(b"\na\nb")
    r, eof = recv_all(s, 3); s.close()
    ok("stream: a head whose blank line is cut between its CR and its LF", r.endswith(b"3 bytes, 1 lines\n") and eof, r)
    r, eof = raw(port, b"POST /count HTTP/1.1\r\nHost: t\r\nContent-Length: 3\r\nContent-Length: 3\r\n"
                      b"Connection: close\r\n\r\nab\n")
    ok("stream: two lengths that agree are one", r.endswith(b"3 bytes, 1 lines\n") and eof, r)
    for what, req in [
            ("two lengths that disagree", b"POST /count HTTP/1.1\r\nHost: t\r\nContent-Length: 3\r\nContent-Length: 4\r\n\r\nabcd"),
            ("a bare LF", b"POST /count HTTP/1.1\r\nHost: t\nContent-Length: 1\r\n\r\nx"),
            ("a folded line", b"POST /count HTTP/1.1\r\nHost: t\r\nX-A: 1\r\n  more\r\nContent-Length: 1\r\n\r\nx"),
            ("a space before a colon", b"POST /count HTTP/1.1\r\nHost: t\r\nContent-Length : 1\r\n\r\nx"),
            ("a length past what a U32 holds", b"POST /count HTTP/1.1\r\nHost: t\r\nContent-Length: 4294967290\r\n\r\nx"),
            ("a coding but chunked", b"POST /count HTTP/1.1\r\nHost: t\r\nTransfer-Encoding: gzip\r\n\r\nx"),
            ("two Hosts", b"POST /count HTTP/1.1\r\nHost: t\r\nHost: u\r\nContent-Length: 1\r\n\r\nx")]:
        r, eof = raw(port, req)
        ok("stream: a head with %s is a 400 that closes, and its body is not read" % what,
           r.startswith(b"HTTP/1.1 400") and r.count(b"HTTP/1.1 ") == 1 and eof, r)
    r, eof = raw(port, b"PUT /upload/x HTTP/1.1\r\nHost: t\r\nContent-Length: 3000000000\r\n\r\n")
    ok("stream: a length past the engine's cap and --max-stream is a 413", r.startswith(b"HTTP/1.1 413") and eof, r)
    r, eof = raw(port, b"PUT /upload/x HTTP/1.1\r\nHost: t\r\nContent-Length: 1\r\nTransfer-Encoding: chunked\r\n\r\n0\r\n\r\n")
    ok("stream: a body framed two ways is a 400 that closes", r.startswith(b"HTTP/1.1 400") and eof, r)
    r, eof = raw(port, b"PUT /upload/x HTTP/1.1\r\nContent-Length: 1\r\n\r\nx")
    ok("stream: no Host is a 400", r.startswith(b"HTTP/1.1 400") and eof, r)
    r, eof = raw(port, b"PUT /upload/x HTTP/1.1\r\nHost: t\rX-A: 1\r\nContent-Length: 1\r\n\r\nx")
    ok("stream: a bare CR in a head is a 400", r.startswith(b"HTTP/1.1 400") and eof, r)
    stop(p)
    p = start([upload_bin, "--port", str(port), "--dir", d, "--max-stream", "1000"], port)
    r, eof = raw(port, b"POST /count HTTP/1.1\r\nHost: t\r\nTransfer-Encoding: chunked\r\n\r\n400\r\n" + b"x" * 1024 + b"\r\n0\r\n\r\n")
    ok("stream: a chunked body past --max-stream is a 413 that closes", r.startswith(b"HTTP/1.1 413") and eof, r)
    stop(p)

# Streamed responses
# ==================

def pattern_sha(n):
    """the sha256 of export's /bytes?n=N: a 16 KiB block of a pattern, over and over"""
    blk = bytes((i * 7 + 3) % 256 for i in range(16384))
    h, left = hashlib.sha256(), n
    while left:
        m = min(left, len(blk)); h.update(blk[:m]); left -= m
    return h.hexdigest()

def dechunk(b):
    """a chunked body, read strictly: its bytes, and whether it ended with the last chunk"""
    out = b""
    while True:
        line, _, b = b.partition(b"\r\n")
        n = int(line, 16)
        if n == 0:
            return out, b == b"\r\n"
        out, b = out + b[:n], b[n:]
        if not b.startswith(b"\r\n"):
            return out, False
        b = b[2:]

def check_pour(export, events, relay, tmp):
    port = PORT + 12
    errf = os.path.join(tmp, "export.err")
    p = subprocess.Popen([export, "--port", str(port)], stdout=subprocess.DEVNULL, stderr=open(errf, "w"))
    PROCS.append(p)
    if not up(port):
        sys.exit("never listened: export")
    r = get(port, "/export.csv?rows=3")
    h, _, body = r.partition(b"\r\n\r\n")
    rows, fin = dechunk(body)
    ok("pour: a body of unknown length is chunked (Stream.pour), the rows written a block at a time",
       b"transfer-encoding: chunked" in h and b"content-length" not in h.lower() and fin
       and rows == b"0,user0,0\n1,user1,2\n2,user2,4\n", r)
    r, eof = raw(port, b"GET /export.csv?rows=1 HTTP/1.1\r\nHost: t\r\n\r\nGET / HTTP/1.1\r\nHost: t\r\nConnection: close\r\n\r\n")
    ok("pour: after a chunked body the connection goes on (a pipelined request answered)",
       r.count(b"HTTP/1.1 200") == 2 and b"\r\n0\r\n\r\nHTTP/1.1 200" in r and eof, r)
    r = get(port, "/export.ndjson?rows=2")
    ok("pour: NDJSON, the same way", dechunk(r.partition(b"\r\n\r\n")[2])[0] ==
       b'{"id":0,"name":"user0","score":0}\n{"id":1,"name":"user1","score":2}\n', r)
    N = 1000 * 1000 * 1000
    base = peak_kb(p.pid)
    with Peak(p.pid) as pk:
        t0 = time.time()
        c = subprocess.run("curl -sS --fail 'http://127.0.0.1:%d/bytes?n=%d' | sha256sum" % (port, N), shell=True,
                           capture_output=True, text=True, timeout=300)
        dt = time.time() - t0
    ok("pour: 1 GB chunked, byte for byte (curl's own reading of the chunks), peak RSS %d kB (%d kB before), %.0f MB/s"
       % (pk.most, base, N / dt / 1e6), c.returncode == 0 and c.stdout.split()[0] == pattern_sha(N) and pk.most < base + 16384,
       (c.returncode, c.stdout, c.stderr[-200:], base, pk.most))
    r, eof = raw(port, b"GET /sized?n=25 HTTP/1.1\r\nHost: t\r\n\r\nGET / HTTP/1.1\r\nHost: t\r\nConnection: close\r\n\r\n")
    ok("pour: a declared length (Stream.pour.len) is a Content-Length, the body exactly it, and the connection goes on",
       r.startswith(b"HTTP/1.1 200 OK\r\n") and b"content-length: 25\r\n\r\n0123456789012345678901234HTTP/1.1 200" in r
       and b"transfer-encoding" not in r and eof, r)
    r, eof = raw(port, b"GET /sized?n=25&give=15 HTTP/1.1\r\nHost: t\r\n\r\nGET / HTTP/1.1\r\nHost: t\r\n\r\n")
    ok("pour: a producer short of its length: what it wrote, then the connection closes (nothing after it read)",
       r.endswith(b"content-length: 25\r\n\r\n012345678901234") and eof, r)
    r, eof = raw(port, b"GET /sized?n=25&give=35 HTTP/1.1\r\nHost: t\r\n\r\nGET / HTTP/1.1\r\nHost: t\r\n\r\n")
    time.sleep(0.2)
    ok("pour: a producer past its length: the write past it refused whole (ELarge), never more than declared, then close",
       r.endswith(b"content-length: 25\r\n\r\n01234567890123456789") and eof
       and "sized stopped after 20: the body is too large" in open(errf).read(), (r, open(errf).read()))
    r, eof = raw(port, b"HEAD /bytes?n=100000 HTTP/1.1\r\nHost: t\r\n\r\nHEAD /sized?n=25 HTTP/1.1\r\nHost: t\r\n\r\n"
                       b"GET /sized?n=3 HTTP/1.1\r\nHost: t\r\nConnection: close\r\n\r\n")
    ok("pour: HEAD sends the head only (chunked's, and the declared length's), and the connection goes on",
       r == b"HTTP/1.1 200 OK\r\ncontent-type: application/octet-stream\r\ntransfer-encoding: chunked\r\n\r\n"
            b"HTTP/1.1 200 OK\r\ncontent-type: text/plain\r\ncontent-length: 25\r\n\r\n"
            b"HTTP/1.1 200 OK\r\ncontent-type: text/plain\r\ncontent-length: 3\r\nconnection: close\r\n\r\n012" and eof, r)
    r, eof = raw(port, b"GET /export.csv?rows=2 HTTP/1.0\r\n\r\n")
    ok("pour: to HTTP/1.0, a body of unknown length runs to the close",
       r == b"HTTP/1.1 200 OK\r\ncontent-type: text/csv\r\nconnection: close\r\n\r\n0,user0,0\n1,user1,2\n" and eof, r)
    s = socket.create_connection(("127.0.0.1", port)); s.settimeout(5)
    s.sendall(b"GET /bytes?n=1000000000 HTTP/1.1\r\nHost: t\r\n\r\n")
    got = 0
    while got < 1 << 20:
        got += len(s.recv(65536))
    s.setsockopt(socket.SOL_SOCKET, socket.SO_LINGER, b"\x01\x00\x00\x00\x00\x00\x00\x00")
    s.close()
    t0, said = time.time(), ""
    while time.time() - t0 < 5 and "bytes stopped after" not in said:
        time.sleep(0.05)
        said = open(errf).read()
    line = [l for l in said.splitlines() if "bytes stopped after" in l]
    ok("pour: a client gone mid-body is an error to the producer (%s), within %.2f s, and the server goes on"
       % (line[0].split(": ", 1)[1] if line else "none", time.time() - t0),
       line and "closed the connection" in line[0] and get(port, "/").startswith(b"HTTP/1.1 200"), said)
    s = socket.socket(); s.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 4096)
    s.connect(("127.0.0.1", port))
    s.sendall(b"GET /bytes?n=1000000000 HTTP/1.1\r\nHost: t\r\n\r\n")
    t0, said = time.time(), ""
    while time.time() - t0 < 40 and "stalled" not in said:
        time.sleep(0.2)
        said = open(errf).read()
    dt = time.time() - t0
    s.close()
    line = [l for l in said.splitlines() if "bytes stopped after" in l and "stalled" in l]
    n = int(line[0].split("after ")[1].split(":")[0]) if line else -1
    ok("pour: a client that stops reading stops the producer (%d bytes written, the socket's buffers), then its send "
       "stalls past the send time: ETime, after %.1f s" % (n, dt), line and 0 <= n < 64 << 20 and 9 < dt < 35, (said, dt))
    rport = PORT + 14
    rerr = os.path.join(tmp, "relay.err")
    rl = subprocess.Popen([relay, "--port", str(rport), "--upstream", "http://127.0.0.1:%d" % port], stdout=subprocess.DEVNULL,
                          stderr=open(rerr, "w"))
    PROCS.append(rl)
    if not up(rport):
        sys.exit("never listened: relay_stream")
    N = 100 * 1000 * 1000
    base = peak_kb(rl.pid)
    with Peak(rl.pid) as pk:
        t0 = time.time()
        c = subprocess.run("curl -sS --fail 'http://127.0.0.1:%d/relay?path=/bytes%%3Fn%%3D%d' | sha256sum" % (rport, N), shell=True,
                           capture_output=True, text=True, timeout=300)
        dt = time.time() - t0
    ok("pour: a relay streams end to end (Client.stream into Stream.pour): 100 MB byte for byte, the relay's peak RSS %d kB "
       "(%d kB before), %.0f MB/s" % (pk.most, base, N / dt / 1e6),
       c.returncode == 0 and c.stdout.split()[0] == pattern_sha(N) and pk.most < base + 16384, (c.returncode, c.stdout, c.stderr[-200:]))
    r, eof = raw(rport, b"GET /relay?path=/nope HTTP/1.1\r\nHost: t\r\n\r\n")
    ok("pour: an upstream's 404, after the relay's head went: the body cut short (no last chunk), the connection closed",
       r.startswith(b"HTTP/1.1 200") and b"\r\n0\r\n\r\n" not in r and eof and "upstream answered 404" in open(rerr).read(), r)
    stop(rl)
    stop(p)
    port = PORT + 13
    p = start([events, "--port", str(port), "--keepalive-ms", "200", "--handler-ms", "600"], port)
    t0 = time.time()
    c = subprocess.run(["curl", "-N", "-sS", "-i", "--max-time", "10", "http://127.0.0.1:%d/ticks?n=3&ms=500" % port],
                       capture_output=True, text=True)
    dt = time.time() - t0
    h, _, b = c.stdout.replace("\r\n", "\n").partition("\n\n")
    evs = [e for e in b.split("\n\n") if e.startswith("event:")]
    ok("pour: server-sent events (Stream.events) with curl -N: each event as it comes, keepalives between, the end (%.2f s)" % dt,
       c.returncode == 0 and "content-type: text/event-stream" in h and "cache-control: no-cache" in h
       and evs == ["event: tick\nid: %d\ndata: %d" % (i, i) for i in range(3)] and b.count(": keepalive\n\n") >= 2
       and 0.9 < dt < 3, (c.returncode, c.stdout, c.stderr))
    ok("handler time: a stream begun runs past --handler-ms (600): only the handler's answer is timed, then the sends",
       c.returncode == 0 and len(evs) == 3 and dt > 0.9, dt)
    t0 = time.time()
    r, eof = raw(port, b"GET /ticks?n=1&delay=5000 HTTP/1.1\r\nHost: t\r\n\r\n", wait=4, total=4)
    dt = time.time() - t0
    ok("handler time: a Stream.get handler that has not answered at --handler-ms is a 503 that closes",
       r.startswith(b"HTTP/1.1 503") and b"connection: close" in r.lower() and eof and 0.5 < dt < 2.0, (r, eof, dt))
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
            b"Sec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==\r\n\r\n")[0]
    ok("ws: an upgrade with no Sec-WebSocket-Version is a 426 naming 13 (RFC 6455 4.4)",
       b" 426 " in r.split(b"\r\n", 1)[0] and b"sec-websocket-version: 13" in r.lower(), r[:300])
    r = raw(port, b"POST /room HTTP/1.1\r\nHost: t\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n"
            b"Sec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==\r\nSec-WebSocket-Version: 13\r\nContent-Length: 0\r\n\r\n")[0]
    ok("ws: a POST that asks to upgrade is a 400, as a HEAD is (RFC 6455 4.2.1)", b" 400 " in r.split(b"\r\n", 1)[0], r[:200])
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
    log = p.stderr.read().decode()
    ok("ws: Server.wrap logs the page and the room, its 101 and its refusals", "GET / 200" in log
       and "GET /room 101" in log and "GET /room 426" in log and "POST /room 400" in log, log[-600:])
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

# IPv6
# ====

def v6_loopback():
    try:
        s = socket.socket(socket.AF_INET6)
        s.bind(("::1", 0))
        s.close()
        return True
    except OSError:
        return False

def up6(port, tries=100):
    for _ in range(tries):
        try:
            socket.create_connection(("::1", port), timeout=0.2).close()
            return True
        except OSError:
            time.sleep(0.05)
    return False

def start6(args, port):
    p = subprocess.Popen(args, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
    PROCS.append(p)
    if not up6(port):
        sys.exit("never listened on ::1: " + " ".join(args))
    return p

def get_at(host, port, path, ctx=None):
    """a GET over host (either family), the Host field [::1]:port or host:port; the response's bytes"""
    s = socket.create_connection((host, port), timeout=5)
    if ctx:
        s = ctx.wrap_socket(s, server_hostname=host)
    s.sendall(("GET %s HTTP/1.1\r\nHost: t\r\nConnection: close\r\n\r\n" % path).encode())
    out = b""
    try:
        while True:
            b = s.recv(65536)
            if not b:
                break
            out += b
    except (socket.timeout, ssl.SSLError, ConnectionResetError):
        pass
    s.close()
    return out

def refused_at(host, port):
    try:
        socket.create_connection((host, port), timeout=1).close()
        return False
    except OSError:
        return True

def dual_name():
    """a name the resolver answers with both ::1 and 127.0.0.1, if there is one"""
    for name in ("localhost", "dual.v6.test"):
        try:
            got = {a[4][0] for a in socket.getaddrinfo(name, 80, type=socket.SOCK_STREAM)}
        except OSError:
            continue
        if "::1" in got and "127.0.0.1" in got:
            return name
    return None

def check_v6(hello, fetch_bin, tls_bin, room, chat_bin, tmp):
    if not v6_loopback():
        print("SKIP v6: this machine has no IPv6 loopback (::1 does not bind)")
        return
    # the server on ::1: reached there and not over IPv4, its banner bracketed
    port = PORT + 20
    p = start6([hello, "--port", str(port), "--host", "::1"], port)
    r = get_at("::1", port, "/")
    ok("v6: --host ::1 binds ::1", r.startswith(b"HTTP/1.1 200") and r.endswith(b"Hello, world!\n"), r)
    ok("v6: a server on ::1 is not reached over 127.0.0.1", refused_at("127.0.0.1", port))
    stop(p)
    log = p.stderr.read().decode()
    ok("v6: the banner names [::1]:port", ("listening on http://[::1]:%d" % port) in log, log)
    # on ::, both families (IPV6_V6ONLY off)
    port = PORT + 21
    p = start6([hello, "--port", str(port), "--host", "::"], port)
    r6, r4 = get_at("::1", port, "/"), get_at("127.0.0.1", port, "/")
    ok("v6: --host :: takes IPv6 and IPv4 both", r6.endswith(b"Hello, world!\n") and r4.endswith(b"Hello, world!\n"),
       (r6, r4))
    stop(p)
    log = p.stderr.read().decode()
    ok("v6: the banner names [::]:port", ("listening on http://[::]:%d" % port) in log, log)
    # a certificate for ::1 and 127.0.0.1 by IP SAN, and one for localhost only
    cert, key = os.path.join(tmp, "ip-cert.pem"), os.path.join(tmp, "ip-key.pem")
    subprocess.run(["openssl", "req", "-x509", "-newkey", "rsa:2048", "-keyout", key, "-out", cert, "-days", "2", "-nodes",
                    "-subj", "/CN=bend-net ip", "-addext", "subjectAltName=IP:::1,IP:127.0.0.1"],
                   capture_output=True, check=True)
    dcert, dkey = os.path.join(tmp, "dns-cert.pem"), os.path.join(tmp, "dns-key.pem")
    subprocess.run(["openssl", "req", "-x509", "-newkey", "rsa:2048", "-keyout", dkey, "-out", dcert, "-days", "2",
                    "-nodes", "-subj", "/CN=localhost", "-addext", "subjectAltName=DNS:localhost"],
                   capture_output=True, check=True)
    cli = ssl.create_default_context(cafile=cert)
    # the TLS server on ::1 and on ::, its request's remote each time
    port = PORT + 22
    p = start6([tls_bin, "--port", str(port), "--host", "::1", "--tls-cert", cert, "--tls-key", key], port)
    r = get_at("::1", port, "/", cli)
    ok("v6: the server over TLS on ::1, its IP SAN verified by Python; the remote is ::1",
       r.startswith(b"HTTP/1.1 200") and r.endswith(b"Hello over TLS, ::1\n"), r)
    c, out, err = fetch(fetch_bin, "--ca", cert, "https://[::1]:%d/" % port)
    ok("v6: the server over TLS on ::1, fetched by the client at https://[::1]:port/",
       c == 0 and out == "Hello over TLS, ::1\n", (c, out, err))
    stop(p)
    port = PORT + 23
    p = start6([tls_bin, "--port", str(port), "--host", "::", "--tls-cert", cert, "--tls-key", key], port)
    r = get_at("127.0.0.1", port, "/", cli)
    ok("v6: an IPv4 peer of a :: listener is its dotted address", r.endswith(b"Hello over TLS, 127.0.0.1\n"), r)
    stop(p)
    # the client to an IP-literal: the Host field bracketed, the pool keyed by it
    port = PORT + 24
    peer = Peer(port, host="::1")
    c, out, err = fetch(fetch_bin, "--twice", "http://[::1]:%d/conn" % port)
    ok("v6: the client fetches http://[::1]:port/, twice on one pooled connection",
       c == 0 and out == "conn 1conn 1", (c, out, err))
    hosts = [hs.get("host") for (_, _, hs, _) in peer.seen]
    ok("v6: its Host field is [::1]:port", hosts == ["[::1]:%d" % port] * 2, hosts)
    c, out, err = fetch(fetch_bin, "http://[::1]:%d/conn" % (PORT + 25))
    ok("v6: a refused connection to [::1] is Refused", c == 1 and "connection refused" in err, (c, err))
    c, out, err = fetch(fetch_bin, "http://[fe80::1%%25lo]:%d/" % port)
    ok("v6: a zone ID is a bad URL", c == 1 and "bad url" in err and "zone" in err, (c, err))
    # a name with both families: whichever listens is reached
    name = dual_name()
    if name is None:
        print("SKIP v6: no name resolves to both ::1 and 127.0.0.1 here (localhost has one family)")
    else:
        c, out, err = fetch(fetch_bin, "http://%s:%d/conn" % (name, port))
        ok("v6: %s reaches a peer on ::1 only (its AAAA)" % name, c == 0 and out.startswith("conn"), (c, out, err))
        port4 = PORT + 26
        Peer(port4)
        c, out, err = fetch(fetch_bin, "http://%s:%d/conn" % (name, port4))
        ok("v6: %s reaches a peer on 127.0.0.1 only (its A, after the other)" % name,
           c == 0 and out.startswith("conn"), (c, out, err))
    # TLS to an IP-literal: the IP SAN checked, no SNI sent
    names = []
    tctx = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER); tctx.load_cert_chain(cert, key)
    tctx.sni_callback = lambda s, n, c: names.append(n)
    tport = PORT + 27
    Peer(tport, tls=tctx, host="::1")
    c, out, err = fetch(fetch_bin, "--ca", cert, "https://[::1]:%d/conn" % tport)
    ok("v6: TLS to https://[::1]:port/ verifies the certificate's IP SAN", c == 0 and out.startswith("conn"), (c, out, err))
    ok("v6: and sends no SNI for the address (RFC 6066 3)", names == [None], names)
    dctx = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER); dctx.load_cert_chain(dcert, dkey)
    dport = PORT + 28
    Peer(dport, tls=dctx, host="::1")
    c, out, err = fetch(fetch_bin, "--ca", dcert, "https://[::1]:%d/conn" % dport)
    ok("v6: a certificate with no IP SAN for ::1 is refused", c == 1 and "tls:" in err, (c, err))
    # a WebSocket room on ::1, through ws://[::1]:port/
    port = PORT + 29
    p = start6([room, "--port", str(port), "--host", "::1"], port)
    url = "ws://[::1]:%d/room" % port
    ada = subprocess.Popen([chat_bin, url, "ada", "--wait-ms", "2500"], stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                           text=True)
    time.sleep(0.5)
    bob = subprocess.Popen([chat_bin, url, "bob", "over six", "--wait-ms", "1000"], stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT, text=True)
    b_out, a_out = bob.communicate(timeout=20)[0], ada.communicate(timeout=20)[0]
    ok("v6: ws://[::1]:port/: a room on ::1 broadcasts", a_out.split("\n")[:1] == ["< bob: over six"]
       and b_out.split("\n")[:1] == ["< bob: over six"], (a_out, b_out))
    stop(p)
    # the WebSocket client's Host field, as a raw listener on ::1 reads it
    port = PORT + 30
    ls = socket.socket(socket.AF_INET6); ls.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    ls.bind(("::1", port)); ls.listen(4); ls.settimeout(10)
    w = subprocess.Popen([chat_bin, "ws://[::1]:%d/x" % port, "cy", "--wait-ms", "200"], stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT, text=True)
    head = b""
    try:
        c, _ = ls.accept(); c.settimeout(5)
        while b"\r\n\r\n" not in head:
            b = c.recv(4096)
            if not b:
                break
            head += b
        c.close()
    except OSError:
        pass
    ls.close()
    w.communicate(timeout=20)
    ok("v6: the WebSocket client's Host field is [::1]:port", ("\r\nHost: [::1]:%d\r\n" % port).encode() in head, head)

def check_guide():
    """every Bend snippet in guide/NETWORKING.md and guide/net/*.md is in a file under net/, word for word"""
    srcs = []
    for d, _, fs in os.walk(HERE):
        srcs += [open(os.path.join(d, f)).read() for f in fs if f.endswith(".bend")]
    pages = [os.path.join(ROOT, "guide", "NETWORKING.md")]
    pages += sorted(os.path.join(ROOT, "guide", "net", f) for f in os.listdir(os.path.join(ROOT, "guide", "net"))
                    if f.endswith(".md"))
    for page in pages:
        guide = open(page).read()
        snips = [b.split("```", 1)[0] for b in guide.split("```python\n")[1:]]
        stale = [b for b in snips if not any(b in src for src in srcs)]
        ok("guide: each of %s's %d snippets is in a file under net/" % (os.path.relpath(page, ROOT), len(snips)),
           not stale, stale[0][:200] if stale else "")

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
        check_args(hello, files)
        check_signup(bins["signup"])
        check_client(fetch_bin, hello, tmp)
        check_stream(bins["upload"], tmp)
        check_pour(bins["export"], bins["events"], bins["relay_stream"], tmp)
        check_ws(bins["chat_server"], bins["ws_chat"], bins["ws_echo"])
        check_v6(hello, fetch_bin, bins["tls_server"], bins["chat_server"], bins["ws_chat"], tmp)
    finally:
        for p in PROCS:
            stop(p)
        shutil.rmtree(tmp, ignore_errors=True)
    print("%d failed" % len(FAILS) if FAILS else "all passed")
    sys.exit(1 if FAILS else 0)

if __name__ == "__main__":
    main()
