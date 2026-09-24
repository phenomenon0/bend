#!/usr/bin/env python3
"""The WebSocket client (net/ws.bend, driven by net/ws_cli.bend) against
real servers: the HTTP engine's /ws echo, plain and over TLS; a server
on Python's websockets library, when it is installed (pip install
websockets); a raw server here that speaks the bytes itself, to send
what no library will (masked frames, broken UTF-8, long pings, reserved
bits, orphan continuations, bad close codes, frames past the cap, and
handshakes answered wrong) and to check what the client sends back:
every frame masked, and the close code each violation calls for; and,
with --autobahn, the Autobahn test suite's fuzzing server (docker),
every client case but compression's (12.*, 13.*), with the pass rate.

With --server ECHO (net/examples/ws_echo.bend built), the server too
(net/ws_server.bend): the opening handshake and its refusals (426, 400,
405, 403 for an Origin not allowed), each frame a client may not send
failed with its close code, once, and the TCP connection closed, every
frame the server writes unmasked, fragments, pings, the message cap,
the keepalive, SIGTERM's 1001; against a raw client, net/ws_cli.bend
and Python's websockets; and with --autobahn, the fuzzing client
against it, every case but compression's.

    python3 net/ws_check.py ./wsc ./httpd 8860 [--server ./echo] [--autobahn]   # ports 8860-8868
"""
import asyncio, base64, hashlib, json, os, socket, struct, subprocess, sys, tempfile, threading, time

GUID = b"258EAFA5-E914-47DA-95CA-C5AB0DC85B11"
WSC, HTTPD, P = os.path.realpath(sys.argv[1]), os.path.realpath(sys.argv[2]), int(sys.argv[3])
fails, passes, procs = [], [], []


def up(port, secs=6):
    for _ in range(int(secs * 10)):
        try:
            socket.create_connection(("127.0.0.1", port), 0.2).close()
            return True
        except OSError:
            time.sleep(0.1)
    return False


def run(*args, timeout=30):
    r = subprocess.run([WSC, *args], capture_output=True, text=True, timeout=timeout)
    return (r.stdout + r.stderr).strip().split("\n")


def expect(name, want, *args, timeout=30):
    """the client's lines must be want, in order (each a prefix)"""
    try:
        got = run(*args, timeout=timeout)
    except subprocess.TimeoutExpired:
        got = ["TIMEOUT"]
    ok = len(got) == len(want) and all(g.startswith(w) for g, w in zip(got, want))
    (passes if ok else fails).append(name)
    print(("PASS " if ok else "FAIL ") + name + ("" if ok else ": " + " | ".join(got) + "  WANTED  " + " | ".join(want)))
    return ok


def check(name, ok, why=""):
    (passes if ok else fails).append(name)
    print(("PASS " if ok else "FAIL ") + name + ("" if ok else ": " + why))


# The raw server
# ==============
#
# A path picks the scenario. Each connection records the frames the
# client sent: (opcode, masked, payload), and the close code among them.

seen = {}
# connections still being served, per path: a check waits for them, so
# it never reads a log the server thread has not finished writing
busy = {}
idle = threading.Condition()


def accept_of(key):
    return base64.b64encode(hashlib.sha1(key.encode() + GUID).digest()).decode()


def frame(op, payload=b"", fin=True, rsv=0, mask=None, ln=None):
    b0 = (0x80 if fin else 0) | rsv | op
    n = len(payload) if ln is None else ln
    if n < 126:
        head = struct.pack("!BB", b0, n | (0x80 if mask else 0))
    elif n < 65536:
        head = struct.pack("!BBH", b0, 126 | (0x80 if mask else 0), n)
    else:
        head = struct.pack("!BBQ", b0, 127 | (0x80 if mask else 0), n)
    if mask:
        payload = bytes(c ^ mask[i % 4] for i, c in enumerate(payload))
        return head + mask + payload
    return head + payload


def read_exact(s, n):
    b = b""
    while len(b) < n:
        c = s.recv(n - len(b))
        if not c:
            raise EOFError
        b += c
    return b


def read_frame(s):
    b0, b1 = read_exact(s, 2)
    n = b1 & 127
    if n == 126:
        n = struct.unpack("!H", read_exact(s, 2))[0]
    elif n == 127:
        n = struct.unpack("!Q", read_exact(s, 8))[0]
    masked = bool(b1 & 0x80)
    key = read_exact(s, 4) if masked else b"\0\0\0\0"
    data = bytes(c ^ key[i % 4] for i, c in enumerate(read_exact(s, n)))
    return b0 & 15, masked, data


def client_frames(s, log, until_close=True, secs=3):
    s.settimeout(secs)
    try:
        while True:
            op, masked, data = read_frame(s)
            log.append((op, masked, data))
            if op == 8 and until_close:
                return
    except (EOFError, OSError):
        return


def head_of(s):
    b = b""
    while b"\r\n\r\n" not in b:
        c = s.recv(4096)
        if not c:
            return None, None
        b += c
    lines = b.split(b"\r\n")
    path = lines[0].split()[1].decode()
    key = ""
    for l in lines[1:]:
        if l.lower().startswith(b"sec-websocket-key:"):
            key = l.split(b":", 1)[1].strip().decode()
    return path, key


def ok101(key, extra=""):
    return ("HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n"
            "Sec-WebSocket-Accept: %s\r\n%s\r\n" % (accept_of(key), extra)).encode()


def scenario(s):
    path, key = head_of(s)
    if path is None:
        return
    with idle:
        busy[path] = busy.get(path, 0) + 1
    try:
        scenario_on(s, path, key)
    finally:
        with idle:
            busy[path] -= 1
            idle.notify_all()


def settled(path, secs=10):
    with idle:
        idle.wait_for(lambda: busy.get(path, 0) == 0, timeout=secs)


def scenario_on(s, path, key):
    log = seen.setdefault(path, [])
    sc = path.strip("/")
    bad_hs = {
        "acc": "HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: %s\r\n\r\n" % accept_of(key + "x"),
        "noup": "HTTP/1.1 101 Switching Protocols\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: %s\r\n\r\n" % accept_of(key),
        "st200": "HTTP/1.1 200 OK\r\nContent-Length: 0\r\n\r\n",
        "ext": "HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: %s\r\nSec-WebSocket-Extensions: permessage-deflate\r\n\r\n" % accept_of(key),
        "proto": "HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: %s\r\nSec-WebSocket-Protocol: superchat\r\n\r\n" % accept_of(key),
    }
    if sc in bad_hs:
        s.sendall(bad_hs[sc].encode())
        time.sleep(0.3)
        return
    if sc == "early":
        # the 101 and a frame in one write: the frame is the first message
        s.sendall(ok101(key) + frame(1, b"early bird"))
        client_frames(s, log)
        s.sendall(frame(8, struct.pack("!H", 1000)))
        return
    s.sendall(ok101(key, "Sec-WebSocket-Protocol: chat\r\n" if sc == "chat" else ""))
    if sc in ("echo", "chat"):
        # every data frame back unmasked, until the client's close, answered
        s.settimeout(5)
        try:
            while True:
                op, masked, data = read_frame(s)
                log.append((op, masked, data))
                if op == 8:
                    s.sendall(frame(8, data[:2]))
                    return
                if op in (1, 2):
                    s.sendall(frame(op, data))
        except (EOFError, OSError):
            return
    bad = {
        "masked": frame(1, b"Hello", mask=b"\x37\xfa\x21\x3d"),
        "utf8": frame(1, b"\xce\xba\xe1\xbd\xb9\xcf\x83\xce\xbc\xce\xb5\xed\xa0\x80edited"),
        "ctl": frame(9, b"x" * 126),
        "rsv": frame(1, b"hi", rsv=0x40),
        "opcode": frame(3, b""),
        "orphan": frame(0, b"lost"),
        "interleave": frame(1, b"one", fin=False) + frame(1, b"two"),
        "ctlfrag": frame(9, b"p", fin=False),
        "close1005": frame(8, struct.pack("!H", 1005)),
        "close1": frame(8, b"\x03"),
        "closeutf8": frame(8, struct.pack("!H", 1000) + b"\xff"),
        "big": frame(2, b"z" * 2000),
        "bigfrag": frame(2, b"z" * 600, fin=False) + frame(0, b"z" * 600),
        "len16": frame(2, b"q" * 100, ln=None)[:1] + bytes([126, 0, 100]) + b"q" * 100,
    }
    if sc in bad:
        s.sendall(bad[sc])
        client_frames(s, log)
        return
    if sc == "frag":
        # a text in three fragments, a ping between, a character cut across two
        s.sendall(frame(1, b"h\xc3", fin=False) + frame(9, b"between") + frame(0, b"\xa9l", fin=False)
                  + frame(10, b"unasked") + frame(0, b"lo"))
        client_frames(s, log)
        s.sendall(frame(8, struct.pack("!H", 1000)))
        return
    if sc == "ping":
        s.sendall(frame(9, b"are you there") + frame(1, b"after"))
        client_frames(s, log)
        s.sendall(frame(8, struct.pack("!H", 1000)))
        return
    if sc == "bye":
        # the server closes first; the client answers with the code and
        # waits for the TCP connection to end
        s.sendall(frame(8, struct.pack("!H", 4001) + "farewell é".encode()))
        client_frames(s, log)
        time.sleep(0.2)
        return
    if sc == "eof":
        return
    if sc == "silent":
        # nothing until the client speaks, then one message and the close
        s.settimeout(5)
        try:
            log.append(read_frame(s))
        except (EOFError, OSError):
            return
        s.sendall(frame(1, b"late"))
        client_frames(s, log)
        s.sendall(frame(8, struct.pack("!H", 1000)))
        return


def raw_server(port):
    ls = socket.socket()
    ls.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    ls.bind(("127.0.0.1", port))
    ls.listen(64)

    def serve():
        while True:
            try:
                c, _ = ls.accept()
            except OSError:
                return
            def one(c=c):
                try:
                    scenario(c)
                except Exception as e:  # a scenario's own failure shows as the client's
                    print("raw server:", e)
                finally:
                    c.close()
            threading.Thread(target=one, daemon=True).start()
    threading.Thread(target=serve, daemon=True).start()
    return ls


def frames_of(path):
    settled(path)
    return seen.get(path, [])


def closes(path):
    settled(path)
    return [struct.unpack("!H", d[:2])[0] if len(d) >= 2 else None for op, m, d in seen.get(path, []) if op == 8]


def all_masked(path):
    settled(path)
    fs = seen.get(path, [])
    return bool(fs) and all(m for op, m, d in fs)


# The websockets library's server
# ===============================

def lib_server(port):
    try:
        from websockets.asyncio.server import serve
    except ImportError:
        return None

    async def handler(ws):
        path = ws.request.path
        if path == "/echo":
            async for m in ws:
                await ws.send(m)
        elif path == "/frag":
            await ws.send(["Hel", "lo ", "wörld"])
            await ws.send([b"\x00\x01", b"\x02"])
            await ws.wait_closed()
        elif path == "/ping":
            pong = await ws.ping(b"lib")
            await asyncio.wait_for(pong, 5)
            await ws.send("pong came")
            await ws.wait_closed()
        elif path == "/close":
            await ws.close(4000, "done here")
        elif path == "/big":
            await ws.send(bytes(i % 251 for i in range(1 << 20)))
            await ws.wait_closed()

    def main():
        async def go():
            async with serve(handler, "127.0.0.1", port, subprotocols=None, max_size=1 << 24,
                             compression=None):
                await asyncio.Future()
        asyncio.run(go())
    threading.Thread(target=main, daemon=True).start()
    return True


def autobahn(port):
    d = tempfile.mkdtemp()
    os.makedirs(d + "/reports")
    json.dump({"url": "ws://127.0.0.1:%d" % port, "outdir": "/reports", "cases": ["*"],
               "exclude-cases": ["12.*", "13.*"], "exclude-agent-cases": {}}, open(d + "/fs.json", "w"))
    name = "bend-ws-autobahn-%d" % port
    subprocess.run(["docker", "rm", "-f", name], capture_output=True)
    r = subprocess.run(["docker", "run", "-d", "--name", name, "--network", "host", "-v", d + ":/config",
                        "-v", d + "/reports:/reports", "crossbario/autobahn-testsuite", "wstest", "-m",
                        "fuzzingserver", "-s", "/config/fs.json", "--webport", str(port + 1)],
                       capture_output=True, text=True)
    if r.returncode != 0 or not up(port, 60):
        print("SKIP autobahn: the fuzzing server did not start", r.stderr.strip()[:200])
        subprocess.run(["docker", "rm", "-f", name], capture_output=True)
        return
    try:
        run("ws://127.0.0.1:%d" % port, "--autobahn", "bend", "--recv-ms", "10000", timeout=1800)
        res = json.load(open(d + "/reports/index.json"))["bend"]
        good = [k for k, v in res.items() if v["behavior"] in ("OK", "NON-STRICT", "INFORMATIONAL")
                and v["behaviorClose"] in ("OK", "INFORMATIONAL")]
        strict = [k for k, v in res.items() if v["behavior"] == "OK" and v["behaviorClose"] == "OK"]
        print("autobahn: %d / %d cases pass (%d strictly OK); failing: %s" % (
            len(good), len(res), len(strict), sorted(set(res) - set(good))))
        check("autobahn.all", len(good) == len(res) and len(res) > 0)
    finally:
        subprocess.run(["docker", "rm", "-f", name], capture_output=True)



# The server (net/ws_server.bend)
# ===============================
#
# net/examples/ws_echo.bend, driven by a raw client here (to send what
# no library will: unmasked frames, reserved bits, long pings, broken
# UTF-8, bad close codes, handshakes asked wrong, and to check what the
# server writes: every frame unmasked, the close each violation calls
# for, once), by net/ws_cli.bend, by Python's websockets, and with
# --autobahn by the Autobahn test suite's fuzzing client (docker), every
# case but compression's (12.*, 13.*).

KEY = "dGhlIHNhbXBsZSBub25jZQ=="


def srv_open(port, path="/echo", key=KEY, ver="13", method="GET", http="HTTP/1.1", extra="", early=b"",
             up=True):
    """a raw opening request: the status, the head's fields, the socket, what came after the head"""
    s = socket.create_connection(("127.0.0.1", port), 3)
    h = "%s %s %s\r\nHost: 127.0.0.1\r\n" % (method, path, http)
    if up:
        h += "Upgrade: websocket\r\nConnection: Upgrade\r\n"
    if key is not None:
        h += "Sec-WebSocket-Key: %s\r\n" % key
    if ver is not None:
        h += "Sec-WebSocket-Version: %s\r\n" % ver
    s.sendall((h + extra + "\r\n").encode() + early)
    b = b""
    s.settimeout(3)
    while b"\r\n\r\n" not in b:
        c = s.recv(65536)
        if not c:
            break
        b += c
    head, _, rest = b.partition(b"\r\n\r\n")
    lines = head.decode("latin-1").split("\r\n")
    status = int(lines[0].split()[1]) if len(lines[0].split()) > 1 else 0
    fields = {}
    for l in lines[1:]:
        n, _, v = l.partition(":")
        fields.setdefault(n.strip().lower(), []).append(v.strip())
    return status, fields, s, rest


class Buf:
    """a socket with what came before it, read as frames"""
    def __init__(self, s, rest):
        self.s, self.b = s, rest

    def need(self, n):
        while len(self.b) < n:
            c = self.s.recv(65536)
            if not c:
                raise EOFError
            self.b += c
        out, self.b = self.b[:n], self.b[n:]
        return out

    def frame(self):
        b0, b1 = self.need(2)
        n = b1 & 127
        if n == 126:
            n = struct.unpack("!H", self.need(2))[0]
        elif n == 127:
            n = struct.unpack("!Q", self.need(8))[0]
        masked = bool(b1 & 0x80)
        key = self.need(4) if masked else b"\0\0\0\0"
        data = bytes(c ^ key[i % 4] for i, c in enumerate(self.need(n)))
        return b0 & 15, masked, data, b0 & 0x80

    def frames(self, secs=3):
        """every frame until the close, and whether the TCP connection ended after it"""
        out, eof = [], False
        self.s.settimeout(secs)
        try:
            while True:
                f = self.frame()
                out.append(f)
                if f[0] == 8:
                    break
            try:
                eof = self.s.recv(1) == b""
            except OSError:
                eof = False
        except (EOFError, OSError):
            eof = True
        return out, eof


def M(op, payload=b"", fin=True, rsv=0, ln=None):
    return frame(op, payload, fin, rsv, b"\x37\xfa\x21\x3d", ln)


def srv_case(name, port, send, want, early=False):
    """frames sent after (or with) the handshake; the frames the server writes back, and the close"""
    try:
        st, fs, s, rest = srv_open(port, early=send if early else b"")
        if not early:
            s.sendall(send)
        got, eof = Buf(s, rest).frames()
        s.close()
    except OSError as e:
        check(name, False, repr(e))
        return []
    ok = st == 101 and [(op, d) for op, m, d, fin in got] == want and not any(m for op, m, d, fin in got)
    ok = ok and (eof or not want or want[-1][0] != 8)
    check(name, ok, "status %d, frames %s, eof %s" % (st, [(op, m, d[:40]) for op, m, d, fin in got], eof))
    return got


def close(code, reason=b""):
    return struct.pack("!H", code) + reason


def server_checks(echo):
    E, S, T = P + 5, P + 6, P + 7
    procs.append(subprocess.Popen([echo, "--port", str(E), "--host", "127.0.0.1"], stdout=subprocess.DEVNULL,
                                  stderr=subprocess.DEVNULL))
    procs.append(subprocess.Popen([echo, "--port", str(S), "--host", "127.0.0.1", "--max-msg", "1000",
                                   "--ping-ms", "300", "--pong-ms", "300", "--origin", "https://ok.example"],
                                  stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL))
    for port in (E, S):
        up(port)

    # the opening handshake (RFC 6455 4.2.2): the RFC's own key, a
    # subprotocol chosen from those offered, permessage-deflate declined
    st, fs, s, rest = srv_open(E, extra="Sec-WebSocket-Protocol: chat, echo\r\n"
                               "Sec-WebSocket-Extensions: permessage-deflate; client_max_window_bits\r\n")
    s.close()
    check("srv.hs.101", st == 101 and fs.get("sec-websocket-accept") == ["s3pPLMBiTxaQ9kYGzzhZRbK+xOo="]
          and fs.get("upgrade", [""])[0].lower() == "websocket" and "upgrade" in fs.get("connection", [""])[0].lower()
          and fs.get("sec-websocket-protocol") == ["echo"] and "sec-websocket-extensions" not in fs, str((st, fs)))
    st, fs, s, rest = srv_open(E, extra="Sec-WebSocket-Protocol: superchat\r\n")
    s.close()
    check("srv.hs.proto_not_offered", st == 101 and "sec-websocket-protocol" not in fs, str((st, fs)))
    # a plain GET is told to upgrade, and the connection goes on
    st, fs, s, rest = srv_open(E, up=False, key=None, ver=None)
    s.sendall(b"GET / HTTP/1.1\r\nHost: x\r\n\r\n")
    s.settimeout(3)
    more = rest
    try:
        while b"200 OK" not in more:
            c = s.recv(4096)
            if not c:
                break
            more += c
    except OSError:
        pass
    s.close()
    check("srv.hs.426", st == 426 and fs.get("sec-websocket-version") == ["13"] and b"200 OK" in more, str((st, fs)))
    for name, kw, want in [("srv.hs.version", dict(ver="8"), 426), ("srv.hs.no_key", dict(key=None), 426),
                           ("srv.hs.bad_key", dict(key="abc"), 400), ("srv.hs.key_no_pad", dict(key="dGhlIHNhbXBsZSBub25jZQAA"), 400),
                           ("srv.hs.http10", dict(http="HTTP/1.0"), 426), ("srv.hs.post", dict(method="POST"), 405),
                           ("srv.hs.no_route", dict(path="/nope"), 404)]:
        st, fs, s, rest = srv_open(E, **kw)
        s.close()
        check(name, st == want, str((st, fs)))
    st, fs, s, rest = srv_open(S, extra="Origin: https://evil.example\r\n")
    s.close()
    check("srv.origin.refused", st == 403, str(st))
    st, fs, s, rest = srv_open(S, extra="Origin: https://ok.example\r\n")
    s.close()
    check("srv.origin.allowed", st == 101, str(st))

    # frames: echoed, unmasked; each violation failed with its code, once, and the TCP connection closed
    srv_case("srv.echo", E, M(1, "héllo".encode()) + M(2, bytes(300)) + M(8, close(1000)),
             [(1, "héllo".encode()), (2, bytes(300)), (8, close(1000))])
    srv_case("srv.early", E, M(1, b"early") + M(8, close(1000)), [(1, b"early"), (8, close(1000))], early=True)
    srv_case("srv.ping", E, M(9, b"are you there") + M(8, close(1000)), [(10, b"are you there"), (8, close(1000))])
    srv_case("srv.frag", E, M(1, "hé".encode()[:2], fin=False) + M(9, b"between") + M(0, "hé".encode()[2:] + b"llo")
             + M(8, close(1000)), [(10, b"between"), (1, "héllo".encode()), (8, close(1000))])
    srv_case("srv.close_echoed", E, M(8, close(4001, b"bye")) + M(9, b"after"), [(8, close(4001))])
    srv_case("srv.close_empty", E, M(8), [(8, b"")])
    for name, send, code in [("unmasked", frame(1, b"Hello"), 1002), ("rsv1", M(1, b"x", rsv=0x40), 1002),
                             ("opcode", M(3), 1002), ("ctl_long", M(9, bytes(126)), 1002),
                             ("ctl_frag", M(9, b"x", fin=False), 1002), ("orphan", M(0, b"x"), 1002),
                             ("interleave", M(1, b"a", fin=False) + M(1, b"b"), 1002),
                             ("utf8", M(1, b"\xc0\xaf"), 1007), ("close1005", M(8, close(1005)), 1002),
                             ("close1", M(8, b"\x03"), 1002), ("close_utf8", M(8, close(1000, b"\xff")), 1007),
                             ("len16", M(2, b"x" * 5, ln=5)[:1] + bytes([0x80 | 126, 0, 5]) + b"\x37\xfa\x21\x3d" + b"x" * 5, 1002)]:
        srv_case("srv." + name, E, send, [(8, close(code))])
    srv_case("srv.big", S, M(2, bytes(2000)), [(8, close(1009))])
    srv_case("srv.big_frags", S, M(2, bytes(600), fin=False) + M(0, bytes(600)), [(8, close(1009))])
    srv_case("srv.at_cap", S, M(2, bytes(1000)) + M(8, close(1000)), [(2, bytes(1000)), (8, close(1000))])

    # the keepalive: a silent client is pinged after 300 ms, and dropped with 1011 300 ms later
    st, fs, s, rest = srv_open(S)
    t0 = time.time()
    got, eof = Buf(s, rest).frames(secs=5)
    dt = time.time() - t0
    s.close()
    check("srv.keepalive.drop", st == 101 and [op for op, m, d, fin in got] == [9, 8] and got[-1][2] == close(1011)
          and eof and 0.5 < dt < 2.5, "%s %s %.2fs" % ([(op, d) for op, m, d, fin in got], eof, dt))
    # our own client (net/ws_cli.bend) against the echo, and past the keepalive: it answers pings
    expect("srv.wsc.echo", ["open", "sent text", "text 5 hello", "sent binary", "binary 70000 sum 3980416790",
                            "sent ping", "sent text", "text 9 héllo € \U0001d11e", "close answered 1000"],
           "ws://127.0.0.1:%d/echo" % E, "t:hello", "r", "b:70000", "r", "p:hi", "t:héllo € \U0001d11e", "r")
    expect("srv.wsc.proto", ["open", "sent text", "text 1 x", "close answered 1000"],
           "ws://127.0.0.1:%d/echo" % E, "--proto", "echo", "t:x", "r")
    expect("srv.wsc.too_big", ["open", "sent binary", "closed 1009", "close answered 1009"],
           "ws://127.0.0.1:%d/echo" % S, "b:2000", "r")

    try:
        import websockets
        from websockets.asyncio.client import connect
    except ImportError:
        print("SKIP srv.lib: pip install websockets")
        return

    async def lib():
        out = {}
        async with connect("ws://127.0.0.1:%d/echo" % E, subprotocols=["echo"], max_size=1 << 24) as ws:
            out["proto"] = ws.subprotocol
            out["ext"] = ws.response.headers.get("Sec-WebSocket-Extensions")
            await ws.send("wörld")
            out["text"] = await ws.recv()
            await ws.send(bytes(range(256)) * 4096)
            out["big"] = len(await ws.recv())
            await ws.send(["frag", "mented ", "wörld"])
            out["frag"] = await ws.recv()
            pong = await ws.ping(b"lib")
            await asyncio.wait_for(pong, 3)
            out["pong"] = True
        out["close"] = ws.close_code
        async with connect("ws://127.0.0.1:%d/echo" % S) as ws:
            await asyncio.sleep(1.5)
            await ws.send("still here")
            out["alive"] = await ws.recv()
        return out

    try:
        out = asyncio.run(lib())
    except Exception as e:
        out = {"error": repr(e)}
    check("srv.lib", out.get("proto") == "echo" and out.get("ext") is None and out.get("text") == "wörld"
          and out.get("big") == 1 << 20 and out.get("frag") == "fragmented wörld" and out.get("pong")
          and out.get("close") == 1000 and out.get("alive") == "still here", str(out))

    # SIGTERM: the connection hears 1001, and the server ends
    procs.append(subprocess.Popen([echo, "--port", str(T), "--host", "127.0.0.1"], stdout=subprocess.DEVNULL,
                                  stderr=subprocess.DEVNULL))
    up(T)

    async def term():
        async with connect("ws://127.0.0.1:%d/echo" % T) as ws:
            await ws.send("x")
            await ws.recv()
            procs[-1].send_signal(15)
            try:
                await asyncio.wait_for(ws.recv(), 5)
            except websockets.ConnectionClosed:
                pass
        return ws.close_code

    try:
        code = asyncio.run(term())
        ended = procs[-1].wait(8)
    except Exception as e:
        code, ended = repr(e), None
    check("srv.sigterm.1001", code == 1001 and ended == 0, "code %s, exit %s" % (code, ended))


def server_autobahn(echo, port):
    procs.append(subprocess.Popen([echo, "--port", str(port), "--host", "127.0.0.1", "--max-msg", "67108864"],
                                  stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL))
    up(port)
    d = tempfile.mkdtemp()
    os.makedirs(d + "/reports")
    json.dump({"outdir": "/reports", "servers": [{"agent": "bend", "url": "ws://127.0.0.1:%d/echo" % port}],
               "cases": ["*"], "exclude-cases": ["12.*", "13.*"], "exclude-agent-cases": {}},
              open(d + "/fc.json", "w"))
    name = "bend-ws-autobahn-srv-%d" % port
    subprocess.run(["docker", "rm", "-f", name], capture_output=True)
    try:
        r = subprocess.run(["docker", "run", "--name", name, "--network", "host", "-v", d + ":/config",
                            "-v", d + "/reports:/reports", "crossbario/autobahn-testsuite", "wstest", "-m",
                            "fuzzingclient", "-s", "/config/fc.json"], capture_output=True, text=True, timeout=3000)
        if r.returncode != 0 or not os.path.exists(d + "/reports/index.json"):
            print("SKIP autobahn server: the fuzzing client did not run", r.stderr.strip()[-300:])
            return
        res = json.load(open(d + "/reports/index.json"))["bend"]
        good = [k for k, v in res.items() if v["behavior"] in ("OK", "NON-STRICT", "INFORMATIONAL")
                and v["behaviorClose"] in ("OK", "INFORMATIONAL")]
        strict = [k for k, v in res.items() if v["behavior"] == "OK" and v["behaviorClose"] == "OK"]
        print("autobahn server: %d / %d cases pass (%d strictly OK); failing: %s; not strict: %s" % (
            len(good), len(res), len(strict), sorted(set(res) - set(good)), sorted(set(res) - set(strict))))
        check("autobahn.server.all", len(good) == len(res) and len(res) > 0)
    finally:
        subprocess.run(["docker", "rm", "-f", name], capture_output=True)

def main():
    tmp = tempfile.mkdtemp()
    os.makedirs(tmp + "/www")
    subprocess.run(["openssl", "req", "-x509", "-newkey", "rsa:2048", "-keyout", tmp + "/key.pem", "-out",
                    tmp + "/cert.pem", "-days", "2", "-nodes", "-subj", "/CN=localhost", "-addext",
                    "subjectAltName=DNS:localhost"], capture_output=True, check=True)
    procs.append(subprocess.Popen([HTTPD, "--port", str(P), "--root", tmp + "/www"],
                                  stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL))
    procs.append(subprocess.Popen([HTTPD, "--port", str(P + 1), "--root", tmp + "/www", "--tls-cert",
                                   tmp + "/cert.pem", "--tls-key", tmp + "/key.pem"],
                                  stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL))
    ls = raw_server(P + 2)
    lib = lib_server(P + 3)
    for port in (P, P + 1, P + 2):
        up(port)
    E, T, R, L = ("ws://127.0.0.1:%d" % P, "wss://localhost:%d" % (P + 1), "ws://127.0.0.1:%d" % (P + 2),
                  "ws://127.0.0.1:%d" % (P + 3))
    ca = ("--ca", tmp + "/cert.pem")

    # the engine's echo, plain and over TLS
    steps = ["t:hello", "r", "b:70000", "r", "p:hi", "t:héllo € \U0001d11e", "r", "b:0", "r", "c:1000"]
    want = ["open", "sent text", "text 5 hello", "sent binary", "binary 70000 sum 3980416790", "sent ping",
            "sent text", "text 9 héllo € \U0001d11e", "sent binary", "binary 0 sum 7", "close answered 1000"]
    expect("engine.echo", want, E + "/ws", *steps)
    expect("engine.tls.echo", want, T + "/ws", *ca, *steps)
    expect("engine.big", ["open", "sent binary", "binary 1000000 sum", "close answered 1000"],
           E + "/ws", "b:1000000", "r")
    expect("engine.tls.untrusted", ["error no connection (13)"], T + "/ws")
    expect("engine.tls.misnamed", ["error no connection (13)"], "wss://127.0.0.1:%d/ws" % (P + 1), *ca)
    expect("engine.not_ws", ["error handshake refused: status 404, not 101"], E + "/nope")
    expect("engine.refused", ["error no connection (111)"], "ws://127.0.0.1:%d/" % (P + 4))
    expect("engine.url", ["error not a ws:// or wss:// URL"], "http://127.0.0.1:%d/" % P)
    expect("engine.dns", ["error the name did not resolve"], "ws://no-such-host.invalid/")

    # the raw server: what a library will not send
    expect("raw.echo", ["open", "sent text", "text 2 hi", "sent binary", "binary 300 sum", "close answered 1000"],
           R + "/echo", "t:hi", "r", "b:300", "r")
    check("raw.echo.masked", all_masked("/echo") and closes("/echo") == [1000], str(seen.get("/echo"))[:300])
    for sc, code in [("masked", 1002), ("utf8", 1007), ("ctl", 1002), ("rsv", 1002), ("opcode", 1002),
                     ("orphan", 1002), ("interleave", 1002), ("ctlfrag", 1002), ("close1005", 1002),
                     ("close1", 1002), ("closeutf8", 1007), ("bigfrag", 1009)]:
        expect("raw." + sc, ["open", "error the connection failed with %d" % code],
               R + "/" + sc, "r", "--max", "1000")
        check("raw.%s.sends_%d" % (sc, code), closes("/" + sc) == [code] and all_masked("/" + sc),
              str(seen.get("/" + sc))[:200])
    expect("raw.big", ["open", "error the connection failed with 1009"], R + "/big", "r",
           "--max", "1000")
    check("raw.big.sends_1009", closes("/big") == [1009], str(seen.get("/big"))[:200])
    # a length in the two-byte form that fits in the one-byte form (RFC 6455 5.2: minimal)
    expect("raw.len16", ["open", "error the connection failed with 1002"], R + "/len16", "r")
    check("raw.len16.sends_1002", closes("/len16") == [1002], str(seen.get("/len16"))[:200])
    for sc, why in [("acc", "Sec-WebSocket-Accept is not the key's"), ("noup", "no Upgrade: websocket"),
                    ("st200", "status 200, not 101"), ("ext", "an extension nobody asked for"),
                    ("proto", "a subprotocol nobody offered")]:
        expect("raw.hs." + sc, ["error handshake refused: " + why], R + "/" + sc, "--proto", "chat")
    expect("raw.chat", ["open", "sent text", "text 1 x", "close answered 1000"], R + "/chat", "--proto", "chat",
           "t:x", "r")
    expect("raw.early", ["open", "text 10 early bird", "close answered 1000"], R + "/early", "r")
    expect("raw.frag", ["open", "text 5 héllo", "closed 1000", "close answered 1000"], R + "/frag", "r", "r")
    check("raw.frag.pong", [(op, d) for op, m, d in frames_of("/frag") if op == 10] == [(10, b"between")]
          and all_masked("/frag"), str(seen.get("/frag"))[:200])
    expect("raw.ping", ["open", "text 5 after", "close answered 1000"], R + "/ping", "r")
    check("raw.ping.pong", [(op, d) for op, m, d in frames_of("/ping") if op == 10] == [(10, b"are you there")],
          str(seen.get("/ping"))[:200])
    expect("raw.bye", ["open", "closed 4001 farewell é", "close answered 4001"], R + "/bye", "r")
    check("raw.bye.echoed", closes("/bye") == [4001] and all_masked("/bye"), str(seen.get("/bye")))
    expect("raw.eof", ["open", "error the peer closed the connection without a close frame (1006)"],
           R + "/eof", "r")
    expect("raw.timeout", ["open", "error timed out", "sent text", "text 4 late", "close answered 1000"],
           R + "/silent", "--recv-ms", "300", "r", "t:x", "r")

    # the websockets library
    if lib is None:
        print("SKIP lib: pip install websockets")
    else:
        up(P + 3)
        expect("lib.echo", ["open", "sent text", "text 5 wörld", "sent binary", "binary 100000 sum",
                            "sent ping", "close answered 1000"], L + "/echo", "t:wörld", "r", "b:100000", "r",
               "p:x")
        expect("lib.frag", ["open", "text 11 Hello wörld", "binary 3 sum", "close answered 1000"],
               L + "/frag", "r", "r")
        expect("lib.ping", ["open", "text 9 pong came", "close answered 1000"], L + "/ping", "r")
        expect("lib.close", ["open", "closed 4000 done here", "close answered 4000"], L + "/close", "r")
        expect("lib.big", ["open", "binary 1048576 sum", "close answered 1000"], L + "/big", "r")

    if "--autobahn" in sys.argv and "--server-only" not in sys.argv:
        autobahn(P + 4)

    if "--server" in sys.argv:
        echo = os.path.realpath(sys.argv[sys.argv.index("--server") + 1])
        server_checks(echo)
        if "--autobahn" in sys.argv:
            server_autobahn(echo, P + 8)

    ls.close()
    for p in procs:
        p.kill()
    print("PASS: %d / %d" % (len(passes), len(passes) + len(fails)))
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    try:
        main()
    finally:
        for p in procs:
            p.kill()
