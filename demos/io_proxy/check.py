#!/usr/bin/env python3
# The proxy against an upstream that records every byte it is sent.
# Each case writes raw bytes to the proxy on a fresh connection, reads
# what comes back, and then looks at what the upstream got: the
# smuggling vectors (CL.TE, TE.CL, the TE.TE obfuscations, a doubled
# Content-Length, an obs-fold, a bare LF, an HTTP/2 preface, a request
# hidden in a body) must never put more requests upstream than the
# client's framing, read by the RFC, holds -- none, where it refuses
# them -- and nothing upstream may carry a hop-by-hop field or a
# Transfer-Encoding. Then the response side (hop fields dropped, a
# chunked response re-framed with a length), pooling (one upstream
# connection for many client ones), 100-continue, and the error paths
# (an upstream that hangs: 504; one that closes early or is not there:
# 502, with no partial response leaked).
#
#   python3 demos/io_proxy/check.py ./proxyd 20120          (uses 20120..20124)
#   python3 demos/io_proxy/check.py ./proxyd 20120 --nginx  (the same cases
#                                                            against nginx, a table)
import os, re, shutil, socket, subprocess, sys, tempfile, threading, time

HOP = [b'connection', b'keep-alive', b'proxy-connection', b'te', b'transfer-encoding', b'upgrade', b'trailer']

# The recording upstream
# ======================
# A strict HTTP/1.1 reader: a head ends at CRLF CRLF, a body is exactly
# the Content-Length's bytes (none without one); anything else (a
# Transfer-Encoding, a malformed head) is noted and the connection is
# closed. It answers each request by its path.

class Upstream:
  def __init__(self, port):
    self.port = port
    self.lock = threading.Lock()
    self.conns = []           # [ [ (head bytes, body bytes) ... ] per connection ]
    self.raw = []             # every byte, per connection
    self.bad = []             # what the strict reader could not read
    self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    self.sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    self.sock.bind(('127.0.0.1', port))
    self.sock.listen(128)
    threading.Thread(target=self.accept, daemon=True).start()

  def mark(self):
    with self.lock:
      return (len(self.conns), [len(c) for c in self.conns])

  def since(self, m):
    n, lens = m
    with self.lock:
      reqs = []
      for i, c in enumerate(self.conns):
        reqs += c[lens[i]:] if i < n else c
      return reqs, len(self.conns) - n

  def accept(self):
    while True:
      try:
        c, _ = self.sock.accept()
      except OSError:
        return
      with self.lock:
        i = len(self.conns); self.conns.append([]); self.raw.append(b'')
      threading.Thread(target=self.serve, args=(c, i), daemon=True).start()

  def serve(self, c, i):
    buf = b''
    try:
      while True:
        while b'\r\n\r\n' not in buf:
          d = c.recv(65536)
          if not d:
            return
          buf += d
          with self.lock:
            self.raw[i] += d
        head, buf = buf.split(b'\r\n\r\n', 1)
        lines = head.split(b'\r\n')
        fields = {}
        for l in lines[1:]:
          if b':' not in l or l[:1] in (b' ', b'\t'):
            self.bad.append(head); return
          n, v = l.split(b':', 1)
          fields.setdefault(n.strip().lower(), []).append(v.strip())
        if b'transfer-encoding' in fields:
          self.bad.append(head); return
        n = int(fields.get(b'content-length', [b'0'])[0])
        while len(buf) < n:
          d = c.recv(65536)
          if not d:
            return
          buf += d
          with self.lock:
            self.raw[i] += d
        body, buf = buf[:n], buf[n:]
        with self.lock:
          self.conns[i].append((head, body))
        path = lines[0].split(b' ')[1] if len(lines[0].split(b' ')) > 1 else b'/'
        if not self.answer(c, path, body, i):
          return
    except OSError:
      return
    finally:
      c.close()

  def answer(self, c, path, body, i):
    if path == b'/slow':
      time.sleep(3); return False
    if path == b'/die':
      return False
    if path == b'/half':
      c.sendall(b'HTTP/1.1 200 OK\r\nContent-Length: 100\r\n\r\nonly part'); return False
    if path == b'/hop':
      c.sendall(b'HTTP/1.1 200 OK\r\nConnection: X-Up\r\nX-Up: 1\r\nKeep-Alive: timeout=5\r\n'
        b'Upgrade: h9\r\nTrailer: X-T\r\nX-End: yes\r\nTransfer-Encoding: chunked\r\n\r\n'
        b'5\r\nhello\r\n6\r\n world\r\n0\r\n\r\n')
      return True
    msg = b'conn %d req %d body %d' % (i, len(self.conns[i]), len(body))
    c.sendall(b'HTTP/1.1 200 OK\r\nContent-Length: %d\r\n\r\n%s' % (len(msg), msg))
    return True

# A client
# ========

def talk(port, data, wait=1.0, chunks=None):
  s = socket.create_connection(('127.0.0.1', port))
  s.settimeout(wait)
  try:
    for part in (chunks or [data]):
      try:
        s.sendall(part)
      except OSError:
        break
      if chunks:
        time.sleep(0.01)
    out = b''
    t0 = time.time()
    while time.time() - t0 < wait + 3:
      try:
        d = s.recv(65536)
      except socket.timeout:
        break
      except OSError:
        break
      if not d:
        break
      out += d
    return out
  finally:
    s.close()

def statuses(out):
  return [int(m.group(1)) for m in re.finditer(rb'HTTP/1\.[01] (\d\d\d)', out)]

def fields_of(head):
  fs = []
  for l in head.split(b'\r\n')[1:]:
    n, _, v = l.partition(b':')
    fs.append((n.strip().lower(), v.strip()))
  return fs

def hop_in(head):
  fs = fields_of(head)
  named = set()
  for n, v in fs:
    if n == b'connection':
      named |= {x.strip().lower() for x in v.split(b',')}
  return [n for n, v in fs if n in HOP or n in named]

# The cases
# =========
# (name, bytes, at most this many requests upstream, what the client
# must see: a status list prefix or None)

def R(s):
  return s.replace('\n', '\r\n').encode()

SMUGGLE = [
  ('CL.TE', R('POST / HTTP/1.1\nHost: a\nContent-Length: 6\nTransfer-Encoding: chunked\n\n0\n\nG'), 1),
  ('TE.CL', R('POST / HTTP/1.1\nHost: a\nContent-Length: 3\nTransfer-Encoding: chunked\n\n8\nSMUGGLED\n0\n\n'), 1),
  ('TE.TE xchunked', R('POST / HTTP/1.1\nHost: a\nTransfer-Encoding: xchunked\nContent-Length: 4\n\n0\n\nGET /x HTTP/1.1\nHost: a\n\n'), 1),
  ('TE.TE space before colon', R('POST / HTTP/1.1\nHost: a\nTransfer-Encoding : chunked\nContent-Length: 4\n\n0\n\nGET /x HTTP/1.1\nHost: a\n\n'), 1),
  ('TE.TE doubled', R('POST / HTTP/1.1\nHost: a\nTransfer-Encoding: chunked\nTransfer-Encoding: x\n\n0\n\nGET /x HTTP/1.1\nHost: a\n\n'), 1),
  ('TE.TE list', R('POST / HTTP/1.1\nHost: a\nTransfer-Encoding: identity, chunked\n\n0\n\nGET /x HTTP/1.1\nHost: a\n\n'), 1),
  ('TE.TE tab', R('POST / HTTP/1.1\nHost: a\nTransfer-Encoding:\tchunked\n\n0\n\n'), 1),
  ('TE.TE case', R('POST / HTTP/1.1\nHost: a\nTransfer-Encoding: cHuNkEd\n\n0\n\n'), 1),
  ('TE.TE vertical tab', R('POST / HTTP/1.1\nHost: a\nTransfer-Encoding:\x0bchunked\n\n0\n\nGET /x HTTP/1.1\nHost: a\n\n'), 1),
  ('TE in HTTP/1.0', R('POST / HTTP/1.0\nHost: a\nTransfer-Encoding: chunked\n\n0\n\nGET /x HTTP/1.1\nHost: a\n\n'), 1),
  ('CL doubled', R('POST / HTTP/1.1\nHost: a\nContent-Length: 5\nContent-Length: 6\n\nabcdefGET /x HTTP/1.1\nHost: a\n\n'), 1),
  ('CL list', R('POST / HTTP/1.1\nHost: a\nContent-Length: 5, 6\n\nabcdefGET /x HTTP/1.1\nHost: a\n\n'), 1),
  ('CL signed', R('POST / HTTP/1.1\nHost: a\nContent-Length: +5\n\nabcdeGET /x HTTP/1.1\nHost: a\n\n'), 1),
  ('CL hex', R('POST / HTTP/1.1\nHost: a\nContent-Length: 0x5\n\nabcdeGET /x HTTP/1.1\nHost: a\n\n'), 1),
  ('obs-fold', R('GET / HTTP/1.1\nHost: a\nX-A: b\n Transfer-Encoding: chunked\n\n'), 1),
  ('obs-fold of CL', R('POST / HTTP/1.1\nHost: a\nContent-Length:\n 5\n\nabcde'), 1),
  ('bare LF', b'GET / HTTP/1.1\nHost: a\n\nGET /x HTTP/1.1\nHost: a\n\n', 1),
  ('bare CR', b'GET / HTTP/1.1\rHost: a\r\n\r\n', 1),
  ('NUL in value', R('GET / HTTP/1.1\nHost: a\nX: a\x00b\n\n'), 1),
  ('H2 preface', b'PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n', 0),
  ('H2 upgrade', R('GET / HTTP/1.1\nHost: a\nConnection: Upgrade, HTTP2-Settings\nUpgrade: h2c\nHTTP2-Settings: AAMAAABkAAQAAP__\n\n'), 1),
  ('two Hosts', R('GET / HTTP/1.1\nHost: a\nHost: b\n\n'), 1),
  ('no Host', R('GET / HTTP/1.1\n\n'), 1),
  ('request in a body', R('POST / HTTP/1.1\nHost: a\nContent-Length: 32\n\n') + R('GET /admin HTTP/1.1\nHost: a\n\n') + b'xx', 1),
  ('chunked with a request after', R('POST / HTTP/1.1\nHost: a\nTransfer-Encoding: chunked\n\n5\nhello\n0\n\nGET /x HTTP/1.1\nHost: a\n\n'), 2),
  ('chunk size overflow', R('POST / HTTP/1.1\nHost: a\nTransfer-Encoding: chunked\n\n10000000000000001\nA\n0\n\nGET /x HTTP/1.1\nHost: a\n\n'), 1),
  ('chunk extension with LF', R('POST / HTTP/1.1\nHost: a\nTransfer-Encoding: chunked\n\n5;a=\x0ab\nhello\n0\n\n'), 1),
  ('space in method line', R('GET  / HTTP/1.1\nHost: a\n\n'), 1),
  ('absolute-form', R('GET http://evil/ HTTP/1.1\nHost: a\n\n'), 1),
]

def main():
  proxyd = os.path.realpath(sys.argv[1]); P = int(sys.argv[2]); nginx = '--nginx' in sys.argv
  up = Upstream(P + 1)
  procs = []
  D = tempfile.mkdtemp(prefix='proxy_check_')
  def start(args, port):
    p = subprocess.Popen(args, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    procs.append(p)
    for _ in range(100):
      try:
        socket.create_connection(('127.0.0.1', port)).close(); return p
      except OSError:
        time.sleep(0.05)
    raise SystemExit('%s did not come up on %d' % (args[0], port))
  targets = [('bend-proxy', P)]
  try:
    start([proxyd, '--port', str(P), '--upstream', '127.0.0.1:%d' % (P + 1), '--upstream-ms', '1000',
      '--connect-ms', '500', '--idle-ms', '2000'], P)
    start([proxyd, '--port', str(P + 2), '--upstream', '127.0.0.1:%d' % (P + 4), '--connect-ms', '500'], P + 2)
    if nginx and shutil.which('nginx'):
      os.makedirs(D + '/tmp')
      conf = open(D + '/nginx.conf', 'w')
      conf.write('''worker_processes 1; daemon off; master_process off; error_log %(d)s/error.log crit;
pid %(d)s/nginx.pid; events { worker_connections 1024; }
http { access_log off; client_body_temp_path %(d)s/tmp; proxy_temp_path %(d)s/tmp;
  fastcgi_temp_path %(d)s/tmp; uwsgi_temp_path %(d)s/tmp; scgi_temp_path %(d)s/tmp;
  upstream up { server 127.0.0.1:%(u)d; keepalive 16; }
  server { listen 127.0.0.1:%(p)d; location / { proxy_pass http://up; proxy_http_version 1.1;
    proxy_set_header Connection ""; proxy_read_timeout 1s; proxy_connect_timeout 500ms; } } }
''' % {'d': D, 'u': P + 1, 'p': P + 3})
      conf.close()
      start(['nginx', '-c', D + '/nginx.conf', '-p', D], P + 3)
      targets.append(('nginx', P + 3))
    fail = 0
    table = []
    for name, data, most in SMUGGLE:
      row = [name]
      for who, port in targets:
        m = up.mark()
        out = talk(port, data, wait=0.6)
        time.sleep(0.1)
        reqs, _ = up.since(m)
        te = [h for h, b in reqs if hop_in(h)]
        st = statuses(out)
        ok = len(reqs) <= most and not te
        row.append('%s up=%d %s' % ('ok ' if ok else ('BAD' if who == 'bend-proxy' else 'lax'), len(reqs), st))
        if who == 'bend-proxy' and not ok:
          fail = 1
      table.append(row)
    # the same, a byte at a time: the framing never depends on the reads
    for name, data, most in SMUGGLE[:6]:
      m = up.mark()
      out = talk(P, data, wait=0.8, chunks=[data[i:i + 1] for i in range(len(data))])
      time.sleep(0.1)
      reqs, _ = up.since(m)
      ok = len(reqs) <= most and not [h for h, b in reqs if hop_in(h)]
      table.append([name + ' (bytewise)', '%s up=%d %s' % ('ok ' if ok else 'BAD', len(reqs), statuses(out))])
      fail |= not ok
    w = max(len(r[0]) for r in table)
    print('%-*s  %s' % (w, 'vector', '  |  '.join(t[0] for t in targets)))
    for r in table:
      print('%-*s  %s' % (w, r[0], '  |  '.join(r[1:])))

    def case(name, cond, detail=''):
      nonlocal fail
      print('%s %s%s' % ('PASS' if cond else 'FAIL', name, '' if cond else ': ' + detail))
      fail |= not cond

    # hop-by-hop fields dropped on the way up, the rest kept, ours added
    m = up.mark()
    out = talk(P, R('POST /x?q=1 HTTP/1.1\nHost: example.test\nConnection: X-Secret, keep-alive\nX-Secret: 1\n'
      'Keep-Alive: timeout=5\nTE: trailers\nProxy-Connection: keep-alive\nTrailer: X-T\nX-Keep: yes\n'
      'X-Forwarded-For: 10.0.0.1\nContent-Length: 5\n\nhello'))
    reqs, _ = up.since(m)
    h = reqs[0][0] if reqs else b''
    fs = dict(fields_of(h)) if h else {}
    case('request.hop_dropped', reqs and not hop_in(h) and b'x-secret' not in fs, repr(h))
    case('request.line', h.split(b'\r\n')[0] == b'POST /x?q=1 HTTP/1.1', repr(h[:60]))
    case('request.kept', fs.get(b'x-keep') == b'yes' and fs.get(b'host') == b'example.test', repr(fs))
    case('request.forwarded', fs.get(b'x-forwarded-for') == b'10.0.0.1, 127.0.0.1'
      and fs.get(b'x-forwarded-proto') == b'http' and fs.get(b'x-forwarded-host') == b'example.test'
      and fs.get(b'via') == b'1.1 bend-proxy', repr(fs))
    case('request.length', fs.get(b'content-length') == b'5' and reqs[0][1] == b'hello', repr(reqs[:1]))
    # a chunked request goes up with a length
    m = up.mark()
    out = talk(P, R('POST / HTTP/1.1\nHost: a\nTransfer-Encoding: chunked\n\n5\nhello\n6\n world\n0\nX-T: 1\n\n'))
    reqs, _ = up.since(m)
    case('request.dechunked', len(reqs) == 1 and reqs[0][1] == b'hello world'
      and dict(fields_of(reqs[0][0])).get(b'content-length') == b'11', repr(reqs))
    # the response's hop fields dropped, the chunked body sent with a length
    out = talk(P, R('GET /hop HTTP/1.1\nHost: a\n\n'))
    head, _, body = out.partition(b'\r\n\r\n')
    rf = dict(fields_of(head))
    case('response.hop_dropped', not hop_in(head) and b'x-up' not in rf and rf.get(b'x-end') == b'yes', repr(head))
    case('response.reframed', rf.get(b'content-length') == b'11' and body == b'hello world'
      and rf.get(b'via') == b'1.1 bend-proxy', repr(out))
    # HEAD: the length said, no body
    out = talk(P, R('HEAD / HTTP/1.1\nHost: a\n\n'))
    case('response.head', statuses(out) == [200] and out.endswith(b'\r\n\r\n'), repr(out))
    # pipelined requests, answered in order, one upstream request each
    m = up.mark()
    out = talk(P, R('GET /1 HTTP/1.1\nHost: a\n\nGET /2 HTTP/1.1\nHost: a\n\nGET /3 HTTP/1.1\nHost: a\n\n'))
    reqs, _ = up.since(m)
    case('pipelined', statuses(out) == [200, 200, 200] and [r[0].split(b' ')[1] for r in reqs] == [b'/1', b'/2', b'/3'],
      repr(out))
    # pooling: many client connections, one upstream connection
    m = up.mark()
    for i in range(20):
      talk(P, R('GET / HTTP/1.1\nHost: a\nConnection: close\n\n'), wait=0.3)
    reqs, fresh = up.since(m)
    case('pool.reused', len(reqs) == 20 and fresh <= 1, 'requests %d, new upstream connections %d' % (len(reqs), fresh))
    # 100-continue: the proxy says continue, the upstream never sees Expect
    s = socket.create_connection(('127.0.0.1', P)); s.settimeout(2)
    s.sendall(R('POST / HTTP/1.1\nHost: a\nExpect: 100-continue\nContent-Length: 3\n\n'))
    first = s.recv(4096)
    m = up.mark()
    s.sendall(b'abc'); time.sleep(0.2)
    rest = s.recv(4096); s.close()
    reqs, _ = up.since(m)
    case('expect.continue', first.startswith(b'HTTP/1.1 100') and statuses(rest)[:1] == [200]
      and reqs and b'expect' not in dict(fields_of(reqs[0][0])), repr((first, rest)))
    # the error paths: no partial response leaks
    out = talk(P, R('GET /slow HTTP/1.1\nHost: a\n\n'), wait=2.5)
    case('upstream.timeout.504', statuses(out) == [504], repr(out))
    out = talk(P, R('GET /die HTTP/1.1\nHost: a\n\n'), wait=1.5)
    case('upstream.closed.502', statuses(out) == [502], repr(out))
    out = talk(P, R('GET /half HTTP/1.1\nHost: a\n\n'), wait=1.5)
    case('upstream.short.502', statuses(out) == [502] and b'only part' not in out, repr(out))
    out = talk(P + 2, R('GET / HTTP/1.1\nHost: a\n\n'), wait=1.5)
    case('upstream.down.502', statuses(out) == [502], repr(out))
    # an idempotent request retried once on a pooled connection the upstream closed
    talk(P, R('GET / HTTP/1.1\nHost: a\n\n'), wait=0.3)
    with up.lock:
      pass
    out = talk(P, R('GET /die HTTP/1.1\nHost: a\n\n'), wait=1.5)
    out = talk(P, R('GET / HTTP/1.1\nHost: a\n\n'), wait=0.5)
    case('pool.stale_retry', statuses(out) == [200], repr(out))
    case('upstream.strict', not up.bad, repr(up.bad[:2]))
    print('FAIL' if fail else 'PASS', 'proxy check')
    sys.exit(1 if fail else 0)
  finally:
    for p in procs:
      p.kill()
    shutil.rmtree(D, ignore_errors=True)

main()
