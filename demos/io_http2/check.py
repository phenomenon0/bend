#!/usr/bin/env python3
# The HTTP/2 server's checks, as a client sees it, with the `h2` package
# (pip install h2) framing and the checks reading every frame that comes
# back: requests and their answers, many streams at once, bodies larger
# than every window both ways, and each budget the server keeps against
# a flood, met.
#
#   python3 demos/io_http2/check.py PORT
import socket, sys, time
import h2.config, h2.connection, h2.events, h2.errors, h2.settings
import hpack

PORT = int(sys.argv[1])
FAILS = []

def ok(cond, what):
  print(('ok   ' if cond else 'FAIL ') + what)
  if not cond:
    FAILS.append(what)

class Client:
  def __init__(self, window=None, maxframe=None):
    self.s = socket.create_connection(('127.0.0.1', PORT))
    self.s.settimeout(5)
    self.c = h2.connection.H2Connection(h2.config.H2Configuration(client_side=True,
      header_encoding='utf-8', validate_inbound_headers=False))
    self.c.initiate_connection()
    ups = {}
    if window is not None:
      ups[h2.settings.SettingCodes.INITIAL_WINDOW_SIZE] = window
    if maxframe is not None:
      ups[h2.settings.SettingCodes.MAX_FRAME_SIZE] = maxframe
    if ups:
      self.c.update_settings(ups)
    self.flush()
    self.events = []
    self.closed = False

  def flush(self):
    data = self.c.data_to_send()
    if data:
      self.s.sendall(data)

  def raw(self, b):
    self.s.sendall(b)

  def pump(self, until, limit=10.0):
    end = time.time() + limit
    while not until() and time.time() < end and not self.closed:
      try:
        d = self.s.recv(65536)
      except socket.timeout:
        break
      except ConnectionResetError:
        self.closed = True
        break
      if not d:
        self.closed = True
        break
      for ev in self.c.receive_data(d):
        self.events.append(ev)
        if isinstance(ev, h2.events.DataReceived):
          self.c.acknowledge_received_data(ev.flow_controlled_length, ev.stream_id)
      self.flush()

  def request(self, method, path, body=b'', extra=()):
    sid = self.c.get_next_available_stream_id()
    hs = [(':method', method), (':scheme', 'http'), (':path', path), (':authority', 'localhost')]
    hs += list(extra)
    if body:
      hs.append(('content-length', str(len(body))))
    self.c.send_headers(sid, hs, end_stream=not body)
    self.flush()
    if body:
      self.send_body(sid, body)
    return sid

  def send_body(self, sid, body):
    off = 0
    while off < len(body):
      room = min(self.c.local_flow_control_window(sid), self.c.max_outbound_frame_size, len(body) - off)
      if room <= 0:
        self.pump(lambda: self.c.local_flow_control_window(sid) > 0, 5)
        if self.c.local_flow_control_window(sid) <= 0:
          raise RuntimeError('the window never opened')
        continue
      self.c.send_data(sid, body[off:off + room], end_stream=off + room == len(body))
      off += room
      self.flush()

  def response(self, sid):
    def done():
      return any(isinstance(e, (h2.events.StreamEnded, h2.events.StreamReset)) and e.stream_id == sid
        for e in self.events)
    self.pump(done)
    hs, body, reset = None, b'', None
    for e in self.events:
      if getattr(e, 'stream_id', None) != sid:
        continue
      if isinstance(e, h2.events.ResponseReceived):
        hs = dict(e.headers)
      elif isinstance(e, h2.events.DataReceived):
        body += e.data
      elif isinstance(e, h2.events.StreamReset):
        reset = e.error_code
    return hs, body, reset

  def goaway(self):
    for e in self.events:
      if isinstance(e, h2.events.ConnectionTerminated):
        return e.error_code
    return None

  def close(self):
    self.s.close()

def frame(ty, fl, sid, pay):
  return len(pay).to_bytes(3, 'big') + bytes([ty, fl]) + sid.to_bytes(4, 'big') + pay

def goaway_of(data):
  # the error code of the first GOAWAY in a byte stream, if any
  i = 0
  while i + 9 <= len(data):
    n = int.from_bytes(data[i:i + 3], 'big')
    if data[i + 3] == 7 and i + 9 + 8 <= len(data):
      return int.from_bytes(data[i + 13:i + 17], 'big')
    i += 9 + n
  return None

def raw_session(frames):
  s = socket.create_connection(('127.0.0.1', PORT))
  s.settimeout(3)
  s.sendall(b'PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n' + frame(4, 0, 0, b''))
  try:
    for f in frames:
      s.sendall(f)
  except (BrokenPipeError, ConnectionResetError):
    pass
  data = b''
  end = time.time() + 3
  while time.time() < end:
    try:
      d = s.recv(65536)
    except (socket.timeout, ConnectionResetError):
      break
    if not d:
      break
    data += d
  s.close()
  return data

def req_block(path='/health', extra=()):
  e = hpack.Encoder()
  return e.encode([(':method', 'GET'), (':scheme', 'http'), (':path', path), (':authority', 'x')] + list(extra))

# Requests
# ========

c = Client()
sid = c.request('GET', '/health')
hs, body, _ = c.response(sid)
ok(hs and hs.get(':status') == '200' and body == b'{"ok":true}', 'GET /health')
sid = c.request('HEAD', '/health')
hs, body, _ = c.response(sid)
ok(hs and hs.get(':status') == '200' and hs.get('content-length') == '11' and body == b'', 'HEAD /health')
sid = c.request('POST', '/echo', b'hello, h2')
hs, body, _ = c.response(sid)
ok(hs and hs.get(':status') == '200' and body == b'hello, h2', 'POST /echo')
sid = c.request('GET', '/nope')
hs, body, _ = c.response(sid)
ok(hs and hs.get(':status') == '404', 'GET /nope is 404')
sid = c.request('DELETE', '/health')
hs, body, _ = c.response(sid)
ok(hs and hs.get(':status') == '405', 'DELETE is 405')
sid = c.request('GET', '/' + 'a' * 9000)
hs, body, _ = c.response(sid)
ok(hs and hs.get(':status') == '414', 'a long target is 414')

# many streams at once: fifty requests before any answer is read
sids = []
for i in range(50):
  if i % 2:
    sids.append((c.request('POST', '/echo', ('body %d' % i).encode()), ('body %d' % i).encode()))
  else:
    sids.append((c.request('GET', '/health'), b'{"ok":true}'))
good = 0
for sid, want in sids:
  hs, body, _ = c.response(sid)
  good += hs is not None and body == want
ok(good == 50, 'fifty concurrent streams, each answered (%d)' % good)
c.close()

# Flow control
# ============

# a body past every window each way: the client's upload waits on the
# server's WINDOW_UPDATEs, the echo on the client's
c = Client()
big = bytes(i % 251 for i in range(1000000))
sid = c.request('POST', '/echo', big)
hs, body, _ = c.response(sid)
ok(hs and hs.get(':status') == '200' and body == big, 'a 1 MB echo through 64 KiB windows')
c.close()

# a client window of 1 byte: DATA frames of one byte, each waiting on a
# WINDOW_UPDATE
c = Client(window=1)
c.pump(lambda: any(isinstance(e, h2.events.SettingsAcknowledged) for e in c.events), 2)
sid = c.request('GET', '/health')
hs, body, _ = c.response(sid)
sizes = [len(e.data) for e in c.events if isinstance(e, h2.events.DataReceived)]
ok(body == b'{"ok":true}' and max(sizes) == 1, 'a window of 1: every DATA frame one byte (%s)' % sizes[:3])
c.close()

# a body past the cap (1 MiB) is refused with ENHANCE_YOUR_CALM
c = Client()
sid = c.request('POST', '/echo', bytes(1048577))
hs, body, reset = c.response(sid)
ok(reset == 11, 'a body past 1 MiB is reset with ENHANCE_YOUR_CALM (%s)' % reset)
c.close()

# Streams
# =======

# a hundred streams open at once are taken; the hundred-and-first is
# refused
c = Client()
opened = []
for i in range(101):
  sid = c.c.get_next_available_stream_id()
  c.c.send_headers(sid, [(':method', 'POST'), (':scheme', 'http'), (':path', '/echo'), (':authority', 'x')])
  opened.append(sid)
c.flush()
c.pump(lambda: any(isinstance(e, h2.events.StreamReset) for e in c.events), 3)
resets = [(e.stream_id, e.error_code) for e in c.events if isinstance(e, h2.events.StreamReset)]
ok(resets == [(opened[-1], 7)], 'the 101st stream at once is REFUSED_STREAM (%s)' % resets[:3])
c.close()

# an even stream id is a PROTOCOL_ERROR
data = raw_session([frame(1, 5, 2, req_block())])
ok(goaway_of(data) == 1, 'an even stream id: GOAWAY PROTOCOL_ERROR')

# a stream id below one already used is a PROTOCOL_ERROR (closed)
data = raw_session([frame(1, 5, 5, req_block()), frame(1, 5, 3, req_block())])
ok(goaway_of(data) in (1, 5), 'a lower stream id after a higher: GOAWAY (%s)' % goaway_of(data))

# The budgets (RFC 9113 10.5)
# ===========================

# a rapid reset (CVE-2023-44487): streams opened and reset at once
fs = []
for i in range(200):
  sid = 1 + 2 * i
  fs.append(frame(1, 4, sid, req_block()) + frame(3, 0, sid, (8).to_bytes(4, 'big')))
data = raw_session([b''.join(fs)])
ok(goaway_of(data) == 11, 'a rapid reset of 200 streams: GOAWAY ENHANCE_YOUR_CALM')

# a PING flood
data = raw_session([b''.join(frame(6, 0, 0, b'12345678') for _ in range(200))])
ok(goaway_of(data) == 11, 'a flood of 200 PINGs: GOAWAY ENHANCE_YOUR_CALM')

# a SETTINGS flood
data = raw_session([b''.join(frame(4, 0, 0, b'') for _ in range(200))])
ok(goaway_of(data) == 11, 'a flood of 200 SETTINGS: GOAWAY ENHANCE_YOUR_CALM')

# a CONTINUATION flood (CVE-2024-27316): a header block that never ends
blk = req_block()
fs = [frame(1, 0, 1, blk)] + [frame(9, 0, 1, b'x-a: ' + b'b' * 1000) for _ in range(100)]
data = raw_session([b''.join(fs)])
ok(goaway_of(data) in (9, 11), 'a CONTINUATION flood past 64 KiB: GOAWAY (%s)' % goaway_of(data))

# an HPACK bomb: one 4 KB entry put in the table, then named a hundred
# times in one block (400 KB decoded from a 100-byte block)
def hint(n, prefix, flags):
  top = (1 << prefix) - 1
  if n < top:
    return bytes([flags | n])
  out, n = [flags | top], n - top
  while n >= 128:
    out.append(128 | (n % 128)); n //= 128
  return bytes(out + [n])

def hstr(b):
  return hint(len(b), 7, 0) + b

first = bytes([0x82, 0x86, 0x84]) + bytes([0x40]) + hstr(b'x-bomb') + hstr(b'z' * 4000)
bomb = bytes([0x82, 0x86, 0x84]) + bytes([0x80 | 62]) * 100
data = raw_session([frame(1, 5, 1, first), frame(1, 5, 3, bomb)])
ok(goaway_of(data) == 9, 'an HPACK bomb past the 64 KiB list: GOAWAY COMPRESSION_ERROR (%s)' % goaway_of(data))

# an ordinary client meets no budget: 300 PINGs, each after a response
c = Client()
for i in range(300):
  c.c.ping(b'%08d' % i)
  sid = c.request('GET', '/health')
  c.response(sid)
ok(c.goaway() is None and not c.closed, 'three hundred PINGs among as many requests: no GOAWAY')
c.close()

print('%d failed' % len(FAILS))
sys.exit(1 if FAILS else 0)
