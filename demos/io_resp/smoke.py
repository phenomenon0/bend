# The RESP server against a client: PING, SET, GET, ECHO, a pipelined
# read with a command cut across two sends, a refused stream answered
# with the error and closed, and SIGTERM.
#
#   bend demos/io_resp/main.bend -o respd
#   python3 demos/io_resp/smoke.py ./respd 6380
import socket, subprocess, sys, time
BIN, PORT = sys.argv[1], int(sys.argv[2])
p = subprocess.Popen([BIN, str(PORT)], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
for _ in range(100):
    try:
        s = socket.create_connection(('127.0.0.1', PORT)); break
    except OSError:
        time.sleep(0.05)
def cmd(*args):
    return b''.join([b'*%d\r\n' % len(args)] + [b'$%d\r\n%s\r\n' % (len(a), a) for a in args])
def ask(req, want):
    s.sendall(req)
    got = b''
    s.settimeout(3)
    while len(got) < len(want):
        chunk = s.recv(4096)
        if not chunk: break
        got += chunk
    ok = got == want
    print('%s %r -> %r' % ('PASS' if ok else 'FAIL', req, got))
    return ok
ok = True
ok &= ask(cmd(b'PING'), b'+PONG\r\n')
ok &= ask(cmd(b'SET', b'k', b'hello'), b'+OK\r\n')
ok &= ask(cmd(b'GET', b'k'), b'$5\r\nhello\r\n')
ok &= ask(cmd(b'GET', b'nope'), b'$-1\r\n')
ok &= ask(cmd(b'ECHO', b'hey'), b'$3\r\nhey\r\n')
# pipelined, and a command cut across two sends
s.sendall(cmd(b'PING') + cmd(b'SET', b'a', b'1')[:7])
time.sleep(0.1)
ok &= ask(cmd(b'SET', b'a', b'1')[7:] + cmd(b'GET', b'a'), b'+PONG\r\n+OK\r\n$1\r\n1\r\n')
ok &= ask(b'?bad\r\n', b'-ERR protocol error\r\n')
s.settimeout(3)
ok &= s.recv(10) == b''
print('closed after the refusal')
s.close()
p.send_signal(15)
try:
    p.wait(5)
except subprocess.TimeoutExpired:
    p.kill(); ok = False
print(p.stderr.read().decode().strip())
print('resp smoke:', 'PASS' if ok else 'FAIL')
sys.exit(0 if ok else 1)
