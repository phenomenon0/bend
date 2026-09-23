#!/usr/bin/env bash
# The sink against curl: bodies by length and chunked, a pipelined pair,
# a body framed two ways refused, and a 100 MB upload each way, whose
# count must come back whole while the server's peak RSS (VmHWM) stays
# under 16 MB: the body is streamed, never held.
#
#   check.sh ./sink 19850
set -u
SINK=$(realpath "$1"); P=$2
D=$(mktemp -d); fail=0
"$SINK" "$P" > /dev/null 2>&1 & pid=$!
trap 'kill $pid 2>/dev/null; rm -rf "$D"' EXIT
for _ in $(seq 1 50); do (exec 3<>/dev/tcp/127.0.0.1/"$P") 2>/dev/null && break; sleep 0.1; done
U=http://127.0.0.1:$P/sink
is() { if [ "$2" = "$3" ]; then echo "PASS $1"; else echo "FAIL $1: got '$2', want '$3'"; fail=1; fi; }
is small "$(curl -s --data-binary hello "$U")" 5
is chunked "$(curl -s -H 'Transfer-Encoding: chunked' --data-binary 'hello world' "$U")" 11
is missing "$(curl -s --data-binary x "http://127.0.0.1:$P/other")" "no route"
is pipelined "$(python3 - "$P" <<'EOF'
import socket, sys
s = socket.create_connection(('127.0.0.1', int(sys.argv[1])))
s.sendall(b'POST /sink HTTP/1.1\r\nContent-Length: 5\r\n\r\nhello'
  b'POST /sink HTTP/1.1\r\nTransfer-Encoding: chunked\r\n\r\n3\r\nabc\r\n0\r\n\r\n')
s.settimeout(2); b = b''
while b.count(b'200 OK') < 2:
  d = s.recv(4096)
  if not d: break
  b += d
print(' '.join(l.decode() for l in b.split(b'\r\n\r\n')[1:] if l).replace('\n', ' ').split('HTTP')[0].strip(),
  b.count(b'200 OK'))
EOF
)" "5 2"
is two.ways "$(printf 'POST /sink HTTP/1.1\r\nContent-Length: 1\r\nTransfer-Encoding: chunked\r\n\r\nx' |
  timeout 2 python3 -c "import socket,sys; s=socket.create_connection(('127.0.0.1',$P)); s.sendall(sys.stdin.buffer.read()); print(s.recv(100).split(b'\r\n')[0].decode())")" "HTTP/1.1 400 Bad Request"
head -c 104857600 /dev/zero > "$D/big.bin"
is upload.length "$(curl -s -T "$D/big.bin" "$U")" 104857600
is upload.chunked "$(curl -s -H 'Transfer-Encoding: chunked' -T "$D/big.bin" "$U")" 104857600
hwm=$(awk '/VmHWM/ {print $2}' /proc/$pid/status)
if [ "$hwm" -lt 16384 ]; then echo "PASS rss: VmHWM ${hwm} kB after 200 MB uploaded"
else echo "FAIL rss: VmHWM ${hwm} kB after 200 MB uploaded"; fail=1; fi
exit $fail
