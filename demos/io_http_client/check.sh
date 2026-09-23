#!/usr/bin/env bash
# The client against real servers: the HTTP engine, plain and over TLS,
# and nginx when it is installed (apt-get install nginx-light). Each case
# runs the client and matches its line; a TLS case the client must refuse
# (a certificate not trusted, a name not on it) must end it with EACCES.
#
#   check.sh ./hc ./httpd 19840        (uses ports 19840 to 19843)
set -u
HC=$(realpath "$1"); HTTPD=$(realpath "$2"); P=$3
D=$(mktemp -d); fail=0; pids=()
trap 'kill "${pids[@]}" 2>/dev/null; [ -f "$D/ngx/nginx.pid" ] && kill "$(cat "$D/ngx/nginx.pid")"; rm -rf "$D"' EXIT
up() { for _ in $(seq 1 60); do (exec 3<>/dev/tcp/127.0.0.1/"$1") 2>/dev/null && return 0; sleep 0.1; done; return 1; }
expect() {
  local name=$1 want=$2; shift 2
  local out; out=$("$HC" "$@" 2>&1)
  if printf '%s\n' "$out" | grep -Eq -- "$want"; then echo "PASS $name"
  else echo "FAIL $name: $(printf '%s' "$out" | tr '\n' '|')"; fail=1; fi
}

mkdir -p "$D/www"; echo "hello from the engine" > "$D/www/index.html"
python3 -c "open('$D/www/big.bin','wb').write(bytes(i % 251 for i in range(300000)))"
openssl req -x509 -newkey rsa:2048 -keyout "$D/key.pem" -out "$D/cert.pem" -days 2 -nodes \
  -subj /CN=localhost -addext subjectAltName=DNS:localhost 2>/dev/null

"$HTTPD" --port "$P" --root "$D/www" >/dev/null 2>&1 & pids+=($!); up "$P"
"$HTTPD" --port $((P + 1)) --root "$D/www" --tls-cert "$D/cert.pem" --tls-key "$D/key.pem" \
  >/dev/null 2>&1 & pids+=($!); up $((P + 1))
E=http://127.0.0.1:$P; T=https://localhost:$((P + 1))
expect engine.health '^status 200, body 11 bytes, interim \[ \], reusable$' "$E/health"
expect engine.file 'status 200, body 22 bytes' "$E/index.html"
expect engine.twice 'again, on the same connection:' "$E/" --twice
expect engine.big '^status 200, body 300000 bytes' "$E/big.bin"
expect engine.head '^status 200, body 0 bytes' "$E/big.bin" --head
expect engine.missing '^status 404' "$E/nope"
expect engine.name '^status 200' "http://localhost:$P/health"
expect engine.tls.pinned '^status 200, body 22 bytes' "$T/" --ca "$D/cert.pem"
expect engine.tls.twice 'again, on the same connection:' "$T/" --ca "$D/cert.pem" --twice
expect engine.tls.untrusted 'TLS: .*\(13\)' "$T/"
expect engine.tls.misnamed 'TLS: .*\(13\)' "https://127.0.0.1:$((P + 1))/" --ca "$D/cert.pem"
expect engine.refused 'Connection refused' "http://127.0.0.1:$((P + 3))/"

NGINX=$(command -v nginx || ls /usr/sbin/nginx 2>/dev/null)
if [ -n "$NGINX" ]; then
  mkdir -p "$D/ngx/logs" "$D/ngx/www/close" "$D/ngx/www/ssi"; echo "nginx says hi" > "$D/ngx/www/index.html"
  printf 'one <!--# echo var="ssi_x" default="two" --> three\n' > "$D/ngx/www/ssi/index.html"
  cp "$D/ngx/www/index.html" "$D/ngx/www/close/"; cp "$D/www/big.bin" "$D/ngx/www/"
  cat > "$D/ngx/nginx.conf" <<EOF
worker_processes 1;
pid $D/ngx/nginx.pid;
error_log $D/ngx/logs/error.log;
events { worker_connections 64; }
http {
  access_log off;
  client_body_temp_path $D/ngx/t1; proxy_temp_path $D/ngx/t2; fastcgi_temp_path $D/ngx/t3;
  uwsgi_temp_path $D/ngx/t4; scgi_temp_path $D/ngx/t5;
  server {
    listen 127.0.0.1:$((P + 2)); listen 127.0.0.1:$((P + 3)) ssl;
    ssl_certificate $D/cert.pem; ssl_certificate_key $D/key.pem;
    root $D/ngx/www;
    location /ssi/ { ssi on; }
    location /close/ { keepalive_timeout 0; }
  }
}
EOF
  chmod -R a+rX "$D"; "$NGINX" -p "$D/ngx" -c "$D/ngx/nginx.conf" 2>/dev/null; up $((P + 2))
  N=http://127.0.0.1:$((P + 2)); S=https://localhost:$((P + 3))
  expect nginx.file '^status 200, body 14 bytes, interim \[ \], reusable$' "$N/"
  expect nginx.twice 'again, on the same connection:' "$N/" --twice
  expect nginx.big '^status 200, body 300000 bytes' "$N/big.bin"
  expect nginx.head '^status 200, body 0 bytes, interim \[ \], reusable$' "$N/big.bin" --head
  expect nginx.missing '^status 404' "$N/nope"
  # SSI takes the length away, so nginx sends the page chunked
  if curl -si "$N/ssi/" | grep -qi '^transfer-encoding: chunked'; then
    expect nginx.chunked '^status 200, body 14 bytes, interim \[ \], reusable$' "$N/ssi/" --twice
  else
    echo "FAIL nginx.chunked: nginx did not send the SSI page chunked"; fail=1
  fi
  expect nginx.close 'not reusable$' "$N/close/index.html" --twice
  expect nginx.tls '^status 200, body 14 bytes' "$S/" --ca "$D/cert.pem" --twice
else
  echo "SKIP nginx: not installed"
fi
exit $fail
