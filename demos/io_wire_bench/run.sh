#!/bin/sh
# Builds buf.bend and list.bend and drives each with the engine's load.c:
# one server thread on one core, the client on another, 32 keep-alive
# connections, pipeline 1 and 8, LOAD_SPIN=1 (see the engine's README).
#   sh demos/io_wire_bench/run.sh [secs] [server-core] [client-core]
set -e
here=$(cd "$(dirname "$0")" && pwd)
bend2="$here/../../bend2"
out=${OUT:-/tmp/io_wire_bench}
secs=${1:-5}
sc=${2:-2}
cc_=${3:-3}
mkdir -p "$out"
cc -std=c11 -O3 "$here/../io_http_engine/load.c" -o "$out/load"
for v in buf list; do
  bun "$bend2/main.ts" "$here/$v.bend" -o "$out/w$v"
done
for v in buf list; do
  port=18710
  [ "$v" = list ] && port=18711
  taskset -c "$sc" "$out/w$v" --threads 1 &
  pid=$!
  sleep 0.5
  curl -s "http://127.0.0.1:$port/health"; echo
  for p in 1 8; do
    printf '%s p%s: ' "$v" "$p"
    LOAD_SPIN=1 taskset -c "$cc_" "$out/load" "$port" 32 "$secs" "$p" /health
  done
  printf '%s rss: ' "$v"; grep VmHWM "/proc/$pid/status"
  kill "$pid"
  wait "$pid" 2>/dev/null || true
done
