#!/bin/bash
# Where the server's time goes, by stack sampling: gdb attaches N times
# while a client that never sleeps drives it, and the samples are folded
# into a count per innermost frame and per frame seen anywhere.
#
# It is here because guessing was wrong twice. Narrowing the parser's
# hot node and removing two of its states each recovered nothing; forty
# samples then showed the time was in syscalls and none of it in the
# parser, which is what sent the work to the poller instead.
#
#   ./prof.sh ./httpd 40
#
# Needs gdb, and load built from load.c beside it.
set -u
H=${1:-./httpd}
N=${2:-40}
DIR=$(cd "$(dirname "$0")" && pwd)
LOAD=${LOAD:-$DIR/load}
PORT=${PORT:-8080}
PIPE=${PIPE:-1}
CONNS=${CONNS:-32}
RAW=$(mktemp)

up() {
  for _ in $(seq 1 50); do
    (exec 3<>/dev/tcp/127.0.0.1/$PORT) 2>/dev/null && return 0
    sleep 0.1
  done
  echo "the server never listened on $PORT" >&2
  return 1
}

"$H" --threads 1 >/dev/null 2>&1 &
up || exit 1
pid=$(pgrep -x "$(basename "$H")" | head -1)

LOAD_SPIN=1 "$LOAD" $PORT $CONNS 25 $PIPE /health >/dev/null 2>&1 &
load=$!
sleep 1
for _ in $(seq 1 "$N"); do
  gdb -p "$pid" -batch -ex 'bt 12' 2>/dev/null | grep -E '^#' >> "$RAW"
  echo "--" >> "$RAW"
done
wait $load
pkill -x "$(basename "$H")"

echo "innermost frame, $N samples:"
grep '^#0 ' "$RAW" | sed 's/^#0 *//; s/ (.*//; s/^0x[0-9a-f]* in //' \
  | sort | uniq -c | sort -rn | head -14
echo
echo "every frame, by how many samples contain it:"
awk '/^--/ { for (f in seen) count[f]++; delete seen; next }
     { gsub(/^#[0-9]+ +/, ""); sub(/ \(.*/, ""); sub(/^0x[0-9a-f]+ in /, ""); seen[$0] = 1 }
     END { for (f in count) printf "%6d %s\n", count[f], f }' "$RAW" \
  | sort -rn | head -20
rm -f "$RAW"
