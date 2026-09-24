#!/usr/bin/env bash
# `demos/mesh/mesh.sh`: bend-mesh against the single-process answers.
#
# Four workers on this machine, one thread each (four "machines"); the
# coordinator splits two jobs into chunks over them:
#
#   lost 8    all C(32,16) = 601,080,390 schedules of lostupdate.bend
#   exact 7   2^26 of kulisch.bend's draws (the kulisch_big run)
#
# Three runs each: clean; one worker a straggler (--slow 4000 on every
# leaf); one worker killed (SIGKILL) two seconds in. Every run must print
# the answer the oracles pinned: lostupdate_gen.py's DP histogram and
# kulisch_big's bits (Fraction-checked at 2^20 by the monoids lane).
set -uo pipefail
cd "$(dirname "$0")/../.."
export BEND_NO_TELEMETRY=1
work=$(mktemp -d /tmp/bend-mesh.XXXXXX)
pids=()
trap 'kill "${pids[@]}" 2>/dev/null; rm -rf -- "$work"' EXIT

bun bend2/main.ts demos/mesh/worker.bend -o "$work/worker" > /dev/null 2>&1 || exit 1
bun bend2/main.ts demos/mesh/mesh.bend -o "$work/mesh" > /dev/null 2>&1 || exit 1

LOST="n=8 schedules=601080390 min=2 x8 correct=12870 | 2:8 3:448 4:11440 5:171968 6:1666808 7:10828672 8:53282976 9:124712320 10:168850776 11:141162176 12:73144304 13:22822080 14:4047464 15:366080 16:12870"
EXACT="exact 0xbe9ac177"
[ "$(python3 demos/monoids/lostupdate_gen.py > /dev/null; python3 -c '
import sys; sys.path.insert(0, "demos/monoids"); import lostupdate_gen as g
print(g.line(8).rsplit(" |", 1)[0])')" = "$LOST" ] || { echo "the DP oracle disagrees with the pinned line"; exit 1; }

up() { # up PORT [ARGS]: a worker on PORT, one thread
  "$work/worker" --port "$1" --threads 1 "${@:2}" > /dev/null 2>&1 &
  pids+=($!)
}
urls="http://127.0.0.1:9101 http://127.0.0.1:9102 http://127.0.0.1:9103 http://127.0.0.1:9104"
fail=0

run() { # run NAME WANT ARGS...: time the coordinator, compare its answer
  local name=$1 want=$2
  shift 2
  local s=$(date +%s%N)
  local got
  got=$("$work/mesh" "$@" $urls 2> "$work/err")
  local ms=$((($(date +%s%N) - s) / 1000000))
  if [ "$got" = "$want" ]; then printf 'ok   %-28s %6d ms  %s\n' "$name" "$ms" "$(cat "$work/err")"
  else printf 'FAIL %-28s %6d ms  %s\n     got: %s\n' "$name" "$ms" "$(cat "$work/err")" "$got"; fail=1; fi
}

restart() { # restart [SLOW]: four fresh workers, the first one slow if asked
  kill "${pids[@]}" 2>/dev/null; wait "${pids[@]}" 2>/dev/null; pids=()
  up 9101 ${1:+--slow $1}; up 9102; up 9103; up 9104
  sleep 1
}

for job in "lost 8 0 64 4:$LOST" "exact 7 67108864 64 6:$EXACT"; do
  args=${job%%:*}; want=${job#*:}
  name=${args%% *}

  # the reference: the whole job in one process, one thread
  s=$(date +%s%N)
  ref=$("$work/mesh" ${args% * *} 0 8 --threads 1)
  ms=$((($(date +%s%N) - s) / 1000000))
  [ "$ref" = "$want" ] && printf 'ok   %-28s %6d ms\n' "$name: one process, 1 thread" "$ms" \
    || { printf 'FAIL %s reference: %s\n' "$name" "$ref"; fail=1; }

  restart;      run "$name: 4 workers" "$want" $args
  restart 4000; run "$name: w0 straggles 4 s/leaf" "$want" $args
  restart
  ( sleep 2; kill -9 "${pids[1]}" ) &
  run "$name: w1 killed at 2 s" "$want" $args
done
exit $fail
