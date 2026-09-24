#!/usr/bin/env bash
# `demos/mesh/spot.sh [PATHS]`: the option job on a fleet that keeps getting
# preempted, against the C twin's bits.
#
# The reference is option_twin.c (same operations, -ffp-contract=off), four
# threads. Then bend-mesh runs the same paths:
#
#   local      one process, all cores
#   2 x 50     two workers, 50 chunks
#   4 x 200    four workers, 200 chunks
#   spot       four workers, 200 chunks, and a chaos loop that SIGKILLs a random
#              worker every 1-3 s and brings it back 1-4 s later (a spot
#              reclaim and a replacement). The coordinator re-admits workers
#              that come back: a failed post costs a strike, not the worker.
#
# Every run must print the twin's accumulator bits; the price is then within a
# few standard errors of Black-Scholes (option_ref.py --bs), and spot.sh says
# how many.
set -uo pipefail
cd "$(dirname "$0")/../.."
export BEND_NO_TELEMETRY=1
N=${1:-20000000}
work=$(mktemp -d /tmp/bend-spot.XXXXXX)
pids=()
chaos=
trap 'kill ${pids[@]+"${pids[@]}"} $chaos 2>/dev/null; rm -rf -- "$work"' EXIT

cc -O2 -ffp-contract=off -o "$work/twin" demos/mesh/option_twin.c -lm -lpthread || exit 1
bun bend2/main.ts demos/mesh/worker.bend -o "$work/worker" > /dev/null 2>&1 || exit 1
bun bend2/main.ts demos/mesh/mesh.bend -o "$work/mesh" > /dev/null 2>&1 || exit 1

twin=$("$work/twin" twin "$N" 4 2> "$work/err")
want=${twin#*acc=}; want=${want%% price=*}
bs=$(python3 demos/mesh/option_ref.py --bs)
printf 'twin %s  (%s)\n' "$twin" "$(cat "$work/err")"
printf 'Black-Scholes %s\n' "$bs"

up() { # up I: worker I on port 910I, one thread
  "$work/worker" --port "910$1" --threads 1 > /dev/null 2>&1 &
  pids[$1]=$!
  disown  # a SIGKILL'd worker is the point here, not news
}
fleet() { # fleet K: workers 0..K-1, fresh
  local p i
  for p in ${pids[@]+"${pids[@]}"}; do
    kill "$p" 2>/dev/null
    while kill -0 "$p" 2>/dev/null; do sleep 0.1; done
  done
  pids=()
  for ((i = 0; i < $1; i++)); do up $i; done
  for ((i = 0; i < $1; i++)); do # a clean run starts with every worker up
    until curl -sf "http://127.0.0.1:910$i/health" > /dev/null; do sleep 0.1; done
  done
}
urls() { for ((i = 0; i < $1; i++)); do printf 'http://127.0.0.1:910%d ' $i; done; }
fail=0

run() { # run NAME ARGS...: time the coordinator, check its bits
  local name=$1
  shift
  local s=$(date +%s%N) got
  got=$("$work/mesh" "$@" 2> "$work/err")
  local ms=$((($(date +%s%N) - s) / 1000000))
  local acc=${got#*acc=}; acc=${acc%% price=*}
  local z=$(python3 -c "import sys; p, e = (float(x.split('=')[1]) for x in sys.argv[1].split()[-2:]); print('%+.2f' % ((p - $bs) / e))" "$got" 2> /dev/null)
  if [ "$acc" = "$want" ]; then printf 'ok   %-10s %7d ms  z=%s  %s\n' "$name" "$ms" "$z" "$(cat "$work/err")"
  else printf 'FAIL %-10s %7d ms  %s\n     got: %s\n' "$name" "$ms" "$(cat "$work/err")" "$got"; fail=1; fi
}

run local option 1 "$N" 0 8
fleet 2; run "2 x 50" option 1 "$N" 50 4 $(urls 2)
fleet 4; run "4 x 200" option 1 "$N" 200 4 $(urls 4)
fleet 4
( while :; do
    sleep "$((1 + RANDOM % 3))"
    v=$((RANDOM % 4))
    kill -9 "${pids[$v]}" 2> /dev/null
    echo "$(date +%s.%N | cut -c1-14) kill w$v" >> "$work/chaos"
    sleep "$((1 + RANDOM % 4))"
    "$work/worker" --port "910$v" --threads 1 > /dev/null 2>&1 &
    pids[$v]=$!
    disown
    echo "$(date +%s.%N | cut -c1-14) back w$v" >> "$work/chaos"
  done ) &
chaos=$!
run spot option 1 "$N" 200 4 $(urls 4)
kill $chaos 2>/dev/null
printf '     chaos: %s kills\n' "$(grep -c kill "$work/chaos" 2>/dev/null || echo 0)"
# the chaos loop's restarted workers are its own children: sweep the ports
pkill -f "$work/worker" 2>/dev/null
exit $fail
