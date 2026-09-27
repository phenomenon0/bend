#!/usr/bin/env bash
# The first energy-routed dispatch: bash demos/placement/run.sh
# One binary of main.bend runs the same bang on the CPU pool (--gpu off) or
# the RTX 3090 (--gpu on). place.py times each size on both units and
# integrates both energy rails net of idle; every run must print the C twin's
# four lines or the script stops. Then the policy predicts J/run for a new
# size on each unit from that table, picks the cheaper unit, runs it there,
# and measures it. Everything lands in demos/placement/receipts/.
#   SIZES="1024:200 ..." (PLACE_COLS:runs per batch)  ROUTE="4096:100 12582912:1"
set -euo pipefail
cd "$(dirname "$0")/../.."
export BEND_NO_TELEMETRY=1
here=demos/placement
R=$here/receipts
export BIN=${BIN:-/tmp/bend-placement}
SIZES=${SIZES:-1024:200 16384:40 131072:6 1048576:1 4194304:1 8388608:1 16777216:1}
ROUTE=${ROUTE:-4096:100 12582912:1}
rm -rf "$R"; mkdir -p "$R" "$BIN"
exec > >(tee "$R/run.log") 2>&1

echo "== machine =="
lscpu | sed -n 's/^Model name: *//p'
nvidia-smi --query-gpu=name,driver_version,power.limit --format=csv,noheader
printf 'nvcc %s, %s, load %s\n' "$(/usr/local/cuda/bin/nvcc --version | sed -n 's/.*release \([0-9.]*\).*/\1/p')" \
  "$(clang --version | head -1)" "$(cut -d' ' -f1-3 /proc/loadavg)"

echo "== build: one source, the CPU binary and its GPU program; the C twin =="
clang -std=c11 -O3 -o "$BIN/twin" $here/twin.c -lpthread
rm -f "$BIN"/twin_*.txt # the twin's answers are this run's, never a last run's
bun bend2/main.ts $here/main.bend -o "$BIN/main"
ls -l "$BIN/main" "$BIN/main.gpu" | awk '{ printf "  %-28s %8d bytes\n", $NF, $5 }'

echo "== the table: every run printed the twin's four lines, or this stops =="
echo "    cols unit runs   wall_s  window idle_c idle_g    cpu_J    gpu_J     J/run   ±J/run   nJ/MAC"
for s in $SIZES; do
  for u in off on; do python3 $here/place.py measure "$R" "$u" "${s%:*}" "${s#*:}"; done
done

echo "== identity: C twin = CPU pool = GPU, per size =="
python3 - "$R/table.jsonl" <<'PY' | tee "$R/identity.txt"
import json, sys
rows = [json.loads(l) for l in open(sys.argv[1])]
for m in sorted({r["m"] for r in rows}):
    f = {r["unit"]: r["four"] for r in rows if r["m"] == m}
    t = [r["twin"] for r in rows if r["m"] == m][0]
    assert f["off"] == f["on"] == t, m
    print(f"{m:>8}  twin = off = on  {' '.join(t)}")
PY

echo "== the policy: route each size to the unit with the lower predicted J/run =="
for s in $ROUTE; do
  m=${s%:*}
  u=$(python3 $here/place.py route "$R" "$m" 2> >(tee -a "$R/route.log" >&2))
  sleep 0.2
  echo "    cols unit runs   wall_s  window idle_c idle_g    cpu_J    gpu_J     J/run   ±J/run   nJ/MAC"
  python3 $here/place.py measure "$R" "$u" "$m" "${s#*:}" routed.jsonl
done
