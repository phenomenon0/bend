#!/usr/bin/env bash
# gates/perf.ts's runtime table on one machine. The gate shards its 48 cells
# over 48 minis and grades them against bench/runtime/_pin_/<hw>.txt; a Mac
# that is not in the cluster cannot be a shard, so this runs the same table
# by hand: the same two build lines (BUILD[0] and BUILD[1] are one line, so
# one CPU binary serves SEQ and PAR), the same flags (FLAGS with $nt the
# power of two under the core count and $gm from MEMORY, "on" otherwise),
# the same one warm run before the timed ones, and medians of three instead
# of the gate's single timed run. Prints the pin format, so the result can be
# read beside apple_m4.txt and apple_m4_max.txt column for column.
#
#   BEND="bun bend2/main.ts" bash docs/omen/apple/bench_pins.sh [bench...]
set -u
ROOT=${ROOT:-$(cd "$(dirname "$0")/../../.." && pwd)}
BEND=${BEND:-bun $ROOT/bend2/main.ts}
OUT=${OUT:-/tmp/bend-pins}
RUNS=${RUNS:-3}
export BEND_NO_TELEMETRY=1

CC="cc -std=c11 -O3"
GPU_CC="$CC -DBEND_METAL=1 -x objective-c -fobjc-arc"
case $(uname) in
  Darwin) GPU_LD="-framework Metal -framework Foundation" ;;
  *) GPU_CC="$CC -DBEND_CUDA=1"; GPU_LD="-lcuda -lcudart" ;;
esac

# the gate's THREADS verbatim. Its comment says "the power of two under the
# core count", but the loop doubles *while* nt < ncpu, so it stops on the
# first power of two at or above it: 16 on the cluster's 10-core minis, 32
# here. The code is what the pins were measured with, so the code is copied.
nt=1
ncpu=$(getconf _NPROCESSORS_ONLN)
while [ "$nt" -lt "$ncpu" ] && [ "$nt" -lt 256 ]; do nt=$((nt * 2)); done

span() { # the gate's MEMORY table, "on" for the rest
  case $1 in
    tree-bitonic | kmeans | merkle | nbody) echo 768MB ;;
    gameoflife | mandelbrot | queens | raytrace | symreg) echo 512MB ;;
    terrain) echo 1GB ;;
    *) echo on ;;
  esac
}

now() { perl -MTime::HiRes=time -e 'printf "%.3f\n", time()'; }
median() { sort -n | sed -n "$(((RUNS + 1) / 2))p"; }

mkdir -p "$OUT"
benches=${*:-$(cd "$ROOT/bench/runtime" && ls -d */ | grep -v _pin_ | tr -d /)}

printf '| %-12s | %-15s | %-15s | %-15s | %-10s |\n' \
  bench SEQ-CPU PAR-CPU PAR-GPU OUTPUT
printf '|%s|%s|%s|%s|%s|\n' \
  -------------- ----------------- ----------------- ----------------- ------------

for b in $benches; do
  d=$OUT/$b
  rm -rf "$d" && mkdir -p "$d"
  ( cd "$ROOT/bench/runtime/$b" && $BEND main.bend -o "$d/main.c" ) >"$d/emit.log" 2>&1 ||
    { printf '| %-12s | %-15s |\n' "$b" "emit failed"; continue; }
  $CC "$d/main.c" -lpthread -o "$d/cell_cpu" >"$d/cc_cpu.log" 2>&1 || true
  $GPU_CC "$d/main.c" -lpthread $GPU_LD -o "$d/cell_gpu" >"$d/cc_gpu.log" 2>&1 || true

  row=""
  out=""
  for mode in seq par gpu; do
    case $mode in
      seq) bin=$d/cell_cpu; flags="--threads 1 --gpu off" ;;
      par) bin=$d/cell_cpu; flags="--threads $nt --gpu off" ;;
      gpu) bin=$d/cell_gpu; flags="--gpu $(span "$b")" ;;
    esac
    if [ ! -x "$bin" ]; then
      row="$row$(printf ' | %-15s' 'build err')"
      continue
    fi
    "$bin" $flags >"$d/$mode.warm" 2>"$d/$mode.warmerr" # the gate's warm run
    if [ $? -ne 0 ]; then
      row="$row$(printf ' | %-15s' "$(head -c 15 "$d/$mode.warmerr")")"
      continue
    fi
    : >"$d/$mode.times"
    for i in $(seq "$RUNS"); do
      t0=$(now)
      /usr/bin/time -l "$bin" $flags >"$d/$mode.out" 2>"$d/$mode.time"
      t1=$(now)
      echo "$t0 $t1" | awk '{printf "%.3f\n", $2 - $1}' >>"$d/$mode.times"
    done
    secs=$(median <"$d/$mode.times")
    # /usr/bin/time -l: "maximum resident set size" in bytes on Darwin, KiB on GNU
    rss=$(awk '/maximum resident set size/ {print $1}' "$d/$mode.time")
    mb=$(awk -v r="$rss" -v u="$(uname)" \
      'BEGIN { printf "%.1f", r / (u == "Darwin" ? 1048576 : 1024) }')
    row="$row$(printf ' | %6ss %7sM' "$secs" "$mb")"
    [ -n "$out" ] || out=$(head -1 "$d/$mode.out")
    [ "$(head -1 "$d/$mode.out")" = "$out" ] ||
      out="$out/MISMATCH:$mode:$(head -1 "$d/$mode.out")"
  done
  printf '| %-12s%s | %-10s |\n' "$b" "$row" "$out"
done

printf '\n# %s, %s cores, nt=%s, medians of %s, %s\n' \
  "$(uname -m)" "$ncpu" "$nt" "$RUNS" "$(uptime | sed 's/.*average[s]*: *//')"
