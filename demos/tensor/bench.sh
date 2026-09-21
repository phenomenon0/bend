#!/usr/bin/env bash
# The tensor lane against its C twin: bash demos/tensor/bench.sh
# POWER.md protocol -- one bench at a time under /tmp/bend-bench.lock, a row
# timed only once C, one thread and sixteen print the SAME four lines, medians
# of three, the load average recorded beside the numbers. The four lines are
# the checksum and its three probes: agreement across backends proves the
# backends match, not that the bench measured anything, so the row also fails
# when `or` and `and` over the result's bits agree (every word one value) or
# when any word is an infinity or a NaN.
set -u
cd "$(dirname "$0")/../.."
export BEND_NO_TELEMETRY=1
here=demos/tensor
work=$(mktemp -d); trap 'rm -rf "$work"' EXIT
exec 9>/tmp/bend-bench.lock; flock 9

${CC:-clang} -std=c11 -O3 -o "$work/twin" $here/twin.c -lm || exit 1
med() { for _ in 1 2 3; do s=$(date +%s.%N); "$@" > /dev/null; e=$(date +%s.%N); echo "$e - $s" | bc; done | sort -n | sed -n 2p; }
bad=0
printf 'load %s  cc %s\n' "$(cut -d' ' -f1-3 /proc/loadavg)" "$(${CC:-clang} --version | head -1)"
printf '%-8s %8s %8s %8s %7s %7s\n' bench C bend-1T bend-16T 1T/C 1T/16T
# gemv and split are the same arithmetic in the same order, so both are timed
# against `twin gemv`; blocked reassociates the row sum and has its own twin.
for name in gemv split blocked; do
  case $name in blocked) arg=blocked ;; *) arg=gemv ;; esac
  bun bend2/main.ts "$here/bench_$name.bend" -o "$work/$name" > "$work/build" 2>&1 \
    || { echo "FAIL $name build"; head -5 "$work/build"; bad=1; continue; }
  want=$("$work/twin" "$arg")
  got1=$("$work/$name" --gpu off --threads 1); got16=$("$work/$name" --gpu off --threads 16)
  if [ "$want" != "$got1" ] || [ "$want" != "$got16" ]; then
    echo "FAIL $name: C [$want] 1T [$got1] 16T [$got16]"; bad=1; continue
  fi
  orb=$(echo "$want" | sed -n 2p); andb=$(echo "$want" | sed -n 3p); nf=$(echo "$want" | sed -n 4p)
  if [ "$orb" = "$andb" ] || [ "$nf" != 0 ]; then
    echo "FAIL $name: degenerate result, or=$orb and=$andb nonfin=$nf"; bad=1; continue
  fi
  c=$(med "$work/twin" "$arg")
  b1=$(med "$work/$name" --gpu off --threads 1)
  b16=$(med "$work/$name" --gpu off --threads 16)
  printf '%-8s %8.3f %8.3f %8.3f %6.2fx %6.2fx\n' "$name" "$c" "$b1" "$b16" \
    "$(echo "$b1 / $c" | bc -l)" "$(echo "$b1 / $b16" | bc -l)"
done
exit $bad
