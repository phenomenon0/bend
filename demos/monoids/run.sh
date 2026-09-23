#!/usr/bin/env bash
# `demos/monoids/run.sh [name]`: each program against its #| block. Per program:
# the oracle (NAME_gen.py --fixture must print the checked-in #| lines), then
# interpret, emitted JS, C, and the same C binary on one thread and on four --
# a schedule must not change an answer, which is the whole claim here.
# `BIG=1` also builds the *_big.bend runs and times them per thread count.
set -uo pipefail
cd "$(dirname "$0")/../.."
export BEND_NO_TELEMETRY=1
work=$(mktemp -d /tmp/bend-monoids.XXXXXX)
trap 'rm -rf -- "$work"' EXIT
pass=0
fail=0

run() { # run LABEL CMD...: compare CMD's output to $work/expected
  local label=$1 status=0
  shift
  timeout 600 "$@" > "$work/actual" 2>&1 || status=$?
  if [ "$status" -eq 0 ] && diff -u "$work/expected" "$work/actual" > "$work/diff"; then
    printf 'ok   %-8s [%s]\n' "$name" "$label"; pass=$((pass + 1))
  else
    printf 'FAIL %-8s [%s] status=%s\n' "$name" "$label" "$status"
    head -20 "$work/diff"; fail=$((fail + 1))
  fi
}

for t in demos/monoids/utf8.bend demos/monoids/kulisch.bend demos/monoids/pcg.bend; do
  name=$(basename "$t" .bend)
  [ -n "${1:-}" ] && [ "$name" != "$1" ] && continue
  sed -n 's/^#|//p' "$t" > "$work/expected"
  [ -s "$work/expected" ] || { echo "FAIL $name: no #| block"; fail=$((fail + 1)); continue; }
  run oracle bash -c 'python3 "$1" --fixture | sed "s/^#|//"' _ "demos/monoids/${name}_gen.py"
  run interpret bun bend2/main.ts "$t"
  if bun bend2/main.ts "$t" -o "$work/$name.js" > "$work/build" 2>&1; then
    run js node "$work/$name.js"
  else
    echo "FAIL $name [js build]"; head "$work/build"; fail=$((fail + 1))
  fi
  if bun bend2/main.ts "$t" -o "$work/$name" > "$work/build" 2>&1; then
    run c-1 "$work/$name" --gpu off --threads 1
    run c-4 "$work/$name" --gpu off --threads 4
  else
    echo "FAIL $name [c build]"; head "$work/build"; fail=$((fail + 1))
  fi
done
printf '\nmonoids PASS: %d, FAIL: %d\n' "$pass" "$fail"

if [ -n "${BIG:-}" ]; then
  for b in utf8 kulisch pcg; do
    bun bend2/main.ts "demos/monoids/${b}_big.bend" -o "$work/${b}_big" > /dev/null || exit 1
    for th in 1 2 4 8; do
      s=$(date +%s%N)
      out=$("$work/${b}_big" --gpu off --threads "$th")
      printf '%-8s threads=%-2s %6.2f s  %s\n' "$b" "$th" "$((($(date +%s%N) - s) / 10000000))e-2" "$out"
    done
  done
fi
[ "$fail" -eq 0 ]
