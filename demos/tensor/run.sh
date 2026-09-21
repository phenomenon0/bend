#!/usr/bin/env bash
# The lane's four gates, reduced to one machine: every tests/tensor/*.bend
# must check, then interpret, then run as emitted JS, then run as emitted C,
# and the C binary must answer the same on one thread as on all of them --
# a schedule must not change an answer. Each run is compared with the file's
# own `#|` block. The runner lives here because gates/repo.ts's allow list
# has a row for demos/<dir>/<name>.sh and none for tests/tensor/<name>.sh.
set -uo pipefail
cd "$(dirname "$0")/../.."
export BEND_NO_TELEMETRY=1
work=$(mktemp -d /tmp/bend-tensor.XXXXXX)
trap 'rm -rf -- "$work"' EXIT
pass=0
fail=0

run() { # label, command...
  local label=$1 status=0
  shift
  timeout "${TENSOR_TIMEOUT:-300}" "$@" > "$work/actual" 2>&1 || status=$?
  if [ "$status" -eq 0 ] && diff -u "$work/expected" "$work/actual" > "$work/diff"; then
    printf 'ok   %-12s [%s]\n' "$name" "$label"
    pass=$((pass + 1))
  else
    printf 'FAIL %-12s [%s] status=%s\n' "$name" "$label" "$status"
    head -15 "$work/diff" "$work/actual"
    fail=$((fail + 1))
  fi
}

for t in tests/tensor/*.bend; do
  name=$(basename "$t" .bend)
  sed -n 's/^#|//p' "$t" > "$work/expected"
  if [ ! -s "$work/expected" ]; then
    printf 'FAIL %s: missing #| block\n' "$name"
    fail=$((fail + 1))
    continue
  fi
  printf 'All terms check.\n' > "$work/checked"
  cp "$work/expected" "$work/keep"
  cp "$work/checked" "$work/expected"
  run check bun bend2/main.ts "$t" --check-only
  cp "$work/keep" "$work/expected"
  run interpret bun bend2/main.ts "$t"
  for lane in js c; do
    target="$work/$name"
    [ "$lane" = js ] && target="$target.js"
    if timeout 180 bun bend2/main.ts "$t" -o "$target" > "$work/build" 2>&1; then
      if [ "$lane" = js ]; then
        run js bun "$target"
      else
        run c "$target" --gpu off
        run c-1thread "$target" --gpu off --threads 1
      fi
    else
      printf 'FAIL %-12s [%s build]\n' "$name" "$lane"
      head -20 "$work/build"
      fail=$((fail + 1))
    fi
  done
done

printf '\nTensor PASS: %d, FAIL: %d\n' "$pass" "$fail"
[ "$fail" -eq 0 ]
