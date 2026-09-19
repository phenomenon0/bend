#!/usr/bin/env bash
# The four lanes of gates/test.ts, reduced to one machine: a test passes when
# its check, its interpreted run, its JS run and its C run all print its `#|
# lines` (the cluster shards this work; here the tests run in order). A test
# with a call bang also gets one untimed warm run on the GPU, as the gate
# gives it, then a timed one. A lane that cannot build fails that lane only.
set -u
cd "$(dirname "$0")/.."
# Keep the 19-result f64 gate stable; strings have their own four-lane suite.
if [ "${1:-}" = "--strings" ]; then
  exec bash tests/strings/run.sh
fi
BEND="bun bend2/main.ts"
pass=0
fail=0

run() { # label, command...
  local label=$1
  shift
  local got
  got=$(timeout 300 "$@" 2>&1)
  if [ "$got" = "$want" ]; then
    printf 'ok   %-22s [%s]\n' "$name" "$label"
    pass=$((pass + 1))
  else
    printf 'FAIL %-22s [%s]\n' "$name" "$label"
    diff <(printf '%s\n' "$want") <(printf '%s\n' "$got") | head -10
    fail=$((fail + 1))
  fi
}

for t in tests/f64/*.bend; do
  name=$(basename "$t" .bend)
  want=$(grep '^#|' "$t" | sed 's/^#|//')
  run interpret $BEND "$t"
  if $BEND "$t" -o "/tmp/g_$name.js" >/dev/null 2>&1; then
    run js bun "/tmp/g_$name.js"
  else
    printf 'FAIL %-22s [js] (build)\n' "$name"
    fail=$((fail + 1))
  fi
  if $BEND "$t" -o "/tmp/g_$name" >/dev/null 2>&1; then
    run c "/tmp/g_$name"
    if grep -qE '[A-Za-z0-9_]!\(' "$t"; then
      "/tmp/g_$name" --gpu 4GB >/dev/null 2>&1 # untimed warm run (context + shader)
      run gpu "/tmp/g_$name" --gpu 4GB
    fi
  else
    printf 'FAIL %-22s [c] (build)\n' "$name"
    fail=$((fail + 1))
  fi
done

printf '\nPASS: %d, FAIL: %d\n' "$pass" "$fail"
[ "$fail" -eq 0 ]
