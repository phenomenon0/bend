#!/usr/bin/env bash
# The numeric lane, checked three ways: the laws with their proofs,
# the demo's own program (byte for byte what hvm5 -s prints for it),
# and TESTS.bend against its own `#| lines`, the repo's convention.
# The reference counts the tests are read against are hvm4's, tabled
# in docs/omen/lanes/hvm5-num.md; this script gates the port alone.
set -u
cd "$(dirname "$0")/../.."
BEND="bun bend2/main.ts"
D=demos/pure_hvm5_mini
pass=0
fail=0

ck() { # label, want, got
  if [ "$3" = "$2" ]; then
    printf 'ok   %s\n' "$1"
    pass=$((pass + 1))
  else
    printf 'FAIL %s\n' "$1"
    diff <(printf '%s\n' "$2") <(printf '%s\n' "$3") | head -20
    fail=$((fail + 1))
  fi
}

ck laws "All terms check." "$($BEND $D/PROOF.bend 2>&1 | tail -1)"

$BEND $D/main.bend -o /tmp/h5_main >/dev/null 2>&1
ck demo "$(printf '&S{#0{()},#1{()}}\n- Itrs: 79 interactions')" "$(/tmp/h5_main 2>&1)"

$BEND $D/TESTS.bend -o /tmp/h5_tests >/dev/null 2>&1
ck tests "$(grep '^#|' $D/TESTS.bend | sed 's/^#|//')" "$(/tmp/h5_tests 2>&1)"

printf 'PASS: %d / %d\n' "$pass" $((pass + fail))
[ "$fail" -eq 0 ]
