#!/usr/bin/env bash
set -euo pipefail

# Resolve relative to this script, even when invoked from the repository root.
suite_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
cd -- "$suite_dir"
export LC_ALL=C

for tool in bun python3 diff timeout; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    printf 'FAIL prerequisite: %s is required\n' "$tool" >&2
    exit 1
  fi
done

work=$(mktemp -d /tmp/cx_suite.XXXXXX)
trap 'rm -rf -- "$work"' EXIT
passed=0
failed=0
suite_errors=0

# A failed build/run fails every affected case and does not stop other programs.
unavailable() {
  local expected=$1 reason=$2 line
  while IFS= read -r line; do
    printf 'FAIL %s (%s)\n' "${line%% *}" "$reason"
    failed=$((failed + 1))
  done < "$expected"
}

python3 expected.py --list > "$work/suites"
while IFS= read -r test; do
  expected="$work/$test.expected"
  actual="$work/$test.actual"
  binary="/tmp/cx_$test"
  if ! python3 expected.py "$test" > "$expected"; then
    printf 'FAIL %s (Python oracle failed)\n' "$test"
    suite_errors=$((suite_errors + 1))
    continue
  fi
  if ! timeout "${BUILD_TIMEOUT:-120}s" bun ../../bend2/main.ts "$test.bend" -o "$binary" > "$work/$test.build.log" 2>&1; then
    unavailable "$expected" 'build failed or timed out'
    cat "$work/$test.build.log" >&2
    continue
  fi
  if ! timeout "${RUN_TIMEOUT:-30}s" "$binary" > "$actual" 2> "$work/$test.stderr"; then
    unavailable "$expected" 'execution failed or timed out'
    cat "$work/$test.stderr" >&2
    continue
  fi

  # Compare whole stdout byte-for-byte; extra/missing/duplicate/reordered lines
  # and a missing final newline are failures, even when some cases still pass.
  if ! diff -u "$expected" "$actual" > "$work/$test.diff"; then
    suite_errors=$((suite_errors + 1))
    printf 'FAIL %s (stdout differs)\n' "$test"
    cat "$work/$test.diff"
  fi
  mapfile -t expected_lines < "$expected"
  mapfile -t actual_lines < "$actual"
  for i in "${!expected_lines[@]}"; do
    line=${expected_lines[$i]}
    if [[ ${actual_lines[$i]-} == "$line" ]]; then
      printf 'PASS %s\n' "${line%% *}"
      passed=$((passed + 1))
    else
      printf 'FAIL %s (expected: %s; actual: %s)\n' "${line%% *}" "$line" "${actual_lines[$i]-<missing>}"
      failed=$((failed + 1))
    fi
  done
  if [[ -s "$work/$test.stderr" ]]; then
    cat "$work/$test.stderr" >&2
  fi
done < "$work/suites"

printf '\n%d PASS, %d FAIL; %d suite errors\n' "$passed" "$failed" "$suite_errors"
[[ $failed -eq 0 && $suite_errors -eq 0 ]]
