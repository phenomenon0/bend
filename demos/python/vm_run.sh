#!/usr/bin/env bash
# `vm_run.sh [prefix]`. The Python VM lane: for each fixture in demos/python/vm_*.py,
# CPython 3.11.15 runs it and demos/python/vm.bend runs it, and the two outputs are
# compared byte for byte. Four lanes: the VM checks strictly once (it is one program,
# the fixtures are its data), then every fixture runs on the interpreter, the emitted
# JS and the emitted C. Two controls ride along: a mutated expectation must be caught
# by the same comparison path, and a construct outside the subset must be REFUSED by
# the compiler rather than miscompiled. Prints `VM PASS: n, FAIL: 0`.
# This script belongs at tests/vm/run.sh and is not there: gates/repo.ts has no allow
# row for tests/vm/**, and this lane may not edit gates/. See docs/omen/lanes/pyspike.md.
# Its scratch still lives under tests/vm/_out/ (gitignored) because /tmp is blocked.
set -uo pipefail
cd "$(dirname "$0")/../.."
# Pin the environment alongside the bytes: the interpreter's daily check prints a
# one-line update notice to stderr when upstream has a newer release, and these
# lanes byte-compare raw stdout+stderr.
export BEND_NO_TELEMETRY=1
work=tests/vm/_out
vm=demos/python/vm.bend
mkdir -p "$work"
pass=0
fail=0
name=""

# The oracle is pinned: CPython's print formatting IS the specification here.
want=3.11.15
got=$(python3 -c 'import platform; print(platform.python_version())' 2>/dev/null)
if [ "$got" != "$want" ]; then
  printf 'FAIL oracle: python3 is %s, the lane is pinned to %s\n' "${got:-missing}" "$want"
  printf '\nVM PASS: 0, FAIL: 1\n'
  exit 1
fi

run() {
  local label=$1 expected=$2 status=0
  shift 2
  : > "$work/diff"
  timeout "${VM_TIMEOUT:-300}" "$@" > "$work/actual" 2>&1 || status=$?
  if [ "$status" -eq 0 ] && diff -u "$expected" "$work/actual" > "$work/diff"; then
    printf 'ok   %-12s [%s]\n' "$name" "$label"
    pass=$((pass + 1))
  else
    printf 'FAIL %-12s [%s] status=%s\n' "$name" "$label" "$status"
    head -15 "$work/actual" "$work/diff"
    fail=$((fail + 1))
  fi
}

check() {
  bun -e '
    import * as B from "./bend2/bend.ts";
    const book = B.book_nil();
    await B.book_load(book, process.argv[1], "", new Map());
    B.book_valid(book);
    if (book.hols + book.open) process.exit(1);
    console.log("All terms check.");' "$1"
}

name=vm
printf 'All terms check.\n' > "$work/checked"
export -f check
run check "$work/checked" bash -c 'check "$1"' _ "$vm"

for lane in js c; do
  target="$work/vm.js"
  [ "$lane" = c ] && target="$work/vm.bin"
  if ! timeout 600 bun bend2/main.ts "$vm" -o "$target" > "$work/build" 2>&1; then
    printf 'FAIL %-12s [%s build]\n' vm "$lane"
    head -20 "$work/build"
    fail=$((fail + 1))
  fi
done

for f in demos/python/vm_*.py; do
  name=$(basename "$f" .py)
  if [ -n "${1:-}" ] && [[ "$name" != "$1"* ]]; then
    continue
  fi
  python3 "$f" > "$work/expected" 2>&1
  export PY_SOURCE=$f
  run interpret "$work/expected" bun bend2/main.ts "$vm"
  run js "$work/expected" bun "$work/vm.js"
  run c "$work/expected" "$work/vm.bin" --gpu off
done

# Control 1: the same comparison path, handed an expectation that is off by one
# line, must report the failure. A green lane that cannot go red proves nothing.
name=mutation_control
printf 'print(6 * 7)\n' > "$work/control.py"
printf '43\n' > "$work/control-expected"
before=$fail
export PY_SOURCE=$work/control.py
run c "$work/control-expected" "$work/vm.bin" --gpu off
if [ "$fail" -eq "$((before + 1))" ] && [ "$(cat "$work/actual")" = "42" ]; then
  fail=$before
  pass=$((pass + 1))
  printf 'ok   %-12s [mutated expectation caught]\n' "$name"
else
  printf 'FAIL %-12s [mutated expectation escaped]\n' "$name"
  fail=$((fail + 1))
fi

# Control 2: outside the subset is REFUSED, not miscompiled. One line each for the
# three refusals the subset leans on, exact message and a non-zero exit.
name=refusal_control
refused() {
  printf '%s\n' "$1" > "$work/refuse.py"
  local status=0
  PY_SOURCE=$work/refuse.py "$work/vm.bin" --gpu off > "$work/refused" 2>&1 || status=$?
  # shellcheck disable=SC2034
  if [ "$status" -ne 0 ] && grep -qF "$2" "$work/refused"; then
    pass=$((pass + 1))
    printf 'ok   %-12s [%s]\n' "$name" "$2"
  else
    fail=$((fail + 1))
    printf 'FAIL %-12s [%s] status=%s\n' "$name" "$2" "$status"
    head -5 "$work/refused"
  fi
}
refused 'print(1 < 2 < 3)' 'chained comparisons are outside the subset'
refused 'print("hi")'      'strings are outside the subset'
refused 'print(3 - 9)'     'a negative result is outside the subset'

printf '\nVM PASS: %d, FAIL: %d\n' "$pass" "$fail"
[ "$fail" -eq 0 ]
