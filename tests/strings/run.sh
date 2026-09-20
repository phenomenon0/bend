#!/usr/bin/env bash
# Check/interpret/JS/C, with explicit expected JS rejection for raw strings.
# io_utf8 is an IO main: its CLI lane runs JS; all other specimens are pure.
set -uo pipefail
cd "$(dirname "$0")/../.."
work=$(mktemp -d /tmp/bend-strings.XXXXXX)
trap 'rm -rf -- "$work"' EXIT
pass=0
fail=0

run() {
  local label=$1 expected=$2 status=0
  shift 2
  timeout "${STRING_TIMEOUT:-300}" "$@" > "$work/actual" 2>&1 || status=$?
  if [ "$status" -eq 0 ] && diff -u "$expected" "$work/actual" > "$work/diff"; then
    printf 'ok   %-14s [%s]\n' "$name" "$label"
    pass=$((pass + 1))
  else
    printf 'FAIL %-14s [%s] status=%s\n' "$name" "$label" "$status"
    cat "$work/actual" "$work/diff" 2>/dev/null | head -15
    fail=$((fail + 1))
  fi
}

printf 'All terms check.\n' > "$work/checked"
for t in tests/strings/*.bend; do
  name=$(basename "$t" .bend)
  sed -n 's/^#|//p' "$t" > "$work/expected"
  if [ ! -s "$work/expected" ]; then
    printf 'FAIL %s: missing measured #| block\n' "$name"
    fail=$((fail + 1))
    continue
  fi
  run check "$work/checked" bun -e '
    import * as B from "./bend2/bend.ts";
    const book = B.book_nil();
    await B.book_load(book, process.argv[1], "", new Map());
    B.book_valid(book);
    if (book.hols + book.open) process.exit(1);
    console.log("All terms check.");' "$t"
  run interpret "$work/expected" bun bend2/main.ts "$t"
  if timeout 120 bun bend2/main.ts "$t" -o "$work/$name.js" > "$work/build" 2>&1; then
    if [ -f "tests/strings/$name.js-error" ]; then
      status=0
      timeout 30 bun "$work/$name.js" > "$work/actual" 2>&1 || status=$?
      if [ "$status" -eq 1 ] && diff -u "tests/strings/$name.js-error" "$work/actual"; then
        printf 'ok   %-14s [js: expected rejection]\n' "$name"
        pass=$((pass + 1))
      else
        printf 'FAIL %-14s [js: expected rejection] status=%s\n' "$name" "$status"
        fail=$((fail + 1))
      fi
    else
      run js "$work/expected" bun "$work/$name.js"
    fi
  else
    printf 'FAIL %-14s [js build]\n' "$name"; cat "$work/build"
    fail=$((fail + 1))
  fi
  if timeout 120 bun bend2/main.ts "$t" -o "$work/$name" > "$work/build" 2>&1; then
    run c "$work/expected" "$work/$name" --gpu off
    if rg -q '[A-Za-z0-9_]!\(' "$t"; then
      run gpu "$work/expected" "$work/$name" --gpu 4GB
    fi
  else
    printf 'FAIL %-14s [c build]\n' "$name"; cat "$work/build"
    fail=$((fail + 1))
  fi
done
# gaps.bend is generated: CPython's str methods are its oracle
name=gaps
run oracle tests/strings/gaps.bend python3 tests/strings/gaps_gen.py
printf '\nStrings PASS: %d, FAIL: %d\n' "$pass" "$fail"
[ "$fail" -eq 0 ]
