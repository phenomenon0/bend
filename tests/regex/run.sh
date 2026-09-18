#!/usr/bin/env bash
# Regex lane: check/interpret/JS/C on every tests/regex/*.bend; a test with a
# call bang also runs on the GPU (as tests/strings/run.sh).
# `--selftest` runs the harness on a fixture whose #| block is deliberately wrong
# and passes only if that fixture is DETECTED as failing.
set -uo pipefail
cd "$(dirname "$0")/../.."
work=$(mktemp -d /tmp/bend-regex.XXXXXX)
trap 'rm -rf -- "$work"' EXIT
pass=0
fail=0

if [ "${1:-}" = "--selftest" ]; then
  mkdir "$work/wrong"
  printf 'import Base\n\ndef main() -> Nat:\n  1n\n\n#|2n\n' > "$work/wrong/wrong.bend"
  if REGEX_DIR="$work/wrong" bash "$0" > "$work/self" 2>&1; then
    printf 'FAIL selftest: wrong #| fixture was not detected\n'; cat "$work/self"; exit 1
  fi
  grep -q '^FAIL wrong' "$work/self" || { printf 'FAIL selftest: no FAIL line\n'; cat "$work/self"; exit 1; }
  printf 'ok   selftest: wrong #| fixture detected as failing\n'
  exit 0
fi

run() {
  local label=$1 expected=$2 status=0
  shift 2
  timeout "${REGEX_TIMEOUT:-300}" "$@" > "$work/actual" 2>&1 || status=$?
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
for t in "${REGEX_DIR:-tests/regex}"/*.bend; do
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
    run js "$work/expected" bun "$work/$name.js"
  else
    printf 'FAIL %-14s [js build]\n' "$name"; cat "$work/build"
    fail=$((fail + 1))
  fi
  if timeout 120 bun bend2/main.ts "$t" -o "$work/$name" > "$work/build" 2>&1; then
    run c "$work/expected" "$work/$name" --gpu off
    if grep -qE '[A-Za-z0-9_]!\(' "$t"; then
      run gpu "$work/expected" "$work/$name" --gpu 4GB
    fi
  else
    printf 'FAIL %-14s [c build]\n' "$name"; cat "$work/build"
    fail=$((fail + 1))
  fi
done
printf '\nRegex PASS: %d, FAIL: %d\n' "$pass" "$fail"
[ "$fail" -eq 0 ]
