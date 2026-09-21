#!/usr/bin/env bash
# `run.sh [prefix]`. Each fixture runs in four lanes against its #| block: the
# strict check, the interpreter, emitted JS, and C (on all threads, then on
# one). The demo runs in the same lanes against the rollout fixture's pin of
# it, so the demo's bytes are pinned too; the bench runs checked and on C.
# Before any of that, the comparison path is shown a deliberately wrong #|
# fixture and has to fail it.
set -uo pipefail
cd "$(dirname "$0")/../.."
export PATH="$HOME/.local/bin:$PATH"
export BEND_NO_TELEMETRY=1
mkdir -p "$HOME/.cache"
work=$(mktemp -d "$HOME/.cache/bend-decode.XXXXXX")
trap 'rm -rf -- "$work"' EXIT
pass=0
fail=0
printf 'All terms check.\n' > "$work/checked"

check() {
  bun -e '
    import * as B from "./bend2/bend.ts";
    const book = B.book_nil();
    await B.book_load(book, process.argv[1], "", new Map());
    B.book_valid(book);
    if (book.hols + book.open) process.exit(1);
    console.log("All terms check.");' "$1"
}
export -f check

run() {
  local label=$1 expected=$2 status=0
  shift 2
  : > "$work/diff"
  timeout "${DECODE_TIMEOUT:-300}" "$@" > "$work/actual" 2>&1 || status=$?
  if [ "$status" -eq 0 ] && diff -u "$expected" "$work/actual" > "$work/diff"; then
    printf 'ok   %-12s [%s]\n' "$name" "$label"
    pass=$((pass + 1))
  else
    printf 'FAIL %-12s [%s] status=%s\n' "$name" "$label" "$status"
    head -15 "$work/actual" "$work/diff"
    fail=$((fail + 1))
  fi
}

lanes() {
  local t=$1 expected=$2 lane
  run check "$work/checked" bash -c 'check "$1"' _ "$t"
  for lane in ${3:-interpret js c}; do
    if [ "$lane" = interpret ]; then
      run interpret "$expected" bun bend2/main.ts "$t"
      continue
    fi
    target="$work/$name"
    [ "$lane" = js ] && target="$target.js"
    if timeout 180 bun bend2/main.ts "$t" -o "$target" > "$work/build" 2>&1; then
      if [ "$lane" = js ]; then
        run js "$expected" bun "$target"
      else
        run c "$expected" "$target" --gpu off
        # a schedule must not change an answer: the same binary on one thread
        run c-1thread "$expected" "$target" --gpu off --threads 1
      fi
    else
      printf 'FAIL %-12s [%s build]\n' "$name" "$lane"
      head -20 "$work/build"
      fail=$((fail + 1))
    fi
  done
}

cat > "$work/wrong.bend" <<'BEND'
import Base
def main() -> Nat:
  1n
#|2n
BEND
name=wrong_fixture_control
sed -n 's/^#|//p' "$work/wrong.bend" > "$work/wrong-expected"
before=$fail
run interpret "$work/wrong-expected" bun bend2/main.ts "$work/wrong.bend" > "$work/control"
if [ "$fail" -eq "$((before + 1))" ] && [ "$(cat "$work/actual")" = "1n" ]; then
  fail=$before
  printf 'ok   wrong #| fixture detected as failing\n'
else
  printf 'FAIL wrong #| fixture escaped detection\n'
  fail=$((fail + 1))
fi

if rg -q -g '*.bend' '@unsafe|\?TODO' tests/decode/ power/decode.bend demos/decode/; then
  printf 'FAIL unsafe or open goal\n'
  fail=$((fail + 1))
fi

for t in tests/decode/*.bend; do
  name=$(basename "$t" .bend)
  if [ -n "${1:-}" ] && [[ "$name" != "$1"* ]]; then
    continue
  fi
  sed -n 's/^#|//p' "$t" > "$work/expected-$name"
  if [ ! -s "$work/expected-$name" ]; then
    printf 'FAIL %s: missing #| block\n' "$name"
    fail=$((fail + 1))
    continue
  fi
  lanes "$t" "$work/expected-$name"
done

# the demo prints the rollout fixture's report, up to its `steps` line
if [ -z "${1:-}" ] || [[ demo == "$1"* ]]; then
  name=demo
  sed -n 's/^#|//p' tests/decode/rollout.bend | sed '/^steps /q' > "$work/expected-demo"
  lanes demos/decode/main.bend "$work/expected-demo"
fi

# the bench, 65536 rollouts, on C only: the JS lane takes minutes on it
if [ -z "${1:-}" ] || [[ bench == "$1"* ]]; then
  name=bench
  printf 'rollouts 65536 steps 1179656 done 56110 bad certs 0\n' > "$work/expected-bench"
  lanes demos/decode/bench.bend "$work/expected-bench" c
fi
printf '\nDecode PASS: %d, FAIL: %d\n' "$pass" "$fail"
[ "$fail" -eq 0 ]
