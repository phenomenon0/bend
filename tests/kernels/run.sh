#!/usr/bin/env bash
# Each #| is an exact pin. A lane fails on a bad exit, timeout, missing pin,
# build failure or output mismatch; the vector and lane are always named.
# --million runs only the optional RFC 6234 million-a resource probe.
# --selftest proves that wrong pins, holes and an empty suite are rejected.
set -uo pipefail
cd "$(dirname "$0")/../.." || exit 2
work=$(mktemp -d /tmp/bend-kernels.XXXXXX) || exit 2
trap 'rm -rf -- "$work"' EXIT
ulimit -c 0
pass=0
fail=0
mode=${1:-}
lane_timeout=${KERNELS_TIMEOUT:-300}
case "$mode" in
  ""|--million|--selftest) ;;
  *) printf 'usage: %s [--million|--selftest]\n' "$0"; exit 2 ;;
esac
if [ "$mode" = --million ]; then lane_timeout=${KERNELS_TIMEOUT:-30}; fi

if [ "$mode" = --selftest ]; then
  mkdir "$work/wrong" "$work/hole" "$work/empty"
  printf 'import Base\n\ndef main() -> Nat:\n  1n\n\n#|2n\n' > "$work/wrong/wrong.bend"
  printf 'import Base\n\ndef main() -> Nat:\n  ?\n\n#|0n\n' > "$work/hole/hole.bend"
  for probe in wrong hole empty; do
    if KERNELS_DIR="$work/$probe" bash "$0" > "$work/$probe.log" 2>&1; then
      printf 'FAIL selftest [%s]: accepted a broken suite\n' "$probe"
      cat "$work/$probe.log"; exit 1
    fi
  done
  for lane in interpret js c; do
    grep -q "^FAIL wrong \[$lane\]" "$work/wrong.log" || {
      cat "$work/wrong.log"; exit 1;
    }
  done
  grep -q '^ok   wrong \[check\]' "$work/wrong.log" || exit 1
  grep -q '^FAIL hole \[check\]' "$work/hole.log" || exit 1
  grep -q '^FAIL suite \[fixtures\]' "$work/empty.log" || exit 1
  printf 'Kernels selftest PASS: wrong pin (3 lanes), hole (strict check), empty suite\n'
  exit 0
fi

run() {
  local lane=$1 expected=$2 status=0
  shift 2
  : > "$work/diff"
  timeout --kill-after=5 "$lane_timeout" "$@" > "$work/actual" 2>&1 || status=$?
  if [ "$status" -eq 0 ] && diff -u "$expected" "$work/actual" > "$work/diff"; then
    printf 'ok   %s [%s]\n' "$name" "$lane"
    pass=$((pass + 1))
  else
    printf 'FAIL %s [%s] status=%s\n' "$name" "$lane" "$status"
    cat "$work/actual" "$work/diff"
    fail=$((fail + 1))
  fi
}

build_run() {
  local lane=$1 target=$2 status=0
  shift 2
  timeout --kill-after=5 "${KERNELS_BUILD_TIMEOUT:-120}" bun bend2/main.ts "$t" -o "$target" > "$work/build" 2>&1 || status=$?
  if [ "$status" -eq 0 ]; then
    run "$lane" "$work/expected" "$@"
  else
    printf 'FAIL %s [%s build] status=%s\n' "$name" "$lane" "$status"
    cat "$work/build"
    fail=$((fail + 1))
  fi
}

dir=${KERNELS_DIR:-tests/kernels}
if [ "$mode" = --million ]; then dir=${KERNELS_DIR:-tests/kernels/slow}; fi
shopt -s nullglob
fixtures=("$dir"/*.bend)
if [ "${#fixtures[@]}" -eq 0 ]; then
  printf 'FAIL suite [fixtures]: no .bend fixtures in %s\n' "$dir"
  exit 1
fi
printf 'All terms check.\n' > "$work/checked"
for t in "${fixtures[@]}"; do
  name=$(basename "$t" .bend)
  sed -n 's/^#|//p' "$t" > "$work/expected"
  if [ ! -s "$work/expected" ]; then
    printf 'FAIL %s [fixtures]: missing #| pin\n' "$name"
    fail=$((fail + 1))
    continue
  fi
  run check "$work/checked" bun -e '
    import * as B from "./bend2/bend.ts";
    try {
      const book = B.book_nil();
      await B.book_load(book, process.argv[1], "", new Map());
      B.book_valid(book);
      if (book.hols + book.open) {
        console.error(`Error: ${book.hols + book.open} hole/open goal(s)`);
        process.exit(1);
      }
      console.log("All terms check.");
    } catch (e) {
      console.error(e?.$ === "Err" ? B.err_show(e) : String(e));
      process.exit(1);
    }' "$t"
  run interpret "$work/expected" bun bend2/main.ts "$t"
  build_run js "$work/test.js" bun "$work/test.js"
  build_run c "$work/test" "$work/test" --threads 1 --gpu off
done
printf '\nKernels PASS: %d, FAIL: %d\n' "$pass" "$fail"
if [ "$mode" != --million ] && [ -z "${KERNELS_DIR:-}" ]; then
  printf 'Optional million-a probe: bash tests/kernels/run.sh --million\n'
fi
[ "$fail" -eq 0 ]
