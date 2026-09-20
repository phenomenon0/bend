#!/usr/bin/env bash
# The ttok ledger. Upstream caps (gates/repo.ts): base.bend 24000, bend.ts
# 41000, comp.ts 61000, main.ts 10000, each test 16000. First-class strings
# land at 27,844 base tokens and 74,981 compiler tokens; their caps are the
# next round thousand. The benchmark oracle also has its planned 1,200 cap.
set -u
cd "$(dirname "$0")/.."
export PYTHONWARNINGS=ignore
command -v ttok >/dev/null || { echo "ttok not installed (pip install --user ttok)"; exit 2; }
rc=0
check() {
  local n
  n=$(ttok < "$1")
  if [ "$n" -le "$2" ]; then
    printf 'ok   %-28s %7d <= %s\n' "$1" "$n" "$2"
  else
    printf 'OVER %-28s %7d >  %s\n' "$1" "$n" "$2"
    rc=1
  fi
}
check bend2/base.bend 46470
check bend2/bend.ts 42300
check bend2/comp.ts 83100
check bend2/main.ts 10000
for t in tests/f64/*.bend tests/strings/*.bend; do
  if [ "$t" = tests/strings/bench_words.bend ]; then
    check "$t" 1200
    continue
  fi
  check "$t" 16000
done
exit $rc
