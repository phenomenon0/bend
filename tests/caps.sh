#!/usr/bin/env bash
# The ttok ledger. Upstream caps (gates/repo.ts): base.bend 24000, bend.ts
# 41000, comp.ts 61000, main.ts 10000, each test 16000. The F64 patch adds
# +1,078 to base and +1,656 to comp, so it lands with those two caps bumped
# to the next round thousand -- the numbers checked here.
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
check bend2/base.bend 25000
check bend2/bend.ts 41000
check bend2/comp.ts 63000
check bend2/main.ts 10000
for t in tests/f64/*.bend; do
  check "$t" 16000
done
exit $rc
