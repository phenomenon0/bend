#!/bin/bash
# The kernel's regression book: every "# expect: VERDICT name" line of
# kernel/tests/*.core must match the kernel's verdict for that item.
set -u
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
cargo build --quiet --release --manifest-path "$ROOT/kernel/Cargo.toml" || exit 2
fail=0
for f in "$ROOT"/kernel/tests/*.core; do
  out=$("$ROOT/kernel/target/release/bend-kernel" "$f")
  while read -r _ _ want name; do
    got=$(printf '%s\n' "$out" | awk -v n="$name" '$2 == n || $2 == n":" { print $1; exit }')
    if [ "$got" != "$want" ]; then
      echo "FAIL $(basename "$f") $name: want $want, got ${got:-nothing}"
      fail=1
    fi
  done < <(grep '^# expect:' "$f")
done
[ $fail = 0 ] && echo "kernel rules: all as expected"
exit $fail
