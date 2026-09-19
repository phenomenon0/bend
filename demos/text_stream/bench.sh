#!/usr/bin/env bash
# Peak RSS of the chunked scan (main.bend) against the whole-file scan
# (whole.bend) as the input grows. C lane, one worker, GPU off; the median
# of three runs per cell. SIZES="8 64 256" (MiB) and OUT=/tmp/... override.
set -euo pipefail
cd "$(dirname "$0")/../.."
out=${OUT:-/tmp/bend-text-stream}
mkdir -p "$out"
bun bend2/main.ts demos/text_stream/main.bend -o "$out/stream"
bun bend2/main.ts demos/text_stream/whole.bend -o "$out/whole"
bun bend2/main.ts demos/text_stream/main.bend -o "$out/stream.js"

cell() { # binary file -> "line|KiB|seconds", the median-RSS run of three
  for _ in 1 2 3; do
    BEND_FILE=$2 /usr/bin/time -f '|%M|%e' "$1" --threads 1 --gpu off 2>&1 | tr -d '\n'
    echo
  done | sort -t'|' -k2 -n | sed -n 2p
}

: > "$out/c0.txt"
base=$(cell "$out/stream" "$out/c0.txt" | cut -d'|' -f2)
echo "empty-file RSS (runtime floor): $base KiB"
echo "| input | stream RSS KiB | over floor KiB | stream s | whole RSS KiB | whole s | same line |"
echo "|---|---:|---:|---:|---:|---:|---|"
for m in ${SIZES:-8 64 256}; do
  f=$out/c$m.txt
  [ -f "$f" ] || head -c $((m * 1048576)) < <(yes 'añ€😀 wörd the quick brown fox') > "$f"
  s=$(cell "$out/stream" "$f"); w=$(cell "$out/whole" "$f")
  IFS='|' read -r sl sk st <<< "$s"; IFS='|' read -r wl wk wt <<< "$w"
  same=no; [ "$sl" = "$wl" ] && same=yes
  if [ "$m" -le 8 ]; then # JS lane and an independent Python oracle
    [ "$(BEND_FILE=$f bun "$out/stream.js")" = "$sl" ] || same="no (js)"
    py=$(python3 - "$f" <<'PY'
import sys
b = open(sys.argv[1], "rb").read()
for cut in range(4):  # the tail head -c cut: one U+FFFD per byte
    try:
        s = b[:len(b) - cut].decode("utf-8") + "�" * cut
        break
    except UnicodeDecodeError:
        pass
h = 2166136261
for c in s:
    for x in ord(c).to_bytes(4, "little"):
        h = ((h ^ x) * 16777619) & 0xffffffff
print(f"{h} {len(s)} chars {len(s.split())} words")
PY
)
    [ "$py" = "$sl" ] || same="no (python: $py)"
  fi
  echo "| $m MiB | $sk | $((sk - base)) | $st | $wk | $wt | $same |"
  [ "$same" = yes ]
done
