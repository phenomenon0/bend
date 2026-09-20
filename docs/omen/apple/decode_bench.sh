#!/usr/bin/env bash
# decode_len.bend on 8 MiB of ASCII and 8 MiB of Unicode, C and JS lanes.
# The corpora are tests/strings/bench.sh's own: its two unit strings repeated
# to exactly N bytes, the tail cut on a code point and space-padded, and its
# own code-point count as the oracle every run must print.
#   ROOT=~/bend-apple docs/omen/apple/decode_bench.sh      # MIB=8 RUNS=7
set -euo pipefail
ROOT=${ROOT:-$(cd "$(dirname "$0")/../../.." && pwd)}
OUT=${OUT:-/tmp/bend-decode}
MIB=${MIB:-8}
RUNS=${RUNS:-7}
WRAP=${WRAP:-}
mkdir -p "$OUT"

now() { perl -MTime::HiRes=time -e 'printf "%.0f\n", time() * 1000'; }
median() { sort -n | sed -n "$(((RUNS + 1) / 2))p"; }

python3 - "$OUT" "$MIB" <<'PY'
import sys
from pathlib import Path
out, mib = Path(sys.argv[1]), int(sys.argv[2])
units = {'ascii': '  alpha beta\n gamma\t\n', 'unicode': '  café λ😀\n 漢字\t\n'}
rows = []
for name, unit in units.items():
    data, size = unit.encode(), mib * 1024**2
    reps = size // len(data)
    rest = size - len(data) * reps
    suffix = data[:rest].decode('utf-8', errors='ignore')
    suffix += ' ' * (rest - len(suffix.encode()))
    path = out / f'{name}-{mib}MiB.txt'
    if not path.exists() or path.stat().st_size != size:
        with path.open('wb') as f:
            block = data * 4096
            for _ in range(reps // 4096):
                f.write(block)
            f.write(data * (reps % 4096) + suffix.encode())
    rows.append(f'{name} {path} {size} {len(unit) * reps + len(suffix)}')
(out / 'corpora.txt').write_text('\n'.join(rows) + '\n')
PY

[ -x "$OUT/decode_len" ] && [ ! "$ROOT/docs/omen/apple/decode_len.bend" -nt "$OUT/decode_len" ] ||
  (cd "$ROOT" && bun bend2/main.ts docs/omen/apple/decode_len.bend -o "$OUT/decode_len" &&
   bun bend2/main.ts docs/omen/apple/decode_len.bend -o "$OUT/decode_len.js")

printf '%8s %5s %9s %9s %9s %9s %10s\n' corpus lane wall_s read_s length_s MB_s Mcp_s
while read -r name path bytes want; do
  export DECODE_FILE=$path
  for lane in c js; do
    [ "$lane" = c ] && cmd="$WRAP $OUT/decode_len --gpu off --threads 1" ||
      cmd="$WRAP bun $OUT/decode_len.js"
    : >"$OUT/wall"; : >"$OUT/read"; : >"$OUT/len"
    for i in $(seq 0 "$RUNS"); do                   # run 0 is the warm one
      a=$(now); got=$($cmd 2>"$OUT/err"); b=$(now)
      [ "$got" = "$want" ] || { echo "MISMATCH $name/$lane: $got != $want"; exit 1; }
      [ "$i" = 0 ] && continue
      echo $((b - a)) >>"$OUT/wall"
      sed -n 's/read \([0-9]*\) ms.*/\1/p' "$OUT/err" >>"$OUT/read"
      sed -n 's/.*length \([0-9]*\) ms.*/\1/p' "$OUT/err" >>"$OUT/len"
    done
    awk -v n="$name" -v l="$lane" -v w="$(median <"$OUT/wall")" \
      -v r="$(median <"$OUT/read")" -v p="$(median <"$OUT/len")" \
      -v b="$bytes" -v c="$want" 'BEGIN { printf "%8s %5s %9.3f %9.3f %9.3f %9.1f %10.2f\n",
        n, l, w/1000, r/1000, p/1000, b/1048576/(w/1000), c/1e6/(w/1000) }'
  done
done <"$OUT/corpora.txt"
printf '%s runs per row after one warm run, median; every run printed the oracle count\n' "$RUNS"
