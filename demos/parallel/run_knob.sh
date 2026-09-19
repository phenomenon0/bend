#!/usr/bin/env bash
# The thread knob: ONE binary of knob.bend, run at --threads 1,2,4,8,16 (three
# runs each, median), every output asserted byte-identical and equal to the
# Python oracle; then the same source interpreted. Every number printed is
# measured by this run.
#   SHARED=1     also measure the variant without the leaf copy (does not scale)
#   INTERP=full  interpret the full corpus too (minutes) instead of the slice
#   THREADS="1 2 4 8 16"  RUNS=3  BLOCKS=8192 (x 65536 code points)
set -euo pipefail
cd "$(dirname "$0")/../.."
DIR=${CORPUS_DIR:-$HOME/videokit-corpus}
BLOCKS=${BLOCKS:-8192}
THREADS=${THREADS:-1 2 4 8 16}
RUNS=${RUNS:-3}
OUT=$(mktemp -d /tmp/knob.XXXXXX)
mkdir -p "$DIR"
corpus() { # file, blocks
  [ -f "$1" ] && [ -f "$1.oracle" ] || python3 demos/parallel/gen_corpus.py "$1" "$2"
}
corpus "$DIR/knob-$BLOCKS.txt" "$BLOCKS"
corpus "$DIR/knob-256.txt" 256
BIG=$DIR/knob-$BLOCKS.txt
want=$(cat "$BIG.oracle")
printf 'corpus  %s  (%s bytes)\noracle  %s  (python: tokens:checksum)\n' \
  "$BIG" "$(stat -c %s "$BIG")" "$want"

median() { sort -n | sed -n "$(((RUNS + 1) / 2))p"; }

table() { # binary
  local base_wall="" base_scan=""
  printf '%8s %10s %8s %10s %8s  %s\n' threads wall_s speedup scan_s speedup output
  for t in $THREADS; do
    : >"$OUT/wall"; : >"$OUT/scan"
    for _ in $(seq "$RUNS"); do
      a=$(date +%s%N)
      got=$(KNOB_CORPUS=$BIG "$1" --gpu off --threads "$t" 2>"$OUT/err")
      b=$(date +%s%N)
      [ "$got" = "$want" ] || { echo "MISMATCH at --threads $t: $got != $want"; exit 1; }
      echo $(((b - a) / 1000000)) >>"$OUT/wall"
      sed -n 's/.*scan \([0-9]*\) ms.*/\1/p' "$OUT/err" >>"$OUT/scan"
    done
    w=$(median <"$OUT/wall"); s=$(median <"$OUT/scan")
    : "${base_wall:=$w}" "${base_scan:=$s}"
    awk -v t="$t" -v w="$w" -v s="$s" -v bw="$base_wall" -v bs="$base_scan" -v o="$got" \
      'BEGIN { printf "%8d %10.2f %7.2fx %10.2f %7.2fx  %s\n", t, w/1000, bw/w, s/1000, bs/s, o }'
  done
}

echo; echo "== compile once (C lane) =="
bun bend2/main.ts demos/parallel/knob.bend -o "$OUT/knob"
echo "== same binary, --threads knob (median of $RUNS; wall = read + decode + scan) =="
table "$OUT/knob"
echo "all outputs byte-identical and equal to the oracle"

if [ "${SHARED:-0}" = 1 ]; then
  echo; echo "== variant WITHOUT the leaf copy (views of one shared payload) =="
  sed 's/String.lines(String.copy(s))/String.lines(s)/' demos/parallel/knob.bend >"$OUT/knob_shared.bend"
  bun bend2/main.ts "$OUT/knob_shared.bend" -o "$OUT/knob_shared"
  table "$OUT/knob_shared"
fi

echo; echo "== same program, interpreted (bun bend2/main.ts knob.bend) =="
[ "${INTERP:-slice}" = full ] && SMALL=$BIG || SMALL=$DIR/knob-256.txt
a=$(date +%s%N)
got=$(KNOB_CORPUS=$SMALL bun bend2/main.ts demos/parallel/knob.bend 2>/dev/null)
b=$(date +%s%N)
[ "$got" = "$(cat "$SMALL.oracle")" ] || { echo "MISMATCH interpreted: $got"; exit 1; }
printf '%s (%s bytes): %s in %d.%02d s, equal to the oracle\n' "$SMALL" "$(stat -c %s "$SMALL")" \
  "$got" $(((b - a) / 1000000000)) $(((b - a) / 10000000 % 100))
rm -rf "$OUT"
