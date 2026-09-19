#!/usr/bin/env bash
# The GPU lane: ONE binary of gputext.bend, run --gpu off (CPU, every core) and
# --gpu $GPU_MEM (the GPU), three runs each, median; both outputs asserted
# byte-identical and equal to the Python oracle. While the GPU run is live,
# nvidia-smi is sampled for this process and for the GPU's utilization. Every
# number printed is measured by this run; the point is "same source, no CUDA
# written", not a throughput claim.
#   SIZES="256 1024 4096" (blocks of 65536 code points)  GPU_MEM=4GB  RUNS=3
set -euo pipefail
cd "$(dirname "$0")/../.."
DIR=${CORPUS_DIR:-$HOME/videokit-corpus}
SIZES=${SIZES:-256 1024 4096}
GPU_MEM=${GPU_MEM:-4GB}
RUNS=${RUNS:-3}
OUT=$(mktemp -d /tmp/gputext.XXXXXX)
mkdir -p "$DIR"

median() { sort -n | sed -n "$(((RUNS + 1) / 2))p"; }

lane() { # label, flags... -> sets $got, prints a row
  local label=$1
  shift
  : >"$OUT/wall"; : >"$OUT/scan"
  for _ in $(seq "$RUNS"); do
    a=$(date +%s%N)
    got=$("$OUT/gputext" "$@" 2>"$OUT/err") || { cat "$OUT/err"; exit 1; }
    b=$(date +%s%N)
    [ "$got" = "$want" ] || { echo "MISMATCH [$label]: $got != $want"; exit 1; }
    echo $(((b - a) / 1000000)) >>"$OUT/wall"
    sed -n 's/.*scan \([0-9]*\) ms.*/\1/p' "$OUT/err" >>"$OUT/scan"
  done
  awk -v l="$label" -v w="$(median <"$OUT/wall")" -v s="$(median <"$OUT/scan")" -v o="$got" \
    'BEGIN { printf "%-14s %8.2f %8.2f  %s\n", l, w/1000, s/1000, o }'
}

echo "== compile once: the C binary and its GPU program, from one source =="
bun bend2/main.ts demos/parallel/gputext.bend -o "$OUT/gputext"
ls -l "$OUT" | awk 'NR > 1 { printf "  %-12s %8d bytes\n", $NF, $5 }'
nvidia-smi --query-gpu=name,memory.total --format=csv,noheader

for n in $SIZES; do
  f=$DIR/knob-$n.txt
  [ -f "$f" ] && [ -f "$f.oracle_gpu" ] || python3 demos/parallel/gen_corpus.py "$f" "$n" >/dev/null
  want=$(cat "$f.oracle_gpu")
  export GPUTEXT_CORPUS=$f
  printf '\n== %s blocks, %s bytes; oracle %s (tokens:checksum:"gpu" occurrences) ==\n' \
    "$n" "$(stat -c %s "$f")" "$want"
  printf '%-14s %8s %8s  %s\n' lane wall_s scan_s output
  lane "--gpu off" --gpu off
  "$OUT/gputext" --gpu "$GPU_MEM" >/dev/null 2>&1 || true # untimed warm run (context + kernel load)
  lane "--gpu $GPU_MEM" --gpu "$GPU_MEM"
done
echo; echo "all outputs byte-identical across lanes and equal to the oracle"

echo; echo "== evidence the GPU ran it: nvidia-smi sampled during one more GPU run =="
"$OUT/gputext" --gpu "$GPU_MEM" >/dev/null 2>&1 &
pid=$!
while kill -0 $pid 2>/dev/null; do
  nvidia-smi --query-compute-apps=pid,used_memory --format=csv,noheader | grep "^$pid," >>"$OUT/apps" || true
  nvidia-smi --query-gpu=utilization.gpu --format=csv,noheader,nounits >>"$OUT/util"
  sleep 0.2
done
wait $pid
echo "compute app: pid $(sort -u "$OUT/apps" | head -1)"
echo "peak GPU utilization while it ran: $(sort -n "$OUT/util" | tail -1) %"
rm -rf "$OUT"
