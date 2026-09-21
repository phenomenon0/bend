# Shared by run_parse.sh and run_search.sh: paths, the build, the corpora, and
# the threads table with its identical-output assertion.
set -euo pipefail
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
OUT=${OUT:-/tmp/bend-parcorpora}     # manifests, binaries, run output
THREADS=${THREADS:-1 2 4 8 16}
RUNS=${RUNS:-5}                      # timed runs per row, after one warm run
mkdir -p "$OUT"

build() { # build NAME: demos/parallel/NAME.bend -> $OUT/NAME (C lane), once
  if [ ! -x "$OUT/$1" ] || [ "$ROOT/demos/parallel/$1.bend" -nt "$OUT/$1" ]; then
    (cd "$ROOT" && bun bend2/main.ts "demos/parallel/$1.bend" -o "$OUT/$1")
  fi
}

manifests() { # $OUT/<name>.txt per corpus; prints `name files bytes path`
  python3 "$ROOT/demos/parallel/gen_manifest.py" "$OUT"
}

median() { sort -n | sed -n "$(((RUNS + 1) / 2))p"; }

once() { # once BIN MODE THREADS BASE: run, then assert the output has not moved
  PAR_MODE=$2 "$1" --gpu off --threads "$3" >"$OUT/out" 2>"$OUT/err"
  [ -s "$4" ] || cp "$OUT/out" "$4"
  cmp -s "$OUT/out" "$4" ||
    { echo "MISMATCH: $2 --threads $3 does not print what the sequential run printed"; exit 1; }
}

table() { # table BIN PHASE NAME FILES BYTES; PAR_MANIFEST etc exported by the caller
  local bin=$1 phase=$2 base="" rows=0
  printf '\n== %s: %s files, %s MB ==\n' "$3" "$4" "$(awk -v b="$5" 'BEGIN{printf "%.1f", b/1048576}')"
  printf '%5s %8s %8s %9s %8s %9s %8s\n' mode threads wall_s "$phase"_s speedup files_s MB_s
  for row in seq $THREADS; do
    [ "$row" = seq ] && { mode=seq; t=1; } || { mode=par; t=$row; }
    once "$bin" "$mode" "$t" "$OUT/$3.base"
    : >"$OUT/wall"; : >"$OUT/phase"
    for _ in $(seq "$RUNS"); do
      a=$(date +%s%N)
      once "$bin" "$mode" "$t" "$OUT/$3.base"
      b=$(date +%s%N)
      echo $(((b - a) / 1000000)) >>"$OUT/wall"
      sed -n "s/.*$phase \([0-9]*\) ms.*/\1/p" "$OUT/err" >>"$OUT/phase"
      rows=$((rows + 1))
    done
    w=$(median <"$OUT/wall"); p=$(median <"$OUT/phase")
    : "${base:=$w}"
    awk -v m="$mode" -v t="$t" -v w="$w" -v p="$p" -v bw="$base" -v f="$4" -v b="$5" \
      'BEGIN { printf "%5s %8d %8.2f %9.2f %7.2fx %9.1f %8.1f\n",
        m, t, w/1000, p/1000, bw/w, f/(w/1000), b/1048576/(w/1000) }'
  done
  printf '%s runs, every one byte-identical to the sequential run (%s)\n' \
    "$((rows + 1 + $(echo "$THREADS" | wc -w)))" "$(tail -1 "$OUT/$3.base")"
}
