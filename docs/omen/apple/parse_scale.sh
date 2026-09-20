#!/usr/bin/env bash
# The parcorpora thread sweep, macOS-portable: no `nproc`, no `date +%s%N`,
# no `timeout`. demos/parallel/_lib.sh's table with three substitutions --
# perl for the millisecond clock, sysctl for the core count, and manifests
# taken as given (gen_manifest.py needs a pinned CPython this host has not).
#   ROOT=~/bend-apple docs/omen/apple/parse_scale.sh
#   WRAP="/usr/sbin/taskpolicy -c utility" THREADS="8 20" ... same, E-leaning
# Every run is asserted byte-identical to the sequential run of its corpus.
set -euo pipefail
ROOT=${ROOT:-$(cd "$(dirname "$0")/../../.." && pwd)}
OUT=${OUT:-/tmp/bend-parcorpora}          # manifests in, binaries + output out
THREADS=${THREADS:-1 2 4 8 16 20 24 28}
RUNS=${RUNS:-5}                           # timed runs per row, after one warm
WRAP=${WRAP:-}                            # scheduler wrapper, e.g. taskpolicy
TAG=${TAG:-default}                       # names the .base file per wrapper
mkdir -p "$OUT"

now() { perl -MTime::HiRes=time -e 'printf "%.0f\n", time() * 1000'; }
median() { sort -n | sed -n "$(((RUNS + 1) / 2))p"; }

build() {
  if [ ! -x "$OUT/$1" ] || [ "$ROOT/demos/parallel/$1.bend" -nt "$OUT/$1" ]; then
    (cd "$ROOT" && bun bend2/main.ts "demos/parallel/$1.bend" -o "$OUT/$1")
  fi
}

once() { # once BIN MODE THREADS BASE
  PAR_MODE=$2 $WRAP "$1" --gpu off --threads "$3" >"$OUT/out" 2>"$OUT/err"
  [ -s "$4" ] || cp "$OUT/out" "$4"
  cmp -s "$OUT/out" "$4" ||
    { echo "MISMATCH: $2 --threads $3 does not print what the sequential run printed"; exit 1; }
}

table() { # table BIN NAME FILES BYTES
  local bin=$1 base="" rows=0 mode t w p
  printf '\n== %s: %s files, %s MB (wrap: %s) ==\n' "$2" "$3" \
    "$(awk -v b="$4" 'BEGIN{printf "%.1f", b/1048576}')" "${WRAP:-none}"
  printf '%5s %8s %8s %9s %8s %9s %8s\n' mode threads wall_s parse_s speedup files_s MB_s
  for row in seq $THREADS; do
    [ "$row" = seq ] && { mode=seq; t=1; } || { mode=par; t=$row; }
    once "$bin" "$mode" "$t" "$OUT/$2.$TAG.base"
    : >"$OUT/wall"; : >"$OUT/phase"
    for _ in $(seq "$RUNS"); do
      a=$(now); once "$bin" "$mode" "$t" "$OUT/$2.$TAG.base"; b=$(now)
      echo $((b - a)) >>"$OUT/wall"
      sed -n 's/.*parse \([0-9]*\) ms.*/\1/p' "$OUT/err" >>"$OUT/phase"
      rows=$((rows + 1))
    done
    w=$(median <"$OUT/wall"); p=$(median <"$OUT/phase")
    : "${base:=$w}"
    awk -v m="$mode" -v t="$t" -v w="$w" -v p="$p" -v bw="$base" -v f="$3" -v b="$4" \
      'BEGIN { printf "%5s %8d %8.2f %9.2f %7.2fx %9.1f %8.1f\n",
        m, t, w/1000, p/1000, bw/w, f/(w/1000), b/1048576/(w/1000) }'
  done
  printf '%s runs, every one byte-identical to the sequential run (%s)\n' \
    "$((rows + 1 + $(echo "$THREADS" | wc -w | tr -d ' ')))" "$(tail -1 "$OUT/$2.$TAG.base")"
}

build parse_corpus
printf 'box     %s hardware threads (%sP + %sE), load%s\n' \
  "$(sysctl -n hw.ncpu)" "$(sysctl -n hw.perflevel0.logicalcpu)" \
  "$(sysctl -n hw.perflevel1.logicalcpu)" "$(uptime | sed 's/.*average[s]*://')"
while read -r name files bytes path; do
  export PAR_MANIFEST=$path
  table "$OUT/parse_corpus" "$name" "$files" "$bytes"
  printf 'verdicts:%s\n' "$(sed '$d' "$OUT/$name.$TAG.base" | awk '{print $1}' |
    sort | uniq -c | awk '{printf " %s %s", $1, $2}')"
done <"$OUT/corpora.txt"
