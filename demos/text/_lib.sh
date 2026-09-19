# Shared by run_*.sh: paths, build-if-stale, and a /usr/bin/time -v wrapper.
set -euo pipefail
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
CORPUS=${CORPUS:-$HOME/videokit-corpus}   # generated inputs; never committed
BIN=${BIN:-/tmp/bend-text-demos}          # compiled demos
mkdir -p "$CORPUS" "$BIN"

build() { # build NAME: demos/text/NAME.bend -> $BIN/NAME (C lane)
  if [ ! -x "$BIN/$1" ] || [ "$ROOT/demos/text/$1.bend" -nt "$BIN/$1" ]; then
    (cd "$ROOT" && bun bend2/main.ts "demos/text/$1.bend" -o "$BIN/$1")
  fi
}

timed() { # timed CMD...: run it, then print measured wall time and peak RSS
  /usr/bin/time -v -o "$BIN/time.txt" "$@"
  awk -F': ' '/Elapsed/ {w=$2} /Maximum resident/ {r=$2}
    END {printf "  => wall %s, peak RSS %.0f MB\n", w, r/1024}' "$BIN/time.txt" >&2
}
