#!/usr/bin/env bash
# Self-test, run before any full-size tour: a 4-block log (262,144 code
# points, 277 KB); every vignette program through the three lanes (CLI run,
# emitted JS, emitted C), stdout identical; the scans equal to gen_log.py's
# Python oracle; oops.bend rejected. Then the whole tour on that small log.
. "$(dirname "$0")/../text/_lib.sh"
cd "$ROOT"
T=demos/strings_tour
work=$(mktemp -d /tmp/bend-strings-tour-test.XXXXXX)
trap 'rm -rf -- "$work"' EXIT
LOG=$work/hostile-4.log
python3 $T/gen_log.py "$LOG" 4
fail=0
check() { # check PATH.bend ENV...: the three lanes agree on stdout
  local src=$1 name; shift; name=$(basename "$src" .bend)
  (bun bend2/main.ts "$src" -o "$work/$name.js" && bun bend2/main.ts "$src" -o "$work/$name") > /dev/null
  env "$@" bun bend2/main.ts "$src" > "$work/$name.cli" 2> /dev/null
  env "$@" bun "$work/$name.js" > "$work/$name.jsout" 2> /dev/null
  env "$@" "$work/$name" --gpu off > "$work/$name.c" 2> /dev/null
  if cmp -s "$work/$name.cli" "$work/$name.jsout" && cmp -s "$work/$name.cli" "$work/$name.c" \
    && [ -s "$work/$name.c" ]; then
    echo "ok   $name [cli = js = c]"
  else
    echo "FAIL $name"; fail=1
  fi
}
oracle() { # oracle NAME FILE: the C lane's stdout equals the Python oracle
  cmp -s "$work/$1.c" "$2" && echo "ok   $1 = python oracle $(cat "$2")" || { echo "FAIL $1 oracle"; fail=1; }
}
check $T/views.bend FILE="$LOG" N=200
check $T/codepoints.bend
check $T/fuel.bend FILE="$LOG"
check $T/viewcap.bend N=1000
check demos/text_stream/main.bend BEND_FILE="$LOG"
check demos/parallel/knob.bend KNOB_CORPUS="$LOG"; oracle knob "$LOG.oracle"
check demos/parallel/gputext.bend GPUTEXT_CORPUS="$LOG"; oracle gputext "$LOG.oracle_gpu"
bun bend2/main.ts $T/oops.bend > "$work/oops" 2>&1 && { echo "FAIL oops.bend compiled"; fail=1; } \
  || { grep -q "consumed more than once" "$work/oops" && echo "ok   oops.bend rejected: consumed more than once"; }
CORPUS=$work BIN=$work/bin BLOCKS=4 N=200 RUNS=1 $T/run_tour.sh > "$work/tour" 2>&1 \
  && echo "ok   run_tour.sh BLOCKS=4 plays all five" || { echo "FAIL run_tour.sh"; tail -5 "$work/tour"; fail=1; }
exit $fail
