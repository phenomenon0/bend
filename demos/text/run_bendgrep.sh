#!/usr/bin/env bash
# bendgrep over a ~500 MiB synthetic log. MIB=, NEEDLE= override.
. "$(dirname "$0")/_lib.sh"
LOG=$CORPUS/app-${MIB:=500}.log NEEDLE=${NEEDLE:-ERROR}
[ -f "$LOG" ] || python3 "$ROOT/demos/text/gen_logs.py" "$LOG" "$MIB"
build bendgrep
echo "\$ FILE=$LOG ($(du -h "$LOG" | cut -f1)) NEEDLE=$NEEDLE bendgrep"
FILE=$LOG NEEDLE=$NEEDLE timed "$BIN/bendgrep" --gpu off
echo "  check: grep -c says $(grep -c -- "$NEEDLE" "$LOG")"
