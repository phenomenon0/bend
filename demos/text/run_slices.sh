#!/usr/bin/env bash
# The instant-slice tour over a ~256 MiB string. MIB=, N= override.
# The program clocks itself: load (read + decode, the only O(n) step), the
# tour, and N scattered slice+parse visits; /usr/bin/time adds wall and RSS.
. "$(dirname "$0")/_lib.sh"
REC=$CORPUS/records-${MIB:=256}.txt
[ -f "$REC" ] || python3 "$ROOT/demos/text/gen_records.py" "$REC" "$MIB"
build slices
echo "\$ FILE=$REC ($(du -h "$REC" | cut -f1)) N=${N:=1000000} slices"
FILE=$REC N=$N timed "$BIN/slices" --gpu off
