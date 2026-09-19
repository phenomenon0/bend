#!/usr/bin/env bash
# topwords over the system dictionary, then a ~200 MiB prose corpus. MIB= overrides.
. "$(dirname "$0")/_lib.sh"
DICT=/usr/share/dict/linux.words PROSE=$CORPUS/prose-${MIB:=200}.txt
[ -f "$PROSE" ] || python3 "$ROOT/demos/text/gen_corpus.py" "$PROSE" "$MIB" "$DICT"
build topwords
for f in "$DICT" "$PROSE"; do
  echo "\$ FILE=$f ($(du -h "$f" | cut -f1)) topwords"
  FILE=$f timed "$BIN/topwords" --gpu off
done
