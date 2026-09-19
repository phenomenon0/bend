#!/usr/bin/env bash
# md2html on this repo's README.md, then on a ~20 MiB generated document;
# each output is diffed against md2html.py, the independent Python oracle.
. "$(dirname "$0")/_lib.sh"
BIG=$CORPUS/big-${MIB:=20}.md
[ -f "$BIG" ] || python3 "$ROOT/demos/text/gen_markdown.py" "$BIG" "$MIB"
build md2html
for f in "$ROOT/README.md" "$BIG"; do
  html=$BIN/$(basename "$f" .md).html
  echo "\$ FILE=$f ($(du -h "$f" | cut -f1)) md2html > $html"
  FILE=$f timed "$BIN/md2html" --gpu off > "$html"
  echo "  $(grep -c '' "$html") lines of HTML; first heading: $(grep -m1 '<h[123]>' "$html")"
  python3 "$ROOT/demos/text/md2html.py" "$f" | cmp - "$html" \
    && echo "  check: byte-identical to the Python oracle"
done
