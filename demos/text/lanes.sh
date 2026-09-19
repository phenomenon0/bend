#!/usr/bin/env bash
# Self-test: every demo on a small input through the three lanes of
# tests/strings/run.sh (CLI run, emitted JS, emitted C); stdout must be
# identical across lanes, and match the independent checks (grep, md2html.py).
. "$(dirname "$0")/_lib.sh"
work=$(mktemp -d /tmp/bend-text-lanes.XXXXXX)
trap 'rm -rf -- "$work"' EXIT
python3 "$ROOT/demos/text/gen_logs.py" "$work/app.log" 1 > /dev/null
python3 "$ROOT/demos/text/gen_corpus.py" "$work/prose1.txt" 1 > /dev/null
# 300 KB: the JS lane recurses on the machine stack and overflows while
# ranking ~30k unique words (1 MiB); C has no such limit
head -c 300000 "$work/prose1.txt" > "$work/prose.txt"
python3 "$ROOT/demos/text/gen_records.py" "$work/records.txt" 1 > /dev/null
python3 "$ROOT/demos/text/gen_markdown.py" "$work/big.md" 1 > /dev/null
fail=0
check() { # check NAME ENV...: the three lanes agree on stdout
  local name=$1; shift
  (cd "$ROOT" && bun bend2/main.ts "demos/text/$name.bend" -o "$work/$name.js" \
    && bun bend2/main.ts "demos/text/$name.bend" -o "$work/$name") > /dev/null
  (cd "$ROOT" && env "$@" bun bend2/main.ts "demos/text/$name.bend") > "$work/$name.cli" 2> /dev/null
  env "$@" bun "$work/$name.js" > "$work/$name.jsout" 2> /dev/null
  env "$@" "$work/$name" --gpu off > "$work/$name.c" 2> /dev/null
  if cmp -s "$work/$name.cli" "$work/$name.jsout" && cmp -s "$work/$name.cli" "$work/$name.c" \
    && [ -s "$work/$name.c" ]; then
    echo "ok   $name [cli = js = c] $*" | sed "s|$work/||g"
  else
    echo "FAIL $name $*"; fail=1
  fi
}
check md2html FILE="$ROOT/README.md"
python3 "$ROOT/demos/text/md2html.py" "$ROOT/README.md" | cmp -s - "$work/md2html.c" \
  && echo "ok   md2html README.md = md2html.py" || { echo "FAIL md2html oracle"; fail=1; }
check md2html FILE="$work/big.md"
python3 "$ROOT/demos/text/md2html.py" "$work/big.md" | cmp -s - "$work/md2html.c" \
  && echo "ok   md2html big.md = md2html.py" || { echo "FAIL md2html oracle"; fail=1; }
check topwords FILE="$work/prose.txt"
python3 - "$work/prose.txt" <<'PY' | cmp -s - "$work/topwords.c" \
  && echo "ok   topwords = collections.Counter" || { echo "FAIL topwords oracle"; fail=1; }
import collections, re, sys
text = open(sys.argv[1]).read().lower().replace(".", " ").replace(",", " ")
c = collections.Counter(re.findall(r"[^ \t-\r]+", text))
print(f"total words:  {sum(c.values())}\nunique words: {len(c)}")
for i, (w, n) in enumerate(sorted(c.items(), key=lambda kv: (-kv[1], kv[0]))[:20], 1):
    print(f"{i:>2}. {w:<16}{n:>10}")
PY
check bendgrep FILE="$work/app.log" NEEDLE=ERROR
[ "$(tail -1 "$work/bendgrep.c")" = "$(grep -c ERROR "$work/app.log") matching lines of $(grep -c '' "$work/app.log")" ] \
  && echo "ok   bendgrep counts = grep -c" || { echo "FAIL bendgrep vs grep"; fail=1; }
check slices FILE="$work/records.txt" N=200
exit $fail
