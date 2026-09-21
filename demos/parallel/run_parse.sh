#!/usr/bin/env bash
# Three Python corpora parsed by demos/python's parser: one binary, run
# sequentially and as a fork/join tree at 1, 2, 4, 8, 16 threads. Every run is
# asserted byte-identical to the sequential one. Every number is measured here.
#   demos/parallel/run_parse.sh          # RUNS=5 THREADS="1 2 4 8 16"
. "$(dirname "$0")/_lib.sh"
build parse_corpus
printf 'box     %s hardware threads, load%s\n' "$(nproc)" "$(uptime | sed 's/.*average://')"
printf 'corpora (every non-test .py under the root that the pinned oracle'\''s\n'
printf '         intake accepts: real UTF-8, no symlink, at most 1 MiB)\n'
manifests | tee "$OUT/corpora.txt"

# The same tree, from the outside: for one file per corpus, the driver's line
# must be the FNV hash of the AST JSON that demos/python's own parser prints.
fnv() { python3 -c 'import sys
h = 2166136261
for c in sys.stdin.read().rstrip("\n"):
    for b in ord(c).to_bytes(4, "little"):
        h = ((h ^ b) * 16777619) & 0xFFFFFFFF
print(h)'; }

check() { # check NAME MANIFEST
  local f line got
  f=$(head -1 "$2"); line=$(head -1 "$OUT/$1.base")
  got="ok $(PY_SOURCE=$f "$OUT/parser" --gpu off | fnv) $f"
  [ "$line" = "$got" ] || { echo "MISMATCH against demos/python: $line != $got"; exit 1; }
  printf 'first file is the parser demo'"'"'s own AST: %s\n' "$line"
}

(cd "$ROOT" && bun bend2/main.ts demos/python/main.bend -o "$OUT/parser")
while read -r name files bytes path; do
  export PAR_MANIFEST=$path
  table "$OUT/parse_corpus" parse "$name" "$files" "$bytes"
  printf 'verdicts:%s\n' "$(sed '$d' "$OUT/$name.base" | awk '{print $1}' |
    sort | uniq -c | awk '{printf " %s %s", $1, $2}')"
  check "$name" "$path"
done <"$OUT/corpora.txt"
