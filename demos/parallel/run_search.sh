#!/usr/bin/env bash
# The same corpora searched for a literal needle: one binary, run sequentially
# and as a fork/join tree at 1, 2, 4, 8, 16 threads, every run asserted
# byte-identical to the sequential one. grep -c counts the same lines, so a
# plain grep over the same list is the outside baseline.
#   NEEDLE=import demos/parallel/run_search.sh      # RUNS=5 REPEAT=8
. "$(dirname "$0")/_lib.sh"
build search_corpus
export PAR_NEEDLE=${NEEDLE:-import}
REPEAT=${REPEAT:-8}
printf 'box     %s hardware threads, load%s\nneedle  %s\n' \
  "$(nproc)" "$(uptime | sed 's/.*average://')" "$PAR_NEEDLE"
manifests >"$OUT/corpora.txt"
cat "$OUT/numpy.txt" "$OUT/pandas.txt" "$OUT/stdlib.txt" >"$OUT/all.txt"
# the same list REPEAT times: a corpus this scan can measure, every copy read
# and searched on its own (the page cache is warm, so `read` is a floor)
for _ in $(seq "$REPEAT"); do cat "$OUT/all.txt"; done >"$OUT/all$REPEAT.txt"
files=$(wc -l <"$OUT/all.txt"); bytes=$(awk '{b+=$3} END {print b}' "$OUT/corpora.txt")
printf 'corpora all = numpy + pandas + stdlib\n'

for name in all "all$REPEAT"; do
  [ "$name" = all ] && k=1 || k=$REPEAT
  export PAR_MANIFEST=$OUT/$name.txt
  table "$OUT/search_corpus" search "$name" "$((files * k))" "$((bytes * k))"
  : >"$OUT/greps"
  for _ in $(seq "$RUNS"); do
    a=$(date +%s%N)
    got=$(tr '\n' '\0' <"$OUT/$name.txt" | xargs -0 grep -c -- "$PAR_NEEDLE" |
      awk -F: '{s += $NF} END {print s}')
    b=$(date +%s%N)
    echo $(((b - a) / 1000000)) >>"$OUT/greps"
  done
  printf 'outside baseline, same file list, same machine: grep -c %s\n' \
    "$(awk -v w="$(median <"$OUT/greps")" -v n="$got" \
      'BEGIN {printf "counts %d matching lines in %.2f s (one process, no parallel mode)", n, w/1000}')"
done
