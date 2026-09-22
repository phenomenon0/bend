#!/bin/bash
# The differential run: every file bend.ts accepts, exported and re-checked
# by the kernel. Usage: kernel/corpus.sh <out-dir> [file.bend ..]; with no
# files, the corpus: tests/**, demos/*/PROOF.bend, bench/checker/*/main.bend.
# Writes <out-dir>/results.tsv (file, bend verdict, kernel verdict) and
# prints the counts; each file's kernel report is <out-dir>/<file>.k.txt.
set -u
ROOT=$(cd "$(dirname "$0")/.." && pwd)
OUT=$(mkdir -p "$1" && cd "$1" && pwd)
shift
cargo build --quiet --release --manifest-path "$ROOT/kernel/Cargo.toml" || exit 2
KERNEL="$ROOT/kernel/target/release/bend-kernel"
cd "$ROOT"
if [ $# -eq 0 ]; then
  set -- $(ls tests/*/*.bend tests/*.bend demos/*/PROOF.bend bench/checker/*/main.bend 2>/dev/null)
fi
one() {
  f=$1; n=$(echo "$f" | tr '/' '_')
  if ! timeout 600 bun "$ROOT/bend2/main.ts" "$f" --export "$OUT/$n.core" > "$OUT/$n.bend.txt" 2>&1; then
    printf '%s\tbend-rejects\t-\n' "$f"
    return
  fi
  timeout 600 "$KERNEL" -q "$OUT/$n.core" > "$OUT/$n.k.txt" 2>&1
  case $? in
    0) v=pass ;;
    1) if grep -q '^REJECT [^[]*:' "$OUT/$n.k.txt"; then v=reject
       elif grep -q '^UNSUPPORTED [^[]*:' "$OUT/$n.k.txt"; then v=unsupported
       else v=leans-on-refused-base; fi ;;
    *) v=crash ;;
  esac
  printf '%s\tbend-accepts\t%s\n' "$f" "$v"
  rm -f "$OUT/$n.core"
}
export -f one
export ROOT OUT KERNEL
printf '%s\n' "$@" | xargs -P "$(nproc)" -I{} bash -c 'one {}' > "$OUT/results.tsv"
sort -o "$OUT/results.tsv" "$OUT/results.tsv"
echo "files: $(wc -l < "$OUT/results.tsv")"
cut -f2,3 "$OUT/results.tsv" | sort | uniq -c
