#!/usr/bin/env bash
# The strings tour: five vignettes over ONE generated hostile log, played in
# order. Every number printed is measured by this run, except lines tagged
# [record <date>], which quote a dated lane report. Footnotes (`  ^ ...`) are
# one-line illustrations from Python or JS, also run live.
#   BLOCKS=4096   log size, x 65,536 code points (a power of two; 4096 = ~283 MB)
#   N=1000000     scattered visits      THREADS="1 4 16"  RUNS=3
#   SHARED=1      vignette 4 also runs the variant that does NOT scale
#   GPU=1         the appendix: the same scan through the `!` GPU lane (GPU_MEM=8GB; 4GB is out of memory at 4096 blocks)
#   ONLY="1 3"    play only these vignettes
BIN=${BIN:-/tmp/bend-strings-tour}
. "$(dirname "$0")/../text/_lib.sh" # ROOT, CORPUS, timed
cd "$ROOT"
T=demos/strings_tour
BLOCKS=${BLOCKS:-4096} N=${N:-1000000} THREADS=${THREADS:-1 4 16} RUNS=${RUNS:-3}
LOG=$CORPUS/hostile-$BLOCKS.log
[ -f "$LOG.oracle_gpu" ] || python3 $T/gen_log.py "$LOG" "$BLOCKS"
build() { # build PATH.bend -> $BIN/NAME when stale
  local out=$BIN/$(basename "$1" .bend)
  if [ ! -x "$out" ] || [ "$1" -nt "$out" ]; then bun bend2/main.ts "$1" -o "$out"; fi
}
on() { case " ${ONLY:-1 2 3 4 5} " in *" $1 "*) printf '\n== %s ==\n' "$2" ;; *) return 1 ;; esac; }
note() { printf '  ^ %s\n' "$*"; }
median() { sort -n | sed -n "$(((RUNS + 1) / 2))p"; }
echo "log $LOG: $(stat -c %s "$LOG") bytes, $((BLOCKS * 65536)) code points"
echo "under load: load average $(cut -d' ' -f1-3 /proc/loadavg) on $(nproc) threads"

if on 1 "1. READ ONCE, VIEW FOREVER"; then
  build demos/text_stream/main.bend; build $T/views.bend
  echo "\$ stream: File.read_text, 64 KiB chunks, nothing kept between chunks"
  BEND_FILE=$LOG timed "$BIN/main" --gpu off --threads 1
  awk '/Maximum resident/ { print "  => that is " $NF " KiB for a '"$(stat -c %s "$LOG")"'-byte file" }' "$BIN/time.txt"
  echo "  [record 2026-09-18, lane-stream] 2.7 MiB streaming a 256 MiB file; whole-file ASCII RSS 2.03x the input at 64 MiB against a 1.5x target: a miss"
  echo "\$ views: one File.read, then every line and $N scattered stamps are views"
  FILE=$LOG N=$N timed "$BIN/views" --gpu off
fi

if on 2 "2. CODE POINTS ARE THE UNIT"; then
  build $T/codepoints.bend
  mapfile -t fn < <(
    bun -e 'const s = "A😀é", u = (x) => [...x].map((c) => c.codePointAt(0).toString(16)).join(" ");
      console.log(`JS: "A😀é".length = ${s.length} (UTF-16 units)`);
      console.log(`JS: split("").reverse().join("") = code units ${u(s.split("").reverse().join(""))}: 😀 torn into lone surrogates`);
      console.log(`JS: "\\ue000" < "😀" = ${String.fromCodePoint(0xe000) < "😀"} (UTF-16 order flips for astral characters)`);'
    python3 -c 'print("Python: upper =", "éßıa".upper(), "(Python has the full Unicode case tables; Bend is ASCII-only here)")
print("Python: len(strip) =", len((chr(0xa0) + "x" + chr(0xa0)).strip()), "(Python trims Unicode spaces; Bend trims ASCII only)")
print("Python: len(\"e\\u0301\") =", len("e" + chr(0x301)), "too: a code point is not a grapheme, in either")'
  )
  i=0
  "$BIN/codepoints" --gpu off | while IFS= read -r row; do echo "$row"; note "${fn[i]}"; i=$((i + 1)); done
fi

if on 3 "3. THE FUEL GAUGE"; then
  build $T/fuel.bend
  FILE=$LOG "$BIN/fuel" --gpu off
  note "$(python3 -c 'import re, time
def t(n):
    a = time.perf_counter(); re.match(r"^(a+)+$", "a" * n + "!"); return time.perf_counter() - a
print("Python re, same pattern, only the first 22 / 24 / 26 of those a: %.2f / %.2f / %.2f s; a backtracking engine doubles per character, unbounded" % (t(22), t(24), t(26)))')"
  echo "  [record 2026-09-18, 8f782000] find_all on a 26 KB text, C, one thread: 14.2 s -> 0.02 s, same answer"
fi

knob() { # knob BINARY: the --threads table, outputs asserted equal to the oracle
  printf '%8s %9s %8s  %s\n' threads scan_s speedup output
  local base=""
  for t in $THREADS; do
    : >"$BIN/scan"
    for _ in $(seq "$RUNS"); do
      got=$(KNOB_CORPUS=$LOG "$1" --gpu off --threads "$t" 2>"$BIN/err")
      [ "$got" = "$(cat "$LOG.oracle")" ] || { echo "MISMATCH at --threads $t: $got"; exit 1; }
      sed -n 's/.*scan \([0-9]*\) ms.*/\1/p' "$BIN/err" >>"$BIN/scan"
    done
    s=$(median <"$BIN/scan"); : "${base:=$s}"
    awk -v t="$t" -v s="$s" -v b="$base" -v o="$got" 'BEGIN { printf "%8d %9.2f %7.2fx  %s\n", t, s/1000, b/s, o }'
  done
}
if on 4 "4. ONE LINE OF THREAD CODE"; then
  build demos/parallel/knob.bend
  grep -n 'a b = scan' demos/parallel/knob.bend
  echo "one binary, median of $RUNS, scan phase (the fork/join tree; the read is serial):"
  knob "$BIN/knob"
  echo "every output byte-identical and equal to the Python oracle $(cat "$LOG.oracle")"
  if [ "${SHARED:-0}" = 1 ]; then
    echo "-- SHARED=1: without the leaf copy, every core counts references on ONE payload --"
    sed 's/String.lines(String.copy(s))/String.lines(s)/' demos/parallel/knob.bend >"$BIN/knob_shared.bend"
    bun bend2/main.ts "$BIN/knob_shared.bend" -o "$BIN/knob_shared"
    knob "$BIN/knob_shared"
  fi
fi

if on 5 "5. THE COMPILER CATCHES IT"; then
  build $T/viewcap.bend
  echo "\$ bun bend2/main.ts $T/oops.bend"
  if bun bend2/main.ts $T/oops.bend 2>&1; then echo "FAIL: oops.bend compiled"; exit 1; fi
  echo "(rejected at compile time, exit 1: nothing ran)"
  echo "\$ N=16000000 viewcap ; N=17000000 viewcap   (the limit is 2^24 - 1 = 16777215)"
  N=16000000 "$BIN/viewcap" --gpu off
  if N=17000000 "$BIN/viewcap" --gpu off 2>&1; then echo "FAIL: no fail-stop"; exit 1; fi
  echo "(fail-stop, exit 1: loud, never a wrong count)"
fi

if [ "${GPU:-0}" = 1 ]; then
  printf '\n== APPENDIX. THE ! GPU LANE ==\n'
  build demos/parallel/gputext.bend
  grep -n 'scan!' demos/parallel/gputext.bend
  GPUTEXT_CORPUS=$LOG "$BIN/gputext" --gpu "${GPU_MEM:=8GB}" >/dev/null 2>&1 || true # untimed warm run
  for lane in off "$GPU_MEM"; do
    got=$(GPUTEXT_CORPUS=$LOG "$BIN/gputext" --gpu "$lane" 2>"$BIN/err") || { cat "$BIN/err"; exit 1; }
    [ "$got" = "$(cat "$LOG.oracle_gpu")" ] || { echo "MISMATCH --gpu $lane: $got"; exit 1; }
    printf '%-10s %s  %s\n' "--gpu $lane" "$got" "$(cat "$BIN/err")"
  done
  echo "same source, same bytes, equal to the Python oracle; slower here, and said so"
fi
