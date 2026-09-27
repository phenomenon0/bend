#!/usr/bin/env bash
# C3 receipt: the tensor rows built strict vs BEND_REASSOC=1, beside the C twin
# strict, with the same reassociation permission (RA), and the plan's fast-math
# row (-march=native -ffast-math). bench.sh's protocol: the lock, medians of three.
# Under the flag the checksum is ALLOWED to leave the strict twin's; the row
# records whether it did, and still requires 1T == 16T and no inf/NaN.
set -u
cd "$(dirname "$0")/.."
export BEND_NO_TELEMETRY=1
here=demos/tensor
work=$(mktemp -d); trap 'rm -rf "$work"' EXIT
exec 9>/tmp/bend-bench.lock; flock 9
RA="-fassociative-math -fno-signed-zeros -fno-trapping-math"
clang -std=c11 -O3 -o "$work/tw" $here/twin.c -lm
clang -std=c11 -O3 $RA -o "$work/twra" $here/twin.c -lm
clang -std=c11 -O3 -march=native -ffast-math -o "$work/twff" $here/twin.c -lm
med() { for _ in 1 2 3; do s=$(date +%s.%N); "$@" > /dev/null; e=$(date +%s.%N); echo "$e - $s" | bc; done | sort -n | sed -n 2p; }
printf 'load %s\n' "$(cut -d' ' -f1-3 /proc/loadavg)"
printf '%-8s %7s %7s %7s | %7s %7s %7s | %s\n' bench C Cra Cff b1T bRA1T bRA16T "RA checksum vs strict twin"
for name in gemv split blocked; do
  case $name in blocked) arg=blocked ;; *) arg=gemv ;; esac
  bun bend2/main.ts $here/bench_$name.bend -o "$work/s_$name" > /dev/null
  BEND_REASSOC=1 bun bend2/main.ts $here/bench_$name.bend -o "$work/r_$name" > /dev/null
  want=$("$work/tw" $arg | head -1)
  r1=$("$work/r_$name" --gpu off --threads 1); r16=$("$work/r_$name" --gpu off --threads 16)
  [ "$r1" = "$r16" ] || echo "NOTE $name: RA 1T and 16T disagree"
  [ "$(echo "$r1" | sed -n 4p)" = 0 ] || echo "FAIL $name: non-finite under RA"
  got=$(echo "$r1" | head -1)
  [ "$got" = "$want" ] && same="same ($got)" || same="differs: $got vs $want"
  printf '%-8s %7.3f %7.3f %7.3f | %7.3f %7.3f %7.3f | %s\n' $name \
    "$(med "$work/tw" $arg)" "$(med "$work/twra" $arg)" "$(med "$work/twff" $arg)" \
    "$(med "$work/s_$name" --gpu off --threads 1)" \
    "$(med "$work/r_$name" --gpu off --threads 1)" \
    "$(med "$work/r_$name" --gpu off --threads 16)" "$same"
done
bun bend2/main.ts receipts/c3_harmonic.bend -o "$work/hs" > /dev/null
BEND_REASSOC=1 bun bend2/main.ts receipts/c3_harmonic.bend -o "$work/hr" > /dev/null
printf 'harmonic strict %s bits %s s | RA %s bits %s s\n' \
  "$("$work/hs" --gpu off --threads 1)" "$(med "$work/hs" --gpu off --threads 1)" \
  "$("$work/hr" --gpu off --threads 1)" "$(med "$work/hr" --gpu off --threads 1)"
