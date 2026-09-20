#!/usr/bin/env bash
# Real watts around one fixed command. Nothing here estimates: if the sampler
# cannot run, the script says so and exits 77 rather than print a number.
#
#   docs/omen/apple/measure_watts.sh parse-20 -- ./parse_corpus --threads 20
#
# macOS samples /usr/bin/powermetrics (--samplers cpu_power), Linux samples
# /usr/sbin/turbostat (--show PkgWatt). Both need root and neither is granted
# by default; the one-time grant is one line, and only for the sampler:
#   mac:   echo "$USER ALL=(ALL) NOPASSWD: /usr/bin/powermetrics" | sudo tee /etc/sudoers.d/powermetrics && sudo chmod 440 /etc/sudoers.d/powermetrics
#   linux: echo "$USER ALL=(ALL) NOPASSWD: /usr/sbin/turbostat"   | sudo tee /etc/sudoers.d/turbostat   && sudo chmod 440 /etc/sudoers.d/turbostat
#
# Every `<name> Power: N mW` row powermetrics prints is reported: samples,
# mean mW, peak mW, and mean x wall = joules. The command's own stdout goes
# to $OUT/<label>.out so the rows stay machine-readable.
set -uo pipefail
MS=${MS:-200}                       # sampling interval, milliseconds
OUT=${OUT:-/tmp/bend-watts}
label=${1:?usage: measure_watts.sh LABEL -- CMD...}
shift
[ "${1:-}" = "--" ] && shift
[ $# -gt 0 ] || { echo "usage: measure_watts.sh LABEL -- CMD..." >&2; exit 2; }
mkdir -p "$OUT"
raw=$OUT/$label.samples

case $(uname) in
  Darwin) sampler=(/usr/bin/powermetrics -i "$MS" --samplers cpu_power) ;;
  Linux)  sampler=(/usr/sbin/turbostat --show PkgWatt,CorWatt --interval 1) ;;
  *) echo "no sampler for $(uname)" >&2; exit 77 ;;
esac
[ -x "${sampler[0]}" ] || { echo "sampler missing: ${sampler[0]}" >&2; exit 77; }
if ! sudo -n true 2>/dev/null; then
  echo "WATTS UNAVAILABLE pending one-time sudo grant: sudo -n needs a password" >&2
  echo "  grant: see the header of $0" >&2
  exit 77
fi

sudo -n "${sampler[@]}" >"$raw" 2>"$OUT/$label.sampler.err" &
pm=$!
sleep 1                                                    # let a sample land
start=$(perl -MTime::HiRes=time -e 'printf "%.3f\n", time()')
"$@" >"$OUT/$label.out" 2>"$OUT/$label.err"
rc=$?
wall=$(perl -MTime::HiRes=time -e 'printf "%.3f\n", time() - '"$start")
sudo -n kill "$pm" 2>/dev/null
wait "$pm" 2>/dev/null

[ -s "$raw" ] || { echo "sampler produced nothing: $OUT/$label.sampler.err" >&2; exit 77; }
printf '%s: rc=%s wall=%ss, %s interval %s ms\n' \
  "$label" "$rc" "$wall" "$(basename "${sampler[0]}")" "$MS"
awk -v wall="$wall" '
  /^[A-Za-z][A-Za-z0-9 /_-]* Power: *[0-9.]+ *mW/ {                 # powermetrics
    split($0, kv, ":"); key = kv[1]; v = kv[2] + 0
    n[key]++; s[key] += v; if (v > p[key]) p[key] = v; next }
  /^[0-9.]+([ \t]+[0-9.]+)*$/ {                                     # turbostat
    for (i = 1; i <= NF; i++) { key = "col" i; n[key]++; s[key] += $i * 1000
      if ($i * 1000 > p[key]) p[key] = $i * 1000 } }
  END {
    printf "%-22s %8s %10s %10s %10s\n", "rail", "samples", "mean_W", "peak_W", "joules"
    for (k in n) printf "%-22s %8d %10.2f %10.2f %10.1f\n",
      k, n[k], s[k]/n[k]/1000, p[k]/1000, s[k]/n[k]/1000 * wall }
' "$raw" | sort
exit $rc
