#!/usr/bin/env bash
# `demos/monoids/real.sh [DEEP_DIVES_DIR]`: the power/ primitives on real data.
#
# utf8   the deep dives' own HTML (real mixed-script UTF-8, emoji included),
#        concatenated and repeated to about 55 MB; then the same bytes with one
#        byte deep inside overwritten by 0xFF. The verdict is compared with
#        CPython's bytes.decode on the same file.
# exact  2^24 little-endian float32s written by Python (giants in cancelling
#        pairs over a sea of small values); the bits are compared with the exact
#        integer sum rounded to the nearest F32 by exact comparison. The naive
#        sequential float32 sum is printed beside it.
# Each Bend binary runs at 1 and 4 threads; the output must not change.
set -euo pipefail
cd "$(dirname "$0")/../.."
DD=${1:-../deep-dives}
work=$(mktemp -d /tmp/bend-real.XXXXXX)
trap 'rm -rf -- "$work"' EXIT
export BEND_NO_TELEMETRY=1

bun bend2/main.ts demos/monoids/real_utf8.bend -o "$work/real_utf8" > /dev/null 2>&1
bun bend2/main.ts demos/monoids/real_exact.bend -o "$work/real_exact" > /dev/null 2>&1

python3 - "$DD" "$work" <<'PY'
import glob, os, struct, sys
dd, work = sys.argv[1], sys.argv[2]
src = b"".join(open(p, "rb").read() for p in sorted(glob.glob(os.path.join(dd, "*.html"))))
data = src * 8
open(f"{work}/good.txt", "wb").write(data)
bad = bytearray(data); bad[len(bad) * 5 // 7] = 0xFF
open(f"{work}/bad.txt", "wb").write(bytes(bad))
M = 0xFFFFFFFF
def key(i):
    x = (((i + 1) * 2654435761) & M) ^ (i >> 3)
    x = ((x ^ (x >> 15)) * 2246822519) & M
    return x ^ (x >> 13)
def val(i):
    if i % 64 == 32: return val(i - 32) ^ 0x80000000
    r = key(i)
    if i % 64 == 0: return ((187 + (r & 15)) << 23) | (r >> 9)
    e = 0 if i % 61 == 0 else 87 + (r & 31)
    return ((r >> 31) << 31) | (e << 23) | ((r >> 8) & 0x7FFFFF)
xs = [val(i) for i in range(1 << 24)]
open(f"{work}/floats.bin", "wb").write(struct.pack("<%dI" % len(xs), *xs))
PY

oracle() { # the file's verdict, from CPython
  python3 - "$1" <<'PY'
import sys
d = open(sys.argv[1], "rb").read()
try:
    s = d.decode("utf-8"); print("valid=yes scalars=%d first_bad=-" % len(s))
except UnicodeDecodeError as e:
    dead = {"invalid start byte": e.start, "invalid continuation byte": e.end,
            "unexpected end of data": len(d)}[e.reason]
    print("valid=no scalars=%d first_bad=%d" % (sum(1 for b in d if b & 0xC0 != 0x80), dead))
PY
}

for f in good bad; do
  want=$(oracle "$work/$f.txt")
  for t in 1 4; do
    got=$("$work/real_utf8" "$work/$f.txt" --threads $t 2> "$work/err")
    [ "$got" = "$want" ] && ok=ok || ok=FAIL
    printf 'utf8  %-4s %s bytes  threads=%s  %s  [%s]  %s\n' "$f" "$(stat -c %s "$work/$f.txt")" "$t" "$got" "$ok" "$(tr '\n' ' ' < "$work/err")"
  done
done

want=$(python3 - "$work/floats.bin" <<'PY'
import struct, sys
from fractions import Fraction
d = open(sys.argv[1], "rb").read(); n = len(d) // 4
ws = struct.unpack("<%dI" % n, d)
tot = 0                      # the exact sum in units of 2^-149
for w in ws:
    e = (w >> 23) & 255; m = (w & 0x7FFFFF) | ((e != 0) << 23)
    v = m << (max(e, 1) - 1)
    tot += -v if w >> 31 else v
r = Fraction(tot, 2 ** 149)
f = lambda b: struct.unpack("<f", struct.pack("<I", b))[0]
g = struct.unpack("<I", struct.pack("<f", float(r)))[0]
best = min({g - 1, g, g + 1}, key=lambda b: (abs(Fraction(f(b)) - r), b & 1))
acc = 0.0                    # naive float32, left to right
for x in struct.unpack("<%df" % n, d):
    acc = struct.unpack("<f", struct.pack("<f", acc + x))[0]
print("floats=%d exact=%d" % (n, best), "naive=%d" % struct.unpack("<I", struct.pack("<f", acc))[0], file=sys.stdout)
PY
)
for t in 1 4; do
  got=$("$work/real_exact" "$work/floats.bin" --threads $t 2> "$work/err")
  [ "$got" = "${want% naive=*}" ] && ok=ok || ok=FAIL
  printf 'exact threads=%s  %s  [%s]  %s | python %s\n' "$t" "$got" "$ok" "$(tr '\n' ' ' < "$work/err")" "$want"
done
