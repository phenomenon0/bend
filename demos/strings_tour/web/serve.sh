#!/usr/bin/env bash
# Builds the two emitted JS programs (if missing) and serves the live page.
set -e
cd "$(dirname "$0")/../../.."    # repo root (bend-work-strings-demo)
for p in codepoints fuel; do
  if [ ! -f "demos/strings_tour/web/$p.js" ] || [ "demos/strings_tour/$p.bend" -nt "demos/strings_tour/web/$p.js" ]; then
    bun bend2/main.ts "demos/strings_tour/$p.bend" -o "demos/strings_tour/web/$p.js"
    echo "built web/$p.js"
  fi
done
cd demos/strings_tour/web
echo "serving on :8124  (http://100.108.6.13:8124/ · http://10.0.0.22:8124/)"
exec python3 -m http.server 8124 --bind 0.0.0.0
