#!/usr/bin/env bash
# verify.sh <bend-checkout> [item...]
# Runs every repro in this directory against a Bend checkout (canon's
# main, or a fix branch) and prints one line per item and lane:
#   U01  c       REPRO  01efbfbdefbfbd02
# REPRO: the behaviour UPSTREAM.md describes is there. FIXED: the repro
# saw the right behaviour (for an item marked NOT-REPRO or OURS, that is
# the expected answer on canon). SKIP: a tool or file is missing.
# Ports 29601-29613 and 29800. Needs bun, python3, perl and clang.
set -u
ROOT=$(cd "${1:?usage: verify.sh <bend-checkout> [item...]}" && pwd)
shift
HERE=$(cd "$(dirname "$0")" && pwd)
W=$(mktemp -d "${TMPDIR:-/tmp}/bend-upstream.XXXXXX")
trap 'kill $(jobs -p) 2>/dev/null; rm -rf "$W"' EXIT
BEND="bun $ROOT/bend2/main.ts"
ONLY=" ${*:-} "
cd "$W" || exit 1

want() { [ "$ONLY" = "  " ] || [[ "$ONLY" == *" $1 "* ]]; }

say() { printf '%-4s %-7s %-6s %s\n' "$1" "$2" "$3" "$4"; }

has() { grep -q "^def $1(" "$ROOT/bend2/base.bend"; }

# build <name> <file.bend>: <name>.js and <name> (the C binary) in $W
build() {
  $BEND "$2" -o "$W/$1.js" -o "$W/$1" > "$W/$1.build" 2>&1
}

# cmd <lane> <name> <file.bend>: the command that runs the program
cmd() {
  case $1 in
    interp) echo "$BEND $3" ;;
    js) echo "bun $W/$2.js" ;;
    c) echo "$W/$2" ;;
  esac
}

# run <secs> <command...>: output (stdout and stderr), then "exit N"
run() {
  local t=$1; shift
  perl -e 'alarm shift; exec @ARGV' "$t" "$@" 2>&1
  echo "exit $?"
}

# judge <item> <lane> <got> <bug-regex>: REPRO when a line of got
# matches (or, for a regex written !re, when none does)
judge() {
  local hit
  grep -Eq -- "${4#!}" <<< "$3" && hit=1 || hit=0
  [ "${4:0:1}" = "!" ] && hit=$((1 - hit))
  local shown
  shown=$(head -c 70 <<< "$3" | tr '\n' ' ')
  if [ $hit = 1 ]; then
    say "$1" "$2" REPRO "$shown"
  else
    say "$1" "$2" FIXED "$shown"
  fi
}

# served <item> <name> <bug-regex> <peer args...>: start the program in
# each lane, run the peer against it, judge the peer's line
served() {
  local item=$1 name=$2 bug=$3; shift 3
  build "$name" "$HERE/$name.bend"
  for lane in interp js c; do
    $(cmd $lane "$name" "$HERE/$name.bend") > "$W/$name.$lane.out" 2>&1 &
    local pid=$!
    local got
    got=$(perl -e 'alarm 30; exec @ARGV' python3 "$HERE/peer.py" "$@" 2>&1)
    sleep 0.2
    kill $pid 2>/dev/null
    wait $pid 2>/dev/null
    judge "$item" $lane "$got" "$bug"
  done
}

# lanes <item> <name> <secs> <bug-regex> [lanes]: run the program in each
# lane and judge its output
lanes() {
  local item=$1 name=$2 secs=$3 bug=$4 ls=${5:-interp js c}
  build "$name" "$HERE/$name.bend"
  for lane in $ls; do
    judge "$item" $lane "$(run "$secs" $(cmd $lane "$name" "$HERE/$name.bend"))" "$bug"
  done
}

# check <item> <file> <bug-regex> [flags]: judge what the checker says
check() {
  judge "$1" check "$(run 60 $BEND "$HERE/$2.bend" ${4:-})" "$3"
}

# U01: with no byte pair, TCP.recv is the only reader, and it decodes
if want U01; then
  if has TCP.recv_bytes; then
    served U01 tcp_bytes_fixed '!^0180fe02$' echo 29601
  else
    served U01 tcp_bytes 'efbfbd' echo 29601
  fi
fi

# U02: 64 connections at once to a listener that is not accepting
want U02 && served U02 listen_backlog 'completed (1[0-9]|2[0-9]) ' burst 29602 64

# U03: the pass cost beside 4000 descriptor waiters; U03t: beside 20000
# timers, and 4000 passes beside 16384 sleepers ("slow" past 1 s)
want U03 && lanes U03 io_fd_waiters 120 'ratio ([5-9]|[0-9]{2,})' "js c"
if want U03 || want U03t; then
  lanes U03t io_waiters 120 'ratio ([5-9]|[0-9]{2,})' "js c"
  lanes U03t io_timer_waiters 60 '^slow' "interp js c"
fi

# U04: 2^40 through Nat.min and Nat.max (U16: the checker's evaluator
# cannot build 2^40, so the interp lane is not asked)
want U04 && lanes U04 nat_min_max 20 '!1099511627776 1099511627777' "js c"

# U05: File.write is text (UTF-8 of code points), File.write_bytes bytes
want U05 && lanes U05 file_write_text 30 '!^194 128 195 169 ?$' "interp js c"

# U06: the arm not taken is a 10^8-step loop (about 20 s on the JS
# runtime); a pure main's normalizer is the one lazy lane
want U06 && lanes U06 bool_pick 90 '^eager$' "interp js c"
want U06 && lanes U06p bool_pick_pure 30 '!^1$' "interp"

# U07: SIGTERM after 1.5 s must end the program within 3 s
if want U07; then
  build sigterm "$HERE/sigterm.bend"
  for lane in interp js c; do
    $(cmd $lane sigterm "$HERE/sigterm.bend") > "$W/sigterm.out" 2>&1 &
    pid=$!
    sleep 1.5
    kill -TERM $pid
    t=0
    while kill -0 $pid 2>/dev/null && [ $t -lt 30 ]; do sleep 0.1; t=$((t + 1)); done
    if kill -0 $pid 2>/dev/null; then
      kill -KILL $pid; wait $pid 2>/dev/null
      say U07 $lane REPRO "still running 3 s after SIGTERM"
    else
      wait $pid 2>/dev/null; code=$?
      say U07 $lane FIXED "ended $((t * 100)) ms after SIGTERM, status $code"
    fi
  done
fi

# U08: a default arm over IO.OP must take a foreign request (70)
want U08 && lanes U08 io_op_default 30 '!^70$' "interp js c"

# U09: a def used above its definition is told apart from a typo
want U09 && check U09 def_order 'expected : a defined name'

# U10: a Nat literal of 100000n in a proof; a Nat literal past 2^32
want U10 && check U10 nat_literal_proof 'stack overflowed'
want U10 && check U10b nat_literal_cap 'nat literal up to'

# U11: a check that relies on @unsafe exits 0 (with --strict, when the
# checkout has one)
if want U11; then
  flag=--check-only
  grep -q -- '--strict' "$ROOT/bend2/main.ts" && flag="--check-only --strict"
  check U11 unsafe_exit '^exit 0$' "$flag"
fi

# U12: IO.signal_pending exists only on our branch
if want U12; then
  if has IO.signal_pending; then
    say U12 - REPRO "IO.signal_pending is in Base: see UPSTREAM.md"
  else
    say U12 - FIXED "no signal effect in Base (the item is ours)"
  fi
fi

# U13: accept out of descriptors must hand back a Fail with errno 24
# (EMFILE) and the listener, not hang, spin or kill the program
if want U13; then
  build accept_emfile "$HERE/accept_emfile.bend"
  for lane in interp js c; do
    (ulimit -n 256; exec $(cmd $lane accept_emfile "$HERE/accept_emfile.bend")) \
      > "$W/emfile.out" 2>&1 &
    pid=$!
    perl -e 'alarm 30; exec @ARGV' python3 "$HERE/peer.py" hold 29613 400 > /dev/null 2>&1
    sleep 0.5
    kill $pid 2>/dev/null
    wait $pid 2>/dev/null
    judge U13 $lane "$(cat "$W/emfile.out")" '!Fail 24'
  done
fi

# U14: canon's own io tests that order sleeps 10 to 20 ms apart, ten runs
# of the JS lane; and whether the audio tests can build here at all
if want U14; then
  for t in spawn_sleep fork_join; do
    f="$ROOT/tests/io/$t.bend"
    [ -f "$f" ] || { say U14 $t SKIP "no tests/io/$t.bend"; continue; }
    expect=$(grep '^#|' "$f" | cut -c3-)
    $BEND "$f" -o "$W/$t.js" > /dev/null 2>&1
    bad=0
    for i in 1 2 3 4 5 6 7 8 9 10; do
      [ "$(run 10 bun "$W/$t.js" | sed '$d')" = "$expect" ] || bad=$((bad + 1))
    done
    if [ $bad -gt 0 ]; then
      say U14 "$t" REPRO "$bad of 10 JS runs out of order"
    else
      say U14 "$t" FIXED "10 of 10 JS runs in order"
    fi
  done
  # two tests that fail on our branch (ours): the checker's answer for
  # tls_connect_close, the JS lane's for marshal_char_scalar
  f="$ROOT/tests/io/tls_connect_close.bend"
  if [ -f "$f" ]; then
    expect=$(grep '^#|' "$f" | cut -c3- | sed 's/[ \t]*$//')
    got=$(run 60 $BEND "$f" | sed 's/[ \t]*$//')
    [ "$got" = "$expect" ] && say U14 tls_close FIXED "prints its #| lines" \
      || say U14 tls_close REPRO "$(head -c 60 <<< "$got" | tr '\n' ' ')"
  fi
  f="$ROOT/tests/io/marshal_char_scalar.bend"
  if [ -f "$f" ]; then
    expect=$(grep '^#|' "$f" | cut -c3-)
    $BEND "$f" -o "$W/mcs.js" > /dev/null 2>&1
    got=$(run 10 bun "$W/mcs.js")
    [ "$got" = "$expect" ] && say U14 marshal FIXED "JS prints its #| lines" \
      || say U14 marshal REPRO "$(head -c 60 <<< "$got" | tr '\n' ' ')"
  fi
  if printf '#include <alsa/asoundlib.h>\n' | clang -E -x c - > /dev/null 2>&1; then
    say U14 audio FIXED "ALSA headers present"
  else
    say U14 audio REPRO "no alsa/asoundlib.h: the audio tests fail both lanes"
  fi
fi

# U15: the core files against their caps in gates/repo.ts. ttok counts
# with cl100k_base (its default model is gpt-3.5-turbo); when ttok cannot
# fetch its table, js-tiktoken's cl100k_base (bun installs it) stands in.
# REPRO: within 3% of the cap, so the next fix needs a raise.
if want U15; then
  for f in bend2/comp.ts bend2/bend.ts bend2/base.bend bend2/main.ts; do
    cap=$(grep -o "allow(\"$f\", [0-9]*" "$ROOT/gates/repo.ts" | grep -o '[0-9]*$')
    n=$(ttok < "$ROOT/$f" 2> /dev/null)
    how=ttok
    if [ -z "$n" ]; then
      how=js-tiktoken
      n=$(bun -e 'import { getEncoding } from "js-tiktoken";
        const t = require("fs").readFileSync(process.argv[1], "utf8");
        console.log(getEncoding("cl100k_base").encode(t, "all").length)' \
        "$ROOT/$f" 2> /dev/null)
    fi
    if [ -z "$n" ] || [ -z "$cap" ]; then
      say U15 "$(basename $f)" SKIP "no counter ran (cap ${cap:-?})"
    elif [ $((n * 100)) -ge $((cap * 97)) ]; then
      say U15 "$(basename $f)" REPRO "$n of $cap ($how, cl100k)"
    else
      say U15 "$(basename $f)" FIXED "$n of $cap ($how, cl100k)"
    fi
  done
fi

# U16: the checker's evaluator on a pure main counts Nats in unary
want U16 && lanes U16 interp_nat_mul 20 '!^1099511627776n$' "interp"
want U16 && lanes U16e interp_nat_epoch 20 '!^28333334n$' "interp"

# U17: TCP.listen takes a port only, and binds 0.0.0.0
if want U17; then
  if has TCP.listen_on; then
    say U17 - FIXED "Base has TCP.listen_on(host, port)"
  else
    say U17 - REPRO "TCP.listen(port) binds every interface; no address"
  fi
fi

# U18: a host name to TCP.connect (or a resolver beside it)
if want U18; then
  if has DNS.resolve; then
    say U18 - FIXED "Base has DNS.resolve"
  else
    lanes U18 connect_name 20 'Fail 22' "interp js c"
  fi
fi

# U19: a Socket dropped without Socket.close keeps its descriptor: under
# `ulimit -n 256`, 400 connect-accept-drop rounds (800 sockets) hit EMFILE
if want U19; then
  build socket_drop "$HERE/socket_drop.bend"
  for lane in interp js c; do
    judge U19 $lane "$(ulimit -n 256; run 60 $(cmd $lane socket_drop \
      "$HERE/socket_drop.bend"))" 'Fail 24'
  done
fi

# F-items: limitations from apps/uptime/FRICTION.md
if want F01; then
  if has IO.wall || has IO.clock; then
    say F01 - FIXED "Base has a wall clock"
  else
    say F01 - REPRO "IO.now is Base's only clock (monotonic)"
  fi
fi
if want F02; then
  miss=""
  for d in File.rename File.sync File.seek File.remove Dir.make; do
    has $d || miss="$miss $d"
  done
  if [ -n "$miss" ]; then
    say F02 - REPRO "not in Base:$miss"
  else
    say F02 - FIXED "all in Base"
  fi
fi
if want F03; then
  if grep -q '^def File.read_at(file: File, offset: U32' "$ROOT/bend2/base.bend"; then
    say F03 - REPRO "File.read_at takes a U32 offset, answers a cell per byte"
  else
    say F03 - FIXED "File.read_at's offset is not a U32"
  fi
fi
want F04 && check F04 mutual 'a filled definition|a defined name'
want F05 && check F05 list_map_quant 'expected : List<&1'
want F06 && check F06 let_computed 'scrutinee'
want F07 && check F07 import_name "an import \\('import Base'"
exit 0
