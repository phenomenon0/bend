#!/usr/bin/env python3
# std/time.bend's mutants: each breaks the calendar, the text or the
# reader the way a real date library goes wrong, and must be killed by
# the file's laws (the checker computes them), by tests/std/time_check.py
# (every day to 9999 against Python's datetime, and its edge cases), or
# by both; the table says which. Every mutant is applied to a copy of
# std/ in a temporary directory, its snippet must occur exactly once, and
# the mutant without its laws must still check: one that does not type
# is a broken test, not a killed one.
#
#   python3 tests/std/time_mutants.py [--bend path/to/main.ts] [--lanes c] [--step k]
import os, shutil, subprocess, sys, tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
ARGS = sys.argv[1:]


def opt(name, default):
  return ARGS[ARGS.index(name) + 1] if name in ARGS else default


BEND = opt('--bend', os.path.join(ROOT, 'bend2', 'main.ts'))
LANES = opt('--lanes', 'c')
STEP = opt('--step', '1')

ONLY = opt('--only', '')
MUTANTS = [
  ('no 100-year rule: 1900 and 2100 leap', 'z / 4 - z / 100 + z / 400', 'z / 4 + z / 400'),
  ('no 400-year rule: 2000 not leap', '- z / 100 + z / 400', '- z / 100'),
  ('an era of 146096 days', '(a % 146097 .|. 3 : U32)', '(a % 146096 .|. 3 : U32)'),
  ('a four-year cycle of 1460 days', '(b % 1461 / 4 * 5', '(b % 1460 / 4 * 5'),
  ('the month table a day off', '* 5 + 461 : U32', '* 5 + 456 : U32'),
  ('months of 154 over five', '+m = (g / 153 : U32)', '+m = (g / 154 : U32)'),
  ('January and February kept in the year before', ' + b / 1461 + m / 13 : U32', ' + b / 1461 : U32'),
  ('civil a day off the epoch', '((n + 719468) * 4', '((n + 719469) * 4'),
  ('days a day off the epoch', '+ d - 719469', '+ d - 719468'),
  ('days with the month table off', '(k % 12 * 153 + 2) / 5', '(k % 12 * 153 + 4) / 5'),
  ('the HTTP weekday a day off', '((n + 4) % 7 : U32)', '((n + 3) % 7 : U32)'),
  ('weekday a day off', 'Nat.add(n, 4n), 7n', 'Nat.add(n, 5n), 7n'),
  ('the month names one off', '(m + 6 : U32)', '(m + 5 : U32)'),
  ('the seconds shown as the minutes', 'dg(2n, (s % 60 : U32), t)', 'dg(2n, (s / 60 % 60 : U32), t)'),
  ('the ms in two places', 'dg(3n, U32.from_nat', 'dg(2n, U32.from_nat'),
  ('day takes a year before 1970', 'Nat.is_le(1970n, y) && ', ''),
  ('day ignores the month', ' && Nat.is_eq(b, m)', ''),
  ('day ignores the day past 2^32 (mod 2^32)', ' && Nat.is_eq(e, d)', ''),
  ('from lets hour 24 through', 'Nat.is_lt(h, 24n)', 'Nat.is_le(h, 24n)'),
  ('from lets second 60 through', 'Nat.is_lt(s, 60n)', 'Nat.is_le(s, 60n)'),
  ('iso.read takes any separator', 'U32.is_eq(c, q)))', 'True{}))'),
  ('iso.read keeps the date digits past the T', 'Bool.pick(U32, x, 0, ', 'Bool.pick(U32, x, lo, '),
  ('iso.read takes : as a digit', 'U32.is_lt((c - 48 : U32), 10)', 'U32.is_lt((c - 48 : U32), 11)'),
]


# a mutant can make the checker count a wrapped U32 in unary: a law that
# does not answer in two minutes has not killed it
def check(work):
  try:
    r = subprocess.run(['bun', BEND, 'std/time.bend', '--check-only'], cwd=work, capture_output=True, text=True,
      env=dict(os.environ, BEND_NO_TELEMETRY='1'), timeout=120)
  except subprocess.TimeoutExpired:
    return None, 'timeout'
  return 'All terms check.' in r.stdout + r.stderr, r.stdout + r.stderr


def main():
  src = open(os.path.join(ROOT, 'std', 'time.bend')).read()
  laws = src.index('# The laws')
  work = tempfile.mkdtemp(prefix='bend-time-mutants.')
  shutil.copytree(os.path.join(ROOT, 'std'), os.path.join(work, 'std'))
  tm = os.path.join(work, 'std', 'time.bend')
  broken = alive = 0
  for name, a, b in MUTANTS:
    if ONLY and ONLY not in name:
      continue
    if src.count(a) != 1:
      print('BROKEN %-46s snippet occurs %d times' % (name, src.count(a)))
      broken += 1
      continue
    m = src.replace(a, b)
    open(tm, 'w').write(m[:m.index('# The laws')])
    ok, out = check(work)
    if not ok:
      print('BROKEN %-46s does not check without its laws:\n%s' % (name, out[:600]))
      broken += 1
      continue
    open(tm, 'w').write(m)
    ok, out = check(work)
    by_laws = ok is False and ('Location: vectors' in out or 'Location: read_back' in out)
    r = subprocess.run([sys.executable, os.path.join(ROOT, 'tests', 'std', 'time_check.py'), '--bend', BEND,
      '--std', os.path.join(work, 'std'), '--lanes', LANES, '--step', STEP], capture_output=True, text=True)
    by_check = r.returncode != 0
    if not (by_laws or by_check):
      alive += 1
    print('%-6s %-46s laws:%-6s check:%s' % ('killed' if by_laws or by_check else 'ALIVE', name,
      'kill' if by_laws else 'hang' if ok is None else '-', 'kill' if by_check else '-'))
    sys.stdout.flush()
  open(tm, 'w').write(src)
  shutil.rmtree(work)
  print('%d mutants: %d killed, %d alive, %d broken' % (len(MUTANTS), len(MUTANTS) - alive - broken, alive, broken))
  sys.exit(1 if alive or broken else 0)


main()
