#!/usr/bin/env python3
# std/time.bend against Python's datetime on EVERY day from 1970-01-01 to
# 9999-12-31 (2,932,897 days), in the lanes named. Day n at second
# n * 7919 mod 86400 (7919 is prime to 86400, so every second of a day is
# hit, each some 34 times) and ms n mod 1000 prints Time.iso, Time.http,
# Time.iso.ms, Time.date and Time.weekday, each matched to datetime's;
# and Time.day must take the date back to n, Time.iso.read the ISO text
# back to its second, and Time.day refuse the day after the date when
# the month has no such day (the leap rule and every month's length).
# The days are cut into shards run side by side, batch lines a print.
#
# A line of edge cases comes first: Nats past U32, hours, minutes and
# seconds out of range, and text iso does not write.
#
#   python3 tests/std/time_check.py [--bend path/to/main.ts] [--lanes c,js,interp]
#     [--step k] (every k-th day) [--std dir] (another std/, a mutant's)
import calendar, datetime, email.utils, os, shutil, subprocess, sys, tempfile, time
from concurrent.futures import ThreadPoolExecutor

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
ARGS = sys.argv[1:]


def opt(name, default):
  return ARGS[ARGS.index(name) + 1] if name in ARGS else default


BEND = opt('--bend', os.path.join(ROOT, 'bend2', 'main.ts'))
LANES = opt('--lanes', 'c,js').split(',')
STEP = int(opt('--step', '1'))
STD = opt('--std', os.path.join(ROOT, 'std'))
DAYS = 2932897
SHARDS = 4
BATCH = 2000

SRC = '''import Base
import ./std/time.bend as Time

def ymd(c: Nat & Nat & Nat) -> String:
  (y, m, d) = c
  Nat.show(y) ++ "/" ++ Nat.show(m) ++ "/" ++ Nat.show(d)

def mb(m: Maybe<&2, Nat>) -> String:
  match m:
    case None{}:
      "-"
    case Some{x}:
      Nat.show(x)

def next.go(+y: Nat, +m: Nat, +d: Nat) -> String:
  mb(Time.day(y, m, d)) ++ "|" ++ mb(Time.day(y, m, Nat.add(d, 1n)))

def next(c: Nat & Nat & Nat) -> String:
  (y, m, d) = c
  next.go(y, m, d)

def line(+n: Nat) -> String:
  +t = Nat.add(Nat.mul(n, 86400n), Nat.mod(Nat.mul(n, 7919n), 86400n))
  Time.iso(t) ++ "|" ++ Time.http(t) ++ "|" ++ Time.iso.ms(Nat.add(Nat.mul(t, 1000n), Nat.mod(n, 1000n)))
    ++ "|" ++ ymd(Time.date(n)) ++ "|" ++ Nat.show(Time.weekday(n)) ++ "|" ++ next(Time.date(n))
    ++ "|" ++ mb(Time.iso.read(Time.iso(t)))

def lines(k: Nat, +n: Nat) -> String:
  match k:
    case 0n:
      ""
    case 1n+j:
      line(n) ++ "\\n" ++ lines(j, Nat.add(n, STEPn))

def run(b: Nat, +n: Nat, +left: Nat) -> IO(Unit):
  match b:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+g:
      do IO<Unit>:
        u : Unit <- IO.print(lines(Nat.min(BATCHn, left), n))
        run(g, Nat.add(n, Nat.mul(BATCHn, STEPn)), Nat.sub(left, BATCHn))

# 2^32 + k
def big(k: Nat) -> Nat:
  Nat.add(Nat.add(4294967295n, 1n), k)

# out of range, or past U32 (a Nat taken mod 2^32 would be a date), or
# text iso does not write
def edges() -> String:
  mb(Time.day(2000n, 2n, big(29n))) ++ " " ++ mb(Time.day(big(2000n), 2n, 29n)) ++ " "
    ++ mb(Time.day(2000n, big(2n), 29n)) ++ " " ++ mb(Time.day(1969n, 12n, 31n)) ++ " "
    ++ mb(Time.day(2000n, 0n, 1n)) ++ " " ++ mb(Time.from(2000n, 2n, 29n, 24n, 0n, 0n)) ++ " "
    ++ mb(Time.from(2000n, 2n, 29n, 0n, 60n, 0n)) ++ " " ++ mb(Time.from(2000n, 2n, 29n, 0n, 0n, 60n)) ++ " "
    ++ mb(Time.from(2000n, 2n, 29n, big(0n), 0n, 0n)) ++ " " ++ mb(Time.from(2000n, 2n, 29n, 23n, 59n, 59n)) ++ " "
    ++ mb(Time.iso.read("1969-12-31T23:59:59Z")) ++ " " ++ mb(Time.iso.read("2000-02-29T12:34:56Z ")) ++ " "
    ++ mb(Time.iso.read("2000-02-29t12:34:56Z")) ++ " " ++ mb(Time.iso.read("2000-02-29T12:34:56")) ++ " "
    ++ mb(Time.iso.read("")) ++ " " ++ mb(Time.iso.read("10000-01-01T00:00:00Z")) ++ " "
    ++ mb(Time.iso.read("2000-02-29T12:34:0:Z"))

def main() -> IO(Unit):
  do IO<Unit>:
    u : Unit <- IO.print(edges())
    run(RUNSn, STARTn, COUNTn)
'''

MON = 'Jan Feb Mar Apr May Jun Jul Aug Sep Oct Nov Dec'.split()
EPOCH = datetime.datetime(1970, 1, 1, tzinfo=datetime.timezone.utc)


def want(n):
  t = n * 86400 + n * 7919 % 86400
  dt = EPOCH + datetime.timedelta(seconds=t)
  d = dt.date()
  return '|'.join([
    dt.strftime('%Y-%m-%dT%H:%M:%SZ'),
    email.utils.format_datetime(dt, usegmt=True),
    dt.strftime('%Y-%m-%dT%H:%M:%S.') + '%03dZ' % (n % 1000),
    '%d/%d/%d' % (d.year, d.month, d.day),
    str((d.weekday() + 1) % 7),
    str(n), str(n + 1) if d.day < calendar.monthrange(d.year, d.month)[1] else '-',
    str(t)])


EDGES = '- - - - - - - - - %d - - - - - - -' % 951868799


def shard(work, lane, i, ns):
  f = os.path.join(work, 'c%d.bend' % i)
  open(f, 'w').write(SRC.replace('COUNT', str(len(ns))).replace('RUNS', str((len(ns) + BATCH - 1) // BATCH)).replace('START', str(ns[0]))
    .replace('STEP', str(STEP)).replace('BATCH', str(BATCH)))
  env = dict(os.environ, BEND_NO_TELEMETRY='1')
  if lane == 'interp':
    cmd = ['bun', BEND, f]
  else:
    out = os.path.join(work, 'c%d%s' % (i, '.js' if lane == 'js' else ''))
    try:
      b = subprocess.run(['bun', BEND, f, '-o', out], cwd=work, capture_output=True, text=True, env=env,
        timeout=300)
    except subprocess.TimeoutExpired:
      return 0, ['build timed out']
    if b.returncode != 0:
      return 0, ['build failed: ' + (b.stdout + b.stderr)[:800]]
    cmd = ['bun', out] if lane == 'js' else [out]
  p = subprocess.Popen(cmd, cwd=work, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, env=env)
  k, bad, first = 0, [], True
  for l in p.stdout:
    l = l.rstrip('\n')
    if l == '':
      continue
    if first:
      first = False
      if l != EDGES:
        bad.append('edges:\n  got  %s\n  want %s' % (l, EDGES))
      continue
    n = ns[k] if k < len(ns) else -1
    w = want(n) if n >= 0 else '(no more days)'
    if l != w and len(bad) < 5:
      bad.append('day %d:\n  got  %s\n  want %s' % (n, l, w))
    elif l != w:
      bad.append('')
    k += 1
  p.wait()
  if k != len(ns):
    bad.append('%d lines for %d days (exit %d)' % (k, len(ns), p.returncode))
  return k, bad


def main():
  work = tempfile.mkdtemp(prefix='bend-time-check.')
  shutil.copytree(STD, os.path.join(work, 'std'))
  # the implementation alone: a broken one can set its laws counting in unary
  tm = os.path.join(work, 'std', 'time.bend')
  src = open(tm).read()
  open(tm, 'w').write(src[:src.index('# The laws')])
  days = list(range(0, DAYS, STEP))
  if days[-1] != DAYS - 1 and STEP == 1:
    days.append(DAYS - 1)
  per = (len(days) + SHARDS - 1) // SHARDS
  parts = [days[i:i + per] for i in range(0, len(days), per)]
  failed = 0
  for lane in LANES:
    t = time.time()
    with ThreadPoolExecutor(SHARDS) as ex:
      rs = list(ex.map(lambda ip: shard(work, lane, ip[0], ip[1]), enumerate(parts)))
    n = sum(r[0] for r in rs)
    bad = [b for r in rs for b in r[1]]
    print('%-6s %d days, %d mismatches (%.0fs)' % (lane, n, len(bad), time.time() - t))
    for b in [b for b in bad if b][:3]:
      print(b)
    failed += 1 if bad else 0
    sys.stdout.flush()
  shutil.rmtree(work)
  sys.exit(1 if failed else 0)


main()
