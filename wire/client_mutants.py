#!/usr/bin/env python3
# The client's and the pool's laws are not vacuous. Each mutant breaks
# wire/client.bend or wire/pool.bend the way a bug would -- a connection
# reused after a close or with bytes unread, a read past the deadline, no
# head cap, a pooled connection handed out though bytes wait on it or
# stale, a pool kept past its cap -- and the file's own laws must refuse
# it. (A connection handed out and kept in the pool too is not a mutant
# that can be written: a connection is affine, and the checker refuses
# the second use.) Each runs in a scratch copy of wire/, checked clean
# first.
#
#   python3 wire/client_mutants.py        (from the repo root)
import os, re, shutil, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)

MUTANTS = [
  ('client.bend', 'a connection reused though its response said close',
    '''  Done{Got{i, r, rest, Bool.not(resp.close(r)) && String.is_empty(rest)}}''',
    '''  Done{Got{i, r, rest, String.is_empty(rest)}}'''),
  ('client.bend', 'a connection reused with bytes unread after the response',
    '''  Done{Got{i, r, rest, Bool.not(resp.close(r)) && String.is_empty(rest)}}''',
    '''  Done{Got{i, r, rest, Bool.not(resp.close(r))}}'''),
  ('client.bend', 'a body that ran to the close taken as reusable',
    '''          Done{Got{i, r, "", False{}}}''',
    '''          Done{Got{i, r, "", True{}}}'''),
  ('client.bend', 'a turn past the deadline reads anyway',
    '''  rd.time(~M, ~pure, ~bind, ~S, ~rx, e, b, Nat.is_lt(now, until), Nat.sub(until, now), p, hd, s,''',
    '''  rd.time(~M, ~pure, ~bind, ~S, ~rx, e, b, True{}, Nat.sub(until, now), p, hd, s,'''),
  ('client.bend', 'a read waits its whole step, past the deadline',
    '''  Nat.min(U32.to_nat(budget.step(b)), left)''',
    '''  U32.to_nat(budget.step(b))'''),
  ('client.bend', 'no head cap: a head is read however long it runs',
    '''      rd.more(~M, ~pure, ~S, Nat.is_lt(U32.to_nat(budget.head(b)), hd2), s, R.feed_buf(e, bs, p), hd2,''',
    '''      rd.more(~M, ~pure, ~S, False{}, s, R.feed_buf(e, bs, p), hd2,'''),
  ('pool.bend', 'a pooled connection handed out though its probe found bytes waiting',
    '''    case False{}:
      bind(Unit, List<a, Slot<a, C>> & Maybe<a, Slot<a, C>>, close(c), u => again(t))

def take.at(''',
    '''    case False{}:
      pure(List<a, Slot<a, C>> & Maybe<a, Slot<a, C>>, (t, Some{Slot{c, born, last}}))

def take.at('''),
  ('pool.bend', 'a stale connection handed out',
    '''          take.at(~M, ~pure, ~bind, ~a, ~C, ~probe, ~close, fresh(age, idle, now, born, last), c, born,''',
    '''          take.at(~M, ~pure, ~bind, ~a, ~C, ~probe, ~close, True{}, c, born,'''),
  ('pool.bend', 'the pool kept past its cap',
    '''      give.keep(~M, ~pure, ~bind, ~a, ~C, ~close, 1n+k, age, idle, s, split(a, C, k, xs))''',
    '''      give.keep(~M, ~pure, ~bind, ~a, ~C, ~close, 1n+k, age, idle, s, split(a, C, 1n+k, xs))'''),
]

def check(path):
  r = subprocess.run(['bun', os.path.join(ROOT, 'bend2', 'main.ts'), path],
    capture_output=True, text=True, cwd=ROOT)
  return (r.stdout + r.stderr).strip()

def where(out):
  m = re.search(r'Location: ([\w.]+)', out)
  return m.group(1) if m else out.splitlines()[0] if out else '?'

def main():
  bad = 0
  top = tempfile.mkdtemp(prefix='client_laws_')
  d = os.path.join(top, 'wire')
  try:
    shutil.copytree(HERE, d)
    for f in ('client.bend', 'pool.bend'):
      out = check(os.path.join(d, f))
      if out != 'All terms check.':
        print('the copy of %s does not check clean: %s' % (f, out))
        sys.exit(1)
    for f, name, a, b in MUTANTS:
      path = os.path.join(d, f)
      src = open(path).read()
      if src.count(a) != 1:
        print('MISSING  %s' % name); bad += 1; continue
      open(path, 'w').write(src.replace(a, b))
      out = check(path)
      open(path, 'w').write(src)
      if out == 'All terms check.':
        print('SURVIVED %s' % name); bad += 1
      else:
        print('KILLED   %s -- %s' % (name, where(out)))
  finally:
    shutil.rmtree(top, ignore_errors=True)
  print('mutants: %d / %d killed' % (len(MUTANTS) - bad, len(MUTANTS)))
  sys.exit(1 if bad else 0)

main()
