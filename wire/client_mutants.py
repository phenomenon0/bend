#!/usr/bin/env python3
# The client's, the pool's and the body stream's laws are not vacuous.
# Each mutant breaks wire/client.bend, wire/pool.bend or wire/stream.bend
# the way a bug would -- a connection reused after a close or with bytes
# unread, a read past the deadline, no head cap, a pooled connection
# handed out though bytes wait on it or stale, a pool kept past its cap;
# a stream that reads with its window full, waits on a stalled consumer,
# reorders, drops or trusts too much of a body, or tells its end early,
# twice, or goes on after it -- and the laws must refuse it: the file's
# own, and the stream's in wire/world.bend. (A connection handed out and kept in the pool too is not a mutant
# that can be written: a connection is affine, and the checker refuses
# the second use.) Each runs in a scratch copy of wire/ of its own,
# re-checked from the mutated file on (mutate.py); a clean copy checks
# clean.
#
#   python3 wire/client_mutants.py [-j N] [--shard i/n]   (from the repo root)
import os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
import mutate as M

MUTANTS = [
  ('client.bend', 'a connection reused though its response said close',
    '''  Done{Got{i, r, rest, Bool.not(resp.close(r)) && String.is_empty(rest)}}''',
    '''  Done{Got{i, r, rest, String.is_empty(rest)}}'''),
  ('client.bend', 'a connection reused with bytes unread after the response',
    '''  Done{Got{i, r, rest, Bool.not(resp.close(r)) && String.is_empty(rest)}}''',
    '''  Done{Got{i, r, rest, Bool.not(resp.close(r))}}'''),
  ('client.bend', 'a body that ran to the close taken as reusable',
    '''        case R.Closing{r}:
          Done{Got{i, r, "", False{}}}''',
    '''        case R.Closing{r}:
          Done{Got{i, r, "", True{}}}'''),
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

# the body stream's mutants: (file, what, before, after); its laws are
# world.bend's, over every framer
STREAM = [
  ('stream.bend', 'a stream reads with its window full',
    '''    case Going{} False{}:
      pull.room(~M, ~pure, ~bind, ~S, ~rx, ~E, ~R, ~feed, ~take, ~K, e, ms, s, r, k, held,
        False{}, Nat.is_lt(Bytes.len(held), win))''',
    '''    case Going{} False{}:
      pull.room(~M, ~pure, ~bind, ~S, ~rx, ~E, ~R, ~feed, ~take, ~K, e, ms, s, r, k, held,
        False{}, True{})'''),
  ('stream.bend', 'a consumer that takes nothing of a full window is waited on',
    '''    Nat.is_eq(n, 0n) && (Nat.is_le(win, Bytes.len(held)) || Bool.not(more(look(r), eof))))''',
    '''    Nat.is_eq(n, 0n) && Bool.not(more(look(r), eof)))'''),
  ('stream.bend', 'a pass drops what the consumer did not take',
    '''  pass.stall(S, R, K, s, r, k, String.drop(held, n), eof,''',
    '''  pass.stall(S, R, K, s, r, k, "", eof,'''),
  ('stream.bend', "a read's body goes in front of what was held",
    '''      (Bq{s, r, k, Bytes.append(held, x), eof}, None{})''',
    '''      (Bq{s, r, k, Bytes.append(x, held), eof}, None{})'''),
  ('stream.bend', "a read's body past its bytes is trusted",
    '''  pull.fits(S, R, K, s, r, k, held, x, eof, Nat.is_le(Bytes.len(x), n))''',
    '''  pull.fits(S, R, K, s, r, k, held, x, eof, True{})'''),
  ('stream.bend', 'the end told with bytes still held',
    '''    case Ended{} _:
      pull.end(~M, ~pure, ~bind, ~S, ~R, ~K, ~fin, s, r, k, held, eof, String.is_empty(held))''',
    '''    case Ended{} _:
      pull.end(~M, ~pure, ~bind, ~S, ~R, ~K, ~fin, s, r, k, held, eof, True{})'''),
  ('stream.bend', 'the end told twice',
    '''      bind(K, Turn(S, R, K), fin(k), k2 => pure(Turn(S, R, K), (Bq{s, r, k2, held, eof},''',
    '''      bind(K, Turn(S, R, K), bind(K, K, fin(k), fin), k2 => pure(Turn(S, R, K), (Bq{s, r, k2, held, eof},'''),
  ('stream.bend', 'the stream goes on after its end',
    '''    case Some{why}:
      pure(Bq<S, R, K> & Why, (bq, why))
    case None{}:
      again(bq)''',
    '''    case Some{why}:
      again(bq)
    case None{}:
      again(bq)'''),
]

def where(out):
  m = re.search(r'Location: ([\w.]+)', out)
  return m.group(1) if m else out.splitlines()[0] if out else '?'

def main():
  jobs, shard = M.args()
  bad = 0
  muts = [(name, 'wire/' + f, a, b, 'wire/' + f) for f, name, a, b in MUTANTS] \
    + [(name, 'wire/' + f, a, b, 'wire/world.bend') for f, name, a, b in STREAM]
  bases, res = M.run(lambda: M.tree(['wire'], prefix='client_laws_'), 'wire/world.bend', muts, jobs, shard)
  for f, out in bases.items():
    if out != 'All terms check.':
      print('the copy of %s does not check clean: %s' % (f, out))
      sys.exit(1)
  for name, _, out in res:
    if out is None:
      print('MISSING  %s' % name); bad += 1
    elif out == 'All terms check.':
      print('SURVIVED %s' % name); bad += 1
    else:
      print('KILLED   %s -- %s' % (name, where(out)))
  print('mutants: %d / %d killed' % (len(res) - bad, len(res)))
  sys.exit(1 if bad else 0)

main()
