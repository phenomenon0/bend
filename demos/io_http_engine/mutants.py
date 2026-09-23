#!/usr/bin/env python3
# The world's laws are not vacuous: each mutant below breaks the loop
# the way one of the review's bugs did (or would), and PROOF.bend must
# then fail, naming a law of the world. Each is applied to main.bend in
# place, checked, and undone.
#
#   python3 demos/io_http_engine/mutants.py        (from the repo root)
import os, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
MAIN = os.path.join(HERE, 'main.bend')

MUTANTS = [
  ('no head deadline: a head out of time is read again',
    '''    Nat.is_lt(el, U32.to_nat(srv.head(srv))))''',
    '''    True{})'''),
  ('no batch cap: a reply joins the batch whatever its size',
    '''    U32.cmp(U32.from_nat(Bytes.len(acc)), send.cap()))''',
    '''    LT{})'''),
  ('a reply after close: End writes one more 400 after its segments',
    '''~fread, ~fclose, s, out, srv.idle(srv)), m => pure(S, put.s(S, m)))''',
    '''~fread, ~fclose, s, out, srv.idle(srv)), m =>
            bind(Put(S), S, tx(put.s(S, m), resp.bad(), srv.idle(srv)), m2 =>
              pure(S, put.s(S, m2))))'''),
  ('a queued reply skipped on refusal: the 400 goes out alone',
    '''      Ans{answer.flat(acc, [Raw{resp.bad()}]), True{}, 0, False{}}''',
    '''      Ans{[Raw{resp.bad()}], True{}, 0, False{}}'''),
  ('the accept loop exits on EMFILE',
    '''  accept.dead(~M, ~pure, ~bind, ~L, ~sig, l, code, accept.soft(code))''',
    '''  accept.dead(~M, ~pure, ~bind, ~L, ~sig, l, code,
    accept.soft(code) && Bool.not(U32.is_eq(code, 24)))'''),
  ('replies out of order: a reply goes out before the batch it follows',
    '''            send.hold(~M, ~pure, ~bind, ~S, ~tx, ms, s, Bytes.append(acc, out)))
''',
    '''            send.hold(~M, ~pure, ~bind, ~S, ~tx, ms, s, Bytes.append(out, acc)))
'''),
  ('a WebSocket reads on after its send failed (as first written)',
    '''    case Fail{e}:
      pure(S & Plan, (s, Stop{}))
    case Done{u}:
      turn.wr(''',
    '''    case Fail{e}:
      turn.wr(~M, ~pure, ~bind, ~S, ~rx, srv, s, wr)
    case Done{u}:
      turn.wr('''),
  ('a silent peer is waited on again, not let go',
    '''  match may:
    case None{}:
      (s, Stop{})
    case Some{buf}:
      (s, plan.chunk(srv, buf, p))''',
    '''  match may:
    case None{}:
      (s, Wait{p})
    case Some{buf}:
      (s, plan.chunk(srv, buf, p))'''),
  ('an emptied file leaves its head to the batch uncapped (as first written)',
    '''        bind(Em<S>, Pump<S, F>, send.hold(~M, ~pure, ~bind, ~S, ~tx, ms, s, pre), em =>
          pure(Pump<S, F>, Over{em})))''',
    '''        pure(Pump<S, F>, Over{Em{s, pre, True{}}}))'''),
]

def check():
  r = subprocess.run(['bun', 'bend2/main.ts', 'demos/io_http_engine/PROOF.bend'], cwd=ROOT,
    capture_output=True, text=True, timeout=1800)
  return (r.stdout + r.stderr).strip()

def main():
  orig = open(MAIN).read()
  bad = 0
  try:
    for name, a, b in MUTANTS:
      if orig.count(a) != 1:
        print('MISSING  %s' % name); bad += 1; continue
      open(MAIN, 'w').write(orig.replace(a, b))
      out = check()
      if out == 'All terms check.':
        print('SURVIVED %s' % name); bad += 1
      else:
        loc = [l for l in out.split('\n') if l.startswith('Location')]
        print('KILLED   %s -- %s' % (name, (loc[0] if loc else out.split('\n')[0])[:100]))
  finally:
    open(MAIN, 'w').write(orig)
  print('mutants: %d / %d killed' % (len(MUTANTS) - bad, len(MUTANTS)))
  sys.exit(1 if bad else 0)

main()
