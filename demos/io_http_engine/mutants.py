#!/usr/bin/env python3
# The laws are not vacuous. Two kinds of mutant, each applied, checked
# and undone:
#
# - the world's: each breaks the loop the way one of the review's bugs
#   did (or would), and PROOF.bend must then fail, naming a law of the
#   world. Applied to main.bend in place.
#
# - the framing's: each breaks the reader (or the spec) the way a
#   smuggling or framing bug would, and must be refused by frame_sim
#   alone. They run in a scratch copy of this directory whose LAWS.bend
#   keeps only frame_sim, frame_sim_buf, frame_sim_reads and the laws
#   their proofs stand on -- every rule-by-rule law and every vector is
#   removed, with its proof, and so are the world's -- so a kill there
#   is frame_sim's and no other law's. The copy is checked clean first.
#
#   python3 demos/io_http_engine/mutants.py        (from the repo root)
import os, re, shutil, subprocess, sys, tempfile

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

# the framing's mutants: (what, file, before, after)
FRAMING = [
  ('TE.CL: a Transfer-Encoding with a Content-Length is read as chunked', 'main.bend',
    '''    case True{} False{} Has{v}:
      BdBad{}''',
    '''    case True{} False{} Has{v}:
      BdChunked{}'''),
  ('a chunk-size wraps: no digit is checked against the budget', 'main.bend',
    '''      chk.paid(U32.is_le(left, n2), CSize{}, n2, b, left, pd, out)''',
    '''      chk.paid(False{}, CSize{}, n2, b, left, pd, out)'''),
  ('a bare LF ends a chunk line', 'main.bend',
    '''        case XCr{}:
          MvTo{CLf{}, False{}}
        case _:
          MvBad{}
    case CBws{}:''',
    '''        case XCr{}:
          MvTo{CLf{}, False{}}
        case XLf{}:
          MvLine{}
        case _:
          MvBad{}
    case CBws{}:'''),
  ('TE.TE: "chunked, identity" (anything that starts chunked) is chunked', 'main.bend',
    '''  step.te.at(bytes.eq(lows(v), te.lit()), pd, out)''',
    '''  step.te.at(Bytes.starts_with(lows(v), te.lit()), pd, out)'''),
  ('an HTTP/1.0 request is kept alive without asking', 'main.bend',
    '''      pend.req.go(meth, path, body, close || (v10 && Bool.not(ka)), Bool.not(v10), up.asked(ws))''',
    '''      pend.req.go(meth, path, body, close, Bool.not(v10), up.asked(ws))'''),
  ('the spec lets a chunk\'s data end in a bare LF', 'spec.bend',
    '''    case ADataCr{} Eng.XCr{}:
      GTo{ADataLf{}, False{}}''',
    '''    case ADataCr{} Eng.XCr{}:
      GTo{ADataLf{}, False{}}
    case ADataCr{} Eng.XLf{}:
      GTo{ASize0{}, False{}}'''),
]

# what the framing's copy keeps of LAWS.bend: frame_sim's family and
# what its proof stands on
KEEP = {'feed_split', 'bad_absorbs', 'bad_feeds', 'feed_buf_is_feed', 'feed_buf_split',
        'bad_feeds_buf', 'cls_every', 'lower_every', 'frame_sim', 'frame_sim_buf',
        'frame_sim_reads'}

def check(proof):
  r = subprocess.run(['bun', 'bend2/main.ts', proof], cwd=ROOT,
    capture_output=True, text=True, timeout=1800)
  return (r.stdout + r.stderr).strip()

def where(out):
  loc = [l for l in out.split('\n') if l.startswith('Location')]
  return (loc[0] if loc else out.split('\n')[0])[:100]

# the top-level blocks of a file: a line at column 0 and the indented
# lines under it
def blocks(text):
  out, cur = [], []
  for line in text.split('\n'):
    if line and not line[0].isspace() and cur:
      out.append(cur)
      cur = []
    cur.append(line)
  out.append(cur)
  return out

def strip(d):
  laws = open(os.path.join(d, 'LAWS.bend')).read()
  gone, keep = set(), []
  for b in blocks(laws):
    m = re.match(r'law (\w+):', b[0])
    if m and m.group(1) not in KEEP:
      gone.add(m.group(1))
      keep.append([l for l in b if not l.strip() or l.startswith('#')])
    else:
      keep.append(b)
  open(os.path.join(d, 'LAWS.bend'), 'w').write('\n'.join(l for b in keep for l in b))
  proof = open(os.path.join(d, 'PROOF.bend')).read()
  a, z = proof.index('# The world\n# =========\n'), proof.index('# Bytes, bridged\n')
  proof = proof[:a] + proof[z:]
  keep = []
  for b in blocks(proof):
    m = re.match(r'def Laws\.(\w+)\(', b[0])
    if not (m and m.group(1) in gone):
      keep.append(b)
  open(os.path.join(d, 'PROOF.bend'), 'w').write('\n'.join(l for b in keep for l in b))
  return len(gone)

def main():
  bad = 0
  total = len(MUTANTS) + len(FRAMING)
  orig = open(MAIN).read()
  try:
    for name, a, b in MUTANTS:
      if orig.count(a) != 1:
        print('MISSING  %s' % name); bad += 1; continue
      open(MAIN, 'w').write(orig.replace(a, b))
      out = check('demos/io_http_engine/PROOF.bend')
      if out == 'All terms check.':
        print('SURVIVED %s' % name); bad += 1
      else:
        print('KILLED   %s -- %s' % (name, where(out)))
  finally:
    open(MAIN, 'w').write(orig)
  d = tempfile.mkdtemp(prefix='frame_sim_')
  try:
    for f in os.listdir(HERE):
      if f.endswith('.bend'):
        shutil.copy(os.path.join(HERE, f), d)
    n = strip(d)
    out = check(os.path.join(d, 'PROOF.bend'))
    if out != 'All terms check.':
      print('the frame_sim copy (%d laws removed) does not check clean: %s' % (n, where(out)))
      sys.exit(1)
    print('frame_sim alone: %d rule-by-rule laws and vectors removed, the rest checks clean' % n)
    for name, f, a, b in FRAMING:
      path = os.path.join(d, f)
      src = open(path).read()
      if src.count(a) != 1:
        print('MISSING  %s' % name); bad += 1; continue
      open(path, 'w').write(src.replace(a, b))
      out = check(os.path.join(d, 'PROOF.bend'))
      open(path, 'w').write(src)
      if out == 'All terms check.':
        print('SURVIVED %s' % name); bad += 1
      else:
        print('KILLED   %s -- %s' % (name, where(out)))
  finally:
    shutil.rmtree(d, ignore_errors=True)
  print('mutants: %d / %d killed' % (total - bad, total))
  sys.exit(1 if bad else 0)

main()
