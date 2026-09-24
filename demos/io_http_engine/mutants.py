#!/usr/bin/env python3
# The laws are not vacuous. Two kinds of mutant, each applied, checked
# and undone:
#
# - the world's: each breaks the loop the way one of the review's bugs
#   did (or would), and PROOF.bend must then fail, naming a law of the
#   world. Applied in place to bend-wire's loop (wire/loop.bend), whose
#   laws PROOF.bend states at the engine's hooks, to main.bend's
#   planner and its files, or to the memo wire/world.bend models.
#
# - the framing's: each breaks the reader (or the spec) the way a
#   smuggling or framing bug would, and must be refused by frame_sim
#   alone. They run in a scratch copy of this directory whose LAWS.bend
#   keeps only frame_sim, frame_sim_buf, frame_sim_reads and the laws
#   their proofs stand on -- every rule-by-rule law and every vector is
#   removed, with its proof, and so are the world's -- so a kill there
#   is frame_sim's and no other law's. The copy (beside a copy of wire/,
#   which it imports) is checked clean first.
#
#   python3 demos/io_http_engine/mutants.py        (from the repo root)
import os, re, shutil, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
LOOP = os.path.join(ROOT, 'wire', 'loop.bend')
MAIN = os.path.join(HERE, 'main.bend')
COND = os.path.join(HERE, 'cond.bend')
WORLD = os.path.join(ROOT, 'wire', 'world.bend')

# the world's mutants: (what, file, before, after). The loops are
# bend-wire's (wire/loop.bend), and their laws are proven there for
# every protocol; PROOF.bend states them at the engine's hooks and must
# refuse each broken loop.
MUTANTS = [
  ('no head deadline: a head out of time is read again', LOOP,
    '''    el, Nat.is_lt(el, U32.to_nat(hdms(srv))))''',
    '''    el, True{})'''),
  ('no batch cap: a reply joins the batch whatever its size', LOOP,
    '''    U32.cmp(U32.from_nat(Bytes.len(acc)), send.cap()))''',
    '''    LT{})'''),
  ('a reply after close: End writes one more reply after its segments', LOOP,
    '''~lsize, s, out, idle(srv)), m =>
            pure(S, put.s(S, m)))''',
    '''~lsize, s, out, idle(srv)), m =>
            bind(Put(S), S, tx(put.s(S, m), big, idle(srv)), m2 =>
              pure(S, put.s(S, m2))))'''),
  ('a queued reply skipped on refusal: the 400 goes out alone', MAIN,
    '''      Ans{answer.flat(acc, [L.Raw{resp.bad()}]), True{}, 0, False{}}''',
    '''      Ans{[L.Raw{resp.bad()}], True{}, 0, False{}}'''),
  ('the accept loop exits on EMFILE', LOOP,
    '''  accept.dead(~M, ~pure, ~bind, ~L, ~sig, l, code, accept.soft(code))''',
    '''  accept.dead(~M, ~pure, ~bind, ~L, ~sig, l, code,
    accept.soft(code) && Bool.not(U32.is_eq(code, 24)))'''),
  ('replies out of order: a reply goes out before the batch it follows', LOOP,
    '''            send.hold(~M, ~pure, ~bind, ~S, ~tx, ms, s, Bytes.append(acc, out)))
''',
    '''            send.hold(~M, ~pure, ~bind, ~S, ~tx, ms, s, Bytes.append(out, acc)))
'''),
  ('a WebSocket reads on after its send failed (as first written)', LOOP,
    '''    case Fail{e}:
      pure(S & Plan<P, U>, (s, Stop{}))
    case Done{u}:
      turn.wr(''',
    '''    case Fail{e}:
      turn.wr(~M, ~pure, ~bind, ~S, ~rx, ~E, ~P, ~U, ~idle, ~uplan, srv, s, wr)
    case Done{u}:
      turn.wr('''),
  ('a silent peer is waited on again, not let go', LOOP,
    '''  match may:
    case None{}:
      (s, Stop{})
    case Some{buf}:
      (s, plan.read(~E, ~P, ~U, ~plan, srv, buf, p))''',
    '''  match may:
    case None{}:
      (s, Wait{p})
    case Some{buf}:
      (s, plan.read(~E, ~P, ~U, ~plan, srv, buf, p))'''),
  ('a file sent by the kernel without its head', LOOP,
    '''      bind(Put(S), Em<S>, tx(s, pre, ms), m =>''',
    '''      bind(Put(S), Em<S>, tx(s, "", ms), m =>'''),
  ('a small file read short is taken as whole', LOOP,
    '''          pure(Em<S>, page.blk(S, m, Nat.is_eq(Bytes.len(bs), U32.to_nat(n))
            && Nat.is_eq(Bytes.len(part), U32.to_nat(len))))))''',
    '''          pure(Em<S>, page.blk(S, m, True{}))))'''),
  ('a small file\'s part that the read did not hold is taken as whole', LOOP,
    '''          pure(Em<S>, page.blk(S, m, Nat.is_eq(Bytes.len(bs), U32.to_nat(n))
            && Nat.is_eq(Bytes.len(part), U32.to_nat(len))))))''',
    '''          pure(Em<S>, page.blk(S, m, Nat.is_eq(Bytes.len(bs), U32.to_nat(n))))))'''),
  ('a small file sent without its head', LOOP,
    '''        bind(Put(S), Em<S>, tx(s, Bytes.append(pre, part), ms), m =>''',
    '''        bind(Put(S), Em<S>, tx(s, part, ms), m =>'''),
  ('a small file\'s part cut from its first byte, not from the range\'s', LOOP,
    '''      +part = Bytes.slice(bs, U32.to_nat(off), U32.to_nat(len))''',
    '''      +part = Bytes.slice(bs, 0n, U32.to_nat(len))'''),
  ('a file sent from the wrong place: sendfile from a byte after its part', LOOP,
    '''fsend(s, f, off, len, ms), g =>''',
    '''fsend(s, f, (off + 1 : U32), len, ms), g =>'''),
  ('a file sent a byte short of the length its head promised', LOOP,
    '''fsend(s, f, off, len, ms), g =>''',
    '''fsend(s, f, off, (len - 1 : U32), ms), g =>'''),
  ('a sendfile that failed or came up short is taken as whole', LOOP,
    '''    pure(Em<S>, Em{s, "", Result.is_done(&1, &1, U32 & String, Unit, r)}))''',
    '''    pure(Em<S>, Em{s, "", True{}}))'''),
  ('a file whose head did not go out is sent all the same', LOOP,
    '''    case Fail{e}:
      bind(Unit, Em<S>, fclose(f), u => pure(Em<S>, Em{s, "", False{}}))
    case Done{u}:''',
    '''    case Fail{e}:
      bind(S & F & Result<&1, &1, U32 & String, Unit>, Em<S>, fsend(s, f, 0, n, ms), g =>
        page.fsent(~M, ~pure, ~bind, ~S, ~F, ~fclose, g))
    case Done{u}:'''),
  # the file a path names: page_is_spec holds the fast path to
  # fnames.of, and file_head_is_built the heads kept ready to the built
  ('the fast path serves a dotfile', MAIN,
    '''      fname.byte(c) && Bool.not(U32.is_eq(c, 46))''',
    '''      fname.byte(c)'''),
  ('the fast path takes an empty segment ("//")', MAIN,
    '''      fname.byte(c) && Bool.not(U32.is_eq(c, 46))''',
    '''      (U32.is_eq(c, 47) || fname.byte(c)) && Bool.not(U32.is_eq(c, 46))'''),
  ('the fast path takes a trailing "/"', MAIN,
    '''    case SNil{}:
      Bool.not(st)''',
    '''    case SNil{}:
      True{}'''),
  ('the fast path keeps the path\'s "/"', MAIN,
    '''L.Page{root, Bytes.drop(path, 1n),''',
    '''L.Page{root, path,'''),
  ('the fast path reads a type across a "/"', MAIN,
    '''ext.buf(r, ext.step(cur, c, U32.is_eq(c, 46) || U32.is_eq(c, 47)))''',
    '''ext.buf(r, ext.step(cur, c, U32.is_eq(c, 46)))'''),
  ('a head kept ready names another type', MAIN,
    '''  Mime{"png", "image/png",
    "HTTP/1.1 200 OK\\r\\ncontent-type: image/png\\r\\ncontent-length: "}''',
    '''  Mime{"png", "image/png",
    "HTTP/1.1 200 OK\\r\\ncontent-type: image/jpeg\\r\\ncontent-length: "}'''),
  # File.get_under's memo, as wire/world.bend models it
  ('the memo keeps every answer, past its cap', WORLD,
    '''  memo.take(Con{Memo{key, now, got}, ms}, memo.cap())''',
    '''  memo.take(Con{Memo{key, now, got}, ms}, 1n+memo.cap())'''),
  ('the memo answers for a key it was not asked', WORLD,
    '''      memo.find.at(same(k, key) && Nat.is_lt(now, Nat.add(at, ttl)), got,''',
    '''      memo.find.at(Nat.is_lt(now, Nat.add(at, ttl)), got,'''),
  # cond.bend: the conditional and range decision, its heads, the date
  ('a 304 carries the file after its head', COND,
    '''      L.Fr{hd.same(mt32, n32), 0, 0}''',
    '''      L.Fr{hd.same(mt32, n32), 0, n32}'''),
  ('a 304 states a Content-Length', COND,
    '''  Bytes.append(vals(Bytes.append("", "HTTP/1.1 304 Not Modified"), mt32, n32), ka())''',
    '''  Bytes.append(vals(Bytes.append("", "HTTP/1.1 304 Not Modified\\r\\ncontent-length: 0"), mt32, n32), ka())'''),
  ('If-Modified-Since read though If-None-Match is present', COND,
    '''    case Some{v}:
      Bool.pick(Got, tags.hit(v, etag.of(mt32, n32), False{}), Same{}, later)''',
    '''    case Some{v}:
      match ims:
        case None{}:
          Bool.pick(Got, tags.hit(v, etag.of(mt32, n32), False{}), Same{}, later)
        case Some{w}:
          ims.go(date.read(w), U32.to_nat(mt32),
            Bool.pick(Got, tags.hit(v, etag.of(mt32, n32), False{}), Same{}, later))'''),
  ('an unreadable If-Modified-Since is a 304', COND,
    '''def ims.go(m: Maybe<&2, Nat>, +mt: Nat, later: Got) -> Got:
  match m:
    case None{}:
      later''',
    '''def ims.go(m: Maybe<&2, Nat>, +mt: Nat, later: Got) -> Got:
  match m:
    case None{}:
      Same{}'''),
  ('If-Unmodified-Since is never read', COND,
    '''          pre.ius(date.read(v), U32.to_nat(mt32))''',
    '''          True{}'''),
  ('If-Match compared weakly', COND,
    '''      tags.hit(v, etag.of(mt32, n32), True{})''',
    '''      tags.hit(v, etag.of(mt32, n32), False{})'''),
  ('If-Range ignored: a stale validator still gets the range', COND,
    '''      Bool.pick(Got, ir.ok(v, mt32, n32), ranged(rg.parse(rg), n), Full{})''',
    '''      ranged(rg.parse(rg), n)'''),
  ('a last-pos past the end is one byte past it', COND,
    '''          want.from(Nat.is_lt(a, n) && Nat.is_le(a, b2), a, Nat.min(b2, Nat.sub(n, 1n)))''',
    '''          want.from(Nat.is_lt(a, n) && Nat.is_le(a, b2), a, Nat.min(b2, n))'''),
  ('a first-pos at the end is satisfiable', COND,
    '''          want.from(Nat.is_lt(a, n), a, Nat.sub(n, 1n))''',
    '''          want.from(Nat.is_le(a, n), a, Nat.sub(n, 1n))'''),
  ('a suffix range one byte too long', COND,
    '''          Span{Nat.sub(m, Nat.min(j, m)), m}''',
    '''          Span{Nat.sub(m, Nat.min(1n+j, m)), m}'''),
  ('a range whose first-pos is past its last-pos is read', COND,
    '''      Bool.pick(Rs & List<&2, Spec>, Nat.is_le(a, b), (RAfter{}, Con{From{a, Some{b}}, sp}),
        (RBad{}, sp))''',
    '''      (RAfter{}, Con{From{a, Some{b}}, sp})'''),
  ('two ranges served as the first', COND,
    '''    case 1n+q:
      Full{}''',
    '''    case 1n+q:
      (a, b) = ab
      Part{a, b}'''),
  ('a 206 sends its part from the file\'s first byte', COND,
    '''      L.Fr{hd.part(ct, a, b, n32, mt32), U32.from_nat(a), U32.from_nat(Nat.sub(1n+b, a))}''',
    '''      L.Fr{hd.part(ct, a, b, n32, mt32), 0, U32.from_nat(Nat.sub(1n+b, a))}'''),
  ('Content-Range names the byte after the last', COND,
    '''  ["\\r\\ncontent-range: bytes ", num(a), "-", num(b), "/", num(n)]''',
    '''  ["\\r\\ncontent-range: bytes ", num(a), "-", num(1n+b), "/", num(n)]'''),
  ('the weekday a day late', COND,
    '''  Con{nth(wkc(), Nat.mod(Nat.add(4n, days), 7n)),''',
    '''  Con{nth(wkc(), Nat.mod(Nat.add(5n, days), 7n)),'''),
  ('every fourth year a leap year', COND,
    '''    case True{}:
      leap.c(y)''',
    '''    case True{}:
      True{}'''),
  ('a date read back a second late', COND,
    '''      Some{Nat.add(Nat.mul(Nat.add(Nat.mul(Nat.add(Nat.mul(days, 24n), h), 60n), mi), 60n), x)}''',
    '''      Some{Nat.add(Nat.mul(Nat.add(Nat.mul(Nat.add(Nat.mul(days, 24n), h), 60n), mi), 60n), 1n+x)}'''),
  ('the entity-tag\'s hex digits read three bits apart, not four', COND,
    '''  U32.and(U32.shrn(x, Nat.mul(4n, g)), 15)''',
    '''  U32.and(U32.shrn(x, Nat.mul(3n, g)), 15)'''),
  ('the entity-tag drops a leading digit that is not zero', COND,
    '''  U32.is_lt(0, nib(x, Nat.sub(g, 1n))) || Nat.is_le(g, 1n)''',
    '''  U32.is_lt(1, nib(x, Nat.sub(g, 1n))) || Nat.is_le(g, 1n)'''),
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
    '''      pend.req.go(meth, path, body, close || (v10 && Bool.not(ka)), Bool.not(v10), up.asked(ws), hd.of(hx, v10))''',
    '''      pend.req.go(meth, path, body, close, Bool.not(v10), up.asked(ws), hd.of(hx, v10))'''),
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
  origs = {f: open(f).read() for f in (LOOP, MAIN, WORLD, COND)}
  try:
    for name, f, a, b in MUTANTS:
      orig = origs[f]
      if orig.count(a) != 1:
        print('MISSING  %s' % name); bad += 1; continue
      open(f, 'w').write(orig.replace(a, b))
      out = check('demos/io_http_engine/PROOF.bend')
      open(f, 'w').write(orig)
      if out == 'All terms check.':
        print('SURVIVED %s' % name); bad += 1
      else:
        print('KILLED   %s -- %s' % (name, where(out)))
  finally:
    for f, orig in origs.items():
      open(f, 'w').write(orig)
  top = tempfile.mkdtemp(prefix='frame_sim_')
  d = os.path.join(top, 'demos', 'io_http_engine')
  try:
    os.makedirs(d)
    shutil.copytree(os.path.join(ROOT, 'wire'), os.path.join(top, 'wire'))
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
    shutil.rmtree(top, ignore_errors=True)
  print('mutants: %d / %d killed' % (total - bad, total))
  sys.exit(1 if bad else 0)

main()
