#!/usr/bin/env python3
# The laws are not vacuous. Each mutant breaks the server the way a bug
# in HPACK, the framing, the stream state machine, flow control, the
# budgets or the request checks would, and PROOF.bend must then fail,
# naming a law. Each runs in a scratch copy of the tree of its own,
# re-checked from the mutated file on (wire/mutate.py); a clean copy
# checks clean.
#
#   python3 demos/io_http2/mutants.py [-j N] [--shard i/n]   (from the repo root)
import os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, 'wire'))
import mutate as M
HP, FM, CN, MN = (os.path.join(HERE, f) for f in ('hpack.bend', 'frame.bend', 'conn.bend', 'main.bend'))

# (what, file, before, after, the law it breaks: the checker stops at
# the first def that fails, which is that law or a lemma of its proof)
MUTANTS = [
  # HPACK
  ('an integer\'s digits weighed by 127, not 128', HP,
    'Nat.mul(mul, 128n), 1n+k}', 'Nat.mul(mul, 127n), 1n+k}', 'int_rt'),
  ('an integer decoder that takes three continuation bytes, not four', HP,
    'ICont{max, 1n, int.cap()}', 'ICont{max, 1n, 3n}', 'int_rt'),
  ('EOS decoded as a byte', HP,
    '''    case True{}:
      HfBad{}
    case False{}:
      HfAt{root, Bytes.push(acc, sym)}''',
    '''    case True{}:
      HfAt{root, Bytes.push(acc, sym)}
    case False{}:
      HfAt{root, Bytes.push(acc, sym)}''', 'huff_eos'),
  ('a byte\'s bits walked least significant first', HP,
    '''    hf.bit(root, h, bit(c, 128)), bit(c, 64)), bit(c, 32)), bit(c, 16)), bit(c, 8)),
    bit(c, 4)), bit(c, 2)), bit(c, 1))''',
    '''    hf.bit(root, h, bit(c, 1)), bit(c, 2)), bit(c, 4)), bit(c, 8)), bit(c, 16)),
    bit(c, 32)), bit(c, 64)), bit(c, 128))''', 'huff_rt'),
  ('an entry that does not fit is kept, not evicted', HP,
    '''    case True{}:
      Con{e, rest}
    case False{}:
      Nil{}''',
    '''    case True{}:
      Con{e, rest}
    case False{}:
      Con{e, rest}''', 'fit_le'),
  ('a size update taken after a field', HP,
    'Bool.not(any) && Nat.is_le(v, lim.t(lim))', 'Nat.is_le(v, lim.t(lim))', 'refuse_size_late'),
  ('no cap on the decoded list (an HPACK bomb decodes)', HP,
    'field.cap(k, t, out, sz, s2, lim, f, Nat.is_le(s2, lim.l(lim)))',
    'field.cap(k, t, out, sz, s2, lim, f, True{})', 'dec_step'),
  ('a string past the cap is kept', HP,
    'str.start(root, fo, h, t, out, sz, lim, v, Nat.is_le(v, lim.l(lim)))',
    'str.start(root, fo, h, t, out, sz, lim, v, True{})', 'refuse_str_big'),
  ('the encoder\'s static index names the wrong entry', HP,
    '"user-agent", 58n', '"user-agent", 57n', 'static_index'),
  # frames
  ('a frame one byte past the maximum is taken', FM,
    'step.len(Nat.is_lt(max, n), n,', 'step.len(Nat.is_lt(1n+max, n), n,', 'frame_sim'),
  ('a payload read one byte long', FM,
    'Rd{FPay{ty, fl, sid, m, ""}, max, out}', 'Rd{FPay{ty, fl, sid, 1n+m, ""}, max, out}', 'frame_sim'),
  ('a wrong preface byte let through', FM,
    '''    case False{} _:
      Rd{FBad{WPre{}}, max, out}
    case True{} Nil{}:''',
    '''    case False{} _:
      Rd{FPre{t}, max, out}
    case True{} Nil{}:''', 'frame_sim'),
  ('the stream id\'s reserved bit kept', FM,
    'U32.or(U32.shln(U32.and(a, 127), 24n)', 'U32.or(U32.shln(a, 24n)', 'frame_sim'),
  # stream states
  ('DATA taken on a half-closed (remote) stream', CN,
    '''    case SHalf{} _:
      VStream{e.closed()}''',
    '''    case SHalf{} _:
      VOk{}''', 'verdict_rfc'),
  ('DATA taken on an idle stream', CN,
    '''    case SIdle{} _:
      VConn{e.proto()}''',
    '''    case SIdle{} _:
      VOk{}''', 'idle_data'),
  ('an even stream id opens a stream', CN,
    'is.idle(s) && U32.is_zero(U32.and(sid, 1))', 'False{}', 'even_id'),
  ('the highest stream id moved down', CN,
    '''    case True{}:
      sid
    case False{}:
      last''',
    '''    case True{}:
      sid
    case False{}:
      sid''', 'ids_grow'),
  ('a frame from another stream inside a header block', CN,
    'U32.is_eq(ty, 9) && U32.is_eq(sid, bsid)', 'U32.is_eq(ty, 9)', 'cont_only'),
  # flow control
  ('a WINDOW_UPDATE past 2^31-1 taken', CN,
    'sw.fit(w2, Nat.is_le(sw.up(w2), win.max()))', 'sw.fit(w2, True{})', 'win_add'),
  ('DATA past the peer\'s window taken', CN,
    'rw.fit(w, n, Nat.is_le(n, w))', 'rw.fit(w, n, True{})', 'rw_refuse'),
  ('DATA sent past the connection\'s window', CN,
    'Nat.min(sw.up(csw), fmax)', 'fmax', 'data_fits'),
  # budgets
  ('a PING answered for free', CN,
    'ok(cn.w.bud(c, Bud{k, s, r}), Bytes.append(w, f.pong(pay)), rq)',
    'ok(cn.w.bud(c, Bud{1n+k, s, r}), Bytes.append(w, f.pong(pay)), rq)', 'ping_pays'),
  ('a budget refilled past its cap', CN,
    'Nat.min(1n+n, bud.cap())', '1n+n', 'bud_capped'),
  ('no cap on a header block (a CONTINUATION flood)', CN,
    'Nat.is_lt(blk.cap(), size), eoh)', 'False{}, eoh)', 'cont_capped'),
  # requests
  ('an uppercase field name taken', CN,
    '''    case _ True{} _:
      chk.bad(c)''',
    '''    case _ True{} _:
      c''', 'req_upper'),
  ('a Connection field taken', CN,
    'beq(n, "connection") || beq(n, "keep-alive")', 'beq(n, "keep-alive")', 'req_connection'),
  # the server
  ('a connection that is over reads on', MN,
    '''    case C.CW{c, w} True{}:
      L.End{[L.Raw{w}]}''',
    '''    case C.CW{c, w} True{}:
      L.Go{[L.Raw{w}], c}''', 'dead_ends'),
]

def main():
  jobs, shard = M.args()
  bases, res = M.run(lambda: M.tree(('demos/io_http2', 'demos/io_http_engine', 'wire', 'power'), prefix='h2_laws_'),
    'demos/io_http2/PROOF.bend', [(w, os.path.relpath(p, ROOT), b, a) for w, p, b, a, _ in MUTANTS], jobs, shard)
  out = bases['demos/io_http2/PROOF.bend']
  if out != 'All terms check.':
    print('the unmutated proof does not check:\n' + out[:2000])
    sys.exit(1)
  bad = 0
  for what, _, out in res:
    if out is None:
      print('MISSING  %s: the text to mutate is not in its file exactly once' % what)
      bad += 1
      continue
    killed = out != 'All terms check.'
    m = re.search(r'Location: (\S+)', out)
    at = m.group(1) if m else out.splitlines()[0][:60] if out else ''
    print('%s %-62s %s' % ('killed' if killed else 'LIVED ', what, 'at ' + at if killed else ''))
    bad += not killed
  print('%d of %d mutants killed' % (len(res) - bad, len(res)))
  sys.exit(1 if bad else 0)

main()
