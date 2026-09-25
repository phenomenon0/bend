#!/usr/bin/env python3
# The proxy's laws are not vacuous. Each mutant breaks core.bend the way
# a bug would -- the client's bytes passed through, a hop-by-hop
# field forwarded, a field the client's Connection named kept, a refused
# stream read on, a request sent unchecked or with a field a framing
# reads, a length that is not the body's; a response sent back
# unchecked, with a body its framing says it has not, with a length or
# a field the check should have stopped, a 101 taken as final, a close
# the client is not told of, a 502 with a body to HEAD -- and PROOF.bend
# must refuse it. Each runs in a scratch copy of the tree the proof
# imports (the proxy, the engine, wire/, power/), where the engine's own proof, which the proxy's
# uses (frame_sim, feed_buf_is_feed, bad_feeds, ...), is replaced by its statements
# left open: the copy then checks to exactly its count of open holes, and a
# mutant that the proxy's proof refuses shows an error instead. (The laws
# hold step checks PROOF.bend whole, the engine's proof included.) Each
# mutant has a copy of its own, re-checked from core.bend on
# (wire/mutate.py's seeded check).
#
#   python3 demos/io_proxy/mutants.py [-j N] [--shard i/n]   (from the repo root)
import os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, 'wire'))
import mutate as M

MUTANTS = [
  ('the client\'s bytes passed through, not rebuilt (forward_canonical, no_smuggle)',
    '''    case Con{t, r}:
      wire.at(fwd(w, t), wire(w, r))''',
    '''    case Con{t, r}:
      match t:
        case Eng.Req{meth, path, body, close, ws, key, hd}:
          Bytes.append(body, wire(w, r))'''),
  ('TE forwarded (hop_by_hop_removed)',
    '''|| Eng.bytes.eq(n, "te") ''', ''''''),
  ('a response\'s Transfer-Encoding sent back (hop_by_hop_removed_rsp)',
    '''|| Eng.bytes.eq(n, "transfer-encoding") ''', ''''''),
  ('the fields the client\'s Connection named kept (hop_by_hop_removed)',
    '''  is.other(Eng.fld.of(n)) && Bool.not(hop(ns, n)) && Bool.not(own(n))''',
    '''  is.other(Eng.fld.of(n)) && Bool.not(hop.fixed(n)) && Bool.not(own(n))'''),
  ('a refused stream read on, as if a request began (scan_is_spec, refused_not_forwarded)',
    '''    case Eng.Bad{}:
      TBad{}''',
    '''    case Eng.Bad{}:
      TWait{scan.new()}'''),
  ('a request sent unchecked (no_smuggle)',
    '''  Bool.pick(Maybe<&2, Msg>, valid(m), Some{m}, None{})''',
    '''  Some{m}'''),
  ('a field a framing reads let through the check (no_smuggle)',
    '''      full(n) && ok.all(Spec.TName{}, n) && is.other(Eng.fld.of(Eng.lows(n))) && ok.all(Spec.TVal{}, v)''',
    '''      full(n) && ok.all(Spec.TName{}, n) && ok.all(Spec.TVal{}, v)'''),
  ('a Content-Length one more than the body (no_smuggle)',
    '''    case True{}:
      [Wr.Field{"content-length", Nat.show(Bytes.len(body))}]''',
    '''    case True{}:
      [Wr.Field{"content-length", Nat.show(1n+Bytes.len(body))}]'''),
  ('a response sent back unchecked (rsp_reframed)',
    '''  Bool.pick(Maybe<&2, Rsp>, rvalid(head, code, r), Some{r}, None{})''',
    '''  Some{r}'''),
  ('a body sent after a response that has none by its framing (rsp_reframed)',
    '''"\\r\\n"), Bool.pick(Bytes(), bodyless, "", body))''',
    '''"\\r\\n"), body)'''),
  ('the check lets a length that is not the body\'s through (rsp_reframed)',
    '''(same(U32.is_zero(n), String.is_empty(body)) && Nat.is_eq(U32.to_nat(n), Bytes.len(body))))''',
    '''(same(U32.is_zero(n), String.is_empty(body)) && True{}))'''),
  ('the check lets a response field its framing reads through (rsp_reframed)',
    '''full(n) && rok.all(RS.TName{}, n) && ris.other(RS.field(RS.lows(Bytes.to_list(n)))) && rok.all(RS.TVal{}, v)''',
    '''full(n) && rok.all(RS.TName{}, n) && rok.all(RS.TVal{}, v)'''),
  ('a 101 sent back as a final response (rsp_reframed)',
    '''&& Bool.not(U32.is_lt(code, 200)) && Bool.not(U32.is_eq(code, 101))''',
    '''&& Bool.not(U32.is_lt(code, 200))'''),
  ('no Connection: close on a connection the proxy closes (rsp_reframed)',
    '''    case True{}:
      "close"''',
    '''    case True{}:
      ""'''),
  ('the proxy\'s own 502 sent with a body to HEAD (rsp_reframed)',
    '''"\\r\\nconnection: close\\r\\n\\r\\n", Bool.pick(Bytes(), head, "", body)''',
    '''"\\r\\nconnection: close\\r\\n\\r\\n", body'''),
]

def where(out):
  m = re.search(r'Location: ([\w.]+)', out)
  return m.group(1) if m else out.splitlines()[0] if out else '?'

# the engine's laws the proxy's proof uses, stated and left open
OPEN = '''import Base
import ../io_http_engine/LAWS.bend as EL
import ../io_http_engine/main.bend as Eng
import ../io_http_engine/spec.bend as Spec

def EL.frame_sim(bs):
  ?TODO

def EL.feed_split(a, b, p):
  ?TODO

def EL.feed_buf_is_feed(b, p):
  ?TODO

def EL.cls_every(c):
  ?TODO

def EL.lower_every(c):
  ?TODO

def EL.field_by_bytes(k):
  ?TODO

def EL.bad_feeds(s, pd, out):
  ?TODO

def br.lows(s: Bytes()) -> {Spec.lows(s) == Eng.lows(s) : Bytes()}:
  ?TODO
'''

def tree():
  top = M.tree(('demos/io_proxy', 'demos/io_http_engine', 'wire', 'power'), prefix='proxy_laws_')
  proof = os.path.join(top, 'demos/io_proxy/PROOF.bend')
  open(os.path.join(top, 'demos/io_proxy/open.bend'), 'w').write(OPEN)
  src = open(proof).read()
  imp = 'import ../io_http_engine/PROOF.bend as EP\n'
  if src.count(imp) != 1:
    print('PROOF.bend does not import the engine proof as EP'); sys.exit(1)
  open(proof, 'w').write(src.replace(imp, 'import ./open.bend as EP\n'))
  return top

def main():
  jobs, shard = M.args()
  bases, res = M.run(tree, 'demos/io_proxy/PROOF.bend',
    [(name, 'demos/io_proxy/core.bend', a, b) for name, a, b in MUTANTS], jobs, shard)
  base = bases['demos/io_proxy/PROOF.bend']
  if not re.fullmatch(r'Error: \d+ TODOs found\.\nThe code is incomplete, and not a valid proof yet\.', base):
    print('the copy of PROOF.bend does not check clean: %s' % base)
    sys.exit(1)
  bad = 0
  for name, _, out in res:
    if out is None:
      print('MISSING  %s' % name); bad += 1
    elif out == base:
      print('SURVIVED %s' % name); bad += 1
    else:
      print('KILLED   %s -- %s' % (name, where(out)))
  print('mutants: %d / %d killed' % (len(res) - bad, len(res)))
  sys.exit(1 if bad else 0)

main()
