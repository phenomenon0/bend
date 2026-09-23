#!/usr/bin/env python3
# The proxy's laws are not vacuous. Each mutant breaks core.bend the way
# a bug would -- the client's raw bytes passed through, a hop-by-hop
# field forwarded, a field the client's Connection named kept, a refused
# stream read on, a request sent unchecked or with a field a framing
# reads, a length that is not the body's; a response sent back
# unchecked, with a body its framing says it has not, with a length or
# a field the check should have stopped, a 101 taken as final, a close
# the client is not told of, a 502 with a body to HEAD -- and PROOF.bend
# must refuse it. Each runs in a scratch copy of the tree the proof imports (the
# proxy, the engine, wire/), checked clean first.
#
#   python3 demos/io_proxy/mutants.py        (from the repo root)
import os, re, shutil, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))

MUTANTS = [
  ('the client\'s raw bytes passed through (forward_canonical, no_smuggle)',
    '''    case Con{t, r}:
      wire.at(fwd(w, t), wire(w, r))''',
    '''    case Con{t, r}:
      match t:
        case Took{raw, r0}:
          Bytes.append(raw, wire(w, r))'''),
  ('TE forwarded (hop_by_hop_removed)',
    '''|| Eng.bytes.eq(n, "te") ''', ''''''),
  ('a response\'s Transfer-Encoding sent back (hop_by_hop_removed_rsp)',
    '''|| Eng.bytes.eq(n, "transfer-encoding") ''', ''''''),
  ('the fields the client\'s Connection named kept (hop_by_hop_removed)',
    '''  is.other(Eng.fld.of(n)) && Bool.not(hop(ns, n)) && Bool.not(own(n))''',
    '''  is.other(Eng.fld.of(n)) && Bool.not(hop.fixed(n)) && Bool.not(own(n))'''),
  ('a refused stream read on, as if a request began (scan_is_spec, refused_not_forwarded)',
    '''    case _ SBad{}:
      done(acc, TBad{})''',
    '''    case _ SBad{}:
      done(acc, TWait{scan.new()})'''),
  ('a request sent unchecked (no_smuggle)',
    '''  Bool.pick(Maybe<&2, Msg>, valid(m), Some{m}, None{})''',
    '''  Some{m}'''),
  ('a field a framing reads let through the check (no_smuggle)',
    '''      full(n) && ok.all(Spec.TName{}, n) && is.other(Eng.fld.of(Eng.lows(n))) && ok.all(Spec.TVal{}, v)''',
    '''      full(n) && ok.all(Spec.TName{}, n) && ok.all(Spec.TVal{}, v)'''),
  ('a Content-Length one more than the body (no_smuggle)',
    '''    case True{}:
      [Field{"content-length", Nat.show(Bytes.len(body))}]''',
    '''    case True{}:
      [Field{"content-length", Nat.show(1n+Bytes.len(body))}]'''),
  ('a response sent back unchecked (rsp_reframed)',
    '''  Bool.pick(Maybe<&2, Rsp>, rvalid(head, code, r), Some{r}, None{})''',
    '''  Some{r}'''),
  ('a body sent after a response that has none by its framing (rsp_reframed)',
    '''Bytes.append("\\r\\n", Bool.pick(Bytes(), bodyless, "", body))''',
    '''Bytes.append("\\r\\n", body)'''),
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

def check(path):
  r = subprocess.run(['bun', os.path.join(ROOT, 'bend2', 'main.ts'), path],
    capture_output=True, text=True, cwd=ROOT)
  return (r.stdout + r.stderr).strip()

def where(out):
  m = re.search(r'Location: ([\w.]+)', out)
  return m.group(1) if m else out.splitlines()[0] if out else '?'

def main():
  bad = 0
  top = tempfile.mkdtemp(prefix='proxy_laws_')
  try:
    for d in ('demos/io_proxy', 'demos/io_http_engine', 'wire'):
      shutil.copytree(os.path.join(ROOT, d), os.path.join(top, d))
    proof = os.path.join(top, 'demos/io_proxy/PROOF.bend')
    core = os.path.join(top, 'demos/io_proxy/core.bend')
    out = check(proof)
    if out != 'All terms check.':
      print('the copy of PROOF.bend does not check clean: %s' % out)
      sys.exit(1)
    for name, a, b in MUTANTS:
      src = open(core).read()
      if src.count(a) != 1:
        print('MISSING  %s' % name); bad += 1; continue
      open(core, 'w').write(src.replace(a, b))
      out = check(proof)
      open(core, 'w').write(src)
      if out == 'All terms check.':
        print('SURVIVED %s' % name); bad += 1
      else:
        print('KILLED   %s -- %s' % (name, where(out)))
  finally:
    shutil.rmtree(top, ignore_errors=True)
  print('mutants: %d / %d killed' % (len(MUTANTS) - bad, len(MUTANTS)))
  sys.exit(1 if bad else 0)

main()
