#!/usr/bin/env python3
# resp_sim is not vacuous. Each mutant breaks the response reader
# (resp.bend) the way a framing or smuggling bug would -- a second
# framing believed, a bodyless status given a body, a folded line or a
# bare LF taken, a length list or a disagreement let through, a budget
# off by one -- and resp_sim alone must refuse it. They run in a scratch
# copy of wire/ whose http1/LAWS.bend keeps only resp_sim: every vector,
# the classes' laws and the kit's laws are removed with their proofs,
# and so is the block walk's proof, so a kill is resp_sim's and no other
# law's. The copy is checked clean first.
#
#   python3 wire/http1/mutants.py        (from the repo root)
import os, re, shutil, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
WIRE = os.path.dirname(HERE)
ROOT = os.path.dirname(WIRE)
KEEP = {'resp_sim'}

# (what, before, after), each applied to resp.bend once
MUTANTS = [
  ('CL.TE: a Content-Length beside chunked is let through, chunked wins',
    '''    case Some{n}:
      te

def frame(''',
    '''    case Some{n}:
      False{}

def frame('''),
  ('a coding in HTTP/1.0 is decoded, not refused',
    '''      frame.at(frame.two(te, l) || (v10 && te),''',
    '''      frame.at(frame.two(te, l),'''),
  ('a 204 is read for a body',
    '''  head || U32.is_lt(code, 200) || U32.is_eq(code, 204) || U32.is_eq(code, 304)''',
    '''  head || U32.is_lt(code, 200) || U32.is_eq(code, 304)'''),
  ('a 304 is read for a body',
    '''  head || U32.is_lt(code, 200) || U32.is_eq(code, 204) || U32.is_eq(code, 304)''',
    '''  head || U32.is_lt(code, 200) || U32.is_eq(code, 204)'''),
  ('a response to HEAD is read for a body',
    '''  head || U32.is_lt(code, 200) || U32.is_eq(code, 204) || U32.is_eq(code, 304)''',
    '''  U32.is_lt(code, 200) || U32.is_eq(code, 204) || U32.is_eq(code, 304)'''),
  ('an interim 1xx is taken for the final response',
    '''        U32.is_lt(code, 200) && Bool.not(U32.is_eq(code, 101)),''',
    '''        False{},'''),
  ('a 101 is taken for an interim response',
    '''        U32.is_lt(code, 200) && Bool.not(U32.is_eq(code, 101)),''',
    '''        U32.is_lt(code, 200),'''),
  ('obs-fold: a line that starts with a space continues the one before',
    '''    case Lin{h} _:
      P{Bad{}, out}''',
    '''    case Lin{h} KSp{}:
      P{Oth{h}, out}
    case Lin{h} _:
      P{Bad{}, out}'''),
  ('a bare LF ends a field line',
    '''    case Oth{h} KLf{}:
      P{Bad{}, out}''',
    '''    case Oth{h} KLf{}:
      P{Lin{h}, out}'''),
  ('a bare LF ends the status line',
    '''    case SWhy{v10, code} KLf{}:
      P{Bad{}, out}''',
    '''    case SWhy{v10, code} KLf{}:
      P{Lin{head.new(v10, code)}, out}'''),
  ('CL.CL: two lengths that disagree, the first believed',
    '''          len.at(U32.is_eq(n, w), Head{v10, code, Some{w}, te, cl, ka})''',
    '''          len.at(True{}, Head{v10, code, Some{w}, te, cl, ka})'''),
  ('CL.CL: a length list ("5, 5") read as one length',
    '''    case Len{h, n} KHt{}:
      P{LenW{h, n}, out}''',
    '''    case Len{h, n} KHt{}:
      P{LenW{h, n}, out}
    case Len{h, n} KCm{}:
      P{LenW{h, n}, out}'''),
  ('an empty Content-Length read as 0',
    '''    case Len0{h} _:
      P{Bad{}, out}''',
    '''    case Len0{h} KCr{}:
      P{len.cr(e, h, 0), out}
    case Len0{h} _:
      P{Bad{}, out}'''),
  ('a length past the cap let through',
    '''  len.big(U32.is_lt(ask.cap(e), n), h, n)''',
    '''  len.big(False{}, h, n)'''),
  ('TE.TE: "chunked " with a space after it taken for chunked',
    '''    case Te{h, m} KLf{}:
      P{Bad{}, out}''',
    '''    case Te{h, m} KSp{}:
      P{Te{h, m}, out}
    case Te{h, m} KLf{}:
      P{Bad{}, out}'''),
  ('TE.TE: chunked named twice let through',
    '''      te.at(ok && Bool.not(te), Head{v10, code, l, te, cl, ka})''',
    '''      te.at(ok, Head{v10, code, l, te, cl, ka})'''),
  ('a space before the colon skipped',
    '''    case Nam{h, a, b, d} _:
      P{Bad{}, out}''',
    '''    case Nam{h, a, b, d} KSp{}:
      P{Nam{h, a, b, d}, out}
    case Nam{h, a, b, d} _:
      P{Bad{}, out}'''),
  ('a status code past 599 let through',
    '''  Nat.is_eq(k, 3n) && U32.is_le(100, n) && U32.is_le(n, 599)''',
    '''  Nat.is_eq(k, 3n) && U32.is_le(100, n)'''),
  ('a status code of two digits let through',
    '''  Nat.is_eq(k, 3n) && U32.is_le(100, n) && U32.is_le(n, 599)''',
    '''  Nat.is_le(k, 3n) && U32.is_le(n, 599)'''),
  ('HTTP/1.0 taken for HTTP/1.1 (and kept alive)',
    '''      P{ver.sp(done(a), done(b)), out}''',
    '''      P{ver.sp(done(a) || done(b), False{}), out}'''),
  ('HTTP/1.0 without keep-alive kept alive',
    '''      Resp{code, v10, close || (v10 && Bool.not(ka)) || U32.is_eq(code, 101) || delim, body}''',
    '''      Resp{code, v10, close || U32.is_eq(code, 101) || delim, body}'''),
  ('Connection: close unheard',
    '''      Eol{Head{v10, code, l, te, cl || a, ka || b}}''',
    '''      Eol{Head{v10, code, l, te, cl, ka || b}}'''),
  ('a chunk line may spend the whole budget (off by one)',
    '''      chunk.paid(U32.is_le(left, n), h, at, n, got, left)''',
    '''      chunk.paid(U32.is_lt(left, n), h, at, n, got, left)'''),
  ('a chunk\'s data is not followed by its CRLF',
    '''      Chk{h, ADataCr{}, 0, Bytes.push(got, c), left}''',
    '''      Chk{h, ASize0{}, 0, Bytes.push(got, c), left}'''),
  ('a body that runs to the close runs past the cap',
    '''    case 0n:
      Bad{}
    case 1n+q:
      Clo{h, Bytes.push(got, c), q}''',
    '''    case 0n:
      Clo{h, Bytes.push(got, c), 0n}
    case 1n+q:
      Clo{h, Bytes.push(got, c), q}'''),
  ('a length read one byte long',
    '''      Bod{h, Nat.sub(U32.to_nat(n), 1n), ""}''',
    '''      Bod{h, U32.to_nat(n), ""}'''),
  ('what follows the final response is dropped, not kept',
    '''      P{Fin{r, Bytes.push(rest, c)}, out}''',
    '''      P{Fin{r, rest}, out}'''),
]

def check(path):
  r = subprocess.run(['bun', os.path.join(ROOT, 'bend2', 'main.ts'), path],
    capture_output=True, text=True, cwd=ROOT)
  return (r.stdout + r.stderr).strip()

def where(out):
  m = re.search(r'Location: ([\w.]+)', out)
  return m.group(1) if m else out.splitlines()[0] if out else '?'

def strip(d):
  laws = open(os.path.join(d, 'LAWS.bend')).read()
  gone = set()
  def law(m):
    if m.group(1) in KEEP:
      return m.group(0)
    gone.add(m.group(1))
    return ''
  laws = re.sub(r'^law (\w+):\n(?:[ ].*\n|\n(?=[ ]))*', law, laws, flags=re.M)
  open(os.path.join(d, 'LAWS.bend'), 'w').write(laws)
  proof = open(os.path.join(d, 'PROOF.bend')).read()
  a, z = proof.index('# The block walk\n# ==============\n'), proof.index('# The laws, whole\n')
  proof = proof[:a] + proof[z:]
  def pf(m):
    return '' if m.group(1) in gone else m.group(0)
  proof = re.sub(r'^def Laws\.(\w+)\(.*\n(?:[ ].*\n)*', pf, proof, flags=re.M)
  open(os.path.join(d, 'PROOF.bend'), 'w').write(proof)
  return len(gone)

def main():
  bad = 0
  top = tempfile.mkdtemp(prefix='resp_sim_')
  d = os.path.join(top, 'wire', 'http1')
  try:
    shutil.copytree(WIRE, os.path.join(top, 'wire'))
    n = strip(d)
    proof = os.path.join(d, 'PROOF.bend')
    out = check(proof)
    if out != 'All terms check.':
      print('the resp_sim copy (%d laws removed) does not check clean: %s' % (n, out))
      sys.exit(1)
    print('resp_sim alone: %d other laws removed, the rest checks clean' % n)
    path = os.path.join(d, 'resp.bend')
    src = open(path).read()
    for name, a, b in MUTANTS:
      if src.count(a) != 1:
        print('MISSING  %s' % name); bad += 1; continue
      open(path, 'w').write(src.replace(a, b))
      out = check(proof)
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
