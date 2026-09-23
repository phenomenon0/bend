#!/usr/bin/env python3
# The WebSocket client's laws are not vacuous. Each mutant breaks the
# client (net/ws_frame.bend, net/ws_hs.bend) as a real bug would -- a
# masked server frame or a reserved bit let through, a long ping read,
# text not held to UTF-8, a frame sent unmasked or masked with a key
# that does not turn, the Accept or the Upgrade or the Connection not
# checked, an orphan continuation or a message inside another taken, a
# bad close code taken, the cap not held, a ping not answered, the
# server's end reading as the client's -- and net/ws_proof.bend must
# refuse every one. Each runs in a scratch copy of what the proof
# imports, and the copy is checked clean first.
#
#   python3 net/ws_mutants.py        (from the repo root)
import os, shutil, subprocess, sys, tempfile
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
FILES = ['net/ws_frame.bend', 'net/ws_hs.bend', 'net/ws_laws.bend', 'net/ws_proof.bend',
  'demos/io_http_engine/ws.bend', 'demos/io_http_engine/sha1.bend', 'demos/io_http_engine/b64.bend',
  'wire/reader.bend']

F, H = 'net/ws_frame.bend', 'net/ws_hs.bend'

# (what, file, before, after)
MUTANTS = [
  ('a masked server frame is read', F,
    '''      c.len.go(cap, op, U32.and(b, 127), U32.is_eq(U32.and(b, 128), 128),''',
    '''      c.len.go(cap, op, U32.and(b, 127), False{},'''),
  ('a ping of 126 bytes is read', F,
    '''        c.ctl(op) && U32.is_lt(125, U32.and(b, 127)), out)''',
    '''        c.ctl(op) && U32.is_lt(126, U32.and(b, 127)), out)'''),
  ('a reserved bit is let through', F,
    '''    case Cli{cap}:
      c.op.go(U32.and(b, 15), U32.is_zero(U32.and(b, 112)) && c.known(U32.and(b, 15)),''',
    '''    case Cli{cap}:
      c.op.go(U32.and(b, 15), c.known(U32.and(b, 15)),'''),
  ('text is not held to UTF-8', F,
    '''      whole.text(body, Ws.utf8(body))''',
    '''      whole.text(body, True{})'''),
  ('a client frame goes out without the mask bit', F,
    '''    Con{U32.or(128, len7(n)), List.append''',
    '''    Con{len7(n), List.append'''),
  ('the mask does not turn: every byte xored with the same key byte', F,
    '''      SCon{Chr{U32.xor(c, Ws.key.of(m))}, mask(t, Ws.rot(m))}''',
    '''      SCon{Chr{U32.xor(c, Ws.key.of(m))}, mask(t, m)}'''),
  ('an orphan continuation is taken for a message', F,
    '''    case True{} _:
      Ax{Idle{}, Refuse{1002}}
    case False{} True{}:
      first(''',
    '''    case True{} _:
      Ax{Idle{}, whole(body, False{})}
    case False{} True{}:
      first('''),
  ('a new message inside a fragmented one is taken', F,
    '''    case False{}:
      Ax{Idle{}, Refuse{1002}}
    case True{}:
      +n2''',
    '''    case False{}:
      Ax{Idle{}, whole(body, U32.is_eq(op, 1))}
    case True{}:
      +n2'''),
  ('a close code no peer may send (1005) is taken', F,
    '''          close.two(code, u, Ws.close.code.ok(code), Ws.utf8(u))''',
    '''          close.two(code, u, U32.is_lt(999, code), Ws.utf8(u))'''),
  ('a frame past the cap is read', F,
    '''      c.fits(op, n, out, U32.is_lt(cap, n))''',
    '''      c.fits(op, n, out, False{})'''),
  ('fragments are joined past the cap', F,
    '''U32.is_lt(cap, n2) || U32.is_lt(n2, n))''',
    '''U32.is_lt(n2, n))'''),
  ('a ping is not answered', F,
    '''    case False{} True{}:
      Pong{body}''',
    '''    case False{} True{}:
      Skip{}'''),
  ("the server's end reads fragments, as the client's does", F,
    '''    case Srv{}:
      Ws.step.op(b)''',
    '''    case Srv{}:
      c.op.go(U32.and(b, 15), U32.is_zero(U32.and(b, 112)) && c.known(U32.and(b, 15)),
        U32.is_eq(U32.and(b, 128), 128))'''),
  ('the Accept is not checked', H,
    '''          j.acc1(offered, proto, ext, String.eq(a, want))''',
    '''          j.acc1(offered, proto, ext, True{})'''),
  ('the Upgrade is not checked', H,
    '''  j.up.go(want, offered, U32.is_eq(up, 1) && upok, conn, acc, ext, proto)''',
    '''  j.up.go(want, offered, True{}, conn, acc, ext, proto)'''),
  ('Connection: Upgrade is not checked', H,
    '''        conn || (String.eq(n, "connection") && has(toks(low(v)), "upgrade")),''',
    '''        True{},'''),
  ('an extension the client never offered is taken', H,
    '''    case True{}:
      Fail{HExtension{}}''',
    '''    case True{}:
      j.proto(offered, proto)'''),
]


def check(top):
  r = subprocess.run(['bun', os.path.join(ROOT, 'bend2', 'main.ts'), os.path.join(top, 'net', 'ws_proof.bend')],
    capture_output=True, text=True, timeout=900)
  return (r.stdout + r.stderr).strip()


def copy(tag):
  top = tempfile.mkdtemp(prefix='ws_mut_%s_' % tag)
  for f in FILES:
    os.makedirs(os.path.dirname(os.path.join(top, f)), exist_ok=True)
    shutil.copy(os.path.join(ROOT, f), os.path.join(top, f))
  return top


def one(i):
  what, f, before, after = MUTANTS[i]
  top = copy(str(i))
  try:
    p = os.path.join(top, f)
    src = open(p).read()
    if src.count(before) != 1:
      return (what, 'STALE (the text to break is not there once)')
    open(p, 'w').write(src.replace(before, after))
    out = check(top)
    if out == 'All terms check.':
      return (what, 'survived')
    # a kill counts only when a law refuses it, not a parse or a type error
    law = [l for l in out.split('\n') if l.startswith('Location: ws_laws.')]
    return (what, ('killed by ' + law[0].split('.', 1)[1]) if law else 'ERROR ' + out[:300].replace('\n', ' '))
  finally:
    shutil.rmtree(top, ignore_errors=True)


def main():
  top = copy('clean')
  try:
    out = check(top)
  finally:
    shutil.rmtree(top, ignore_errors=True)
  if out != 'All terms check.':
    print('the clean copy does not check:\n' + out[:2000])
    sys.exit(1)
  with ThreadPoolExecutor(max_workers=int(os.environ.get('JOBS', '4'))) as ex:
    res = list(ex.map(one, range(len(MUTANTS))))
  bad = 0
  for what, verdict in res:
    print('%s: %s' % (what, verdict))
    bad += not verdict.startswith('killed')
  print('%d / %d mutants killed' % (len(res) - bad, len(res)))
  sys.exit(1 if bad else 0)


if __name__ == '__main__':
  main()
