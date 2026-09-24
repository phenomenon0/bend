#!/usr/bin/env python3
# The WebSocket client's laws are not vacuous. Each mutant breaks the
# client (net/ws_frame.bend, net/ws_hs.bend) as a real bug would -- a
# masked server frame or a reserved bit let through, a long ping read,
# text not held to UTF-8, a frame sent unmasked or masked with a key
# that does not turn, the Accept or the Upgrade or the Connection not
# checked, an orphan continuation or a message inside another taken, a
# bad close code taken, the cap not held, a ping not answered, the
# server's end reading as the client's -- and, at the server's end
# (net/ws_server.bend), an unmasked client frame read, a server frame
# masked, the cap not held, a read's messages lost or assembled from
# scratch, a close answered twice or written after, a ping not answered,
# the key or the method not checked, a 200 for a request that did not
# ask, the Accept or Connection: Upgrade wrong, a subprotocol not
# offered named -- and net/ws_proof.bend must refuse every one. Each
# runs in a scratch copy of what the proof imports, and the copy is
# checked clean first.
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
    '''      c.len.go(cap, op, U32.and(b, 127), U32.is_eq(U32.and(b, 128), 128),
        c.ctl(op) && U32.is_lt(125, U32.and(b, 127)), out)''',
    '''      c.len.go(cap, op, U32.and(b, 127), U32.is_eq(U32.and(b, 128), 128),
        c.ctl(op) && U32.is_lt(126, U32.and(b, 127)), out)'''),
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

  # the server's end (net/ws_server.bend)
  ('the server reads an unmasked client frame', F,
    '''      s.len.go(cap, op, U32.and(b, 127), U32.is_eq(U32.and(b, 128), 128),''',
    '''      s.len.go(cap, op, U32.and(b, 127), True{},'''),
  ('the server sets the mask bit on its frames', F,
    '''Con{U32.and(len7(n), 127), len.ext(n)}''',
    '''Con{U32.or(len7(n), 128), len.ext(n)}'''),
  ('the server reads a frame past its cap', F,
    '''      s.fits(op, n, out, U32.is_lt(cap, n))''',
    '''      s.fits(op, n, out, False{})'''),
  ('each read is assembled from scratch', F,
    '''w2 => a2 => s.reads.go(cap, t, w2, a2))''',
    '''w2 => a2 => s.reads.go(cap, t, w2, Idle{}))'''),
  ("a read's messages are lost when the next read comes", F,
    '''      List.append(&2, Act, xs, go(w, a))''',
    '''      go(w, a)'''),
  ("the peer's close is answered after this end's own", F,
    '''  match sent:
    case True{}:
      None{}''',
    '''  match sent:
    case True{}:
      match x:
        case Bye{code, reason}:
          Some{WClose{code}}
        case _:
          None{}'''),
  ('the connection writes on after a close', F,
    '''      s.put(s.out(sent, x), Bool.pick(List<&2, Wr>, s.stops(x), [], s.writes(sent, t)))''',
    '''      s.put(s.out(sent, x), s.writes(sent, t))'''),
  ('the server answers no ping', F,
    '''        case Pong{body}:
          Some{WPong{body}}''',
    '''        case Pong{body}:
          None{}'''),
  ("the server's key is not checked", H,
    '''  s.check.at(asked, get && asked && key.ok(key))''',
    '''  s.check.at(asked, get && asked)'''),
  ('the server upgrades a request that is not a GET', H,
    '''  s.check.at(asked, get && asked && key.ok(key))''',
    '''  s.check.at(asked, asked && key.ok(key))'''),
  ('a request that did not ask is answered 200', H,
    '''      Some{Bool.pick(U32, asked, 400, 426)}''',
    '''      Some{Bool.pick(U32, asked, 400, 200)}'''),
  ("the server's Accept is the key itself", H,
    '''    ++ expect(key) ++ "\\r\\n" ++ s.proto.line(p) ++ "\\r\\n"''',
    '''    ++ key ++ "\\r\\n" ++ s.proto.line(p) ++ "\\r\\n"'''),
  ('the 101 leaves out Connection: Upgrade', H,
    '''Upgrade: websocket\\r\\nConnection: Upgrade\\r\\nSec-WebSocket-Accept: "
    ++ expect(key)''',
    '''Upgrade: websocket\\r\\nSec-WebSocket-Accept: "
    ++ expect(key)'''),
  ('a subprotocol the client did not offer is named', H,
    '''  Bool.pick(Bytes(), has(offered, proto) && Bool.not(String.is_empty(proto)), proto, "")''',
    '''  Bool.pick(Bytes(), Bool.not(String.is_empty(proto)), proto, "")'''),
]


# each lemma of ws_proof.bend, and the law it is on the way to: the
# next law proven after it
def lemmas():
  out, pend = {}, []
  for l in open(os.path.join(HERE, 'ws_proof.bend')):
    if l.startswith('def '):
      name = l[4:].split('(', 1)[0]
      if name.startswith('Laws.'):
        for p in pend:
          out[p] = name[5:]
        pend = []
      else:
        pend.append(name)
  return out


LEMMAS = lemmas()


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
    # a kill counts only when a law refuses it, or the proof of one (a
    # lemma of ws_proof.bend on the way to it), not a parse or a type
    # error in the code
    locs = [l[len('Location: '):] for l in out.split('\n') if l.startswith('Location: ')]
    if locs and locs[0].startswith('ws_laws.'):
      return (what, 'killed by ' + locs[0].split('.', 1)[1])
    if locs and locs[0] in LEMMAS:
      return (what, 'killed by %s (its lemma %s)' % (LEMMAS[locs[0]], locs[0]))
    return (what, 'ERROR ' + out[:300].replace('\n', ' '))
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
