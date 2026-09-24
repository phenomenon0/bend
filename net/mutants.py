#!/usr/bin/env python3
# bend-net's laws are not vacuous. Each mutant breaks net/ as a real bug
# would -- a read scanned from a fresh reader, a header value left
# untrimmed (or trimmed at one end only), a path that keeps its query;
# a response check that lets any name or any value through, a status
# line that lies, a response that failed the check written anyway, the
# length unchecked or read wrong a digit at a time; a router
# that skips a hit, counts routes wrong, lists a method twice or one of
# a route that does not match; a pool that takes back a connection its
# response closed; a redirect that keeps credentials, forgets a cookie,
# or sends once more past its cap; percent-escapes and URLs read wrong;
# a streamed body read from past a read's first byte, a read dropped, a
# length counted one too many, a chunked body given a budget of its own,
# a reader that keeps the body instead of handing it on, a read kept
# whatever came after the body or those bytes not counted, a connection
# that goes on before its body ended or without the bytes after it --
# and net/PROOF.bend must refuse every one. Each runs in a scratch
# copy of the tree the proof imports, where bend-proxy's proof (which
# net/'s uses: rr.h, u32.eq, the list lemmas, and scan_is_spec and
# frames_agree through them) is replaced by its statements left open:
# the copy checks to exactly its count of open holes, and a mutant the
# proof refuses shows an error instead. (The laws hold step checks
# net/PROOF.bend whole, bend-proxy's proof included.)
#
#   python3 net/mutants.py        (from the repo root)
import os, re, shutil, subprocess, sys, tempfile
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
DIRS = ['net', 'wire', 'demos/io_http_engine', 'demos/io_proxy', 'power']

H, S, C, U = 'net/http.bend', 'net/server.bend', 'net/client.bend', 'net/url.bend'
B = 'net/stream.bend'

# (what, file, before, after)
MUTANTS = [
  ('each read scanned from a fresh reader (handler_framed)', S,
    '''def scan(+bs: Bytes(), sc: X.Scan) -> X.Scanned:
  X.scan(bs, sc)''',
    '''def scan(+bs: Bytes(), sc: X.Scan) -> X.Scanned:
  X.scan(bs, X.scan.new())'''),
  ('the first byte of every read dropped (handler_framed)', S,
    '''def scan(+bs: Bytes(), sc: X.Scan) -> X.Scanned:
  X.scan(bs, sc)''',
    '''def scan(+bs: Bytes(), sc: X.Scan) -> X.Scanned:
  X.scan(String.drop(bs, 1n), sc)'''),
  ('a header value handed on untrimmed (handler_framed)', H,
    '''          Con{Header{n, trim.fast(v)}, fields.of(t)}''',
    '''          Con{Header{n, v}, fields.of(t)}'''),
  ('a value that ends in a blank taken for trimmed (handler_framed)', H,
    '''  trim.at(X.ows(Bytes.get(v, 0n)) || X.ows(Bytes.get(v, Nat.sub(Bytes.len(v), 1n))), v)''',
    '''  trim.at(X.ows(Bytes.get(v, 0n)), v)'''),
  ('the path keeps the query (handler_framed)', H,
    '''  (String.take(t, i), String.drop(t, 1n+i))''',
    '''  (t, String.drop(t, 1n+i))'''),
  ('the fast check takes any field name (respond_framed)', H,
    '''          (known.has(n, known()) && X.all.in(v, 32, 127)) && fields.fast(t)''',
    '''          X.all.in(v, 32, 127) && fields.fast(t)'''),
  ('the fast check does not scan a value (respond_framed)', H,
    '''          (known.has(n, known()) && X.all.in(v, 32, 127)) && fields.fast(t)''',
    '''          known.has(n, known()) && fields.fast(t)'''),
  ('the fast check skips the length (respond_framed)', H,
    '''      st.in(statuses(), code, cd, why) && fields.fast(fs)
        && len.fast(head, X.rbodyless(head, code), X.rclen(head, X.rbodyless(head, code), hl, body), body)''',
    '''      st.in(statuses(), code, cd, why) && fields.fast(fs)'''),
  ('the length read with a stray byte after its digits (respond_framed)', H,
    '''    case False{}:
      RS.len.digits(acc, RS.SAt{k, x, Bytes.to_list(v)})''',
    '''    case False{}:
      more'''),
  ('the length read with every digit past the first a zero (respond_framed)', H,
    '''lv.dig(e, v, lv.num(e, acc, x))''', '''lv.dig(e, v, lv.num(e, acc, 48))'''),
  ('a status line that says 200 for a 204 (respond_framed)', H,
    '''St{204, "204", "No Content"}''', '''St{204, "200", "No Content"}'''),
  ('a response that failed the check written anyway (respond_framed)', H,
    '''    case False{}:
      X.reply(Some{X.rsp.fin(head, 500, e500.head(), e500.body())}, head, closing, v10)''',
    '''    case False{}:
      X.reply(Some{X.rsp.fin(head, code, h, body)}, head, closing, v10)'''),
  ('a matching route with the method skipped (route_first)', S,
    '''        case True{}:
          Hit{i, ps}
        case False{}:
          go(union(ms, allow))''',
    '''        case True{}:
          go(allow)
        case False{}:
          go(union(ms, allow))'''),
  ('routes counted from the wrong one (route_first)', S,
    '''al => pick.go(t, m, xs, 1n+i, al))''', '''al => pick.go(t, m, xs, i, al))'''),
  ('a method listed twice in Allow (route_first)', S,
    '''    case True{}:
      acc
    case False{}:
      List.append(&2, Bytes(), acc, [x])''',
    '''    case True{}:
      List.append(&2, Bytes(), acc, [x])
    case False{}:
      List.append(&2, Bytes(), acc, [x])'''),
  ('Allow lists the methods of a route that does not match (route_first)', S,
    '''    case None{}:
      go(allow)
    case Some{ps}:''',
    '''    case None{}:
      go(union(ms, allow))
    case Some{ps}:'''),
  ('a connection its response closed back in the pool (pool_clean)', C,
    '''        case C.Got{i, x, extra, reuse}:
          reuse''',
    '''        case C.Got{i, x, extra, reuse}:
          True{}'''),
  ('credentials kept on a redirect to another origin (redirect_creds)', C,
    '''keep.put(Bool.not(strip && cred(n)) && ''', '''keep.put(True{} && '''),
  ('a cookie not taken for a credential (redirect_creds)', C,
    '''  String.eq(n, "authorization") || String.eq(n, "cookie") || String.eq(n, "proxy-authorization")''',
    '''  String.eq(n, "authorization") || String.eq(n, "proxy-authorization")'''),
  ('one more request past the last redirect allowed (redirect_cap)', C,
    '''        chain.on(~M, ~pure, ~S, orig, rq, sr, s2 => rq2 => pure(S & Res(), (s2, Fail{TooManyRedirects{}}))))''',
    '''        chain.on(~M, ~pure, ~S, orig, rq, sr, s2 => rq2 => send(s2, rq2)))'''),
  ('a percent-escape with one hex digit decoded (pct_vectors)', H,
    '''pct.at(plus, out, c, s, h, l, U32.is_lt(h, 16) && U32.is_lt(l, 16))''',
    '''pct.at(plus, out, c, s, h, l, U32.is_lt(h, 16))'''),
  ('dot segments left in the path (url_vectors, resolve_vectors)', U,
    '''  Bytes.append(esc.go(False{}, dots(Bool.pick(Bytes(), String.is_empty(path), "/", path)), ""),''',
    '''  Bytes.append(esc.go(False{}, Bool.pick(Bytes(), String.is_empty(path), "/", path), ""),'''),
  ('a user and password in a URL taken (url_vectors)', U,
    '''  url.made(Nat.is_lt(Bytes.find_byte(auth, 0n, 64), Bytes.len(auth)), U32.is_eq(Bytes.get(auth, 0n), 91),''',
    '''  url.made(False{}, U32.is_eq(Bytes.get(auth, 0n), 91),'''),
  ('a streamed body read from past each read\'s first byte (stream_body)', B,
    '''  R.take(R.feed_buf(e, bs, p))''', '''  R.take(R.feed_buf(e, String.drop(bs, 1n), p))'''),
  ('a read of a streamed body dropped (stream_body)', B,
    '''      Wr.drain.on(R.P, step(e, r, p), acc, q => a => drain(e, t, q, a))''',
    '''      drain(e, t, p, acc)'''),
  ('a length counted one byte too many (stream_body)', B,
    '''      R.Bod{R.body.head(), q, ""}''', '''      R.Bod{R.body.head(), 1n+q, ""}'''),
  ('a chunked body given a budget of its own (stream_body)', B,
    '''R.Chk{R.body.head(), R.ASize0{}, 0, "", R.ask.cap(e)}''', '''R.Chk{R.body.head(), R.ASize0{}, 0, "", 268435455}'''),
  ('the reader keeps the body instead of handing it on (stream_body)', B,
    '''  R.take(R.feed_buf(e, bs, p))''', '''  (R.feed_buf(e, bs, p), "")'''),
  ('the bytes after a body left out of what a Body holds (stream_bounded)', B,
    '''        case R.Fin{r, x}:
          x
''', '''        case R.Fin{r, x}:
          ""
'''),
  ('a read kept whatever came after the body (stream_bounded)', B,
    '''  Nat.is_le(Nat.add(Bytes.len(x), Bytes.len(rest(p))), n)''', '''  Nat.is_le(Bytes.len(x), n)'''),
  ('the connection goes on before the body ended (stream_next)', B,
    '''          Some{x}
        case _:
          None{}''', '''          Some{x}
        case _:
          Some{""}'''),
  ('the bytes after a streamed body dropped (stream_next)', B,
    '''        case R.Final{r, x}:
          Some{x}''', '''        case R.Final{r, x}:
          Some{""}'''),
]

# bend-proxy's proof, as net/PROOF.bend uses it: its statements, open
OPEN = '''import Base
import ../wire/http1/resp.bend as R
import ../wire/http1/spec.bend as RS
import ../demos/io_proxy/core.bend as X
import ../demos/io_proxy/LAWS.bend as Laws

def app.nil(-A: Data, xs: List<&2, A>) -> {List.append(&2, A, xs, Nil{}) == xs : List<&2, A>}:
  ?TODO

def app.assoc(-A: Data, xs: List<&2, A>, -ys: List<&2, A>, -zs: List<&2, A>) ->
  {List.append(&2, A, List.append(&2, A, xs, ys), zs) == List.append(&2, A, xs, List.append(&2, A, ys, zs)) :
    List<&2, A>}:
  ?TODO

def u32.eq(a: U32, b: U32, h: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  ?TODO

def Laws.scan_is_spec(rs):
  ?TODO

def Laws.frames_agree(bs):
  ?TODO

def rr.h(h: X.RHead, +head: Bool, +code: U32, +body: Bytes(), +closing: Bool, +v10: Bool,
  hv: {X.rvalid(head, code, X.rsp.fin(head, code, h, body)) == True{} : Bool}) ->
  {RS.response(X.rask(head), Bytes.to_list(X.reply(Some{X.rsp.fin(head, code, h, body)}, head, closing, v10))) ==
    Laws.rlook(Some{X.rsp.fin(head, code, h, body)}, head, code, body, closing) : R.Look}:
  ?TODO
'''

def check(top, path):
  r = subprocess.run(['bun', os.path.join(ROOT, 'bend2', 'main.ts'), path], capture_output=True, text=True, cwd=top)
  return (r.stdout + r.stderr).strip()

def where(out):
  m = re.search(r'Location: ([^\s]+)', out)
  return m.group(1) if m else out.splitlines()[0] if out else '?'

def tree():
  top = tempfile.mkdtemp(prefix='net_laws_')
  for d in DIRS:
    shutil.copytree(os.path.join(ROOT, d), os.path.join(top, d))
  proof = os.path.join(top, 'net/PROOF.bend')
  open(os.path.join(top, 'net/open.bend'), 'w').write(OPEN)
  src = open(proof).read()
  imp = 'import ../demos/io_proxy/PROOF.bend as PP\n'
  if src.count(imp) != 1:
    print('net/PROOF.bend does not import the proxy proof as PP'); sys.exit(1)
  open(proof, 'w').write(src.replace(imp, 'import ./open.bend as PP\n'))
  return top, proof

def run(m, base):
  name, f, a, b = m
  top, proof = tree()
  try:
    path = os.path.join(top, f)
    src = open(path).read()
    if src.count(a) != 1:
      return 'MISSING  %s' % name, False
    open(path, 'w').write(src.replace(a, b))
    out = check(top, proof)
    if out == base:
      return 'SURVIVED %s' % name, False
    return 'KILLED   %s -- %s' % (name, where(out)), True
  finally:
    shutil.rmtree(top, ignore_errors=True)

def main():
  top, proof = tree()
  try:
    base = check(top, proof)
  finally:
    shutil.rmtree(top, ignore_errors=True)
  if not re.fullmatch(r'Error: \d+ TODOs found\.\nThe code is incomplete, and not a valid proof yet\.', base):
    print('the copy of net/PROOF.bend does not check clean: %s' % base)
    sys.exit(1)
  killed = 0
  with ThreadPoolExecutor(max_workers=int(os.environ.get('JOBS', '3'))) as ex:
    for line, ok in ex.map(lambda m: run(m, base), MUTANTS):
      print(line, flush=True)
      killed += ok
  print('mutants: %d / %d killed' % (killed, len(MUTANTS)))
  sys.exit(0 if killed == len(MUTANTS) else 1)

main()
