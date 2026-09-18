#!/usr/bin/env bash
# Local, VM-free acceptance: identical Bend drivers, emitted C and JS.
# Artifacts (sources, binaries, /usr/bin/time -v, JSONL, table) stay in OUT.
set -euo pipefail
cd "$(dirname "$0")/../.."
export BEND_BENCH_ROOT="$PWD"
export BEND_BENCH_OUT="${BENCH_OUT:-$(mktemp -d /tmp/bend-string-bench.XXXXXX)}"
export BEND_BENCH_BASE="${BENCH_BASE:-/tmp/bench-base}"
if [[ ! -d "$BEND_BENCH_BASE/bend2" ]]; then
  git worktree add "$BEND_BENCH_BASE" master
fi
python3 - <<'PY'
import hashlib, json, math, os, platform, re, statistics, subprocess, time
from pathlib import Path

ROOT = Path(os.environ['BEND_BENCH_ROOT'])
BASE = Path(os.environ['BEND_BENCH_BASE'])
OUT = Path(os.environ['BEND_BENCH_OUT']).resolve()
OUT.mkdir(parents=True, exist_ok=True)
TIMEOUT = int(os.getenv('BENCH_TIMEOUT', '120'))
SIZES = [int(x) for x in os.getenv('BENCH_SIZES', '1,8,64').split(',')]
FILTER = os.getenv('BENCH_FILTER', '')
JS_MAX = int(os.getenv('BENCH_JS_MAX_MIB', '8'))*1024**2
CC = os.getenv('CC', 'clang')
FLAGS = ['-std=c11', '-O3', '-g', '-fno-omit-frame-pointer']
ENV = {**os.environ, 'LC_ALL': 'C', 'BEND_LIB': str(OUT / 'unused-lib')}

def call(cmd, **kw):
    return subprocess.run([str(x) for x in cmd], env=ENV, text=True,
                          check=True, timeout=180, **kw)

def capture(cmd):
    return call(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT).stdout.strip()

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

meta = dict(start_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
    candidate=capture(['git', '-C', ROOT, 'rev-parse', 'HEAD']),
    baseline=capture(['git', '-C', BASE, 'rev-parse', 'HEAD']),
    candidate_branch=capture(['git', '-C', ROOT, 'branch', '--show-current']),
    baseline_status=capture(['git', '-C', BASE, 'status', '--short']),
    baseline_sources={f:sha(BASE/f) for f in ['bend2/base.bend','bend2/comp.ts','bend2/bend.ts','bend2/main.ts']},
    machine=platform.platform(), cpu=capture(['lscpu']), memory=capture(['free', '-b']),
    compiler=capture([CC, '--version']), bun=capture(['bun', '--version']),
    flags=FLAGS + ['-lpthread', '-lm'], c_args=['--gpu', 'off', '--threads', '1'],
    warmups=1, measurements=7, timeout_seconds=TIMEOUT,
    js_max_input_bytes=JS_MAX,
    warm_state='One untimed process per row, then seven fresh processes; page cache warm; JS JIT starts fresh each process; no cache flush or CPU pinning.',
    counters='Separate instrumented binary: heap_alloc/free requested bytes (not allocator reserve, RSS, or malloc); tick snapshots reset interval peak.',
    sources={str(p.relative_to(ROOT)): sha(p) for p in [ROOT/'bend2/base.bend', ROOT/'bend2/comp.ts', ROOT/'tests/strings/bench_words.bend', ROOT/'tests/strings/bench.sh']})
(OUT/'provenance.json').write_text(json.dumps(meta, indent=2)+'\n')

# Baseline lacks words/copy. Load only their checked reference definitions
# plus words' new helpers, in the Base namespace. No old definition is replaced.
src = (ROOT/'bend2/base.bend').read_text()
compat = (src[src.index('law String.split.acc:'):src.index('def String.split(s:')]
        + src[src.index('def String.words.cut'):src.index('def String.partition.at')]
        + src[src.index('def String.copy(s:'):src.index('law String.find.go:')])
(OUT/'compat.bend').write_text(compat)
(OUT/'compile.ts').write_text('''
import * as fs from "node:fs";
const [root, input, output, compat] = process.argv.slice(2);
const B = await import(root + "/bend2/bend.ts");
const C = await import(root + "/bend2/comp.ts");
const book = B.book_nil(), seen = new Map();
try {
await B.book_load(book, root + "/bend2/base.bend", "", seen);
if (compat !== "-") {
  const start = book.order.length;
  await B.book_load(book, compat, "", seen);
  for (const k of book.order.slice(start)) book.tlds[k].b = true;
}
await B.book_load(book, input, "", seen);
B.book_valid(book);
if (book.hols + book.open) throw new Error("unchecked benchmark");
fs.writeFileSync(output + ".c", C.compile_book(book));
fs.writeFileSync(output + ".js", C.js_book(book));
} catch (e) { console.error(e?.$ === "Err" ? B.err_show(e) : String(e)); process.exit(1); }
''')
(OUT/'mark.c').write_text(r'''
Term bench_mark_run(Env e, Term* f, IoWork* w) {
  fprintf(stderr, "BENCH {\"phase\":%u,\"ns\":%llu", (u32)f[0], (unsigned long long)io_tick());
#ifdef BENCH_TRACK
  fprintf(stderr, ",\"allocs\":%llu,\"frees\":%llu,\"live\":%llu,\"peak\":%llu",
    bench_allocs, bench_frees, bench_live, bench_peak);
#ifdef BENCH_COPY_TRACK
  fprintf(stderr, ",\"copy_cells\":%llu", bench_copies);
#else
  fprintf(stderr, ",\"copy_cells\":null");
#endif
  bench_peak = bench_live;
#endif
  fprintf(stderr, "}\n");
  return term_pak(CID_UNIT, 0);
}
static void __attribute__((constructor)) bench_mark_use(void) {
  io_eff(CID_BENCH_MARK, bench_mark_run, 0);
}
''')
(OUT/'mark.js').write_text('''
function bench_mark(phase) {
  console.error('BENCH ' + JSON.stringify({phase, ns: Math.round(performance.now()*1e6)}));
  return {$: "Unit"};
}
''')

(OUT/'words.bend').write_bytes((ROOT/'tests/strings/bench_words.bend').read_bytes())
PRE = '''import Base
import ./words.bend as W

def Bench.mark(phase: U32) -> IO(Unit):
  import "./mark.c"
  import "./mark.js"

def report(r: U32 & U32) -> IO(Unit):
  (n, h) = r
  do IO<Unit>:
    Bench.mark(3)
    IO.print(String.append(U32.show(n), String.append(":", U32.show(h))))

def materialized(xs: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    Bench.mark(2)
    report(W.tokens(xs, 0, 0))

def retained(s: String) -> IO(Unit):
  do IO<Unit>:
    Bench.mark(2)
    report((3, W.token(s, 0)))

def found(b: Bool) -> IO(Unit):
  match b:
    case True{}:
      report((1, 1))
    case False{}:
      report((0, 0))
'''

def oracle(text):
    words = re.findall(r'[^ \t-\r]+', text)
    h = 0
    for word in words:
        x = 0
        for c in word: x = (x*33+ord(c)) & 0xffffffff
        h = (h+x) & 0xffffffff
    return f'{len(words)}:{h}'

units = {'ascii': '  alpha beta\n gamma\t\n', 'unicode': '  café λ😀\n 漢字\t\n',
         'legacy': 'the quick brown fox jumps over the lazy dog\n'}
cases = []
for reps in [1024,4096]:
    cases.append(dict(name=f'legacy-{reps}', corpus='legacy', reps=reps, mode='materialize', source='construct'))
for corpus in ['ascii','unicode']:
    for size in SIZES:
        reps = (size*1024**2)//len(units[corpus].encode())
        for mode, source in [('scan','io'),('scan','construct'),('materialize','io')]:
            cases.append(dict(name=f'{corpus}-{size}MiB-{source}-{mode}', corpus=corpus, reps=reps, size_bytes=size*1024**2, mode=mode, source=source))
for mode in ['view','copy']:
    cases.append(dict(name=f'retain-8MiB-{mode}', corpus='ascii', reps=(8*1024**2)//21, size_bytes=8*1024**2, mode=mode, source='io'))
for n,m in [(32768,512),(65536,1024),(131072,2048)]:
    cases.append(dict(name=f'search-{n}-{m}', corpus='search', n=n, m=m, mode='search', source='construct'))
for op in ['concat','join','repeat','append','snapshots']:
    for n in ([128,512] if op=='snapshots' else [1024,4096]):
        cases.append(dict(name=f'build-{op}-{n}',mode='builder',op=op,n=n,source='construct'))
for prefix in [256,4096]:
    cases.append(dict(name=f'map-prefix-{prefix}',mode='map',prefix=prefix,n=64,source='construct'))
if FILTER: cases = [c for c in cases if re.search(FILTER, c['name'])]

records = []
raw = (OUT/'raw.jsonl').open('w')

def record(r):
    records.append(r); raw.write(json.dumps(r)+'\n'); raw.flush()

def instrument(c):
    a = 'INLINE Loc heap_alloc(Env e, Cls cls) {'
    b = 'INLINE void heap_free(Env e, Cls cls, Loc loc) {'
    assert c.count(a)==1 and c.count(b)==1
    c = c.replace(a, 'INLINE Loc bench_heap_alloc(Env e, Cls cls) {')
    tracker = '''
#define BENCH_TRACK 1
static unsigned long long bench_allocs, bench_frees, bench_live, bench_peak, bench_copies;
INLINE Loc heap_alloc(Env e, Cls cls) {
  Loc l = bench_heap_alloc(e, cls);
  if (!err_seen(e.mem)) {
    bench_allocs++; bench_live += 8ull << cls;
    if (bench_live > bench_peak) bench_peak = bench_live;
  }
  return l;
}
'''
    c = c.replace(b, tracker+b)
    free = '''  e.mem[loc]       = ALC_AT(e, cls);'''
    assert c.count(free)==1
    c = c.replace(free, '''  bench_frees++;
  if (bench_live < (8ull << cls)) { fprintf(stderr, "counter underflow\\n"); abort(); }
  bench_live -= 8ull << cls;
'''+free)
    copy = 'INLINE void str_copy_cells(Env e, StrParts dst, u32 at, StrParts src) {'
    if copy in c: c = '#define BENCH_COPY_TRACK 1\n'+c.replace(copy, copy+' bench_copies += src.len;')
    return c

def run_one(case, lane, kind, run, cmd):
    stem = OUT/f"{case['name']}.{lane}.{kind}.{run}"
    start = time.perf_counter_ns()
    with stem.with_suffix(stem.suffix+'.stdout').open('w') as out, stem.with_suffix(stem.suffix+'.stderr').open('w') as err:
        p = subprocess.run(['/usr/bin/time','-v','-o',str(stem)+'.time','timeout','--signal=TERM','--kill-after=5',str(TIMEOUT),*cmd],
            cwd=OUT, env=ENV, stdout=out, stderr=err, text=True)
    wall = (time.perf_counter_ns()-start)/1e6
    stderr = Path(str(stem)+'.stderr').read_text()
    stdout = Path(str(stem)+'.stdout').read_text().strip()
    stats = Path(str(stem)+'.time').read_text()
    marks = [json.loads(x[6:]) for x in stderr.splitlines() if x.startswith('BENCH ')]
    phases = {m['phase']:m for m in marks}
    rss = re.search(r'Maximum resident set size \(kbytes\): (\d+)', stats)
    result = dict(case=case['name'],lane=lane,kind=kind,run=run,status=p.returncode,
        correct=p.returncode==0 and stdout==case['expected'], stdout=stdout,
        wall_ms=wall,rss_kib=int(rss[1]) if rss else None,marks=marks,
        diagnostic='\n'.join(x for x in stderr.splitlines() if not x.startswith('BENCH '))[-1800:])
    for label,a,b in [('acquire_ms',0,1),('process_ms',1,3),('materialize_ms',1,2),('consume_ms',2,3)]:
        if a in phases and b in phases: result[label]=(phases[b]['ns']-phases[a]['ns'])/1e6
    record(result)
    return result

for case in cases:
    mode = case['mode']
    if mode=='builder':
        n=case['n'];op=case['op']
        unit='ab😀' if op in ['concat','join','repeat'] else 'x'
        body='''def append(n: Nat, s: String) -> String:
  match n:
    case 0n:
      s
    case 1n+p:
      append(p, String.append(s, "x"))

def snapshots(n: Nat, +s: String) -> List<&2, String>:
  match n:
    case 0n:
      [s]
    case 1n+p:
      s <> snapshots(p, String.append(s, "x"))

'''
        if op=='snapshots':
            expected_h=0;h=0
            for _ in range(n):
                h=(h*33+120)&0xffffffff
                expected_h=(expected_h+h)&0xffffffff
            case.update(bytes=n*(n+1)//2,expected=f'{n+1}:{expected_h}')
            body+=f'''def ready(xs: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    Bench.mark(1)
    report(W.tokens(xs, 0, 0))

def main() -> IO(Unit):
  do IO<Unit>:
    Bench.mark(0)
    ready(snapshots(U32.to_nat({n}), ""))
'''
        else:
            literal=json.dumps(unit,ensure_ascii=False)
            arg=f'List.replicate(String, U32.to_nat({n}), {literal})'
            operation={'concat':f'String.concat({arg})','join':f'String.join({arg}, "|")',
                'repeat':f'String.repeat({literal}, U32.to_nat({n}))',
                'append':f'append(U32.to_nat({n}), "")'}[op]
            text=('|' if op=='join' else '').join([unit]*n)
            case.update(bytes=len(text.encode()),expected=oracle(text))
            body+=f'''def ready(s: String) -> IO(Unit):
  do IO<Unit>:
    Bench.mark(1)
    report((1, W.token(s, 0)))

def main() -> IO(Unit):
  do IO<Unit>:
    Bench.mark(0)
    ready({operation})
'''
    elif mode=='map':
        prefix=case['prefix'];n=case['n']
        case.update(bytes=sum(prefix+len(str(i)) for i in range(1,n+1)),expected=f'{n}:{n*(n+1)//2}')
        body=f'''def make(+n: Nat, +prefix: String, m: Map<&2, U32>) -> Map<&2, U32>:
  match n:
    case 0n:
      m
    case 1n+p:
      make(p, prefix, Map.set(&2, U32, m,
        String.append(prefix, U32.show(U32.from_nat(1n+p))), U32.from_nat(1n+p)))

def lookup(+n: Nat, +prefix: String, +m: Map<&2, U32>, h: U32) -> U32:
  match n:
    case 0n:
      h
    case 1n+p:
      lookup(p, prefix, m, U32.add(h, Pair.snd(Map<&2, U32>, U32,
        Map.get(U32, 0, m, String.append(prefix, U32.show(U32.from_nat(1n+p)))))))

def ready(m: Map<&2, U32>, prefix: String) -> IO(Unit):
  do IO<Unit>:
    Bench.mark(1)
    report(({n}, lookup(U32.to_nat({n}), prefix, m, 0)))

def build(+prefix: String) -> IO(Unit):
  ready(make(U32.to_nat({n}), prefix, Map.new(&2, U32)), prefix)

def main() -> IO(Unit):
  do IO<Unit>:
    Bench.mark(0)
    build(String.repeat("a", U32.to_nat({prefix})))
'''
    elif mode=='search':
        n,m = case['n'],case['m']
        case.update(bytes=n,expected='1:1')
        body=f'''def ready(s: String, p: String) -> IO(Unit):
  do IO<Unit>:
    Bench.mark(1)
    found(String.contains(s, p))

def main() -> IO(Unit):
  do IO<Unit>:
    Bench.mark(0)
    ready(String.append(String.repeat("a", U32.to_nat({n-1})), "b"),
      String.append(String.repeat("a", U32.to_nat({m-1})), "b"))
'''
    else:
        unit = units[case['corpus']]; reps=case['reps']; data=unit.encode()
        byte_count=case.get('size_bytes',len(data)*reps)
        rest=byte_count-len(data)*reps
        suffix=data[:rest].decode('utf-8',errors='ignore')
        suffix+=' '*(rest-len(suffix.encode()))
        case.update(bytes=byte_count,codepoints=len(unit)*reps+len(suffix),suffix=suffix)
        wn,wh=map(int,oracle(unit).split(':')); sn,sh=map(int,oracle(suffix).split(':'))
        case['expected']=f'{wn*reps+sn}:{(wh*reps+sh)&0xffffffff}' if mode not in ['view','copy'] else '3:'+str(ord('p')*33*33+ord('h')*33+ord('a'))
        chunk=len(unit)*256; fuel=math.ceil(case['codepoints']/chunk)
        operation = {'scan':f'report(W.scan(U32.to_nat({fuel}), s, U32.to_nat({chunk}), (0, 0)))',
          'materialize':'materialized(W.materialize(s))',
          'view':'retained(String.take(String.drop(s, 4n), 3n))',
          'copy':'retained(String.copy(String.take(String.drop(s, 4n), 3n)))'}[mode]
        body=f'''def ready(s: String) -> IO(Unit):
  do IO<Unit>:
    Bench.mark(1)
    {operation}
'''
        if case['source']=='io':
            file=OUT/f"{case['corpus']}-{byte_count}.txt"
            if not file.exists():
                with file.open('wb') as f:
                    block=data*4096
                    for _ in range(reps//4096): f.write(block)
                    f.write(data*(reps%4096)+suffix.encode())
            case['input_sha256']=sha(file)
            body+=f'''
def read_done(read: File & Result<&1, &1, U32 & String, String>) -> IO(Unit):
  (f, r) = read
  do IO<Unit>:
    s : String <- IO.pass(String, r)
    File.close(f)
    ready(s)

def main() -> IO(Unit):
  do IO<Unit>:
    Bench.mark(0)
    f : File <- IO.try(File, File.open("{file.name}", "r"))
    r : File & Result<&1, &1, U32 & String, String> <- File.read(f, {byte_count+1})
    read_done(r)
'''
        else:
            literal=json.dumps(unit, ensure_ascii=False)
            build=f'String.repeat({literal}, U32.to_nat({reps}))'
            if suffix: build=f'String.append({build}, {json.dumps(suffix,ensure_ascii=False)})'
            body+=f'''
def main() -> IO(Unit):
  do IO<Unit>:
    Bench.mark(0)
    ready({build})
'''
    driver=OUT/(case['name']+'.bend');driver.write_text(PRE+body)
    (OUT/'cases.json').write_text(json.dumps(cases, indent=2, ensure_ascii=False)+'\n')
    case['driver_sha256']=sha(driver)
    print(f"BUILD {case['name']} ({case['bytes']} bytes)", flush=True)
    for lane,root in [('base',BASE),('candidate',ROOT)]:
        target=OUT/f"{case['name']}.{lane}"
        try:
            with Path(str(target)+'.build.log').open('w') as log:
                call(['bun',OUT/'compile.ts',root,driver,target,OUT/'compat.bend' if lane=='base' else '-'],stdout=log,stderr=subprocess.STDOUT)
                call([CC,*FLAGS,str(target)+'.c','-lpthread','-lm','-o',target],stdout=log,stderr=subprocess.STDOUT)
                tracked=Path(str(target)+'.tracked.c');tracked.write_text(instrument(Path(str(target)+'.c').read_text()))
                call([CC,*FLAGS,tracked,'-lpthread','-lm','-o',str(target)+'.tracked'],stdout=log,stderr=subprocess.STDOUT)
        except (subprocess.CalledProcessError,subprocess.TimeoutExpired) as e:
            print(Path(str(target)+'.build.log').read_text()[-5000:],flush=True)
            raise
        case[lane+'_binary_sha256']=sha(target)
        for kind,cmd in [('c',[str(target),'--gpu','off','--threads','1']),('js',['bun',str(target)+'.js'])]:
            if kind=='js' and case['bytes'] > JS_MAX+64:
                print(f'  {lane:9} js: not run (BENCH_JS_MAX_MIB)',flush=True)
                continue
            warm=run_one(case,lane,kind,'warm',cmd)
            measured=[run_one(case,lane,kind,i,cmd) for i in range(1,8)]
            ok=sum(x['correct'] for x in measured)
            med=statistics.median(x['wall_ms'] for x in measured)
            print(f"  {lane:9} {kind}: {ok}/7 valid, median wall {med:.3f} ms, status {measured[0]['status']}",flush=True)
        run_one(case,lane,'c-counters',1,[str(target)+'.tracked','--gpu','off','--threads','1'])
    (OUT/'cases.json').write_text(json.dumps(cases, indent=2, ensure_ascii=False)+'\n')

raw.close()
lines=['| Workload | Lane | Valid | Wall ms median [min,max] | Acquire ms | Process ms median [min,max] | Peak RSS KiB median [min,max] |',
       '|---|---|---:|---:|---:|---:|---:|']
def fmt(xs):
    return f'{statistics.median(xs):.3f} [{min(xs):.3f},{max(xs):.3f}]' if xs else '—'
for case in cases:
    for lane in ['base','candidate']:
        for kind in ['c','js']:
            rows=[r for r in records if r['case']==case['name'] and r['lane']==lane and r['kind']==kind and r['run']!='warm']
            if not rows:
                lines.append(f"| {case['name']} | {lane}/{kind} | NOT RUN (JS size limit) | — | — | — | — |")
                continue
            valid=[r for r in rows if r['correct']]
            status=f'{len(valid)}/7' if valid else 'FAIL '+','.join(str(s) for s in sorted(set(r['status'] for r in rows)))
            lines.append(f"| {case['name']} | {lane}/{kind} | {status} | {fmt([r['wall_ms'] for r in rows])} | {fmt([r['acquire_ms'] for r in valid])} | {fmt([r['process_ms'] for r in valid])} | {fmt([r['rss_kib'] for r in rows])} |")
table='\n'.join(lines)+'\n';(OUT/'table.md').write_text(table)
print(table);print('Artifacts:',OUT,flush=True)
# Baseline stack overflow is a recorded result; candidate failures are failures.
if any(r['lane']=='candidate' and not r['correct'] for r in records): raise SystemExit(1)
PY
