# What every mutant harness (wire/, net/, demos/io_*) shares: a private
# scratch tree per mutant, so they run side by side (-j N, nproc by
# default) and none edits the checkout; a slice of them (--shard i/n,
# every n-th from the i-th) for a CI job of its own; and a check that
# re-checks only what a mutant can change.
#
# The seeded check: a book loads its files depth first, each after its
# imports, so every def loaded before the first mutated file's is the
# clean tree's own, over the same defs before it -- and the clean tree
# checks (the laws hold step checks each proof whole, from scratch). The
# check takes those as checked (book_valid's done, as main.ts seeds Base)
# and checks from the mutated file on, which is every def the mutant can
# reach. What it prints is what `bun bend2/main.ts <proof>` prints; each
# harness also checks the clean tree seeded at each file its mutants
# break, and it must print the clean verdict, so a seed that went wrong
# fails the run rather than killing every mutant.
import atexit, os, shutil, subprocess, sys, tempfile, time
from concurrent.futures import ThreadPoolExecutor

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

SEEDED = r'''
import * as fs from "node:fs";
import * as path from "node:path";
const [bdir, file, ...changed] = process.argv.slice(2);
const Bend = await import(path.resolve(bdir, "bend.ts"));
const Comp = await import(path.resolve(bdir, "comp.ts"));
const book = Bend.book_nil();
const seen = new Map();
const at = new Map();
// the loader's own walk: each import (in order, depth first) before the
// file, so book_load finds them seen and parses the file alone
async function load(f, ns) {
  const real = fs.realpathSync(f);
  if (seen.has(real)) return;
  const dir = f.slice(0, f.lastIndexOf("/") + 1);
  for (const raw of fs.readFileSync(f, "utf8").split("\n")) {
    const line = raw.trim();
    const m = line.match(/^import(\s.*|)$/);
    if (m === null) {
      if (line !== "" && !line.startsWith("#")) break;
      continue;
    }
    const h = m[1].match(/^\s+(\S+)(?:\s+as\s+([A-Za-z_][A-Za-z0-9_]*))?\s*(?:#.*)?$/);
    if (h === null || h[2] === undefined) {
      if (h !== null && h[1] === "Base") await load(Bend.BASE_BEND, "");
      continue;
    }
    const rel = path.posix.normalize(h[1]);
    if (rel.startsWith("/") || /^0x[0-9a-f]+\//.test(rel) || !rel.endsWith(".bend")) continue;
    await load(dir + rel, path.posix.join(path.posix.dirname(ns), rel).replace(/\.bend$/, ""));
  }
  at.set(real, await Bend.book_load(book, f, ns, seen));
}
try {
  await load(file, "");
  const n0 = at.get(fs.realpathSync(file));
  let done = changed.length === 0 ? 0 : n0;
  for (const c of changed) {
    done = Math.min(done, at.get(fs.realpathSync(c)) ?? done);
  }
  // an unfilled law before the seed is still an open claim
  const last = new Map(book.order.map((k, i) => [k, i]));
  for (let i = 0; i < done; i++) {
    const t = book.tlds[book.order[i]];
    if (t.$ === "Def" && last.get(book.order[i]) === i && t.v === null && t.b !== true && !t.i) {
      book.open += 1;
    }
  }
  Bend.book_valid(book, done);
  Comp.book_owned(book, Comp.SYNTH);
  const hols = book.hols + book.open;
  if (hols > 0) {
    throw "Error: " + hols + " TODO" + (hols === 1 ? "" : "s")
      + " found.\nThe code is incomplete, and not a valid proof yet.";
  }
  // main.ts's report: the root's defs that reach a promise (@unsafe, a
  // foreign def) along who names whom
  const own = [...new Set(book.order.slice(n0))];
  const bad = new Set(Object.keys(book.tlds).filter((k) =>
    book.tlds[k].u === true || (book.tlds[k].i !== undefined && book.tlds[k].b !== true)));
  const refs = (tm, out) => {
    if (typeof tm === "object" && tm !== null) {
      if ((tm.$ === "Ref" || tm.$ === "ADT") && tm.k !== undefined) out.add(tm.k);
      for (const [f, v] of Object.entries(tm)) if (f !== "s") refs(v, out);
    }
  };
  const uses = new Map();
  const saw = new Set();
  for (const q = bad.size === 0 ? [] : own.slice(); q.length > 0;) {
    const k = q.pop();
    const t = book.tlds[k];
    if (t !== undefined && !saw.has(k)) {
      saw.add(k);
      const rs = new Set();
      for (const c of t.$ === "ADT" ? t.c : [t]) refs(Bend.term_lower(c.T), rs);
      refs(t.$ === "Def" ? t.e : undefined, rs);
      for (const r of rs) {
        if (!uses.has(r)) uses.set(r, []);
        uses.get(r).push(k);
        q.push(r);
      }
    }
  }
  for (const k of bad) (uses.get(k) ?? []).forEach((j) => bad.add(j));
  const list = own.filter((k) => bad.has(k));
  console.log(list.length === 0 ? "All terms check." : "All terms check, but " + list.length + " def"
    + (list.length === 1 ? " relies" : "s rely") + " on unsafe or foreign code:\n"
    + list.map((k) => "- " + k).join("\n"));
} catch (e) {
  console.error(e instanceof RangeError ? "Error: the machine stack overflowed (a deep recursion, or a"
    + " literal too large to expand)"
    : e?.$ === "Err" ? Bend.err_show(e) : String(e));
  process.exitCode = 1;
}
'''

_script = None

def seeded():
  global _script
  if _script is None:
    d = tempfile.mkdtemp(prefix='seeded_')
    atexit.register(shutil.rmtree, d, True)
    _script = os.path.join(d, 'seeded.mjs')
    open(_script, 'w').write(SEEDED)
  return _script

# check(proof, changed): the verdict on proof, re-checked from the first
# of the changed files (none: from scratch), stdout and stderr as one
def check(proof, changed=(), timeout=3600):
  r = subprocess.run(['bun', seeded(), os.path.join(ROOT, 'bend2'), proof] + list(changed),
    capture_output=True, text=True, timeout=timeout)
  return (r.stdout + r.stderr).strip()

# -j N and --shard i/n from the command line
def args():
  jobs, shard, argv = os.cpu_count() or 1, (0, 1), sys.argv[1:]
  while argv:
    a = argv.pop(0)
    if a == '-j':
      jobs = int(argv.pop(0))
    elif a.startswith('-j'):
      jobs = int(a[2:])
    elif a == '--shard':
      i, n = argv.pop(0).split('/')
      shard = (int(i), int(n))
    else:
      print('usage: %s [-j N] [--shard i/n]' % sys.argv[0]); sys.exit(2)
  return max(1, jobs), shard

def mine_of(xs, shard):
  i, n = shard
  return [x for k, x in enumerate(xs) if k % n == i]

def pmap(f, xs, jobs):
  with ThreadPoolExecutor(max_workers=jobs) as ex:
    yield from ex.map(f, xs)

# tree(dirs): a scratch copy of each dir (from ROOT, or src) under a new top
def tree(dirs, src=ROOT, prefix='mut_'):
  top = tempfile.mkdtemp(prefix=prefix)
  for d in dirs:
    shutil.copytree(os.path.join(src, d), os.path.join(top, d), symlinks=True)
  return top

def drop(top):
  shutil.rmtree(top, ignore_errors=True)

# apply(path, before, after): False when before is not there exactly once
def apply(path, before, after):
  src = open(path).read()
  if src.count(before) != 1:
    return False
  open(path, 'w').write(src.replace(before, after))
  return True

# run(make, proof, muts, jobs, shard): this shard's mutants, (what, file,
# before, after[, their proof]) with the files relative to the top make()
# returns, each in a tree of its own, side by side with each proof's
# clean verdict (from scratch) and the clean tree's seeded at this
# shard's share of the files the mutants break, which must be that
# verdict too (else it exits). Returns the clean verdicts, by proof, and
# per mutant (what, its proof, its verdict, or None when before is not in
# its file exactly once).
def run(make, proof, muts, jobs, shard):
  muts = [tuple(m[:4]) + (m[4] if len(m) > 4 else proof,) for m in muts]
  mine = mine_of(muts, shard)
  proofs = sorted(set(m[4] for m in muts))
  seeds = mine_of(sorted(set((m[4], m[1]) for m in muts)), shard)
  def one(t):
    kind, x = t
    top, t0 = make(), time.time()
    try:
      if kind == 'base':
        return check(os.path.join(top, x))
      if kind == 'seed':
        return check(os.path.join(top, x[0]), [os.path.join(top, x[1])])
      path = os.path.join(top, x[1])
      return check(os.path.join(top, x[4]), [path]) if apply(path, x[2], x[3]) else None
    finally:
      drop(top)
      if os.environ.get('MUTATE_TIMES'):
        print('%5.0f s  %s %s' % (time.time() - t0, kind, x if kind != 'mut' else x[0]), file=sys.stderr, flush=True)
  tasks = [('base', p) for p in proofs] + [('seed', s) for s in seeds] + [('mut', m) for m in mine]
  outs = list(pmap(one, tasks, jobs))
  base = dict(zip(proofs, outs))
  got = outs[len(proofs):]
  bad = [(s, out) for s, out in zip(seeds, got) if out != base[s[0]]]
  for (p, f), out in bad:
    print('%s seeded at %s is not its clean verdict:\n%s\n(from scratch:\n%s)' % (p, f, out[:600], base[p][:600]))
  if bad:
    sys.exit(1)
  return base, [(m[0], m[4], out) for m, out in zip(mine, got[len(seeds):])]
