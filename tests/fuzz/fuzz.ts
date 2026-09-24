#!/usr/bin/env bun
// The compiler's differential fuzzer: random well-typed programs (gen.ts),
// each checked, then run by the interpreter (the reference: a pure main is
// normalized by the checker, an IO main's pure twin is), the JS lane and
// the C lane (clang -O3), and, with --san, C again under ASan and UBSan.
// Every lane must print what the reference prints; a program whose outputs
// differ is shrunk (--reduce) to a small one that still differs the same
// way. See README.md.
//
//   bun tests/fuzz/fuzz.ts [--seed S] [--n N] [--jobs J] [--san] [--reduce]
//                          [--out DIR] [--ci]
//   bun tests/fuzz/fuzz.ts --one SEED[:io|:f64] [--san] [--reduce]
//   bun tests/fuzz/fuzz.ts --file F.bend      (the lanes on a file)

import * as child from "node:child_process";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import * as readline from "node:readline";

import * as G from "./gen.ts";

// Types
// =====

type Lane = "interp" | "js" | "c" | "san";

type Req = { id: number; text: string; twin: string | null; dir: string; interp: boolean; emit: boolean };

type Rep = { id: number; ok: boolean; err?: string; interp?: string; ms?: number };

type Verdict = {
  ok: boolean;         // the checker took it
  err?: string;        // its refusal
  outs: Partial<Record<Lane, string>>;
  sig: string;         // "" when every lane agrees
  ref: Lane | null;
};

// Constants
// =========

const ROOT = path.join(import.meta.dirname, "..", "..");

const BEND = process.env.FUZZ_BEND2 ?? path.join(ROOT, "bend2");

const ARGS = process.argv.slice(2);

function opt(k: string): string | undefined {
  const i = ARGS.indexOf(k);
  return i < 0 ? undefined : ARGS[i + 1];
}

const CI = ARGS.includes("--ci");

const JOBS = Number(opt("--jobs") ?? Math.max(1, os.availableParallelism()));

const SAN = ARGS.includes("--san");

// --san K: every Kth batch also runs sanitized (-O0: -O1 costs four times more)
const SAN_EVERY = Math.max(1, Number(opt("--san") ?? 1) || 1);

const CC = process.env.CC ?? "clang";

const T_INTERP = 30_000;

const T_RUN = 10_000;

// programs built and run as one (--batch 1: each alone)
const BATCH = Number(opt("--batch") ?? 8);

// Worker
// ======

// A worker loads Base once, then checks, normalizes and emits each program
// it is handed: one JSON line in, one out.
async function worker(): Promise<void> {
  const Bend = await import(path.join(BEND, "bend.ts"));
  const Comp = await import(path.join(BEND, "comp.ts"));
  const base = Bend.book_nil();
  await Bend.book_load(base, Bend.BASE_BEND, "", new Map());
  Bend.book_valid(base, 0);
  Comp.book_owned(base, Comp.SYNTH);
  const seed = (): unknown => {
    const book = Bend.book_nil();
    for (const k of Object.keys(base.tlds)) book.tlds[k] = { ...base.tlds[k] };
    Object.assign(book.ctrs, base.ctrs);
    for (const k of Object.keys(base.tmps)) book.tmps[k] = { ...base.tmps[k] };
    book.order.push(...base.order);
    return book;
  };
  const load = async (file: string): Promise<any> => {
    const book = seed() as any;
    const seen = new Map<string, string | null>([[Bend.BASE_BEND, ""]]);
    await Bend.book_load(book, file, "", seen);
    Bend.book_valid(book, base.order.length);
    Comp.book_owned(book, Comp.SYNTH);
    if (book.hols + book.open > 0) throw "Error: TODO found";
    return book;
  };
  const show = (e: unknown): string => e instanceof RangeError ? "Error: stack overflow"
    : (e as any)?.$ === "Err" ? Bend.err_show(e) : String(e);
  const rl = readline.createInterface({ input: process.stdin });
  for await (const line of rl) {
    const q = JSON.parse(line) as Req;
    const rep: Rep = { id: q.id, ok: false };
    try {
      const t0 = Date.now();
      fs.writeFileSync(path.join(q.dir, "p.bend"), q.text);
      const book = await load(path.join(q.dir, "p.bend"));
      let tb = book;
      if (q.twin !== null) {
        fs.writeFileSync(path.join(q.dir, "twin.bend"), q.twin);
        tb = await load(path.join(q.dir, "twin.bend"));
      }
      if (q.emit) {
        fs.writeFileSync(path.join(q.dir, "p.js"), Comp.js_book(book));
        fs.writeFileSync(path.join(q.dir, "p.c"), Comp.compile_book(book));
      }
      rep.ok = true;
      rep.ms = Date.now() - t0;
      if (q.interp) {
        try {
          const main = tb.tlds["main"];
          rep.interp = Bend.term_show(Bend.term_lower(Bend.term_snf(tb, main.v)));
        } catch (e) {
          rep.interp = show(e);
        }
      }
    } catch (e) {
      rep.err = show(e);
    }
    process.stdout.write(JSON.stringify(rep) + "\n");
  }
}

// Pool
// ====

// J workers; a request past its time kills its worker, which is replaced.
class Pool {
  kids: { p: child.ChildProcess; busy: boolean; n: number; cb: ((r: Rep | null) => void) | null }[] = [];
  wait: (() => void)[] = [];

  constructor(n: number) {
    for (let i = 0; i < n; i++) this.kids.push(this.spawn());
  }

  spawn(): Pool["kids"][number] {
    const p = child.spawn(process.execPath, [import.meta.filename, "--worker"],
      { stdio: ["pipe", "pipe", "inherit"], env: { ...process.env, BEND_NO_TELEMETRY: "1" } });
    const k = { p, busy: false, n: 0, cb: null as ((r: Rep | null) => void) | null };
    readline.createInterface({ input: p.stdout! }).on("line", (l) => {
      const cb = k.cb;
      k.cb = null;
      cb?.(JSON.parse(l));
    });
    p.on("exit", () => { const cb = k.cb; k.cb = null; cb?.(null); });
    return k;
  }

  async run(q: Req, ms = T_INTERP): Promise<Rep | null> {
    let k = this.kids.find((x) => !x.busy);
    while (k === undefined) {
      await new Promise<void>((r) => this.wait.push(r));
      k = this.kids.find((x) => !x.busy);
    }
    k.busy = true;
    const kid = k;
    const rep = await new Promise<Rep | null>((res) => {
      const bomb = setTimeout(() => { kid.cb = null; res(null); }, ms);
      kid.cb = (r) => { clearTimeout(bomb); res(r); };
      kid.p.stdin!.write(JSON.stringify(q) + "\n");
    });
    kid.n += 1;
    if (rep === null || kid.n >= 150) {
      // hung, dead or old: a fresh one (the checker's caches grow)
      kid.p.kill("SIGKILL");
      const i = this.kids.indexOf(kid);
      this.kids[i] = this.spawn();
    } else {
      kid.busy = false;
    }
    this.wait.shift()?.();
    return rep;
  }

  close(): void {
    for (const k of this.kids) k.p.kill("SIGKILL");
  }
}

// Exec
// ====

let slots = JOBS;
const queue: (() => void)[] = [];

async function sh(cmd: string, args: string[], ms: number, env: Record<string, string> = {}):
  Promise<{ out: string; code: number | null; sig: string | null }> {
  while (slots === 0) await new Promise<void>((r) => queue.push(r));
  slots -= 1;
  try {
    return await new Promise((res) => {
      const p = child.spawn(cmd, args, { env: { ...process.env, ...env }, stdio: ["ignore", "pipe", "pipe"] });
      let out = "";
      p.stdout.on("data", (d) => { if (out.length < 1 << 20) out += d; });
      p.stderr.on("data", (d) => { if (out.length < 1 << 20) out += d; });
      const bomb = setTimeout(() => p.kill("SIGKILL"), ms);
      p.on("close", (code, sig) => { clearTimeout(bomb); res({ out, code, sig }); });
    });
  } finally {
    slots += 1;
    queue.shift()?.();
  }
}

function tidy(s: string): string {
  return s.replace(/[ \t]+$/gm, "").trim();
}

function ran(r: { out: string; code: number | null; sig: string | null }): string {
  return tidy(r.out) + (r.sig !== null ? "\n§signal " + r.sig
    : r.code !== 0 ? "\n§exit " + String(r.code) : "");
}

// The interpreter shows a String as a literal; an IO program prints raw.
function unshow(s: string): string | null {
  const m = /^"((?:[^"\\]|\\.|\\u\{[0-9a-f]+\})*)"$/s.exec(s.trim());
  if (m === null) return null;
  return m[1].replace(/\\(u\{([0-9a-f]+)\}|.)/g, (_, e: string, h: string) =>
    h !== undefined ? String.fromCodePoint(parseInt(h, 16))
      : ({ n: "\n", t: "\t", r: "\r", "0": "\0" } as Record<string, string>)[e] ?? e);
}

// Lanes
// =====

let DIRS = 0;
const TMP = fs.mkdtempSync(path.join(os.tmpdir(), "bend-fuzz-"));

function newdir(): [string, number] {
  const idx = DIRS++;
  const dir = path.join(TMP, String(idx));
  fs.mkdirSync(dir);
  return [dir, idx];
}

// The interpreter's answer as the lane prints it.
function interp_out(v: string, twin: boolean): string {
  if (twin) {
    const u = unshow(v);
    return u === null ? "§stuck " + v.slice(0, 200) : tidy(u + "\nend");
  }
  return /^"/.test(v) ? v : "§stuck " + v.slice(0, 200);
}

// The compiled lanes of the p.js and p.c in dir.
async function compiled(dir: string, on: (l: Lane) => boolean): Promise<Partial<Record<Lane, string>>> {
  const outs: Partial<Record<Lane, string>> = {};
  const jobs: Promise<void>[] = [];
  if (on("js")) {
    jobs.push(sh(process.execPath, [path.join(dir, "p.js")], T_RUN,
      { BUN_JSC_maxPerThreadStackUsage: "33554432" }).then((r) => { outs.js = ran(r); }));
  }
  if (on("c")) {
    jobs.push(sh(CC, ["-std=c11", "-O3", path.join(dir, "p.c"), "-lpthread", "-lm", "-o", path.join(dir, "p")], 120_000)
      .then(async (b) => {
        outs.c = b.code !== 0 ? "§build " + b.out.slice(0, 400) : ran(await sh(path.join(dir, "p"), [], T_RUN));
      }));
  }
  if (on("san")) {
    jobs.push(sh(CC, ["-std=c11", "-O0", "-fsanitize=address,undefined",
      path.join(dir, "p.c"), "-lpthread", "-lm", "-o", path.join(dir, "ps")], 120_000)
      .then(async (b) => {
        outs.san = b.code !== 0 ? "§build " + b.out.slice(0, 400) : ran(await sh(path.join(dir, "ps"), [], T_RUN * 3,
          { ASAN_OPTIONS: "detect_leaks=0", UBSAN_OPTIONS: "print_stacktrace=1" }));
      }));
  }
  await Promise.all(jobs);
  return outs;
}

// the lanes a program runs in; `want` narrows them (the reducer's)
async function lanes(pool: Pool, text: string, twin: string | null, want?: Set<Lane>): Promise<Verdict> {
  const [dir, idx] = newdir();
  try {
    const on = (l: Lane): boolean => want === undefined ? (l !== "san" || (SAN && idx % SAN_EVERY === 0)) : want.has(l);
    const rep = await pool.run({ id: 0, text, twin, dir, interp: on("interp"), emit: true });
    if (rep === null) return { ok: true, outs: { interp: "§timeout" }, sig: "", ref: null };
    if (!rep.ok) return { ok: false, err: rep.err, outs: {}, sig: "", ref: null };
    const outs = await compiled(dir, on);
    if (on("interp")) outs.interp = interp_out(rep.interp ?? "", twin !== null);
    return { ok: true, outs, ...judge(outs) };
  } finally {
    fs.rmSync(dir, { recursive: true, force: true });
  }
}

// Programs of one kind at once: each checked and normalized alone, then
// built and run as one (one clang, one bun); the outputs split at SEP. A
// build or a run that fails, or does not split, runs each alone.
async function batch(pool: Pool, ps: G.Prog[], san: boolean): Promise<(Verdict | null)[]> {
  const io = ps[0].io;
  const got = await Promise.all(ps.map(async (p) => {
    const [dir] = newdir();
    try {
      const [text, twin] = render(p);
      return await pool.run({ id: 0, text, twin, dir, interp: true, emit: false });
    } finally {
      fs.rmSync(dir, { recursive: true, force: true });
    }
  }));
  const vs: (Verdict | null)[] = got.map((r) => r === null ? null
    : r.ok ? { ok: true, outs: {}, sig: "", ref: null } : { ok: false, err: r.err, outs: {}, sig: "", ref: null });
  const live = ps.map((_, i) => i).filter((i) => vs[i]?.ok === true);
  if (live.length === 0) return vs;
  const alone = async (): Promise<void> => {
    for (const i of live) vs[i] = await lanes(pool, ...render(ps[i]));
  };
  const [dir] = newdir();
  try {
    const rep = await pool.run({ id: 0, text: G.batch_render(live.map((i) => ps[i])), twin: null, dir,
      interp: false, emit: true });
    if (rep === null || !rep.ok) {
      await alone();
      return vs;
    }
    const outs = await compiled(dir, (l) => l === "js" || l === "c" || (l === "san" && san));
    const split = (o: string | undefined): string[] | null => {
      if (o === undefined || /§|runtime error|AddressSanitizer/.test(o)) return null;
      if (!io) {
        const m = /^"(.*)"$/s.exec(o);
        const xs = m === null ? [] : m[1].split(G.SEP).map((x) => "\"" + x + "\"");
        return xs.length === live.length ? xs : null;
      }
      const xs = o.split(new RegExp("^" + G.SEP + "$", "m")).map(tidy);
      return xs.length === live.length + 1 && xs[live.length] === "end" ? xs.slice(0, -1) : null;
    };
    const parts: Partial<Record<Lane, string[] | null>> = {};
    for (const l of ["js", "c", "san"] as Lane[]) if (outs[l] !== undefined) parts[l] = split(outs[l]);
    if (Object.values(parts).some((x) => x === null)) {
      await alone();
      return vs;
    }
    live.forEach((i, j) => {
      const o: Partial<Record<Lane, string>> = {};
      for (const l of ["js", "c", "san"] as Lane[]) if (parts[l]) o[l] = parts[l]![j];
      const v = got[i]!.interp ?? "";
      const u = io ? unshow(v) : null;
      o.interp = !io ? interp_out(v, false) : u === null ? "§stuck " + v.slice(0, 200) : tidy(u);
      vs[i] = { ok: true, outs: o, ...judge(o) };
    });
    // a difference seen in the batch is judged again alone, as the reducer sees it
    for (const i of live) {
      if (vs[i]!.sig !== "") vs[i] = await lanes(pool, ...render(ps[i]));
    }
    return vs;
  } finally {
    fs.rmSync(dir, { recursive: true, force: true });
  }
}

// The reference is the interpreter unless it is stuck (F64 is opaque to
// it) or timed out; then JS. The signature names each lane that differs
// from it, and how: its output, its exit, a signal or a sanitizer report.
function judge(outs: Partial<Record<Lane, string>>): { sig: string; ref: Lane | null } {
  const good = (s: string | undefined): boolean => s !== undefined && !s.startsWith("§");
  const ref: Lane | null = good(outs.interp) ? "interp" : good(outs.js) ? "js" : good(outs.c) ? "c" : null;
  const bad: string[] = [];
  const how = (s: string): string => /runtime error|AddressSanitizer|LeakSanitizer/.test(s) ? "report"
    : /§signal/.test(s) ? "signal" : /§exit/.test(s) ? "exit" : /^§build/.test(s) ? "build" : "out";
  for (const l of ["js", "c", "san"] as Lane[]) {
    const s = outs[l];
    if (s === undefined || l === ref) continue;
    if (l === "js" && /JS strings cannot contain non-scalar/.test(s)) {
      continue; // by design: a JS string holds scalar values only
    } else if (l === "san" && /runtime error|AddressSanitizer/.test(s)) {
      bad.push("san:report");
    } else if (ref === null ? s.startsWith("§") : s !== outs[ref]) {
      bad.push(l + ":" + how(s));
    }
  }
  if (ref === null && outs.interp !== undefined && !outs.interp.startsWith("§stuck")) {
    bad.push("all:" + outs.interp.slice(0, 20).replace(/\s/g, "_"));
  }
  return { sig: bad.join(" "), ref };
}

// Reduce
// ======

type Cand = { text: string; twin: string | null; apply: () => void };

// Each edit of the tree, applied, rendered and undone in turn; the first
// (in tree order) that still checks and still differs the same way stays.
function edits(p: G.Prog): { name: string; go: () => () => void }[] {
  const out: { name: string; go: () => () => void }[] = [];
  const arr = <X>(xs: X[], i: number): () => () => void => () => {
    const [x] = xs.splice(i, 1);
    return () => { xs.splice(i, 0, x); };
  };
  for (let i = p.parts.length - 1; i >= 0; i--) out.push({ name: "part", go: arr(p.parts, i) });
  for (let i = p.stmts.length - 1; i >= 0; i--) out.push({ name: "stmt", go: arr(p.stmts, i) });
  for (let i = p.lets.length - 1; i >= 0; i--) out.push({ name: "let", go: arr(p.lets, i) });
  for (let i = p.defs.length - 1; i >= 0; i--) out.push({ name: "def", go: arr(p.defs, i) });
  const body = (holder: { body: G.Body }): void => {
    const b = holder.body;
    if (b.$ === "mat") {
      for (const a of b.arms) {
        out.push({ name: "arm", go: () => { holder.body = a.body; return () => { holder.body = b; }; } });
      }
      for (const a of b.arms) body(a);
    } else {
      for (let i = b.lets.length - 1; i >= 0; i--) out.push({ name: "let", go: arr(b.lets, i) });
      for (const l of b.lets) l.v.forEach(node);
      node(b.e);
    }
  };
  const node = (n: G.Node): void => {
    const leaf = G.LEAF[n.ty];
    if (!(n.parts.length === 1 && n.parts[0] === leaf)) {
      out.push({ name: "leaf", go: () => { const ps = n.parts; n.parts = [leaf]; return () => { n.parts = ps; }; } });
    }
    for (const k of n.parts) {
      if (typeof k !== "string" && k.ty === n.ty) {
        out.push({ name: "hoist", go: () => { const ps = n.parts; n.parts = k.parts; return () => { n.parts = ps; }; } });
      }
    }
    for (const k of n.parts) if (typeof k !== "string") node(k);
  };
  p.parts.forEach(node);
  p.stmts.forEach((s) => {
    node(s.e);
    if (s.pick !== undefined) {
      node(s.pick.c);
      node(s.pick.b);
      out.push({ name: "unpick", go: () => { const k = s.pick; delete s.pick; return () => { s.pick = k; }; } });
    }
  });
  p.lets.forEach((l) => l.v.forEach(node));
  p.defs.forEach(body);
  return out;
}

function render(p: G.Prog): [string, string | null] {
  return [G.prog_render(p), p.io ? G.prog_render(p, true) : null];
}

async function reduce(pool: Pool, p: G.Prog, sig: string, log: (s: string) => void): Promise<G.Prog> {
  // the lanes the signature needs: the reference and each differing lane
  const want = new Set<Lane>(["interp", "js"]);
  for (const s of sig.split(" ")) want.add(s.split(":")[0] as Lane);
  want.delete("all" as Lane);
  const keeps = (v: Verdict): boolean => v.ok && v.sig === sig;
  let size = render(p)[0].length;
  for (let round = 0; ; round++) {
    let hit = false;
    const es = edits(p);
    for (let i = 0; i < es.length; i += JOBS) {
      // JOBS candidates at once; the first that keeps the difference wins
      const cands: Cand[] = [];
      for (const e of es.slice(i, i + JOBS)) {
        const undo = e.go();
        const [text, twin] = render(p);
        undo();
        if (text.length < size) cands.push({ text, twin, apply: () => { e.go(); } });
      }
      const vs = await Promise.all(cands.map((c) => lanes(pool, c.text, c.twin, want)));
      const j = vs.findIndex(keeps);
      if (j >= 0) {
        cands[j].apply();
        size = render(p)[0].length;
        log("  reduce: " + String(size) + " bytes");
        hit = true;
        break;
      }
    }
    if (!hit) return p;
  }
}

// Main
// ====

// runs of BATCH pure programs, then a run of IO ones (a quarter)
function kind(i: number): { io: boolean; f64: boolean } {
  const io = Math.floor(i / BATCH) % 4 === 3;
  return { io, f64: !io && i % 7 === 5 };
}

function parse_one(s: string): { seed: number; io: boolean; f64: boolean } {
  const [n, k] = s.split(":");
  return { seed: Number(n), io: k === "io", f64: k === "f64" };
}

async function main(): Promise<void> {
  if (ARGS.includes("--worker")) {
    return worker();
  }
  const pool = new Pool(JOBS);
  for (const sig of ["SIGINT", "SIGTERM"] as const) {
    process.on(sig, () => {
      pool.close();
      fs.rmSync(TMP, { recursive: true, force: true });
      process.exit(130);
    });
  }
  const log = (s: string): void => { process.stdout.write(s + "\n"); };
  const outdir = opt("--out") ?? path.join(os.tmpdir(), "bend-fuzz-found");
  fs.mkdirSync(outdir, { recursive: true });
  try {
    if (opt("--file") !== undefined) {
      const text = fs.readFileSync(opt("--file")!, "utf8");
      const v = await lanes(pool, text, null);
      log(v.ok ? JSON.stringify(v, null, 1) : "rejected: " + v.err);
      return;
    }
    const seed0 = Number(opt("--seed") ?? (CI ? 1 : Date.now() % 1000000));
    const n = Number(opt("--n") ?? (CI ? 60 : 200));
    const secs = Number(opt("--time") ?? 0);
    const one = opt("--one");
    const todo = one !== undefined ? [parse_one(one)]
      : Array.from({ length: n }, (_, i) => ({ seed: seed0 * 100003 + i, ...kind(i) }));
    const stats = { gen: 0, rej: 0, run: 0, same: 0, diff: 0, slow: 0, rejs: new Map<string, number>() };
    const sigs = new Map<string, string[]>();
    const t0 = Date.now();
    let next = 0;
    const found: { seed: string; sig: string; p: G.Prog; v: Verdict }[] = [];
    const note = (t: { seed: number; io: boolean; f64: boolean }, p: G.Prog, v: Verdict | null): void => {
      const tag = String(t.seed) + (t.io ? ":io" : t.f64 ? ":f64" : "");
      stats.gen += 1;
      if (stats.gen % 50 === 0) {
        log("... " + String(stats.gen) + " programs, " + String(stats.rej) + " rejected, "
          + String(stats.diff) + " differ, " + ((Date.now() - t0) / 1000).toFixed(0) + " s");
      }
      if (v === null) {
        stats.run += 1;
        stats.slow += 1;
        return;
      }
      if (!v.ok) {
        stats.rej += 1;
        const why = (v.err ?? "").split("\n").slice(0, 3).join(" ").replace(/[a-z]+[0-9]+/g, "_").slice(0, 90);
        stats.rejs.set(why, (stats.rejs.get(why) ?? 0) + 1);
        if (one !== undefined) log(v.err ?? "");
        if (stats.rej <= 40) fs.writeFileSync(path.join(outdir, "rej_" + tag.replace(":", "_") + ".bend"),
          render(p)[0] + "\n# " + (v.err ?? "").split("\n").join("\n# ") + "\n");
        return;
      }
      stats.run += 1;
      if (v.outs.interp === "§timeout") {
        stats.slow += 1;
        return;
      }
      if (v.sig === "") {
        stats.same += 1;
        if (one !== undefined) log(JSON.stringify(v.outs, null, 1));
        return;
      }
      stats.diff += 1;
      sigs.set(v.sig, [...sigs.get(v.sig) ?? [], tag]);
      found.push({ seed: tag, sig: v.sig, p, v });
      fs.writeFileSync(path.join(outdir, "s" + tag.replace(":", "_") + ".bend"), render(p)[0]);
      log("DIFF " + tag + " [" + v.sig + "]");
      for (const [l, o] of Object.entries(v.outs)) log("  " + l + ": " + (o ?? "").slice(0, 300).replace(/\n/g, "\\n"));
    };
    let nb = 0;
    const go = async (): Promise<void> => {
      while (next < todo.length && (secs === 0 || Date.now() - t0 < secs * 1000)) {
        // BATCH programs of one kind (pure or IO), tagged apart
        const k = todo[next].io;
        const ts: typeof todo = [];
        while (next < todo.length && ts.length < BATCH) {
          const t = todo[next];
          if (t.io !== k) break;
          ts.push(t);
          next += 1;
        }
        const ps = ts.map((t, j) => G.prog_gen(t.seed, t.io, t.f64, ts.length > 1 ? "q" + String(j) + "_" : ""));
        const vs = ts.length === 1 ? [await lanes(pool, ...render(ps[0]))].map((v) =>
          v.outs.interp === "§timeout" ? null : v)
          : await batch(pool, ps, SAN && nb++ % SAN_EVERY === 0);
        ts.forEach((t, j) => note(t, ps[j], vs[j]));
      }
    };
    await Promise.all(Array.from({ length: JOBS }, go));
    const dt = (Date.now() - t0) / 1000;
    log("programs " + String(stats.gen) + ", rejected " + String(stats.rej) + " ("
      + (100 * stats.rej / Math.max(1, stats.gen)).toFixed(1) + "%), ran " + String(stats.run)
      + ", agreed " + String(stats.same) + ", differed " + String(stats.diff)
      + ", interp timeouts " + String(stats.slow) + ", " + dt.toFixed(0) + " s");
    for (const [why, k] of [...stats.rejs].sort((a, b) => b[1] - a[1]).slice(0, 6)) {
      log("  reject x" + String(k) + ": " + why);
    }
    for (const [s, tags] of sigs) log("  [" + s + "] x" + String(tags.length) + ": " + tags.slice(0, 8).join(" "));
    if (ARGS.includes("--reduce")) {
      // one reduction per distinct signature
      const done = new Set<string>();
      for (const f of found) {
        if (done.has(f.sig)) continue;
        done.add(f.sig);
        log("reducing " + f.seed + " [" + f.sig + "]");
        const small = await reduce(pool, f.p, f.sig, log);
        const [text] = render(small);
        const at = path.join(outdir, "min_" + f.seed.replace(":", "_") + ".bend");
        fs.writeFileSync(at, text);
        if (small.io) fs.writeFileSync(at.replace(".bend", "_twin.bend"), render(small)[1]!);
        const v = await lanes(pool, text, small.io ? render(small)[1] : null);
        log("minimal (" + at + "):\n" + text.split("\n").filter((l) => l !== "").join("\n"));
        for (const [l, o] of Object.entries(v.outs)) log("  " + l + ": " + (o ?? "").slice(0, 300).replace(/\n/g, "\\n"));
      }
    }
    if (stats.diff > 0 || (CI && stats.run === 0)) {
      process.exitCode = 1;
      log("FAIL: " + String(stats.diff) + " programs differ (rerun one with --one SEED --reduce)");
    } else {
      log("PASS: " + String(stats.same) + " / " + String(stats.run - stats.slow) + " programs agree");
    }
  } finally {
    pool.close();
    if (!ARGS.includes("--keep")) fs.rmSync(TMP, { recursive: true, force: true });
  }
}

await main();
