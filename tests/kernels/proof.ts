// Check the complete import closure, including bodies unreachable from the last law.
import * as B from "../../bend2/bend.ts";
import * as fs from "node:fs";
import * as path from "node:path";
import * as crypto from "node:crypto";
import * as child from "node:child_process";

const root = path.resolve(import.meta.dir, "../..");
const entry = path.resolve(process.argv[2] ?? path.join(root, "demos/kernels/PROOF.bend"));
const receipt = process.argv[3];
const sources = new Map<string, string>();
function closure(file: string): void {
  file = path.resolve(file);
  if (sources.has(file)) return;
  const source = fs.readFileSync(file, "utf8");
  sources.set(file, source);
  for (const match of source.matchAll(/^import\s+(\S+)/gm)) {
    const imported = match[1] === "Base" ? path.join(root, "bend2/base.bend")
      : path.resolve(path.dirname(file), match[1]);
    closure(imported);
  }
}
try {
  closure(entry);
  if (/^(def|law) main\b/m.test(sources.get(entry)!)) throw Error("proof entry must have no main");
  const lawsFile = path.join(path.dirname(entry), "LAWS.bend");
  const laws = [...sources.get(lawsFile)!.matchAll(/^law (\w+):/gm)].map(m => m[1]);
  if (!laws.length) throw Error("empty public contract");
  for (const [file, source] of sources) {
    if (file.endsWith("/bend2/base.bend")) continue;
    for (const match of source.matchAll(/^def (\w+\.[\w.]+)\(/gm)) {
      if (file !== entry || !laws.includes(match[1].replace(/^L\./, "")) || !match[1].startsWith("L.")) {
        throw Error("unexpected imported definition override: " + match[1]);
      }
    }
  }
  const book = B.book_nil();
  await B.book_load(book, entry, "", new Map());
  for (const [name, def] of Object.entries(book.tlds)) {
    if (def.$ === "Def" && def.u) throw Error("unsafe dependency: " + name);
  }
  // Base declares IO effects, but pure claims must never depend on their bodies.
  const base = B.book_nil();
  await B.book_load(base, path.join(root, "bend2/base.bend"), "", new Map());
  const pending = Object.keys(book.tlds).filter(name => !(name in base.tlds));
  const reached = new Set<string>();
  function references(term: B.HTerm): void {
    const nodes: any[] = [B.term_lower(term)];
    while (nodes.length) {
      const node = nodes.pop();
      if (!node || typeof node !== "object") continue;
      if (node.$ === "Ref" || node.$ === "ADT") pending.push(node.k);
      if (node.$ === "Ctr" && book.ctrs[node.k] && !constructors.has(node.k)) {
        constructors.add(node.k);
        references(book.ctrs[node.k].T);
      }
      for (const [key, value] of Object.entries(node)) {
        if (key !== "s" && typeof value === "object") nodes.push(...(Array.isArray(value) ? value : [value]));
      }
    }
  }
  // Constructor types are visited once to avoid recursive datatype cycles.
  const constructors = new Set<string>();
  function definition(name: string): void {
    if (reached.has(name)) return;
    reached.add(name);
    const def = book.tlds[name];
    if (!def) throw Error("missing definition in closure: " + name);
    if (def.$ === "Def" && def.i) throw Error("foreign dependency: " + name);
    references(def.T);
    if (def.$ === "Def" && def.v) references(def.v);
  }
  while (pending.length) definition(pending.pop()!);
  B.book_valid(book);
  if (book.hols || book.open) throw Error(`holes=${book.hols}, open=${book.open}`);
  for (const name of laws) {
    const definition = book.tlds["LAWS." + name];
    if (definition?.$ !== "Def" || !definition.v) throw Error("unfilled public law: " + name);
  }
  for (const [file, before] of sources) {
    if (fs.readFileSync(file, "utf8") !== before) throw Error("source changed during check: " + file);
  }
  const sha = (content: string | Buffer) => crypto.createHash("sha256").update(content).digest("hex");
  const hashes = Object.fromEntries([...sources].sort().map(([file, content]) => [path.relative(root, file), sha(content)]));
  hashes["bend2/bend.ts"] = sha(fs.readFileSync(path.join(root, "bend2/bend.ts")));
  hashes["tests/kernels/proof.ts"] = sha(fs.readFileSync(import.meta.path));
  const report = { verdict: "checked-by-Bend", entry: path.relative(root, entry), laws,
    definitions: Object.keys(book.tlds).length, pure_dependencies: reached.size, holes: book.hols, open: book.open,
    unsafe: 0, foreign: 0, source_sha256: hashes,
    git_head: child.execFileSync("git", ["rev-parse", "HEAD"], {cwd: root, encoding: "utf8"}).trim(),
    trust: "Bend checker, Base semantics, spec transcription; not compiler, hardware or timing" };
  if (receipt) fs.writeFileSync(receipt, JSON.stringify(report, null, 2) + "\n");
  console.log(`Proof PASS: ${laws.length} public laws; closure ${report.definitions} definitions; no holes, open laws, unsafe or foreign definitions.`);
  for (const name of laws) console.log("checked-by-Bend " + name);
} catch (error: any) {
  console.error(error?.$ === "Err" ? B.err_show(error) : String(error));
  console.error("Proof FAIL");
  process.exit(1);
}
