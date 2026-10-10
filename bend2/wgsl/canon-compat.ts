// Canon-compat
// ============

// wgsl.ts reads the compiler through this module as `C`. It was written against
// a comp.ts that passes the file and the book as arguments and exports its
// helpers; this repo's comp.ts keeps the book in one module state (FL) and
// exports five functions. comp.ts is the compiler's one file and sits at its
// ttok cap, so it is not edited: the names wgsl.ts needs are exported from a
// copy of its text, loaded once, that shares this repo's bend.ts. The copy goes
// to the temp dir, named by the hash of its text.

import * as crypto from "node:crypto";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { fileURLToPath } from "node:url";

import * as Bend from "../bend.ts";

// Types
// =====

export type HTerm = Bend.HTerm;
export type Name = Bend.Name;
export type Of<K> = Extract<HTerm, { $: K }>;
export type HLet = Of<"Let">;
export type Def = Bend.Def & { h?: HTerm };
export type Carb = { book: Bend.Book };
export type File = Carb & { seg: { lines: string[] }; fresh: Map<string, number>;
  tab: number };

type Spine = { h: HTerm; t: HTerm; all: HTerm[]; args: HTerm[];
  tld: Bend.TLD | undefined; k: Name | null; xs: HTerm[]; b?: boolean };
type Call = { k: Name; args: HTerm[]; all: HTerm[]; bang?: boolean };

// The copy
// ========

const NAMES = ("CLO_APPLY CMPS DUMMY adt_of call_eta ctr_adt ctr_flds"
  + " def_foreign die done_live fun_of intr_of let_live mat_arms mat_ctrs"
  + " mat_head memo_gc name_local op_name quant_live term_kids term_spine"
  + " term_strip tpl ty_all ty_peel").split(" ");

const HERE = path.dirname(fileURLToPath(import.meta.url));

// file_open starts the compile of a book: FL is a `let` no export can set.
const TAIL = `\nexport { ${NAMES.join(", ")} };\n`
  + "export function file_open(book: Bend.Book, roots: Bend.Name[]): void {\n"
  + "  FL = file_new(book, true);\n  file_book(roots);\n}\n"
  + "export function file_srcs(): Bend.Name[] { return [...FL.srcs.keys()]; }\n";

async function comp_load(): Promise<any> {
  const text = fs.readFileSync(path.join(HERE, "../comp.ts"), "utf8")
    .replace('from "./bend.ts"', `from ${JSON.stringify(path.join(HERE,
      "../bend.ts"))}`) + TAIL;
  const out = path.join(os.tmpdir(), "bend-wgsl-comp-"
    + crypto.createHash("sha1").update(text).digest("hex").slice(0, 16) + ".ts");
  if (!fs.existsSync(out)) {
    fs.writeFileSync(out + "." + process.pid, text);
    fs.renameSync(out + "." + process.pid, out);
  }
  return await import(out);
}

const X = await comp_load();

// Re-exports
// ==========

export const { CMPS, DUMMY, die, def_foreign, memo_gc, tpl, term_strip,
  ty_peel, quant_live, mat_head } = X;

// The names the old comp.ts took the file or the book for
// =======================================================

export const adt_of = (_: unknown, A: HTerm | null): Of<"ADT"> => X.adt_of(A);
export const ty_all = (_: unknown, A: HTerm | null): Of<"All"> => X.ty_all(A);
export const ctr_flds = (_: unknown, k: Name, xs: HTerm[]): HTerm[] =>
  X.ctr_flds(k, xs);
export const ctr_adt = (_: unknown, x: Of<"Ctr">, ty: HTerm | null) =>
  X.ctr_adt(x, ty) as [Of<"ADT">, number | null];
export const let_live = (_: unknown, x: HLet): boolean[] => X.let_live(x);
export const term_kids = (_: unknown, t: HTerm): HTerm[] => X.term_kids(t);
export const call_eta = (_: unknown, t: HTerm): HTerm | null => X.call_eta(t);
export const mat_ctrs = (_: unknown, x: HTerm, adt: Of<"ADT">):
  [Name, HTerm][] => X.mat_ctrs(x, adt);
export const name_local = (fl: File, k: Name): string => X.name_local(fl, k);
export const eff_name = (k: Name): string => X.op_name(k);
export const sig_def = (_: unknown, k: Name) => X.fun_of(k) as
  { live: [Bend.Quant, Name, HTerm][]; lays: unknown[]; ret: { ks: string[] } };

// Bytes is a String of bytes (base.bend); the emitter reads Bytes.get and
// Bytes.word_le as the lane's buffer reads, so they answer as operations.
export function intr_of(_: unknown, k: Name, js = false): unknown {
  return X.intr_of(k, js)
    ?? (k === "Bytes.get" || k === "Bytes.word_le" ? { JS: "" } : undefined);
}

// A term's application view, and the call it is (Clo.apply for a closure).
export function term_spine(_: unknown, t: HTerm): Spine & { call: Call | null } {
  const s: Spine = X.term_spine(t);
  return { ...s, call: call_of(s) };
}

export function call_kind(_: unknown, t: HTerm): Call | null {
  return call_of(X.term_spine(t));
}

function call_of(s: Spine): Call | null {
  return s.k === null ? null : { k: s.k, args: s.xs,
    all: s.k === X.CLO_APPLY ? s.xs : s.all, bang: s.b };
}

// A Nat match's arms as (arm, n): n null a literal arm (the scrutinee is its
// position), else the arm that takes the predecessor n below the scrutinee.
// A default arm has no such form: null.
export function emit_nats(adt: Of<"ADT">, x: HTerm): [HTerm, number | null][] | null {
  const rows: [HTerm, number | null][] = [];
  if (adt.k !== "Nat") {
    return null;
  }
  for (let m = x, n = 0; ; n++) {
    const { arms } = X.mat_arms(m);
    const { Zero, Succ } = Object.fromEntries(arms);
    if (Zero === undefined || Succ === undefined) {
      return null;
    }
    rows.push([Zero, null]);
    m = X.term_strip(Succ);
    if (m.$ !== "Mat") {
      rows.push([Succ, n + 1]);
      return rows;
    }
  }
}

// The emission context
// ====================

export function file_push(fl: File, line: string): void {
  fl.seg.lines.push("  ".repeat(fl.tab) + line);
}

export function block(fl: File, open: string, go: () => void): void {
  file_push(fl, open);
  fl.tab += 1;
  go();
  fl.tab -= 1;
  file_push(fl, "}");
}

export function file_new(cb: Carb, _js: boolean): File {
  return { book: cb.book, seg: { lines: [] }, fresh: new Map(), tab: 2 };
}

// carb_book opens the compile of the book at the roots, and gives the book
// back with every def it reaches raised (n and h as comp.ts's fun_of has them).
export function carb_book(src: Bend.Book, roots: Name[]): Carb {
  X.file_open(src, roots);
  const tlds = { ...src.tlds };
  for (const k of X.file_srcs() as Name[]) {
    const tld = tlds[k];
    if (X.done_live(tld)) {
      const f = X.fun_of(k);
      tlds[k] = { ...tld, n: f.n, h: f.h } as Def;
    }
  }
  return { book: { ...src, tlds } };
}
