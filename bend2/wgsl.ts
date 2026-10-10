// Wgsl: the WebGPU lane (bend -o x.wgsl), beside comp.ts's C and JS.
//
// WGSL cannot take the device program as Metal and NVRTC do (comp.ts's
// Dialect block): it has no u64, no pointer into a corpus, no preprocessor and
// no recursion. So this lane emits WGSL from terms, for the defs that fit its
// envelope, and runs them on the entries below. Entries are what the host
// dispatches; a book names them, and the first line of the .wgsl lists them
// (bend-wgsl/2: a manifest the host runtime reads).
//
// Defs (an instance of each is emitted where an entry or another def calls it):
// - a scalar def: F32 / U32 / Bool / Nat words in, one word out; lets, word
//   reinterprets (f32_from_bits), Bool and Nat matches; a Nat as a u32 that
//   flags its overflow (the run then answers "past the envelope", never a
//   wrong number);
// - a fold: a def whose one self call is on its Nat's predecessor with its
//   other parameters unchanged (pow2) becomes a loop;
// - a flat tail loop (spin): a def whose self calls are all its last act
//   becomes a loop over its parameters (Nat fuel counting down);
// - shape specialisation: a recursion on a Nat that a call gives as a literal
//   is unrolled, one WGSL fn per (def, literal), as WGSL has no recursion;
// - Bytes: a buffer parameter is a storage binding read by Bytes.get /
//   Bytes.word_le (a byte past the end is 0, as the C lane's); the def is
//   instanced per buffer it is given;
// - the F64 chains (F64.to_f32 (F64.exp (F32.to_f64 x)) and its siblings,
//   softplus's log (1 + exp x)) are x32's integer forms (x32w.ts);
// - f32 + - * are calls the GPU's compiler cannot fuse, reassociate or take a
//   zero's sign through (see OPS).
//
// Entries:
// - a fork tree under a bang, SHADERS.md's shape: f(d, xs) = match d: 0 ->
//   a leaf of xs; 1 + p -> a b = f(p, ls(p, xs)) f(p, rs(p, xs)); j(a, b).
//   One lane a leaf: lane L walks L's bits from the root to its xs, then the
//   joins run as the perfect tree over lanes, a workgroup at a time; a join
//   that reads its node's level and parameters finds them by the same walk;
// - a cube: a book's cube.<name>.n / leaf / join / fin / out (+ len, pad,
//   bind), the "leaf, tree of joins, finish, map" row of a norm or a
//   matrix-vector product; a workgroup a row, any n up to 2^20;
// - a map: map.<name>.f (+ len, rowlen, bind), one invocation an element.
//
// Outside the envelope (each a die naming it): F64 (WGSL has none), heap data
// (lists, trees, strings, arrays), closures, IO, general recursion on a Nat
// that is not a literal. Such programs keep the C / JS lanes.

import * as Bend from "./bend.ts";
import * as C from "./wgsl/canon-compat.ts";
import { x32wSource } from "./x32w.ts";
import { X32A } from "./x32a.ts";

type File = C.File;
type HTerm = C.HTerm;
type Name = C.Name;
type Def = C.Def;

const die = C.die;

// WGSL says + - * are correctly rounded and / and sqrt within 2.5 ulp; Apple's
// GPU misses IEEE by 1 on / and sqrt under Chrome and Safari: x32w.ts's x32_div
// and x32_sqrt round them as the C lane's (f32) ops do, in integers.
const OPS: Record<string, string> = {
  ...Object.fromEntries("add:+ sub:- mul:* and:& or:| xor:^".split(" ")
    .map((s) => s.split(":")).map(([k, o]) => ["u32_" + k, `($0 ${o} $1)`])),
  ...Object.fromEntries(C.CMPS.split(" ").map((s) => s.split(":"))
    .flatMap(([k, o]) => [["u32_" + k, `($0 ${o} $1)`],
      ["f32_" + k, `($0 ${o} $1)`]])),
  u32_div: "select($0 / $1, 0u, $1 == 0u)",
  u32_mod: "select($0 % $1, $0, $1 == 0u)",
  u32_inc: "($0 + 1u)",
  u32_shl: "($0 << 1u)",
  u32_shr: "($0 >> 1u)",
  u32_shln: "select($0 << $1, 0u, $1 >= 32u)",
  u32_shrn: "select($0 >> $1, 0u, $1 >= 32u)",
  u32_not: "(~$0)",
  u32_is_zero: "($0 == 0u)",
  u32_to_f32: "f32($0)",
  u32_to_nat: "$0",
  u32_from_nat: "$0",
  // Integer IEEE arithmetic preserves every rounded operation, signed zero
  // and subnormal. Hardware fma barriers still flush operands/results.
  f32_add: "x32_add($0, $1)",
  f32_sub: "x32_sub($0, $1)",
  f32_mul: "x32_mul($0, $1)",
  f32_div: "x32_div($0, $1)",
  f32_neg: "bitcast<f32>(bitcast<u32>($0) ^ 0x80000000u)",
  // x != x must find a NaN: the GPU's compiler may assume there is none and
  // fold it to false, so the test reads the bits (receipts: argmax's NaN row)
  f32_is_ne: "fne($0, $1)",
  f32_max: "max($0, $1)",
  f32_min: "min($0, $1)",
  f32_sqrt: "x32_sqrt($0)",
  ...Object.fromEntries("abs floor ceil trunc".split(" ")
    .map((k) => ["f32_" + k, `${k}($0)`])),
  f32_bits: "bitcast<u32>($0)",
  nat_add: "nat_add($0, $1)",
  nat_sub: "select($0 - $1, 0u, $0 < $1)",
  nat_mul: "nat_mul($0, $1)",
  nat_double: "nat_add($0, $0)",
  nat_is_lt: "($0 < $1)",
  nat_min: "min($0, $1)",
  nat_max: "max($0, $1)",
  bool_or: "($0 || $1)",
  bool_xor: "($0 != $1)",
};

function sat(k: Name): string {
  return "b_" + k.replace(/\W/g, "_");
}

// The WGSL type of a word: f32, u32 (U32 and Nat) or bool. A Bytes (a String
// below 256 in every Char) is a buffer: "bytes", never passed, a global
// binding that a token names.
function ty_of(fl: File, A: HTerm | null, what: string): string {
  const k = C.adt_of(fl.book, A).k;
  return k === "F32" ? "f32" : k === "U32" || k === "Nat" ? "u32"
    : k === "Bool" ? "bool" : k === "String" ? "bytes"
    : die("WGSL: " + what + " is a " + k + ", outside the lane's words"
      + " (F32, U32, Bool, Nat) and Bytes");
}

// The emission context: the def a fold is rewriting (its self call on the
// predecessor answers the accumulator), or a spin loop (its self calls are
// jumps: the loop's variables and which parameters they carry).
type Fold = { k: Name; p: string; rest: string[] };
type Spin = { k: Name; vs: string[]; keep: boolean[] };
let FOLD: Fold | null = null;
let SPIN: Spin | null = null;

// A def is emitted once per instance: its Bytes parameters bound to buffer
// tokens (the names of global bindings) and its recursion Nat to a literal.
// "plain" has no self call; "fold" and "spin" are loops; "rec" recurses on a
// Nat and so needs a literal (unrolled, one fn per literal).
type Mode = "plain" | "fold" | "spin" | "rec";
type Inst = { k: Name; name: string; toks: (string | null)[];
  stat: (number | null)[] };
const MODES = new Map<Name, Mode>();
const INSTS = new Map<string, Inst>();
const QUEUE: Inst[] = [];
let TRIAL = false;
const INST_MAX = 4096;

// A buffer token: the global binding's array and its byte length (WGSL
// expressions); `used` once a Bytes read names it.
type Buf = { arr: string; len: string; used: boolean };
const BUFS = new Map<string, Buf>();

function inst(k: Name, toks: (string | null)[], stat: (number | null)[]): string {
  const part = toks.map((t, j) => t !== null ? t : stat[j] !== null
    ? `s${j}x${stat[j]}` : null).filter((x) => x !== null).join("_");
  const name = sat(k) + (part === "" ? "" : "_" + part);
  if (!TRIAL && !INSTS.has(name)) {
    if (INSTS.size >= INST_MAX) {
      die("WGSL: more than " + INST_MAX + " instances (a recursion that does not"
        + " bottom out on a literal): " + k);
    }
    const it = { k, name, toks, stat };
    INSTS.set(name, it);
    QUEUE.push(it);
  }
  return name;
}

function open(fl: File, x: C.HLet): HTerm {
  const on = C.let_live(fl, x);
  return x.f(x.v.map((v, j): HTerm => {
    if (!on[j]) {
      return v;
    }
    const al = C.name_local(fl, x.k[j]);
    C.file_push(fl, `let ${al} = ${expr(fl, v, null)};`);
    return Bend.Var(al, 0);
  }));
}

// A Bytes read: the buffer is the token the first argument names, the read a
// global fn over its binding (bg_ one byte, bw_ four bytes little end first).
function bytes_op(k: Name, xs: string[]): string {
  const b = BUFS.get(xs[0]);
  if (b === undefined) {
    die("WGSL: " + k + " on a Bytes that is not one of the lane's buffers");
  }
  b.used = true;
  const fn = k.endsWith("bytes_get") || k === "Bytes.get" ? "bg_"
    : k.endsWith("bytes_word_le") || k === "Bytes.word_le" ? "bw_"
    : die("WGSL: no WGSL form for the operation " + k);
  return fn + xs[0] + "(" + xs[1] + ")";
}

// The F64 chains that spell a correctly rounded f32 function, as the C lane
// runs them ((f32)exp((double)x) and its siblings; softplus's log(1 + exp x)):
// X32's integer forms answer them with F64 gone from the device program.
function x32_chain(fl: File, k: Name, args: HTerm[]): string | null {
  if (C.eff_name(k) !== "f64_to_f32" || args.length !== 1) {
    return null;
  }
  const sub = (t: HTerm): { en: string; args: HTerm[] } | null => {
    const x = C.ty_peel(t, null)[0];
    if (x.$ !== "App" && x.$ !== "Ref") {
      return null;
    }
    const ck = C.call_kind(fl, x);
    if (ck !== null) {
      return { en: C.eff_name(ck.k), args: ck.args };
    }
    const m = C.term_spine(fl, x);
    return m.t.$ === "Ref" ? { en: C.eff_name(m.t.k), args: m.args } : null;
  };
  const wide = (t: HTerm): string | null => {
    const w = sub(t);
    return w?.en === "f32_to_f64" && w.args.length === 1
      ? expr(fl, w.args[0], null) : null;
  };
  const f = sub(args[0]);
  if (f === null) {
    return null;
  }
  if (["f64_exp", "f64_sin", "f64_cos"].includes(f.en) && f.args.length === 1) {
    const a = wide(f.args[0]);
    return a === null ? null : `x32_${f.en.slice(4)}(${a})`;
  }
  if (f.en === "f64_pow" && f.args.length === 2) {
    const [a, b] = [wide(f.args[0]), wide(f.args[1])];
    return a === null || b === null ? null : `x32_pow(${a}, ${b})`;
  }
  if (f.en === "f64_log" && f.args.length === 1) {
    // log(1 + exp(x)), softplus's False arm (x <= 20, or NaN as 88)
    const s = sub(f.args[0]);
    const one = s?.en === "f64_add" ? sub(s.args[0]) : null;
    const ex = s?.en === "f64_add" ? sub(s.args[1]) : null;
    if (one?.en === "f64_from_nat" && nat_lit(fl, one.args[0]) === "1u"
      && ex?.en === "f64_exp" && ex.args.length === 1) {
      const a = wide(ex.args[0]);
      return a === null ? null : `x32_softplus(${a})`;
    }
  }
  return null;
}

function call(fl: File, k: Name, args: HTerm[]): string {
  const chain = x32_chain(fl, k, args);
  if (chain !== null) {
    return chain;
  }
  const xs = args.map((x) => expr(fl, x, null));
  if (FOLD !== null && k === FOLD.k) {
    if (xs[0] !== FOLD.p || xs.slice(1).join() !== FOLD.rest.join()) {
      die("WGSL: " + k + " calls itself other than on its predecessor with"
        + " the same parameters");
    }
    return "acc";
  }
  if (SPIN !== null && k === SPIN.k) {
    die("WGSL: " + k + " calls itself other than as its last act (a spin loop"
      + " jumps)");
  }
  const tld = fl.book.tlds[k];
  if (C.intr_of(fl, k, true) !== undefined) {
    const en = C.eff_name(k);
    if (en.startsWith("bytes_")) {
      return bytes_op(en, xs);
    }
    const op = OPS[en];
    return op !== undefined ? C.tpl(op, xs)
      : die("WGSL: no WGSL form for the operation " + k);
  }
  if (tld?.$ !== "Def" || C.def_foreign(tld)
    || xs.length !== C.sig_def(fl, k).live.length) {
    die("WGSL: a call that is not a whole def of the lane: " + k);
  }
  if (C.eff_name(k) === "bool_pick" && xs.length === 3) {
    // polymorphic in its type, so no instance: both arms are values already
    return `select(${xs[2]}, ${xs[1]}, ${xs[0]})`;
  }
  const live = C.sig_def(fl, k).live;
  const tys = live.map(([, n, A]) => ty_of(fl, A, k + "'s " + n));
  const toks = tys.map((t, j) => {
    if (t !== "bytes") {
      return null;
    }
    return TRIAL || BUFS.has(xs[j]) ? xs[j]
      : die("WGSL: " + k + " is given a Bytes that is not one of the lane's"
        + " buffers");
  });
  const stat = tys.map((t, j) => null as number | null);
  if (mode_of(fl, k, tld as Def) === "rec") {
    tys.forEach((t, j) => {
      // only a Nat is a depth: a U32 literal stays a value
      if (t === "u32" && C.adt_of(fl.book, live[j][2]).k === "Nat"
        && /^\d+u$/.test(xs[j])) {
        stat[j] = Number(xs[j].slice(0, -1));
      }
    });
    if (stat.every((v) => v === null)) {
      die("WGSL: " + k + " recurses on a Nat, which needs a literal where it"
        + " is called (WGSL has no recursion; a literal unrolls it)");
    }
  }
  const rest = xs.filter((_, j) => toks[j] === null && stat[j] === null);
  return inst(k, toks, stat) + "(" + rest.join(", ") + ")";
}

// A Nat literal: its Succ count over Zero, a Lit, or a non-literal base.
function nat_lit(fl: File, t: HTerm): string {
  let n = 0;
  let x = C.term_strip(t);
  while (x.$ === "Ctr" && x.k === "Succ" && x.x.length === 1) {
    n += 1;
    x = C.term_strip(x.x[0]);
  }
  const base = x.$ === "Ctr" && x.k === "Zero" ? 0
    : x.$ === "Lit" && typeof x.v === "number" ? x.v : null;
  if (base !== null) {
    return n + base > 0xffffffff
      ? die("WGSL: a Nat literal past 2^32 - 1") : (n + base) + "u";
  }
  return `nat_add(${expr(fl, x, null)}, ${n}u)`;
}

function expr(fl: File, tm: HTerm, ty0: HTerm | null): string {
  const [x, ty] = C.ty_peel(tm, ty0);
  switch (x.$) {
    case "Var": return x.k;
    case "Lit": {
      return typeof x.v === "number" ? x.v + "u"
        : die("WGSL: a String literal");
    }
    case "Ref":
    case "App": {
      const ck = C.call_kind(fl, x);
      if (ck !== null) {
        if (ck.bang === true) {
          die("WGSL: a bang inside the device program");
        }
        return call(fl, ck.k, ck.args);
      }
      const m = C.term_spine(fl, x);
      const y = C.call_eta(fl, x) ?? (m.t.$ !== "Ref" ? m.h : null);
      if (y !== null) {
        return expr(fl, y, ty);
      }
      return call(fl, (m.t as C.Of<"Ref">).k, m.args);
    }
    case "Ctr": {
      if (x.k === "Zero" || x.k === "Succ") {
        return nat_lit(fl, x);
      }
      const [adt, u] = C.ctr_adt(fl, x, ty);
      if (adt.k === "Bool") {
        return x.k.endsWith("True") ? "true" : "false";
      }
      if (adt.k !== "F32" && adt.k !== "U32") {
        die("WGSL: a " + adt.k + " value, outside the lane's words");
      }
      // a literal by its bits (exact); else the word a match bound
      const w = u !== null ? u + "u"
        : expr(fl, C.ctr_flds(fl.book, x.k, x.x)[0], null);
      return adt.k === "F32" ? `bitcast<f32>(${w})` : w;
    }
    case "Let": return expr(fl, open(fl, x), ty);
    default: return die("WGSL: a " + x.$ + " where a word is expected");
  }
}

// A def's body as statements ending in a return (or, with `to`, an
// assignment): Lams bind the parameters, Lets become lets, matches if-chains.
// A Nat match on a literal picks its arm here, as the instance's literal.
function body(fl: File, tm: HTerm, ty0: HTerm | null, args: string[],
  to = "return "): void {
  const [x, ty] = C.ty_peel(tm, ty0);
  if (x.$ === "Lam") {
    const all = C.ty_all(fl.book, ty);
    const v: HTerm = Bend.Var(C.quant_live(all.q) ? args[0] : "null", 0);
    return body(fl, x.f(v), all.B(v),
      C.quant_live(all.q) ? args.slice(1) : args, to);
  }
  if (C.mat_head(x)) {
    const all = C.ty_all(fl.book, ty);
    const adt = C.adt_of(fl.book, all.A);
    const s = args[0];
    const rest = args.slice(1);
    if (adt.k === "U32" || adt.k === "F32") {
      // a word match binds its bits: a reinterpret
      const arms = C.mat_ctrs(fl, x, adt);
      if (arms.length !== 1 || arms[0][0] === "") {
        die("WGSL: a " + adt.k + " match that is not a reinterpret");
      }
      const bits = adt.k === "F32" ? `bitcast<u32>(${s})` : s;
      return body(fl, arms[0][1], null, [bits, ...rest], to);
    }
    // Bool and Nat: an if-chain, a level per arm
    const lv: [string, HTerm, string[]][] = [];
    if (adt.k === "Bool") {
      for (const [k, h] of C.mat_ctrs(fl, x, adt)) {
        lv.push([k === "" ? "" : k.endsWith("True") ? s : `!${s}`, h, []]);
      }
    } else if (adt.k === "Nat") {
      for (const [h, n] of C.emit_nats(adt, x)!) {
        lv.push([n === null ? `${s} == ${lv.length}u` : "", h,
          n === null ? [] : [`(${s} - ${n}u)`]]);
      }
      if (/^\d+u$/.test(s)) {
        // a literal: the arm it takes, its predecessor a literal
        const v = Number(s.slice(0, -1));
        const hit = lv.findIndex(([c], i) => c === "" || v === i);
        const n = lv[hit][1] !== undefined && lv[hit][0] === ""
          ? Number(/- (\d+)u\)$/.exec(lv[hit][2][0] ?? "")?.[1] ?? 0) : 0;
        const fs = lv[hit][2].length > 0 ? [`${v - n}u`] : [];
        return body(fl, lv[hit][1], null, [...fs, ...rest], to);
      }
    } else {
      die("WGSL: a match on a " + adt.k + ", outside the lane's words");
    }
    // the last arm is the else: the match is exhaustive by its type
    const arm = ([, h, fs]: [string, HTerm, string[]]): void => {
      const fv = fs.map((f) => {
        const al = C.name_local(fl, "p");
        C.file_push(fl, `let ${al} = ${f};`);
        return al;
      });
      body(fl, h, null, [...fv, ...rest], to);
    };
    if (lv.length === 1) {
      return arm(lv[0]);
    }
    lv.forEach((l, i) => {
      C.file_push(fl, i === 0 ? `if (${l[0]}) {` : i === lv.length - 1
        ? "} else {" : `} else if (${l[0]}) {`);
      fl.tab += 1;
      arm(l);
      fl.tab -= 1;
    });
    C.file_push(fl, "}");
    return;
  }
  if (x.$ === "Let") {
    return body(fl, open(fl, x), ty, args, to);
  }
  if (args.length > 0) {
    die("WGSL: a def body short of its parameters");
  }
  const ck = SPIN !== null && (x.$ === "App" || x.$ === "Ref")
    ? C.call_kind(fl, x) : null;
  if (SPIN !== null && ck?.k === SPIN.k) {
    return jump(fl, SPIN, ck.args);
  }
  C.file_push(fl, to + expr(fl, x, ty) + ";");
}

// A spin loop's tail call: the new parameters, all read before any lands.
function jump(fl: File, sp: Spin, args: HTerm[]): void {
  const xs = args.map((a) => expr(fl, a, null));
  const at = sp.keep.map((on, j) => on ? j : -1).filter((j) => j >= 0);
  const ts = at.map((j) => {
    const al = C.name_local(fl, "j");
    C.file_push(fl, `let ${al} = ${xs[j]};`);
    return al;
  });
  at.forEach((j, i) => C.file_push(fl, `${sp.vs[j]} = ${ts[i]};`));
  C.file_push(fl, "continue;");
}

// Self calls under a term (a fold has one, a fork tree two in a Let).
function selfs(fl: File, k: Name, t: HTerm): number {
  const ck = t.$ === "App" || t.$ === "Ref" ? C.call_kind(fl, t) : null;
  return (ck?.k === k ? 1 : 0)
    + C.term_kids(fl, t).reduce((n, c) => n + selfs(fl, k, c), 0);
}

// A def's parameters (WGSL names and types) and result type.
function sig(fl: File, k: Name, def: Def, pre: string): {
  ps: string[]; tys: string[]; ret: string } {
  const live = C.sig_def(fl, k).live;
  return {
    ps: live.map(([, n]) => pre + C.name_local(fl, n)),
    tys: live.map(([, n, A]) => ty_of(fl, A, k + "'s " + n)),
    ret: ty_of(fl, Bend.tele_fill(fl.book, def.T, Array(def.n).fill(C.DUMMY),
      Bend.ctx_nil()), k + "'s result"),
  };
}

// Lams bound to `args` up to the first non-Lam (a match takes the next arg
// as its scrutinee, as js_func's): that term, its type, the args left.
function head(fl: File, t: HTerm, ty0: HTerm | null, args: string[]): {
  x: HTerm; ty: HTerm | null; args: string[] } {
  const [x, ty] = C.ty_peel(t, ty0);
  if (x.$ !== "Lam") {
    return { x, ty, args };
  }
  const all = C.ty_all(fl.book, ty);
  const v: HTerm = Bend.Var(C.quant_live(all.q) ? args[0] : "null", 0);
  return head(fl, x.f(v), all.B(v), C.quant_live(all.q) ? args.slice(1) : args);
}

// A Nat match's two arms (0 and 1 + p) with p bound, or null.
function nat_split(fl: File, x: HTerm, ty: HTerm | null):
  [HTerm, HTerm] | null {
  if (!C.mat_head(x)) {
    return null;
  }
  const adt = C.adt_of(fl.book, C.ty_all(fl.book, ty).A);
  const ls = C.emit_nats(adt, x);
  return ls !== null && ls.length === 2 && ls[0][1] === null && ls[1][1] === 1
    ? [ls[0][0], ls[1][0]] : null;
}

// The fn of an instance, in the given mode.
function def_emit(fl: File, it: Inst, def: Def, mode: Mode): void {
  const { k, toks, stat } = it;
  fl.fresh = new Map();
  const { ps, tys, ret } = sig(fl, k, def, "");
  // the bound parameters (a buffer, a literal) are not passed
  const keep = ps.map((_, j) => toks[j] === null && stat[j] === null);
  const args = ps.map((p, j) => toks[j] ?? (stat[j] !== null ? stat[j] + "u" : p));
  const sg = `fn ${it.name}(${ps.map((p, i) => p + ": " + tys[i])
    .filter((_, j) => keep[j]).join(", ")}) -> ${ret} {`;
  if (mode === "plain" || mode === "rec") {
    C.block(fl, sg, () => body(fl, def.h!, def.T, args));
  } else if (mode === "spin") {
    const vs = args.map((a, j) => keep[j] ? "sp" + ps[j] : a);
    C.block(fl, sg, () => {
      ps.forEach((p, j) => keep[j] && C.file_push(fl, `var ${vs[j]} = ${p};`));
      SPIN = { k, vs, keep };
      try {
        C.block(fl, "loop {", () => body(fl, def.h!, def.T, vs));
      } finally {
        SPIN = null;
      }
    });
  } else {
    // a fold: acc = the 0 arm, then the 1 + p arm per p, its self call = acc
    const h = head(fl, def.h!, def.T, args);
    const arms = selfs(fl, k, def.h!) === 1 && h.args[0] === args[0]
      && tys[0] === "u32" && keep[0] ? nat_split(fl, h.x, h.ty) : null;
    if (arms === null) {
      die("WGSL: " + k + " recurses other than as a fold over its first Nat"
        + " (WGSL has no recursion)");
    }
    const rest = args.slice(1);
    C.block(fl, sg, () => {
      C.file_push(fl, `var acc: ${ret};`);
      body(fl, arms[0], null, rest, "acc = ");
      C.block(fl, `for (var fp = 0u; fp < ${ps[0]}; fp += 1u) {`, () => {
        FOLD = { k, p: "fp", rest };
        try {
          body(fl, arms[1], null, ["fp", ...rest], "acc = ");
        } finally {
          FOLD = null;
        }
      });
      C.file_push(fl, "return acc;");
    });
  }
  C.file_push(fl, "");
}

// How a def with a self call is emitted: tried in this order, on a scratch
// instance (the first that emits without a die wins; "rec" is the last
// resort, and its die, if any, comes with the real instance).
function mode_of(fl: File, k: Name, def: Def): Mode {
  const had = MODES.get(k);
  if (had !== undefined) {
    return had;
  }
  if (selfs(fl, k, def.h!) === 0) {
    MODES.set(k, "plain");
    return "plain";
  }
  const live = C.sig_def(fl, k).live;
  const scratch: Inst = { k, name: "scratch",
    toks: live.map(([, , A]) => ty_of(fl, A, k) === "bytes" ? "scratch" : null),
    stat: live.map(() => null) };
  const at = fl.seg.lines.length;
  const fresh = fl.fresh;
  const tab = fl.tab;
  const was = TRIAL;
  TRIAL = true;
  let mode: Mode = "rec";
  for (const m of ["fold", "spin"] as Mode[]) {
    try {
      def_emit(fl, scratch, def, m);
      mode = m;
      break;
    } catch {
      FOLD = null;
      SPIN = null;
    } finally {
      fl.seg.lines.length = at;
      fl.fresh = fresh;
      fl.tab = tab;
    }
  }
  TRIAL = was;
  MODES.set(k, mode);
  return mode;
}

// The instances the roots reach (callees on demand), as fns.
function lib(fl: File, cb: C.Carb): string {
  while (QUEUE.length > 0) {
    const it = QUEUE.shift()!;
    C.memo_gc();
    const def = cb.book.tlds[it.k] as Def;
    def_emit(fl, it, def, mode_of(fl, it.k, def));
  }
  return fl.seg.lines.splice(0).join("\n");
}

// Entries
// =======

// A binding of an entry: an input (a class: "row" one word an element of a
// row, "shared" one an element of the entry, "rowv" one a row, "scalar" one
// a dispatch, "bytes" a buffer the defs read byte-wise) or the output.
type Bind = { name: string; ty: string; cls: string; binding: number };

// A fork tree's root: its leaf, its two children's parameters per level and
// its join, as WGSL fns; the kernel's word types. A join that reads its node's
// parameters (or level) gets them: the node is found by the descent from the
// root that the leaf makes, stopped short.
type Fork = { def: Name; params: string[]; result: string; args: number[];
  joinp: boolean; bytes: { param: number; binding: number }[]; sfx: string };

function fork_emit(fl: File, k: Name, def: Def, sfx: string): Fork {
  fl.fresh = new Map();
  const { ps, tys, ret } = sig(fl, k, def, "fk_");
  const bytes: Fork["bytes"] = [];
  const args = ps.map((p, j) => {
    if (tys[j] !== "bytes") {
      return p;
    }
    if (j === 0) {
      die("WGSL: the bang " + k + "'s first parameter must be its Nat depth");
    }
    const tok = `fork${sfx}_by${j}`;
    BUFS.set(tok, { arr: tok, len: `fork${sfx}_args[${j}u]`, used: false });
    bytes.push({ param: j, binding: 8 + bytes.length });
    return tok;
  });
  const h = head(fl, def.h!, def.T, args);
  const arms = h.args[0] === ps[0] && tys[0] === "u32"
    ? nat_split(fl, h.x, h.ty) : null;
  if (arms === null) {
    die("WGSL: the bang " + k + " is not a fork tree over its first Nat"
      + " (match d: 0 -> a leaf; 1 + p -> a b = .. ..; a join)");
  }
  const vi = ps.map((_, j) => j).filter((j) => j > 0 && tys[j] !== "bytes");
  const ins = (j: number): string => ps[j] + "_in";
  const formals = vi.map((j) => ins(j) + ": " + tys[j]);
  // the 1 + p arm on (the level, the parameters): its parallel let, its join
  const { x: lt } = head(fl, arms[1], null, ["fk_p", ...args.slice(1)]);
  const kids = lt.$ === "Let" && lt.v.length === 2
    ? lt.v.map((v) => C.call_kind(fl, v)) : [];
  if (lt.$ !== "Let" || kids.length !== 2 || kids.some((c) => c?.k !== k)) {
    die("WGSL: the bang " + k + "'s 1 + p arm is not `a b = " + k + "(p, ..) "
      + k + "(p, ..)` then a join");
  }
  const let_ = lt as C.HLet;
  const j = let_.f([Bend.Var("ja", 0), Bend.Var("jb", 0)]);
  // a lane walks its bits from the root: the parameters are vars under the
  // names the arms were opened with, so a child's arguments read this level's
  const descend = (lane: string, steps: string): void => {
    vi.forEach((q) => C.file_push(fl, `var ${ps[q]} = ${ins(q)};`));
    C.block(fl, `for (var fk_k = 0u; fk_k < ${steps}; fk_k += 1u) {`, () => {
      C.file_push(fl, `let fk_p = ${ps[0]} - 1u - fk_k;`);
      // a child's parameters, all read before any lands
      const side = (c: number): void => {
        const ca = kids[c]!.args;
        if (expr(fl, ca[0], null) !== "fk_p") {
          die("WGSL: " + k + "'s children are not on the predecessor");
        }
        ca.slice(1).forEach((a, q) => {
          if (tys[q + 1] === "bytes" && expr(fl, a, null) !== args[q + 1]) {
            die("WGSL: " + k + "'s children pass another Bytes");
          }
        });
        const nv = vi.map((q) => expr(fl, ca[q], null));
        nv.forEach((e, i) => C.file_push(fl, `let ${ps[vi[i]]}_${c} = ${e};`));
        nv.forEach((_, i) => C.file_push(fl,
          `${ps[vi[i]]} = ${ps[vi[i]]}_${c};`));
      };
      C.file_push(fl, `if (((${lane} >> fk_p) & 1u) == 0u) {`);
      fl.tab += 1;
      side(0);
      fl.tab -= 1;
      C.file_push(fl, "} else {");
      fl.tab += 1;
      side(1);
      fl.tab -= 1;
      C.file_push(fl, "}");
    });
  };
  const nm = sat(k);
  C.block(fl, `fn ${nm}_leaf(lane: u32, ${[ps[0] + ": u32", ...formals]
    .join(", ")}) -> ${ret} {`, () => {
    descend("lane", ps[0]);
    // the leaf: the 0 arm on this lane's parameters
    body(fl, arms[0], null, args.slice(1));
  });
  C.file_push(fl, "");
  // the join, tried without the node: any fk_ it reads asks for the node
  const at = fl.seg.lines.length;
  const fresh = fl.fresh;
  fl.fresh = new Map(fresh);
  C.block(fl, `fn ${nm}_join(ja: ${ret}, jb: ${ret}) -> ${ret} {`, () => {
    body(fl, j, null, []);
  });
  const joinp = fl.seg.lines.slice(at).some((l) => /\bfk_/.test(l));
  if (joinp) {
    fl.seg.lines.length = at;
    fl.fresh = new Map(fresh);
    C.block(fl, `fn ${nm}_join(ja: ${ret}, jb: ${ret}, lane0: u32, lvl: u32, `
      + `${[ps[0] + ": u32", ...formals].join(", ")}) -> ${ret} {`, () => {
      descend("lane0", `${ps[0]} - lvl`);
      C.file_push(fl, "let fk_p = lvl - 1u;");
      body(fl, j, null, []);
    });
  }
  C.file_push(fl, "");
  return { def: k, params: tys, result: ret, args: [], joinp, bytes, sfx };
}

// The bang calls under main with their literal arguments (the run's default).
function bangs(fl: File, t: HTerm, out: Map<Name, number[] | null>): void {
  const ck = t.$ === "App" || t.$ === "Ref" ? C.call_kind(fl, t) : null;
  if (ck?.bang === true) {
    const lits = ck.args.map((a) => {
      const s = (() => {
        try {
          return nat_lit(fl, a);
        } catch {
          return null;
        }
      })();
      return s !== null && /^\d+u$/.test(s) ? Number(s.slice(0, -1)) : null;
    });
    out.set(ck.k, lits.every((v) => v !== null) ? lits as number[] : null);
  }
  for (const c of C.term_kids(fl, t)) {
    bangs(fl, c, out);
  }
}

// A cube or a map of the book: its defs by role. `cube.n` ... is the unnamed
// cube; `cube.rms.n` ... the cube "rms"; `map.silu.f` the map "silu".
const ROLES: Record<string, string[]> = {
  cube: ["n", "leaf", "join", "fin", "out", "len", "pad", "bind"],
  map: ["f", "len", "rowlen", "bind"],
};
type Shape = { kind: string; name: string; defs: Record<string, Name> };

function shapes(book: Bend.Book): Shape[] {
  const by = new Map<string, Shape>();
  for (const k of Object.keys(book.tlds)) {
    const m = /^(cube|map)(?:\.(\w+))?\.(\w+)$/.exec(k);
    if (m === null || book.tlds[k]?.$ !== "Def" || !ROLES[m[1]].includes(m[3])) {
      continue;
    }
    const key = m[1] + "." + (m[2] ?? "");
    const sh = by.get(key) ?? { kind: m[1], name: m[2] ?? "", defs: {} };
    sh.defs[m[3]] = k;
    by.set(key, sh);
  }
  return [...by.values()].filter((sh) => sh.kind === "cube"
    ? ["n", "leaf", "join", "fin"].every((r) => sh.defs[r] !== undefined)
    : sh.defs.f !== undefined);
}

// A String literal def's text (the bind declaration): a chain of SCon over Chr
// over U32 literals.
function text_of(fl: File, k: Name | undefined): string | null {
  if (k === undefined) {
    return null;
  }
  const t = (fl.book.tlds[k] as Def).h;
  let c = t === undefined ? null : C.term_strip(t);
  let s = "";
  while (c !== null && c.$ === "Ctr" && c.k === "SCon") {
    const h = C.term_strip(c.x[0]);
    const w = h.$ === "Ctr" && h.k === "Chr" ? C.term_strip(h.x[0]) : h;
    const u = w.$ === "Ctr" ? C.ctr_adt(fl, w, null)[1] : null;
    s += String.fromCharCode(u ?? die("WGSL: " + k + " is not a plain String literal"));
    c = C.term_strip(c.x[1]);
  }
  return c !== null && c.$ === "Ctr" && c.k === "SNil" ? s
    : die("WGSL: " + k + " must be a String literal (the bind declaration)");
}

// A literal U32 def (cube.n()), by its WGSL form.
function lit_of(fl: File, k: Name, what: string): number {
  fl.fresh = new Map();
  const def = fl.book.tlds[k] as Def;
  const m = /^(\d+)u$/.exec(expr(fl, def.h!, def.T));
  return m !== null ? Number(m[1]) : die("WGSL: " + what + " must be a U32 literal");
}

type Param = { name: string; ty: string; q: number };

function params_of(fl: File, k: Name | undefined): Param[] {
  if (k === undefined) {
    return [];
  }
  return C.sig_def(fl, k).live.map(([, n, A], q) => ({ name: n,
    ty: ty_of(fl, A, k + "'s " + n), q }));
}

function ret_of(fl: File, k: Name): string {
  fl.fresh = new Map();
  return sig(fl, k, fl.book.tlds[k] as Def, "").ret;
}

// An entry's inputs: its defs' parameters by name (the reserved ones are the
// row, the index and the finished tree), with classes from the bind text.
function binds_of(fl: File, sh: Shape, roles: string[], reserved: string[]):
  Bind[] {
  const cls = new Map<string, string>();
  for (const w of (text_of(fl, sh.defs.bind) ?? "").split(/\s+/).filter(Boolean)) {
    const [n, c] = w.split("=");
    if (!["row", "shared", "rowv", "scalar"].includes(c)) {
      die("WGSL: " + sh.defs.bind + ": " + w + " (a class is row, shared, rowv"
        + " or scalar)");
    }
    cls.set(n, c);
  }
  const ins: Bind[] = [];
  for (const r of roles) {
    for (const p of params_of(fl, sh.defs[r])) {
      const b = ins.find((x) => x.name === p.name);
      if (reserved.includes(p.name)) {
        continue;
      }
      if (b !== undefined) {
        if (b.ty !== p.ty) {
          die("WGSL: " + sh.defs[r] + "'s " + p.name + " is a " + p.ty + ", a "
            + b.ty + " elsewhere in " + sh.kind + " " + sh.name);
        }
        continue;
      }
      ins.push({ name: p.name, ty: p.ty, binding: -1,
        cls: p.ty === "bytes" ? "bytes" : cls.get(p.name) ?? "row" });
    }
  }
  for (const n of cls.keys()) {
    if (!ins.some((b) => b.name === n)) {
      die("WGSL: " + sh.defs.bind + " names " + n + ", which no def of "
        + sh.kind + " " + sh.name + " takes");
    }
  }
  return ins;
}

const SC = (P: string): string => P + "__sc";
const arr_ty = (t: string): string => t === "bool" ? "u32" : t;

// One entry's bindings: the declarations, the scalar layout (sc: [rows or
// len, scalars, byte lengths]) and the manifest's view of them.
function bind_decls(P: string, ins: Bind[], out: { ty: string } | null,
  scalars: boolean): { wgsl: string; man: object } {
  const lines: string[] = [];
  const sc: { name: string; ty: string; at: number }[] = [];
  const lens: { name: string; at: number }[] = [];
  let at = 1;
  let b = 0;
  const inman: object[] = [];
  for (const i of ins) {
    if (i.cls === "scalar") {
      sc.push({ name: i.name, ty: i.ty, at: at++ });
      continue;
    }
    i.binding = b++;
    lines.push(`@group(0) @binding(${i.binding}) var<storage, read> ${P}_${i.name}: array<${
      i.cls === "bytes" ? "u32" : arr_ty(i.ty)}>;`);
    if (i.cls === "bytes") {
      lens.push({ name: i.name, at: at++ });
    }
    inman.push({ name: i.name, ty: i.ty, cls: i.cls, binding: i.binding });
  }
  let ob: number | null = null;
  if (out !== null) {
    ob = b++;
    lines.push(`@group(0) @binding(${ob}) var<storage, read_write> ${P}__out: array<${
      arr_ty(out.ty)}>;`);
  }
  let sb: number | null = null;
  if (scalars || sc.length > 0 || lens.length > 0) {
    sb = b++;
    lines.push(`@group(0) @binding(${sb}) var<storage, read> ${SC(P)}: array<u32>;`);
  }
  return { wgsl: lines.join("\n"), man: { ins: inman,
    out: out === null ? null : { ty: out.ty, binding: ob },
    sc: sb === null ? null : { binding: sb, scalars: sc, lens } } };
}

// The text of a call to a lane def from a kernel: its Bytes parameters are
// the bindings' tokens, the rest are read from the entry's bindings.
function kcall(fl: File, P: string, ins: Bind[], k: Name, idx: string,
  rowx: string, extra: Record<string, string>): string {
  const live = C.sig_def(fl, k).live;
  const tys = live.map(([, n, A]) => ty_of(fl, A, k + "'s " + n));
  const toks: (string | null)[] = tys.map((t, j) => {
    if (t !== "bytes") {
      return null;
    }
    const b = ins.find((x) => x.name === live[j][1])!;
    const tok = `${P}_${b.name}`;
    const at = SCAT.get(tok)!.at;
    if (!BUFS.has(tok)) {
      BUFS.set(tok, { arr: tok, len: `${SC(P)}[${at}u]`, used: false });
    }
    return tok;
  });
  const args: string[] = [];
  live.forEach(([, n], j) => {
    if (toks[j] !== null) {
      return;
    }
    if (n in extra) {
      args.push(extra[n]);
      return;
    }
    const b = ins.find((x) => x.name === n);
    if (b === undefined) {
      die("WGSL: " + k + "'s parameter " + n + " is not bound in this entry");
    }
    const v = b.cls === "row" ? `${P}_${n}[${rowx}]`
      : b.cls === "shared" ? `${P}_${n}[${idx}]`
      : b.cls === "rowv" ? `${P}_${n}[row]` : sc_read(P, b);
    args.push(b.cls !== "scalar" && tys[j] === "bool" ? `(${v} != 0u)` : v);
  });
  return inst(k, toks, toks.map(() => null)) + "(" + args.join(", ") + ")";
}
const SCAT = new Map<string, { at: number }>();

function sc_read(P: string, b: Bind): string {
  const at = SCAT.get(P + "_" + b.name)!.at;
  const w = `${SC(P)}[${at}u]`;
  return b.ty === "f32" ? `bitcast<f32>(${w})` : b.ty === "bool" ? `(${w} != 0u)` : w;
}

// A cube's kernel: lane l owns the n / T leaves from l n / T and joins them as
// the bottom levels of the perfect tree over n (the Bend def's tree is the
// spec: leaf pairs (2i, 2i + 1) first), left to right with a stack of one
// finished subtree a level (as a binary counter carries), so n is bounded by
// nothing but the index; the T partials join as its top levels, level by
// level with a barrier each; lane 0 finishes. A row is a workgroup; `len`
// real leaves a row, the rest the pad.
function cube_emit(fl: File, sh: Shape): { wgsl: string; man: object } {
  const d = sh.defs;
  const P = "cube" + (sh.name === "" ? "" : "_" + sh.name);
  const n = lit_of(fl, d.n, d.n);
  if ((n & (n - 1)) !== 0 || n > 1048576 || n < 1) {
    die("WGSL: " + d.n + " must be a power of two up to 2^20");
  }
  const len = d.len === undefined ? n : lit_of(fl, d.len, d.len);
  if (len < 1 || len > n) {
    die("WGSL: " + d.len + " must be in 1 .. " + n);
  }
  const T = Math.min(n, 256);
  const Q = n / T;
  const LQ = Math.log2(Q);
  const hasout = d.out !== undefined;
  const lp = params_of(fl, d.leaf), op = params_of(fl, d.out);
  // the legacy cube (unnamed, no bind, leaf(v), out(v, s, g)): x = v, w = g
  const legacy = d.bind === undefined && sh.name === "" && lp.length === 1
    && op.length === 3;
  const sname = legacy ? op[1].name : "s";
  const finp = params_of(fl, d.fin);
  let ins: Bind[];
  if (legacy) {
    ins = [{ name: "x", ty: lp[0].ty, cls: "row", binding: -1 },
      { name: "w", ty: op[2].ty, cls: "row", binding: -1 }];
  } else {
    ins = binds_of(fl, sh, ["leaf", "out", "fin"],
      ["row", "i", ...hasout ? [sname] : [], finp[0].name]);
  }
  const W = ret_of(fl, d.join);
  const S = ret_of(fl, d.fin);
  const O = hasout ? ret_of(fl, d.out) : S;
  // the scalar layout is fixed before the calls name it
  let at = 1;
  for (const i of ins) {
    if (i.cls === "scalar" || i.cls === "bytes") {
      SCAT.set(P + "_" + i.name, { at: at++ });
    }
  }
  const dec = bind_decls(P, ins, { ty: O }, false);
  // call texts: the leaf at leaf index i, the out at element i
  const leafRx = (l: string): string => `row * ${P}__LEN + ${l}`;
  const x = (k: Name, idx: string, extra: Record<string, string> = {}): string =>
    kcall(fl, P, ins, k, idx, leafRx(idx), extra);
  const lcall = (): string => {
    if (!legacy) {
      return x(d.leaf, "i", { row: "row", i: "i" });
    }
    return inst(d.leaf, [null], [null]) + `(${P}_x[${leafRx("i")}])`;
  };
  const ocall = (): string => {
    if (!legacy) {
      return x(d.out, "i", { row: "row", i: "i", [sname]: "s" });
    }
    return inst(d.out, [null, null, null], [null, null, null])
      + `(${P}_x[${leafRx("i")}], s, ${P}_w[${leafRx("i")}])`;
  };
  const zero = W === "f32" ? "0.0" : W === "bool" ? "false" : "0u";
  const pad = d.pad === undefined ? zero : inst(d.pad, [], []) + "()";
  const jn = inst(d.join, [null, null], [null, null]);
  const man_sc = dec.man as { sc: { binding: number } | null };
  const guard = man_sc.sc !== null ? `if (row >= ${SC(P)}[0u]) {
    return;
  }
` : "";
  const fin = (a: string): string => {
    const fx = kcall(fl, P, ins, d.fin, "0u", "row * " + P + "_LEN",
      { row: "row", [finp[0].name]: a });
    return fx;
  };
  const wgsl = String.raw`// Cube ${sh.name === "" ? "(unnamed)" : sh.name}
// ====

const ${P}__N: u32 = ${n}u;
const ${P}__LEN: u32 = ${len}u;
const ${P}__T: u32 = ${T}u;
const ${P}__Q: u32 = ${Q}u;

${dec.wgsl}

var<workgroup> ${P}__t: array<${W}, ${P}__T>;
${hasout ? `var<workgroup> ${P}__s: ${S};` : ""}

@compute @workgroup_size(${P}__T)
fn ${P}_main(@builtin(local_invocation_index) l: u32,
  @builtin(workgroup_id) g: vec3<u32>, @builtin(num_workgroups) ng: vec3<u32>) {
  let row = g.y * ng.x + g.x;
  ${guard}var st: array<${W}, ${LQ + 1}>;
  for (var j = 0u; j < ${P}__Q; j += 1u) {
    let i = l * ${P}__Q + j;
    var v: ${W};
    if (i < ${P}__LEN) {
      v = ${lcall()};
    } else {
      v = ${pad};
    }
    var lv = 0u;
    for (var t = j; (t & 1u) != 0u; t >>= 1u) {
      v = ${jn}(st[lv], v);
      lv += 1u;
    }
    st[lv] = v;
  }
  ${P}__t[l] = st[${LQ}];
  workgroupBarrier();
  for (var h = 1u; h < ${P}__T; h *= 2u) {
    for (var p = l * 2u * h; p < ${P}__T; p += ${P}__T * 2u * h) {
      ${P}__t[p] = ${jn}(${P}__t[p], ${P}__t[p + h]);
    }
    workgroupBarrier();
  }
${hasout ? `  if (l == 0u) {
    ${P}__s = ${fin(`${P}__t[0]`)};
  }
  workgroupBarrier();
  let s = ${P}__s;
  for (var i = l; i < ${P}__LEN; i += ${P}__T) {
    ${P}__out[row * ${P}__LEN + i] = ${ty_store(O, ocall())};
  }` : `  if (l == 0u) {
    ${P}__out[row] = ${ty_store(O, fin(`${P}__t[0]`))};
  }`}
}
`;
  return { wgsl, man: { kind: "cube", name: sh.name, entry: P + "_main", n, len,
    lanes: T, node: W, per: hasout ? "elem" : "row", ...dec.man,
    rows_at: (dec.man as { sc: unknown }).sc === null ? null : 0 } };
}

const ty_store = (t: string, v: string): string =>
  t === "bool" ? `select(0u, 1u, ${v})` : v;

// A map's kernel: one invocation an element; with a `rowlen` the elements are
// rows of that many, `row` and `col` name an element's place and a rowv input
// is one word a row (softmax's max and sum).
function map_emit(fl: File, sh: Shape): { wgsl: string; man: object } {
  const d = sh.defs;
  const P = "map_" + sh.name;
  const rl = d.rowlen === undefined ? 0 : lit_of(fl, d.rowlen, d.rowlen);
  const ins = binds_of(fl, sh, ["f"], ["i", "row", "col"]);
  const O = ret_of(fl, d.f);
  let at = 1;
  for (const i of ins) {
    if (i.cls === "scalar" || i.cls === "bytes") {
      SCAT.set(P + "_" + i.name, { at: at++ });
    }
  }
  const dec = bind_decls(P, ins, { ty: O }, true);
  const call_ = kcall(fl, P, ins, d.f, "i", "i", { i: "i", row: "row", col: "col" });
  const wgsl = String.raw`// Map ${sh.name}
// ====

${dec.wgsl}

@compute @workgroup_size(256)
fn ${P}_main(@builtin(global_invocation_id) gid: vec3<u32>,
  @builtin(num_workgroups) ng: vec3<u32>) {
  let i = gid.y * ng.x * 256u + gid.x;
  if (i >= ${SC(P)}[0u]) {
    return;
  }
  ${rl > 0 ? `let row = i / ${rl}u;
  let col = i % ${rl}u;
  ` : ""}${P}__out[i] = ${ty_store(O, call_)};
}
`;
  return { wgsl, man: { kind: "map", name: sh.name, entry: P + "_main", lanes: 256,
    ...dec.man, len_at: 0 } };
}

// The global reads of the Bytes the lane's defs touch: a byte, four bytes
// little end first, a byte past the end 0 (the C lane's Bytes.get / word_le).
function bytes_fns(): string {
  return [...BUFS.entries()].filter(([, b]) => b.used).map(([tok, b]) => String.raw`fn bg_${tok}(i: u32) -> u32 {
  if (i >= ${b.len}) {
    return 0u;
  }
  return (${b.arr}[i >> 2u] >> ((i & 3u) * 8u)) & 255u;
}

fn bw_${tok}(i: u32) -> u32 {
  if ((i & 3u) == 0u && i + 4u <= ${b.len}) {
    return ${b.arr}[i >> 2u];
  }
  return bg_${tok}(i) | (bg_${tok}(i + 1u) << 8u) | (bg_${tok}(i + 2u) << 16u)
    | (bg_${tok}(i + 3u) << 24u);
}
`).join("\n");
}

// bend -o x.wgsl: the book's bangs (fork trees), cubes and maps, with the
// scalar defs they reach and runtime_wgsl. The first line is the manifest
// (bend-wgsl/2) the host runtime (webgpu.js) reads.
export function wgsl_book(book: Bend.Book): string {
  MODES.clear();
  INSTS.clear();
  QUEUE.length = 0;
  BUFS.clear();
  SCAT.clear();
  TRIAL = false;
  const cm = C.carb_book(book, ["main"]);
  const fm = C.file_new(cm, true);
  const bs = new Map<Name, number[] | null>();
  const main = cm.book.tlds["main"] as Def | undefined;
  if (main?.$ === "Def" && main.h !== undefined) {
    // main's arguments are read for literals only: nothing here is a lane def
    TRIAL = true;
    bangs(fm, main.h, bs);
    TRIAL = false;
  }
  const sh = shapes(book);
  if (bs.size === 0 && sh.length === 0) {
    die("WGSL: nothing for the lane: no bang in main and no cube.* or map.* defs");
  }
  const roots = [...bs.keys(), ...sh.flatMap((s) => Object.values(s.defs))];
  const cb = C.carb_book(book, roots);
  const fl = C.file_new(cb, true);
  fl.tab = 0;
  const forks: Fork[] = [];
  let fork_fns = "";
  for (const [k, args] of bs) {
    const f = fork_emit(fl, k, cb.book.tlds[k] as Def,
      bs.size === 1 ? "" : "_" + sat(k).slice(2));
    f.args = args ?? [];
    forks.push(f);
    fork_fns += fl.seg.lines.splice(0).join("\n") + "\n";
  }
  const kernels: { wgsl: string; man: object }[] = [];
  for (const s of sh) {
    kernels.push(s.kind === "cube" ? cube_emit(fl, s) : map_emit(fl, s));
  }
  const prog = lib(fl, cb);
  const man = { lane: "bend-wgsl/2", entries: [...forks.map((f) => ({
    kind: "fork", name: f.sfx === "" ? "" : f.sfx.slice(1), def: f.def,
    leaves: `fork${f.sfx}_leaves`, join: `fork${f.sfx}_join`,
    params: f.params, result: f.result, args: f.args, joinp: f.joinp,
    bytes: f.bytes })), ...kernels.map((k) => k.man)] };
  return "// bend-wgsl " + JSON.stringify(man) + "\n"
    + runtime_wgsl(prog + "\n" + bytes_fns() + "\n" + fork_fns)
    + forks.map(fork_rt).join("") + kernels.map((k) => k.wgsl).join("\n");
}

// The WebGPU device side.
// X32: / and sqrt as IEEE. Nat: u32 words that flag an overflow.
// Cube: a row of n leaves a workgroup; lane-local subtrees, then the perfect
// tree of joins level by level, a barrier each (no backend can fuse a leaf
// into a join), lane 0 finishes, every lane maps.
// Fork: a lane a leaf, the joins as the perfect tree over lanes, 256 a
// workgroup, the workgroups' partials joined again until one is left.
const runtime_wgsl = (prog: string): string =>
  String.raw`// emitted by bend (wgsl.ts): the program's lane defs and runtime_wgsl

${x32_blocks(prog)}${RT_COMMON}// Program
// =======

${prog}
`;

// X32: the correctly rounded f32 functions a program uses (/, sqrt, exp, sin,
// cos, pow, softplus), as the C lane's (f32) ops and (f32)fn((double)x) round
// them: integer arithmetic only, so neither the GPU's 2.5 ulp bound on / and
// sqrt, nor its fused multiply-add and flushed subnormals, can move a bit
// (x32w.ts, gated over every f32 input against the C lane).
const X32_USE: [RegExp, string][] = [
  [/\bx32_(div|sqrt)\(/, "x32_divsqrt"], [/\bx32_exp\(/, "x32_exp"],
  [/\bx32_(sin|cos)\(/, "x32_sincos"], [/\bx32_pow\(/, "x32_pow"],
  [/\bx32_softplus\(/, "x32_softplus"],
];
function x32_blocks(prog: string): string {
  const keys = X32_USE.filter(([re]) => re.test(prog)).map(([, k]) => k);
  const arith = /\bx32_(add|sub|mul)\(/.test(prog);
  if (arith) keys.push("x32_divsqrt", "x32w_u64");
  return keys.length === 0 ? "" : "// X32\n// ===\n\n" + x32wSource(keys)
    + (arith ? X32A : "") + "\n";
}

// A fork tree's kernels. fork_args: [d, the root's parameters as words (a
// Bytes parameter's word is its byte length), the lanes 2^d]; fork_leaves runs
// lane = global id, joins its workgroup's lanes and writes one partial;
// fork_join joins 256 partials a workgroup (the host repeats it until one is
// left; join_args: [partials, the level the partials stand at]). The perfect
// tree over lanes is the fork tree's own: lane L's bit p is its choice at
// level p, the root's the top.
function fork_rt(fk: Fork): string {
  const r = fk.result;
  const s = fk.sfx;
  const word = (t: string, w: string): string =>
    t === "f32" ? `bitcast<f32>(${w})` : t === "bool" ? `(${w} != 0u)` : w;
  const back = (t: string, v: string): string =>
    t === "f32" ? `bitcast<u32>(${v})` : t === "bool" ? `select(0u, 1u, ${v})` : v;
  const vi = fk.params.map((_, j) => j).filter((j) => j > 0 && fk.params[j] !== "bytes");
  const xs = vi.map((j) => word(fk.params[j], `fork${s}_args[${j}u]`));
  const k = sat(fk.def);
  const jp = fk.joinp ? `, lane0, lvl, fork${s}_args[0u]${xs.map((x) => ", " + x).join("")}` : "";
  const byd = fk.bytes.map((b) => `@group(0) @binding(${b.binding}) var<storage, read> fork${s}_by${b.param}: array<u32>;`).join("\n");
  return String.raw`
// Fork${s}
// ====

const FORK_T: u32 = 256u;

@group(0) @binding(0) var<storage, read> fork${s}_args: array<u32>;
@group(0) @binding(1) var<storage, read_write> fork${s}_part: array<u32>;
@group(0) @binding(2) var<storage, read_write> fork${s}_err: atomic<u32>;
@group(0) @binding(3) var<storage, read> join${s}_in: array<u32>;
@group(0) @binding(4) var<storage, read_write> join${s}_out: array<u32>;
@group(0) @binding(5) var<storage, read> join${s}_args: array<u32>;
${byd}

var<workgroup> fork${s}_t: array<${r}, FORK_T>;

// the perfect tree over fork_t[0 .. m), m a power of two <= FORK_T; the
// region's first node stands at lane w0 << lb (the partials of pass lb / 8
// are 2^lb lanes apart)
fn fork${s}_tree(l: u32, m: u32, w0: u32, lb: u32) {
  for (var h = 1u; h < m; h *= 2u) {
    workgroupBarrier();
    let p = l * 2u * h;
    if (p + h < m) {
${fk.joinp ? `      let lvl = lb + countTrailingZeros(2u * h);
      let lane0 = (w0 + p) << lb;
` : ""}      fork${s}_t[p] = ${k}_join(fork${s}_t[p], fork${s}_t[p + h]${jp});
    }
  }
  workgroupBarrier();
}

@compute @workgroup_size(FORK_T)
fn fork${s}_leaves(@builtin(local_invocation_index) l: u32,
  @builtin(workgroup_id) g: vec3<u32>, @builtin(num_workgroups) ng: vec3<u32>) {
  let n = fork${s}_args[${fk.params.length}u];
  let w = g.y * ng.x + g.x;
  // a 2-d grid's spare workgroups (uniform: the barriers stay legal)
  if (w * FORK_T >= n) {
    return;
  }
  let lane = w * FORK_T + l;
  let m = min(n, FORK_T);
  if (lane < n) {
    fork${s}_t[l] = ${k}_leaf(lane, fork${s}_args[0]${xs.map((x) => ", " + x).join("")});
  }
  fork${s}_tree(l, m, w * FORK_T, 0u);
  if (l == 0u) {
    fork${s}_part[w] = ${back(r, `fork${s}_t[0]`)};
  }
  if (nat_ovf != 0u) {
    atomicOr(&fork${s}_err, 1u);
  }
}

@compute @workgroup_size(FORK_T)
fn fork${s}_join(@builtin(local_invocation_index) l: u32,
  @builtin(workgroup_id) g: vec3<u32>, @builtin(num_workgroups) ng: vec3<u32>) {
  let n = join${s}_args[0];
  let w = g.y * ng.x + g.x;
  if (w * FORK_T >= n) {
    return;
  }
  let at = w * FORK_T + l;
  let m = min(n - w * FORK_T, FORK_T);
  if (l < m) {
    fork${s}_t[l] = ${word(r, `join${s}_in[at]`)};
  }
  fork${s}_tree(l, m, w * FORK_T, join${s}_args[1]);
  if (l == 0u) {
    join${s}_out[w] = ${back(r, `fork${s}_t[0]`)};
  }
  if (nat_ovf != 0u) {
    atomicOr(&fork${s}_err, 1u);
  }
}
`;
}

// The common device text: X32 (/ and sqrt as IEEE) and Nat.
const RT_COMMON = String.raw`// F32
// ===

fn fisnan(x: f32) -> bool {
  return (bitcast<u32>(x) & 0x7fffffffu) > 0x7f800000u;
}

fn fne(a: f32, b: f32) -> bool {
  return fisnan(a) || fisnan(b) || a != b;
}

// a * b rounded once, never fused into a sum, a zero keeping its sign (fma(a, b,
// -0.0) alone gives +0 for a zero product of opposite signs on Apple's GPUs)
fn bmul(a: f32, b: f32) -> f32 {
  let q = fma(a, b, -0.0);
  return select(q, bitcast<f32>((bitcast<u32>(a) ^ bitcast<u32>(b)) & 0x80000000u),
    q == 0.0);
}

// Nat
// ===

// A Nat is a u32 here; past 2^32 - 1 the lane sets nat_ovf and the run
// answers "past the envelope" (the C and JS lanes hold any Nat).
var<private> nat_ovf: u32;

fn nat_add(a: u32, b: u32) -> u32 {
  let s = a + b;
  if (s < a) {
    nat_ovf = 1u;
  }
  return s;
}

// a b = a1 b1 2^32 + (a1 b0 + a0 b1) 2^16 + a0 b0, a = a1 2^16 + a0
fn nat_mul(a: u32, b: u32) -> u32 {
  let a1 = a >> 16u;
  let b1 = b >> 16u;
  let mid = a1 * (b & 0xFFFFu) + b1 * (a & 0xFFFFu);
  let lo = (a & 0xFFFFu) * (b & 0xFFFFu);
  if ((a1 != 0u && b1 != 0u) || mid > 0xFFFFu || lo + (mid << 16u) < lo) {
    nat_ovf = 1u;
  }
  return a * b;
}

`;
