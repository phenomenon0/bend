// The generator: a random, well-typed Bend program from a small typed
// grammar, kept as a tree the reducer can shrink. A program is a custom
// datatype, a fixed prelude, a few generated defs (plain, matching,
// recursive over a Nat, a list, a string or the datatype) and a main whose
// value is a String of parts: pure (every lane prints it, the interpreter
// normalizes it) or IO (prints and binds, with a pure twin for the
// interpreter). Variables are tracked with their quantity: a `+` one is used
// freely, an affine one at most once (a match's arms each start from the
// same uses), so what the checker refuses is the grammar's slack, counted.

// Types
// =====

export type Ty = "U32" | "Nat" | "Bool" | "Str" | "Chr" | "LU" | "LS" | "U64"
  | "I64" | "MU" | "MN" | "T" | "F64" | "FUU";

// A node: text with holes. `ty` lets the reducer put a leaf in its place.
export type Node = { ty: Ty; parts: (string | Node)[] };

// A body: matches first (the checker refuses a let before a match on a
// parameter), then lets, then the value.
export type Body =
  | { $: "mat"; x: string; arms: { pat: string; body: Body }[] }
  | { $: "ret"; lets: Let[]; e: Node };

export type Let = { names: string[]; plus: boolean; ty: Ty | null; v: Node[] };

export type Def = { name: string; head: string; body: Body; uses: string[] };

export type Stmt = { $: "print"; e: Node } | { $: "bind"; x: string; ty: Ty; e: Node };

export type Prog = {
  seed: number;
  tag: string;
  io: boolean;
  f64: boolean;
  defs: Def[];
  parts: Node[];
  stmts: Stmt[];
  lets: Let[];
};

type Var = { k: string; ty: Ty; plus: boolean; used: boolean };

type Sig = { name: string; ps: { ty: Ty; q: string }[]; ret: Ty; tpl?: boolean };

// Rand
// ====

export function rng(seed: number): () => number {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6D2B79F5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

// Text
// ====

export const TY: Record<Ty, string> = {
  U32: "U32", Nat: "Nat", Bool: "Bool", Str: "String", Chr: "Char",
  LU: "List<&2, U32>", LS: "List<&2, String>", U64: "U64", I64: "I64",
  MU: "Maybe<&2, U32>", MN: "Maybe<&2, Nat>", T: "T0", F64: "F64",
  FUU: "U32 -> U32",
};

// The smallest value of each type: what the reducer puts in a node's place.
export const LEAF: Record<Ty, string> = {
  U32: "0", Nat: "0n", Bool: "False{}", Str: "\"\"", Chr: "'a'", LU: "Nil{}",
  LS: "Nil{}", U64: "u64.of(0, 0)", I64: "i64.of(0, 0)", MU: "None{}",
  MN: "None{}", T: "K2{}", F64: "0.0d", FUU: "(x => x)",
};

export function node_text(n: Node): string {
  return n.parts.map((p) => typeof p === "string" ? p : node_text(p)).join("");
}

function ind(d: number): string {
  return "  ".repeat(d);
}

function let_text(l: Let, d: number): string {
  if (l.names.length === 2 && l.v.length === 2) {
    return ind(d) + l.names.join(" ") + " = " + l.v.map(node_text).join(" ") + "\n";
  }
  return ind(d) + (l.plus ? "+" : "") + l.names[0]
    + (l.ty === null ? "" : " : " + TY[l.ty]) + " = " + node_text(l.v[0]) + "\n";
}

export function body_text(b: Body, d: number): string {
  if (b.$ === "ret") {
    return b.lets.map((l) => let_text(l, d)).join("") + ind(d) + node_text(b.e) + "\n";
  }
  return ind(d) + "match " + b.x + ":\n" + b.arms.map((a) => ind(d + 1) + "case "
    + a.pat + ":\n" + body_text(a.body, d + 2)).join("");
}

// main's value (a pure program's), as a def body
function pure_body(p: Prog): string {
  return p.lets.map((l) => let_text(l, 1)).join("")
    + "  " + (p.parts.length === 0 ? "\"\"" : p.parts.map(node_text).join(" ++ \" | \" ++ ")) + "\n";
}

// an IO program's steps, as lines of a do block
function io_steps(p: Prog): string {
  return p.stmts.map((s) => s.$ === "print"
    ? "    IO.print(" + node_text(s.e) + ")\n"
    : "    " + s.x + " : " + TY[s.ty] + " <- IO.pure(" + TY[s.ty] + ", " + node_text(s.e) + ")\n").join("");
}

export function prog_text(p: Prog, twin = false): string {
  const out = ["import Base", "", TYPE];
  for (const d of p.defs) {
    out.push(d.head + "\n" + body_text(d.body, 1));
  }
  if (!p.io) {
    out.push("def main() -> String:\n" + pure_body(p));
  } else if (twin) {
    // the interpreter's twin: each bind a let, the prints one string
    const lets = p.stmts.flatMap((s) => s.$ === "bind"
      ? ["  +" + s.x + " : " + TY[s.ty] + " = " + node_text(s.e) + "\n"] : []);
    const outs = p.stmts.flatMap((s) => s.$ === "print" ? [node_text(s.e)] : []);
    out.push("def main() -> String:\n" + lets.join("") + "  "
      + (outs.length === 0 ? "\"\"" : outs.map((o) => "(" + o + ")").join(" ++ \"\\n\" ++ ")) + "\n");
  } else {
    out.push("def main() -> IO(Unit):\n  do IO<Unit>:\n" + io_steps(p) + "    IO.print(\"end\")\n");
  }
  return out.join("\n");
}

// Programs of one kind (their tags apart) as one: each pure main a def of
// its own, main their values between SEPs; the IO ones' steps in a row.
export const SEP = "@@SEP@@";

export function batch_render(ps: Prog[]): string {
  const out = ["import Base", "", TYPE];
  for (const p of ps) {
    for (const d of p.defs) {
      out.push(d.head + "\n" + body_text(d.body, 1));
    }
  }
  if (!ps[0].io) {
    for (const p of ps) out.push("def m" + p.tag + "() -> String:\n" + pure_body(p));
    out.push("def main() -> String:\n  " + ps.map((p) => "m" + p.tag + "()").join(" ++ \"" + SEP + "\" ++ ") + "\n");
  } else {
    out.push("def main() -> IO(Unit):\n  do IO<Unit>:\n" + ps.map((p) => io_steps(p)
      + "    IO.print(\"" + SEP + "\")\n").join("") + "    IO.print(\"end\")\n");
  }
  const text = out.join("\n");
  return text.replace(TYPE, TYPE + "\n" + prelude_for(text));
}

// Prelude
// =======

const TYPE = `type T0 is Data:
  K0{a: U32, s: String}
  K1{n: Nat, t: T0}
  K2{}
  K3{xs: List<&2, U32>, b: Bool, t: T0}
`;

// Fixed helpers, each kept only if the program names it (prog_prune).
export const PRELUDE_DEFS: Record<string, string> = {
  "w.ext": `def w.ext(n: Nat, a: Word(n), hi: Word(32n)) -> Word(Nat.add(n, 32n)):
  match n:
    case 0n:
      hi
    case 1n+p:
      match a:
        case WCon{b, t}:
          WCon{b, w.ext(p, t, hi)}
`,
  "w.dig": `def w.dig(a: Bool, b: Bool, c: Bool, d: Bool) -> String:
  String.take(String.drop("0123456789abcdef", Nat.add(Nat.add(Bool.pick(Nat, a, 1n, 0n), Bool.pick(Nat, b, 2n, 0n)),
    Nat.add(Bool.pick(Nat, c, 4n, 0n), Bool.pick(Nat, d, 8n, 0n)))), 1n)
`,
  "w.hex": `def w.hex(n: Nat, w: Word(n)) -> String:
  match n:
    case 4n+p:
      match w:
        case WCon{a, WCon{b, WCon{c, WCon{d, t}}}}:
          w.hex(p, t) ++ w.dig(a, b, c, d)
    case _:
      ""
`,
  "u32.hex": `def u32.hex(x: U32) -> String:
  match x:
    case U32{w}:
      w.hex(32n, w)
`,
  "app": `def app(f: U32 -> U32, x: U32) -> U32:
  f(x)
`,
  "sumu": `def sumu(xs: List<&2, U32>) -> U32:
  match xs:
    case []:
      0
    case x <> rest:
      (x + sumu(rest) : U32)
`,
  "showlu": `def showlu(+xs: List<&2, U32>) -> String:
  List.show(~&2, ~U32, ~u32.hex, xs)
`,
  "showls": `def showls(+xs: List<&2, String>) -> String:
  List.show(~&2, ~String, ~(s => "<" ++ s ++ ">"), xs)
`,
  "showmu": `def showmu(m: Maybe<&2, U32>) -> String:
  match m:
    case None{}:
      "none"
    case Some{x}:
      "some " ++ u32.hex(x)
`,
  "showmn": `def showmn(m: Maybe<&2, Nat>) -> String:
  match m:
    case None{}:
      "none"
    case Some{x}:
      "some " ++ Nat.show(x)
`,
  "showt": `def showt(t: T0) -> String:
  match t:
    case K0{a, s}:
      "K0(" ++ u32.hex(a) ++ "," ++ s ++ ")"
    case K1{n, t}:
      "K1(" ++ Nat.show(n) ++ "," ++ showt(t) ++ ")"
    case K2{}:
      "K2"
    case K3{xs, b, t}:
      "K3(" ++ showlu(xs) ++ "," ++ Bool.show(b) ++ "," ++ showt(t) ++ ")"
`,
  "mapu": `def mapu(~f: U32 -> U32, xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case []:
      []
    case +x <> rest:
      f(x) <> mapu(~f, rest)
`,
  "u64.of": `def u64.of(hi: U32, lo: U32) -> U64:
  match hi lo:
    case U32{h} U32{l}:
      U64{w.ext(32n, l, h)}
`,
  "i64.of": `def i64.of(hi: U32, lo: U32) -> I64:
  match hi lo:
    case U32{h} U32{l}:
      I64{w.ext(32n, l, h)}
`,
  "u64.show": `def u64.show(x: U64) -> String:
  match x:
    case U64{w}:
      w.hex(64n, w)
`,
  "i64.show": `def i64.show(x: I64) -> String:
  match x:
    case I64{w}:
      w.hex(64n, w)
`,
  "pick3": `def pick3(-A: Data, +c: Bool, +a: A, +b: A) -> List<&2, A>:
  Bool.pick(A, c, a, b) <> Bool.pick(A, c, b, a) <> [a]
`,
  "len": `def len(a, -A: Kind(a), xs: List<a, A>) -> Nat:
  List.length(a, A, xs)
`,
};


// Gen
// ===

const ALPHA = ["a", "b", "c", "x", "y", "z", "A", "Z", "0", "1", "9", " ", " ", ",", ".",
  "-", "\\t", "\\n", "\\r", "é", "ß", "\\u{1F600}", "\\u{7F}", "\\0", "'", "\\\"", "\\\\", "ab",
  "  ", "é\\u{301}", "\\u{85}", "\\u{A0}", "\\u{FEFF}", "Σ", "ǅ"];

const U32S = [0, 1, 2, 3, 5, 7, 8, 10, 31, 32, 33, 63, 64, 127, 128, 255, 256, 1000,
  65535, 65536, 2147483647, 2147483648, 4294967295, 4294967294, 3000000000, 12345];

export class Gen {
  r: () => number;
  vars: Var[] = [];
  sigs: Sig[] = [];
  fuel = 0;
  n = 0;
  f64: boolean;
  self: { sig: Sig; small: string } | null = null;
  selfUsed = false;

  tag: string;

  constructor(seed: number, f64: boolean, tag: string) {
    this.r = rng(seed);
    this.f64 = f64;
    this.tag = tag;
  }

  int(n: number): number {
    return Math.floor(this.r() * n);
  }

  pick<X>(xs: X[]): X {
    return xs[this.int(xs.length)];
  }

  chance(p: number): boolean {
    return this.r() < p;
  }

  fresh(s = "v"): string {
    return s + this.tag + String(this.n++);
  }

  // Vars
  // ----

  avail(ty: Ty): Var[] {
    return this.vars.filter((v) => v.ty === ty && (v.plus || !v.used));
  }

  use(v: Var): Node {
    if (!v.plus) {
      v.used = true;
    }
    return { ty: v.ty, parts: [v.k] };
  }

  snap(): boolean[] {
    return this.vars.map((v) => v.used);
  }

  // runs each branch from the same uses; after, a var is used if any used it
  branch<X>(fs: (() => X)[]): X[] {
    const s0 = this.snap();
    const n0 = this.vars.length;
    const acc = s0.slice();
    const out = fs.map((f) => {
      this.vars.forEach((v, i) => { if (i < n0) v.used = s0[i]; });
      const x = f();
      this.vars.slice(0, n0).forEach((v, i) => { acc[i] = acc[i] || v.used; });
      this.vars.length = n0;
      return x;
    });
    this.vars.forEach((v, i) => { v.used = acc[i]; });
    return out;
  }

  scope<X>(vs: Var[], f: () => X): X {
    const n0 = this.vars.length;
    this.vars.push(...vs);
    const x = f();
    this.vars.length = n0;
    return x;
  }

  // Nodes
  // -----

  N(ty: Ty, ...parts: (string | Node)[]): Node {
    return { ty, parts };
  }

  // an expression of type ty at depth d (0: a leaf)
  e(ty: Ty, d: number): Node {
    this.fuel -= 1;
    if (this.fuel < 0) {
      d = 0;
    }
    const vs = this.avail(ty);
    if (vs.length > 0 && this.chance(d === 0 ? 0.7 : 0.4)) {
      return this.use(this.pick(vs));
    }
    if (d <= 0) {
      return this.lit(ty);
    }
    const calls = this.sigs.filter((s) => s.ret === ty);
    if (calls.length > 0 && this.chance(0.15)) {
      return this.call(this.pick(calls), d - 1);
    }
    if (this.self !== null && !this.selfUsed && this.self.sig.ret === ty && this.chance(0.35)) {
      this.selfUsed = true;
      return this.selfcall(d - 1);
    }
    if (ty !== "FUU" && this.chance(0.07)) {
      return this.bpick(ty, d - 1);
    }
    return this.op(ty, d - 1);
  }

  call(s: Sig, d: number): Node {
    const parts: (string | Node)[] = [s.name + "("];
    s.ps.forEach((p, i) => {
      if (i > 0) parts.push(", ");
      parts.push(this.arg(p.ty, d));
    });
    parts.push(")");
    return this.N(s.ret, ...parts);
  }

  arg(ty: Ty, d: number): Node {
    return ty === "Nat" ? this.small(d) : this.e(ty, d);
  }

  selfcall(d: number): Node {
    const s = this.self!;
    const parts: (string | Node)[] = [s.sig.name + "(" + s.small];
    s.sig.ps.slice(1).forEach((p) => {
      parts.push(", ");
      parts.push(this.arg(p.ty, d));
    });
    parts.push(")");
    return this.N(s.sig.ret, ...parts);
  }

  bpick(ty: Ty, d: number): Node {
    const c = this.e("Bool", d);
    const a = this.e(ty, d);
    const b = this.e(ty, d);
    return this.N(ty, "Bool.pick(" + TY[ty] + ", ", c, ", ", a, ", ", b, ")");
  }

  // a string built at a borrowed read's call (Bytes.len(SCon{h, t})):
  // the read must evaluate it once, and drop it once
  built(d: number): Node {
    if (this.chance(0.5)) return this.e("Str", d);
    const S = (): Node => this.e("Str", 0);
    return this.pick([
      () => this.N("Str", "SCon{", this.e("Chr", 0), ", ", S(), "}"),
      () => this.N("Str", "Bytes.append(", S(), ", ", S(), ")"),
      () => this.N("Str", "(", S(), " ++ ", S(), ")"),
      () => this.N("Str", "Bytes.push(", S(), ", ", String(this.int(256)), ")"),
    ])();
  }

  // a Nat the interpreter can count: literals, lengths, small arithmetic
  small(d: number): Node {
    if (d <= 0 || this.chance(0.4)) {
      const vs = this.avail("Nat");
      return vs.length > 0 && this.chance(0.5) ? this.use(this.pick(vs))
        : this.N("Nat", String(this.int(9)) + "n");
    }
    return this.op("Nat", d - 1);
  }

  lit(ty: Ty): Node {
    switch (ty) {
      case "U32": return this.N(ty, String(this.chance(0.6) ? this.pick(U32S) : this.int(4294967296)));
      case "Nat": return this.N(ty, String(this.int(12)) + "n");
      case "Bool": return this.N(ty, this.chance(0.5) ? "True{}" : "False{}");
      case "Str": return this.N(ty, this.str());
      case "Chr": return this.N(ty, this.pick(["'a'", "'Z'", "' '", "'0'", "','", "'é'", "'\\n'", "'\\t'", "'x'"]));
      case "LU": {
        const k = this.int(5);
        return k === 0 ? this.N(ty, "Nil{}") : this.N(ty, "[" + Array.from({ length: k },
          () => String(this.pick(U32S))).join(", ") + "]");
      }
      case "LS": {
        const k = this.int(4);
        return k === 0 ? this.N(ty, "Nil{}") : this.N(ty, "[" + Array.from({ length: k },
          () => this.str()).join(", ") + "]");
      }
      case "U64": return this.N(ty, "u64.of(" + String(this.pick(U32S)) + ", " + String(this.pick(U32S)) + ")");
      case "I64": return this.N(ty, "i64.of(" + String(this.pick(U32S)) + ", " + String(this.pick(U32S)) + ")");
      case "MU": return this.chance(0.5) ? this.N(ty, "None{}") : this.N(ty, "Some{" + String(this.pick(U32S)) + "}");
      case "MN": return this.chance(0.5) ? this.N(ty, "None{}") : this.N(ty, "Some{" + String(this.int(9)) + "n}");
      case "T": return this.N(ty, this.pick(["K2{}", "K0{7, \"t\"}", "K1{2n, K2{}}", "K3{[1, 2], True{}, K2{}}"]));
      case "F64": return this.N(ty, this.pick(["0.0d", "1.0d", "0.5d", "2.5d", "3.0d", "1.0e10d", "0.1d", "7.25d"]));
      case "FUU": return this.lam(0);
    }
  }

  str(): string {
    const k = this.int(5);
    let s = "";
    for (let i = 0; i < k; i++) s += this.pick(ALPHA);
    return "\"" + s + "\"";
  }

  lam(d: number): Node {
    const x = this.fresh("x");
    const plus = this.chance(0.5);
    const body = this.scope([{ k: x, ty: "U32", plus, used: false }], () => this.e("U32", d));
    return this.N("FUU", "(" + (plus ? "+" : "") + x + " => ", body, ")");
  }

  // a closed lambda for a template argument: no local variable
  tlam(ty: "U32" | "Bool", d: number, plus = true): Node {
    const saved = this.vars;
    const s0 = this.self;
    this.vars = [];
    this.self = null;
    const x = this.fresh("y");
    this.vars.push({ k: x, ty: "U32", plus, used: false });
    const body = this.e(ty, d);
    this.vars = saved;
    this.self = s0;
    return this.N(ty, "~(" + (plus ? "+" : "") + x + " => ", body, ")");
  }

  // the operations of each type
  op(ty: Ty, d: number): Node {
    const E = (t: Ty): Node => this.e(t, d);
    const S = (): Node => this.small(d);
    const N = this.N.bind(this);
    const F = (name: string, ...xs: (Node | string)[]): Node => {
      const parts: (string | Node)[] = [name + "("];
      xs.forEach((x, i) => { if (i > 0) parts.push(", "); parts.push(x); });
      parts.push(")");
      return N(ty, ...parts);
    };
    const bin = (op: string): Node => N(ty, "(", E(ty), " " + op + " ", E(ty), " : " + TY[ty] + ")");
    const choices: (() => Node)[] = [];
    const add = (w: number, f: () => Node): void => { for (let i = 0; i < w; i++) choices.push(f); };
    switch (ty) {
      case "U32":
        add(3, () => bin(this.pick(["+", "-", "*", "/", "%", ".&.", ".|.", ".^."])));
        add(2, () => F("U32." + this.pick(["add", "sub", "mul", "div", "mod", "and", "or", "xor", "min", "max"]), E("U32"), E("U32")));
        add(1, () => F("U32." + this.pick(["not", "shl", "shr", "inc"]), E("U32")));
        add(2, () => F("U32." + this.pick(["shln", "shrn"]), E("U32"), this.pick([S(), N("Nat", this.pick(["31n", "32n", "33n", "64n", "0n", "1n"]))])));
        add(1, () => F("U32.pow", E("U32"), N("Nat", String(this.int(6)) + "n")));
        add(1, () => F("U32.clamp", E("U32"), E("U32"), E("U32")));
        add(1, () => F("U32.from_nat", S()));
        add(1, () => F("Char.to_u32", E("Chr")));
        add(1, () => F("Bool.to_u32", E("Bool")));
        add(1, () => F("String.hash", E("Str")));
        add(2, () => F("Bytes.get", this.built(d), S()));
        add(1, () => F("Bytes.word_le", this.built(d), S()));
        add(1, () => F("sumu", E("LU")));
        add(1, () => F("Maybe.default", "&2", "U32", E("MU"), E("U32")));
        add(1, () => F("app", E("FUU"), E("U32")));
        add(1, () => {
          const vs = this.avail("FUU");
          return vs.length > 0 ? N("U32", this.use(this.pick(vs)), "(", E("U32"), ")") : F("app", E("FUU"), E("U32"));
        });
        add(1, () => N("U32", "Bool.pick(U32 -> U32, ", E("Bool"), ", ", this.lam(d), ", ", this.lam(d), ")(", E("U32"), ")"));
        add(1, () => this.tmatch("U32", d));
        if (this.f64) add(2, () => F("F64.to_u32", E("F64")));
        break;
      case "Nat":
        add(2, () => F("Nat." + this.pick(["add", "sub", "div", "mod", "min", "max"]), S(), S()));
        add(1, () => F("Nat.mul", N("Nat", String(this.int(20)) + "n"), S()));
        add(1, () => N("Nat", "1n+", S()));
        add(1, () => F("String.length", E("Str")));
        add(1, () => F("Bytes.len", this.built(d)));
        add(1, () => F("List.length", "&2", "U32", E("LU")));
        add(1, () => F("len", "&2", "String", E("LS")));
        add(1, () => F("U32.to_nat", N("U32", "U32.and(", E("U32"), ", 63)")));
        add(1, () => F("Bytes.span", this.built(d), S(), E("U32"), E("U32")));
        add(2, () => F("Bytes.find_byte", this.built(d), S(), E("U32")));
        add(1, () => F("Bytes.find_any", this.built(d), S(), E("U32"), E("U32"), E("U32"), E("U32")));
        add(1, () => F("String.count", E("Str"), E("Str")));
        add(1, () => F("U32.log2", E("U32")));
        add(1, () => F("Maybe.default", "&2", "Nat", E("MN"), S()));
        break;
      case "Bool":
        add(2, () => F("U32." + this.pick(["is_eq", "is_ne", "is_lt", "is_le", "is_gt", "is_ge"]), E("U32"), E("U32")));
        add(1, () => F("U32." + this.pick(["is_zero", "is_even"]), E("U32")));
        add(1, () => F("Nat." + this.pick(["is_eq", "is_ne", "is_lt", "is_le", "is_gt", "is_ge"]), S(), S()));
        add(2, () => F("String." + this.pick(["eq", "is_lt", "is_le", "is_gt", "is_ge", "starts_with", "ends_with", "contains"]), E("Str"), E("Str")));
        add(1, () => F("String." + this.pick(["is_empty", "is_digit", "is_alpha", "is_space", "is_alnum", "is_lower", "is_upper", "is_ascii", "is_printable", "is_identifier", "is_title", "is_numeric", "is_decimal"]), E("Str")));
        add(1, () => F("Bool." + this.pick(["and", "or", "xor"]), E("Bool"), E("Bool")));
        add(1, () => F("Bool.not", E("Bool")));
        add(1, () => N("Bool", "(", E("Bool"), this.pick([" && ", " || "]), E("Bool"), ")"));
        add(1, () => F("Bytes.starts_with", E("Str"), E("Str")));
        add(1, () => F("Maybe.is_some", "&2", "U32", E("MU")));
        add(1, () => F("List.is_empty", "&2", "U32", E("LU")));
        add(1, () => F("Cmp.is_" + this.pick(["lt", "eq", "gt", "le", "ge"]), N("Bool", "U32.cmp(", E("U32"), ", ", E("U32"), ")")));
        add(1, () => F("U64.is_" + this.pick(["eq", "lt", "le", "gt", "zero"].slice(0, 4)), E("U64"), E("U64")));
        add(1, () => F("I64.is_" + this.pick(["eq", "lt", "le", "gt", "ge"]), E("I64"), E("I64")));
        add(1, () => F("I64.is_neg", E("I64")));
        add(1, () => F("Char.is_" + this.pick(["digit", "upper", "lower", "space", "alnum", "ascii"]), E("Chr")));
        add(1, () => F("List." + this.pick(["any", "all"]), "~&2", "~U32", this.tlam("Bool", d, false), E("LU")));
        if (this.f64) add(1, () => F("F64.is_" + this.pick(["eq", "lt", "le", "gt", "ne"]), E("F64"), E("F64")));
        break;
      case "Str":
        add(4, () => N("Str", "(", E("Str"), " ++ ", E("Str"), ")"));
        add(1, () => N("Str", "SCon{", E("Chr"), ", ", E("Str"), "}"));
        add(2, () => F("U32.show", E("U32")));
        add(1, () => F("Nat.show", S()));
        add(1, () => F("Bool.show", E("Bool")));
        add(1, () => F("Char.show", E("Chr")));
        add(2, () => F("String." + this.pick(["take", "drop", "take_end", "drop_end"]), E("Str"), S()));
        add(1, () => F("String.slice", E("Str"), S(), S()));
        add(2, () => F("String." + this.pick(["reverse", "to_upper", "to_lower", "trim", "trim_start", "trim_end", "capitalize", "swapcase", "title", "casefold", "copy"]), E("Str")));
        add(1, () => F("String.repeat", E("Str"), N("Nat", String(this.int(4)) + "n")));
        add(1, () => F("String." + this.pick(["pad_start", "pad_end"]), E("Str"), S(), E("Chr")));
        add(1, () => F("String.zfill", E("Str"), S()));
        add(1, () => F("String.center", E("Str"), S(), E("Chr")));
        add(1, () => F("String.expandtabs", E("Str"), N("Nat", String(this.int(5)) + "n")));
        add(1, () => F("String.replace", E("Str"), E("Str"), E("Str")));
        add(1, () => F("String." + this.pick(["remove_prefix", "remove_suffix"]), E("Str"), E("Str")));
        add(1, () => F("String.join", E("LS"), E("Str")));
        add(1, () => F("String.concat", E("LS")));
        add(1, () => F("String.from_list", N("Str", "String.to_list(", E("Str"), ")")));
        add(2, () => F("Bytes.push", E("Str"), this.chance(0.7) ? N("U32", String(this.pick([this.int(256), 300, 0x1F600, 0x10FFFF, 0xFEFF])))
          : N("U32", "U32.and(", E("U32"), ", 255)")));
        add(1, () => F("Bytes.slice", E("Str"), S(), S()));
        add(1, () => F("Bytes.drop", E("Str"), S()));
        add(1, () => F("Bytes.append", E("Str"), E("Str")));
        add(1, () => F("Bytes.from_list", N("LU", "mapu(~(+b => U32.and(b, 255)), ", E("LU"), ")")));
        add(2, () => F("showlu", E("LU")));
        add(1, () => F("showls", E("LS")));
        add(1, () => F("showmu", E("MU")));
        add(1, () => F("showmn", E("MN")));
        add(1, () => F("showt", E("T")));
        add(1, () => F("u64.show", E("U64")));
        add(1, () => F("i64.show", E("I64")));
        add(1, () => this.tmatch("Str", d));
        add(1, () => F("Maybe.show", "~&2", "~Char", "~Char.show", N("Str", "String.get", "(", E("Str"), ", ", S(), ")")));
        if (this.f64) add(3, () => F("F64.show", E("F64")));
        break;
      case "Chr":
        add(1, () => F("Char.from_u32", N("U32", "U32.and(", E("U32"), ", 1023)")));
        add(1, () => F("Char." + this.pick(["to_upper", "to_lower"]), E("Chr")));
        add(1, () => F("Maybe.default", "&2", "Char", N("Chr", "String." + this.pick(["get", "get_end"]) + "(", E("Str"), ", ", S(), ")"), E("Chr")));
        break;
      case "LU":
        add(2, () => N("LU", "(", E("U32"), " <> ", E("LU"), ")"));
        add(1, () => F("List.append", "&2", "U32", E("LU"), E("LU")));
        add(1, () => F("List.reverse", "&2", "U32", E("LU")));
        add(1, () => F("List." + this.pick(["take", "drop"]), "&2", "U32", E("LU"), S()));
        add(1, () => F("List.set", "&2", "U32", E("LU"), S(), E("U32")));
        add(1, () => F("List.tail", "&2", "U32", E("LU")));
        add(1, () => F("List.replicate", "U32", N("Nat", String(this.int(5)) + "n"), E("U32")));
        add(1, () => F("mapu", this.tlam("U32", d), E("LU")));
        add(1, () => F("List.filter", "~U32", this.tlam("Bool", d), E("LU")));
        add(1, () => F("List.sort", "~U32", "~(a => b => U32.is_le(a, b))", E("LU")));
        add(1, () => F("Bytes.to_list", E("Str")));
        add(1, () => F("pick3", "U32", E("Bool"), E("U32"), E("U32")));
        break;
      case "LS":
        add(1, () => N("LS", "(", E("Str"), " <> ", E("LS"), ")"));
        add(2, () => F("String.split", E("Str"), E("Chr")));
        add(2, () => F("String.split_on", E("Str"), E("Str")));
        add(1, () => F("String." + this.pick(["words", "lines", "splitlines"]), E("Str")));
        add(1, () => F("String.rsplit", E("Str"), E("Str")));
        add(1, () => F("List.reverse", "&2", "String", E("LS")));
        add(1, () => F("List.append", "&2", "String", E("LS"), E("LS")));
        break;
      case "MU":
        add(1, () => N("MU", "Some{", E("U32"), "}"));
        add(1, () => F("List." + this.pick(["head", "last"]), "&2", "U32", E("LU")));
        add(1, () => F("List.get", "&2", "U32", E("LU"), S()));
        break;
      case "MN":
        add(1, () => F("String." + this.pick(["find", "find_last"]), E("Str"), E("Str")));
        add(1, () => F("Bytes.find", E("Str"), E("Str")));
        break;
      case "U64":
        add(2, () => F("U64." + this.pick(["add", "sub", "mul", "and", "or", "xor"]), E("U64"), E("U64")));
        add(1, () => F("U64." + this.pick(["not", "shl", "shr", "inc"]), E("U64")));
        add(1, () => F("U64." + this.pick(["shln", "shrn"]), E("U64"), N("Nat", this.pick(["1n", "31n", "32n", "33n", "63n", "64n", "65n"]))));
        break;
      case "I64":
        add(2, () => F("I64." + this.pick(["add", "sub", "mul", "and", "or", "xor"]), E("I64"), E("I64")));
        add(1, () => F("I64." + this.pick(["not", "neg", "shl", "shr", "inc", "shr.s"]), E("I64")));
        add(1, () => F("I64." + this.pick(["shln", "shrn", "shr.s.n"]), E("I64"), N("Nat", this.pick(["1n", "31n", "32n", "63n", "64n", "70n"]))));
        break;
      case "T":
        add(2, () => N("T", "K0{", E("U32"), ", ", E("Str"), "}"));
        add(2, () => N("T", "K1{", S(), ", ", E("T"), "}"));
        add(1, () => N("T", "K3{", E("LU"), ", ", E("Bool"), ", ", E("T"), "}"));
        break;
      case "F64":
        add(3, () => F("F64." + this.pick(["add", "sub", "mul", "div", "mod", "pow", "atan2", "min", "max"]), E("F64"), E("F64")));
        add(2, () => F("F64." + this.pick(["neg", "abs", "sqrt", "floor", "ceil", "trunc", "round", "exp", "log", "sin", "square"]), E("F64")));
        add(1, () => F("F64.from_nat", S()));
        add(1, () => F("U32.to_f64", E("U32")));
        add(1, () => F("F64.pick", E("Bool"), E("F64"), E("F64")));
        break;
      case "FUU":
        add(1, () => this.lam(d));
        break;
    }
    return this.pick(choices)();
  }

  // a match on a variable in expression position is not Bend: a helper def
  // does it. tmatch builds an inline call to a template-free local: here, a
  // Bool.pick on a test of the value, which the compiler may lift.
  tmatch(ty: Ty, d: number): Node {
    const c = this.e("Bool", d);
    const a = this.e(ty, d + 1);
    const b = this.e(ty, d + 1);
    return this.N(ty, "Bool.pick(" + TY[ty] + ", ", c, ", ", a, ", ", b, ")");
  }

  // Bodies
  // ------

  lets(k: number, d: number): Let[] {
    const out: Let[] = [];
    for (let i = 0; i < k; i++) {
      const par = this.sigs.length >= 2 && this.chance(0.15);
      if (par) {
        const [s1, s2] = [this.pick(this.sigs), this.pick(this.sigs)];
        const [a, b] = [this.fresh(), this.fresh()];
        const v1 = this.call(s1, d);
        const v2 = this.call(s2, d);
        out.push({ names: [a, b], plus: false, ty: null, v: [v1, v2] });
        this.vars.push({ k: a, ty: s1.ret, plus: false, used: false },
          { k: b, ty: s2.ret, plus: false, used: false });
        continue;
      }
      const ty = this.ty(true);
      const plus = ty !== "FUU" && this.chance(0.6);
      const x = this.fresh();
      const v = this.e(ty, d);
      out.push({ names: [x], plus, ty, v: [v] });
      this.vars.push({ k: x, ty, plus, used: false });
    }
    return out;
  }

  ret(ty: Ty, d: number, nlets: number): Body {
    const n0 = this.vars.length;
    const lets = this.lets(nlets, d);
    const e = this.e(ty, d);
    this.vars.length = n0;
    return { $: "ret", lets, e };
  }

  ty(fn = false): Ty {
    const ts: Ty[] = ["U32", "U32", "U32", "Str", "Str", "Str", "Nat", "Bool", "LU", "LS", "U64", "I64", "MU", "T", "Chr"];
    if (fn) ts.push("FUU");
    if (this.f64) ts.push("F64", "F64");
    return this.pick(ts);
  }

  // the arms of a match on x : ty, each a body built by f
  arms(x: Var, f: () => Body): { pat: string; body: Body }[] {
    const plus = x.plus;
    x.used = !plus;
    const fv = (ty: Ty, q = this.chance(0.5)): Var => ({ k: this.fresh("p"), ty, plus: plus || q, used: false });
    const q = (v: Var): string => (v.plus && !plus ? "+" : "") + v.k;
    type Arm = { pat: string; vs: Var[] };
    let arms: Arm[] = [];
    const deflt = (): Arm => {
      if (this.chance(0.5)) return { pat: "_", vs: [] };
      const v: Var = { k: this.fresh("w"), ty: x.ty, plus, used: false };
      return { pat: v.k, vs: [v] };
    };
    switch (x.ty) {
      case "Bool":
        arms = this.chance(0.7) ? [{ pat: "True{}", vs: [] }, { pat: "False{}", vs: [] }]
          : [{ pat: this.pick(["True{}", "False{}"]), vs: [] }, deflt()];
        break;
      case "Nat": {
        const p = fv("Nat");
        if (!plus || this.chance(0.6)) {
          arms = [{ pat: "0n", vs: [] }, { pat: "1n+" + q(p), vs: [p] }];
        } else {
          const p2 = fv("Nat");
          arms = [{ pat: String(this.int(3)) + "n", vs: [] }, { pat: "2n+" + q(p2), vs: [p2] }, deflt()];
        }
        break;
      }
      case "U32":
        arms = [{ pat: String(this.pick([0, 1, 7, 255, 4294967295])), vs: [] }, ...(this.chance(0.5) ? [{ pat: String(this.pick([2, 3, 256, 65536])), vs: [] }] : []), deflt()];
        break;
      case "LU": {
        const h = fv("U32"), t = fv("LU");
        const alt = this.chance(0.5);
        arms = [{ pat: alt ? "Nil{}" : "[]", vs: [] }, { pat: alt ? "Con{" + q(h) + ", " + q(t) + "}" : q(h) + " <> " + q(t), vs: [h, t] }];
        if (this.chance(0.4)) {
          const a = fv("U32"), b = fv("U32"), r = fv("LU");
          arms.splice(1, 0, { pat: "Con{" + q(a) + ", Con{" + q(b) + ", " + q(r) + "}}", vs: [a, b, r] });
        }
        if (this.chance(0.3)) {
          arms = [arms[0], ...arms.slice(1, -1), deflt()];
        }
        break;
      }
      case "Str": {
        const c = fv("U32"), t = fv("Str"), h = fv("Chr");
        arms = this.chance(0.5)
          ? [{ pat: "SNil{}", vs: [] }, { pat: "SCon{Chr{" + q(c) + "}, " + q(t) + "}", vs: [c, t] }]
          : [{ pat: "SNil{}", vs: [] }, { pat: "SCon{" + q(h) + ", " + q(t) + "}", vs: [h, t] }];
        if (this.chance(0.3)) arms = [arms[1], deflt()];
        break;
      }
      case "MU": {
        const v = fv("U32");
        arms = [{ pat: "None{}", vs: [] }, { pat: "Some{" + q(v) + "}", vs: [v] }];
        break;
      }
      case "T": {
        const [a, s, n, t, xs, b, t3] = [fv("U32"), fv("Str"), fv("Nat"), fv("T"), fv("LU"), fv("Bool"), fv("T")];
        arms = [
          { pat: "K0{" + q(a) + ", " + q(s) + "}", vs: [a, s] },
          { pat: "K1{" + q(n) + ", " + q(t) + "}", vs: [n, t] },
          { pat: "K2{}", vs: [] },
          { pat: "K3{" + q(xs) + ", " + q(b) + ", " + q(t3) + "}", vs: [xs, b, t3] },
        ];
        if (this.chance(0.5)) {
          // a nested arm ahead of the general one
          const [p, u, w] = [fv("Nat"), fv("U32"), fv("Str")];
          const nest = this.pick([
            { pat: "K1{1n+" + q(p) + ", K0{" + q(u) + ", " + q(w) + "}}", vs: [p, u, w] },
            { pat: "K1{0n, K2{}}", vs: [] },
            { pat: "K3{[], True{}, _}", vs: [] },
            { pat: "K0{7, " + q(w) + "}", vs: [w] },
          ]);
          arms.splice(this.int(2), 0, nest);
        }
        if (this.chance(0.4)) {
          const k = 1 + this.int(arms.length - 1);
          arms = [...arms.slice(0, k), deflt()];
        }
        break;
      }
      default:
        arms = [deflt()];
    }
    return this.branch(arms.map((a) => () => ({ pat: a.pat, body: this.scope(a.vs, f) })));
  }

  // Defs
  // ----

  def(i: number): Def {
    const name = "f" + this.tag + String(i);
    const kind = this.pick(["plain", "plain", "mat", "mat", "nat", "nat", "list", "str", "tree"]);
    const ret = this.pick<Ty>(["U32", "U32", "Str", "Str", "Str", "Bool", "LU", "Nat", "T", "FUU", ...(this.f64 ? ["F64" as Ty] : [])]);
    const first: Ty | null = kind === "nat" ? "Nat" : kind === "list" ? "LU" : kind === "str" ? "Str"
      : kind === "tree" ? "T" : null;
    const np = this.int(3) + (first === null ? 1 : 0);
    const ps: { ty: Ty; q: string }[] = [];
    if (first !== null) ps.push({ ty: first, q: "" });
    for (let j = 0; j < np; j++) {
      const ty = this.ty(this.chance(0.3));
      ps.push({ ty, q: ty === "FUU" ? "" : this.pick(["", "+", "+"]) });
    }
    if (this.chance(0.15)) {
      ps.push({ ty: "U32", q: "-" });
    }
    const vars: Var[] = ps.map((p, j) => ({ k: "a" + String(j), ty: p.ty, plus: p.q === "+", used: p.q === "-" }));
    const sig: Sig = { name, ps, ret };
    const head = "def " + name + "(" + ps.map((p, j) => (p.q === "-" ? "-" : p.q) + "a" + String(j) + ": "
      + TY[p.ty]).join(", ") + ") -> " + TY[ret] + ":";
    this.vars = vars;
    this.fuel = 60;
    let body: Body;
    const d = 3;
    if (first !== null) {
      // recursion on the first parameter: its step arm may call name once
      const x = vars[0];
      const arms = this.arms(x, () => {
        const sm = this.vars.find((v) => v.ty === first && v.k.startsWith("p") && !v.used);
        if (sm !== undefined) {
          this.self = { sig: { ...sig, ps: sig.ps }, small: sm.k };
          this.selfUsed = false;
          sm.used = !sm.plus;
        }
        const b = this.inner(ret, d);
        this.self = null;
        return b;
      });
      body = { $: "mat", x: x.k, arms };
    } else if (kind === "mat") {
      const ms = vars.filter((v) => ["Bool", "Nat", "U32", "LU", "Str", "MU", "T"].includes(v.ty) && !v.used
        && (v.plus || v.ty !== "U32"));
      if (ms.length > 0) {
        const x = ms[0];
        body = { $: "mat", x: x.k, arms: this.arms(x, () => this.inner(ret, d)) };
      } else {
        body = this.ret(ret, d, this.int(3));
      }
    } else {
      body = this.ret(ret, d, this.int(4));
    }
    this.sigs.push(sig);
    return { name, head, body, uses: [] };
  }

  // an arm's body: a nested match on a pattern variable, or lets and a value
  inner(ret: Ty, d: number): Body {
    const ms = this.vars.filter((v) => v.k.startsWith("p") && !v.used && ["Bool", "Nat", "LU", "MU", "T"].includes(v.ty));
    if (ms.length > 0 && this.chance(0.25) && this.self === null) {
      const x = ms[this.int(ms.length)];
      x.used = !x.plus;
      return { $: "mat", x: x.k, arms: this.arms(x, () => this.ret(ret, d - 1, this.int(2))) };
    }
    return this.ret(ret, d, this.int(3));
  }
}

// Prog
// ====

// tag: a prefix for its names, so programs can share a file
export function prog_gen(seed: number, io: boolean, f64: boolean, tag = ""): Prog {
  const g = new Gen(seed, f64, tag);
  const defs: Def[] = [];
  const nd = 1 + g.int(5);
  for (let i = 0; i < nd; i++) {
    defs.push(g.def(i));
  }
  g.vars = [];
  g.fuel = 80;
  const p: Prog = { seed, tag, io, f64, defs, parts: [], stmts: [], lets: [] };
  // what main shows: every def called once, then values of random types,
  // each through its type's show (a String alone is lossy to nest in)
  const shows = (): Node[] => {
    const out: Node[] = [];
    for (const s of g.sigs) out.push(show_of(s.ret, g.call(s, 2), g.chance(0.7)));
    const k = 2 + g.int(4);
    for (let i = 0; i < k; i++) {
      const ty = g.ty(true);
      out.push(show_of(ty, g.e(ty, 3), g.chance(0.7)));
    }
    return out;
  };
  if (!io) {
    p.lets = g.lets(g.int(4), 3);
    for (const v of g.vars) {
      if (g.chance(0.7) && (v.plus || !v.used)) p.parts.push(show_of(v.ty, g.use(v), g.chance(0.7)));
    }
    p.parts.push(...shows());
    // shuffled: a var's own show competes with the calls that read it
    for (let i = p.parts.length - 1; i > 0; i--) {
      const j = g.int(i + 1);
      [p.parts[i], p.parts[j]] = [p.parts[j], p.parts[i]];
    }
  } else {
    const k = 3 + g.int(5);
    for (let i = 0; i < k; i++) {
      if (g.chance(0.35)) {
        const ty = g.pick<Ty>(["U32", "Str", "Nat", "LU", "T"]);
        const x = g.fresh("b");
        p.stmts.push({ $: "bind", x, ty, e: g.e(ty, 3) });
        g.vars.push({ k: x, ty, plus: false, used: false });
      } else {
        const ty = g.ty(true);
        p.stmts.push({ $: "print", e: show_of(ty, g.e(ty, 3), g.chance(0.7)) });
      }
    }
    for (const e of shows()) p.stmts.push({ $: "print", e });
  }
  return p;
}

// A value of any type as a String.
// (U32.show runs its digit loop in the normalizer: a hex walk of the
// word is ten times cheaper there, and unpacks the word in C and JS)
export function show_of(ty: Ty, n: Node, hex = false): Node {
  const f: Record<Ty, string> = {
    U32: "U32.show", Nat: "Nat.show", Bool: "Bool.show", Str: "", Chr: "Char.show", LU: "showlu",
    LS: "showls", U64: "u64.show", I64: "i64.show", MU: "showmu", MN: "showmn", T: "showt",
    F64: "F64.show", FUU: "",
  };
  if (ty === "U32" && hex) return { ty: "Str", parts: ["u32.hex(", n, ")"] };
  return ty === "Str" ? n : ty === "FUU" ? { ty: "Str", parts: ["U32.show(app(", n, ", 12345))"] }
    : { ty: "Str", parts: [f[ty] + "(", n, ")"] };
}

// The prelude defs a program names, in dependency order.
export function prelude_for(text: string): string {
  const need = new Set<string>();
  const deps: Record<string, string[]> = {
    "showt": ["showlu", "u32.hex", "w.hex", "w.dig"], "showlu": ["u32.hex", "w.hex", "w.dig"],
    "showmu": ["u32.hex", "w.hex", "w.dig"], "u64.of": ["w.ext"], "i64.of": ["w.ext"],
    "u32.hex": ["w.hex", "w.dig"], "u64.show": ["w.hex", "w.dig"], "i64.show": ["w.hex", "w.dig"],
  };
  for (const k of Object.keys(PRELUDE_DEFS)) {
    if (new RegExp("(^|[^a-z0-9_.])" + k.replace(".", "\\.") + "\\(").test(text)) {
      need.add(k);
      (deps[k] ?? []).forEach((x) => need.add(x));
    }
  }
  return Object.keys(PRELUDE_DEFS).filter((k) => need.has(k)).map((k) => PRELUDE_DEFS[k]).join("\n");
}

export function prog_render(p: Prog, twin = false): string {
  const text = prog_text(p, twin);
  // the prelude goes in after the type, only what is named
  return text.replace(TYPE, TYPE + "\n" + prelude_for(text));
}
