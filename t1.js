function word_to_u32(w) {
  let x = 0;
  for (let i = 0; w.$ === "WCon"; i++) {
    x |= Number(w.head) << i;
    w = w.tail;
  }
  return x >>> 0;
}

function u32_to_word(x) {
  let w = {$: "WNil"};
  for (let i = 31; i >= 0; i--) {
    w = {$: "WCon", head: ((x >>> i) & 1) === 1, tail: w};
  }
  return w;
}

function cmp_new(a, b) {
  return {$: a < b ? "LT"
    : a === b ? "EQ" : "GT"};
}

function nat_divmod(a, b) {
  return b === 0n ? {$: "Tuple", fst: 0n, snd: a}
    : {$: "Tuple", fst: a / b, snd: a % b};
}

function nat_chk(n) {
  if (n > 281474976710655n) {
    throw "bend: a Nat past the largest immediate 2^48-1";
  }
  return n;
}

function f32_show(x) {
  if (x !== x) {
    return "nan";
  }
  if (!Number.isFinite(x) || Object.is(x, -0)) {
    return x < 0 ? "-inf"
      : x === 0 ? "-0" : "inf";
  }
  let s = "x";
  for (let p = 1; p <= 9 && Math.fround(Number(s)) !== x; p += 1) {
    s = String(Number(x.toExponential(p - 1)));
  }
  return s;
}

function f32_bits(x) {
  return new Uint32Array(new Float32Array([x]).buffer)[0];
}

function f32_from_bits(u) {
  return new Float32Array(new Uint32Array([u]).buffer)[0];
}

function f32_read(s) {
  const re = /^\s*[+-]?((\d+\.?\d*|\.\d+)(e[+-]?\d+)?|inf(inity)?|nan)$/i;
  const v = Number(s.replace(/inf\w*/i, "Infinity"));
  return re.test(s) ? {$: "Some", value: Math.fround(v)} : {$: "None"};
}

function word_to_u64(w) {
  let x = 0n;
  for (let i = 0; w.$ === "WCon"; i++) {
    if (w.head) { x |= 1n << BigInt(i); }
    w = w.tail;
  }
  return x;
}

function u64_to_word(x) {
  let w = {$: "WNil"};
  for (let i = 63; i >= 0; i--) {
    w = {$: "WCon", head: ((x >> BigInt(i)) & 1n) === 1n, tail: w};
  }
  return w;
}

function f64_bits(x) {
  const d = new DataView(new ArrayBuffer(8));
  d.setFloat64(0, x);
  return d.getBigUint64(0);
}

function f64_from_bits(u) {
  const d = new DataView(new ArrayBuffer(8));
  d.setBigUint64(0, u);
  return d.getFloat64(0);
}

function f64_show(x) {
  if (x !== x) {
    return "nan";
  }
  if (!Number.isFinite(x) || Object.is(x, -0)) {
    return x < 0 ? "-inf"
      : x === 0 ? "-0" : "inf";
  }
  let s = "x";
  for (let p = 1; p <= 17 && Number(s) !== x; p += 1) {
    s = String(Number(x.toExponential(p - 1)));
  }
  return s;
}

function f64_read(s) {
  const re = /^\s*[+-]?((\d+\.?\d*|\.\d+)(e[+-]?\d+)?|inf(inity)?|nan)$/i;
  const v = Number(s.replace(/inf\w*/i, "Infinity"));
  return re.test(s) ? {$: "Some", value: v} : {$: "None"};
}

// Scalar strings stay primitive; raw U32 Char values dispatch through char_code.
// The string boundary rejects raw values consistently, including SCon/from_list.
function char_code(c) { return typeof c === "string" ? c.codePointAt(0) : c.code; }
function str_prepend(c, s) {
  if (typeof c !== "string") { throw "bend: JS strings cannot contain non-scalar Char values"; }
  return c + s;
}
function str_length(s) { let n = 0n; for (const c of s) { n++; } return n; }
function str_offset(s, n) {
  let i = 0;
  while (n > 0n && i < s.length) { i += s.codePointAt(i) > 0xffff ? 2 : 1; n--; }
  return i;
}
function str_slice(s, lo, hi) {
  if (hi <= lo) { return ""; }
  const a = str_offset(s, lo);
  return s.slice(a, a + str_offset(s.slice(a), hi - lo));
}
function str_get(s, n) {
  const i = str_offset(s, n);
  return i === s.length ? {$: "None"} : {$: "Some", value: String.fromCodePoint(s.codePointAt(i))};
}
function str_end(s, n, take) {
  const len = str_length(s), at = len > n ? len - n : 0n;
  return take ? s.slice(str_offset(s, at)) : s.slice(0, str_offset(s, at));
}
function str_get_end(s, n) {
  const len = str_length(s);
  return n === 0n || n > len ? {$: "None"} : str_get(s, len - n);
}
function map_bit(s, pos) {
  const i = str_offset(s, pos / 33n), off = Number(pos % 33n);
  const b = i < s.length
    && (off === 0 || ((s.codePointAt(i) >>> (32 - off)) & 1) === 1);
  return {$: "Tuple", fst: s, snd: b};
}
function str_order(a, b) {
  let i = 0, j = 0;
  while (i < a.length && j < b.length) {
    const x = a.codePointAt(i), y = b.codePointAt(j);
    if (x !== y) { return {$: x < y ? "LT" : "GT"}; }
    i += x > 0xffff ? 2 : 1; j += y > 0xffff ? 2 : 1;
  }
  return {$: i < a.length ? "GT" : j < b.length ? "LT" : "EQ"};
}
function str_cmp(a, b) { return {$: "Tuple", fst: {$: "Tuple", fst: a, snd: b}, snd: str_order(a, b)}; }
function str_list(xs) {
  let out = {$: "Nil"};
  for (let i = xs.length - 1; i >= 0; i--) { out = {$: "Con", head: xs[i], tail: out}; }
  return out;
}
function str_from_list(xs) {
  const out = [];
  for (; xs.$ === "Con"; xs = xs.tail) { out.push(str_prepend(xs.head, "")); }
  return out.join("");
}
function str_join(xs, sep) {
  const out = [];
  for (; xs.$ === "Con"; xs = xs.tail) { out.push(xs.head); }
  return out.join(sep);
}
function str_repeat(s, n) {
  const len = str_length(s);
  if (len === 0n) { return ""; }
  if (n > 2147483648n / len) { throw "bend: a string past the maximum length 2^31"; }
  return s.repeat(Number(n));
}
function str_split(s, c) {
  // A raw separator cannot equal any scalar string element.
  return str_list(typeof c === "string" ? s.split(c) : [s]);
}

// Strings contain scalars only, so a nonempty scalar needle cannot match
// inside a surrogate pair. Native UTF-16 search is exact; convert only the
// final position to code points. No repeated positional get/offset scans.
function str_find(s, p, last) {
  const i = last ? s.lastIndexOf(p) : s.indexOf(p);
  return i < 0 ? {$: "None"} : {$: "Some", value: str_length(s.slice(0, i))};
}
function str_count(s, p) {
  if (p === "") { return str_length(s) + 1n; }
  let n = 0n, at = 0;
  for (;;) {
    const i = s.indexOf(p, at);
    if (i < 0) { return n; }
    n++; at = i + p.length;
  }
}
function str_replace(s, old, value) {
  // A string separator and array join treat $&, $1, etc. literally.
  if (old !== "") { return s.split(old).join(value); }
  return s === "" ? value : value + [...s].join(value) + value;
}
function str_partition(s, sep) {
  const i = sep === "" ? -1 : s.indexOf(sep);
  return {$: "Tuple", fst: i < 0 ? s : s.slice(0, i),
    snd: {$: "Tuple", fst: i < 0 ? "" : sep, snd: i < 0 ? "" : s.slice(i + sep.length)}};
}
function str_splitlines(s) {
  const lines = s.split(/\r\n|[\n\r\v\f\x1c-\x1e\x85\u2028\u2029]/);
  if (lines[lines.length - 1] === "") { lines.pop(); }
  return str_list(lines);
}
function str_capitalize(s) {
  return s.replace(/[a-zA-Z]/g, (c, i) => i === 0 ? c.toUpperCase() : c.toLowerCase());
}
function str_pad(s, width, c, mode) {
  const n = str_length(s);
  if (width <= n) { return s; }
  if (width > 2147483648n) { throw "bend: a string past the maximum length 2^31"; }
  const pad = str_prepend(c, "").repeat(Number(width - n));
  if (mode === 1) { return s + pad; }
  if (mode === 2 && (s[0] === "+" || s[0] === "-")) { return s[0] + pad + s.slice(1); }
  return pad + s;
}
// The C VM over Int32Array: three ints per inst, the set ranges in pairs, a
// slot -1 unset, a dead pc or slot -1. A JS string indexes UTF-16 units, so
// at costs one prefix scan; the walk itself goes by codePointAt.
function re_exec(re, s, at, anchored) {
  const insts = [];
  for (let t = re.prog; t.$ === "Con"; t = t.tail) { insts.push(t.head); }
  const m = insts.length, ns = 2 * (1 + Number(re.ngroups)), sets = [];
  if (!(m < 16777215 && ns <= 8388608)) { throw "bend: a regex past the maximum size"; }
  const arg = (n, lim) => n < lim ? Number(n) : -1;
  const P = new Int32Array(3 * m);
  insts.forEach((h, i) => {
    let op = 10, a = 0, b = 0;
    switch (h.$) {
      case "IChr": op = 0; a = h.c | 0; break;
      case "IAny": op = 1; break;
      case "ISet":
        op = h.neg ? 3 : 2; a = sets.length >> 1;
        for (let r = h.rs; r.$ === "Con"; r = r.tail) { sets.push(r.head.fst, r.head.snd); }
        b = (sets.length >> 1) - a; break;
      case "ISplit": op = 4; a = arg(h.x, m); b = arg(h.y, m); break;
      case "IJmp": op = 5; a = arg(h.x, m); break;
      case "ISave": op = 6; a = arg(h.slot, ns); break;
      case "IBol": op = 7; a = h.multi ? 1 : 0; break;
      case "IEol": op = 8; a = h.multi ? 1 : 0; break;
      case "IWordB": op = 9; a = h.neg ? 1 : 0; break;
    }
    P[3 * i] = op; P[3 * i + 1] = a; P[3 * i + 2] = b;
  });
  const S = Int32Array.from(sets), V = new Int32Array(m);
  const RP = new Int32Array(m), RS = new Int32Array(m * ns);
  const CP = new Int32Array(m), CS = new Int32Array(m * ns);
  const CUR = new Int32Array(ns), BEST = new Int32Array(ns), STK = new Int32Array(2 * m + 2);
  const word = (c) => (c >= 48 && c <= 57) || (c >= 65 && c <= 90) || c === 95 || (c >= 97 && c <= 122);
  let i = 0, pos = 0, prev = -1;
  for (; at > 0n && i < s.length; at--, pos++) { prev = s.codePointAt(i); i += prev > 0xffff ? 2 : 1; }
  let nraw = 0, best = false;
  for (const at0 = pos; ; pos++) {
    const fresh = !best && (pos === at0 || !anchored) ? 1 : 0, gen = pos - at0 + 1;
    if (nraw + fresh === 0) { break; }
    const c = i < s.length ? s.codePointAt(i) : -1;
    i += c > 0xffff ? 2 : 1;
    let ncl = 0;
    for (let r = 0; r < nraw + fresh; r++) {
      if (r < nraw) { CUR.set(RS.subarray(r * ns, (r + 1) * ns)); } else { CUR.fill(-1); }
      let sp = 1;
      STK[0] = r < nraw ? RP[r] : 0;
      while (sp) {
        const x = STK[--sp];
        if (x < -1) { CUR[x & 0x7fffffff] = STK[--sp]; continue; }
        if (x < 0 || x >= m || V[x] === gen) { continue; }
        V[x] = gen;
        const op = P[3 * x], a = P[3 * x + 1], b = P[3 * x + 2];
        let go = false;
        if (op === 4) { STK[sp++] = b; STK[sp++] = a; }
        else if (op === 5) { STK[sp++] = a; }
        else if (op === 6) {
          if (a >= 0) { STK[sp++] = CUR[a]; STK[sp++] = a | -0x80000000; CUR[a] = pos; go = true; }
        }
        else if (op === 7) { go = pos === 0 || (a === 1 && prev === 10); }
        else if (op === 8) { go = c < 0 || (c === 10 && (a === 1 || i >= s.length)); }
        else if (op === 9) { go = (pos > 0 || s.length > 0) && (a === 1) !== (word(prev) !== word(c)); }
        else { CP[ncl] = x; CS.set(CUR, ncl++ * ns); }
        if (go) { STK[sp++] = x + 1; }
      }
    }
    nraw = 0;
    for (let t = 0; t < ncl; t++) {
      const x = CP[t], op = P[3 * x], a = P[3 * x + 1], b = P[3 * x + 2];
      if (op === 10) { BEST.set(CS.subarray(t * ns, (t + 1) * ns)); best = true; break; }
      let eat = op === 0 ? a === c : op === 1 ? c !== 10 : false;
      if (op === 2 || op === 3) {
        for (let j = a; j < a + b && !eat; j++) { eat = (S[2 * j] >>> 0) <= c && c <= (S[2 * j + 1] >>> 0); }
        eat = eat !== (op === 3);
      }
      if (eat && c >= 0) { RP[nraw] = x + 1; RS.set(CS.subarray(t * ns, (t + 1) * ns), nraw++ * ns); }
    }
    prev = c;
    if (c < 0) { break; }
  }
  if (!best || BEST[0] < 0 || BEST[1] < 0) { return {$: "None"}; }
  let gs = {$: "Nil"};
  for (let g = ns - 2; g >= 2; g -= 2) {
    const f = BEST[g] < 0 || BEST[g + 1] < 0 ? {$: "None"}
      : {$: "Some", value: {$: "Tuple", fst: BigInt(BEST[g]), snd: BigInt(BEST[g + 1])}};
    gs = {$: "Con", head: f, tail: gs};
  }
  return {$: "Some", value: {$: "Match", start: BigInt(BEST[0]), end: BigInt(BEST[1]), groups: gs}};
}
function str_hash(s) {
  let h = 2166136261;
  for (const c of s) {
    const x = c.codePointAt(0);
    for (let shift = 0; shift < 32; shift += 8) { h = Math.imul(h ^ ((x >>> shift) & 255), 16777619) >>> 0; }
  }
  return h;
}

function char_new(code) {
  if (code > 0x10FFFF || (code >= 0xD800 && code <= 0xDFFF)) {
    return {$: "RawChar", code: code};
  }
  return String.fromCodePoint(code);
}

// Array
// =====

function array_new(d, v) {
  if (d > 31n) {
    throw "bend: an array past the deepest block class 31";
  }
  return Array(2 ** Number(d)).fill(v);
}

// An unbalanced tree fails, as in C.
function array_node(a, b) {
  if (a.length !== b.length) {
    throw "bend: runtime fail-stop";
  }
  return a.concat(b);
}

function array_swap(a, i, v) {
  const at = i % a.length;
  const old = a[at];
  a[at] = v;
  return {$: "Tuple", fst: a, snd: old};
}

// Run
// ===

function run_jump(f, x) {
  return {$: "$JMP", f: f, x: x};
}

function run_tail(f, x) {
  return {$: "$JMP", f: f.j?.f === f ? f.j : f, x: [x]};
}

function run_clo(j) {
  const f = (x) => run_loop(j(x));
  f.j = j;
  j.f = f;
  return f;
}

function run_loop(r) {
  while (r !== null && typeof r === "object" && r.$ === "$JMP") {
    r = r.f(...r.x);
  }
  return r;
}

function run_lib(f, n) {
  return (...a) => a.length < n ? run_lib((...b) => f(...a, ...b), n - a.length)
    : run_loop(f(...a));
}
const $0eff = {
...(() => {
// IO
// ==

function io_print(text) {
  io_out(1, io_bytes(text + "\n"));
  return { $: "Unit" };
}

return {
  io_print: typeof io_print === "function" ? io_print : undefined,
  io_print_need: typeof io_print_need === "function" ? io_print_need : undefined,
};
})(),
};

// Program
// =======

function $main$() {
  const x_0 = {$: "U64", ["data"]: run_loop($Word$zero$(64n))};
  const a_0 = ((x_0 + 1n) & 0xFFFFFFFFFFFFFFFFn);
  return run_clo((x_1) => {
  const x_2 = run_loop($Nat$show$(run_loop($show$(a_0))));
  const x_3 = (x_2 + "\n");
  return run_jump($IO$bind$, [(x_4) => $IO$print$(("inc: " + x_3), x_4), run_clo((x_5) => {
  return (x_6) => $IO$print$("T1-END\n", x_6);
}), x_1]);
});
}

function $Word$zero$(n_0) {
  if (n_0 === 0n) {
    return {$: "WNil"};
  } else {
    const p_0 = (n_0 - 1n);
    return {$: "WCon", ["head"]: false, ["tail"]: run_loop($Word$zero$(p_0))};
  }
}

function $IO$bind$(m_0, f_0, k_0) {
  return run_tail(m_0, run_clo((x_0) => {
  return run_tail(f_0(x_0), k_0);
}));
}

function $Nat$show$(n_0) {
  const m_0 = n_0;
  return run_jump($Nat$show$fin$, [m_0, "", run_loop($Nat$show$put$(nat_divmod(m_0, 10n)))]);
}

function $show$(a_0) {
  const x_0 = a_0.data;
  return run_jump($Word$to_nat$, [64n, x_0]);
}

function $Nat$show$fin$(g_0, acc_0, dq_0) {
  const d_0 = dq_0.fst;
  const _t_0 = dq_0.snd;
  if (_t_0 === 0n) {
    return str_prepend(d_0, acc_0);
  } else {
    const p_0 = (_t_0 - 1n);
    return run_jump($Nat$show$go$, [g_0, nat_chk(p_0 + 1n), str_prepend(d_0, acc_0)]);
  }
}

function $Nat$show$put$(qr_0) {
  const q_0 = qr_0.fst;
  const r_0 = qr_0.snd;
  const x_0 = nat_chk(48n + r_0);
  return {$: "Tuple", ["fst"]: char_new(Number(x_0 & 0xFFFFFFFFn)), ["snd"]: q_0};
}

function $Word$to_nat$(n_0, w_0) {
  if (n_0 === 0n) {
    return 0n;
  } else {
    const p_0 = (n_0 - 1n);
    const _t_0 = w_0.head;
    if (!_t_0) {
      const t_0 = w_0.tail;
      const x_0 = run_loop($Word$to_nat$(p_0, t_0));
      return nat_chk(x_0 << 1n);
    } else {
      const t_1 = w_0.tail;
      const x_1 = run_loop($Word$to_nat$(p_0, t_1));
      return nat_chk(nat_chk(x_1 << 1n) + 1n);
    }
  }
}

function $Nat$show$go$(f_0, n_0, acc_0) {
  if (f_0 === 0n) {
    return acc_0;
  } else {
    const g_0 = (f_0 - 1n);
    return run_jump($Nat$show$fin$, [g_0, acc_0, run_loop($Nat$show$put$(nat_divmod(n_0, 10n)))]);
  }
}

function $IO$print$(text_0, k_0) {
  return { $: "$FFI", run: $0eff.io_print, need: $0eff.io_print_need, args: [text_0], kont: k_0 };
}

// Cli
// ===

// A JS program runs one thread and no GPU: --threads and --gpu do nothing.
let cli_args = [];

function cli(argv) {
  for (let i = 0; i < argv.length; i += 1) {
    if (argv[i] === "--") {
      cli_args.push(...argv.slice(i + 1));
      break;
    } else if (argv[i] === "--help") {
      io_out(1, io_bytes("usage: " + process.argv[1] + "\n"));
      process.exit(0);
    } else if (argv[i] === "--threads" || argv[i] === "--gpu") {
      i += 1;
    } else {
      cli_args.push(argv[i]);
    }
  }
}

// Show
// ====

// char_show: an escape, a \u{hex}, else the code point
function show_chr(c, q) {
  const k = { 10: "n", 9: "t", 13: "r", 0: "0", 92: "\\" }[c]
    ?? (c === q.codePointAt(0) ? q : null);
  return k !== null ? "\\" + k : c < 32 || c === 127
    || c > 0x10ffff || (c >= 0xd800 && c <= 0xdfff)
    ? "\\u{" + c.toString(16) + "}" : String.fromCodePoint(c);
}

// A pure main's value, spelled as term_show spells it: d is a node of
// the descriptor D over the names N (see show_main), v the value, chain
// the bracket of the [a, b] or (a, b) it continues, or 0.
function show_val(D, N, d, v, chain) {
  if (D[d] === 7) {
    const fs = Object.values(typeof v === "boolean"
      ? { $: v ? "True" : "False" } : v);
    let a = d + 3;
    for (; N[D[a]] !== fs[0]; a += 3 + 2 * D[a + 2]) {}
    let o = "{";
    let z = "}";
    if (fs[0] === "Con" || fs[0] === "Nil") {
      o = "[";
      z = "]";
    } else if (fs[0] === "Tuple") {
      o = "(";
      z = ")";
    }
    let s = o === "{" ? fs[0] + "{" : chain === o ? "" : o;
    for (const [j, f] of fs.slice(1).entries()) {
      if (o === "[" ? j === 0 && chain === o : j > 0) {
        s += ", ";
      }
      s += show_val(D, N, D[a + 4 + 2 * j], f, j === 1 && o !== "{" ? o : 0);
    }
    return o === "{" || chain !== o ? s + z : s;
  }
  return D[d] === 0 ? String(v)
    : D[d] === 1 ? f32_show(v).replace(/^-?\d+(?=e|$)/, "$&.0")
    : D[d] === 2 ? v + "n"
    : D[d] === 3 ? "'" + show_chr(char_code(v), "'") + "'"
    : D[d] === 4 ? "\"" + [...v].map((c) =>
      show_chr(c.codePointAt(0), "\"")).join("") + "\""
    : D[d] === 5 ? "{==}"
    : "[" + v.map((x) => show_val(D, N, D[d + 1], x, 0)).join(", ") + "]";
}

// Io
// ==

function io_exit(main, show) {
  try {
    if (show !== null) {
      io_out(1, io_bytes(show_val(...show, 0, run_loop(main()), 0) + "\n"));
      process.exit(0);
    }
    process.exit(io_run(main));
  } catch (e) {
    io_errs(String(e));
    process.exit(1);
  }
}

function io_out(fd, data) {
  const fs = require("fs");
  let at = 0;
  while (at < data.length) {
    try {
      at += fs.writeSync(fd, data, at, data.length - at);
    } catch (e) {
      if (e.code === "EAGAIN" || e.code === "EINTR") {
        continue;
      }
      try {
        fs.writeSync(2, "bend: a short write on a standard stream\n");
      } catch (o) {
      }
      process.exit(1);
    }
  }
}

function io_errs(message) {
  io_out(2, io_bytes(message + "\n"));
}

function io_sys() {
  if (globalThis.BEND_SYS === undefined) {
    const ffi = require("bun:ffi");
    const mac = process.platform === "darwin";
    const err = mac ? "__error" : "__errno_location";
    const T = { i: "i32", u: "u32", U: "u64", I: "i64", p: "ptr",
      c: "cstring" };
    // fcntl is variadic. Apple arm64 passes variadic arguments on the
    // stack, where the fixed convention puts arguments past the eighth, so
    // there the flags ride as a ninth argument; elsewhere in a register.
    const vari = mac && process.arch === "arm64";
    const lib = ffi.dlopen(mac ? "libSystem.dylib" : "libc.so.6",
      Object.fromEntries(("socket:iii>i bind:ipu>i listen:ii>i connect:ipu>i"
        + " accept:ipp>i send:ipUi>I recv:ipUi>I read:ipU>I pread:ipUI>I"
        + " sendto:ipUipu>I"
        + " recvfrom:ipUipp>I close:i>i poll:pui>i setsockopt:iiipu>i"
        + (vari ? " fcntl:iiiiiiiii>i" : " fcntl:iii>i") + " getsockopt:iiipp>i"
        + " strerror:i>c " + err + ":>p").split(" ").map((s) => {
        const [name, args, ret] = s.split(/[:>]/);
        return [name, { args: [...args].map((a) => T[a]), returns: T[ret] }];
      })));
    const fcntl = (fd, cmd, arg) => vari
      ? lib.symbols.fcntl(fd, cmd, 0, 0, 0, 0, 0, 0, arg)
      : lib.symbols.fcntl(fd, cmd, arg);
    globalThis.BEND_SYS = { ...lib.symbols, fcntl, ptr: ffi.ptr, mac,
      errno: () => ffi.read.i32(lib.symbols[err](), 0) };
  }
  return globalThis.BEND_SYS;
}

function io_fail(code) {
  const text = String(io_sys().strerror(code));
  return { $: "Fail", error: io_tup(code >>> 0, text) };
}

function io_done(value) {
  return { $: "Done", value };
}

function io_tup(...xs) {
  return xs.reduceRight((snd, fst) => ({ $: "Tuple", fst: fst, snd: snd }));
}

function io_bytes(text) {
  if (typeof text !== "string") { throw "bend: cannot encode a non-scalar Char as UTF-8"; }
  for (const c of text) {
    const code = c.codePointAt(0);
    if (code >= 0xd800 && code <= 0xdfff) { throw "bend: cannot encode a non-scalar Char as UTF-8"; }
  }
  return new TextEncoder().encode(text);
}

// One replacement per ill-formed byte, including truncated sequences; BOM
// is a normal U+FEFF element. Each IO chunk is decoded independently.
// Well-formed input takes the native decoder (fatal rejects exactly the
// ill-formed chunks; the byte walk below then keeps the per-byte contract).
function io_text(b, n) {
  try {
    return new TextDecoder("utf-8", { fatal: true, ignoreBOM: true }).decode(b.subarray(0, n));
  } catch (_) {}
  const out = [];
  for (let i = 0; i < n;) {
    const h = b[i];
    const k = h < 0x80 ? 1 : h >= 0xc2 && h <= 0xdf ? 2
      : h >= 0xe0 && h <= 0xef ? 3 : h >= 0xf0 && h <= 0xf4 ? 4 : 0;
    let c = k === 1 ? h : h & (0x7f >> k), ok = k > 0 && k <= n - i;
    for (let j = 1; ok && j < k; j++) {
      const t = b[i + j]; ok = (t & 0xc0) === 0x80; c = (c << 6) | (t & 63);
    }
    ok = ok && (k === 1 || c >= (k === 2 ? 0x80 : k === 3 ? 0x800 : 0x10000))
      && c <= 0x10ffff && !(c >= 0xd800 && c <= 0xdfff);
    out.push(String.fromCodePoint(ok ? c : 0xfffd));
    i += ok ? k : 1;
  }
  return out.join("");
}

function io_addr(host, port) {
  const part = host.split(".");
  const deci = (p) => /^(0|[1-9]\d{0,2})$/.test(p) && Number(p) < 256;
  if (port > 65535 || part.length !== 4 || !part.every(deci)) {
    return null;
  }
  const b = new Uint8Array(16);
  const head = io_sys().mac ? [16, 2] : [2, 0];
  b.set([...head, port >> 8, port & 255, ...part.map(Number)]);
  return b;
}

function io_push(fun, arg, fresh) {
  const io = globalThis.BEND_IO;
  io.runs.push({ fun: fun, arg: arg });
  io.live += fresh ? 1 : 0;
}

function io_wait(io) {
  const soon = io.waits.reduce((m, w) => Math.min(m, w.at ?? m), Infinity);
  let ms = -1;
  if (soon !== Infinity) {
    ms = Math.ceil(soon - performance.now());
    ms = Math.min(Math.max(0, ms), 2147483647);
  }
  const fds = io.waits.filter((w) => w.fd !== undefined);
  const buf = Int32Array.from(fds.flatMap((w) => [w.fd, w.out ? 4 : 1]));
  io_sys().poll(fds.length > 0 ? io_sys().ptr(buf) : null, fds.length, ms);
  const now = performance.now();
  const fire = io.waits.filter((w) =>
    (buf[2 * fds.indexOf(w) + 1] >>> 16) !== 0 || w.at <= now);
  io.waits = io.waits.filter((w) => !fire.includes(w));
  for (const w of fire) {
    io_push(io_wake, w, false);
  }
}

// A park's wake: more's value goes to k, or undefined, a re-park.
function io_wake(w) {
  const x = w.more();
  return x === undefined ? undefined : w.k(x);
}

// Parks the running effect until fd is readable (out false) or writable,
// or until at (a performance.now() tick; undefined for no deadline),
// whichever comes first.
function io_park_on(fd, out, k, more, at) {
  globalThis.BEND_IO.waits.push({ fd: fd, out: out, k: k, more: more, at: at });
}

function io_run(m) {
  const io = { runs: [], live: 0, waits: [] };
  globalThis.BEND_IO = io;
  try {
    io_push(run_loop(m()), (x) => ({ $: "Emit", value: x }), true);
    for (;;) {
      if (io.runs.length === 0) {
        if (io.live === 0) {
          return 0;
        }
        if (io.waits.length === 0) {
          io_errs("bend: deadlock: every computation waits on a channel");
          return 1;
        }
        io_wait(io);
        continue;
      }
      const s = io.runs.shift();
      let op = s.fun(s.arg);
      for (;;) {
        if (op === undefined) {
          break;
        }
        if (op.$ === "Emit") {
          io.live -= 1;
          break;
        }
        if (op.$ === "Halt") {
          io_errs(op.message);
          return op.code;
        }
        const need = op.need?.() ?? {};
        const fd = need.read ? op.args[0] : null;
        if (need.time || fd !== null) {
          const more = () => op.run(...op.args, op.kont);
          io.waits.push(fd === null
            ? { at: performance.now() + Number(op.args[0]), k: op.kont, more }
            : { fd: fd, k: op.kont, more });
          break;
        }
        const x = op.run(...op.args, op.kont);
        if (x === undefined) {
          break;
        }
        op = op.kont(x);
      }
    }
  } catch (req) {
    if (req instanceof RangeError) {
      throw "bend: memory fault (machine stack overflow?)";
    }
    if (req?.$ !== "$FFI") {
      throw req;
    }
    io_errs("bend: runtime fail-stop");
    return 1;
  }
}

// Chan
// ====

function chan_wake(row, x) {
  const w = row.wait.shift();
  io_push(w.cont, x, false);
  return w.item;
}

function chan_take(row) {
  const v = row.ring.shift();
  if (row.wait.length > 0) {
    row.ring.push(chan_wake(row, true));
  }
  return v;
}

// A handle is the row (a stale copy keeps it, shut).
function chan_shut(row) {
  row.shut = true;
  while (row.wait.length > 0) {
    chan_wake(row, row.wait[0].item === null ? { $: "None" } : false);
  }
}

cli(process.argv.slice(2));
io_exit($main$, null);