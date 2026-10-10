// Run the four tests/wgsl programs on the GPU and compare with their expected outputs.
//   deno run --unstable-webgpu -A tests/wgsl/run.mjs
// Each program is emitted by `bun bend2/main.ts x.bend -o x.wgsl` (the WGSL lane needs the source main.ts).
import { gpu_open, pipes, fork_run, entry_run } from "../../bend2/webgpu.js";

const root = new URL("../../", import.meta.url).pathname;
const tmp = Deno.makeTempDirSync();
const emit = async (name) => {
  const out = `${tmp}/${name}.wgsl`;
  const r = await new Deno.Command("bun", { args: ["bend2/main.ts", `tests/wgsl/${name}.bend`, "-o", out], cwd: root }).output();
  if (!r.success) throw new Error(`emit ${name}: ${new TextDecoder().decode(r.stderr)}`);
  return Deno.readTextFileSync(out);
};
const expect = (name) => Deno.readTextFileSync(`${root}tests/wgsl/${name}.bend`).split("\n")
  .filter((l) => l.startsWith("#|")).map((l) => l.slice(2).trim());

const g = await gpu_open();
let bad = 0;
const check = (what, got, want) => {
  const ok = String(got) === String(want);
  if (!ok) bad++;
  console.log(`${ok ? "ok  " : "FAIL"} ${what}: got ${got}${ok ? "" : `, want ${want}`}`);
};

// the fork programs: the host run prints the value the `#|` line holds
const lcg = (s) => (Math.imul(s, 1664525) + 1013904223) >>> 0;
const bytes64 = new Uint8Array(64);
for (let i = 0, s = 12345; i < 64; i++) { s = lcg(s); bytes64[i] = s >>> 24; }
const forks = [
  ["spin_collatz", [10, 0], {}],
  ["spec_tree", [8, 0], {}],
  ["bytes_hash", [4, bytes64, 0], { 1: bytes64 }],
];
for (const [name, args, bufs] of forks) {
  const r = await fork_run(g, await emit(name), args, bufs);
  check(name, r.value, expect(name).at(-1));
}

// cubes and the map: the inputs are the program's own generators (xval)
const f32 = Math.fround, f32bits = (v) => new Uint32Array(new Float32Array([v]).buffer)[0];
const SCALE = new Float32Array(new Uint32Array([864026624]).buffer)[0];
const xval = (r, i, salt) => {
  const u = lcg(lcg((Math.imul(r, 4099) + i + salt) >>> 0));
  return f32(f32(f32(f32(u >>> 8) * SCALE) * 2) - 1);
};
const mat = (rows, len, salt) => Float32Array.from({ length: rows * len }, (_, k) => xval(Math.floor(k / len), k % len, salt));
const wb = new Uint8Array(7 * 136), dv = new DataView(wb.buffer);
for (let r = 0; r < 7; r++) for (let i = 0; i < 32; i++) dv.setFloat32(r * 136 + 2 + i * 4, xval(r, i, 4), true);

const ps = await pipes(g, await emit("cubes"));
const run = (name, kind, io) => entry_run(g, ps.by(kind, name), io).then((r) => [...r.bits]);
const ctr = await run("ctr", "cube", { rows: 8, in: { x: mat(8, 128, 1) } });
const amax = await run("amax", "cube", { rows: 7, in: { x: mat(7, 256, 2) } });
const padsq = await run("padsq", "cube", { rows: 7, in: { x: mat(7, 50, 3) } });
const bdot = await run("bdot", "cube", { rows: 7, in: { wb, x: Float32Array.from({ length: 32 }, (_, i) => xval(0, i, 5)) } });
const clamp = await run("clamp", "map", { len: 300, in: { v: mat(1, 300, 6) }, sc: { hi: 0.5 } });
const got = [...ctr];
for (let r = 0; r < 7; r++) got.push(amax[r], padsq[r], bdot[r]);
got.push(...clamp);
const want = Deno.readTextFileSync(`${root}tests/wgsl/cubes.expected`).trim().split("\n").map(Number);
let first = -1;
want.forEach((w, k) => { if (first < 0 && got[k] !== w) first = k; });
check(`cubes (${want.length} words)`, first < 0 && got.length === want.length ? "all equal" : `differs at ${first} (len ${got.length})`, "all equal");
Deno.exit(bad ? 1 : 0);
