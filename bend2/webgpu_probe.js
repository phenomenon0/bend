// Load-time adapter smoke test for wgsl.ts's integer IEEE arithmetic and arithmetic barriers.
// No global device state, no gpu_open changes. This is a bounded probe, not
// exhaustive arithmetic certification; the caller decides the fallback policy.
// The WGSL helpers below are a pinned copy of the ones wgsl.ts emits (x32a.ts, x32w.ts).
const INTEGER_WGSL = String.raw`
fn x32d_pack(sg: u32, q: u32, sticky: bool, e: i32) -> u32 {
  let eb = e + 25 + 127;
  if (eb >= 255) {
    return 0x7f800000u | sg;
  }
  let sh = select(3 - eb, 2, eb >= 1);
  if (sh > 26) {
    return sg;
  }
  let s = u32(sh);
  let kept = q >> s;
  let rem = q & ((1u << s) - 1u);
  let hf = 1u << (s - 1u);
  let up = rem > hf || (rem == hf && (sticky || (kept & 1u) == 1u));
  var b = kept + select(0u, 1u, up);
  if (eb >= 1) {
    b += u32(eb - 1) << 23u;
  }
  return b | sg;
}

fn x32d_norm(a: u32) -> vec2<u32> {
  if (a >= 0x800000u) {
    return vec2<u32>((a & 0x7fffffu) | 0x800000u, bitcast<u32>(i32(a >> 23u) - 150));
  }
  let z = countLeadingZeros(a) - 8u;
  return vec2<u32>(a << z, bitcast<u32>(-149 - i32(z)));
}

fn x32w_m32(a: u32, b: u32) -> vec2<u32> {
  let a0 = a & 0xFFFFu;
  let a1 = a >> 16u;
  let b0 = b & 0xFFFFu;
  let b1 = b >> 16u;
  let p00 = a0 * b0;
  let p01 = a0 * b1;
  let p10 = a1 * b0;
  let p11 = a1 * b1;
  let mid = p01 + (p00 >> 16u) + (p10 & 0xFFFFu);
  return vec2<u32>(p11 + (mid >> 16u) + (p10 >> 16u), (mid << 16u) | (p00 & 0xFFFFu));
}

fn x32a_jam(x: u32, d: u32) -> u32 {
  if (d == 0u) { return x; }
  if (d >= 32u) { return select(0u, 1u, x != 0u); }
  return (x >> d) | select(0u, 1u, (x & ((1u << d) - 1u)) != 0u);
}

fn x32a_nan(a: u32, b: u32) -> u32 {
  let aa = a & 0x7fffffffu;
  let ab = b & 0x7fffffffu;
  if (aa > 0x7f800000u && (a & 0x400000u) == 0u) { return a | 0x400000u; }
  if (ab > 0x7f800000u && (b & 0x400000u) == 0u) { return b | 0x400000u; }
  if (aa > 0x7f800000u) { return a | 0x400000u; }
  return b | 0x400000u;
}

fn x32a_add_bits(ua: u32, ub: u32) -> u32 {
  let aa = ua & 0x7fffffffu;
  let ab = ub & 0x7fffffffu;
  if (aa > 0x7f800000u || ab > 0x7f800000u) { return x32a_nan(ua, ub); }
  if (aa == 0x7f800000u) {
    if (ab == aa && ua != ub) { return 0x7fc00000u; }
    return ua;
  }
  if (ab == 0x7f800000u) { return ub; }
  if (aa == 0u && ab == 0u) { return (ua & ub) & 0x80000000u; }
  if (aa == 0u) { return ub; }
  if (ab == 0u) { return ua; }
  // Keep the greater magnitude on the left, so cancellation has its sign.
  let a = select(ub, ua, aa >= ab);
  let b = select(ua, ub, aa >= ab);
  let na = x32d_norm(a & 0x7fffffffu);
  let nb = x32d_norm(b & 0x7fffffffu);
  var e = bitcast<i32>(na.y) - 3;
  let delta = u32(bitcast<i32>(na.y) - bitcast<i32>(nb.y));
  let ma = na.x << 3u;
  let mb = x32a_jam(nb.x << 3u, delta);
  var m = 0u;
  if (((a ^ b) & 0x80000000u) == 0u) {
    m = ma + mb;
    if ((m & 0x8000000u) != 0u) { m = x32a_jam(m, 1u); e += 1; }
  } else {
    m = ma - mb;
    if (m == 0u) { return 0u; }
    let shift = countLeadingZeros(m) - 5u;
    m = m << shift;
    e -= i32(shift);
  }
  return x32d_pack(a & 0x80000000u, m >> 1u, (m & 1u) != 0u, e + 1);
}

fn x32a_mul_bits(ua: u32, ub: u32) -> u32 {
  let aa = ua & 0x7fffffffu;
  let ab = ub & 0x7fffffffu;
  let sign = (ua ^ ub) & 0x80000000u;
  if (aa > 0x7f800000u || ab > 0x7f800000u) { return x32a_nan(ua, ub); }
  if (aa == 0x7f800000u || ab == 0x7f800000u) {
    if (aa == 0u || ab == 0u) { return 0x7fc00000u; }
    return sign | 0x7f800000u;
  }
  if (aa == 0u || ab == 0u) { return sign; }
  let na = x32d_norm(aa);
  let nb = x32d_norm(ab);
  let p = x32w_m32(na.x, nb.x);
  // A 48-bit product, bit 46 or 47 set. Keep 26 bits and a sticky tail.
  let shift = select(21u, 22u, (p.x & 0x8000u) != 0u);
  let q = (p.x << (32u - shift)) | (p.y >> shift);
  let tail = (p.y & ((1u << shift) - 1u)) != 0u;
  return x32d_pack(sign, q, tail, bitcast<i32>(na.y) + bitcast<i32>(nb.y) + i32(shift));
}

fn x32_add(a: f32, b: f32) -> f32 {
  return bitcast<f32>(x32a_add_bits(bitcast<u32>(a), bitcast<u32>(b)));
}

fn x32_sub(a: f32, b: f32) -> f32 {
  let ua = bitcast<u32>(a);
  let ub = bitcast<u32>(b);
  if ((ua & 0x7fffffffu) > 0x7f800000u || (ub & 0x7fffffffu) > 0x7f800000u) {
    return bitcast<f32>(x32a_nan(ua, ub));
  }
  return bitcast<f32>(x32a_add_bits(ua, ub ^ 0x80000000u));
}

fn x32_mul(a: f32, b: f32) -> f32 {
  return bitcast<f32>(x32a_mul_bits(bitcast<u32>(a), bitcast<u32>(b)));
}

fn fisnan(x: f32) -> bool {
  return (bitcast<u32>(x) & 0x7fffffffu) > 0x7f800000u;
}

fn fne(a: f32, b: f32) -> bool {
  return fisnan(a) || fisnan(b) || a != b;
}

fn bmul(a: f32, b: f32) -> f32 {
  let q = fma(a, b, -0.0);
  return select(q, bitcast<f32>((bitcast<u32>(a) ^ bitcast<u32>(b)) & 0x80000000u),
    q == 0.0);
}
`;

const f = Math.fround;
const word = new Uint32Array(1), float = new Float32Array(word.buffer);
const bits = (x) => { float[0] = x; return word[0]; };
const value = (x) => { word[0] = x; return float[0]; };
const hex = (x) => `0x${x.toString(16).padStart(8, "0")}`;

// Inputs travel as storage bits: the shader compiler cannot constant-fold rows.
// Finite references use JS binary64 then explicit f32 rounding at every edge.
export function gpu_probe_cases() {
  const rows = [];
  const add = (probe, op, a, b, c, d, want) => rows.push({ probe, op, input: [a, b, c, d], want: want >>> 0 });
  const numbers = (probe, op, a, b, c, d, want) => add(probe, op, ...[a, b, c, d].map(bits), bits(want));
  let seed = 99991;
  const xs = (x) => { x ^= x << 13; x ^= x >>> 17; x ^= x << 5; return x >>> 0; };
  const rnd = () => { seed = xs(seed); return ((seed >>> 8) / 16777216) * 2 - 1; };
  // P2's seed and expression, shortened from 65536 to 256 tuples.
  for (let i = 0; i < 256; i++) {
    const a = f(rnd() * 2 ** ((xs(seed ^ 1) % 20) - 10));
    const b = f(rnd() * 2 ** ((xs(seed ^ 3) % 20) - 10));
    const c = f(rnd() * 2 ** ((xs(seed ^ 5) % 20) - 10));
    const want = f(f(a * b) + c);
    numbers("fma/barrier", 0, a, b, c, 0, want);
    numbers("fma/integer", 3, a, b, c, 0, want);
  }
  const vals = [0, -0, 1, -1, 1e30, -1e30, 16777216, 1.0000001].map(f);
  for (const a of vals) for (const b of vals) for (const c of [1, -1, -0]) {
    const d = f(0.1), want = f(f(f(a + b) + f(c + d)) + a);
    numbers("assoc/barrier", 1, a, b, c, d, want);
    numbers("assoc/integer", 4, a, b, c, d, want);
  }
  for (const a of [0, -0, 1, -1, 3.5, -2.25]) for (const b of [0, -0, 1, -1]) {
    numbers("zsign/barrier", 2, a, b, 0, 0, f(a * b));
    numbers("zsign/integer", 5, a, b, 0, 0, f(a * b));
  }
  // Near-underflow cancellation, subnormal operands/results, ties to even,
  // signed zeros, normal boundaries, and one overflow (all non-NaN inputs).
  const pairs = [
    [0x00800001, 0x00800000], [0x00800000, 0x3f7ffffe],
    [0x00800000, 0x3f000000], [0x00800000, 0xbf000000],
    [1, 1], [1, 0x3f000000], [3, 0x3f000000], [5, 0x3f000000],
    [0x007fffff, 1], [0x807fffff, 0x80000001],
    [0x00800001, 0x80800000], [0x80800001, 0x00800000],
    [0x80000001, 0x3f800000], [0, 0x80000000], [0x80000000, 0x80000000],
    [0x00800000, 0x33800000], [0x3f800001, 0x33800000], [0x7f7fffff, 0x40000000],
  ];
  for (const [a, b] of pairs) {
    add("underflow/add", 6, a, b, 0, 0, bits(f(value(a) + value(b))));
    add("underflow/sub", 7, a, b, 0, 0, bits(f(value(a) - value(b))));
    add("underflow/mul", 8, a, b, 0, 0, bits(f(value(a) * value(b))));
  }
  for (const a of [0, 0x80000000, 1, 0x3f800000, 0x7f800000, 0xff800000,
    0x7fc00000, 0xffc12345, 0x7f800001, 0xff800001]) {
    add("nan/x!=x", 9, a, 0, 0, 0, (a & 0x7fffffff) > 0x7f800000 ? 1 : 0);
  }
  return rows;
}

// The alternate source is a real negative control: replace production barriers
// and integer arithmetic with hardware expressions; expected bytes stay fixed.
export function gpu_probe_source(variant = "exact") {
  if (!["exact", "barrier-free"].includes(variant)) throw new Error("unknown probe variant");
  const expressions = variant === "exact" ? [
    "fma(1.0, bmul(a, b), c)",
    "fma(1.0, fma(1.0, fma(1.0, a, b), fma(1.0, c, d)), a)",
    "bmul(a, b)", "x32_add(x32_mul(a, b), c)",
    "x32_add(x32_add(x32_add(a, b), x32_add(c, d)), a)",
    "x32_mul(a, b)", "x32_add(a, b)", "x32_sub(a, b)", "x32_mul(a, b)",
    "select(0u, 1u, fne(a, a))",
  ] : ["a * b + c", "((a + b) + (c + d)) + a", "a * b", "a * b + c",
    "((a + b) + (c + d)) + a", "a * b", "a + b", "a - b", "a * b", "select(0u, 1u, a != a)"];
  return `${INTEGER_WGSL}
@group(0) @binding(0) var<storage, read> input: array<u32>;
@group(0) @binding(1) var<storage, read_write> output: array<u32>;
@compute @workgroup_size(64)
fn probe(@builtin(global_invocation_id) gid: vec3<u32>) {
  let i = gid.x;
  if (i >= arrayLength(&output)) { return; }
  let at = i * 5u;
  let a = bitcast<f32>(input[at + 1u]); let b = bitcast<f32>(input[at + 2u]);
  let c = bitcast<f32>(input[at + 3u]); let d = bitcast<f32>(input[at + 4u]);
  switch input[at] {
    ${expressions.map((e, i) => `case ${i}u: { output[i] = ${i === 9 ? e : `bitcast<u32>(${e})`}; }`).join("\n    ")}
    default: { output[i] = 0xdeadbeefu; }
  }
}`;
}

export function gpu_probe_check(got, rows = gpu_probe_cases()) {
  if (!(got instanceof Uint32Array) || got.length !== rows.length) {
    return { exact: false, fails: [{ probe: "readback", error: `expected ${rows.length} words, got ${got?.length ?? "no words"}` }] };
  }
  const fails = [], probes = {};
  let mismatches = 0;
  rows.forEach((row, i) => {
    const probe = probes[row.probe] ??= { checks: 0, mismatches: 0 };
    probe.checks++;
    if (got[i] !== row.want) {
      mismatches++; probe.mismatches++;
      if (fails.length < 64) fails.push({ probe: row.probe, row: i, got: hex(got[i]), want: hex(row.want) });
    }
  });
  return { exact: mismatches === 0, fails, mismatches, checks: rows.length, probes };
}

// Call on a freshly opened device, before other users push device error scopes.
// No successful result is cached: device loss/reopen requires a new call.
// source is a lane-test hook; production callers use gpu_selftest(g) unchanged.
export async function gpu_selftest(g, { source = gpu_probe_source(), timeoutMs = 10000 } = {}) {
  const started = performance.now(), d = g?.device, buffers = [];
  let timer, scopes = 0, cancelled = false;
  const active = () => { if (cancelled) throw new Error("self-test cancelled"); };
  const fail = (error) => ({ exact: false, fails: [{ probe: "device", error: String(error?.message ?? error) }] });
  if (!d) return fail("no GPUDevice");
  if (!Number.isFinite(timeoutMs) || timeoutMs <= 0) return fail("invalid timeoutMs");
  const run = async () => {
    for (const kind of ["internal", "out-of-memory", "validation"]) { d.pushErrorScope(kind); scopes++; }
    const rows = gpu_probe_cases(), input = Uint32Array.from(rows.flatMap((r) => [r.op, ...r.input]));
    const mk = (size, usage) => { const b = d.createBuffer({ size, usage }); buffers.push(b); return b; };
    const ib = mk(input.byteLength, GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST);
    const ob = mk(rows.length * 4, GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_SRC | GPUBufferUsage.COPY_DST);
    const rb = mk(rows.length * 4, GPUBufferUsage.MAP_READ | GPUBufferUsage.COPY_DST);
    d.queue.writeBuffer(ib, 0, input);
    d.queue.writeBuffer(ob, 0, new Uint32Array(rows.length).fill(0xa5a5a5a5));
    const t0 = performance.now();
    const module = d.createShaderModule({ code: source, label: "bend exactness probe" });
    const info = await module.getCompilationInfo();
    active();
    const errors = info.messages.filter((m) => m.type === "error");
    if (errors.length) throw new Error(errors.map((m) => `${m.lineNum}:${m.linePos} ${m.message}`).join("; "));
    const pipe = await d.createComputePipelineAsync({ layout: "auto", compute: { module, entryPoint: "probe" } });
    active();
    const compile_ms = performance.now() - t0;
    const bg = d.createBindGroup({ layout: pipe.getBindGroupLayout(0), entries: [
      { binding: 0, resource: { buffer: ib } }, { binding: 1, resource: { buffer: ob } },
    ] });
    const enc = d.createCommandEncoder(), pass = enc.beginComputePass();
    pass.setPipeline(pipe); pass.setBindGroup(0, bg); pass.dispatchWorkgroups(Math.ceil(rows.length / 64)); pass.end();
    enc.copyBufferToBuffer(ob, 0, rb, 0, rows.length * 4);
    const command = enc.finish(), t1 = performance.now();
    d.queue.submit([command]);
    await rb.mapAsync(GPUMapMode.READ);
    const submit_readback_ms = performance.now() - t1;
    const got = new Uint32Array(rb.getMappedRange().slice(0)); rb.unmap();
    return { ...gpu_probe_check(got, rows), compile_ms, submit_readback_ms };
  };
  let cleanupPromise;
  const cleanup = () => {
    if (cleanupPromise) return cleanupPromise;
    const errors = [], pending = [];
    for (const b of buffers) {
      try { b.destroy(); } catch (error) { errors.push(String(error)); }
    }
    // Pop every scope synchronously; waiting for a driver's promises must not
    // strand later scopes or prevent a timeout from returning the fallback.
    while (scopes > 0) {
      scopes--;
      try {
        pending.push(Promise.resolve(d.popErrorScope()).then(
          (error) => { if (error) errors.push(error.message); },
          (error) => { errors.push(String(error)); }));
      } catch (error) { errors.push(String(error)); }
    }
    cleanupPromise = Promise.all(pending).then(() => errors);
    return cleanupPromise;
  };
  const work = async () => {
    let result;
    try { result = await run(); } catch (error) { result = fail(error); }
    for (const error of await cleanup()) {
      result.exact = false; result.fails.push({ probe: "validation", error });
    }
    return result;
  };
  let result;
  try {
    const timeout = new Promise((_, reject) => { timer = setTimeout(() => reject(new Error("self-test timeout")), timeoutMs); });
    const lost = d.lost.then((info) => { throw new Error(`device lost: ${info.message}`); });
    // Cleanup is inside the deadline, including asynchronous error scopes.
    result = await Promise.race([work(), timeout, lost]);
  } catch (error) { result = fail(error); }
  finally {
    cancelled = true;
    clearTimeout(timer);
    // Idempotent; also observes late scope rejections if the device timed out.
    void cleanup();
  }
  return { ...result, elapsed_ms: performance.now() - started };
}
