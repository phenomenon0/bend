#!/usr/bin/env python3
"""Exercise emitted runtime ownership/IO with allocation tracking and sanitizers."""
import json
import os
from pathlib import Path
import random
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent


def run(args, **kw):
    return subprocess.run(args, cwd=ROOT, check=True, text=True, timeout=120, **kw)


def decode(data):
    """Independent oracle: try complete strict single-scalar UTF-8 prefixes."""
    out, i = [], 0
    while i < len(data):
        for n in range(1, min(4, len(data) - i) + 1):
            try:
                scalar = data[i:i+n].decode("utf-8", errors="strict")
            except UnicodeDecodeError:
                continue
            if len(scalar) == 1:
                out.append(ord(scalar))
                i += n
                break
        else:
            out.append(0xfffd)
            i += 1
    return out


TRACK = r'''
#include <assert.h>
#define TRACK_SIZE (1u << 18)
static struct { Loc loc; Cls cls; bool live; } tracked[TRACK_SIZE];
static u64 track_live, track_bytes, track_allocs, track_payload_words;
static u64 track_peak_live, track_copy_cells;
static u64 track_str_reads, track_kmp_builds, track_kmp_live;
static int track_fail_after = -1;
static u32 track_slot(Loc l) {
  u32 i = (u32)(l * 11400714819323198485ull >> 46);
  while (tracked[i].loc && tracked[i].loc != l) { i = (i + 1) & (TRACK_SIZE - 1); }
  return i;
}
INLINE Loc heap_alloc(Env e, Cls cls) {
  if (track_fail_after == 0) { a32_store(a32_at(e.mem, H_ERROR_CODE), ERR_HEAP); return 0; }
  if (track_fail_after > 0) { track_fail_after--; }
  Loc l = heap_alloc_impl(e, cls);
  if (!err_seen(e.mem)) {
    u32 i = track_slot(l);
    assert(!tracked[i].live);
    tracked[i].loc = l; tracked[i].cls = cls; tracked[i].live = true;
    track_live++; track_bytes += 8ull << cls; track_allocs++;
    if (track_live > track_peak_live) { track_peak_live = track_live; }
  }
  return l;
}
'''
FREE = r'''
INLINE void heap_free(Env e, Cls cls, Loc l) {
  if (!err_seen(e.mem)) {
    u32 i = track_slot(l);
    assert(tracked[i].live && tracked[i].cls == cls);
    tracked[i].live = false;
    track_live--; track_bytes -= 8ull << cls;
  }
  heap_free_impl(e, cls, l);
}
'''

rng = random.Random(0xB3D)
cases = [b"", b"\xef\xbb\xbfA\0\xf0\x9f\x98\x80", b"\xe2\x82",
         b"\xc0\x80\xed\xa0\x80\xf4\x90\x80\x80",
         "\x7f\u0080\u07ff\u0800\ud7ff\ue000\uffff\U00010000\U0010ffff".encode()]
cases += [bytes([b]) for b in range(256)]
cases += [rng.randbytes(rng.randrange(1, 33)) for _ in range(256)]
# Python's scalar-string operations are independent oracles for JS's bulk
# UTF-16 paths. Deliberately include NUL, supplementary and non-ASCII spaces.
texts = ["", "aaaaa", "ababa", "a😀a😀", "\0a\0", "\r\n\n", "é\u0085\u2028"]
texts += ["".join(rng.choices("ab😀é\0\r\n\v\f\x1c\u0085\u2028", k=rng.randrange(20))) for _ in range(250)]
js_cases = []
for s in texts:
    for p in ["", "a", "aa", "aba", "😀", "\0", "\r\n"]:
        r = "$&a😀"
        h = 2166136261
        for ch in s:
            for byte in ord(ch).to_bytes(4, "little"):
                h = ((h ^ byte) * 16777619) & 0xffffffff
        js_cases.append([s, p, r, s.find(p), s.rfind(p), s.count(p), s.replace(p, r),
                         s.split(p) if p else [s], list(s.partition(p)) if p else [s, "", ""],
                         s.splitlines(), h])
with tempfile.TemporaryDirectory(prefix="bend-strings-runtime-") as temp:
    tmp = Path(temp)
    seed = tmp / "seed.bend"
    # An IO seed (never run; its one literal stays the probe's static image),
    # so the emitted runtimes carry the File.read_text effect.
    seed.write_text('import Base\n\n'
                    'def done(r: File & Result<&1, &1, U32 & String, Utf8.Dec & String>) -> IO(Unit):\n'
                    '  (f, x) = r\n  File.close(f)\n\n'
                    'def go(+s: String) -> IO(Unit):\n  do IO<Unit>:\n'
                    '    f : File <- IO.try(File, File.open(s, s))\n'
                    '    r : File & Result<&1, &1, U32 & String, Utf8.Dec & String> <-\n'
                    '      File.read_text(f, Utf8.Dec.new(), 1)\n'
                    '    done(r)\n\n'
                    'def main() -> IO(Unit):\n  go("abcdef")\n')
    cfile, jsfile = tmp / "runtime.c", tmp / "runtime.js"
    run(["bun", "bend2/main.ts", str(seed), "-o", str(cfile), "-o", str(jsfile)])
    c = cfile.read_text().replace("int main(int argc, char** argv)", "int bend_main(int argc, char** argv)")
    # Host err_post exits; injected allocation failures instead emulate the
    # device's sticky error state, so late writes into failed storage are visible.
    c = c.replace("(DEVICE && a32_load(a32_at(H, H_ERROR_CODE)) != 0)",
                  "(a32_load(a32_at(H, H_ERROR_CODE)) != 0)")
    c = c.replace("INLINE Loc heap_alloc(Env e, Cls cls)", "INLINE Loc heap_alloc_impl(Env e, Cls cls)")
    c = c.replace("INLINE void heap_free(Env e, Cls cls, Loc loc)", TRACK + "\nINLINE void heap_free_impl(Env e, Cls cls, Loc loc)")
    c = c.replace("// Spare\n// =====", FREE + "\n// Spare\n// =====")
    c = c.replace("Loc l = heap_alloc(e, buf_wcls(c));", "track_payload_words += 1ull << buf_wcls(c);\n  Loc l = heap_alloc(e, buf_wcls(c));")
    c = c.replace("INLINE u32 str_at_peek(Env e, StrParts p, u32 i) {",
                  "INLINE u32 str_at_peek(Env e, StrParts p, u32 i) { track_str_reads++;")
    c = c.replace("INLINE void str_copy_cells(Env e, StrParts dst, u32 at, StrParts src) {",
                  "INLINE void str_copy_cells(Env e, StrParts dst, u32 at, StrParts src) { track_copy_cells += src.len;")
    c = c.replace("k.table = table;", "k.table = table; track_kmp_builds++; track_kmp_live++;")
    c = c.replace("k->table = 0;", "track_kmp_live--; k->table = 0;")
    # Scratch is reclaimed even with a sticky error; account for its direct
    # local recycling, which deliberately bypasses heap_free's error guard.
    scratch = "e.mem[l] = ALC_AT(e, cls);"
    assert c.count(scratch) == 1, "str_scratch_free hook moved"
    c = c.replace(scratch, """
    u32 slot = track_slot(l);
    assert(tracked[slot].live && tracked[slot].cls == cls);
    tracked[slot].live = false; track_live--; track_bytes -= 8ull << cls;
    e.mem[l] = ALC_AT(e, cls);""")
    tests = ["static void utf8_cases(Env e) {"]
    for data in cases:
        expected = decode(data)
        raw = ",".join(str(x) for x in data) or "0"
        want = ",".join(str(x) for x in expected) or "0"
        tests += [f"{{ const unsigned char b[] = {{{raw}}}; const u32 want[] = {{{want}}};",
                  f"Term s = io_str(e, (const char*)b, {len(data)}); StrParts p = str_peek(e, s);",
                  f"assert(p.len == {len(expected)});",
                  "for (u32 i = 0; i < p.len; i++) { assert(str_at_peek(e, p, i) == want[i]); }",
                  "term_sink(e, s); assert(track_live == 0); }"]
    tests.append("}")
    cfile.write_text(c + "\n" + "\n".join(tests) + "\n" + (HERE / "runtime.c").read_text())
    binary = tmp / "probe"
    flags = ["-O1", "-g", "-fsanitize=address,undefined", "-fno-omit-frame-pointer"]
    run([os.environ.get("CC", "clang"), "-std=c11", *flags, str(cfile), "-lpthread", "-lm", "-o", str(binary)])
    run([str(binary)], env={**os.environ, "ASAN_OPTIONS": "detect_leaks=0"})
    faults = 0
    fault_ops = dict.fromkeys(["repeat", "prepend", "append", "copy", "transform",
                              "split", "from-list", "join"], 4)
    fault_ops.update(slice=2, find=2, count=1, replace=5, split_on=9, partition=8,
                     splitlines=12, pad=4, decode=8)
    for op, allocations in fault_ops.items():
        for offset in range(allocations):
            run([str(binary), "fault-" + op, str(offset)], capture_output=True,
                env={**os.environ, "ASAN_OPTIONS": "detect_leaks=0"})
            faults += 1
    print(f"Device-style allocation failures: ok ({faults} injected cases)", flush=True)
    fail = subprocess.run([str(binary), "raw-output"], cwd=ROOT, text=True, capture_output=True)
    assert fail.returncode and fail.stderr == "bend: cannot encode a non-scalar Char as UTF-8\n", fail
    for mode in ["limit-pad", "limit-repeat"]:
        fail = subprocess.run([str(binary), mode], cwd=ROOT, text=True, capture_output=True)
        assert fail.returncode and fail.stderr == "bend: a string past the maximum length 2^31\n", fail
    js = jsfile.read_text().split("\ncli(process.argv.slice(2));")[0]
    js += "\nconst cases = " + json.dumps([[list(b), decode(b)] for b in cases]) + ";\n"
    js += "\nconst textCases = " + json.dumps(js_cases) + ";\n"
    js += r'''
for (const [bytes, want] of cases) {
  const got = [...io_text(new Uint8Array(bytes), bytes.length)].map(c => c.codePointAt(0));
  if (JSON.stringify(got) !== JSON.stringify(want)) { throw new Error(JSON.stringify({bytes, got, want})); }
}
try { io_bytes("\ud800"); throw new Error("accepted raw output"); }
catch (e) { if (e !== "bend: cannot encode a non-scalar Char as UTF-8") { throw e; } }
for (const build of [() => str_prepend(char_new(0xd800), ""),
  () => str_from_list({$: "Con", head: char_new(0xffffffff), tail: {$: "Nil"}}),
  () => str_pad("a", 2n, char_new(0xd800), 0),
  () => str_pad("", 1n, char_new(0xffffffff), 1)]) {
  try { build(); throw new Error("accepted raw string"); }
  catch (e) { if (e !== "bend: JS strings cannot contain non-scalar Char values") { throw e; } }
}
console.log("JS UTF-8: ok (" + cases.length + " byte vectors)");
function unpack(xs) { const out = []; for (; xs.$ === "Con"; xs = xs.tail) { out.push(xs.head); } return out; }
function index(m) { return m.$ === "None" ? -1 : Number(m.value); }
for (const [s, p, r, ...want] of textCases) {
  const part = str_partition(s, p);
  const got = [index(str_find(s, p, false)), index(str_find(s, p, true)), Number(str_count(s, p)),
    str_replace(s, p, r), p === "" ? [s] : s.split(p), [part.fst, part.snd.fst, part.snd.snd],
    unpack(str_splitlines(s)), str_hash(s)];
  if (JSON.stringify(got) !== JSON.stringify(want)) { throw new Error(JSON.stringify({s, p, got, want})); }
}
const adversarial = "a".repeat(262143) + "b", needle = "a".repeat(16383) + "b";
if (str_find(adversarial, needle, false).value !== 245760n
  || str_find(adversarial, needle, true).value !== 245760n
  || str_count(adversarial, needle) !== 1n) { throw new Error("adversarial search"); }
console.log("JS text Python oracle: ok (" + textCases.length + " cases + adversarial search)");
for (const build of [() => str_pad("a", 1n << 32n, ".", 0),
  () => str_pad("a", 1n << 32n, ".", 1), () => str_repeat("ab", 1n << 31n)]) {
  try { build(); throw new Error("accepted oversized string"); }
  catch (e) { if (e !== "bend: a string past the maximum length 2^31") { throw e; } }
}
console.log("C/JS string length diagnostics: ok");
// Streaming partition law, as in runtime.c's stream_law.
function streamRun(b, cuts) {
  let pend = 0, need = 0, out = "", i = 0;
  for (;;) {
    let j = i;
    while (j < b.length && !cuts(j)) { j += 1; }
    j = j < b.length ? j + 1 : b.length;
    const buf = new Uint8Array(need + j - i + 4);
    for (let m = 0; m < need; m += 1) { buf[m] = (pend >>> (8 * m)) & 255; }
    buf.set(b.subarray(i, j), need);
    const r = file_read_text_go_dec(buf, need + j - i, i === b.length);
    if (i < b.length && r.snd.snd === "" && r.snd.fst <= need) { throw new Error("silent chunk"); }
    pend = r.fst; need = r.snd.fst; out += r.snd.snd;
    if (i === b.length) { if (need !== 4 || pend !== 0) { throw new Error("eof state"); } return out; }
    i = j;
  }
}
function streamCheck(b, cuts) {
  const got = streamRun(b, cuts), want = io_text(b, b.length);
  if (got !== want) { throw new Error(JSON.stringify({bytes: [...b], got, want})); }
}
const abc = [0x00, 0x41, 0x80, 0xbf, 0xc2, 0xe0, 0xed, 0xf0, 0xf4, 0xa0, 0x90, 0xff];
let parts = 0;
for (let n = 0; n <= 4; n += 1) {
  for (let w = 0; w < 12 ** n; w += 1) {
    const b = new Uint8Array(n);
    for (let i = 0, x = w; i < n; i += 1, x = Math.floor(x / 12)) { b[i] = abc[x % 12]; }
    for (let mask = 0; mask < 1 << Math.max(n - 1, 0); mask += 1) { streamCheck(b, (j) => (mask >> j) & 1); parts += 1; }
  }
}
for (const [bytes] of cases) {
  const b = new Uint8Array(bytes);
  streamCheck(b, () => 1); parts += 1;
  for (let i = 0; i < b.length; i += 1) { streamCheck(b, (j) => j === i); parts += 1; }
}
let seed = 0xB3D;
const rand = () => (seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0) >>> 8;
for (let t = 0; t < 2000; t += 1) {
  const b = new Uint8Array(1 + rand() % 64);
  for (let i = 0; i < b.length; i += 1) {
    const r = rand();
    b[i] = r % 3 === 0 ? abc[(r >> 4) % 12] : r % 3 === 1 ? 0x80 | ((r >> 4) & 0x7f) : (r >> 4) & 255;
  }
  streamCheck(b, () => rand() % 3 === 0); parts += 1;
}
console.log("JS streaming partition law: ok (" + parts + " partitions)");
'''
    # Effects are emitted inside a closure; the probe needs the decode step.
    js += (ROOT / "bend2/effs/file_read_text_go.js").read_text()
    jsfile.write_text(js)
    run(["bun", str(jsfile)])
