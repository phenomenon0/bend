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
with tempfile.TemporaryDirectory(prefix="bend-strings-runtime-") as temp:
    tmp = Path(temp)
    seed = tmp / "seed.bend"
    seed.write_text('import Base\n\ndef main() -> String:\n  "abcdef"\n')
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
    for op in ["repeat", "prepend", "append", "copy", "transform", "split", "from-list", "join", "slice"]:
        for offset in range(2 if op == "slice" else 4):
            run([str(binary), "fault-" + op, str(offset)], capture_output=True,
                env={**os.environ, "ASAN_OPTIONS": "detect_leaks=0"})
            faults += 1
    print(f"Device-style allocation failures: ok ({faults} injected cases)", flush=True)
    fail = subprocess.run([str(binary), "raw-output"], cwd=ROOT, text=True, capture_output=True)
    assert fail.returncode and fail.stderr == "bend: cannot encode a non-scalar Char as UTF-8\n", fail
    js = jsfile.read_text().split("\ncli(process.argv.slice(2));")[0]
    js += "\nconst cases = " + json.dumps([[list(b), decode(b)] for b in cases]) + ";\n"
    js += r'''
for (const [bytes, want] of cases) {
  const got = [...io_text(new Uint8Array(bytes), bytes.length)].map(c => c.codePointAt(0));
  if (JSON.stringify(got) !== JSON.stringify(want)) { throw new Error(JSON.stringify({bytes, got, want})); }
}
try { io_bytes("\ud800"); throw new Error("accepted raw output"); }
catch (e) { if (e !== "bend: cannot encode a non-scalar Char as UTF-8") { throw e; } }
for (const build of [() => str_prepend(char_new(0xd800), ""),
  () => str_from_list({$: "Con", head: char_new(0xffffffff), tail: {$: "Nil"}})]) {
  try { build(); throw new Error("accepted raw string"); }
  catch (e) { if (e !== "bend: JS strings cannot contain non-scalar Char values") { throw e; } }
}
console.log("JS UTF-8: ok (" + cases.length + " byte vectors)");
'''
    jsfile.write_text(js)
    run(["bun", str(jsfile)])
