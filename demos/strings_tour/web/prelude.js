// prelude.js - shim layer that lets the Bend->JS lane programs run outside node.
// Used by the browser worker AND the node self-test (same file, same logic).
/* eslint-disable */
(function () {
  class NodeBuf extends Uint8Array {
    static from(x, enc) {
      if (typeof x === "string") {
        const utf8 = enc && enc !== "utf8" && enc !== "utf-8";
        const bytes = utf8 ? NodeBuf.encodeLatin(x) : new TextEncoder().encode(x);
        const b = new NodeBuf(bytes.length);
        b.set(bytes);
        return b;
      }
      if (x instanceof Uint8Array) { const b = new NodeBuf(x.length); b.set(x); return b; }
      if (Array.isArray(x)) { const b = new NodeBuf(x.length); b.set(x); return b; }
      return new NodeBuf(0);
    }
    static alloc(n) { return new NodeBuf(n); }
    static encodeLatin(s) { return new Uint8Array(Array.from(s).map((c) => c.charCodeAt(0) & 0xff)); }
    toString(enc) {
      if (enc && enc !== "utf8" && enc !== "utf-8") return Array.from(this).map((c) => String.fromCharCode(c)).join("");
      return new TextDecoder().decode(this);
    }
  }

  function makeEnv() {
    const cap = { out: [], err: [], exit: undefined, error: undefined };
    const files = {};
    const fds = {}; // fd -> { key, pos }
    let nfd = 10;
    const dec = (d) => (typeof d === "string" ? d : new TextDecoder().decode(d instanceof Uint8Array ? d : new Uint8Array(d)));

    const fs = {
      openSync(p, mode) {
        const key = dec(p);
        if (!(key in files)) { const e = new Error("ENOENT: no such file or directory: " + key); e.code = "ENOENT"; throw e; }
        const fd = nfd++; fds[fd] = { key, pos: 0 }; return fd;
      },
      closeSync(fd) { delete fds[fd]; },
      readSync(fd, buf, off = 0, len = buf.length, pos) {
        const e = fds[fd];
        if (!e) return 0;
        const data = files[e.key];
        const at = (pos === undefined || pos === null) ? e.pos : pos;
        if (at >= data.length) return 0;
        const n = Math.min(len, data.length - at);
        buf.set(data.subarray(at, at + n), off);
        if (pos === undefined || pos === null) e.pos = at + n;
        return n;
      },
      writeSync(fd, data, off = 0, len) {
        const n = len === undefined ? data.length - off : len;
        const s = data instanceof Uint8Array ? dec(data.subarray(off, off + n)) : String(data);
        (fd === 2 ? cap.err : cap.out).push(s);
        return n; // node semantics: bytes written, not chars
      },
      fstatSync(fd) { const e = fds[fd]; return { size: e ? files[e.key].length : 0 }; },
      statSync(p) { const d = files[dec(p)]; if (!d) { const e = new Error("ENOENT"); e.code = "ENOENT"; throw e; } return { size: d.length, isFile: () => true }; },
    };

    // The io layer's raw-syscall path (file_read uses sys.read(fd, ptr, len)).
    const ffiStub = {
      ptr: (x) => x,
      read: { i32: () => 0 },
      dlopen: (name, defs) => {
        const symbols = {};
        for (const k of Object.keys(defs || {})) symbols[k] = () => 0;
        symbols.read = (fd, ptr, len) => {
          const e = fds[fd];
          if (!e) return -1;
          const data = files[e.key];
          const n = Math.min(len, Math.max(0, data.length - e.pos));
          if (n > 0) { ptr.set(data.subarray(e.pos, e.pos + n)); e.pos += n; }
          return n;
        };
        symbols.write = (fd, ptr, len) => {
          const s = dec(ptr.subarray(0, len));
          (fd === 2 ? cap.err : cap.out).push(s);
          return len;
        };
        symbols.strerror = (code) => "errno " + code;
        return { symbols };
      },
    };

    const proc = {
      argv: ["bend", "prog"], env: {}, platform: "linux", arch: "x64",
      exit: (c) => { cap.exit = c; },
      stdout: {}, stderr: {}, cwd: () => ".",
    };
    return { cap, files, fds, fs, ffiStub, proc };
  }

  function runProgram(code, filesIn, envIn, argvIn, opts) {
    const { cap, files, fs, ffiStub, proc } = makeEnv();
    if (opts && opts.trace) {
      const wrap = (obj, names) => names.forEach((n) => { const f = obj[n].bind(obj); obj[n] = (...a) => { cap.err.push("[trace] " + n + "(" + a.map((x) => (typeof x === "string" ? JSON.stringify(x) : x instanceof Uint8Array ? "<u8 " + x.length + ">" : x)).join(", ") + ")\n"); return f(...a); }; });
      wrap(fs, ["openSync", "closeSync", "readSync", "writeSync", "statSync"]);
    }
    for (const [k, v] of Object.entries(filesIn || {})) {
      files[k] = v instanceof Uint8Array ? v : new TextEncoder().encode(v);
    }
    proc.env = Object.assign({}, envIn || {});
    proc.argv = ["bend", "prog"].concat(argvIn || []);
    globalThis.process = proc;
    globalThis.Buffer = NodeBuf;
    globalThis.require = (m) => (m === "fs" ? fs : m === "bun:ffi" ? ffiStub : {});
    globalThis.BEND_SYS = undefined;
    try {
      (0, eval)(code);
    } catch (e) {
      cap.error = (e && (e.stack || e.message)) || String(e);
    }
    return { out: cap.out.join(""), err: cap.err.join(""), exit: cap.exit, error: cap.error };
  }

  const api = { runProgram, NodeBuf };
  if (typeof module !== "undefined" && module.exports) module.exports = api;
  globalThis.BendShim = api;
})();
