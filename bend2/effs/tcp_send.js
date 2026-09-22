// TCP
// ===

// Sends what is left; a full socket (non-blocking, so EAGAIN) parks the
// computation until the socket is writable, and the loop resumes here.
function tcp_send(socket, data, k) {
  return tcp_send_buffer(socket, io_bytes(data), k);
}

// The bytes as they are (0..255), one List cell each; a value past 255
// is not a byte and fails with EINVAL before anything goes out.
function tcp_send_bytes(socket, data, k) {
  const bytes = [];
  for (let xs = data; xs.$ === "Con"; xs = xs.tail) {
    bytes.push(xs.head);
  }
  if (bytes.some((x) => x > 255)) {
    return io_tup(socket, io_fail(22));
  }
  return tcp_send_buffer(socket, Uint8Array.from(bytes), k);
}

function tcp_send_buffer(socket, b, k) {
  const sys = io_sys();
  const fd = socket;
  const again = sys.mac ? 35 : 11;
  const go = (at) => {
    while (at < b.length) {
      const part = b.subarray(at);
      const n = Number(sys.send(fd, sys.ptr(part), part.length, 0));
      if (n < 0) {
        const code = sys.errno();
        if (code === again) {
          io_park_on(fd, true, k, () => go(at));
          return undefined;
        }
        return io_tup(socket, io_fail(code));
      }
      at += n;
    }
    return io_tup(socket, io_done({ $: "Unit" }));
  };
  return go(0);
}
