// TCP
// ===

// The loop parked the request until the socket was readable; a recv that
// still finds nothing (the socket is non-blocking) parks again.
function tcp_recv(socket, max, k) {
  const sys = io_sys();
  const fd = socket;
  const b = new Uint8Array(Math.max(Number(max), 1));
  const again = sys.mac ? 35 : 11;
  const go = () => {
    const n = Number(sys.recv(fd, sys.ptr(b), Number(max), 0));
    if (n < 0) {
      const code = sys.errno();
      if (code === again) {
        io_park_on(fd, false, k, go);
        return undefined;
      }
      return io_tup(socket, io_fail(code));
    }
    return io_tup(socket, io_done(io_text(b, n)));
  };
  return go();
}

function tcp_recv_need() {
  return { read: true };
}

// The bytes as they are (0..255), one List cell each: no text decoder
// anywhere near the socket.
function tcp_recv_bytes(socket, max, k) {
  const sys = io_sys();
  const fd = socket;
  const b = new Uint8Array(Math.max(Number(max), 1));
  const again = sys.mac ? 35 : 11;
  const go = () => {
    const n = Number(sys.recv(fd, sys.ptr(b), Number(max), 0));
    if (n < 0) {
      const code = sys.errno();
      if (code === again) {
        io_park_on(fd, false, k, go);
        return undefined;
      }
      return io_tup(socket, io_fail(code));
    }
    let xs = { $: "Nil" };
    for (let i = n; i > 0; i -= 1) {
      xs = { $: "Con", head: b[i - 1], tail: xs };
    }
    return io_tup(socket, io_done(xs));
  };
  return go();
}

function tcp_recv_bytes_need() {
  return { read: true };
}
