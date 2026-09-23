// TCP
// ===

// TCP.poll(sock, max, ms) is recv with a deadline: a recv that finds
// nothing parks on the socket and on the clock, whichever fires first;
// past the deadline it answers None{}, else Some{data} ("" is the peer's
// close, as TCP.recv answers it). pack makes data of what arrived.
function tcp_poll_with(socket, max, ms, k, pack) {
  const sys = io_sys();
  const fd = socket;
  const b = new Uint8Array(Math.max(Number(max), 1));
  const at = performance.now() + Number(ms);
  const go = () => {
    const n = Number(sys.recv(fd, sys.ptr(b), Number(max), 0));
    if (n >= 0) {
      return io_tup(socket, io_done({ $: "Some", value: pack(b, n) }));
    }
    const code = sys.errno();
    if (code !== (sys.mac ? 35 : 11)) {
      return io_tup(socket, io_fail(code));
    }
    if (performance.now() >= at) {
      return io_tup(socket, io_done({ $: "None" }));
    }
    io_park_on(fd, false, k, go, at);
    return undefined;
  };
  return go();
}

// The bytes as they are (0..255), one List cell each.
function tcp_poll_list(b, n) {
  let xs = { $: "Nil" };
  for (let i = n; i > 0; i -= 1) {
    xs = { $: "Con", head: b[i - 1], tail: xs };
  }
  return xs;
}

function tcp_poll(socket, max, ms, k) {
  return tcp_poll_with(socket, max, ms, k, io_text);
}

function tcp_poll_bytes(socket, max, ms, k) {
  return tcp_poll_with(socket, max, ms, k, tcp_poll_list);
}
