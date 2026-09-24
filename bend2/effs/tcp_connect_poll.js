// TCP
// ===

// TCP.connect with a deadline, as tcp_connect.js: EINPROGRESS parks the
// computation on the socket becoming writable and on the clock. Woken,
// SO_ERROR says whether the connect failed, and a second connect whether
// it is done (EISCONN) or still going (EALREADY); the clock past, it is
// ETIMEDOUT.
function tcp_connect_poll(host, port, ms, k) {
  const sys = io_sys();
  const at = io_addr(host, Number(port));
  if (at === null) {
    return io_fail(22);
  }
  const fd = sys.socket(2, 1, 0);
  if (fd < 0) {
    return io_fail(sys.errno());
  }
  const end = (code) => {
    if (code !== 0) {
      sys.close(fd);
      return io_fail(code);
    }
    return io_done(fd);
  };
  const error = () => {
    const v = new Int32Array([0]);
    const l = new Uint32Array([4]);
    return sys.getsockopt(fd, sys.mac ? 0xffff : 1, sys.mac ? 0x1007 : 4,
      sys.ptr(v), sys.ptr(l)) < 0 ? sys.errno() : v[0];
  };
  const set = sys.fcntl(fd, 4, sys.fcntl(fd, 3, 0) | (sys.mac ? 4 : 0x800));
  const ok = set >= 0 && sys.connect(fd, sys.ptr(at), 16) >= 0;
  const code = ok ? 0 : sys.errno();
  const going = sys.mac ? [36, 37] : [115, 114];
  if (code !== going[0]) {
    return end(code);
  }
  const due = performance.now() + Math.max(Number(ms), 1);
  const more = () => {
    const err = error();
    if (err !== 0) {
      return end(err);
    }
    const again = sys.connect(fd, sys.ptr(at), 16) >= 0 ? 0 : sys.errno();
    if (!going.includes(again)) {
      return end(again === (sys.mac ? 56 : 106) ? 0 : again);
    }
    if (performance.now() >= due) {
      return end(sys.mac ? 60 : 110);
    }
    io_park_on(fd, true, k, more, due);
    return undefined;
  };
  io_park_on(fd, true, k, more, due);
  return undefined;
}
