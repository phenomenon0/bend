// TCP
// ===

// TCP.listen_shared(port) is TCP.listen with SO_REUSEPORT;
// TCP.listen_shared_on(host, port) binds the one address named.

function tcp_listen_shared_at(host, port) {
  const sys = io_sys();
  const fd = sys.socket(2, 1, 0);
  if (fd < 0) {
    return io_fail(sys.errno());
  }
  const one = new Int32Array([1]);
  const level = sys.mac ? 0xffff : 1;
  sys.setsockopt(fd, level, sys.mac ? 4 : 2, sys.ptr(one), 4);
  sys.setsockopt(fd, level, sys.mac ? 0x200 : 15, sys.ptr(one), 4);
  const at = io_addr(host, Number(port));
  if (at === null) {
    sys.close(fd);
    return io_fail(22);
  }
  if (sys.bind(fd, sys.ptr(at), 16) < 0 || sys.listen(fd, 4096) < 0
    || sys.fcntl(fd, 4, sys.fcntl(fd, 3, 0) | (sys.mac ? 4 : 0x800)) < 0) {
    const code = sys.errno();
    sys.close(fd);
    return io_fail(code);
  }
  return io_done(fd);
}

function tcp_listen_shared(port) {
  return tcp_listen_shared_at("0.0.0.0", port);
}

function tcp_listen_shared_on(host, port) {
  return tcp_listen_shared_at(host, port);
}
