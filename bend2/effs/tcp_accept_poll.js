// TCP
// ===

// TCP.accept_poll(listener, ms) is TCP.accept with a deadline: an accept
// is tried first; nothing parks on the listener and on the clock; past
// the deadline it answers None{}.
function tcp_accept_poll(listener, ms, k) {
  const sys = io_sys();
  const lfd = listener;
  const at = performance.now() + Number(ms);
  const again = sys.mac ? 35 : 11;
  const go = () => {
    const fd = sys.accept(lfd, null, null);
    if (fd < 0) {
      const code = sys.errno();
      if (code !== again) {
        return io_tup(listener, io_fail(code));
      }
      if (performance.now() >= at) {
        return io_tup(listener, io_done({ $: "None" }));
      }
      io_park_on(lfd, false, k, go, at);
      return undefined;
    }
    if (sys.fcntl(fd, 4, sys.fcntl(fd, 3, 0) | (sys.mac ? 4 : 0x800)) < 0) {
      const code = sys.errno();
      sys.close(fd);
      return io_tup(listener, io_fail(code));
    }
    return io_tup(listener, io_done({ $: "Some", value: fd }));
  };
  return go();
}
