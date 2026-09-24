// TCP
// ===

// TCP.listen_shared(port) is TCP.listen with SO_REUSEPORT: several
// processes may listen on one port and the kernel deals the connections
// out among them, which is how a single-threaded server takes more than
// one core. TCP.listen itself keeps refusing a port already taken, since
// that refusal is what most programs want to hear. TCP.listen_shared_on
// (host, port) binds the one dotted IPv4 address named.
uint32_t tcp_listen_shared_at(const char* host, uint32_t port, int* out) {
  int fd = socket(AF_INET, SOCK_STREAM, 0);
  if (fd < 0) {
    return (uint32_t)errno;
  }
  int one = 1;
  setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one));
  setsockopt(fd, SOL_SOCKET, SO_REUSEPORT, &one, sizeof(one));
  struct sockaddr_in at;
  if (io_sys_addr(host, port, &at) < 0) {
    close(fd);
    return EINVAL;
  }
  int bound = bind(fd, (struct sockaddr*)&at, sizeof(at));
  if (bound < 0 || listen(fd, SOMAXCONN) < 0
    || fcntl(fd, F_SETFL, fcntl(fd, F_GETFL) | O_NONBLOCK) < 0) {
    uint32_t code = (uint32_t)errno;
    close(fd);
    return code;
  }
  *out = fd;
  return 0;
}

uint32_t tcp_listen_shared(uint32_t port, int* out) {
  return tcp_listen_shared_at("0.0.0.0", port, out);
}

static Term tcp_listen_shared_end(Env e, uint32_t q, int out) {
  return q != 0 ? io_fail(e, q, NULL) : io_done(e, io_hand(out));
}

#ifdef CID_TCP_LISTEN_SHARED
Term tcp_listen_shared_run(Env e, Term* f, IoWork* w) {
  int out = -1;
  uint32_t q = tcp_listen_shared((uint32_t)f[0], &out);
  return tcp_listen_shared_end(e, q, out);
}

static void __attribute__((constructor)) tcp_listen_shared_use(void) {
  io_eff(CID_TCP_LISTEN_SHARED, tcp_listen_shared_run, 0);
}
#endif

#ifdef CID_TCP_LISTEN_SHARED_ON
Term tcp_listen_shared_on_run(Env e, Term* f, IoWork* w) {
  u64   n = 0;
  char* host = io_cstr(e, f[0], &n);
  int   out = -1;
  uint32_t q = io_nul(host, n) ? EINVAL : tcp_listen_shared_at(host, (uint32_t)f[1], &out);
  free(host);
  return tcp_listen_shared_end(e, q, out);
}

static void __attribute__((constructor)) tcp_listen_shared_on_use(void) {
  io_eff(CID_TCP_LISTEN_SHARED_ON, tcp_listen_shared_on_run, 0);
}
#endif
