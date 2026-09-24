// TCP
// ===

// TCP.listen(port) binds every interface, TCP.listen_on(host, port) the
// one dotted IPv4 address named (EINVAL for anything else). The shared
// pair sets SO_REUSEPORT too: several processes may listen on one port
// and the kernel deals the connections out among them.
uint32_t tcp_listen_at(const char* host, uint32_t port, int shared, int* out) {
  int fd = socket(AF_INET, SOCK_STREAM, 0);
  if (fd < 0) {
    return (uint32_t)errno;
  }
  int one = 1;
  setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one));
  if (shared) {
    setsockopt(fd, SOL_SOCKET, SO_REUSEPORT, &one, sizeof(one));
  }
  struct sockaddr_in at;
  if (io_sys_addr(host, port, &at) < 0) {
    close(fd);
    return EINVAL;
  }
  int bound = bind(fd, (struct sockaddr*)&at, sizeof(at));
  // the backlog is clamped to the kernel's limit (somaxconn)
  if (bound < 0 || listen(fd, 4096) < 0
    || fcntl(fd, F_SETFL, fcntl(fd, F_GETFL) | O_NONBLOCK) < 0) {
    uint32_t code = (uint32_t)errno;
    close(fd);
    return code;
  }
  *out = fd;
  return 0;
}

uint32_t tcp_listen(uint32_t port, int* out) {
  return tcp_listen_at("0.0.0.0", port, 0, out);
}

// f holds the port alone, or the host and then the port
static Term tcp_listen_host(Env e, Term* f, int named, int shared) {
  u64   n = 0;
  char* host = named ? io_cstr(e, f[0], &n) : NULL;
  int   out = -1;
  uint32_t q = named && io_nul(host, n) ? EINVAL
    : tcp_listen_at(named ? host : "0.0.0.0", (uint32_t)f[named], shared, &out);
  free(host);
  return q != 0 ? io_fail(e, q, NULL) : io_done(e, io_hand(out));
}

#ifdef CID_TCP_LISTEN
Term tcp_listen_run(Env e, Term* f, IoWork* w) {
  return tcp_listen_host(e, f, 0, 0);
}

static void __attribute__((constructor)) tcp_listen_use(void) {
  io_eff(CID_TCP_LISTEN, tcp_listen_run, 0);
}
#endif

#ifdef CID_TCP_LISTEN_ON
Term tcp_listen_on_run(Env e, Term* f, IoWork* w) {
  return tcp_listen_host(e, f, 1, 0);
}

static void __attribute__((constructor)) tcp_listen_on_use(void) {
  io_eff(CID_TCP_LISTEN_ON, tcp_listen_on_run, 0);
}
#endif

#ifdef CID_TCP_LISTEN_SHARED
Term tcp_listen_shared_run(Env e, Term* f, IoWork* w) {
  return tcp_listen_host(e, f, 0, 1);
}

static void __attribute__((constructor)) tcp_listen_shared_use(void) {
  io_eff(CID_TCP_LISTEN_SHARED, tcp_listen_shared_run, 0);
}
#endif

#ifdef CID_TCP_LISTEN_SHARED_ON
Term tcp_listen_shared_on_run(Env e, Term* f, IoWork* w) {
  return tcp_listen_host(e, f, 1, 1);
}

static void __attribute__((constructor)) tcp_listen_shared_on_use(void) {
  io_eff(CID_TCP_LISTEN_SHARED_ON, tcp_listen_shared_on_run, 0);
}
#endif
