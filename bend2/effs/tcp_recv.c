// TCP
// ===

static Term tcp_recv_open(Term sock, Term max, IoWork* w) {
  w->hand = (intptr_t)io_hand_v(sock);
  w->made = max < INT32_MAX ? (intptr_t)max : INT32_MAX;
  w->data = io_mem(malloc((size_t)w->made + 1));
  return 0;
}

#ifdef CID_TCP_RECV

static Term tcp_recv_pack(Env e, IoWork* w) {
  Term r = w->code ? io_fail(e, w->code, NULL)
    : io_done(e, io_str(e, w->data, w->size));
  free(w->data);
  return io_tup(e, io_hand(w->hand), r);
}

// The loop parked the request until the socket was readable; a recv that
// still finds nothing (the socket is non-blocking) parks again.
static Term tcp_recv_more(Env e, IoWork* w) {
  int fd  = (int)w->hand;
  w->size = io_sys_end(w, recv(fd, w->data, (size_t)w->made, 0));
  return w->code == EAGAIN ? io_wait_on(w, fd, POLLIN, 0, tcp_recv_more)
    : tcp_recv_pack(e, w);
}

Term tcp_recv_run(Env e, Term* f, IoWork* w) {
  tcp_recv_open(f[0], f[1], w);
  return tcp_recv_more(e, w);
}

static void __attribute__((constructor)) tcp_recv_use(void) {
  io_eff(CID_TCP_RECV, tcp_recv_run, IO_READ);
}

#endif

#ifdef CID_TCP_RECV_BYTES

// The bytes as they are (0..255), one List cell each, as
// File.read_bytes gives them. A text reader decodes them as UTF-8,
// which on a socket is not a cost but a corruption: every byte that is
// not valid UTF-8 becomes U+FFFD, three bytes out for one byte in, so a
// reply framed by a length it no longer matches desynchronises the
// stream. A reader of anything that is not text needs this instead.
static Term tcp_recv_bytes_pack(Env e, IoWork* w) {
  Term r;
  if (w->code) {
    r = io_fail(e, w->code, NULL);
  } else {
    Term xs = term_pak(CID_NIL, 0);
    for (u64 i = w->size; i > 0; i -= 1) {
      xs = io_node(e, CID_CON, ((uint8_t*)w->data)[i - 1], xs);
    }
    r = io_done(e, xs);
  }
  free(w->data);
  return io_tup(e, io_hand(w->hand), r);
}

static Term tcp_recv_bytes_more(Env e, IoWork* w) {
  int fd  = (int)w->hand;
  w->size = io_sys_end(w, recv(fd, w->data, (size_t)w->made, 0));
  return w->code == EAGAIN
    ? io_wait_on(w, fd, POLLIN, 0, tcp_recv_bytes_more)
    : tcp_recv_bytes_pack(e, w);
}

Term tcp_recv_bytes_run(Env e, Term* f, IoWork* w) {
  tcp_recv_open(f[0], f[1], w);
  return tcp_recv_bytes_more(e, w);
}

static void __attribute__((constructor)) tcp_recv_bytes_use(void) {
  io_eff(CID_TCP_RECV_BYTES, tcp_recv_bytes_run, IO_READ);
}

#endif
