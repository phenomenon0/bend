// TCP
// ===

static void tcp_recv_start(Term* f, IoWork* w) {
  w->hand = (intptr_t)io_hand_v(f[0]);
  w->made = f[1] < INT32_MAX ? (intptr_t)f[1] : INT32_MAX;
  w->data = io_mem(malloc((size_t)w->made + 1));
}

// The loop parked the request until the socket was readable; a recv that
// still finds nothing (the socket is non-blocking) parks again on more.
// val makes the answer of what arrived.
static Term tcp_recv_with(Env e, IoWork* w, IoPack more, IoPack val) {
  int fd  = (int)w->hand;
  w->size = io_sys_end(w, recv(fd, w->data, (size_t)w->made, 0));
  if (w->code == EAGAIN) {
    return io_wait_on(w, fd, POLLIN, 0, more);
  }
  Term r = w->code ? io_fail(e, w->code, NULL) : io_done(e, val(e, w));
  free(w->data);
  return io_tup(e, io_hand(w->hand), r);
}

#ifdef CID_TCP_RECV

static Term tcp_recv_text(Env e, IoWork* w) {
  return io_str(e, w->data, w->size);
}

static Term tcp_recv_more(Env e, IoWork* w) {
  return tcp_recv_with(e, w, tcp_recv_more, tcp_recv_text);
}

Term tcp_recv_run(Env e, Term* f, IoWork* w) {
  tcp_recv_start(f, w);
  return tcp_recv_more(e, w);
}

static void __attribute__((constructor)) tcp_recv_use(void) {
  io_eff(CID_TCP_RECV, tcp_recv_run, IO_READ);
}

#endif

#ifdef CID_TCP_RECV_BYTES

// The bytes as they are (0..255), one List cell each; a text reader
// would decode them as UTF-8.
static Term tcp_recv_list(Env e, IoWork* w) {
  Term xs = term_pak(CID_NIL, 0);
  for (u64 i = w->size; i > 0; i -= 1) {
    xs = io_node(e, CID_CON, ((uint8_t*)w->data)[i - 1], xs);
  }
  return xs;
}

static Term tcp_recv_bytes_more(Env e, IoWork* w) {
  return tcp_recv_with(e, w, tcp_recv_bytes_more, tcp_recv_list);
}

Term tcp_recv_bytes_run(Env e, Term* f, IoWork* w) {
  tcp_recv_start(f, w);
  return tcp_recv_bytes_more(e, w);
}

static void __attribute__((constructor)) tcp_recv_bytes_use(void) {
  io_eff(CID_TCP_RECV_BYTES, tcp_recv_bytes_run, IO_READ);
}

#endif
