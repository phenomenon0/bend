// TCP
// ===

// TCP.poll(sock, max, ms) is recv with a deadline: the park waits on the
// socket and on the clock, whichever fires first. A wake that finds data
// answers Some{data} ("" is the peer's close, as TCP.recv answers it); one
// that finds nothing parks again until the deadline, then answers None{}.
// val makes data of what arrived.
static Term tcp_poll_with(Env e, IoWork* w, IoPack more, IoPack val) {
  int  fd = (int)w->hand;
  u64  at = io_wait_time(w);
  Term r;
  w->size = io_sys_end(w, recv(fd, w->data, (size_t)w->made, 0));
  if (w->code == EAGAIN && io_tick() < at) {
    return io_wait_on(w, fd, POLLIN, at, more);
  }
  r = w->code == EAGAIN ? io_done(e, term_pak(CID_NONE, 0))
    : w->code ? io_fail(e, w->code, NULL)
    : io_done(e, io_box(e, CID_SOME, val(e, w)));
  free(w->data);
  return io_tup(e, io_hand(w->hand), r);
}

static Term tcp_poll_start(Term* f, IoWork* w, IoPack more) {
  w->hand = (intptr_t)io_hand_v(f[0]);
  w->made = f[1] < INT32_MAX ? (intptr_t)f[1] : INT32_MAX;
  w->data = io_mem(malloc((size_t)w->made + 1));
  return io_wait_on(w, (int)w->hand, POLLIN,
    io_tick() + (u64)f[2] * 1000000ull, more);
}

#ifdef CID_TCP_POLL

static Term tcp_poll_text(Env e, IoWork* w) {
  return io_str(e, w->data, w->size);
}

static Term tcp_poll_more(Env e, IoWork* w) {
  return tcp_poll_with(e, w, tcp_poll_more, tcp_poll_text);
}

Term tcp_poll_run(Env e, Term* f, IoWork* w) {
  return tcp_poll_start(f, w, tcp_poll_more);
}

static void __attribute__((constructor)) tcp_poll_use(void) {
  io_eff(CID_TCP_POLL, tcp_poll_run, 0);
}

#endif

#ifdef CID_TCP_POLL_BYTES

// The bytes as they are (0..255), one List cell each.
static Term tcp_poll_list(Env e, IoWork* w) {
  Term xs = term_pak(CID_NIL, 0);
  for (u64 i = w->size; i > 0; i -= 1) {
    xs = io_node(e, CID_CON, ((uint8_t*)w->data)[i - 1], xs);
  }
  return xs;
}

static Term tcp_poll_bytes_more(Env e, IoWork* w) {
  return tcp_poll_with(e, w, tcp_poll_bytes_more, tcp_poll_list);
}

Term tcp_poll_bytes_run(Env e, Term* f, IoWork* w) {
  return tcp_poll_start(f, w, tcp_poll_bytes_more);
}

static void __attribute__((constructor)) tcp_poll_bytes_use(void) {
  io_eff(CID_TCP_POLL_BYTES, tcp_poll_bytes_run, 0);
}

#endif
