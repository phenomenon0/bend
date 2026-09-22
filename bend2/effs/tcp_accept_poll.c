// TCP
// ===

// TCP.accept_poll(listener, ms) is TCP.accept with a deadline: an accept
// is tried first, and one that finds no connection parks on the listener
// and on the clock, whichever fires first. Past the deadline it answers
// None{}, so a loop that accepts can also look up from time to time --
// at a signal, at a count -- without a second computation to do it.
static Term tcp_accept_poll_more(Env e, IoWork* w);

static Term tcp_accept_poll_at(Env e, IoWork* w, u64 at) {
  int fd  = (int)w->hand;
  int got = accept(fd, NULL, NULL);
  if (got >= 0 && fcntl(got, F_SETFL, fcntl(got, F_GETFL) | O_NONBLOCK) < 0) {
    close(got);
    got = -1;
  }
  io_sys_end(w, got);
  if (w->code == EAGAIN) {
    return io_tick() < at ? io_wait_on(w, fd, POLLIN, at, tcp_accept_poll_more)
      : io_tup(e, io_hand(fd), io_done(e, term_pak(CID_NONE, 0)));
  }
  Term r = w->code != 0 ? io_fail(e, w->code, NULL)
    : io_done(e, io_box(e, CID_SOME, io_hand(got)));
  return io_tup(e, io_hand(fd), r);
}

static Term tcp_accept_poll_more(Env e, IoWork* w) {
  return tcp_accept_poll_at(e, w, io_wait_time(w));
}

Term tcp_accept_poll_run(Env e, Term* f, IoWork* w) {
  w->hand = (intptr_t)io_hand_v(f[0]);
  return tcp_accept_poll_at(e, w, io_tick() + (u64)f[1] * 1000000ull);
}

static void __attribute__((constructor)) tcp_accept_poll_use(void) {
  io_eff(CID_TCP_ACCEPT_POLL, tcp_accept_poll_run, 0);
}
