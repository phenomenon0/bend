// IO
// ==

// IO.signal_pending(sig) answers whether the signal has arrived since it
// was last asked, and takes the first ask as the request to catch it: the
// handler only sets a flag, so the default (for SIGTERM, to die at once)
// becomes the program's own answer, given when it next looks. Syscalls
// restart across it, so an effect in flight is not failed by a signal.
static volatile sig_atomic_t io_sig_seen[65];
static volatile sig_atomic_t io_sig_hook[65];

static void io_sig_note(int sig) {
  if (sig > 0 && sig < 65) {
    io_sig_seen[sig] = 1;
  }
}

Term io_signal_pending_run(Env e, Term* f, IoWork* w) {
  u32 sig = (u32)f[0];
  if (sig == 0 || sig >= 65) {
    return chan_bool(false);
  }
  if (!io_sig_hook[sig]) {
    struct sigaction sa;
    memset(&sa, 0, sizeof(sa));
    sa.sa_handler = io_sig_note;
    sigemptyset(&sa.sa_mask);
    sa.sa_flags = SA_RESTART;
    sigaction((int)sig, &sa, NULL);
    io_sig_hook[sig] = 1;
  }
  bool seen = io_sig_seen[sig] != 0;
  io_sig_seen[sig] = 0;
  return chan_bool(seen);
}

static void __attribute__((constructor)) io_signal_pending_use(void) {
  io_eff(CID_IO_SIGNAL_PENDING, io_signal_pending_run, 0);
}
