// Clock.wall: the wall clock, in ms since the Unix epoch. Base has only
// IO.now (CLOCK_MONOTONIC), which cannot date a log line or survive a
// restart, so the app brings its own effect (guide/EFFECTS.md).
Term clock_wall_run(Env e, Term* f, IoWork* w) {
  struct timespec ts;
  clock_gettime(CLOCK_REALTIME, &ts);
  return (Term)((u64)ts.tv_sec * 1000ull + (u64)ts.tv_nsec / 1000000ull);
}

static void __attribute__((constructor)) clock_wall_use(void) {
  io_eff(CID_CLOCK_WALL, clock_wall_run, 0);
}
