// sig.raise: the signal sent to the process itself; the handler the
// program installed (by asking after the signal) runs before it returns
Term sig_raise_run(Env e, Term* f, IoWork* w) {
  raise((int)f[0]);
  return term_pak(CID_UNIT, 0);
}

static void __attribute__((constructor)) sig_raise_use(void) {
  io_eff(CID_SIG_RAISE, sig_raise_run, 0);
}
