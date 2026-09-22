// IO
// ==

// IO.signal_pending(sig) answers whether the signal has arrived since it
// was last asked; the first ask installs the listener that notes it.
const io_sig_seen = {};

function io_signal_pending(sig) {
  const names = { 1: "SIGHUP", 2: "SIGINT", 10: "SIGUSR1", 12: "SIGUSR2", 15: "SIGTERM" };
  const name = names[Number(sig)];
  if (name === undefined) {
    return false;
  }
  if (!(name in io_sig_seen)) {
    io_sig_seen[name] = false;
    process.on(name, () => { io_sig_seen[name] = true; });
  }
  const seen = io_sig_seen[name];
  io_sig_seen[name] = false;
  return seen;
}
