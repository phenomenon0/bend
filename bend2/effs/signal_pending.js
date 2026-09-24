// IO
// ==

// IO.signal_pending(sig) answers whether the signal has arrived since it
// was last asked; the first ask installs the listener that notes it.
// IO.signal_seen(sig) answers whether it has arrived at all since then,
// and clears nothing.
const io_sig_seen = {};
const io_sig_ever = {};

function io_sig_catch(sig) {
  const names = { 1: "SIGHUP", 2: "SIGINT", 10: "SIGUSR1", 12: "SIGUSR2", 15: "SIGTERM" };
  const name = names[Number(sig)];
  if (name === undefined) {
    return undefined;
  }
  if (!(name in io_sig_seen)) {
    io_sig_seen[name] = false;
    io_sig_ever[name] = false;
    process.on(name, () => { io_sig_seen[name] = true; io_sig_ever[name] = true; });
  }
  return name;
}

function io_signal_pending(sig) {
  const name = io_sig_catch(sig);
  if (name === undefined) {
    return false;
  }
  const seen = io_sig_seen[name];
  io_sig_seen[name] = false;
  return seen;
}

function io_signal_seen(sig) {
  const name = io_sig_catch(sig);
  return name !== undefined && io_sig_ever[name];
}
