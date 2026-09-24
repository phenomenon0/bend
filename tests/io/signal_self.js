// sig.raise: the signal sent to the process itself, mid-run: bun's event
// loop does not turn before the program asks after it
function sig_raise(sig) {
  process.kill(process.pid, sig);
  return { $: "Unit" };
}
