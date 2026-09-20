// worker.js - runs the emitted Bend->JS programs under the shim, off the main thread.
importScripts("prelude.js");
self.onmessage = (e) => {
  const r = BendShim.runProgram(e.data.code, e.data.files, e.data.env, e.data.argv);
  self.postMessage(Object.assign({ id: e.data.id }, r));
};
