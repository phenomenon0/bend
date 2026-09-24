// Peer.addr(sock), as peer.c: one getpeername on the descriptor, dotted
// for IPv4, RFC 5952's text for IPv6 (io_ip6_show), an IPv4-mapped peer
// dotted, "" when there is none to give.
function peer_addr(socket) {
  const ffi = require("bun:ffi");
  const mac = process.platform === "darwin";
  if (globalThis.BEND_PEER === undefined) {
    globalThis.BEND_PEER = ffi.dlopen(mac ? "libSystem.dylib" : "libc.so.6", {
      getpeername: { args: ["i32", "ptr", "ptr"], returns: "i32" },
    }).symbols;
  }
  const sa = new Uint8Array(128);
  const len = new Uint32Array([128]);
  if (globalThis.BEND_PEER.getpeername(socket, ffi.ptr(sa), ffi.ptr(len)) !== 0) {
    return io_tup(socket, "");
  }
  const fam = mac ? sa[1] : sa[0] | sa[1] << 8;
  const mapped = sa.subarray(8, 18).every((x) => x === 0) && sa[18] === 255 && sa[19] === 255;
  const ip = fam === 2 ? [...sa.subarray(4, 8)].join(".")
    : fam === (mac ? 30 : 10) ? (mapped ? [...sa.subarray(20, 24)].join(".") : io_ip6_show(sa.subarray(8, 24)))
    : "";
  return io_tup(socket, ip);
}
