// Peer.addr(sock), as peer.c; the JS lane has no getpeername at hand,
// and answers the empty address.
function peer_addr(socket) {
  return io_tup(socket, "");
}
